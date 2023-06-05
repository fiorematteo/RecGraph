use crate::{
    graph::{create_graph_struct, LnzGraph},
    pathwise_graph::{create_path_graph, PathGraph},
    utils::create_handle_pos_in_lnz_from_hashgraph,
};
use gfa::{
    gfa::{Orientation, GFA},
    parser::GFAParser,
};
use handlegraph::{
    handle::{Direction, Handle, NodeId},
    handlegraph::HandleGraph,
    hashgraph::{HashGraph, Path},
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::File,
    io::{stderr, Write},
    rc::Rc,
    time::Instant,
};

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
struct GramPoint {
    pub points: Vec<Point>,
    pub value: String,
}

impl GramPoint {
    fn start(&self) -> Point {
        self.points[0]
    }

    fn end(&self) -> Point {
        self.points[self.points.len() - 1]
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq, Copy)]
struct Point {
    pub node: NodeId,
    pub offset: usize,
}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.node == other.node {
            self.offset.partial_cmp(&other.offset)
        } else {
            self.node.partial_cmp(&other.node)
        }
    }
}

#[derive(Debug, Clone)]
struct Bound {
    start: GramPoint,
    end: GramPoint,
    begin_offset: usize,
    end_offset: usize,
}
type GraphIndex = HashMap<String, GramPoint>;

struct GraphOptimizer<F: Write> {
    graph: HashGraph,
    q: usize,
    graph_qgrams: GraphIndex,
    logger: StatsLogger<F>,
    mask: Option<Vec<bool>>,
    last_graph_non_optimized: bool,
}

impl<F: Write> GraphOptimizer<F> {
    fn new(graph_path: &str, q: usize, mask: Option<String>, stats_out_file: F) -> Self {
        let parser = GFAParser::new();
        let gfa: GFA<usize, ()> = parser.parse_file(graph_path).unwrap();
        let graph: HashGraph = HashGraph::from_gfa(&gfa);
        let qgrams: Vec<GramPoint> = graph.find_all_qgrams(q);

        let mask: Option<Vec<bool>> = mask.map(|mask| {
            assert_eq!(mask.len(), q, "Mask should be as long as q");
            mask.chars()
                .map(|c| match c {
                    '1' => true,
                    '0' => false,
                    _ => panic!("Mask should only contain 1 or 0"),
                })
                .collect()
        });

        let mut graph_qgrams: HashMap<String, Vec<GramPoint>> = apply_mask(qgrams, &mask);
        graph_qgrams.retain(|_, v| v.len() == 1); // remove duplicates
        let graph_qgrams: GraphIndex = graph_qgrams
            .into_iter()
            .map(|(k, v)| (k, v[0].clone()))
            .collect();

        let logger = StatsLogger::new(stats_out_file, q, &graph);
        Self {
            graph,
            q,
            graph_qgrams,
            logger,
            mask,
            last_graph_non_optimized: false,
        }
    }

    fn cut_graph(&mut self, bound: &Bound, read_len: usize, q: usize) -> Option<HashGraph> {
        let before_nodes = self
            .graph
            .predecessors_bfs(bound.start.start(), |_, d| d == bound.begin_offset);
        let after_nodes = self
            .graph
            .successors_bfs(bound.end.end(), |_, d| d == read_len - bound.end_offset - q);

        let direct_bfs = self
            .graph
            .predecessors_bfs(bound.end.start(), |_, depth| depth == read_len);
        let reverse_bfs = self
            .graph
            .successors_bfs(bound.start.end(), |_, depth| depth == read_len);

        // no intersection
        direct_bfs.intersection(&reverse_bfs).next()?;

        let reachable_points: HashSet<_> = direct_bfs
            .union(&reverse_bfs)
            .cloned()
            .chain(before_nodes.into_iter())
            .chain(after_nodes.into_iter())
            .chain(bound.start.points.clone().into_iter())
            .chain(bound.end.points.clone().into_iter())
            .collect();

        let reachable_nodes: HashSet<_> = reachable_points.iter().map(|p| p.node).collect();

        let graph = self
            .graph
            .graph
            .iter()
            .filter(|&(n, _)| reachable_nodes.contains(n))
            .map(|(id, node)| (*id, node.clone()))
            .map(|(id, mut node)| {
                node.left_edges
                    .retain(|h| reachable_nodes.contains(&h.id()));
                node.right_edges
                    .retain(|h| reachable_nodes.contains(&h.id()));
                (id, node)
            })
            .collect();

        let paths = self
            .graph
            .paths
            .iter()
            .map(|(&path_id, path)| {
                let mut nodes = path.nodes.clone();
                nodes.retain(|node| reachable_nodes.contains(&node.id()));
                (
                    path_id,
                    Path {
                        path_id: path.path_id,
                        name: path.name.clone(),
                        is_circular: path.is_circular,
                        nodes,
                    },
                )
            })
            .collect();

        Some(HashGraph {
            max_id: *reachable_nodes.iter().max().unwrap(),
            min_id: *reachable_nodes.iter().min().unwrap(),
            graph,
            path_id: self.graph.path_id.clone(),
            paths,
        })
    }

    fn find_best_bound(&mut self, read: &str, q: usize) -> Option<Bound> {
        let mut read_grams: Vec<(usize, String)> = (0..=read.len() - q)
            .map(|i| (i, &read[i..i + q]))
            .map(|(i, read)| (i, read.to_string()))
            .collect();

        if let Some(mask) = &self.mask {
            for (_, qgram) in read_grams.iter_mut() {
                *qgram = qgram
                    .chars()
                    .enumerate()
                    .filter(|(i, _)| mask[*i])
                    .map(|(_, c)| c)
                    .collect();
            }
        }

        // remove duplicates qgrams from read
        let mut counter = HashMap::new();
        for (_, gram) in &read_grams {
            *counter.entry(gram.clone()).or_insert(0) += 1;
        }
        read_grams.retain(|(_, v)| counter[v.as_str()] == 1);
        read_grams.retain(|(_, v)| self.graph_qgrams.contains_key(v));

        self.logger.current_read.unique_qgrams = Some(read_grams.len());
        self.find_first_valid_gram(&read_grams)
    }

    fn find_first_valid_gram(&self, read_grams: &[(usize, String)]) -> Option<Bound> {
        let (i, begin_gram) = self.find_coherent_left_qgrams(read_grams);
        let (j, end_gram) = self.find_coherent_right_qgrams(read_grams);
        let begin_id = &self.graph_qgrams[begin_gram.as_str()];
        let end_id = &self.graph_qgrams[end_gram.as_str()];

        if begin_id.end() > end_id.start() {
            // order is wrong
            None
        } else {
            // possible invalid pair (parallel qgrams)
            Some(Bound {
                start: begin_id.clone(),
                end: end_id.clone(),
                begin_offset: i,
                end_offset: j,
            })
        }
    }

    fn filter_non_coherent_qgrams(
        &self,
        qgrams: &[(usize, String)],
        infinity: usize,
    ) -> Vec<(usize, String)> {
        let nodes: Vec<_> = qgrams
            .iter()
            .map(|(_, gram)| &self.graph_qgrams[gram])
            .collect();
        let mut summed_errors = HashMap::new();
        for (i, x) in nodes.iter().enumerate() {
            for (j, y) in nodes.iter().enumerate() {
                if i == j {
                    continue;
                }
                if qgrams[i].0 > qgrams[j].0 {
                    // order is wrong
                    continue;
                }
                let read_distance = qgrams[i].0.abs_diff(qgrams[j].0);
                let graph_distance = self.graph_distance(x.start(), y.start(), read_distance * 2);
                let error = graph_distance.unwrap_or(infinity).abs_diff(read_distance);
                *summed_errors.entry(i).or_insert(0) += error;
                *summed_errors.entry(j).or_insert(0) += error;
            }
        }

        // find median
        let mut summed_errors = Vec::from_iter(summed_errors);
        summed_errors.sort_by_key(|(_, v)| *v);
        let median = summed_errors[summed_errors.len() / 2].1;
        summed_errors.retain(|(_, v)| *v <= median);
        let valid_indexes: Vec<_> = summed_errors.clone().into_iter().map(|(i, _)| i).collect();

        qgrams
            .iter()
            .enumerate()
            .filter(|(i, _)| valid_indexes.contains(i))
            .map(|(_, v)| v.clone())
            .collect()
    }

    fn find_coherent_right_qgrams(&self, read_grams: &[(usize, String)]) -> (usize, String) {
        let qgrams = &read_grams[read_grams.len() - 5..];
        // no distance should be bigger then this
        let infinity = read_grams.last().unwrap().0 * 10;
        self.filter_non_coherent_qgrams(qgrams, infinity)
            .last()
            .unwrap()
            .clone()
    }

    fn find_coherent_left_qgrams(&self, read_grams: &[(usize, String)]) -> (usize, String) {
        let qgrams = &read_grams[..5];
        // no distance should be bigger then this
        let infinity = read_grams.last().unwrap().0 * 10;
        self.filter_non_coherent_qgrams(qgrams, infinity)
            .first()
            .unwrap()
            .clone()
    }

    fn graph_distance(&self, start: Point, end: Point, max_distance: usize) -> Option<usize> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<(Point, usize)> = vec![(start, 0)].into();
        while let Some((node, depth)) = queue.pop_front() {
            if node == end {
                return Some(depth);
            }
            if depth > max_distance {
                return None;
            }
            for next in self.graph.iter_successors(node) {
                if !visited.contains(&next) {
                    queue.push_back((next, depth + 1));
                    visited.insert(next);
                }
            }
        }
        None
    }

    fn optimize_graph(&mut self, read: &[char]) -> HashGraph {
        self.logger.current_read.clear();
        match self.find_graph(read) {
            Ok(graph) => {
                self.last_graph_non_optimized = false;
                self.logger.current_read.set_from_graph(&graph);
                self.logger.log_read();
                graph
            }
            Err(reason) => {
                self.last_graph_non_optimized = true;
                self.logger.log_failure(reason);
                self.graph.clone()
            }
        }
    }

    fn find_graph(&mut self, read: &[char]) -> Result<HashGraph, ReadResult> {
        let start_time = Instant::now();
        self.logger.current_read.start_time = Some(start_time);
        let read: String = read.iter().collect();
        let Some(bound) = self.find_best_bound(&read, self.q) else {
                return Err(ReadResult::NoBoundFound((start_time, Instant::now())));
            };
        let Some(graph) = self.cut_graph(&bound, read.len(), self.q) else {
                return Err(ReadResult::NoGraphFound((start_time, Instant::now())));
            };
        self.logger.current_read.start_offset = Some(bound.begin_offset);
        self.logger.current_read.end_offset = Some(bound.end_offset);
        self.logger.current_read.q = Some(self.q);
        Ok(graph)
    }
}

fn apply_mask(qgrams: Vec<GramPoint>, mask: &Option<Vec<bool>>) -> HashMap<String, Vec<GramPoint>> {
    let mut graph_qgrams = HashMap::new();
    for position in &qgrams {
        let key = if let Some(mask) = &mask {
            //apply mask
            position
                .value
                .chars()
                .enumerate()
                .filter_map(|(i, c)| if mask[i] { Some(c) } else { None })
                .collect()
        } else {
            position.value.clone()
        };
        graph_qgrams
            .entry(key)
            .or_insert_with(Vec::new)
            .push(position.clone());
    }
    graph_qgrams
}

pub fn get_optimizer<'a>(
    graph_path: &str,
    q: usize,
    mask: Option<String>,
    stats_out_file: Option<String>,
) -> Box<dyn Optimizer + 'a> {
    if q == 0 {
        Box::new(PassThrough::new(graph_path))
    } else if let Some(file_name) = stats_out_file {
        let file = File::create(file_name).unwrap();
        Box::new(GraphOptimizer::new(graph_path, q, mask, file))
    } else {
        Box::new(GraphOptimizer::new(graph_path, q, mask, stderr()))
    }
}

struct PassThrough {
    sequence_graph: Rc<LnzGraph>,
    hofp_forward: Rc<HandleMap>,
    hofp_reverse: Rc<HandleMap>,
    variation_graph: Rc<PathGraph>,
    inverse_variation_graph: Rc<PathGraph>,
}

impl PassThrough {
    fn new(graph_path: &str) -> Self {
        let parser = GFAParser::new();
        let gfa: GFA<usize, ()> = parser.parse_file(graph_path).unwrap();
        let hashgraph: HashGraph = HashGraph::from_gfa(&gfa);
        let sequence_graph = create_graph_struct(&hashgraph, false);
        let hofp_forward =
            create_handle_pos_in_lnz_from_hashgraph(&sequence_graph.nwp, &hashgraph, false);
        let hofp_reverse =
            create_handle_pos_in_lnz_from_hashgraph(&sequence_graph.nwp, &hashgraph, true);
        let variation_graph = create_path_graph(&hashgraph, false);
        let inverse_variation_graph = create_path_graph(&hashgraph, true);
        Self {
            sequence_graph: sequence_graph.into(),
            hofp_forward: hofp_forward.into(),
            hofp_reverse: hofp_reverse.into(),
            variation_graph: variation_graph.into(),
            inverse_variation_graph: inverse_variation_graph.into(),
        }
    }
}

type HandleMap = HashMap<usize, String>;
pub trait Optimizer {
    fn generate_sequence_graph(
        &mut self,
        read: &[char],
    ) -> (Rc<LnzGraph>, Rc<HandleMap>, Rc<HandleMap>);
    fn generate_variation_graph(&mut self, read: &[char], is_reversed: bool) -> Rc<PathGraph>;
    fn last_graph_non_optimized(&self) -> bool;
}

impl Optimizer for PassThrough {
    fn generate_sequence_graph(
        &mut self,
        _read: &[char],
    ) -> (Rc<LnzGraph>, Rc<HandleMap>, Rc<HandleMap>) {
        (
            self.sequence_graph.clone(),
            self.hofp_forward.clone(),
            self.hofp_reverse.clone(),
        )
    }

    fn generate_variation_graph(&mut self, _read: &[char], is_reversed: bool) -> Rc<PathGraph> {
        if is_reversed {
            self.inverse_variation_graph.clone()
        } else {
            self.variation_graph.clone()
        }
    }

    fn last_graph_non_optimized(&self) -> bool {
        true
    }
}

impl<F: Write> Optimizer for GraphOptimizer<F> {
    fn generate_sequence_graph(
        &mut self,
        read: &[char],
    ) -> (Rc<LnzGraph>, Rc<HandleMap>, Rc<HandleMap>) {
        let hashgraph = self.optimize_graph(read);
        let graph_struct = create_graph_struct(&hashgraph, false);
        let hofp_forward =
            create_handle_pos_in_lnz_from_hashgraph(&graph_struct.nwp, &hashgraph, false);
        let hofp_reverse =
            create_handle_pos_in_lnz_from_hashgraph(&graph_struct.nwp, &hashgraph, true);
        (
            graph_struct.into(),
            hofp_forward.into(),
            hofp_reverse.into(),
        )
    }

    fn generate_variation_graph(&mut self, read: &[char], is_reversed: bool) -> Rc<PathGraph> {
        let hashgraph = self.optimize_graph(read);
        create_path_graph(&hashgraph, is_reversed).into()
    }

    fn last_graph_non_optimized(&self) -> bool {
        self.last_graph_non_optimized
    }
}

trait HashGraphExt<'a> {
    fn successors_bfs(
        &self,
        start: Point,
        check_fun: impl Fn(Point, usize) -> bool,
    ) -> HashSet<Point>;
    fn predecessors_bfs(
        &self,
        start: Point,
        check_fun: impl Fn(Point, usize) -> bool,
    ) -> HashSet<Point>;
    fn find_all_qgrams(&self, q: usize) -> Vec<GramPoint>;
    fn iter_successors(&'a self, point: Point) -> Box<dyn Iterator<Item = Point> + 'a>;
    fn iter_predecessors(&'a self, point: Point) -> Box<dyn Iterator<Item = Point> + 'a>;
    fn clone(&self) -> Self;
}

impl HashGraphExt<'_> for HashGraph {
    fn successors_bfs(
        &self,
        start: Point,
        check_fun: impl Fn(Point, usize) -> bool,
    ) -> HashSet<Point> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<(Point, usize)> = vec![(start, 0)].into();
        while let Some((node, depth)) = queue.pop_front() {
            if check_fun(node, depth) {
                break;
            }
            for next in self.iter_successors(node) {
                if !visited.contains(&next) {
                    queue.push_back((next, depth + 1));
                    visited.insert(next);
                }
            }
        }
        queue.into_iter().for_each(|(node, _)| {
            visited.insert(node);
        });
        visited
    }

    fn predecessors_bfs(
        &self,
        start: Point,
        check_fun: impl Fn(Point, usize) -> bool,
    ) -> HashSet<Point> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<(Point, usize)> = vec![(start, 0)].into();
        while let Some((node, depth)) = queue.pop_front() {
            if check_fun(node, depth) {
                break;
            }
            for next in self.iter_successors(node) {
                if !visited.contains(&next) {
                    queue.push_back((next, depth + 1));
                    visited.insert(next);
                }
            }
        }
        queue.into_iter().for_each(|(node, _)| {
            visited.insert(node);
        });
        visited
    }

    fn find_all_qgrams(&self, q: usize) -> Vec<GramPoint> {
        let mut cache: HashMap<(Point, usize), Vec<Vec<Point>>> = HashMap::new();
        for current_q in 1..=q {
            for node in self.graph.keys() {
                for offset in 0..self.get_node(node).unwrap().sequence.len() {
                    let point = Point {
                        node: *node,
                        offset,
                    };
                    for next in self.iter_successors(point) {
                        if current_q == 1 {
                            // base case
                            let new_v = vec![vec![next]];
                            cache.insert((next, current_q), new_v);
                        } else if let Some(v) = cache.get(&(point, current_q - 1)) {
                            // recursive case
                            for mut new_v in v.clone() {
                                new_v.push(next);
                                cache
                                    .entry((next, current_q))
                                    .or_insert_with(Vec::new)
                                    .push(new_v);
                            }
                        }
                    }
                }
            }
            cache.retain(|&(_, len), _| len == current_q);
        }

        let qgrams: Vec<GramPoint> = cache
            .values()
            .flatten()
            .cloned()
            .map(|points| {
                let value = String::from_utf8(
                    points
                        .iter()
                        .map(|p| self.get_node(&p.node).unwrap().sequence[p.offset])
                        .collect::<Vec<_>>(),
                )
                .unwrap();
                GramPoint { value, points }
            })
            .collect();
        qgrams
    }

    fn iter_successors<'a>(&'a self, point: Point) -> Box<dyn Iterator<Item = Point> + 'a> {
        let node = self.get_node(&point.node).unwrap();
        if point.offset == node.sequence.len() - 1 {
            let handle = Handle::new(point.node, Orientation::Forward);
            return Box::new(
                self.handle_edges_iter(handle, Direction::Right)
                    .map(|handle| Point {
                        node: handle.id(),
                        offset: 0,
                    }),
            );
        } else {
            Box::new(
                [Point {
                    node: point.node,
                    offset: point.offset + 1,
                }]
                .into_iter(),
            )
        }
    }

    fn iter_predecessors<'a>(&'a self, point: Point) -> Box<dyn Iterator<Item = Point> + 'a> {
        if point.offset == 0 {
            let handle = Handle::new(point.node, Orientation::Forward);
            return Box::new(
                self.handle_edges_iter(handle, Direction::Left)
                    .map(|handle| {
                        let node = self.get_node(&handle.id()).unwrap();
                        Point {
                            node: handle.id(),
                            offset: node.sequence.len() - 1,
                        }
                    }),
            );
        } else {
            Box::new(
                [(Point {
                    node: point.node,
                    offset: point.offset - 1,
                })]
                .into_iter(),
            )
        }
    }

    fn clone(&self) -> HashGraph {
        let paths = self
            .paths
            .iter()
            .map(|(&k, v)| {
                (
                    k,
                    Path {
                        path_id: v.path_id,
                        name: v.name.clone(),
                        is_circular: v.is_circular,
                        nodes: v.nodes.clone(),
                    },
                )
            })
            .collect();

        HashGraph {
            max_id: self.max_id,
            min_id: self.min_id,
            graph: self.graph.clone(),
            path_id: self.path_id.clone(),
            paths,
        }
    }
}

#[derive(Debug, Clone)]
struct StatsRead {
    unique_qgrams: usize,
    start_offset: usize,
    end_offset: usize,
    subgraph_size: usize,
    total_sequence_size: usize,
    first_node: NodeId,
    last_node: NodeId,
    q: usize,
    start_time: Instant,
    end_time: Instant,
}

#[derive(Debug, Clone, Default)]
struct StatsReadBuilder {
    unique_qgrams: Option<usize>,
    start_offset: Option<usize>,
    end_offset: Option<usize>,
    subgraph_size: Option<usize>,
    total_sequence_size: Option<usize>,
    first_node: Option<NodeId>,
    last_node: Option<NodeId>,
    q: Option<usize>,
    start_time: Option<Instant>,
}

impl StatsReadBuilder {
    fn clear(&mut self) {
        *self = StatsReadBuilder::default();
    }

    fn build(&self) -> StatsRead {
        StatsRead {
            start_offset: self.start_offset.unwrap(),
            end_offset: self.end_offset.unwrap(),
            subgraph_size: self.subgraph_size.unwrap(),
            total_sequence_size: self.total_sequence_size.unwrap(),
            first_node: self.first_node.unwrap(),
            last_node: self.last_node.unwrap(),
            unique_qgrams: self.unique_qgrams.unwrap(),
            q: self.q.unwrap(),
            start_time: self.start_time.unwrap(),
            end_time: Instant::now(),
        }
    }

    fn set_from_graph(&mut self, graph: &HashGraph) {
        self.subgraph_size = Some(graph.node_count());
        self.first_node = Some(graph.min_node_id());
        self.last_node = Some(graph.max_node_id());
        self.total_sequence_size = Some(
            graph
                .handles_iter()
                .map(|handle| graph.get_node(&handle.id()).unwrap().sequence.len())
                .sum(),
        )
    }
}

struct StatsLogger<F: Write> {
    out_file: F,
    current_read: StatsReadBuilder,
    reads: Vec<ReadResult>,
    begin_time: Instant,
    q: usize,
    full_graph_len: usize,
    total_sequence_size: usize,
}

enum ReadResult {
    Success(StatsRead),
    NoBoundFound((Instant, Instant)),
    NoGraphFound((Instant, Instant)),
}

impl<F: Write> StatsLogger<F> {
    fn new(out: F, q: usize, graph: &HashGraph) -> Self {
        Self {
            out_file: out,
            current_read: StatsReadBuilder::default(),
            reads: Vec::new(),
            begin_time: Instant::now(),
            q,
            full_graph_len: graph.node_count(),
            total_sequence_size: graph
                .handles_iter()
                .map(|handle| graph.get_node(&handle.id()).unwrap().sequence.len())
                .sum(),
        }
    }

    fn log_read(&mut self) {
        let read = self.current_read.build();
        self.reads.push(ReadResult::Success(read));
    }

    fn log_failure(&mut self, result: ReadResult) {
        self.reads.push(result);
    }

    fn write_all(&mut self) -> std::io::Result<()> {
        let reads: Vec<_> = self
            .reads
            .iter()
            .map(|read| match read {
                ReadResult::Success(read) => {
                    let start_time = read
                        .start_time
                        .duration_since(self.begin_time)
                        .as_secs_f64();
                    let end_time = read.end_time.duration_since(self.begin_time).as_secs_f64();
                    let first_node: u64 = read.first_node.into();
                    let last_node: u64 = read.last_node.into();
                    json::object! {
                        success: true,
                        start_offset: read.start_offset,
                        end_offset: read.end_offset,
                        subgraph_size: read.subgraph_size,
                        total_sequence_size: read.total_sequence_size,
                        first_node: first_node,
                        last_node: last_node,
                        unique_qgrams: read.unique_qgrams,
                        q: read.q,
                        start_time: start_time,
                        end_time: end_time
                    }
                }
                ReadResult::NoBoundFound((start_time, end_time)) => {
                    let start_time = start_time.duration_since(self.begin_time).as_secs_f64();
                    let end_time = end_time.duration_since(self.begin_time).as_secs_f64();
                    json::object! {
                        success: false,
                        start_time: start_time,
                        end_time: end_time,
                        reason: "no_bound_found"
                    }
                }
                ReadResult::NoGraphFound((start_time, end_time)) => {
                    let start_time = start_time.duration_since(self.begin_time).as_secs_f64();
                    let end_time = end_time.duration_since(self.begin_time).as_secs_f64();
                    json::object! {
                        success: false,
                        start_time: start_time,
                        end_time: end_time,
                        reason: "no_graph_found"
                    }
                }
            })
            .collect();
        let buffer = json::object! {
            q: self.q,
            full_graph_len: self.full_graph_len,
            total_sequence_size: self.total_sequence_size,
            reads: reads
        };
        writeln!(self.out_file, "{}", buffer)?;
        Ok(())
    }
}

impl<F: Write> Drop for StatsLogger<F> {
    fn drop(&mut self) {
        self.write_all()
            .expect("Error while writing json stat file")
    }
}
