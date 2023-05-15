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
use log::{error, info, warn};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::File,
    io::{stderr, Write},
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
type GraphIndex = HashMap<String, Vec<GramPoint>>;

struct GraphOptimizer<F: Write> {
    graph: HashGraph,
    max_q: usize,
    graph_qgrams: GraphIndex,
    logger: StatsLogger<F>,
}

impl<F: Write> GraphOptimizer<F> {
    fn new(graph_path: &str, max_q: usize, stats_out_file: F) -> Self {
        let parser = GFAParser::new();
        let gfa: GFA<usize, ()> = parser.parse_file(graph_path).unwrap();
        let graph: HashGraph = HashGraph::from_gfa(&gfa);
        let qgrams: Vec<GramPoint> = graph.find_all_qgrams(max_q);
        let mut graph_qgrams: GraphIndex = Default::default();
        for position in &qgrams {
            graph_qgrams
                .entry(position.value.clone())
                .or_insert_with(Vec::new)
                .push(position.clone());
        }
        graph_qgrams.retain(|_, v| v.len() == 1); // remove duplicates
        info!("Found {} unique qgrams", graph_qgrams.len());

        let logger = StatsLogger::new(stats_out_file, max_q, graph.node_count());

        Self {
            graph,
            max_q,
            graph_qgrams,
            logger,
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

        if direct_bfs.intersection(&reverse_bfs).next().is_none() {
            error!("No intersection found between direct and reverse bfs");
            return None;
        }

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
        let mut read_grams: Vec<(usize, &str)> =
            (0..=read.len() - q).map(|i| (i, &read[i..i + q])).collect();

        // remove duplicates qgrams from read
        let mut counter = HashMap::new();
        for (_, gram) in &read_grams {
            *counter.entry(*gram).or_insert(0) += 1;
        }
        read_grams.retain(|(_, v)| counter[v] == 1);

        info!(
            "Found {} unique qgrams in {} long read",
            read_grams.len(),
            read.len()
        );
        self.logger.current_read.unique_qgrams = Some(read_grams.len());
        self.find_first_valid_gram(&read_grams)
    }

    fn find_first_valid_gram(&self, read_grams: &[(usize, &str)]) -> Option<Bound> {
        // maximising distance inside read
        for &(i, begin_gram) in read_grams.iter() {
            if !self.graph_qgrams.contains_key(begin_gram) {
                continue;
            }
            for (j, end_gram) in (i + 1..read_grams.len()).map(|j| read_grams[j]).rev() {
                if !self.graph_qgrams.contains_key(end_gram) {
                    continue;
                }
                for begin_id in &self.graph_qgrams[begin_gram] {
                    for end_id in &self.graph_qgrams[end_gram] {
                        if begin_id.end() > end_id.start() {
                            // order is wrong
                            continue;
                        }
                        // possible invalid pair (parallel qgrams)
                        return Some(Bound {
                            start: begin_id.clone(),
                            end: end_id.clone(),
                            begin_offset: i,
                            end_offset: j,
                        });
                    }
                }
            }
        }
        None
    }

    fn optimize_graph(&mut self, read: &[char]) -> HashGraph {
        self.logger.current_read.clear();
        self.logger.current_read.start_time = Some(Instant::now());
        let read: String = read.iter().collect();
        let mut failure = None;
        for q in (2..=self.max_q).rev() {
            let Some(bound) = self.find_best_bound(&read, q) else {
                warn!("No valid bound found for q={}", q);
                failure = Some(ReadResult::NoBoundFound(Instant::now()));
                continue;
            };
            let Some(graph) = self.cut_graph(&bound, read.len(), q) else {
                warn!("No valid graph for bound found with q={}", q);
                failure = Some(ReadResult::NoGraphFound(Instant::now()));
                continue;
            };
            info!(
                "Graph reduced from {} to {}",
                self.graph.node_count(),
                graph.node_count()
            );
            info!("Bound start offset {}", bound.begin_offset);
            info!("Bound end offset {}", bound.end_offset);
            self.logger.current_read.start_offset = Some(bound.begin_offset);
            self.logger.current_read.end_offset = Some(bound.end_offset);
            self.logger.current_read.q = Some(q);
            self.logger.current_read.set_from_graph(&graph);
            self.logger.log_read();
            return graph;
        }
        warn!("No valid bound found, falling back to whole graph");
        self.logger
            .log_failure(failure.expect("q must be greater than 2"));
        self.graph.clone()
    }
}

pub fn get_optimizer<'a>(
    graph_path: &str,
    q: usize,
    stats_out_file: Option<String>,
) -> Box<dyn Optimizer + 'a> {
    if q == 0 {
        Box::new(PassThrough::new(graph_path))
    } else if let Some(file_name) = stats_out_file {
        let file = File::create(file_name).unwrap();
        Box::new(GraphOptimizer::new(graph_path, q, file))
    } else {
        Box::new(GraphOptimizer::new(graph_path, q, stderr()))
    }
}

struct PassThrough {
    sequence_graph: LnzGraph,
    hofp_forward: HandleMap,
    hofp_reverse: HandleMap,
    variation_graph: PathGraph,
    inverse_variation_graph: PathGraph,
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
            sequence_graph,
            hofp_forward,
            hofp_reverse,
            variation_graph,
            inverse_variation_graph,
        }
    }
}

type HandleMap = HashMap<usize, String>;
pub trait Optimizer {
    fn generate_sequence_graph(&mut self, read: &[char]) -> (LnzGraph, HandleMap, HandleMap);
    fn generate_variation_graph(&mut self, read: &[char], is_reversed: bool) -> PathGraph;
}

impl Optimizer for PassThrough {
    fn generate_sequence_graph(&mut self, _read: &[char]) -> (LnzGraph, HandleMap, HandleMap) {
        (
            self.sequence_graph.clone(),
            self.hofp_forward.clone(),
            self.hofp_reverse.clone(),
        )
    }

    fn generate_variation_graph(&mut self, _read: &[char], is_reversed: bool) -> PathGraph {
        if is_reversed {
            self.inverse_variation_graph.clone()
        } else {
            self.variation_graph.clone()
        }
    }
}

impl<F: Write> Optimizer for GraphOptimizer<F> {
    fn generate_sequence_graph(&mut self, read: &[char]) -> (LnzGraph, HandleMap, HandleMap) {
        let hashgraph = self.optimize_graph(read);
        let graph_struct = create_graph_struct(&hashgraph, false);
        let hofp_forward =
            create_handle_pos_in_lnz_from_hashgraph(&graph_struct.nwp, &hashgraph, false);
        let hofp_reverse =
            create_handle_pos_in_lnz_from_hashgraph(&graph_struct.nwp, &hashgraph, true);
        (graph_struct, hofp_forward, hofp_reverse)
    }

    fn generate_variation_graph(&mut self, read: &[char], is_reversed: bool) -> PathGraph {
        let hashgraph = self.optimize_graph(read);
        create_path_graph(&hashgraph, is_reversed)
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
        info!("Found {} non-unique qgrams", qgrams.len());

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
    first_node: NodeId,
    last_node: NodeId,
    q: usize,
    start_time: Instant,
}

#[derive(Debug, Clone, Default)]
struct StatsReadBuilder {
    unique_qgrams: Option<usize>,
    start_offset: Option<usize>,
    end_offset: Option<usize>,
    subgraph_size: Option<usize>,
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
            first_node: self.first_node.unwrap(),
            last_node: self.last_node.unwrap(),
            unique_qgrams: self.unique_qgrams.unwrap(),
            q: self.q.unwrap(),
            start_time: self.start_time.unwrap(),
        }
    }

    fn set_from_graph(&mut self, graph: &HashGraph) {
        self.subgraph_size = Some(graph.node_count());
        self.first_node = Some(graph.min_node_id());
        self.last_node = Some(graph.max_node_id());
    }
}

struct StatsLogger<F: Write> {
    out_file: F,
    current_read: StatsReadBuilder,
    reads: Vec<ReadResult>,
    begin_time: Instant,
    max_q: usize,
    full_graph_len: usize,
}

enum ReadResult {
    Success(StatsRead),
    NoBoundFound(Instant),
    NoGraphFound(Instant),
}

impl<F: Write> StatsLogger<F> {
    fn new(out: F, max_q: usize, full_graph_len: usize) -> Self {
        Self {
            out_file: out,
            current_read: StatsReadBuilder::default(),
            reads: Vec::new(),
            begin_time: Instant::now(),
            max_q,
            full_graph_len,
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
                    let start_time = read.start_time.duration_since(self.begin_time).as_secs();
                    let first_node: u64 = read.first_node.into();
                    let last_node: u64 = read.last_node.into();
                    json::object! {
                        success: true,
                        start_offset: read.start_offset,
                        end_offset: read.end_offset,
                        subgraph_size: read.subgraph_size,
                        first_node: first_node,
                        last_node: last_node,
                        unique_qgrams: read.unique_qgrams,
                        q: read.q,
                        start_time: start_time
                    }
                }
                ReadResult::NoBoundFound(time) => {
                    let start_time = time.duration_since(self.begin_time).as_secs();
                    json::object! {
                        success: false,
                        start_time: start_time,
                        reason: "no_bound_found"
                    }
                }
                ReadResult::NoGraphFound(time) => {
                    let start_time = time.duration_since(self.begin_time).as_secs();
                    json::object! {
                        success: false,
                        start_time: start_time,
                        reason: "no_graph_found"
                    }
                }
            })
            .collect();
        let buffer = json::object! {
            max_q: self.max_q,
            full_graph_len: self.full_graph_len,
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
