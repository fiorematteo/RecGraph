use gfa::{
    gfa::{Orientation, GFA},
    parser::GFAParser,
};
use handlegraph::{
    handle::{Direction, Handle, NodeId},
    handlegraph::HandleGraph,
    hashgraph::{HashGraph, Path},
};
use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    graph::{create_graph_struct, LnzGraph},
    pathwise_graph::{create_path_graph, PathGraph},
    utils::create_handle_pos_in_lnz_from_hashgraph,
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

#[derive(Debug, Clone, Eq, Hash, PartialEq, PartialOrd, Ord, Copy)]
struct Point {
    pub node: NodeId,
    pub offset: usize,
}

#[derive(Debug, Clone)]
struct Bound {
    start: GramPoint,
    end: GramPoint,
    begin_offset: usize,
    end_offset: usize,
}
type GraphIndex = HashMap<String, Vec<GramPoint>>;

struct GraphOptimizer {
    graph: HashGraph,
    q: usize,
    graph_qgrams: GraphIndex,
}

impl GraphOptimizer {
    fn new(graph_path: &str, q: usize) -> Self {
        let parser = GFAParser::new();
        let gfa: GFA<usize, ()> = parser.parse_file(graph_path).unwrap();
        let graph: HashGraph = HashGraph::from_gfa(&gfa);
        let qgrams: Vec<GramPoint> = graph.find_all_qgrams(q);
        let mut graph_qgrams: GraphIndex = Default::default();
        for position in &qgrams {
            graph_qgrams
                .entry(position.value.clone())
                .and_modify(|x| x.push(position.clone()))
                .or_insert_with(|| vec![position.clone()]);
        }
        graph_qgrams.retain(|_, v| v.len() == 1); // avoid duplicates

        Self {
            graph,
            q,
            graph_qgrams,
        }
    }

    fn cut_graph(&mut self, bound: &Bound, read_len: usize) -> HashGraph {
        let before_nodes = self
            .graph
            .predecessors_bfs(bound.start.start(), |_, d| d == bound.begin_offset);
        let after_nodes = self.graph.successors_bfs(bound.end.end(), |_, d| {
            d == read_len - bound.end_offset - self.q
        });

        let direct_bfs = self.graph.predecessors_bfs(bound.end.start(), |_, _| false);
        let reverse_bfs = self.graph.successors_bfs(bound.start.end(), |_, _| false);

        let reachable_points: HashSet<_> = direct_bfs
            .intersection(&reverse_bfs)
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

        HashGraph {
            max_id: *reachable_nodes.iter().max().unwrap(),
            min_id: *reachable_nodes.iter().min().unwrap(),
            graph,
            path_id: self.graph.path_id.clone(),
            paths,
        }
    }

    fn find_best_bound(&mut self, read: &str) -> Option<Bound> {
        let mut read_grams: Vec<(usize, &str)> = (0..=read.len() - self.q)
            .map(|i| (i, &read[i..i + self.q]))
            .collect();

        // remove duplicates qgrams from read
        let mut duplicates = HashSet::new();
        read_grams = read_grams
            .drain(..)
            .filter(|&(_, v)| duplicates.insert(v))
            .collect();

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
        let read: String = read.iter().collect();
        if let Some(bound) = self.find_best_bound(&read) {
            let graph = self.cut_graph(&bound, read.len());
            // println!(
            //     "graph reduced from {} to {}",
            //     self.graph.node_count(),
            //     graph.node_count()
            // );
            return graph;
        }
        println!("graph is the same");
        self.graph.clone()
    }
}

pub fn get_optimizer<'a>(graph_path: &str, q: usize) -> Box<dyn Optimizer + 'a> {
    if q == 0 {
        Box::new(PassThrough::new(graph_path))
    } else {
        Box::new(GraphOptimizer::new(graph_path, q))
    }
}

struct PassThrough {
    sequence_graph: LnzGraph,
    hofp_forward: HandleMap,
    hofp_reverse: HandleMap,
    variation_graph: PathGraph,
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
        Self {
            sequence_graph,
            hofp_forward,
            hofp_reverse,
            variation_graph,
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
        assert!(!is_reversed);
        self.variation_graph.clone()
    }
}

impl Optimizer for GraphOptimizer {
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

trait HashGraphExt {
    fn clone(&self) -> Self;
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
    fn with_successors(&self, point: Point, callback: impl FnMut(Point));
    fn with_predecessors(&self, point: Point, callback: impl FnMut(Point));
    fn find_all_qgrams(&self, q: usize) -> Vec<GramPoint>;
    fn find_all_qgrams_rec(&self, q: usize) -> Vec<Vec<Point>>;
}

impl HashGraphExt for HashGraph {
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
            self.with_successors(node, |next| {
                if !visited.contains(&next) {
                    queue.push_back((next, depth + 1));
                    visited.insert(next);
                }
            })
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
            self.with_predecessors(node, |next| {
                if !visited.contains(&next) {
                    queue.push_back((next, depth + 1));
                    visited.insert(next);
                }
            })
        }
        queue.into_iter().for_each(|(node, _)| {
            visited.insert(node);
        });
        visited
    }

    fn with_successors(&self, point: Point, mut callback: impl FnMut(Point)) {
        let node = self.get_node(&point.node).unwrap();
        if point.offset == node.sequence.len() - 1 {
            let handle = Handle::new(point.node, Orientation::Forward);
            for handle in self.handle_edges_iter(handle, Direction::Right) {
                callback(Point {
                    node: handle.id(),
                    offset: 0,
                });
            }
        } else {
            callback(Point {
                node: point.node,
                offset: point.offset + 1,
            });
        }
    }

    fn with_predecessors(&self, point: Point, mut callback: impl FnMut(Point)) {
        let node = self.get_node(&point.node).unwrap();
        if point.offset == 0 {
            let handle = Handle::new(point.node, Orientation::Forward);
            for handle in self.handle_edges_iter(handle, Direction::Left) {
                callback(Point {
                    node: handle.id(),
                    offset: node.sequence.len() - 1,
                });
            }
        } else {
            callback(Point {
                node: point.node,
                offset: point.offset - 1,
            });
        }
    }

    fn find_all_qgrams(&self, q: usize) -> Vec<GramPoint> {
        let qgrams = self.find_all_qgrams_rec(q);
        qgrams
            .into_iter()
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
            .collect()
    }

    fn find_all_qgrams_rec(&self, q: usize) -> Vec<Vec<Point>> {
        let mut cache: HashMap<(Point, usize), Vec<Point>> = HashMap::new();
        for q in 1..=q {
            for node in self.graph.keys() {
                for offset in 0..self.get_node(node).unwrap().sequence.len() {
                    let point = Point {
                        node: *node,
                        offset,
                    };
                    self.with_successors(point, |next| {
                        if q == 1 {
                            let new_v = vec![next];
                            cache.insert((next, q), new_v);
                        } else if let Some(v) = cache.get(&(point, q - 1)) {
                            let mut new_v = v.clone();
                            new_v.push(next);
                            cache.insert((next, q), new_v);
                        }
                    });
                }
            }
        }
        cache.values().filter(|v| v.len() == q).cloned().collect()
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
