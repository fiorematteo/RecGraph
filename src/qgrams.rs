use crate::graph::LnzGraph;
use std::collections::{HashMap, VecDeque};

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
struct GramPoint {
    start: usize,
    end: usize,
}
#[derive(Debug, Clone)]
struct Bound {
    start: GramPoint,
    end: GramPoint,
    distance: usize,
    begin_gram: String,
    end_gram: String,
    read_offset: usize,
}
type GraphIndex = HashMap<String, Vec<GramPoint>>;

impl LnzGraph {
    fn find_all_qgrams(&self, q: usize) -> Vec<(GramPoint, VecDeque<char>)> {
        let mut qgrams: Vec<(GramPoint, VecDeque<char>)> = Vec::new();
        for node in 0..self.len() - 1 {
            let mut new_qgrams = self.find_all_qgram_from_node(node, q);
            qgrams.append(&mut new_qgrams);
        }
        qgrams
    }

    fn find_all_qgram_from_node(&self, node: usize, q: usize) -> Vec<(GramPoint, VecDeque<char>)> {
        let mut qgrams: Vec<(GramPoint, VecDeque<char>)> = Vec::new();
        if q == 1 {
            qgrams.push((
                GramPoint {
                    start: node,
                    end: node,
                },
                VecDeque::new(),
            ));
        } else {
            for pred in self.get_predecessors(node) {
                let mut inner_qgrams = self.find_all_qgram_from_node(pred, q - 1);
                qgrams.append(&mut inner_qgrams);
            }
        }
        for qgram in &mut qgrams {
            qgram.0.end = node;
            qgram.1.push_front(self.lnz[node]);
        }
        qgrams
    }

    fn get_predecessors(&self, node: usize) -> Vec<usize> {
        if node == 0 {
            return vec![];
        }
        if self.nwp[node] {
            self.pred_hash.get(&node).unwrap().to_vec()
        } else {
            vec![node - 1]
        }
    }

    fn len(&self) -> usize {
        self.lnz.len()
    }
}

struct DistanceMap<'a> {
    graph: &'a LnzGraph,
    cached_distance: Vec<Vec<Option<usize>>>,
}

impl<'a> DistanceMap<'a> {
    fn new(graph: &'a LnzGraph) -> Self {
        let mut cached_distance = vec![vec![None; graph.len()]; graph.len()];
        for i in 0..graph.len() {
            cached_distance[i][i] = Some(0);
        }
        Self {
            graph,
            cached_distance,
        }
    }

    fn get(&mut self, from: usize, to: usize) -> usize {
        if let Some(distance) = self.cached_distance[from][to] {
            return distance;
        }
        let mut queue = VecDeque::new();
        queue.push_back(to);
        while let Some(node) = queue.pop_front() {
            if node == from {
                return self.cached_distance[from][to].unwrap();
            }
            for pred in self.graph.get_predecessors(node) {
                if self.cached_distance[from][pred].is_none() {
                    self.cached_distance[from][pred] = Some(self.graph.len() - node);
                    queue.push_back(pred);
                }
            }
        }
        usize::MAX
    }
}

struct GraphOptimizer<'a> {
    graph: &'a LnzGraph,
    q: usize,
    cache: HashMap<String, Bound>,
    distance: DistanceMap<'a>,
    graph_qgrams: GraphIndex,
}

impl<'a> GraphOptimizer<'a> {
    fn new(graph: &'a LnzGraph, q: usize) -> Self {
        let distance = DistanceMap::new(graph);
        let qgrams = graph.find_all_qgrams(q);
        assert!(qgrams.iter().all(|qgram| qgram.1.len() == q));
        let mut graph_qgrams: GraphIndex = Default::default();
        for (position, key) in qgrams {
            let key: Vec<_> = key.into();
            graph_qgrams
                .entry(key.iter().collect())
                .and_modify(|x| x.push(position))
                .or_insert(vec![position]);
        }
        Self {
            graph,
            q,
            cache: Default::default(),
            distance,
            graph_qgrams,
        }
    }

    fn get_graph(&mut self, read: &[char]) -> LnzGraph {
        let read: String = read.iter().collect();
        if let Some(bound) = self.cache.get(&read) {
            return self.cut_graph(bound, read.len());
        }
        if let Some(bound) = self.find_best_bound(&read, self.q) {
            return self.cut_graph(&bound, read.len());
        }
        return self.graph.clone();
    }

    fn cut_graph(&self, bound: &Bound, read_len: usize) -> LnzGraph {
        todo!()
    }

    fn find_best_bound(&mut self, read: &str, q: usize) -> Option<Bound> {
        let read_grams: Vec<_> = (0..read.len() - q + 1).map(|i| &read[i..i + q]).collect();
        let mut possible_bounds = Vec::new();
        for (i, &begin_gram) in read_grams.iter().enumerate() {
            if !self.graph_qgrams.contains_key(begin_gram) {
                continue;
            }
            for end_gram in (i + 1..=read_grams.len() - 1).map(|j| read_grams[j]) {
                if !self.graph_qgrams.contains_key(end_gram) {
                    continue;
                }
                for &begin_id in &self.graph_qgrams[begin_gram] {
                    for &end_id in &self.graph_qgrams[end_gram] {
                        let distance = self.distance.get(begin_id.end, end_id.start);
                        if distance != usize::MAX {
                            possible_bounds.push(Bound {
                                start: begin_id,
                                end: end_id,
                                distance,
                                begin_gram: begin_gram.to_string(),
                                end_gram: end_gram.to_string(),
                                read_offset: i,
                            });
                        }
                    }
                }
            }
        }

        possible_bounds
            .into_iter()
            //.min_by_key(|Bound { distance, .. }| distance.abs_diff(read.len())) // exact?
            .max_by_key(|Bound { distance, .. }| *distance) // conservative
    }
}

pub fn get_optimizer<'a>(
    graph: &'a LnzGraph,
    q: usize,
    use_qgrams: bool,
) -> Box<dyn Optimizer + 'a> {
    if use_qgrams {
        Box::new(GraphOptimizer::new(&graph, q))
    } else {
        Box::new(PassThrough::new(&graph))
    }
}

struct PassThrough<'a> {
    graph: &'a LnzGraph,
}

impl<'a> PassThrough<'a> {
    fn new(graph: &'a LnzGraph) -> Self {
        Self { graph }
    }
}

pub trait Optimizer {
    fn get_graph(&mut self, read: &[char]) -> LnzGraph;
}

impl<'a> Optimizer for PassThrough<'a> {
    fn get_graph(&mut self, _read: &[char]) -> LnzGraph {
        self.graph.clone()
    }
}

impl<'a> Optimizer for GraphOptimizer<'a> {
    fn get_graph(&mut self, read: &[char]) -> LnzGraph {
        self.get_graph(read)
    }
}
