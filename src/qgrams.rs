use crate::graph::LnzGraph;
use bit_vec::BitVec;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
};

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
    cached_distance: RefCell<Vec<Vec<Option<usize>>>>,
}

impl<'a> DistanceMap<'a> {
    fn new(graph: &'a LnzGraph) -> Self {
        let mut cached_distance = vec![vec![None; graph.len()]; graph.len()];
        for i in 0..graph.len() {
            cached_distance[i][i] = Some(0);
        }

        Self {
            graph,
            cached_distance: RefCell::new(cached_distance),
        }
    }

    fn get(&self, from: usize, to: usize) -> usize {
        let mut cache = self.cached_distance.borrow_mut();
        if let Some(distance) = cache[from][to] {
            return distance;
        }

        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(to);
        while let Some(node) = queue.pop_front() {
            if node == from {
                return cache[from][to].unwrap();
            }
            for pred in self.graph.get_predecessors(node) {
                if cache[pred][to].is_none() {
                    cache[pred][to] = Some(cache[node][to].unwrap() + 1);
                }
                if visited.insert(pred) {
                    queue.push_back(pred);
                }
            }
        }
        cache[from][to] = Some(usize::MAX);
        usize::MAX
    }
}

struct GraphOptimizer<'a> {
    graph: &'a LnzGraph,
    q: usize,
    cache: HashMap<String, (Bound, HandlePos, HandlePos)>,
    distance: DistanceMap<'a>,
    graph_qgrams: GraphIndex,
    handle_pos: &'a HandlePos,
    reverse_handle_pos: &'a HandlePos,
}

type HandlePos = HashMap<usize, String>;

impl<'a> GraphOptimizer<'a> {
    fn new(
        graph: &'a LnzGraph,
        handle_pos: &'a HandlePos,
        reverse_handle_pos: &'a HandlePos,
        q: usize,
    ) -> Self {
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
            handle_pos,
            reverse_handle_pos,
        }
    }

    fn cut_graph(&mut self, bound: &Bound, read_len: usize) -> (LnzGraph, HandlePos, HandlePos) {
        let node_before = bound.read_offset;

        let starts: Vec<_> = (0..self.graph.len())
            .filter(|&node| self.distance.get(node, bound.start.start) <= node_before)
            .collect();

        let node_after = read_len - bound.read_offset + self.q;
        let ends: Vec<_> = (0..self.graph.len())
            .filter(|&node| self.distance.get(bound.end.end, node) <= node_after)
            .collect();

        self.cut_graph_exact(&starts, &ends)
    }

    fn cut_graph_exact(
        &mut self,
        start: &[usize],
        end: &[usize],
    ) -> (LnzGraph, HandlePos, HandlePos) {
        let mut reachable_nodes = (0..self.graph.len())
            .filter(|&node| {
                start
                    .iter()
                    .any(|&start| self.distance.get(start, node) != usize::MAX)
            })
            .filter(|&node| {
                end.iter()
                    .any(|&end| self.distance.get(node, end) != usize::MAX)
            })
            .collect::<Vec<_>>();

        if reachable_nodes[0] != 0 {
            reachable_nodes.insert(0, 0);
        }
        if reachable_nodes[reachable_nodes.len() - 1] != self.graph.len() - 1 {
            reachable_nodes.push(self.graph.len() - 1);
        }

        let lnz = reachable_nodes
            .iter()
            .map(|&node| self.graph.lnz[node])
            .collect::<Vec<_>>();

        let mut nwp = BitVec::from_elem(reachable_nodes.len(), false);
        reachable_nodes
            .iter()
            .enumerate()
            .for_each(|(i, &node)| nwp.set(i, self.graph.nwp[node]));

        let mut pred_hash: HashMap<_, _> = reachable_nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| self.graph.nwp[**node])
            .map(|(i, node)| {
                let predecessors = self.graph.pred_hash[node]
                    .iter()
                    .filter(|pred| reachable_nodes.contains(pred))
                    .map(|pred| reachable_nodes.iter().position(|x| x == pred).unwrap())
                    .collect::<Vec<_>>();
                (i, predecessors)
            })
            .collect();

        let mut last_nodes: Vec<_> = reachable_nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| pred_hash.values().all(|v| !v.contains(node)))
            .map(|(i, _)| i)
            .collect();

        let last_preds = pred_hash.entry(reachable_nodes.len() - 1).or_insert(vec![]);
        last_preds.append(&mut last_nodes);

        let new_handle_pos = reachable_nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| Some((i, self.handle_pos.get(node)?.clone())))
            .collect();

        let new_reverse_handle_pos = reachable_nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| Some((i, self.reverse_handle_pos.get(node)?.clone())))
            .collect();

        (
            LnzGraph {
                lnz,
                nwp,
                pred_hash,
            },
            new_handle_pos,
            new_reverse_handle_pos,
        )
    }

    fn find_best_bound(&mut self, read: &str) -> Option<Bound> {
        let read_grams: Vec<_> = (0..read.len() - self.q + 1)
            .map(|i| &read[i..i + self.q])
            .collect();
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
    handle_pos: &'a HandlePos,
    reverse_handle_pos: &'a HandlePos,
    q: usize,
) -> Box<dyn Optimizer + 'a> {
    if q == 0 {
        Box::new(PassThrough::new(graph, handle_pos, reverse_handle_pos))
    } else {
        Box::new(GraphOptimizer::new(
            graph,
            handle_pos,
            reverse_handle_pos,
            q,
        ))
    }
}

struct PassThrough<'a> {
    graph: &'a LnzGraph,
    handle_pos: &'a HandlePos,
    reverse_handle_pos: &'a HandlePos,
}

impl<'a> PassThrough<'a> {
    fn new(
        graph: &'a LnzGraph,
        handle_pos: &'a HandlePos,
        reverse_handle_pos: &'a HandlePos,
    ) -> Self {
        Self {
            graph,
            handle_pos,
            reverse_handle_pos,
        }
    }
}

pub trait Optimizer {
    fn optimize_graph(&mut self, read: &[char]) -> (LnzGraph, HandlePos, HandlePos);
}

impl<'a> Optimizer for PassThrough<'a> {
    fn optimize_graph(&mut self, _read: &[char]) -> (LnzGraph, HandlePos, HandlePos) {
        (
            self.graph.clone(),
            self.handle_pos.clone(),
            self.reverse_handle_pos.clone(),
        )
    }
}

impl<'a> Optimizer for GraphOptimizer<'a> {
    fn optimize_graph(&mut self, read: &[char]) -> (LnzGraph, HandlePos, HandlePos) {
        let read: String = read.iter().collect();
        if let Some((bound, handle_pos, reverse_handle_pos)) = self.cache.get(&read).cloned() {
            let (graph, _, _) = self.cut_graph(&bound, read.len());
            println!("graph went from {} to {}", self.graph.len(), graph.len());
            return (graph, handle_pos, reverse_handle_pos);
        }
        if let Some(bound) = self.find_best_bound(&read) {
            let (graph, handle_pos, reverse_handle_pos) = self.cut_graph(&bound, read.len());
            self.cache.insert(
                read,
                (bound, handle_pos.clone(), reverse_handle_pos.clone()),
            );
            println!("graph went from {} to {}", self.graph.len(), graph.len());
            return (graph, handle_pos, reverse_handle_pos);
        }
        println!("graph is the same");
        (
            self.graph.clone(),
            self.handle_pos.clone(),
            self.reverse_handle_pos.clone(),
        )
    }
}
