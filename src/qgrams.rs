use crate::graph::LnzGraph;
use bit_vec::BitVec;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
struct GramPoint {
    points: Vec<usize>,
}

impl GramPoint {
    fn new(points: Vec<usize>) -> Self {
        Self { points }
    }

    fn start(&self) -> usize {
        self.points[0]
    }

    fn end(&self) -> usize {
        self.points[self.points.len() - 1]
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

impl LnzGraph {
    fn find_all_qgrams(&self, q: usize) -> Vec<GramPoint> {
        (0..self.len() - 1)
            .flat_map(|node| self.find_all_qgram_from_node(node, q))
            .collect()
    }

    fn find_all_qgram_from_node(&self, node: usize, q: usize) -> Vec<GramPoint> {
        let mut result = Vec::new();
        let mut queue: VecDeque<VecDeque<usize>> = VecDeque::new();
        queue.push_back(vec![node].into());
        while let Some(point) = queue.pop_front() {
            if point.len() == q {
                result.push(point);
            } else {
                self.with_predecessors(point[0], |pred| {
                    let mut new_point = point.clone();
                    new_point.push_front(pred);
                    queue.push_back(new_point);
                });
            }
        }
        result
            .into_iter()
            .map(|x| GramPoint::new(x.into()))
            .collect()
    }

    fn with_predecessors(&self, node: usize, mut callback: impl FnMut(usize)) {
        if self.nwp[node] {
            for pred in self.pred_hash.get(&node).unwrap() {
                callback(*pred);
            }
            return;
        }
        if node == 0 {
            return;
        }
        callback(node - 1);
    }

    fn len(&self) -> usize {
        self.lnz.len()
    }
}

struct DistanceMap<'a> {
    graph: &'a LnzGraph,
    cached_distance: Vec<Vec<Option<usize>>>,
    visited: BitVec,
    queue: VecDeque<usize>,
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
            visited: BitVec::from_elem(graph.len(), false),
            queue: VecDeque::new(),
        }
    }

    fn get(&mut self, from: usize, to: usize) -> usize {
        let cache = &mut self.cached_distance;
        if let Some(distance) = cache[from][to] {
            return distance;
        }

        self.visited.clear();
        self.queue.clear();

        self.queue.push_back(to);
        while let Some(node) = self.queue.pop_front() {
            if node == from {
                return cache[from][to].unwrap();
            }
            self.graph.with_predecessors(node, |pred| {
                if cache[pred][to].is_none() {
                    cache[pred][to] = Some(cache[node][to].unwrap() + 1);
                }
                if !self.visited[pred] {
                    self.visited.set(pred, true);
                    self.queue.push_back(pred);
                }
            });
        }
        cache[from][to] = Some(usize::MAX);
        usize::MAX
    }
}

struct GraphOptimizer<'a> {
    graph: &'a LnzGraph,
    q: usize,
    // distance: DistanceMap<'a>,
    graph_qgrams: GraphIndex,
    handle_pos: &'a HandlePos,
    reverse_handle_pos: &'a HandlePos,
    successors: HashMap<usize, Vec<usize>>,
}

type HandlePos = HashMap<usize, String>;

impl<'a> GraphOptimizer<'a> {
    fn new(
        graph: &'a LnzGraph,
        handle_pos: &'a HandlePos,
        reverse_handle_pos: &'a HandlePos,
        q: usize,
    ) -> Self {
        // let distance = DistanceMap::new(graph);
        let qgrams = graph.find_all_qgrams(q);
        assert!(qgrams.iter().all(|qgram| qgram.points.len() == q));
        let mut graph_qgrams: GraphIndex = Default::default();
        for position in &qgrams {
            let key: String = position.points.iter().map(|&p| graph.lnz[p]).collect();
            graph_qgrams
                .entry(key)
                .and_modify(|x| x.push(position.clone()))
                .or_insert_with(|| vec![position.clone()]);
        }
        graph_qgrams.retain(|_, v| v.len() == 1); // avoid duplicates
        let mut successors = HashMap::new();
        for node in 0..graph.len() {
            graph.with_predecessors(node, |pred| {
                successors.entry(pred).or_insert_with(Vec::new).push(node);
            });
        }
        successors.insert(graph.len() - 1, vec![]);

        Self {
            graph,
            q,
            // distance,
            graph_qgrams,
            handle_pos,
            reverse_handle_pos,
            successors,
        }
    }

    fn predecessors_bfs(
        &self,
        start: usize,
        check_fun: impl Fn(usize, usize) -> bool,
    ) -> HashSet<usize> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<(usize, usize)> = vec![(start, 0)].into();
        while let Some((node, depth)) = queue.pop_front() {
            if check_fun(node, depth) {
                break;
            }
            self.graph.with_predecessors(node, |pred| {
                if !visited.contains(&pred) {
                    queue.push_back((pred, depth + 1));
                    visited.insert(pred);
                }
            })
        }
        queue.into_iter().for_each(|(node, _)| {
            visited.insert(node);
        });
        visited
    }

    fn successors_bfs(
        &self,
        start: usize,
        check_fun: impl Fn(usize, usize) -> bool,
    ) -> HashSet<usize> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<(usize, usize)> = vec![(start, 0)].into();
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

    fn with_successors(&self, node: usize, mut callback: impl FnMut(usize)) {
        for &succ in &self.successors[&node] {
            callback(succ);
        }
    }

    fn cut_graph(&mut self, bound: &Bound, read_len: usize) -> (LnzGraph, HandlePos, HandlePos) {
        let before_nodes =
            self.predecessors_bfs(bound.start.start(), |_, d| d == bound.begin_offset);
        let after_nodes = self.successors_bfs(bound.end.end(), |_, d| {
            d == read_len - bound.end_offset - self.q
        });

        let direct_bfs = self.predecessors_bfs(bound.end.start(), |_, _| false);
        let reverse_bfs = self.successors_bfs(bound.start.end(), |_, _| false);

        let mut reachable_nodes: Vec<_> = direct_bfs
            .intersection(&reverse_bfs)
            .cloned()
            .chain(before_nodes.into_iter())
            .chain(after_nodes.into_iter())
            .chain(bound.start.points.clone().into_iter())
            .chain(bound.end.points.clone().into_iter())
            .collect();

        reachable_nodes.sort_unstable();
        reachable_nodes.dedup();

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

        let last_preds = pred_hash.entry(reachable_nodes.len() - 1).or_default();
        last_preds.append(&mut last_nodes);

        for i in 0..lnz.len() {
            if nwp[i] && pred_hash[&i].is_empty() {
                pred_hash.remove(&i);
                nwp.set(i, false);
            }
        }

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
                        // if self.distance.get(begin_id.end(), end_id.start()) == usize::MAX {
                        //     println!("error avoided!");
                        //     continue;
                        // }
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
        if let Some(bound) = self.find_best_bound(&read) {
            let (graph, handle_pos, reverse_handle_pos) = self.cut_graph(&bound, read.len());
            println!("graph reduced from {} to {}", self.graph.len(), graph.len());
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
