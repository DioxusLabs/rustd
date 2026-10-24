//! Push-based SCC and root-mask maintenance, adapted from PR #23's reach-incr prototype.

use std::collections::VecDeque;

use super::{Bits, Graph, print_of};
use rustc_hash::FxHashSet;

#[derive(Clone)]
pub(super) struct Dynamic {
    pub(super) edges: Vec<Vec<usize>>,
    pub(super) owner: Vec<usize>,
    members: Vec<Vec<usize>>,
    below: Vec<Vec<usize>>,
    above: Vec<Vec<usize>>,
    prints: Vec<Option<u128>>,
    roots_at: Vec<Bits>,
    pub(super) masks: Vec<Bits>,
    own: Vec<Option<u128>>,
    sums: Vec<u128>,
    missing: Vec<usize>,
    free: Vec<usize>,
    pub(super) affected: Bits,
}

impl Dynamic {
    pub(super) fn new(
        edges: Vec<Vec<usize>>,
        own: Vec<Option<u128>>,
        roots: &[(usize, usize)],
        count: usize,
    ) -> Self {
        let (members, owner) = Graph { edges: edges.clone(), ..Graph::default() }.components();
        let n = members.len();
        let mut this = Self {
            edges,
            owner,
            members,
            below: vec![Vec::new(); n],
            above: vec![Vec::new(); n],
            prints: vec![None; n],
            roots_at: vec![Bits::default(); n],
            masks: vec![Bits::default(); n],
            own,
            sums: vec![0; count],
            missing: vec![0; count],
            free: Vec::new(),
            affected: Bits::default(),
        };
        for id in 0..n {
            this.prints[id] = this.print(id);
        }
        for &(node, root) in roots {
            this.roots_at[this.owner[node]].insert(root);
        }
        let mut seeds = Vec::new();
        this.repair(&(0..n).collect::<Vec<_>>(), &mut seeds);
        this.propagate((0..n).rev().collect());
        this
    }

    fn print(&self, id: usize) -> Option<u128> {
        let mut own: Vec<_> =
            self.members[id].iter().map(|&node| self.own[node]).collect::<Option<_>>()?;
        own.sort_unstable();
        Some(print_of(&own))
    }

    pub(super) fn code(&self, root: usize) -> Option<u128> {
        (self.missing[root] == 0).then_some(self.sums[root])
    }

    fn contribution(&mut self, root: usize, print: Option<u128>, add: bool) {
        match print {
            Some(print) => {
                self.sums[root] = if add {
                    self.sums[root].wrapping_add(print)
                } else {
                    self.sums[root].wrapping_sub(print)
                }
            }
            None if add => self.missing[root] += 1,
            None => self.missing[root] -= 1,
        }
        self.affected.insert(root);
    }

    fn replace_print(&mut self, id: usize, new: Option<u128>) {
        let old = std::mem::replace(&mut self.prints[id], new);
        if old != new {
            for root in self.masks[id].clone().iter() {
                self.contribution(root, old, false);
                self.contribution(root, new, true);
            }
        }
    }

    pub(super) fn set_own(&mut self, node: usize, own: Option<u128>) {
        if self.own[node] != own {
            self.own[node] = own;
            let id = self.owner[node];
            self.replace_print(id, self.print(id));
        }
    }

    fn add_component(&mut self, members: Vec<usize>) -> usize {
        let id = self.free.pop().unwrap_or(self.members.len());
        for &node in &members {
            self.owner[node] = id;
        }
        if id == self.members.len() {
            self.members.push(members);
            self.prints.push(None);
            self.below.push(Vec::new());
            self.above.push(Vec::new());
            self.roots_at.push(Bits::default());
            self.masks.push(Bits::default());
        } else {
            self.members[id] = members;
        }
        self.prints[id] = self.print(id);
        id
    }

    pub(super) fn add_node(&mut self, own: Option<u128>) -> usize {
        let node = self.edges.len();
        self.edges.push(Vec::new());
        self.owner.push(usize::MAX);
        self.own.push(own);
        self.add_component(vec![node]);
        node
    }

    fn repair(&mut self, sources: &[usize], seeds: &mut Vec<usize>) {
        for &id in sources {
            let old = std::mem::take(&mut self.below[id]);
            let mut below: Vec<_> = self.members[id]
                .iter()
                .flat_map(|&node| &self.edges[node])
                .map(|&to| self.owner[to])
                .filter(|&to| to != id)
                .collect();
            below.sort_unstable();
            below.dedup();
            for &to in &old {
                self.above[to].retain(|&from| from != id);
            }
            for &to in &below {
                self.above[to].push(id);
            }
            seeds.push(id);
            seeds.extend(old);
            seeds.extend(&below);
            self.below[id] = below;
        }
    }

    fn repartition(
        &mut self,
        old: &[usize],
        groups: Vec<Vec<usize>>,
        root_nodes: &[(usize, usize)],
        seeds: &mut Vec<usize>,
    ) {
        let mut sources = old.to_vec();
        let mut roots = Bits::default();
        for &id in old {
            sources.extend(&self.above[id]);
            roots.union(&std::mem::take(&mut self.roots_at[id]));
            for root in std::mem::take(&mut self.masks[id]).iter() {
                self.contribution(root, self.prints[id], false);
            }
            self.members[id].clear();
            self.prints[id] = Some(print_of(&Vec::<u128>::new()));
        }
        for members in groups {
            sources.push(self.add_component(members));
        }
        for &(node, root) in root_nodes {
            if roots.contains(root) {
                self.roots_at[self.owner[node]].insert(root);
            }
        }
        sources.sort_unstable();
        sources.dedup();
        self.repair(&sources, seeds);
        self.free.extend(old);
    }

    fn closure(start: usize, edges: &[Vec<usize>]) -> FxHashSet<usize> {
        let mut seen = FxHashSet::default();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if seen.insert(node) {
                pending.extend(&edges[node]);
            }
        }
        seen
    }

    fn split(&mut self, id: usize, roots: &[(usize, usize)], seeds: &mut Vec<usize>) {
        let members = &self.members[id];
        let local: rustc_hash::FxHashMap<_, _> =
            members.iter().enumerate().map(|(i, &node)| (node, i)).collect();
        let edges: Vec<Vec<_>> = members
            .iter()
            .map(|&node| self.edges[node].iter().filter_map(|to| local.get(to).copied()).collect())
            .collect();
        let (groups, _) = Graph { edges, ..Graph::default() }.components();
        if groups.len() > 1 {
            let groups = groups
                .into_iter()
                .map(|group| group.into_iter().map(|i| members[i]).collect())
                .collect();
            self.repartition(&[id], groups, roots, seeds);
        }
    }

    fn propagate(&mut self, seeds: Vec<usize>) {
        let mut queued = FxHashSet::default();
        let mut pending = VecDeque::new();
        for id in seeds {
            if queued.insert(id) {
                pending.push_back(id);
            }
        }
        while let Some(id) = pending.pop_front() {
            queued.remove(&id);
            let mut mask = self.roots_at[id].clone();
            for &from in &self.above[id] {
                mask.union(&self.masks[from]);
            }
            let old = std::mem::replace(&mut self.masks[id], mask);
            let new = &self.masks[id];
            if old == *new {
                continue;
            }
            let removed: Vec<_> = old.iter().filter(|&root| !new.contains(root)).collect();
            let added: Vec<_> = new.iter().filter(|&root| !old.contains(root)).collect();
            for root in removed {
                self.contribution(root, self.prints[id], false);
            }
            for root in added {
                self.contribution(root, self.prints[id], true);
            }
            for &to in &self.below[id] {
                if queued.insert(to) {
                    pending.push_back(to);
                }
            }
        }
    }

    pub(super) fn change_edges(
        &mut self,
        node: usize,
        edges: Vec<usize>,
        roots: &[(usize, usize)],
        seeds: &mut Vec<usize>,
    ) {
        let old = self.edges[node].clone();
        for to in old.iter().copied().filter(|to| !edges.contains(to)) {
            let from = self.owner[node];
            let target = self.owner[to];
            self.edges[node].retain(|&edge| edge != to);
            if from == target {
                self.split(from, roots, seeds);
            } else {
                self.repair(&[from], seeds);
            }
        }
        for to in edges.iter().copied().filter(|to| !old.contains(to)) {
            self.edges[node].push(to);
            let from = self.owner[node];
            let target = self.owner[to];
            if from == target {
                continue;
            }
            let forward = Self::closure(target, &self.below);
            if forward.contains(&from) {
                let backward = Self::closure(from, &self.above);
                let merged: Vec<_> = forward.intersection(&backward).copied().collect();
                let members =
                    merged.iter().flat_map(|&id| self.members[id].iter().copied()).collect();
                self.repartition(&merged, vec![members], roots, seeds);
            } else {
                self.repair(&[from], seeds);
            }
        }
        self.edges[node] = edges;
    }

    pub(super) fn settle(&mut self, seeds: Vec<usize>) {
        self.propagate(seeds);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(graph: &Dynamic, roots: &[(usize, usize)], count: usize) {
        let (components, of) =
            Graph { edges: graph.edges.clone(), ..Graph::default() }.components();
        let prints: Vec<_> = components
            .iter()
            .map(|members| {
                let mut own: Vec<_> =
                    members.iter().map(|&node| graph.own[node]).collect::<Option<_>>()?;
                own.sort_unstable();
                Some(print_of(&own))
            })
            .collect();
        for root in 0..count {
            let mut seen = FxHashSet::default();
            let mut pending: Vec<_> =
                roots.iter().filter_map(|&(node, id)| (id == root).then_some(node)).collect();
            while let Some(node) = pending.pop() {
                if seen.insert(node) {
                    pending.extend(&graph.edges[node]);
                }
            }
            let reached: FxHashSet<_> = seen.iter().map(|&node| of[node]).collect();
            let expected = reached
                .iter()
                .try_fold(0u128, |sum, &id| prints[id].map(|print| sum.wrapping_add(print)));
            assert_eq!(graph.code(root), expected, "root {root}");
            for node in 0..graph.edges.len() {
                assert_eq!(
                    graph.masks[graph.owner[node]].contains(root),
                    seen.contains(&node),
                    "node {node} root {root}"
                );
                for other in 0..graph.edges.len() {
                    assert_eq!(graph.owner[node] == graph.owner[other], of[node] == of[other]);
                }
            }
        }
    }

    #[test]
    fn add_remove_and_merge_split_match_full_traversal() {
        let roots = [(0, 0), (3, 1), (2, 2), (3, 2)];
        let mut graph = Dynamic::new(
            vec![vec![1], vec![2], vec![], vec![]],
            vec![Some(1), Some(2), Some(3), None],
            &roots,
            3,
        );
        check(&graph, &roots, 3);
        for (node, edges) in [(0, vec![1, 3]), (0, vec![1]), (2, vec![0]), (2, vec![])] {
            let mut seeds = Vec::new();
            graph.change_edges(node, edges, &roots, &mut seeds);
            graph.settle(seeds);
            check(&graph, &roots, 3);
        }
        graph.set_own(3, Some(4));
        check(&graph, &roots, 3);
        let node = graph.add_node(Some(5));
        let mut seeds = Vec::new();
        graph.change_edges(0, vec![1, node], &roots, &mut seeds);
        graph.change_edges(node, vec![0], &roots, &mut seeds);
        graph.settle(seeds);
        check(&graph, &roots, 3);
    }

    #[test]
    fn mixed_edge_batches_and_code_changes_match_full_traversal() {
        let n = 24;
        let roots = [(0, 0), (1, 1), (2, 2), (3, 2)];
        let mut graph =
            Dynamic::new(vec![Vec::new(); n], (0..n).map(|i| Some(i as u128)).collect(), &roots, 3);
        let mut random = 7u64;
        for edit in 0..600 {
            let mut seeds = Vec::new();
            for _ in 0..3 {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let node = random as usize % n;
                let to = (random >> 32) as usize % n;
                let mut edges = graph.edges[node].clone();
                if edges.contains(&to) {
                    edges.retain(|&id| id != to);
                } else {
                    edges.push(to);
                }
                graph.change_edges(node, edges, &roots, &mut seeds);
                graph.set_own(node, (edit % 13 != 0).then_some(random as u128));
            }
            graph.settle(seeds);
            check(&graph, &roots, 3);
        }
    }

    #[test]
    fn empty_graph_has_empty_ambient_print() {
        let graph = Dynamic::new(Vec::new(), Vec::new(), &[], 1);
        assert_eq!(graph.code(0), Some(0));
    }
}
