use std::cmp::min;

use petgraph::{prelude::UnGraph, stable_graph::IndexType, visit::NodeIndexable};
use petgraph::stable_graph::NodeIndex;

pub trait Bcc {
    type Output;

    /// Return all biconnected components
    fn bcc(&self) -> Self::Output;
}


impl<N, E, Ix: IndexType> Bcc for UnGraph<N, E, Ix> {
    type Output = Vec<Vec<NodeIndex<Ix>>>;

    fn bcc(&self) -> Self::Output {
        let mut dfs = HopcroftTarjan::new(self.node_count());
        dfs.find_bcc(self)
    }
}

struct HopcroftTarjan {
    visited: Vec<bool>,
    depth: Vec<usize>,
    lowpoint: Vec<usize>,
    parent: Vec<usize>,
}

impl HopcroftTarjan {
    fn new(nnodes: usize) -> Self {
        Self {
            visited: vec![false; nnodes],
            depth: vec![0; nnodes],
            lowpoint: vec![0; nnodes],
            parent: vec![0; nnodes],
        }
    }

    fn find_bcc<'a, N, E, Ix: IndexType>(
        &mut self,
        g: &UnGraph<N, E, Ix>
    ) -> Vec<Vec<NodeIndex<Ix>>> {
        if g.node_count() == 0 {
            return vec![];
        }
        let mut res = vec![];
        self.find_bcc_from(g, 0, 0, &mut res);
        res
    }

    fn find_bcc_from<'a, N, E, Ix: IndexType>(
        &mut self,
        g: &'a UnGraph<N, E, Ix>,
        node: usize,
        depth: usize,
        res: &mut Vec<Vec<NodeIndex<Ix>>>
    ) {
        self.visited[node] = true;
        self.depth[node] = depth;
        self.lowpoint[node] = depth;
        let mut num_children = 0;

        let mut is_cut_vx = false;

        let idx = g.from_index(node);
        for n_idx in g.neighbors(idx) {
            let n = g.to_index(n_idx);
            if !self.visited[n] {
                let parent = node;
                self.parent[n] = parent;
                self.find_bcc_from(g, n, depth + 1, res);
                num_children += 1;
                if self.lowpoint[n] >= self.depth[parent] {
                    is_cut_vx = true;
                }
                self.lowpoint[parent] = min(
                    self.lowpoint[parent],
                    self.lowpoint[n]
                );
            } else if n != self.parent[node] {
                self.lowpoint[node] = min(
                    self.lowpoint[node],
                    self.depth[n]
                );
            }
        }
        if node > 0 && is_cut_vx {
            for n_idx in g.neighbors(idx) {
                let n = g.to_index(n_idx);
                if self.parent[n] == node && self.lowpoint[n] >= self.depth[node] {
                    let mut bcc = vec![idx, n_idx];
                    self.add_subtree(g, n, &mut bcc);
                    res.push(bcc);
                }
            }
        } else if node == 0 && num_children > 1 {
            for n_idx in g.neighbors(idx) {
                let n = g.to_index(n_idx);
                if self.parent[n] == node {
                    let mut bcc = vec![idx, n_idx];
                    self.add_subtree(g, n, &mut bcc);
                    res.push(bcc);
                }
            }
        }
    }

    fn add_subtree<N, E, Ix: IndexType>(
        &mut self,
        g: &UnGraph<N, E, Ix>,
        root: usize,
        bcc: &mut Vec<NodeIndex<Ix>>,
    ) {
        // detach from depth-first search tree
        self.parent[root] = usize::MAX;
        let root_idx = g.from_index(root);
        for n_idx in g.neighbors(root_idx) {
            let n = g.to_index(n_idx);
            if self.parent[n] == root {
                bcc.push(n_idx);
                self.add_subtree(g, n, bcc)
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use petgraph::Graph;

    use super::*;

    #[test]
    fn wp_example() {
        // example taken from wikipedia
        let g: UnGraph::<(), (), u32> = Graph::from_edges([
            (0, 1, ()),
            (0, 9, ()),
            (1, 2, ()),
            (1, 6, ()),
            (1, 8, ()),
            (2, 3, ()),
            (2, 4, ()),
            (3, 4, ()),
            (4, 5, ()),
            (5, 6, ()),
            (6, 7, ()),
            (9, 10, ()),
            (10, 11, ()),
            (10, 13, ()),
            (11, 12, ()),
            (12, 13, ()),
        ]);
        let mut bcc: Vec<Vec<usize>> = g.bcc().into_iter().map(
            |bcc| bcc.into_iter().map(|i| g.to_index(i)).collect()
        ).collect();
        for bcc in &mut bcc {
            bcc.sort();
        }
        bcc.sort();
        let bcc_ref = [
            vec![0, 1],
            vec![0, 9],
            vec![1, 2, 3, 4, 5, 6],
            vec![1, 8],
            vec![6, 7],
            vec![9, 10],
            vec![10, 11, 12, 13],
        ];
        assert_eq!(bcc, bcc_ref);
    }
}
