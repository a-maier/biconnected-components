//! Compute the [biconnected
//! components](https://en.wikipedia.org/wiki/Biconnected_component)
//! of a graph.
//!
//! # Example
//!
//! ```
//! use petgraph::graph::UnGraph;
//! use biconnected_components::Bcc;
//!
//! // construct a simple graph
//! let g = UnGraph::<(), ()>::from_edges([
//!    (0, 1),
//!    (1, 2)
//!  ]);
//!
//! // Get a vector of the biconnected components defined by their node indices
//! let bcc = g.bcc();
//! assert_eq!(bcc.len(), 2);
//! for bcc_nodes in bcc {
//!    println!("Found biconnected component with nodes {bcc_nodes:?}");
//! }
//! ```
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

// Find biconnected components using the algorithm from
// Hopcroft, J.; Tarjan, R.
// "Algorithm 447: efficient algorithms for graph manipulation".
// Communications of the ACM. 16 (6): 372–378.
// [doi:10.1145/362248.362272](https://doi.org/10.1145%2F362248.362272).
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
        if res.is_empty() {
            vec![g.node_indices().collect()]
        } else {
            res
        }
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

        let mut is_cut_vx = false;

        let idx = g.from_index(node);
        for n_idx in g.neighbors(idx) {
            let n = g.to_index(n_idx);
            if !self.visited[n] {
                let parent = node;
                self.parent[n] = parent;
                self.find_bcc_from(g, n, depth + 1, res);
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
        } else if node == 0 {
            // The starting node is only a cut vertex if it has more
            // than one child. But even if there is only a single
            // child the corresponding subtree is a biconnected
            // component
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

    fn bcc_indices(
        g: &UnGraph::<(), (), u32>,
    ) -> Vec<Vec<usize>> {
        let mut bcc: Vec<Vec<usize>> = g.bcc().into_iter().map(
            |bcc| bcc.into_iter().map(|i| g.to_index(i)).collect()
        ).collect();
        for bcc in &mut bcc {
            bcc.sort();
        }
        bcc.sort();
        bcc
    }

    #[test]
    fn trivial() {
        let g: UnGraph::<(), (), u32> = UnGraph::default();
        assert!(g.bcc().is_empty());
    }

    #[test]
    fn single_edge() {
        let g: UnGraph::<(), (), u32> = Graph::from_edges([(0, 1)]);
        let bcc = bcc_indices(&g);
        assert_eq!(bcc, [[0, 1]]);
    }

    #[test]
    fn star_2() {
        let g: UnGraph::<(), (), u32> = Graph::from_edges([(0, 1), (0, 2)]);
        let bcc = bcc_indices(&g);
        let bcc_ref = [[0, 1], [0, 2]];
        assert_eq!(bcc, bcc_ref);
    }

    #[test]
    fn star_2_alt() {
        let g: UnGraph::<(), (), u32> = Graph::from_edges([(0, 1), (1, 2)]);
        let bcc = bcc_indices(&g);
        let bcc_ref = [[0, 1], [1, 2]];
        assert_eq!(bcc, bcc_ref);
    }

    #[test]
    fn lacrosse_stick() {
        let g: UnGraph::<(), (), u32> = Graph::from_edges([
            (0, 1),
            (1, 2),
            (2, 0),
            (2, 3),
        ]);
        let bcc = bcc_indices(&g);
        let bcc_ref = [vec![0, 1, 2], vec![2, 3]];
        assert_eq!(bcc, bcc_ref);
    }

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
        let bcc = bcc_indices(&g);
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
