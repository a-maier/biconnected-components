# biconnected-components

Compute the [biconnected
components](https://en.wikipedia.org/wiki/Biconnected_component)
of a graph.

## Example

```rust
use petgraph::graph::UnGraph;
use biconnected_components::Bcc;

// construct a simple graph
let g = UnGraph::<(), ()>::from_edges([
   (0, 1),
   (1, 2)
 ]);

// Get a vector of the biconnected components defined by their node indices
let bcc = g.bcc();
assert_eq!(bcc.len(), 2);
for bcc_nodes in bcc {
   println!("Found biconnected component with nodes {bcc_nodes:?}");
}
```

License: MIT OR Apache-2.0
