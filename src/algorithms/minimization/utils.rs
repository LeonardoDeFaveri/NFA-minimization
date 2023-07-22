use petgraph::dot::{Config, Dot};
use petgraph::stable_graph::{NodeIndex, StableDiGraph};
use petgraph::{prelude::DiGraphMap, Direction};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::hash::Hash;

/// Type used to identify states in depency graphs.
pub type PlaceHolder = usize;

/// Updates `graph` edges so that every edge going out or into `old_node` become
/// and edge going out or into `new_node`. More precisely, what happens is that:
/// - All edges of type `(other, old_node)` are removed and `(other, new_node)`
///     is added to `to_add_in`;
/// - All edges of type `(old_node, other)` are removed and `to_add_out` is updated
///     so that it counts how many times and edge that goes into `old_node` is found.
///
/// After the call, it is safe to add every edge in `to_add_in` to `graph`, while
/// for each pair `(source, count)`, and edge `(new_node, source)` can be added
/// to `graph` only if `count == scc.len()`.
///
/// NOTE:
/// * `old_node` is removed from `graph`'s nodes.
/// * At the end of the call, all edges that involved `old_node` will have been removed.
///
/// ### Complexity
/// Every edge that has `old_node` as one of its ends is checked. The worst case
/// is when every edge passes through `old_node`, so the complexity is O(E).
pub fn update_graph(
    old_node: PlaceHolder,
    new_node: PlaceHolder,
    scc: &Vec<PlaceHolder>,
    to_add_in: &mut HashSet<(PlaceHolder, PlaceHolder)>,
    to_add_out: &mut HashMap<PlaceHolder, usize>,
    graph: &mut DiGraphMap<usize, ()>,
) {
    let mut to_remove = HashSet::new();

    // Manages edges of type (old_node, other)
    for (source, dest, _) in graph.edges_directed(old_node, Direction::Incoming) {
        if !scc.contains(&source) {
            to_add_in.insert((source, new_node));
        }
        to_remove.insert((source, dest));
    }

    // Manages edges of type (other, old_node)
    for (source, dest, _) in graph.edges_directed(old_node, Direction::Outgoing) {
        if !scc.contains(&dest) {
            let counter = to_add_out.entry(dest).or_default();
            *counter += 1;
        }
        to_remove.insert((source, dest));
    }

    for (source, dest) in to_remove {
        graph.remove_edge(source, dest);
    }

    graph.remove_node(old_node);
}

/// Printrs `old_graph` using real states name as node label. The output is
/// written in `file_name`.
pub fn print_graph<S>(
    old_graph: &DiGraphMap<usize, ()>,
    merge_info: &HashMap<PlaceHolder, HashSet<S>>,
    file_name: String,
) where
    S: Eq + Hash + Clone + Display,
{
    let mut graph: StableDiGraph<String, ()> = StableDiGraph::new();
    // Creates a new graph where nodes have as value the set of original states
    // they represents
    let mut trans: HashMap<PlaceHolder, NodeIndex> = HashMap::new();
    for (old_node, set) in merge_info {
        let new_index = graph.add_node(set.to_str());
        trans.insert(*old_node, new_index);
    }

    for (source, dest, _) in old_graph.all_edges() {
        graph.add_edge(trans[&source], trans[&dest], ());
    }

    let _ = std::fs::write(
        file_name,
        format!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel])),
    );
}

trait Stringify {
    fn to_str(&self) -> String;
}

impl<S> Stringify for HashSet<S>
where
    S: Display,
{
    fn to_str(&self) -> String {
        let mut string = String::from("{");
        for (i, s) in self.iter().enumerate() {
            string.push_str(&format!("{}", s));
            if i < self.len() - 1 {
                string.push(',');
            }
        }
        string.push('}');
        string
    }
}
