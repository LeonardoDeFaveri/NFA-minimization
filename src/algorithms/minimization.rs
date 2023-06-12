use disjoint_hash_set::DisjointHashSet;
use petgraph::{
    dot::{Config, Dot},
    prelude::DiGraphMap,
    stable_graph::{NodeIndex, StableDiGraph},
    Direction,
};
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
};

/// Merges states that have the same right_language.
///
/// NOTE: works even for left languages if `left_rel` is provided in place
/// of `right_rel`
pub fn right_eq<S>(states: &HashSet<S>, right_rel: &HashSet<(S, S)>) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
{
    let mut merge_info: DisjointHashSet<S> =
        states.into_iter().map(|x| (x.clone(), x.clone())).collect();

    for (p, q) in right_rel {
        if right_rel.contains(&(q.clone(), p.clone())) {
            merge_info.link(p.clone(), q.clone());
        }
    }

    merge_info.sets().collect()
}

/// Merges states that have the same right language and then states that have
/// the same left language.
///
/// Works even for left-right equivalences if `right_rel` and `left_rel` are
/// swapped.
pub fn right_left_eq<S>(
    states: &HashSet<S>,
    right_rel: &HashSet<(S, S)>,
    left_rel: &HashSet<(S, S)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
{
    let mut merge_info: DisjointHashSet<S> =
        states.into_iter().map(|x| (x.clone(), x.clone())).collect();

    let mut to_forget: HashSet<(S, S)> = HashSet::new();

    for (p, q) in right_rel {
        if right_rel.contains(&(q.clone(), p.clone())) {
            merge_info.link(p.clone(), q.clone());
            for (a, s) in left_rel {
                if a != q {
                    continue;
                }

                if !left_rel.contains(&(p.clone(), s.clone())) {
                    to_forget.insert((q.clone(), s.clone()));
                }
            }
        }
    }

    for (p, q) in left_rel {
        if to_forget.contains(&(p.clone(), q.clone())) {
            continue;
        }

        let rev_pair = (q.clone(), p.clone());
        if left_rel.contains(&rev_pair) && !to_forget.contains(&rev_pair) {
            merge_info.link(p.clone(), q.clone());
        }
    }

    merge_info.sets().collect()
}

/*  Priority (dec)              | Reduction
    Preorder, RightEq, LeftEq   | 12.430%
    Preorder, LeftEq, RightEq   | 12.534%   *
    RightEq, LeftEq, Preorder   | 12.278%
    RightEq, Preorder, LeftEq   | 12.430%
    LeftEq, Preorder, RightEq   | 12.534%   *
    LeftEq, RightEq, Preorder   | 12.534%   *
*/
#[derive(PartialEq, PartialOrd, Eq, Ord)]
enum MergeReason {
    Preorder = 2,
    RightEq = 1,
    LeftEq = 3,
    None = 0,
}

/// Scores state pairs and merge states using pairs in a decresing priority order
pub fn preorders_with_priority<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
    right_rel: &HashSet<(S, S)>,
    left_rel: &HashSet<(S, S)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone + Display,
{
    let mut merge_info: DisjointHashSet<S> =
        states.into_iter().map(|x| (x.clone(), x.clone())).collect();

    let mut sorted_pairs: priority_queue::PriorityQueue<(S, S), MergeReason> =
        priority_queue::PriorityQueue::new();

    for ((p, q), (right, left, has_loops)) in rel_table {
        let mut reason = MergeReason::None;
        let rev_pair = (q.clone(), p.clone());
        if let Some((rev_right, rev_left, _)) = rel_table.get(&rev_pair) {
            if *left && *rev_left {
                reason = reason.max(MergeReason::LeftEq);
            }
            if *right && *rev_right {
                reason = reason.max(MergeReason::RightEq);
            }
        }
        if *right && *left && !*has_loops {
            reason = reason.max(MergeReason::Preorder);
        }

        if reason != MergeReason::None {
            sorted_pairs.push((p.clone(), q.clone()), reason);
        }
    }

    let mut to_forget_right: HashSet<(S, S)> = HashSet::new();
    let mut to_forget_left: HashSet<(S, S)> = HashSet::new();

    //let mut i = 1;
    for ((p, q), reason) in sorted_pairs.into_sorted_iter() {
        let pair = (p.clone(), q.clone());
        let rev_pair = (q.clone(), p.clone());

        if to_forget_left.contains(&pair) || to_forget_right.contains(&pair) {
            continue;
        }

        match reason {
            MergeReason::Preorder => {
                merge_info.link(p.clone(), q.clone());
            }
            MergeReason::RightEq if !to_forget_right.contains(&rev_pair) => {
                merge_info.link(p.clone(), q.clone());
                for (a, s) in left_rel {
                    if *a == q && !left_rel.contains(&(p.clone(), s.clone())) {
                        to_forget_left.insert((q.clone(), s.clone()));
                    }
                }
            }
            MergeReason::LeftEq if !to_forget_left.contains(&rev_pair) => {
                merge_info.link(p.clone(), q.clone());
                for (a, s) in right_rel {
                    if *a == q && !right_rel.contains(&(p.clone(), s.clone())) {
                        to_forget_right.insert((q.clone(), s.clone()));
                    }
                }
            }
            _ => {}
        }
    }

    merge_info.sets().collect()
}

/*pub fn preorders_with_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone + Display,
{
    type PlaceHolder = usize;

    // Dependency graphs for right and left preorders
    let mut graph_right: StableDiGraph<usize, ()> = StableDiGraph::new();
    let mut graph_left: StableDiGraph<usize, ()> = StableDiGraph::new();

    // Used only to avoid duplicated nodes: every state is mapped to an integer
    // and new states obtained by merge have incremental integers as values
    let mut placheholders: HashMap<&S, PlaceHolder> = HashMap::new();
    // Used to map each placeholder to its index in `graph_left` and `graph_right`
    let mut node_indexes: HashMap<PlaceHolder, (NodeIndex, NodeIndex)> = HashMap::new();
    let mut right_phs: HashMap<NodeIndex, PlaceHolder> = HashMap::new();
    let mut left_phs: HashMap<NodeIndex, PlaceHolder> = HashMap::new();

    // Each SCC will ultimately contain one or more of the original states.
    // `merge_info` uses node indexes of `graph_left` as keys.
    let mut merge_info: HashMap<NodeIndex, HashSet<S>> = HashMap::new();

    // Populates graphs and structures with nodes (aka states)
    for (placeholder, state) in states.iter().enumerate() {
        placheholders.insert(state, placeholder);
        let indexes = (
            graph_left.add_node(placeholder),
            graph_right.add_node(placeholder),
        );
        node_indexes.insert(placeholder, indexes);
        left_phs.insert(indexes.0, placeholder);
        right_phs.insert(indexes.1, placeholder);

        // Left node indexes are used to get states
        let mut set = HashSet::new();
        set.insert(state.clone());
        merge_info.insert(indexes.0, set);
    }

    // Builds a dependency graph for right and left preorder
    for ((p, q), (right, left, _)) in rel_table {
        let p_ph = placheholders[p];
        let q_ph = placheholders[q];

        if p_ph == q_ph {
            continue;
        }

        let (p_left, p_right) = node_indexes.get(&p_ph).unwrap();
        let (q_left, q_right) = node_indexes.get(&q_ph).unwrap();

        if *right {
            graph_right.add_edge(*p_right, *q_right, ());
        }
        if *left {
            graph_left.add_edge(*p_left, *q_left, ());
        }
    }

    //let mut i = 0;
    let mut next_state = states.len();

    loop {
        // Calculates SCCs for both dependency graphs
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        //print_graph(&graph_right, &merge_info, format!("steps/right-{i}.gv"));
        //print_graph(&graph_left, &merge_info, format!("steps/left-{i}.gv"));
        //i += 1;

        let biggest_right_scc = sccs_right
            .iter()
            .max_by(|a, b| a.len().cmp(&b.len()))
            .unwrap();
        let biggest_left_scc = sccs_left
            .iter()
            .max_by(|a, b| a.len().cmp(&b.len()))
            .unwrap();

        let (biggest_scc, graph, other_graph, is_right) =
            if biggest_right_scc.len() >= biggest_left_scc.len() {
                (biggest_right_scc, &mut graph_right, &mut graph_left, true)
            } else {
                (biggest_left_scc, &mut graph_left, &mut graph_right, false)
            };

        if biggest_scc.len() == 1 {
            break;
        }

        // Adds the node associated to the scc
        let graph_nodeindex = graph.add_node(next_state);
        let other_nodeindex = other_graph.add_node(next_state);
        // Updates the other structures
        if is_right {
            right_phs.insert(graph_nodeindex, next_state);
            left_phs.insert(other_nodeindex, next_state);
            node_indexes.insert(next_state, (other_nodeindex, graph_nodeindex));
        } else {
            right_phs.insert(other_nodeindex, next_state);
            left_phs.insert(graph_nodeindex, next_state);
            node_indexes.insert(next_state, (graph_nodeindex, other_nodeindex));
        }

        let mut new_states_set = HashSet::new();
        let mut to_add_graph_in = HashSet::new();
        let mut to_add_other_in = HashSet::new();
        let mut to_add_graph_out = HashMap::new();
        let mut to_add_other_out = HashMap::new();

        // Every state in `biggest_scc` will have `next_state` as container
        for old_state in biggest_scc {
            let ph = if is_right {
                right_phs[old_state]
            } else {
                left_phs[old_state]
            };
            let (old_left, old_right) = node_indexes[&ph];

            update_graph(
                old_left,
                graph_nodeindex,
                &biggest_scc,
                &mut to_add_graph_in,
                &mut to_add_graph_out,
                graph,
            );
            update_graph(
                old_right,
                other_nodeindex,
                &biggest_scc,
                &mut to_add_other_in,
                &mut to_add_other_out,
                other_graph,
            );

            // Removes every scc that has been merged and adds the original
            // states previously contained in those scc to `set`
            let original_states = merge_info.get(&old_left).unwrap();
            new_states_set.extend(original_states.iter().map(|s| s.to_owned()));

            merge_info.remove(&old_left);
        }

        // Since `merge_info` uses `graph_left` indexes, if `graph` is
        // currently refering to `graph_right`, `graph_nodeindex` is the index
        // of the new node in `graph_left`, so it is added to `merge_info`
        if is_right {
            merge_info.insert(other_nodeindex, new_states_set);
        } else {
            merge_info.insert(graph_nodeindex, new_states_set);
        }

        graph.extend_with_edges(to_add_graph_in);
        other_graph.extend_with_edges(to_add_other_in);

        for (state_index, counter) in to_add_graph_out {
            if biggest_scc.len() == counter {
                graph.add_edge(graph_nodeindex, state_index, ());
            }
        }

        for (state_index, counter) in to_add_other_out {
            if biggest_scc.len() == counter {
                other_graph.add_edge(other_nodeindex, state_index, ());
            }
        }

        next_state += 1;
    }

    merge_info
        .into_iter()
        .map(|(_placeholder, states_set)| states_set)
        .collect()
}*/

use union_find_rs::prelude::*;
type PlaceHolder = usize;

pub fn preorders_with_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone + Display,
{
    // Maps each original state to its placeholder
    let mut all_ph: HashMap<&S, PlaceHolder> = HashMap::new();
    // [Used only for merging states using rule 3]
    // Maps each placeholder to the placeholder of the state that containes it
    let mut containers: DisjointSets<PlaceHolder> = DisjointSets::new();

    // Dependency graphs for right and left preorders
    let mut graph_right: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_left: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();

    // Used to keep track of nfa states.
    let mut merge_info: HashMap<PlaceHolder, HashSet<S>> = HashMap::new();

    // Assigns a placeholder to each state
    for (ph, state) in states.iter().enumerate() {
        graph_right.add_node(ph);
        graph_left.add_node(ph);
        all_ph.insert(state, ph);
        containers.make_set(ph).unwrap();

        let mut set = HashSet::new();
        set.insert(state.clone());
        merge_info.insert(ph, set);
    }

    //let mut intersection = Vec::new();

    // Adds edges to dependency graphs
    for ((p, q), (right, left, has_loop)) in rel_table {
        let p_ph = all_ph[p];
        let q_ph = all_ph[q];

        if *right {
            graph_right.add_edge(p_ph, q_ph, ());
        }
        if *left {
            graph_left.add_edge(p_ph, q_ph, ());
        }

        /*if *right && *left && !*has_loop {
            intersection.push((p_ph, q_ph));
        }*/
    }

    let mut next_state = states.len();
    //let mut i = 0;

    // MERGES STATES USING RULES 1 AND 2!
    // Merges every non trivial SCC
    loop {
        // Calculates SCCs for both dependency graphs
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        //print_graph(&graph_right, &merge_info, format!("steps/right-{i}.gv"));
        //print_graph(&graph_left, &merge_info, format!("steps/left-{i}.gv"));
        //i += 1;

        let biggest_right_scc = sccs_right
            .iter()
            .max_by(|a, b| a.len().cmp(&b.len()))
            .unwrap();
        let biggest_left_scc = sccs_left
            .iter()
            .max_by(|a, b| a.len().cmp(&b.len()))
            .unwrap();

        let (biggest_scc, graph, other_graph) = if biggest_right_scc.len() >= biggest_left_scc.len()
        {
            (biggest_right_scc, &mut graph_right, &mut graph_left)
        } else {
            (biggest_left_scc, &mut graph_left, &mut graph_right)
        };

        if biggest_scc.len() == 1 {
            break;
        }

        // Adds the node associated to the scc
        graph.add_node(next_state);
        other_graph.add_node(next_state);
        containers.make_set(next_state).unwrap();

        let mut new_states_set = HashSet::new();
        let mut to_add_graph_in = HashSet::new();
        let mut to_add_other_in = HashSet::new();
        let mut to_add_graph_out = HashMap::new();
        let mut to_add_other_out = HashMap::new();

        for old_state in biggest_scc {
            update_graph(
                *old_state,
                next_state,
                &biggest_scc,
                &mut to_add_graph_in,
                &mut to_add_graph_out,
                graph,
            );
            update_graph(
                *old_state,
                next_state,
                &biggest_scc,
                &mut to_add_other_in,
                &mut to_add_other_out,
                other_graph,
            );

            // Removes every scc that has been merged and adds the original
            // states previously contained in those scc to `set`
            let original_states = merge_info.get(&old_state).unwrap();
            new_states_set.extend(original_states.iter().map(|s| s.to_owned()));

            merge_info.remove(&old_state);
            containers.union(old_state, &next_state).unwrap();
        }

        merge_info.insert(next_state, new_states_set);

        graph.extend(to_add_graph_in);
        other_graph.extend(to_add_other_in);

        for (state_index, counter) in to_add_graph_out {
            if biggest_scc.len() == counter {
                graph.add_edge(next_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_other_out {
            if biggest_scc.len() == counter {
                other_graph.add_edge(next_state, state_index, ());
            }
        }

        next_state += 1;
    }
    // After this loop ends, no cicle is left in any dependency graph

    // MERGES STATES USING RULE 3!

    // All edges that exists in both graphs, indicated a preorder of type 3
    let intersection = graph_right
        .all_edges()
        .filter(|(source, dest, _)| graph_left.contains_edge(*source, *dest))
        .map(|(source, dest, _)| (source, dest))
        .collect::<Vec<_>>();

    for (old_source, old_dest) in intersection {
        //println!("1) NEW STATE: {}", next_state);
        //println!(
        //    "2) Accessing ({}, {}) = ({}, {})",
        //    old_source,
        //    old_dest,
        //    containers.find_set(&old_source).unwrap(),
        //    containers.find_set(&old_dest).unwrap(),
        //);
        let source = containers.find_set(&old_source).unwrap();
        let dest = containers.find_set(&old_dest).unwrap();

        //print!("3) ({},", merge_info.get(&source).unwrap().to_str());
        //println!("{})", merge_info.get(&dest).unwrap().to_str());

        let pair = vec![source, dest];
        graph_right.add_node(next_state);
        graph_left.add_node(next_state);

        let mut new_states_set = HashSet::new();
        let mut to_add_right_in = HashSet::new();
        let mut to_add_left_in = HashSet::new();
        let mut to_add_right_out = HashMap::new();
        let mut to_add_left_out = HashMap::new();

        update_graph(
            source,
            next_state,
            &pair,
            &mut to_add_right_in,
            &mut to_add_right_out,
            &mut graph_right,
        );
        update_graph(
            dest,
            next_state,
            &pair,
            &mut to_add_right_in,
            &mut to_add_right_out,
            &mut graph_right,
        );
        update_graph(
            source,
            next_state,
            &pair,
            &mut to_add_left_in,
            &mut to_add_left_out,
            &mut graph_left,
        );
        update_graph(
            dest,
            next_state,
            &pair,
            &mut to_add_left_in,
            &mut to_add_left_out,
            &mut graph_left,
        );

        let original_states = merge_info.get(&source).unwrap();
        new_states_set.extend(original_states.iter().map(|s| s.to_owned()));
        let original_states = merge_info.get(&dest).unwrap();
        new_states_set.extend(original_states.iter().map(|s| s.to_owned()));

        merge_info.remove(&source);
        merge_info.remove(&dest);

        //println!("4) Adding state: {} -> {}", next_state, new_states_set.to_str());
        containers.make_set(next_state).unwrap();
        containers.union(&source, &next_state).unwrap();
        containers.union(&dest, &next_state).unwrap();
        //merge_info.insert(next_state, new_states_set);
        let merged_state_ph = containers.find_set(&next_state).unwrap();
        merge_info.insert(merged_state_ph, new_states_set);
        //println!("6) {} -> {}", source, containers.find_set(&source).unwrap());
        //println!("5) {} -> {}", dest, containers.find_set(&dest).unwrap());
        //println!("7) {} -> {}", next_state, containers.find_set(&next_state).unwrap());

        graph_right.extend(to_add_right_in);
        graph_left.extend(to_add_left_in);

        for (state_index, counter) in to_add_right_out {
            if pair.len() == counter {
                graph_right.add_edge(next_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_left_out {
            if pair.len() == counter {
                graph_left.add_edge(next_state, state_index, ());
            }
        }

        //print_graph(&graph_right, &merge_info, format!("steps/right-{i}.gv"));
        //print_graph(&graph_left, &merge_info, format!("steps/left-{i}.gv"));
        //i += 1;

        next_state += 1;
    }

    merge_info
        .into_iter()
        .map(|(_placeholder, states_set)| states_set)
        .collect()
}

/// Updates `graph` edges so that every edge going out or into `old_node` become
/// and edge going out or into `new_node`. More precisely, what happens is that:
/// - All edges of type `(other, old_node)` are removed and `(other, new_node)`
///     is added to `to_add_in`;
/// - All edges of type `(old_node, other)` are removed and `to_add_out` is updated
///     so that it counts how many times and edge that goes into `old_node` is found.
///
/// After the call, it is safe to add every edge in `to_add_in` to `graph`, while
/// for each pair `(source, count)`, and edge `(source, new_node)` can be added
/// to `graph` only if `count == scc.len()`.
///
/// NOTE:
/// * `old_node` is removed from `graph`'s nodes.
/// * At the end of the call, all edges that involved `old_node` will have been removed.
fn update_graph(
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

/*fn update_graph(
    old_nodeindex: NodeIndex,
    new_nodeindex: NodeIndex,
    scc: &Vec<NodeIndex>,
    to_add_in: &mut HashSet<(NodeIndex, NodeIndex)>,
    to_add_out: &mut HashMap<NodeIndex, usize>,
    graph: &mut StableDiGraph<usize, ()>,
) {
    let mut to_remove = HashSet::new();

    for edge in graph.edges_directed(old_nodeindex, Direction::Incoming) {
        let (other, _) = graph.edge_endpoints(edge.id()).unwrap();
        if !scc.contains(&other) {
            to_add_in.insert((other, new_nodeindex));
        }
        to_remove.insert(edge.id());
    }

    for edge in graph.edges_directed(old_nodeindex, Direction::Outgoing) {
        let (_, other) = graph.edge_endpoints(edge.id()).unwrap();
        if !scc.contains(&other) {
            let counter = to_add_out.entry(other).or_default();
            *counter += 1;
        }
        to_remove.insert(edge.id());
    }

    graph.filter_map(
        |_, weight| Some(weight),
        |index, weight| {
            if to_remove.contains(&index) {
                None
            } else {
                Some(weight)
            }
        },
    );
    graph.remove_node(old_nodeindex);
}*/

fn print_graph<S>(
    old_graph: &DiGraphMap<usize, ()>,
    merge_info: &HashMap<PlaceHolder, HashSet<S>>,
    name: String,
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
        name,
        format!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel])),
    );
}

trait MyDisplay {
    fn to_str(&self) -> String;
}

impl<S> MyDisplay for HashSet<S>
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
