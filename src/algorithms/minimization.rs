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
use union_find_rs::prelude::*;

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

/// Type used to identify states in depency graphs.
type PlaceHolder = usize;

/// Builds 3 depency graphs: left, right, preorder. While there is at least one
/// non trivial Strongly Connected Component, merges the states in that component
/// into a single state and updates all the graphs.
pub fn preorders_with_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone + Display,
{
    let mut all_ph: HashMap<&S, PlaceHolder> = HashMap::new();
    let mut graph_pre: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_right: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_left: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();

    let mut merge_info: HashMap<PlaceHolder, HashSet<S>> = HashMap::new();

    for (ph, state) in states.iter().enumerate() {
        graph_pre.add_node(ph);
        graph_right.add_node(ph);
        graph_left.add_node(ph);
        all_ph.insert(state, ph);

        let mut set = HashSet::new();
        set.insert(state.clone());
        merge_info.insert(ph, set);
    }

    for ((p, q), (right, left, has_loop)) in rel_table {
        let p_ph = all_ph[&p];
        let q_ph = all_ph[&q];

        if *right {
            graph_right.add_edge(p_ph, q_ph, ());
        }
        if *left {
            graph_left.add_edge(p_ph, q_ph, ());
        }
        if *right && *left && !*has_loop {
            graph_pre.add_edge(p_ph, q_ph, ());
            graph_pre.add_edge(q_ph, p_ph, ());
        }
    }

    let mut new_state = states.len();
    loop {
        let sccs_pre = petgraph::algo::kosaraju_scc(&graph_pre);
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        let mut sccs = [
            (get_biggest_scc(&sccs_pre), &mut graph_pre),
            (get_biggest_scc(&sccs_right), &mut graph_right),
            (get_biggest_scc(&sccs_left), &mut graph_left),
        ];
        sccs.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
        let [(scc, graph), (_, other_graph1), (_, other_graph2)] = sccs;

        if scc.len() == 1 {
            break;
        }

        graph.add_node(new_state);
        other_graph1.add_node(new_state);
        other_graph2.add_node(new_state);

        let mut new_states_set = HashSet::new();
        let mut to_add_graph_in = HashSet::new();
        let mut to_add_other1_in = HashSet::new();
        let mut to_add_other2_in = HashSet::new();
        let mut to_add_graph_out = HashMap::new();
        let mut to_add_other1_out = HashMap::new();
        let mut to_add_other2_out = HashMap::new();

        for old_state in scc {
            update_graph(
                *old_state,
                new_state,
                scc,
                &mut to_add_graph_in,
                &mut to_add_graph_out,
                graph,
            );
            update_graph(
                *old_state,
                new_state,
                scc,
                &mut to_add_other1_in,
                &mut to_add_other1_out,
                other_graph1,
            );
            update_graph(
                *old_state,
                new_state,
                scc,
                &mut to_add_other2_in,
                &mut to_add_other2_out,
                other_graph2,
            );

            let original_states = merge_info.get(&old_state).unwrap();
            new_states_set.extend(original_states.iter().map(|s| s.to_owned()));
            merge_info.remove(&old_state);
        }
        merge_info.insert(new_state, new_states_set);

        graph.extend(to_add_graph_in);
        other_graph1.extend(to_add_other1_in);
        other_graph2.extend(to_add_other2_in);

        for (state_index, counter) in to_add_graph_out {
            if scc.len() == counter {
                graph.add_edge(new_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_other1_out {
            if scc.len() == counter {
                other_graph1.add_edge(new_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_other2_out {
            if scc.len() == counter {
                other_graph2.add_edge(new_state, state_index, ());
            }
        }

        new_state += 1;
    }

    merge_info
        .into_iter()
        .map(|(_placeholder, states_set)| states_set)
        .collect()
}

fn get_biggest_scc(sccs: &Vec<Vec<PlaceHolder>>) -> &Vec<PlaceHolder> {
    sccs.iter().max_by(|a, b| a.len().cmp(&b.len())).unwrap()
}

/// Merges states using rule 3, then creates two dependency graphs, one for left
/// and one for right preorders. Further reduction are carried out merging every
/// time the biggest Strongly Connected Component of either of dependency graph.
pub fn preorders_with_sccs2<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
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

    // Merges states using rule 3
    for ((p, q), (right, left, has_loop)) in rel_table {
        if *right && *left && !*has_loop {
            let p_ph = containers.find_set(&all_ph[&p]).unwrap();
            let q_ph = containers.find_set(&all_ph[&q]).unwrap();

            if p_ph != q_ph {
                containers.union(&p_ph, &q_ph).unwrap();
                let new_parent = containers.find_set(&p_ph).unwrap();

                let (other_states, other_ph) = if new_parent == p_ph {
                    let states = merge_info
                        .get(&q_ph)
                        .unwrap()
                        .iter()
                        .map(|s| s.to_owned())
                        .collect::<Vec<_>>();
                    (states, q_ph)
                } else {
                    let states = merge_info
                        .get(&p_ph)
                        .unwrap()
                        .iter()
                        .map(|s| s.to_owned())
                        .collect::<Vec<_>>();
                    (states, p_ph)
                };

                let parent_states = merge_info.get_mut(&new_parent).unwrap();
                parent_states.extend(other_states);
                merge_info.remove(&other_ph);
            }
        }
    }

    // Adds edges to dependency graphs
    for ((p, q), (right, left, _)) in rel_table {
        let p_ph = containers.find_set(&all_ph[&p]).unwrap();
        let q_ph = containers.find_set(&all_ph[&q]).unwrap();

        if p_ph == q_ph {
            continue;
        }
        if *right && !graph_right.contains_edge(p_ph, q_ph) {
            graph_right.add_edge(p_ph, q_ph, ());
        }
        if *left && !graph_left.contains_edge(p_ph, q_ph) {
            graph_left.add_edge(p_ph, q_ph, ());
        }
    }

    let mut new_state = states.len();
    //let mut i = 0;

    // MERGES STATES USING RULES 1 AND 2!
    // Merges every non trivial SCC. After this loop ends, no cicle is left in
    // any dependency graph
    loop {
        // Calculates SCCs for both dependency graphs
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        //print_graph(&graph_right, &merge_info, format!("steps/right-{i}.gv"));
        //print_graph(&graph_left, &merge_info, format!("steps/left-{i}.gv"));
        //i += 1;

        let biggest_right_scc = get_biggest_scc(&sccs_right);
        let biggest_left_scc = get_biggest_scc(&sccs_left);

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
        graph.add_node(new_state);
        other_graph.add_node(new_state);
        containers.make_set(new_state).unwrap();

        let mut new_states_set = HashSet::new();
        let mut to_add_graph_in = HashSet::new();
        let mut to_add_other_in = HashSet::new();
        let mut to_add_graph_out = HashMap::new();
        let mut to_add_other_out = HashMap::new();

        for old_state in biggest_scc {
            update_graph(
                *old_state,
                new_state,
                &biggest_scc,
                &mut to_add_graph_in,
                &mut to_add_graph_out,
                graph,
            );
            update_graph(
                *old_state,
                new_state,
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
            containers.union(old_state, &new_state).unwrap();
        }

        merge_info.insert(new_state, new_states_set);

        graph.extend(to_add_graph_in);
        other_graph.extend(to_add_other_in);

        for (state_index, counter) in to_add_graph_out {
            if biggest_scc.len() == counter {
                graph.add_edge(new_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_other_out {
            if biggest_scc.len() == counter {
                other_graph.add_edge(new_state, state_index, ());
            }
        }

        new_state += 1;
    }

    // MERGES STATES USING RULE 3!
    // All edges that exists in both graphs, indicated a preorder of type 3
    /*let intersection = graph_right
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
        graph_right.add_node(new_state);
        graph_left.add_node(new_state);

        let mut new_states_set = HashSet::new();
        let mut to_add_right_in = HashSet::new();
        let mut to_add_left_in = HashSet::new();
        let mut to_add_right_out = HashMap::new();
        let mut to_add_left_out = HashMap::new();

        update_graph(
            source,
            new_state,
            &pair,
            &mut to_add_right_in,
            &mut to_add_right_out,
            &mut graph_right,
        );
        update_graph(
            dest,
            new_state,
            &pair,
            &mut to_add_right_in,
            &mut to_add_right_out,
            &mut graph_right,
        );
        update_graph(
            source,
            new_state,
            &pair,
            &mut to_add_left_in,
            &mut to_add_left_out,
            &mut graph_left,
        );
        update_graph(
            dest,
            new_state,
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
        containers.make_set(new_state).unwrap();
        containers.union(&source, &new_state).unwrap();
        containers.union(&dest, &new_state).unwrap();

        let merged_state_ph = containers.find_set(&new_state).unwrap();
        merge_info.insert(merged_state_ph, new_states_set);

        //println!("6) {} -> {}", source, containers.find_set(&source).unwrap());
        //println!("5) {} -> {}", dest, containers.find_set(&dest).unwrap());
        //println!("7) {} -> {}", next_state, containers.find_set(&next_state).unwrap());

        graph_right.extend(to_add_right_in);
        graph_left.extend(to_add_left_in);

        for (state_index, counter) in to_add_right_out {
            if pair.len() == counter {
                graph_right.add_edge(new_state, state_index, ());
            }
        }

        for (state_index, counter) in to_add_left_out {
            if pair.len() == counter {
                graph_left.add_edge(new_state, state_index, ());
            }
        }

        //print_graph(&graph_right, &merge_info, format!("steps/right-{i}.gv"));
        //print_graph(&graph_left, &merge_info, format!("steps/left-{i}.gv"));
        //i += 1;

        new_state += 1;
    }*/

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

/// Printrs `old_graph` using real states name as node label. The output is
/// written `file_name`.
fn print_graph<S>(
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
