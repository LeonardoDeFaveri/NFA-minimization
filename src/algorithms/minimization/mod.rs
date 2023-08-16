use disjoint_hash_set::DisjointHashSet;
use petgraph::prelude::DiGraphMap;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::algorithms::minimization::utils::*;

pub mod eq;
mod utils;

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
    S: Eq + Hash + Clone,
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

fn get_biggest_scc(sccs: &Vec<Vec<PlaceHolder>>) -> &Vec<PlaceHolder> {
    sccs.iter().max_by(|a, b| a.len().cmp(&b.len())).unwrap()
}

/// Builds 3 depency graphs: left, right, preorder. While there is at least one
/// non trivial Strongly Connected Component, merges the states in that component
/// into a single state and updates all the graphs.
pub fn preorders_with_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
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

/// Merges states using rule 3, then creates two dependency graphs, one for left
/// and one for right preorders. Further reduction are carried out merging every
/// time the biggest Strongly Connected Component of either of dependency graph.
///
/// ### Complexity
/// O(S*N(N+E)) where S is the maximum number of SCC that there can be (must be
/// estimated in some way, idea: N/2 SCCs)
pub fn preorders_with_sccs_pre<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
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
    // In the worst every SCC of the 3 depency graphs includes different states,
    // so the loop executes one time for each SCC
    loop {
        let sccs_pre = petgraph::algo::kosaraju_scc(&graph_pre);
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        let mut sccs = [
            (get_biggest_scc(&sccs_pre), &mut graph_pre),
            (get_biggest_scc(&sccs_right), &mut graph_right),
            (get_biggest_scc(&sccs_left), &mut graph_left),
        ];
        // While `sccs_pre` biggest SCC is non trivial, merges it.
        if sccs[0].0.len() == 1 {
            sccs.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
        }
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

        // For sure this loop is limited by the number of states in the original
        // NFA because there might be one giant SCC holding every state.
        // Putting all together, this loop has a complexity of O(N(N+E))
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

            // Trivially, this is limited by the number of states in the original
            // NFA
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

pub fn preorders_with_sccs_left<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
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
    // In the worst every SCC of the 3 depency graphs includes different states,
    // so the loop executes one time for each SCC
    loop {
        let sccs_pre = petgraph::algo::kosaraju_scc(&graph_pre);
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        let mut sccs = [
            (get_biggest_scc(&sccs_left), &mut graph_left),
            (get_biggest_scc(&sccs_pre), &mut graph_pre),
            (get_biggest_scc(&sccs_right), &mut graph_right)
        ];
        // While `sccs_left` biggest SCC is non trivial, merges it.
        if sccs[0].0.len() == 1 {
            sccs.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
        }
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

        // For sure this loop is limited by the number of states in the original
        // NFA because there might be one giant SCC holding every state.
        // Putting all together, this loop has a complexity of O(N(N+E))
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

            // Trivially, this is limited by the number of states in the original
            // NFA
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

pub fn preorders_with_sccs_right<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone,
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
    // In the worst every SCC of the 3 depency graphs includes different states,
    // so the loop executes one time for each SCC
    loop {
        let sccs_pre = petgraph::algo::kosaraju_scc(&graph_pre);
        let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
        let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);

        let mut sccs = [
            (get_biggest_scc(&sccs_right), &mut graph_right),
            (get_biggest_scc(&sccs_pre), &mut graph_pre),
            (get_biggest_scc(&sccs_left), &mut graph_left),
        ];
        // While `sccs_right` biggest SCC is non trivial, merges it.
        if sccs[0].0.len() == 1 {
            sccs.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
        }
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

        // For sure this loop is limited by the number of states in the original
        // NFA because there might be one giant SCC holding every state.
        // Putting all together, this loop has a complexity of O(N(N+E))
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

            // Trivially, this is limited by the number of states in the original
            // NFA
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
