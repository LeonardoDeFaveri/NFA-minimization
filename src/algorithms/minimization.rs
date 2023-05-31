use disjoint_hash_set::DisjointHashSet;
use petgraph::Graph;
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

#[derive(PartialEq, PartialOrd, Eq, Ord)]
enum MergeReason {
    Preorder = 3,
    RightEq = 2,
    LeftEq = 1,
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
            //if sorted_pairs.get(&(&q, &p)).is_none() {
            sorted_pairs.push((p.clone(), q.clone()), reason);
            //}
        }
    }

    let mut to_forget_right: HashSet<(S, S)> = HashSet::new();
    let mut to_forget_left: HashSet<(S, S)> = HashSet::new();

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

pub fn preorders_with_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
    right_rel: &HashSet<(S, S)>,
    left_rel: &HashSet<(S, S)>,
) -> Vec<HashSet<S>>
where
    S: Eq + Hash + Clone + Display,
{
    let mut graph: Graph<S, ()> = Graph::new();
    let mut node_indexes = HashMap::new();

    for s in states {
        node_indexes.insert(s.clone(), graph.add_node(s.clone()));
    }

    for ((p, q), _) in rel_table {
        let p_index = node_indexes.get(p).unwrap();
        //.entry(p.clone())
        //.or_insert_with(|| graph.add_node(p.clone()))
        //.clone();
        let q_index = node_indexes.get(q).unwrap();
        //.entry(q.clone())
        //.or_insert_with(|| graph.add_node(q.clone()))
        //.clone();

        graph.add_edge(*p_index, *q_index, ());
    }

    let sccs = petgraph::algo::kosaraju_scc(&graph);

    let mut merge_info = vec![];
    for scc in &sccs {
        let mut set = HashSet::new();
        for node_index in scc {
            set.insert(graph[*node_index].clone());
        }
        merge_info.push(set);
    }

    merge_info
}
