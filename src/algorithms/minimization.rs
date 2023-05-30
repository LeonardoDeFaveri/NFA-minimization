use disjoint_hash_set::DisjointHashSet;
use std::{
    collections::{HashMap, HashSet},
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
enum Priority {
    High = 3,
    Medium = 2,
    Low = 1,
    Zero = 0,
}

/// Scores state pairs and merge states using pairs in a decresing order of
/// scores.
pub fn preorders_with_scores<S>(
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

    let mut sorted_pairs: priority_queue::PriorityQueue<(&S, &S), Priority> =
        priority_queue::PriorityQueue::new();

    for ((p, q), (right, left, has_loops)) in rel_table {
        let mut score = Priority::Zero;
        let rev_pair = (q.clone(), p.clone());
        if let Some((rev_right, rev_left, _)) = rel_table.get(&rev_pair) {
            if *right && *rev_right {
                score = Priority::Medium;
            }
            if *left && *rev_left {
                score = Priority::Low;
            }
        }
        if *right && *left && !*has_loops {
            score = Priority::High;
        }

        if score != Priority::Zero {
            //if sorted_pairs.get(&(&q, &p)).is_none() {
            sorted_pairs.push((&p, &q), score);
            //}
        }
    }

    let mut to_forget_right: HashSet<(S, S)> = HashSet::new();
    let mut to_forget_left: HashSet<(S, S)> = HashSet::new();

    for ((p, q), priority) in sorted_pairs {
        let pair = (p.clone(), q.clone());
        let rev_pair = (q.clone(), p.clone());

        if to_forget_left.contains(&pair) || to_forget_right.contains(&pair) {
            continue;
        }

        match priority {
            Priority::High => {
                merge_info.link(p.clone(), q.clone());
            },
            Priority::Medium if !to_forget_right.contains(&rev_pair) => {
                merge_info.link(p.clone(), q.clone());
                for (a, s) in left_rel {
                    if a == q && !left_rel.contains(&(p.clone(), s.clone())) {
                        to_forget_left.insert((q.clone(), s.clone()));
                    }
                }
            },
            Priority::Low if !to_forget_left.contains(&rev_pair) => {
                merge_info.link(p.clone(), q.clone());
                for (a, s) in right_rel {
                    if a == q && !right_rel.contains(&(p.clone(), s.clone())) {
                        to_forget_right.insert((q.clone(), s.clone()));
                    }
                }
            },
            _ => {}
        }
    }

    merge_info.sets().collect()
}
