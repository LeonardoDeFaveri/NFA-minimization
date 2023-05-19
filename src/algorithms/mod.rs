use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Debug, Display, Write},
    hash::Hash,
};

pub mod minimization;

use crate::nfa::Nfa;

pub struct Path<S, A> {
    pub transition_symbol: A,
    pub reached_state: S,
}

impl<S, A> Path<S, A> {
    pub fn new(symbol: A, state: S) -> Self {
        Path {
            transition_symbol: symbol,
            reached_state: state,
        }
    }
}

/// Represents the language recognized from a certain state.
/// It is made up of all the words made self-loops on the state followed
/// by out-transitions towards some other state and the language of those
/// states. The pair (out_transition, reached_state) is called `path`.
pub struct Language<S, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    loops: HashSet<A>,
    paths: Vec<Path<S, A>>,
}

impl<S, A> Language<S, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    pub fn new() -> Self {
        Language {
            loops: HashSet::new(),
            paths: Vec::new(),
        }
    }

    /// Adds `symbol` to the set of symbols for which there is a self-loop
    pub fn push_loop(&mut self, symbol: A) {
        self.loops.insert(symbol);
    }

    /// Adds `path` to the set of paths
    pub fn push_path(&mut self, path: Path<S, A>) {
        self.paths.push(path);
    }

    pub fn loops(&self) -> &HashSet<A> {
        &self.loops
    }

    pub fn paths(&self) -> &Vec<Path<S, A>> {
        &self.paths
    }

    /// Returns `true` if the language is empty. So, if there's neither
    /// a self-loop  nor a path.
    pub fn is_empty(&self) -> bool {
        self.loops.is_empty() && self.paths.is_empty()
    }
}

impl<S, A> Display for Language<S, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut loop_str = String::new();
        if !self.loops.is_empty() {
            loop_str.push('(');
            for symbol in &self.loops {
                loop_str.push_str(&format!("{}", *symbol));
                loop_str.push('+');
            }
            loop_str.pop();
            loop_str.push_str(")*");
        }

        for (i, path) in self.paths.iter().enumerate() {
            f.write_fmt(format_args!(
                "{}{}L{}",
                loop_str, path.transition_symbol, path.reached_state
            ))?;
            if i < self.paths.len() - 1 {
                f.write_char('+')?;
            }
        }

        Ok(())
    }
}

/// Calculates the right language of an nfa. Takes as input the revere nfa.
pub fn calc_right_language<S, A>(rev_nfa: &Nfa<S, A>) -> HashMap<S, Language<S, A>>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut languages = HashMap::new();
    let mut added = HashSet::new();
    for state in rev_nfa.states() {
        languages.insert(state.to_owned(), Language::new());
    }

    let mut states = VecDeque::new();
    for state in rev_nfa.initial_states() {
        states.push_back(state);
        added.insert(state.to_owned());
    }

    while let Some(state) = states.pop_front() {
        for symbol in rev_nfa.symbols() {
            let reached_states = rev_nfa.eval_symbol_from_state(state, symbol).unwrap();

            for other_state in reached_states {
                if *other_state == *state {
                    languages
                        .get_mut(state)
                        .unwrap()
                        .push_loop(symbol.to_owned());
                } else {
                    let path = Path::new(symbol.to_owned(), state.to_owned());
                    languages.get_mut(other_state).unwrap().push_path(path);
                }

                if !added.contains(other_state) {
                    added.insert(other_state.to_owned());
                    states.push_back(other_state);
                }
            }
        }
    }

    languages
}

/// Given an nfa and the relative language (either right or left), calculates
/// the set of pairs (s1, s2) for which the language of s1 is a subset of those
/// of s2.
pub fn calc_relation<S, A>(
    nfa: &Nfa<S, A>,
    right_languages: &HashMap<S, Language<S, A>>,
) -> HashSet<(S, S)>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut rel = HashSet::new();
    let mut checked = HashSet::new();

    for state in nfa.states() {
        calc_relation_aux(nfa, &right_languages, state, &mut checked, &mut rel);
    }

    for final_state in nfa.final_states() {
        for state in nfa.states() {
            if !nfa.is_final(state).unwrap() {
                rel.remove(&(final_state.to_owned(), state.to_owned()));
            }
        }
    }

    rel
}

/// Given a state `state` populates `rel` with all the pairs `(state, o)`
/// for which `o` contains `state`.
fn calc_relation_aux<S, A>(
    nfa: &Nfa<S, A>,
    right_languages: &HashMap<S, Language<S, A>>,
    state: &S,
    checked: &mut HashSet<S>,
    rel: &mut HashSet<(S, S)>,
) where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    if checked.contains(state) {
        return;
    }

    checked.insert(state.to_owned());

    // Initialization
    let state_lang = right_languages.get(state).unwrap();

    let mut non_suitable_container = HashSet::new();
    non_suitable_container.insert(state.to_owned());
    for other in nfa.states() {
        if right_languages.get(other).unwrap().is_empty() {
            non_suitable_container.insert(other.to_owned());
        }
    }

    // First cleaning: removing all states that clearly cannot be containers
    // for state
    for path in state_lang.paths() {
        for other in nfa.states() {
            if non_suitable_container.contains(other) {
                continue;
            }

            // Checks if there's at least one of other's path that contains path
            let mut found = false;
            let other_lang = right_languages.get(other).unwrap();
            for other_path in other_lang.paths() {
                if path.transition_symbol != other_path.transition_symbol {
                    continue;
                }

                calc_relation_aux(nfa, right_languages, &path.reached_state, checked, rel);
                if path.reached_state != other_path.reached_state
                    && !rel
                        .contains(&(path.reached_state.clone(), other_path.reached_state.clone()))
                {
                    continue;
                }

                found = true;
            }

            // Solution to triangular problem
            // If I'm reaching a state with a transition on a symbol for which
            // the reached state has a self-loop, the path is included in the loop
            if path.reached_state == *other && other_lang.loops.contains(&path.transition_symbol) {
                found = true;
            }

            if !found {
                non_suitable_container.insert(other.to_owned());
                if non_suitable_container.len() == nfa.states().len() {
                    // No state can be a container for `state`, so nothing
                    // else can be found.
                    return;
                }
            }
        }
    }

    // Second cleaning: for each state that could be a container, checks if
    // state's self-loops corresponds to either self-loops of that other state
    // or out-transitions to states that contains state
    let mut waiting_contexts = Vec::new();
    for other in nfa.states() {
        if non_suitable_container.contains(other) {
            continue;
        }

        let other_lang = right_languages.get(other).unwrap();
        let missing: HashSet<&A> = state_lang.loops().difference(other_lang.loops()).collect();

        if missing.is_empty() {
            // Every self-loop on state, is also a self-loop on other so,
            // (state, other) can be added to rel without any doubt
            rel.insert((state.to_owned(), other.to_owned()));
        } else {
            // There is at least on self-loop on state that doesn't correspond
            // to a self-loop on other, so further checks are necessary
            waiting_contexts.push((other, missing)) //Context::new(other, missing));
        }
    }

    // For each pair (reached_state, missing_self_loops) checks if reached_state
    // has an out-transition towards a state that containes state for each
    // symbol in missing_self_loops
    for (reached_state, missing_self_loops) in waiting_contexts {
        let other_lang = right_languages.get(reached_state).unwrap();
        let mut to_solve_count = missing_self_loops.len();

        for symbol in missing_self_loops {
            for other_path in other_lang.paths() {
                if other_path.transition_symbol == *symbol
                    && (*state == other_path.reached_state
                        || rel.contains(&(state.to_owned(), other_path.reached_state.to_owned())))
                {
                    to_solve_count -= 1;
                    break;
                }
            }
        }

        // For each symbol in missing_self_loops there's an out-transition
        // from reached_state to another state that can contain state, so
        // reached state can containe state, too
        if to_solve_count == 0 {
            rel.insert((state.to_owned(), reached_state.to_owned()));
        }
    }
}

/// Given an nfa and both the right and left languages of its states, creates
/// a table that associates every pair (s1, s2) to a triple of booleans
/// `(right, left, loop)`.
/// - `right`: `true` if `(s1, s2)` is in `right_rel`;
/// - `left`: `true` if `(s1, s2)` is in `left_rel`;
/// - `loop`: `true` if there is a path that starts in `s1` and returns to it,
/// forming a cycle;
pub fn initialize_rel_table<S, A>(
    nfa: &Nfa<S, A>,
    right_rel: &HashSet<(S, S)>,
    left_rel: &HashSet<(S, S)>,
) -> HashMap<(S, S), (bool, bool, bool)>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut table = HashMap::new();
    let loops = find_if_loops(&nfa);

    for (p, q) in right_rel {
        let has_loop = loops.contains(&p);
        table.insert((p.clone(), q.clone()), (true, false, has_loop));
    }

    for (p, q) in left_rel {
        if table.contains_key(&(p.clone(), q.clone())) {
            let mut value = table.get_mut(&(p.clone(), q.clone())).unwrap();
            value.1 = true;
        } else {
            let has_loop = loops.contains(&p);
            table.insert((p.clone(), q.clone()), (false, true, has_loop));
        }
    }

    table
}

/// Given an nfa returns a set of all the states for which exists a path
/// that begins and ends in them.
fn find_if_loops<S, A>(nfa: &Nfa<S, A>) -> HashSet<S>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut result = HashSet::new();

    let mut discovery_time = HashMap::new();
    let mut finish_time = HashMap::new();

    for state in nfa.states() {
        discovery_time.insert(state, 0);
        finish_time.insert(state, 0);
    }

    for state in nfa.initial_states() {
        let mut time = 0;
        find_if_loops_aux(
            nfa,
            state,
            &mut result,
            &mut time,
            &mut discovery_time,
            &mut finish_time,
        );
    }

    result
}

fn find_if_loops_aux<'a, S, A>(
    nfa: &'a Nfa<S, A>,
    state: &'a S,
    loops: &mut HashSet<S>,
    time: &mut u64,
    dt: &mut HashMap<&'a S, u64>,
    ft: &mut HashMap<&'a S, u64>,
) where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    *time += 1;
    dt.insert(state, *time);
    let state_dt = *time;

    for symbol in nfa.symbols() {
        let result = nfa.eval_symbol_from_state(state, symbol);
        if result.is_err() {
            continue;
        }

        for other in result.unwrap() {
            let o_dt = dt.get(other).unwrap();
            if *o_dt > 0 {
                let o_ft = ft.get(other).unwrap();
                if state_dt >= *o_dt && *o_ft == 0 {
                    loops.insert(other.to_owned());
                }
            } else {
                find_if_loops_aux(nfa, other, loops, time, dt, ft);
            }
        }
    }

    *time += 1;
    ft.insert(state, *time);
}

/// Ginen a vector of sets of statea, creates a new nfa in which
/// each set of states is associated to one state.
pub fn build_minimized<S, A>(nfa: &Nfa<S, A>, new_states: &Vec<HashSet<S>>) -> Nfa<usize, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut new_nfa = Nfa::new();
    let mut containers = HashMap::new();

    // Adds states to `new_nfa`
    for (i, set) in new_states.iter().enumerate() {
        new_nfa.add_state(i);

        let mut is_initial = false;
        let mut is_final = false;

        for state in set {
            containers.insert(state.clone(), i);
            is_initial = nfa.is_initial(&state).unwrap();
            is_final = nfa.is_final(&state).unwrap();
        }

        if is_initial {
            let _ = new_nfa.add_initial_state(i);
        }
        if is_final {
            let _ = new_nfa.add_final_state(i);
        }
    }

    // Adds symbols to `new_nfa`
    for a in nfa.symbols() {
        new_nfa.add_symbol(a.clone());
    }

    // Adds transitions to `new_nfa`
    for p in nfa.states() {
        for a in nfa.symbols() {
            let reachables = nfa.eval_symbol_from_state(p, a).unwrap();
            for q in reachables {
                let _ = new_nfa.add_transition(containers[p], a.clone(), containers[q]);
            }
        }
    }

    new_nfa
}
