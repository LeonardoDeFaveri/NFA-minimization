use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Debug, Display, Write},
    hash::Hash,
};

use crate::nfa::Nfa;

pub struct Path<S, A> {
    pub transition_symbol: A,
    pub reached_state: S,
}

impl<S, A> Path<S, A> {
    pub fn new(symbol: A, state: S) -> Path<S, A> {
        Path {
            transition_symbol: symbol,
            reached_state: state,
        }
    }
}

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
    pub fn new() -> Language<S, A> {
        Language {
            loops: HashSet::new(),
            paths: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, symbol: A) {
        self.loops.insert(symbol);
    }

    pub fn push_path(&mut self, path: Path<S, A>) {
        self.paths.push(path);
    }

    pub fn loops(&self) -> &HashSet<A> {
        &self.loops
    }

    pub fn paths(&self) -> &Vec<Path<S, A>> {
        &self.paths
    }

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

struct WaitingContext<'a, S, A> {
    state: S,
    missing_loops: HashSet<&'a A>,
}

impl<'a, S, A> WaitingContext<'a, S, A> {
    pub fn new(state: S, missing_loops: HashSet<&'a A>) -> Self {
        WaitingContext {
            state,
            missing_loops,
        }
    }
}

pub fn calc_relation<S, A>(
    nfa: &Nfa<S, A>,
    language: &HashMap<S, Language<S, A>>,
) -> HashSet<(S, S)>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut rel = HashSet::new();
    let mut checked = HashSet::new();

    for state in nfa.states() {
        calc_relation_aux(nfa, &language, state, &mut checked, &mut rel);
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

fn calc_relation_aux<S, A>(
    nfa: &Nfa<S, A>,
    language: &HashMap<S, Language<S, A>>,
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
    let state_lang = language.get(state).unwrap();

    let mut non_suitable_container = HashSet::new();
    non_suitable_container.insert(state.to_owned());
    for state in nfa.states() {
        if language.get(state).unwrap().is_empty() {
            non_suitable_container.insert(state.to_owned());
        }
    }

    // First cleaning
    for path in state_lang.paths() {
        for other in nfa.states() {
            if non_suitable_container.contains(other) {
                continue;
            }

            // Checks if there's at least one of other's path that contains path
            let mut found = false;
            let other_lang = language.get(other).unwrap();
            for other_path in other_lang.paths() {
                if path.transition_symbol != other_path.transition_symbol {
                    continue;
                }

                calc_relation_aux(nfa, language, &other_path.reached_state, checked, rel);
                if path.reached_state != other_path.reached_state
                    && !rel
                        .contains(&(path.reached_state.clone(), other_path.reached_state.clone()))
                {
                    continue;
                }

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

    // Second cleaning
    let mut waiting_contexts = Vec::new();

    for other in nfa.states() {
        if non_suitable_container.contains(other) {
            continue;
        }

        let other_lang = language.get(other).unwrap();
        let missing: HashSet<&A> = state_lang.loops().difference(other_lang.loops()).collect();

        if missing.is_empty() {
            rel.insert((state.to_owned(), other.to_owned()));
        } else {
            waiting_contexts.push(WaitingContext::new(other, missing));
        }
    }

    for context in waiting_contexts {
        let other_lang = language.get(context.state).unwrap();
        let mut to_solve_count = context.missing_loops.len();

        for symbol in context.missing_loops {
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

        if to_solve_count == 0 {
            rel.insert((state.to_owned(), context.state.to_owned()));
        }
    }
}
