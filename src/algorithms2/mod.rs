use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;

use crate::nfa::Nfa;

pub struct Language<S, A>
where
    S: Eq + Hash,
    A: Eq + Hash,
{
    paths: HashMap<S, HashSet<A>>,
}

impl<S, A> Language<S, A>
where
    S: Eq + Hash,
    A: Eq + Hash,
{
    pub fn new() -> Self {
        Language {
            paths: HashMap::new(),
        }
    }

    /// Adds `symbol` to the set of transition symbols that allows
    /// reaching `dest`. Inserts `dest` in the set of reachable states
    /// if it isn't already present.
    pub fn add(&mut self, dest: S, symbol: A) {
        self.paths.entry(dest).or_default().insert(symbol);
    }

    /// Returns the set of symbols that allows reaching `dest`.
    pub fn get(&self, dest: &S) -> Option<&HashSet<A>> {
        self.paths.get(dest)
    }

    /// Checks if there are paths that can reach `state`.
    pub fn has(&self, state: &S) -> bool {
        self.paths.contains_key(state)
    }
}

pub struct Languages<S, A>
where
    S: Eq + Hash,
    A: Eq + Hash,
{
    langs: HashMap<S, Language<S, A>>,
}

impl<S, A> Languages<S, A>
where
    S: Eq + Hash,
    A: Eq + Hash,
{
    pub fn new() -> Self {
        Languages {
            langs: HashMap::new(),
        }
    }

    /// Adds the `symbol` to the set of transition symbols that allows
    /// reaching `dest` from `source`. Both `source` and `dest` are inserted
    /// in the set of source and destination states if they aren't already
    /// present.
    pub fn add(&mut self, source: S, dest: S, symbol: A) {
        self.langs
            .entry(source)
            .or_insert(Language::new())
            .add(dest, symbol);
    }

    /// Adds en empty language for `state` if none has been registered yet.
    pub fn add_empty(&mut self, state: S) {
        self.langs.entry(state).or_insert(Language::new());
    }

    /// Returns the language associated to `source` state.
    pub fn get(&self, source: &S) -> Option<&Language<S, A>> {
        self.langs.get(source)
    }

    /// Checks if there is a language for `state`.
    pub fn has(&self, state: &S) -> bool {
        self.langs.contains_key(state)
    }
}

impl<S, A> Display for Languages<S, A>
where
    S: Eq + Hash + Display,
    A: Eq + Hash + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut output = String::new();

        for (state, lang) in &self.langs {
            output.push_str(&format!("{}: ", &state));

            let mut loop_str = String::new();
            if let Some(symbols) = lang.get(state) {
                loop_str.push('(');

                for symbol in symbols {
                    loop_str.push_str(&format!("{}+", symbol));
                }

                loop_str.pop();
                loop_str.push_str(")*");
            }

            for (state, symbols) in &lang.paths {
                output.push_str(&loop_str);
                let mut symbols_str = String::new();
                symbols_str.push('(');
                for symbol in symbols {
                    symbols_str.push_str(&format!("{}+", symbol));
                }
                symbols_str.pop();
                symbols_str.push(')');

                if symbols.len() == 1 {
                    output.push_str(&symbols_str[1..symbols_str.len() - 1]);
                } else {
                    output.push_str(&symbols_str);
                }
                output.push_str(&format!("L{}+", state));
            }
            output.pop();
            output.push('\n');
        }

        f.write_str(&output)
    }
}

pub fn calc_right_languages<S, A>(nfa: &Nfa<S, A>) -> Languages<S, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut languages = Languages::new();

    for source in nfa.states() {
        //languages.add_empty(source.to_owned());
        for symbol in nfa.symbols() {
            let reachable_states = nfa.eval_symbol_from_state(source, symbol).unwrap();
            for dest in reachable_states {
                languages.add(source.to_owned(), dest.to_owned(), symbol.to_owned());
            }
        }

        // This way, every state has a language so, less checks are necessary
        if !languages.has(source) {
            languages.add_empty(source.to_owned());
        }
    }

    languages
}

pub fn calc_relation<S, A>(nfa: &Nfa<S, A>, right_languages: &Languages<S, A>) -> HashSet<(S, S)>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut rel = HashSet::new();
    let mut checked = HashSet::new();

    for p in nfa.states() {
        for q in nfa.states() {
            calc_relation_aux(&right_languages, p, q, &mut checked, &mut rel);
        }
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

/// Checks if the right language of `p` is a subset of `q`'s right language.
/// If so, `(p, q)` is added to `rel` as well as every pair `(p1, q1)` of
/// states reached by `p` and `q` that fit the relationship.
fn calc_relation_aux<S, A>(
    right_languages: &Languages<S, A>,
    p: &S,
    q: &S,
    checked: &mut HashSet<(S, S)>,
    rel: &mut HashSet<(S, S)>,
) where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    if p == q || checked.contains(&(p.to_owned(), q.to_owned())) {
        return;
    }

    checked.insert((p.clone(), q.clone()));

    for (p_reached, p_syms) in &right_languages.get(p).unwrap().paths {
        let mut found = false;

        for (q_reached, q_syms) in &right_languages.get(q).unwrap().paths {
            calc_relation_aux(right_languages, p_reached, q_reached, checked, rel);
            if p_reached != q_reached
                && !rel.contains(&(p_reached.to_owned(), q_reached.to_owned()))
            {
                continue;
            }

            let diff_syms = p_syms.difference(q_syms).collect::<Vec<_>>();
            if diff_syms.len() > 0 {
                continue;
            }

            found = true;
        }

        // `p_reached` cannot be reached by `q`, or none of the states reached
        // by `q` can contain `p_reached`'s language, or `p` can reach `p_reached`
        // with more symbols than what `q` uses to reach states similar to `p_reached`
        if !found {
            return;
        }
    }

    rel.insert((p.to_owned(), q.to_owned()));
}
