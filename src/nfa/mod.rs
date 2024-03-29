use graphviz_rust::dot_structures::{Attribute, EdgeTy, GraphAttributes, Id, Stmt, Vertex};
use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    str::FromStr,
};

#[derive(Debug)]
pub enum NfaErrors<S, A> {
    InvalidState(S),
    InvalidSymbol(A),
}

/// Implements an epsilon-free NFA.
/// S: data type for state representation
/// A: data type for transition symbol
#[derive(Debug)]
pub struct Nfa<S, A>
where
    S: Eq + Hash + Clone + Debug,
    A: Eq + Hash + Clone + Debug,
{
    /// States
    states: HashSet<S>,
    /// Vocabulary
    symbols: HashSet<A>,
    /// Transition function
    transitions: HashMap<S, HashMap<A, HashSet<S>>>,
    /// Set of initial states
    initial_states: HashSet<S>,
    /// Set of fianl states
    final_states: HashSet<S>,
}

#[allow(dead_code)]
impl<S, A> Nfa<S, A>
where
    S: Eq + Hash + Clone + Debug,
    A: Eq + Hash + Clone + Debug,
{
    /// Creates an empty NFA with no states, nor transitions.
    pub fn new() -> Self {
        Nfa {
            states: HashSet::new(),
            symbols: HashSet::new(),
            transitions: HashMap::new(),
            final_states: HashSet::new(),
            initial_states: HashSet::new(),
        }
    }

    pub fn states(&self) -> &HashSet<S> {
        &self.states
    }

    pub fn symbols(&self) -> &HashSet<A> {
        &self.symbols
    }

    pub fn initial_states(&self) -> &HashSet<S> {
        &self.initial_states
    }

    pub fn final_states(&self) -> &HashSet<S> {
        &self.final_states
    }

    /// Adds `states` to the set of states if it wasn't previously inserted.
    pub fn add_state(&mut self, state: S) {
        self.states.insert(state);
    }

    /// Adds `symbol` to the vocabulary if it wasn't previously inserted.
    pub fn add_symbol(&mut self, symbol: A) {
        self.symbols.insert(symbol);
    }

    /// Adds the transition `(source, symbol, destination)` to the set of transitons.
    /// Returns an error if either `source` or `destination` arent' in the set of states,
    /// or if `symbol` isn't in the vocabulary.
    pub fn add_transition(
        &mut self,
        source: S,
        symbol: A,
        destination: S,
    ) -> Result<(), NfaErrors<S, A>> {
        if !self.states.contains(&source) {
            return Err(NfaErrors::InvalidState(source));
        }
        if !self.states.contains(&destination) {
            return Err(NfaErrors::InvalidState(destination));
        }
        if !self.symbols.contains(&symbol) {
            return Err(NfaErrors::InvalidSymbol(symbol));
        }

        if !self.transitions.contains_key(&source) {
            let mut destination_set = HashSet::new();
            destination_set.insert(destination);

            let mut trans_to = HashMap::new();
            trans_to.insert(symbol, destination_set);

            self.transitions.insert(source, trans_to);
        } else {
            let trans_to = self.transitions.get_mut(&source).unwrap();
            if !trans_to.contains_key(&symbol) {
                let mut destination_set = HashSet::new();
                destination_set.insert(destination);

                trans_to.insert(symbol, destination_set);
            } else {
                trans_to.get_mut(&symbol).unwrap().insert(destination);
            }
        }

        Ok(())
    }

    /// Adds `states` to the set of initial states. Returns an error if `state` isn't
    /// in the set of states.
    pub fn add_initial_state(&mut self, state: S) -> Result<(), NfaErrors<S, A>> {
        if !self.states.contains(&state) {
            return Err(NfaErrors::InvalidState(state));
        }

        self.initial_states.insert(state);
        Ok(())
    }

    /// Adds `states` to the set of final states. Returns an error if `state` isn't
    /// in the set of states.
    pub fn add_final_state(&mut self, state: S) -> Result<(), NfaErrors<S, A>> {
        if !self.states.contains(&state) {
            return Err(NfaErrors::InvalidState(state));
        }

        self.final_states.insert(state);
        Ok(())
    }

    /// Evaluates the set of states that can be reached by `sources` with
    /// a transition on `symbol` and returns the set of reached states.
    pub fn eval_symbol(
        &self,
        sources: HashSet<&S>,
        symbol: &A,
    ) -> Result<HashSet<&S>, NfaErrors<S, A>> {
        if !self.symbols.contains(symbol) {
            return Err(NfaErrors::InvalidSymbol(symbol.to_owned()));
        }

        let mut destinations = HashSet::new();
        for state in sources {
            if !self.states.contains(&state) {
                return Err(NfaErrors::InvalidState(state.to_owned()));
            }

            if let Some(trans_to) = self.transitions.get(&state) {
                if let Some(reached_states) = trans_to.get(&symbol) {
                    for reached_state in reached_states {
                        destinations.insert(reached_state);
                    }
                }
            }
        }

        Ok(destinations)
    }

    /// Returns the set of states that can be reached by `source` reading
    /// `symbol`.
    pub fn eval_symbol_from_state(
        &self,
        source: &S,
        symbol: &A,
    ) -> Result<HashSet<&S>, NfaErrors<S, A>> {
        if !self.symbols.contains(symbol) {
            return Err(NfaErrors::InvalidSymbol(symbol.to_owned()));
        }

        if !self.states.contains(source) {
            return Err(NfaErrors::InvalidState(source.to_owned()));
        }

        let mut destinations = HashSet::new();
        if let Some(trans_to) = self.transitions.get(source) {
            if let Some(reached_states) = trans_to.get(symbol) {
                for reached_state in reached_states {
                    destinations.insert(reached_state);
                }
            }
        }

        Ok(destinations)
    }

    /// Evaluates a word starting from states in `sources` and returns the final
    /// set of reached states.
    pub fn eval_word<'a>(
        &'a self,
        sources: HashSet<&'a S>,
        symbols: Vec<&'a A>,
    ) -> Result<HashSet<&'a S>, NfaErrors<S, A>> {
        let mut destinations = sources;
        for symbol in symbols {
            let result = self.eval_symbol(destinations, symbol);

            if let Ok(reached_states) = result {
                destinations = reached_states;
            } else {
                return result;
            }
        }

        Ok(destinations)
    }

    /// Evaluates a word starting from source` and returns the final
    /// set of reached states.
    pub fn eval_word_from_state<'a>(
        &'a self,
        source: &'a S,
        symbols: Vec<&'a A>,
    ) -> Result<HashSet<&'a S>, NfaErrors<S, A>> {
        let mut sources = HashSet::new();
        sources.insert(source);
        self.eval_word(sources, symbols)
    }

    /// Checks if `state` is an initial state. Returs an error if it isn't
    /// in the set of valid states.
    pub fn is_initial(&self, state: &S) -> Result<bool, NfaErrors<S, A>> {
        if !self.states.contains(state) {
            return Err(NfaErrors::InvalidState(state.to_owned()));
        }

        Ok(self.initial_states.contains(state))
    }

    /// Checks if `state` is a final state. Returs an error if it isn't
    /// in the set of valid states.
    pub fn is_final(&self, state: &S) -> Result<bool, NfaErrors<S, A>> {
        if !self.states.contains(state) {
            return Err(NfaErrors::InvalidState(state.to_owned()));
        }

        Ok(self.final_states.contains(state))
    }

    /// Constructs and returns the reversed automaton.
    pub fn reverse(&self) -> Nfa<S, A> {
        let mut rev_nfa = Nfa::new();

        for state in &self.states {
            rev_nfa.states.insert(state.to_owned());
            if self.is_final(state).unwrap() {
                rev_nfa.initial_states.insert(state.to_owned());
            }
            if self.is_initial(state).unwrap() {
                rev_nfa.final_states.insert(state.to_owned());
            }
        }

        for symbol in &self.symbols {
            rev_nfa.symbols.insert(symbol.to_owned());
        }

        for source in &self.states {
            if let Some(trans_to) = self.transitions.get(&source) {
                for (symbol, destinations) in trans_to {
                    for destination in destinations {
                        let _ = rev_nfa.add_transition(
                            destination.to_owned(),
                            symbol.to_owned(),
                            source.to_owned(),
                        );
                    }
                }
            }
        }

        rev_nfa
    }
}

impl<S, A> ToString for Nfa<S, A>
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    fn to_string(&self) -> String {
        let mut result = String::new();
        result.push_str("digraph {\n");
        result.push_str("\trankdir = LR;\n");
        result.push_str("\tsize = \"30,20\";\n");

        let mut dummy_count = 0;
        for state in &self.initial_states {
            result.push('\t');
            result.push_str(&format!(r#"node [shape = point]; "dummy{}""#, dummy_count));
            result.push('\n');
            if self.is_final(state).unwrap() {
                result.push_str("\tnode [shape = doublecircle]; ");
            } else {
                result.push_str("\tnode [shape = circle]; ");
            }
            result.push_str(&format!(r#""{}""#, state));
            result.push('\n');
            result.push('\t');
            result.push_str(&format!(r#""dummy{}" -> "{}";"#, dummy_count, state));
            result.push('\n');
            dummy_count += 1;
        }

        for state in &self.states {
            if self.is_initial(state).unwrap() {
                continue;
            }

            if self.is_final(state).unwrap() {
                result.push_str("\tnode [shape = doublecircle]; ");
            } else {
                result.push_str("\tnode [shape = circle]; ");
            }
            result.push_str(&format!(r#""{}";"#, &state));
            result.push('\n');
        }

        for (source, trans_to) in &self.transitions {
            for (symbol, dests) in trans_to {
                for dest in dests {
                    result.push('\t');
                    result.push_str(&format!(
                        r#""{}" -> "{}" [label = "{}"];"#,
                        source, dest, symbol
                    ));
                    result.push('\n');
                }
            }
        }

        result.push('}');

        result
    }
}

impl FromStr for Nfa<String, String> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let raw_graph = graphviz_rust::parse(s)?;
        let stmts = match raw_graph {
            graphviz_rust::dot_structures::Graph::Graph {
                id: _,
                strict: _,
                stmts,
            } => stmts,
            graphviz_rust::dot_structures::Graph::DiGraph {
                id: _,
                strict: _,
                stmts,
            } => stmts,
        };
        let mut nfa = Nfa::new();

        let mut previous_node_is_final = false;
        for stmt in stmts {
            match stmt {
                Stmt::Node(node) => {
                    let node_id = match node.id.0 {
                        Id::Html(id) => id,
                        Id::Escaped(id) => id[1..id.len() - 1].into(),
                        Id::Plain(id) => id,
                        Id::Anonymous(id) => id,
                    };
                    // Dummy nodes must not be added to `nfa`
                    if node_id.starts_with("dummy") {
                        continue;
                    }
                    nfa.add_state(node_id.clone());

                    if previous_node_is_final {
                        let _ = nfa.add_final_state(node_id);
                        previous_node_is_final = false;
                    }
                }
                Stmt::Edge(edge) => {
                    let mut label = None;

                    // Scan attributes to look for a label
                    for Attribute(name, value) in edge.attributes {
                        if name.to_string().to_ascii_lowercase() == "label" {
                            label = Some(match value {
                                Id::Html(value) => value,
                                Id::Escaped(value) => value[1..value.len() - 1].into(),
                                Id::Plain(value) => value,
                                Id::Anonymous(value) => value,
                            });
                            break;
                        }
                    }

                    if let EdgeTy::Pair(source_vertex, dest_vertex) = edge.ty {
                        let mut source = None;
                        if let Vertex::N(source_id) = source_vertex {
                            source = Some(source_id.0);
                        }
                        let mut dest = None;
                        if let Vertex::N(dest_id) = dest_vertex {
                            dest = Some(dest_id.0);
                        }

                        if source.is_none() || dest.is_none() {
                            return Err(format!("Source and dest nodes in edges must be node ids"));
                        }

                        let source = match source.unwrap() {
                            Id::Html(id) => id,
                            Id::Escaped(id) => id[1..id.len() - 1].into(),
                            Id::Plain(id) => id,
                            Id::Anonymous(id) => id,
                        };
                        let dest = match dest.unwrap() {
                            Id::Html(id) => id,
                            Id::Escaped(id) => id[1..id.len() - 1].into(),
                            Id::Plain(id) => id,
                            Id::Anonymous(id) => id,
                        };

                        // If `source` starts with `dummy`, `dest` is an initial
                        // note
                        if source.starts_with("dummy") {
                            nfa.add_state(dest.clone());
                            let _ = nfa.add_initial_state(dest);
                        } else {
                            // `source` is an actual node, so try to see if
                            // there is a valid transition
                            if label.is_none() {
                                return Err(format!(
                                    "Transition on no symbol (edge without label attribute)"
                                ));
                            }
                            let label = label.unwrap();
                            nfa.add_symbol(label.clone());
                            let _ = nfa.add_transition(source, label, dest);
                        }
                    } else {
                        return Err(format!("Edges must be pairs (source, dest) with label attribute set to be the transition symbol"));
                    }
                }
                Stmt::GAttribute(graph_attr) => {
                    if let GraphAttributes::Node(attributes) = graph_attr {
                        for Attribute(name, value) in attributes {
                            if name.to_string().to_lowercase() == "shape" {
                                let value = match value {
                                    Id::Html(value) => value,
                                    Id::Escaped(value) => value[1..value.len() - 1].into(),
                                    Id::Plain(value) => value,
                                    Id::Anonymous(value) => value,
                                };

                                if value == "doublecircle" {
                                    previous_node_is_final = true;
                                    break;
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }

        Ok(nfa)
    }
}
