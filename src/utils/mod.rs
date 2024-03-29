use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    str::FromStr,
};

use petgraph::prelude::DiGraphMap;

use crate::{
    algorithms::{self, calc_right_language, initialize_rel_table, Language, Path},
    nfa::Nfa,
};

/// Struct used to keep all sizes of minimized nfas.
pub struct Sizes {
    pub original: usize,
    pub right_eq: usize,
    pub left_eq: usize,
    pub right_left_eq: usize,
    pub left_right_eq: usize,
    pub sccs: (usize, usize, usize, usize),
}

impl Sizes {
    pub fn as_vec(&self) -> Vec<usize> {
        vec![
            self.original,
            self.right_eq,
            self.left_eq,
            self.right_left_eq,
            self.left_right_eq,
            self.sccs.0,
            self.sccs.1,
            self.sccs.2,
            self.sccs.3,
        ]
    }
}

impl Default for Sizes {
    fn default() -> Self {
        Sizes {
            original: 0,
            right_eq: 0,
            left_eq: 0,
            right_left_eq: 0,
            left_right_eq: 0,
            sccs: (0, 0, 0, 0),
        }
    }
}

impl PartialEq for Path<String, String> {
    fn eq(&self, other: &Self) -> bool {
        self.transition_symbol == other.transition_symbol
            && self.reached_state == other.reached_state
    }
}

fn test_equality(
    langs1: &HashMap<String, Language<String, String>>,
    langs2: &HashMap<String, Language<String, String>>,
) -> bool {
    for (state, lang1) in langs1 {
        let lang2 = &langs2[state];

        if lang1.loops() != lang2.loops() {
            return false;
        }

        for path1 in lang1.paths() {
            if !lang2.paths().contains(path1) {
                return false;
            }
        }
        for path2 in lang2.paths() {
            if !lang1.paths().contains(path2) {
                return false;
            }
        }
    }

    true
}

pub fn minimize(
    source_file: &str,
    mut right: HashSet<(String, String)>,
    mut left: HashSet<(String, String)>,
) -> Sizes {
    // Original NFA
    let source = std::fs::read_to_string(source_file).unwrap();
    let nfa = Nfa::from_str(&source).unwrap();
    let original = nfa.states().len();

    let rev_nfa = nfa.reverse();
    let right_language = calc_right_language(&nfa);
    let left_language = calc_right_language(&rev_nfa);

    algorithms::calc_relation(&nfa, &right_language, &mut right);
    algorithms::calc_relation(&rev_nfa, &left_language, &mut left);
    let table = initialize_rel_table(&nfa, &right, &left);

    // Minimize using only right equivalence classes
    let res = algorithms::minimization::eq::right_eq(nfa.states(), &right);
    let right_eq = res.len();

    // Minimize using only left equivalence classes
    let res = algorithms::minimization::eq::right_eq(nfa.states(), &left);
    let left_eq = res.len();

    // Minimize using right and then left equivalence classes
    let res = algorithms::minimization::eq::right_left_eq(nfa.states(), &right, &left);
    let right_left_eq = res.len();

    // Minimize using left and then right equivalence classes
    let res = algorithms::minimization::eq::right_left_eq(nfa.states(), &left, &right);
    let left_right_eq = res.len();

    // Minimize using merging rules in order: iii, i, ii
    //let res =
    //    algorithms::minimization::preorders_with_priority(nfa.states(), &table, &right, &left);
    //let reason = res.len();

    // Minimize using strongly connected components
    let res = algorithms::minimization::preorders_with_sccs(nfa.states(), &table);
    let sccs = res.len();

    let res = algorithms::minimization::preorders_with_sccs_right(nfa.states(), &table);
    let sccs_right = res.len();

    let res = algorithms::minimization::preorders_with_sccs_left(nfa.states(), &table);
    let sccs_left = res.len();

    let res = algorithms::minimization::preorders_with_sccs_pre(nfa.states(), &table);
    let sccs_pre = res.len();

    //let sccs_count = count_sccs(nfa.states(), &table);

    Sizes {
        original,
        right_eq,
        left_eq,
        right_left_eq,
        left_right_eq,
        sccs: (sccs, sccs_right, sccs_left, sccs_pre),
    }
}

pub fn print_language<S, A>(languages: &HashMap<S, Language<S, A>>)
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut output = String::new();

    for (state, language) in languages {
        output.push_str(&format!("{state}: {language}\n"));
    }

    println!("{output}");
}

/// Saves an nfa to a `.gv` and `.pdf` file. The extensions are automatically
/// added.
pub fn save_as<S, A>(nfa: &Nfa<S, A>, file_name: &str)
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let dot_representation = nfa.to_string();
    let file_name = file_name.to_string();

    let _ = std::fs::write(format!("{}.gv", &file_name), dot_representation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg(format!("{}.gv", &file_name))
        .output()
        .expect("Error while writing nfa to pdf");
    let _ = std::fs::write(format!("{}.pdf", &file_name), output.stdout);
}

/// Utility function for printing merged states of an NFA.
pub fn print_equivalence_classes<S>(title: &str, classes: &Vec<HashSet<S>>)
where
    S: Display,
{
    println!("{title}");
    for (i, r) in classes.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }
}

/// Builds left, right and mixed dependency graphs and returns the number of
/// Strongly Connected Components.
pub fn count_sccs<S>(
    states: &HashSet<S>,
    rel_table: &HashMap<(S, S), (bool, bool, bool)>,
) -> (usize, usize, usize, usize)
where
    S: Eq + Hash + Clone,
{
    type PlaceHolder = usize;
    let mut all_ph: HashMap<&S, PlaceHolder> = HashMap::new();
    let mut all_states: HashMap<PlaceHolder, &S> = HashMap::new();
    let mut graph_rl: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_all: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_right: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();
    let mut graph_left: DiGraphMap<PlaceHolder, ()> = DiGraphMap::new();

    for (ph, state) in states.iter().enumerate() {
        graph_right.add_node(ph);
        graph_left.add_node(ph);
        all_ph.insert(state, ph);
        all_states.insert(ph, state);
    }

    for ((p, q), (right, left, l)) in rel_table {
        let p_ph = all_ph[&p];
        let q_ph = all_ph[&q];

        if *right {
            graph_right.add_edge(p_ph, q_ph, ());
            graph_rl.add_edge(p_ph, q_ph, ());
            graph_all.add_edge(p_ph, q_ph, ());
        }
        if *left {
            graph_left.add_edge(p_ph, q_ph, ());
            graph_rl.add_edge(p_ph, q_ph, ());
            graph_all.add_edge(p_ph, q_ph, ());
        }
        if *right && *left && !*l {
            graph_all.add_edge(q_ph, p_ph, ());
        }
    }

    let sccs_right = petgraph::algo::kosaraju_scc(&graph_right);
    let sccs_left = petgraph::algo::kosaraju_scc(&graph_left);
    let sccs_rl = petgraph::algo::kosaraju_scc(&graph_rl);
    let sccs_all = petgraph::algo::kosaraju_scc(&graph_all);

    (
        sccs_left.len(),
        sccs_right.len(),
        sccs_rl.len(),
        sccs_all.len(),
    )
}

pub fn read_rel(source_file: &str) -> HashSet<(String, String)> {
    let mut rel = HashSet::new();

    let source = std::fs::read_to_string(source_file).unwrap();
    for line in source.lines() {
        let tokens: Vec<&str> = line.rsplit(" ").collect();
        rel.insert((tokens[0].to_string(), tokens[1].to_string()));
    }

    rel
}

pub fn test_minimization(
    source_file: &str,
    mut right: HashSet<(String, String)>,
    mut left: HashSet<(String, String)>,
) -> Vec<usize> {
    let mut sizes = Vec::new();

    let source = std::fs::read_to_string(source_file).unwrap();
    let nfa = Nfa::from_str(&source).unwrap();
    //save_as(&nfa, "nfa");
    sizes.push(nfa.states().len());

    let rev_nfa = nfa.reverse();
    //save_as(&rev_nfa, "rev_nfa");

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    println!("Right Language");
    print_language(&right_language);
    println!("Left Language");
    print_language(&left_language);

    algorithms::calc_relation(&nfa, &right_language, &mut right);
    algorithms::calc_relation(&rev_nfa, &left_language, &mut left);

    let table = initialize_rel_table(&nfa, &right, &left);
    println!("\n(p, q)  \t| Right\t| Left\t| Loop(p)");
    println!("-----------------------------------------");
    for (p, q) in table.keys() {
        let value = table.get(&(p.to_owned(), q.to_owned())).unwrap();
        println!(
            "({}, {})  \t| {}\t| {}\t| {}",
            p, q, value.0, value.1, value.2
        );
    }

    // Minimization algorithms
    // Minimize using only right equivalence classes
    let res = algorithms::minimization::eq::right_eq(nfa.states(), &right);
    sizes.push(res.len());
    let min_right = algorithms::build_minimized(&nfa, &res);
    save_as(&min_right, "minimized/right");
    //print_equivalence_classes("Right Equivalence classes", &res);

    // Minimize using only left equivalence classes
    let res = algorithms::minimization::eq::right_eq(nfa.states(), &left);
    sizes.push(res.len());
    let min_left = algorithms::build_minimized(&nfa, &res);
    save_as(&min_left, "minimized/left");
    //print_equivalence_classes("Left Equivalence classes", &res);

    // Minimize using right and then left equivalence classes
    let res = algorithms::minimization::eq::right_left_eq(nfa.states(), &right, &left);
    sizes.push(res.len());
    let min_right_left = algorithms::build_minimized(&nfa, &res);
    save_as(&min_right_left, "minimized/right_left");
    //print_equivalence_classes("Right-Left Equivalence classes", &res);

    // Minimize using left and then right equivalence classes
    let res = algorithms::minimization::eq::right_left_eq(nfa.states(), &left, &right);
    sizes.push(res.len());
    let min_left_right = algorithms::build_minimized(&nfa, &res);
    save_as(&min_left_right, "minimized/left_right");
    //print_equivalence_classes("Left-Right Equivalence classes", &res);

    // Minimize using only rule 3 of merging with preorder equivalence classes
    let res =
        algorithms::minimization::preorders_with_priority(nfa.states(), &table, &right, &left);
    sizes.push(res.len());
    let min_pre1 = algorithms::build_minimized(&nfa, &res);
    save_as(&min_pre1, "minimized/pre_priority");
    //print_equivalence_classes("Preorder1 Equivalence classes", &res);

    let sccs_count = count_sccs(nfa.states(), &table);

    sizes.push(sccs_count.0);
    sizes.push(sccs_count.1);
    sizes.push(sccs_count.2);
    sizes.push(sccs_count.3);
    sizes
}
