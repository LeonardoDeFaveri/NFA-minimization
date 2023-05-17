use core::hash::Hash;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::str::FromStr;

use algorithms::*;
use nfa::Nfa;

mod algorithms;
mod nfa;

fn main() {
    let sizes = test_minimization("nfa.gv");
    println!("{:-<97}", "");
    println!(
        "|{:^15}|{:^15}|{:^15}|{:^15}|{:^15}|{:^15}|",
        "Original", "Right Eq", "Left Eq", "Right-Left Eq", "Left-Right Eq", "Preorder"
    );
    println!("{:-<97}", "");
    print!("|");
    for size in sizes {
        print!("{:^15}|", size);
    }
    println!("\n{:-<97}", "");
}

fn print_language<S, A>(languages: &HashMap<S, Language<S, A>>)
where
    S: Eq + Hash + Clone + Debug + Display,
    A: Eq + Hash + Clone + Debug + Display,
{
    let mut output = String::new();

    for (state, language) in languages {
        output.push_str(&format!("{state}: "));
        let mut loop_str =
            String::from_iter(language.loops().iter().map(|symbol| format!("{symbol}+")));

        if !loop_str.is_empty() {
            loop_str.pop();
            loop_str = format!("({})*", loop_str);
        }

        for path in language.paths() {
            output.push_str(&format!(
                "{}{}L{}+",
                loop_str, path.transition_symbol, path.reached_state
            ));
        }
        output.pop();
        output.push('\n');
    }

    println!("{output}");
}

/// Saves an nfa to a `.gv` and `.pdf` file.
fn save_as<S, A>(nfa: &Nfa<S, A>, file_name: &str)
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

fn print_equivalence_classes<S>(title: &str, classes: &Vec<HashSet<S>>)
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

fn test_minimization(source_file: &str) -> Vec<usize> {
    let mut sizes = Vec::new();

    let source = std::fs::read_to_string(source_file).unwrap();
    let nfa = Nfa::from_str(&source).unwrap();
    sizes.push(nfa.states().len());

    let rev_nfa = nfa.reverse();
    save_as(&rev_nfa, "rev_nfa");

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    let right = algorithms::calc_relation(&nfa, &right_language);
    let left = algorithms::calc_relation(&rev_nfa, &left_language);

    let table = initialize_rel_table(&nfa, &right, &left);
    //println!("\n(p, q)  \t| Right\t| Left\t| Loop(p)");
    //println!("-----------------------------------------");
    //for (p, q) in table.keys() {
    //    let value = table.get(&(p.to_owned(), q.to_owned())).unwrap();
    //    println!(
    //        "({}, {})  \t| {}\t| {}\t| {}",
    //        p, q, value.0, value.1, value.2
    //    );
    //}

    // Minimization algorithms
    // Minimize using only right equivalence classes
    let res = algorithms::minimization::right_eq(nfa.states(), &right);
    sizes.push(res.len());
    let min_right = algorithms::build_minimized(&nfa, &res);
    save_as(&min_right, "minimized/right");
    //print_equivalence_classes("Right Equivalence classes", &res);

    // Minimize using only left equivalence classes
    let res = algorithms::minimization::right_eq(nfa.states(), &left);
    sizes.push(res.len());
    let min_left = algorithms::build_minimized(&nfa, &res);
    save_as(&min_left, "minimized/left");
    //print_equivalence_classes("Left Equivalence classes", &res);

    // Minimize using only rule 3 of merging with preorder equivalence classes
    let res = algorithms::minimization::preorder_1(nfa.states(), &table);
    sizes.push(res.len());
    let min_pre1 = algorithms::build_minimized(&nfa, &res);
    save_as(&min_pre1, "minimized/pre1");
    //print_equivalence_classes("Preorder1 Equivalence classes", &res);

    // Minimize using right and then left equivalence classes
    let res = algorithms::minimization::right_left_eq(nfa.states(), &right, &left);
    sizes.push(res.len());
    let min_right_left = algorithms::build_minimized(&nfa, &res);
    save_as(&min_right_left, "minimized/right_left");
    //print_equivalence_classes("Right-Left Equivalence classes", &res);

    // Minimize using left and then right equivalence classes
    let res = algorithms::minimization::right_left_eq(nfa.states(), &left, &right);
    sizes.push(res.len());
    let min_left_right = algorithms::build_minimized(&nfa, &res);
    save_as(&min_left_right, "minimized/left_right");
    //print_equivalence_classes("Left-Right Equivalence classes", &res);

    sizes
}
