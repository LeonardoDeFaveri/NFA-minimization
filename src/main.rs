use core::hash::Hash;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::str::FromStr;

use algorithms::*;
use nfa::Nfa;

mod algorithms;
mod nfa;

fn main() {
    let source = std::fs::read_to_string("nfa.gv").unwrap();
    let nfa = Nfa::from_str(&source).unwrap();

    let dot_notation = nfa.to_string();
    let _ = std::fs::write("nfa.gv", dot_notation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg("nfa.gv")
        .output()
        .expect("Error while writing nfa to pdf");
    let _ = std::fs::write("nfa.pdf", output.stdout);
    let rev_nfa = nfa.reverse();
    let dot_notation = rev_nfa.to_string();
    let _ = std::fs::write("rev_nfa.gv", dot_notation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg("rev_nfa.gv")
        .output()
        .expect("Error while writing rev_nfa to pdf");
    let _ = std::fs::write("rev_nfa.pdf", output.stdout);

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    println!("Right language:");
    print_language(&right_language);
    println!("Left language:");
    print_language(&left_language);

    let right = algorithms::calc_relation(&nfa, &right_language);
    let left = algorithms::calc_relation(&rev_nfa, &left_language);

    let mut right_row = String::new();
    right_row.push('[');
    for (source, dest) in &right {
        right_row.push_str(&format!("({}, {})", source, dest));
        right_row.push(',');
    }
    right_row.pop();
    right_row.push(']');

    let mut left_row = String::new();
    left_row.push('[');
    for (source, dest) in &left {
        left_row.push_str(&format!("({}, {})", source, dest));
        left_row.push(',');
    }
    left_row.pop();
    left_row.push(']');

    println!("Right preorder:\n{}", right_row);
    println!("Left preorder:\n{}", left_row);
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

    let res = algorithms::minimization::right_eq(nfa.states(), &right);
    let min_right_size = res.len();

    println!("Right equivalence classes");
    for (i, r) in res.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }

    let min_right = algorithms::build_minimized(&nfa, &res);
    let dot_notation = min_right.to_string();
    let _ = std::fs::write("minimized/right.gv", dot_notation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg("minimized/right.gv")
        .output()
        .expect("Error while writing minimized nfa to pdf");
    let _ = std::fs::write("minimized/right.pdf", output.stdout);

    let res = algorithms::minimization::right_eq(nfa.states(), &left);
    let min_left_size = res.len();

    println!("Left equivalence classes");
    for (i, r) in res.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }

    let min_left = algorithms::build_minimized(&nfa, &res);
    let dot_notation = min_left.to_string();
    let _ = std::fs::write("minimized/left.gv", dot_notation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg("minimized/left.gv")
        .output()
        .expect("Error while writing minimized nfa to pdf");
    let _ = std::fs::write("minimized/left.pdf", output.stdout);

    let res = algorithms::minimization::preorder_1(nfa.states(), &table);
    let min_pre_size = res.len();

    println!("Preorder equivalence classes");
    for (i, r) in res.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }

    let min_pre1 = algorithms::build_minimized(&nfa, &res);
    let dot_notation = min_pre1.to_string();
    let _ = std::fs::write("minimized/pre1.gv", dot_notation);
    let output = std::process::Command::new("dot")
        .arg("-T")
        .arg("pdf")
        .arg("minimized/pre1.gv")
        .output()
        .expect("Error while writing minimized nfa to pdf");
    let _ = std::fs::write("minimized/pre1.pdf", output.stdout);

    println!("| Original | Right Eq | Left Eq | Preorder |");
    println!(
        "| {} | {} | {} | {} |",
        nfa.states().len(),
        min_right_size,
        min_left_size,
        min_pre_size
    );
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
