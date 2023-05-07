use core::hash::Hash;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::str::FromStr;

use algorithms::*;

use crate::nfa::Nfa;

mod algorithms;
mod nfa;

fn main() {
    let source = std::fs::read_to_string("nfa.gv").unwrap();
    let nfa = Nfa::from_str(&source).unwrap();

    //let dot_notation = nfa.to_string();
    //let _ = std::fs::write("nfa.gv", dot_notation);
    let rev_nfa = nfa.reverse();

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    println!("Right language:");
    print_language(&right_language);
    println!("Left language:");
    print_language(&left_language);

    let right = calc_relation(&nfa, &right_language);
    let left = calc_relation(&rev_nfa, &left_language);

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
    println!("\n(p, q)\t| Right\t| Left\t| Loop(p)");
    println!("-------------------------------");
    for (p, q) in table.keys() {
        let value = table.get(&(p.to_owned(), q.to_owned())).unwrap();
        println!(
            "({}, {})\t| {}\t| {}\t| {}",
            p, q, value.0, value.1, value.2
        );
    }

    println!("Right equivalence classes");
    let res = algorithms::minimization::right_eq(nfa.states(), &right);
    for (i, r) in res.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }

    let min_right = algorithms::build_minimized(&nfa, &res);
    let dot_notation = min_right.to_string();
    let _ = std::fs::write("min_right.gv", dot_notation);

    println!("Left equivalence classes");
    let res = algorithms::minimization::right_eq(nfa.states(), &left);
    for (i, r) in res.iter().enumerate() {
        print!("{}: {{", i);
        for state in r {
            print!("{}, ", state);
        }
        println!("}}");
    }

    let min_left = algorithms::build_minimized(&nfa, &res);
    let dot_notation = min_left.to_string();
    let _ = std::fs::write("min_left.gv", dot_notation);
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
