use algorithms::calc_right_language;

use crate::algorithms::calc_relation;

mod algorithms;
mod nfa;

fn main() {
    let mut nfa = nfa::Nfa::<String, char>::new();
    nfa.add_state("0".into());
    nfa.add_state("1".into());
    nfa.add_state("2".into());
    nfa.add_state("3".into());
    nfa.add_state("4".into());
    nfa.add_state("5".into());

    let _ = nfa.add_initial_state("0".into());
    let _ = nfa.add_final_state("5".into());

    nfa.add_symbol('a');
    nfa.add_symbol('b');
    nfa.add_symbol('c');
    nfa.add_symbol('x');
    nfa.add_symbol('y');

    let _ = nfa.add_transition("0".into(), 'a', "1".into());
    let _ = nfa.add_transition("0".into(), 'a', "2".into());
    let _ = nfa.add_transition("0".into(), 'x', "2".into());
    let _ = nfa.add_transition("0".into(), 'a', "3".into());
    let _ = nfa.add_transition("1".into(), 'b', "1".into());
    let _ = nfa.add_transition("1".into(), 'c', "5".into());
    let _ = nfa.add_transition("2".into(), 'c', "5".into());
    let _ = nfa.add_transition("2".into(), 'y', "5".into());
    let _ = nfa.add_transition("2".into(), 'b', "4".into());
    let _ = nfa.add_transition("4".into(), 'b', "4".into());
    let _ = nfa.add_transition("4".into(), 'c', "5".into());
    let _ = nfa.add_transition("3".into(), 'b', "2".into());
    let _ = nfa.add_transition("3".into(), 'b', "3".into());

    //let dot_notation = nfa.to_string();
    //let _ = std::fs::write("nfa.gv", dot_notation);
    let rev_nfa = nfa.reverse();

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    let mut right_row = String::new();
    let mut left_row = String::new();
    for state in nfa.states() {
        right_row.push_str(&format!(
            "\t{}: {}\n",
            state,
            right_language.get(state).unwrap()
        ));
        left_row.push_str(&format!(
            "\t{}: {}\n",
            state,
            left_language.get(state).unwrap()
        ));
    }
    println!("Right language:\n{}", right_row);
    println!("Left language:\n{}", left_row);

    let right = calc_relation(&nfa, &right_language);
    let left = calc_relation(&rev_nfa, &left_language);
    
    right_row.clear();
    right_row.push('[');
    for (source, dest) in right {
        right_row.push_str(&format!("({}, {})", source, dest));
        right_row.push(',');
    }
    right_row.pop();
    right_row.push(']');

    left_row.clear();
    left_row.push('[');
    for (source, dest) in left {
        left_row.push_str(&format!("({}, {})", source, dest));
        left_row.push(',');
    }
    left_row.pop();
    left_row.push(']');

    println!("Right preorder:\n{}", right_row);
    println!("Left preorder:\n{}", left_row);
}
