use crate::{algorithms::*, nfa::Nfa, utils::*};
use std::str::FromStr;

#[test]
fn general() {
    //let source_file = "tests/medium-9.gv";
    let source_file = "mini_tests/nfa5.gv";
    let source = std::fs::read_to_string(source_file).unwrap();
    let nfa = Nfa::from_str(&source).unwrap();

    let rev_nfa = nfa.reverse();
    //save_as(&rev_nfa, "rev_nfa");

    let right_language = calc_right_language(&rev_nfa);
    let left_language = calc_right_language(&nfa);

    println!("Right Language");
    print_language(&right_language);
    println!("Left Language");
    print_language(&left_language);

    let right = calc_relation(&nfa, &right_language);
    let left = calc_relation(&rev_nfa, &left_language);

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

    let res = minimization::preorders_with_sccs(nfa.states(), &table);
    print_equivalence_classes("SCCs", &res);
    let min = build_minimized(&nfa, &res);
    save_as(&min, "scc");

    let res = minimization::preorders_with_sccs2(nfa.states(), &table);
    print_equivalence_classes("SCCs2", &res);
    let min = build_minimized(&nfa, &res);
    save_as(&min, "scc2");
}
