use crate::{algorithms::*, nfa::Nfa, utils::*};
use std::str::FromStr;

#[test]
fn general() {
    let graph = "p.gv";
    let right_rel = "p.right_rel";
    let left_rel = "p.left_rel";
    let mut right = read_rel(&right_rel);
    let mut left = read_rel(&left_rel);
    let source = std::fs::read_to_string(graph).unwrap();
    let nfa = Nfa::from_str(&source).unwrap();

    let rev_nfa = nfa.reverse();
    //save_as(&rev_nfa, "rev_nfa");

    let right_language = calc_right_language(&nfa);
    let left_language = calc_right_language(&rev_nfa);

    println!("Right Language");
    print_language(&right_language);
    println!("Left Language");
    print_language(&left_language);

    //let mut right = HashSet::new();
    //let mut left = HashSet::new();
    calc_relation(&nfa, &right_language, &mut right);
    calc_relation(&rev_nfa, &left_language, &mut left);

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

    let mut sizes = Vec::new();

    let res = minimization::preorders_with_sccs(nfa.states(), &table);
    sizes.push(res.len());
    print_equivalence_classes("SCCs", &res);
    let min = build_minimized(&nfa, &res);
    save_as(&min, "scc");

    let res = minimization::preorders_with_sccs2(nfa.states(), &table);
    sizes.push(res.len());
    print_equivalence_classes("SCCs2", &res);
    let min = build_minimized(&nfa, &res);
    save_as(&min, "scc2");

    let sccs_count = count_sccs(nfa.states(), &table);
    sizes.push(sccs_count.0);
    sizes.push(sccs_count.1);
    sizes.push(sccs_count.2);

    println!("{:?}", sizes);
}
