use cli_table::{format::Justify, print_stdout, Cell, Style, Table};
use std::io::Write;
use utils::minimize;

use crate::utils::read_rel;

#[allow(dead_code)]
mod algorithms;
mod nfa;
#[allow(dead_code)]
mod utils;

#[cfg(test)]
mod test;

fn main() {
    let mut tests: Vec<String> = vec![];
    let mut right_rels: Vec<String> = vec![];
    let mut left_rels: Vec<String> = vec![];

    /*let mut files: Vec<String> = */
    match std::env::args_os().nth(1) {
        Some(path) => match std::fs::read_dir(&path) {
            Ok(content) => {
                println!("Reading tests from {:?}", &path);
                content
                    .filter(|entry| entry.is_ok())
                    .map(|entry| entry.unwrap().path())
                    .for_each(|entry| {
                        let file_name = entry.to_str().unwrap().to_string();
                        let extension = entry.extension().unwrap_or_default().to_str().unwrap();
                        match extension {
                            "gv" => tests.push(file_name),
                            "right_rel" => right_rels.push(file_name),
                            "left_rel" => left_rels.push(file_name),
                            _ => {}
                        };
                    });
                //.filter(|entry| entry.extension().unwrap_or_default() == "gv")
                //.map(|entry| match entry.to_str() {
                //    Some(path) => Some(path.to_string()),
                //    None => None,
                //})
                //.filter(|entry| entry.is_some())
                //.map(|entry| entry.unwrap())
                //.collect()
            }
            Err(err) => {
                eprintln!("Error while trying to read {:?}", &path);
                eprintln!("{}", err);
                std::process::exit(1);
            }
        },
        None => {
            eprintln!("You need to provide a source folder for tests");
            std::process::exit(1);
        }
    };

    tests.sort_by(|t1, t2| t1.cmp(&t2));
    right_rels.sort_by(|t1, t2| t1.cmp(&t2));
    left_rels.sort_by(|t1, t2| t1.cmp(&t2));

    let mut sizes = vec![];
    let tests_count = tests.len();
    for (i, path) in tests.iter().enumerate() {
        let right_rel_path = right_rels.get(i).unwrap();
        let left_rel_path = left_rels.get(i).unwrap();
        let right_rel = read_rel(&right_rel_path);
        let left_rel = read_rel(&left_rel_path);
        print!(
            "\rAnalyzing test: {:0>2}/{:0>2} [{:^30}]",
            i + 1,
            tests_count,
            path,
        );
        let _ = std::io::stdout().flush();
        sizes.push(minimize(path, right_rel, left_rel).as_vec());
    }

    sizes.sort_by(|a, b| a[0].cmp(&b[0]));

    println!("\nResults:");
    print_results(
        &sizes,
        vec![
            "#",
            "Original",
            "Right Eq",
            "Left Eq",
            "Right-Left Eq",
            "Left-Right Eq",
            "SCC All",
            "SCC Right",
            "SCC Left",
            "SCC Pre"
        ],
    );
}

fn print_results(sizes: &Vec<Vec<usize>>, titles: Vec<&str>) {
    let sizes_count = sizes.len();
    if sizes_count == 0 {
        return;
    }

    // Prepares titles
    let mut title_row1 = vec![];
    let mut title_row2 = vec![];
    for title in titles {
        title_row1.push(title.cell().justify(Justify::Center).bold(true));
        title_row2.push(title.cell().justify(Justify::Center).bold(true));
    }

    // Calculate average reduction in size for each method
    // 1. Sums up all reductions
    let mut avg_red = vec![0.0; sizes[0].len() - 1];

    for sample_sizes in sizes {
        let original = sample_sizes[0];
        for (i, size) in sample_sizes[1..].iter().enumerate() {
            avg_red[i] += (original - size) as f64 / original as f64;
        }
    }

    // 2. Calculates the average
    for red in avg_red.as_mut_slice() {
        *red = *red / sizes_count as f64 * 100.0;
    }

    let mut table_rows = vec![];
    // Main data rows
    for (i, sample_sizes) in sizes.iter().enumerate() {
        let mut row = vec![(i + 1).cell().justify(Justify::Center)];
        for size in sample_sizes {
            row.push(size.cell().justify(Justify::Center));
        }
        table_rows.push(row);
    }

    // Summary row
    table_rows.push(title_row2);
    let mut summary_row = vec![
        "Res".cell().justify(Justify::Center).italic(true),
        "-".cell().justify(Justify::Center).italic(true),
    ];
    for red in &avg_red {
        let red_str = format!("{:.3}%", red);
        summary_row.push(red_str.cell().justify(Justify::Center).italic(true));
    }
    summary_row.extend([
        "-".cell().justify(Justify::Center).italic(true),
        "-".cell().justify(Justify::Center).italic(true),
        "-".cell().justify(Justify::Center).italic(true),
    ]);
    table_rows.push(summary_row);

    let table = table_rows.table().title(title_row1);
    let _ = print_stdout(table);
}
