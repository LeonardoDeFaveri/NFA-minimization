use cli_table::{format::Justify, print_stdout, Cell, Style, Table};
use std::io::Write;
use utils::minimize;

#[allow(dead_code)]
mod algorithms;
mod nfa;
#[allow(dead_code)]
mod utils;

fn main() {
    let tests: Vec<String> = match std::env::args_os().nth(1) {
        Some(path) => match std::fs::read_dir(&path) {
            Ok(content) => {
                println!("Reading tests from {:?}", &path);
                content
                    .filter(|entry| entry.is_ok())
                    .map(|entry| entry.unwrap().path())
                    .filter(|entry| entry.extension().unwrap_or_default() == "gv")
                    .map(|entry| match entry.to_str() {
                        Some(path) => Some(path.to_string()),
                        None => None,
                    })
                    .filter(|entry| entry.is_some())
                    .map(|entry| entry.unwrap())
                    .collect()
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

    let mut sizes = vec![];
    let tests_count = tests.len();
    for (i, path) in tests.iter().enumerate() {
        print!("\rAnalyzing test: {:0>2}/{:0>2}", i + 1, tests_count);
        let _ = std::io::stdout().flush();
        sizes.push(minimize(path).as_vec());
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
            "Reason priority",
            "SCCs",
        ],
    );
}

fn print_results(sizes: &Vec<Vec<usize>>, titles: Vec<&str>) {
    let sizes_count = sizes.len();
    if sizes_count == 0 {
        return;
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
    let mut summary_row = vec![
        "Res".cell().justify(Justify::Center).bold(true),
        "-".cell().justify(Justify::Center).bold(true),
    ];
    for red in avg_red {
        let red_str = format!("{:.3}%", red);
        summary_row.push(red_str.cell().justify(Justify::Center).bold(true));
    }
    table_rows.push(summary_row);

    // Prepares titles
    let mut title_row = vec![];
    for title in titles {
        title_row.push(title.cell().justify(Justify::Center).bold(true));
    }

    let table = table_rows.table().title(title_row);
    let _ = print_stdout(table);
}
