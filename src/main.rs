use std::io::Write;
use tabled::Table;

use crate::utils::{minimize, Sizes};

mod algorithms;
mod nfa;
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

    let mut avg_size_red = Sizes::default();
    let mut sizes: Vec<Sizes> = Vec::new();
    let tests_count = tests.len();
    for (i, path) in tests.iter().enumerate() {
        print!("\rAnalyzing test: {:0>2}/{}", i + 1, tests_count);
        let _ = std::io::stdout().flush();
        let i_sizes = minimize(path);
        avg_size_red.right_eq += (i_sizes.original - i_sizes.right_eq) / i_sizes.original;
        avg_size_red.left_eq += (i_sizes.original - i_sizes.left_eq) / i_sizes.original;
        avg_size_red.right_left_eq += (i_sizes.original - i_sizes.right_left_eq) / i_sizes.original;
        avg_size_red.left_right_eq += (i_sizes.original - i_sizes.left_right_eq) / i_sizes.original;
        avg_size_red.scores += (i_sizes.original - i_sizes.scores) / i_sizes.original;
        sizes.push(i_sizes);
    }

    avg_size_red.right_eq = (avg_size_red.right_eq / tests_count as f64) * 100.0;
    avg_size_red.left_eq = (avg_size_red.left_eq / tests_count as f64) * 100.0;
    avg_size_red.right_left_eq = (avg_size_red.right_left_eq / tests_count as f64) * 100.0;
    avg_size_red.left_right_eq = (avg_size_red.left_right_eq / tests_count as f64) * 100.0;
    avg_size_red.scores = (avg_size_red.scores / tests_count as f64) * 100.0;
    sizes.push(avg_size_red);

    let output_table = Table::new(sizes).to_string();
    println!("\nResults");
    println!("{}", output_table);
}
