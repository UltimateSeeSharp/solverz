//! Usage: catch-up [max_n]   (default 20)
//! Prints, for each N, the optimal-play outcome of Catch-Up on {1..N} and player 1's opening options.

use catch_up::{interval, Outcome, Solver};
use std::time::Instant;

const DEFAULT_MAX_N: u64 = 20;

fn list(openings: &[(u64, Outcome)], want: Outcome) -> String {
    let xs: Vec<String> = openings.iter().filter(|&&(_, o)| o == want).map(|(x, _)| x.to_string()).collect();
    if xs.is_empty() { "-".into() } else { xs.join(",") }
}

fn main() {
    let max_n = std::env::args().nth(1).map_or(DEFAULT_MAX_N, |s| s.parse().expect("max_n must be a number"));
    println!("| N | total even | value (P1) | openings that win | draw | lose | positions | ms |");
    println!("|---|---|---|---|---|---|---|---|");
    for n in 1..=max_n {
        let start = Instant::now();
        let mut solver = Solver::new(&interval(n));
        let openings = solver.openings();
        let value = openings.iter().map(|&(_, o)| o).max().unwrap_or(Outcome::Draw);
        println!(
            "| {n} | {} | {value:?} | {} | {} | {} | {} | {} |",
            (n * (n + 1) / 2) % 2 == 0,
            list(&openings, Outcome::Win),
            list(&openings, Outcome::Draw),
            list(&openings, Outcome::Loss),
            solver.positions,
            start.elapsed().as_millis()
        );
    }
}
