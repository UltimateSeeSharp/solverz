//! Usage: set_value <n1> <n2> ...
//! Value of Catch-Up on the given numbers for player 1, and player 1's outcome after each opening, from `Solver`;
//! for at most REFERENCE_LIMIT numbers also from the independent turn-by-turn `reference_value`.

use catch_up::{Outcome, Solver, reference_value};

const REFERENCE_LIMIT: usize = 10;

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

fn main() {
    let numbers: Vec<u64> = std::env::args().skip(1).map(|a| a.parse().expect("positive integers")).collect();
    assert!(!numbers.is_empty(), "give the numbers");
    let total: u64 = numbers.iter().sum();
    let mut solver = Solver::new(&numbers);
    let openings: Vec<String> = solver.openings().into_iter().map(|(x, o)| format!("{x}:{}", letter(o))).collect();
    println!("{numbers:?} total {total}: value {} (openings {})", letter(solver.value()), openings.join(" "));
    if numbers.len() <= REFERENCE_LIMIT {
        println!("reference_value: {}", letter(reference_value(&numbers)));
    }
}
