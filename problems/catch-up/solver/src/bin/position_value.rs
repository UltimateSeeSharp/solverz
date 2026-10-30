//! Usage: position_value <d> <n1> <n2> ...
//! V(S, d): value for the mover trailing by d with the numbers S left (non-opening flag), from `Solver`,
//! and the mover's outcome after each pick; a pick below the deficit keeps the turn (marked +).

use catch_up::{Outcome, Solver};

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

fn main() {
    let args: Vec<u64> = std::env::args().skip(1).map(|a| a.parse().expect("non-negative integers")).collect();
    let (&deficit, numbers) = args.split_first().expect("give the deficit and the numbers");
    assert!(!numbers.is_empty(), "give the numbers");
    let total: u64 = numbers.iter().sum();
    let full = (1usize << numbers.len()) - 1;
    let mut solver = Solver::new(numbers);
    let picks: Vec<String> = (0..numbers.len())
        .map(|i| {
            let x = numbers[i];
            let rest = full & !(1 << i);
            if x >= deficit {
                format!("{x}:{}", letter(solver.position(rest, x - deficit).neg()))
            } else {
                format!("{x}+:{}", letter(solver.position(rest, deficit - x)))
            }
        })
        .collect();
    println!(
        "{numbers:?} total {total} deficit {deficit}: value {} (picks {})",
        letter(solver.position(full, deficit)),
        picks.join(" ")
    );
}
