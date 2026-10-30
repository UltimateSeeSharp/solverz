//! Usage: set_margin <d> <n1> <n2> ...
//! Margin game value m(S, d) (C33): the mover trailing by d on the numbers given (a multiset), payoff its final score
//! minus the opponent's, both players optimizing it. Checks sign(m) against `Solver::position` on the same position.

use catch_up::{Outcome, Solver};
use std::collections::HashMap;

/// m(s, d) on a sorted multiset.
fn margin(s: &[u64], d: u64, memo: &mut HashMap<(Vec<u64>, u64), i64>) -> i64 {
    if s.is_empty() {
        return -(d as i64);
    }
    if let Some(&v) = memo.get(&(s.to_vec(), d)) {
        return v;
    }
    let mut best = i64::MIN;
    for i in 0..s.len() {
        if i > 0 && s[i] == s[i - 1] {
            continue;
        }
        let x = s[i];
        let mut rest = s.to_vec();
        rest.remove(i);
        let o = if x >= d { -margin(&rest, x - d, memo) } else { margin(&rest, d - x, memo) };
        best = best.max(o);
    }
    memo.insert((s.to_vec(), d), best);
    best
}

fn sign(m: i64) -> Outcome {
    match m {
        m if m > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

fn main() {
    let args: Vec<u64> = std::env::args().skip(1).map(|a| a.parse().expect("d and positive integers")).collect();
    assert!(args.len() >= 2, "give d and the numbers");
    let d = args[0];
    let mut numbers = args[1..].to_vec();
    numbers.sort_unstable();
    let m = margin(&numbers, d, &mut HashMap::new());
    let solver = Solver::new(&numbers).position((1 << numbers.len()) - 1, d);
    assert_eq!(sign(m), solver, "sign(m) disagrees with Solver");
    println!("S = {numbers:?}, d = {d}: m = {m} (sign matches Solver: {solver:?})");
}
