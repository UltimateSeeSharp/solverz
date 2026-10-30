//! Usage: e21_dense_holes <n_min> <n_max>
//! Is the mover ever losing on a dense set? For each N: every S = {1..N} ∖ H, |H| ≤ MAX_HOLES, and every deficit
//! 0 ≤ d ≤ N with d + sum(S) even; prints the losses (CU-L003 says there are none for 9 ≤ N ≤ 25).
//! Then C5's three-hole question: S = {1..m} ∖ H, H ⊆ {1..m−1}, |H| = 3, m ≤ C5_MAX_M, gaps g ≡ sum(S) (mod 2)
//! with C5_LOW_GAP ≤ g ≤ sum(S)/C5_GAP_DEN; lists each non-draw as W or L.
//! One `Solver` on {1..N} answers every subset. First checks it: game values against `reference_value` and fresh
//! per-set solvers, and {1..N} drawn exactly at even totals (E1).

use catch_up::{Outcome, Solver, interval, reference_value};
use std::time::Instant;

const MAX_HOLES: u32 = 3;
const C5_HOLES: u32 = 3;
const C5_MAX_M: usize = 16;
const C5_LOW_GAP: u64 = 5;
const C5_GAP_DEN: u64 = 12;
/// Game values of every S ⊆ {1..REFERENCE_U} are checked against `reference_value`.
const REFERENCE_U: usize = 9;
/// Positions of every S ⊆ {1..FRESH_U}, d ≤ FRESH_U, are checked against a fresh `Solver` on S.
const FRESH_U: usize = 9;
/// Losses printed per N.
const SHOWN: usize = 50;

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

/// Bit i of a mask stands for the number i + 1.
fn members(mask: usize, n: usize) -> Vec<u64> {
    (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| i as u64 + 1).collect()
}

fn show(xs: &[u64]) -> String {
    format!("{{{}}}", xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

/// Game value of `mask` from the mover's positions: the opening is one pick, then the turn passes.
fn game_value(solver: &mut Solver, mask: usize, n: usize) -> Outcome {
    (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| solver.position(mask & !(1 << i), i as u64 + 1).neg()).max().unwrap()
}

/// Masks of every H ⊆ {1..n} with |H| ≤ max_holes.
fn hole_masks(n: usize, max_holes: u32) -> Vec<usize> {
    (0..1usize << n).filter(|h| h.count_ones() <= max_holes).collect()
}

fn self_check() {
    let mut mismatches = 0u64;
    let mut solver = Solver::new(&interval(REFERENCE_U as u64));
    for s in 1..1usize << REFERENCE_U {
        if game_value(&mut solver, s, REFERENCE_U) != reference_value(&members(s, REFERENCE_U)) {
            mismatches += 1;
        }
    }
    println!("check: game value vs reference_value on every S ⊆ {{1..{REFERENCE_U}}}: {mismatches} mismatches");

    let mut mismatches = 0u64;
    let mut solver = Solver::new(&interval(FRESH_U as u64));
    for s in 1..1usize << FRESH_U {
        let xs = members(s, FRESH_U);
        let mut fresh = Solver::new(&xs);
        let full = (1usize << xs.len()) - 1;
        if game_value(&mut solver, s, FRESH_U) != fresh.value() {
            mismatches += 1;
        }
        for d in 0..=FRESH_U as u64 {
            if solver.position(s, d) != fresh.position(full, d) {
                mismatches += 1;
            }
        }
    }
    println!("check: positions vs a fresh Solver on every S ⊆ {{1..{FRESH_U}}}, d ≤ {FRESH_U}: {mismatches} mismatches");
}

fn dense_losses(n: usize) {
    let start = Instant::now();
    let mut solver = Solver::new(&interval(n as u64));
    let full = (1usize << n) - 1;
    let total = (n * (n + 1) / 2) as u64;
    let interval_value = game_value(&mut solver, full, n);
    let expected = if total % 2 == 0 { Outcome::Draw } else { Outcome::Win };
    let (mut sets, mut positions, mut wins, mut draws) = (0u64, 0u64, 0u64, 0u64);
    let mut losses: Vec<(Vec<u64>, u64)> = vec![];
    for h in hole_masks(n, MAX_HOLES) {
        let s = full & !h;
        if s == 0 {
            continue;
        }
        sets += 1;
        let sum: u64 = members(s, n).iter().sum();
        for d in (sum % 2..=n as u64).step_by(2) {
            positions += 1;
            match solver.position(s, d) {
                Outcome::Win => wins += 1,
                Outcome::Draw => draws += 1,
                Outcome::Loss => losses.push((members(h, n), d)),
            }
        }
    }
    println!(
        "N = {n}: {{1..N}} value {} (E1: {}); {sets} sets, {positions} positions: {wins} W, {draws} D, {} L ({:.1} s)",
        letter(interval_value),
        letter(expected),
        losses.len(),
        start.elapsed().as_secs_f64()
    );
    for (h, d) in losses.iter().take(SHOWN) {
        println!("  loss: S = {{1..{n}}} ∖ {}, d = {d}", show(h));
    }
}

fn c5_three_holes() {
    let mut solver = Solver::new(&interval(C5_MAX_M as u64));
    let (mut positions, mut wins, mut losses) = (0u64, 0u64, 0u64);
    println!("C5, |H| = {C5_HOLES}, m ≤ {C5_MAX_M}, {C5_LOW_GAP} ≤ g ≤ sum/{C5_GAP_DEN}, non-draws:");
    for m in 1..=C5_MAX_M {
        let below = (1usize << (m - 1)) - 1; // H ⊆ {1..m−1}
        for h in hole_masks(m - 1, C5_HOLES).into_iter().filter(|h| h.count_ones() == C5_HOLES) {
            let s = (below | 1 << (m - 1)) & !h;
            let sum: u64 = members(s, m).iter().sum();
            let low = C5_LOW_GAP + (C5_LOW_GAP + sum) % 2;
            for g in (low..=sum / C5_GAP_DEN).step_by(2) {
                positions += 1;
                let v = solver.position(s, g);
                if v != Outcome::Draw {
                    if v == Outcome::Win { wins += 1 } else { losses += 1 }
                    println!("  m = {m}, S = {}, g = {g}: {}", show(&members(s, m)), letter(v));
                }
            }
        }
    }
    println!("C5: {positions} positions, {wins} W, {losses} L");
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("n_min n_max")).collect();
    let (n_min, n_max) = (args[0], args[1]);
    assert!(1 <= n_min && n_min <= n_max && n_max <= catch_up::MAX_NUMBERS, "N range out of bounds");
    self_check();
    c5_three_holes();
    for n in n_min..=n_max {
        dense_losses(n);
    }
}
