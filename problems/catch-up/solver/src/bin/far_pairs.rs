//! Usage: far_pairs
//! Far-apart pairs (B11). S = P_1 ∪ … ∪ P_p, P_i = {a_i, a_i + 1}, a_1 < … < a_p.
//! V(S, g) = the mover's value with S left, trailing by g. Paper claim: if a_1 ≥ p and
//! a_{i+1} > sum(P_1 ∪ … ∪ P_i) + a_i + 1 for every i, then V(S, g) = f_p(g) for 0 ≤ g ≤ a_1, where
//! f_p(g) = draw if g ≤ p and g ≡ p (mod 2), win if g < p and g ≢ p, loss if g > p.
//! 1. The claim on sequences in that regime, p ≤ 7.
//! 2. Every pair set with p = 2, 3, 4 and max ≤ U_p: rows g ≤ min(p + 1, a_1) against f_p, by which
//!    hypotheses hold: A (a_1 ≥ p), F (the spacing above), F0 (a_{i+1} > sum(P_1 ∪ … ∪ P_i)).

use catch_up::{reference_value, Outcome, Solver};
use std::time::Instant;

const MAX_PAIRS: usize = 7;
/// a_1 − p in part 1.
const BOTTOM_OFFSETS: [u64; 3] = [0, 1, 5];
/// Part 1 cross-checks V(S, 0) = value(S) with `reference_value` up to this many pairs.
const REFERENCE_MAX_PAIRS: usize = 4;
/// (p, largest number) for part 2.
const EXHAUSTIVE: [(usize, u64); 3] = [(2, 80), (3, 60), (4, 40)];
const SHOWN: usize = 6;

fn f(p: usize, g: u64) -> Outcome {
    let p = p as u64;
    if g > p {
        Outcome::Loss
    } else if (p - g) % 2 == 0 {
        Outcome::Draw
    } else {
        Outcome::Win
    }
}

fn numbers(bottoms: &[u64]) -> Vec<u64> {
    bottoms.iter().flat_map(|&a| [a, a + 1]).collect()
}

fn pair_sum(a: u64) -> u64 {
    2 * a + 1
}

/// Hypothesis F: a_{i+1} > sum(P_1..P_i) + a_i + 1 for every i.
fn spaced(bottoms: &[u64]) -> bool {
    let mut below = 0;
    bottoms.windows(2).all(|w| {
        below += pair_sum(w[0]);
        w[1] > below + w[0] + 1
    })
}

/// Hypothesis F0: a_{i+1} > sum(P_1..P_i) for every i.
fn dominant(bottoms: &[u64]) -> bool {
    let mut below = 0;
    bottoms.windows(2).all(|w| {
        below += pair_sum(w[0]);
        w[1] > below
    })
}

/// Gaps g ≤ last where V(S, g) ≠ f_p(g).
fn mismatches(bottoms: &[u64], last: u64) -> Vec<(u64, Outcome)> {
    let xs = numbers(bottoms);
    let full = (1usize << xs.len()) - 1;
    let mut s = Solver::new(&xs);
    (0..=last).map(|g| (g, s.position(full, g))).filter(|&(g, o)| o != f(bottoms.len(), g)).collect()
}

/// Smallest sequence in the regime of the claim with a_1 = bottom.
fn regime_sequence(p: usize, bottom: u64) -> Vec<u64> {
    let mut bottoms = vec![bottom];
    let mut below = pair_sum(bottom);
    while bottoms.len() < p {
        let a = below + bottoms[bottoms.len() - 1] + 2;
        bottoms.push(a);
        below += pair_sum(a);
    }
    bottoms
}

/// Every increasing sequence of p pair bottoms with disjoint pairs and largest number ≤ max.
fn all_sequences(p: usize, max: u64) -> Vec<Vec<u64>> {
    fn go(p: usize, max: u64, from: u64, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        if cur.len() == p {
            out.push(cur.clone());
            return;
        }
        for a in from..max {
            cur.push(a);
            go(p, max, a + 2, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    go(p, max, 1, &mut Vec::new(), &mut out);
    out
}

fn show(bottoms: &[u64]) -> String {
    let xs: Vec<String> = numbers(bottoms).iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

fn main() {
    let start = Instant::now();
    println!("# far_pairs\n\n## 1. The claimed regime (a_1 ≥ p, spacing F), rows g ≤ a_1\n");
    println!("| p | a_1 | largest | gaps checked | mismatches |\n|---|---|---|---|---|");
    for p in 1..=MAX_PAIRS {
        for off in BOTTOM_OFFSETS {
            let bottoms = regime_sequence(p, p as u64 + off);
            let xs = numbers(&bottoms);
            let bad = mismatches(&bottoms, bottoms[0]);
            if p <= REFERENCE_MAX_PAIRS {
                let full = (1usize << xs.len()) - 1;
                assert_eq!(Solver::new(&xs).position(full, 0), reference_value(&xs), "{}", show(&bottoms));
            }
            println!("| {p} | {} | {} | {} | {} |", bottoms[0], xs[xs.len() - 1], bottoms[0] + 1, bad.len());
            for (g, o) in bad.iter().take(SHOWN) {
                println!("  - {} at g = {g}: {} (f_p: {})", show(&bottoms), letter(*o), letter(f(p, *g)));
            }
        }
    }

    println!("\n## 2. Every pair set with p pairs, largest ≤ U: rows g ≤ min(p + 1, a_1) against f_p\n");
    println!("| p | U | A | F | F0 | sets | with a mismatch | at g0 = p mod 2 |\n|---|---|---|---|---|---|---|---|");
    for (p, max) in EXHAUSTIVE {
        // (A, F, F0) → (sets, rows with a mismatch, mismatches at g0, examples)
        let mut tally: Vec<((bool, bool, bool), u64, u64, u64, Vec<String>)> = Vec::new();
        for bottoms in all_sequences(p, max) {
            let key = (bottoms[0] >= p as u64, spaced(&bottoms), dominant(&bottoms));
            let bad = mismatches(&bottoms, (p as u64 + 1).min(bottoms[0]));
            let at_g0 = bad.iter().any(|&(g, _)| g == p as u64 % 2);
            let i = match tally.iter().position(|t| t.0 == key) {
                Some(i) => i,
                None => {
                    tally.push((key, 0, 0, 0, Vec::new()));
                    tally.len() - 1
                }
            };
            let t = &mut tally[i];
            t.1 += 1;
            if !bad.is_empty() {
                t.2 += 1;
                if t.4.len() < SHOWN {
                    let row: Vec<String> = bad.iter().map(|&(g, o)| format!("g={g}:{}", letter(o))).collect();
                    t.4.push(format!("{} {}", show(&bottoms), row.join(" ")));
                }
            }
            if at_g0 {
                t.3 += 1;
            }
        }
        tally.sort_by_key(|t| std::cmp::Reverse(t.0));
        for (key, sets, bad, g0, _) in &tally {
            let yn = |b: bool| if b { "yes" } else { "no" };
            println!("| {p} | {max} | {} | {} | {} | {sets} | {bad} | {g0} |", yn(key.0), yn(key.1), yn(key.2));
        }
        for (key, _, _, _, ex) in &tally {
            for e in ex {
                println!("  - (A, F, F0) = {key:?}: {e}");
            }
        }
    }
    eprintln!("{:.1} s", start.elapsed().as_secs_f64());
}
