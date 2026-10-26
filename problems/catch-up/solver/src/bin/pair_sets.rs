//! Usage: pair_sets [universe]   (default 24)
//! Are sets made of adjacent pairs draws? Two classes of S ⊆ {1..U}, p pairs, g0 = p mod 2 (the
//! smallest draw-parity gap, since each pair has an odd sum):
//! (E) every maximal run of consecutive numbers in S has even length, so S splits into p pairs
//!     {x, x+1}. {1..N} for N ≡ 0 mod 4 is E with p even: V(S, 0) = value(S), the goal.
//! (T) {1,2,3} ∪ an E set above 3. {1..N} for N ≡ 3 mod 4 is T with p even.
//! Claim: V(S, g0) = draw for every S in either class. Also, for E: the first draw-parity gap
//! g ≤ min(sum, U) at which S is not a draw (the draw band). One layered table on {1..U}.

use catch_up::layered::Layered;
use catch_up::{interval, Outcome, Solver};
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 24;
/// Every class member with max ≤ CHECK_UNIVERSE is re-solved with `Solver` at all draw-parity gaps.
const CHECK_UNIVERSE: usize = 16;
/// Universe of the ideator's count (scratch/ideator): 5,472 E sets with p even, 5,473 with p odd.
const REPRODUCE_UNIVERSE: usize = 20;
const SHOWN: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    E,
    T,
}
const CLASSES: [Class; 2] = [Class::E, Class::T];
const TRIPLE: u64 = 0b111;

fn max_number(mask: u64) -> usize {
    (u64::BITS - mask.leading_zeros()) as usize
}

fn numbers_of(mask: u64) -> Vec<u64> {
    (0..64).filter(|&i| mask >> i & 1 == 1).map(|i| i as u64 + 1).collect()
}

fn show(mask: u64) -> String {
    let xs: Vec<String> = numbers_of(mask).iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

/// Every E set ⊆ {lo..u} (number x ↔ bit x − 1), the empty set included: at each x, skip it or
/// take the pair {x, x+1}.
fn e_sets(lo: usize, u: usize) -> Vec<u64> {
    fn go(x: usize, u: usize, mask: u64, out: &mut Vec<u64>) {
        if x > u {
            out.push(mask);
            return;
        }
        go(x + 1, u, mask, out);
        if x < u {
            go(x + 2, u, mask | 0b11 << (x - 1), out);
        }
    }
    let mut out = Vec::new();
    go(lo, u, 0, &mut out);
    out
}

fn members(class: Class, u: usize) -> Vec<u64> {
    match class {
        Class::E => e_sets(1, u).into_iter().filter(|&m| m != 0).collect(),
        Class::T => e_sets(4, u).into_iter().map(|m| m | TRIPLE).collect(),
    }
}

fn pairs(class: Class, mask: u64) -> u32 {
    match class {
        Class::E => mask.count_ones() / 2,
        Class::T => (mask.count_ones() - 3) / 2,
    }
}

fn sum_of(mask: u64) -> usize {
    numbers_of(mask).iter().sum::<u64>() as usize
}

#[derive(Default)]
struct Tally {
    /// [p mod 2] → (checked, not draws)
    by_parity: [(u64, u64); 2],
    /// Non-draws at g0: (mask, value).
    bad: Vec<(u64, Outcome)>,
    /// Members with max ≤ REPRODUCE_UNIVERSE, by p mod 2.
    small: [u64; 2],
    /// E only: [g] → sets whose first non-draw draw-parity gap is g; [u + 1] → none up to min(sum, u).
    first_fail: Vec<u64>,
    first_fail_examples: Vec<Vec<u64>>,
}

/// Tallies one member; `row(g)` = V(mask, g) for g ≤ u.
fn record(t: &mut Tally, class: Class, mask: u64, u: usize, row: impl Fn(usize) -> Outcome) {
    let p = pairs(class, mask) as usize;
    let g0 = p % 2;
    let v = row(g0);
    t.by_parity[g0].0 += 1;
    if max_number(mask) <= REPRODUCE_UNIVERSE {
        t.small[g0] += 1;
    }
    if v != Outcome::Draw {
        t.by_parity[g0].1 += 1;
        t.bad.push((mask, v));
    }
    if class == Class::E {
        let top = sum_of(mask).min(u);
        let f = (g0..=top).step_by(2).find(|&g| row(g) != Outcome::Draw).unwrap_or(u + 1);
        t.first_fail[f] += 1;
        if t.first_fail_examples[f].len() < SHOWN {
            t.first_fail_examples[f].push(mask);
        }
    }
}

fn verify(mask: u64, g: usize, v: Outcome) {
    let mut dfs = Solver::new(&numbers_of(mask));
    let all = (1usize << mask.count_ones()) - 1;
    assert_eq!(dfs.position(all, g as u64), v, "{} at gap {g}", show(mask));
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((REPRODUCE_UNIVERSE..=30).contains(&u), "universe out of range");
    let start = Instant::now();
    let l = Layered::new(&interval(u as u64));
    let full = (1u64 << u) - 1;
    let classes: Vec<Vec<u64>> = CLASSES.iter().map(|&c| members(c, u)).collect();
    // Members by size, so each layer reads only its own rows.
    let mut by_size: Vec<Vec<(usize, u64)>> = vec![Vec::new(); u + 1];
    for (ci, ms) in classes.iter().enumerate() {
        for &m in ms {
            by_size[m.count_ones() as usize].push((ci, m));
        }
    }
    let mut tallies: Vec<Tally> = CLASSES
        .iter()
        .map(|_| Tally { first_fail: vec![0; u + 2], first_fail_examples: vec![Vec::new(); u + 2], ..Default::default() })
        .collect();
    let mut checked_small = 0u64;
    // interval_gap0[n] = V({1..n}, 0) = value({1..n}).
    let mut interval_gap0 = vec![Outcome::Draw; u + 1];
    let last = l.run(|k, layer| {
        for &(ci, mask) in &by_size[k] {
            let r = l.rank(mask);
            let row = |g: usize| l.get(layer, r, g);
            if mask == (1 << k) - 1 {
                interval_gap0[k] = row(0);
            }
            if max_number(mask) <= CHECK_UNIVERSE {
                let sum = sum_of(mask);
                for g in (sum % 2..=max_number(mask).min(sum)).step_by(2) {
                    verify(mask, g, row(g));
                }
                checked_small += 1;
            }
            record(&mut tallies[ci], CLASSES[ci], mask, u, row);
        }
    });
    // `run` stops at layer u − 1; the full set's row by the recurrence, from layer u − 1.
    let full_row: Vec<Outcome> = (0..=u)
        .map(|g| {
            (1..=u)
                .map(|x| {
                    let r = l.rank(full & !(1 << (x - 1)));
                    if x >= g { l.get(&last, r, x - g).neg() } else { l.get(&last, r, g - x) }
                })
                .max()
                .unwrap()
        })
        .collect();
    let full_class = if u % 2 == 0 { 0 } else { 1 };
    record(&mut tallies[full_class], CLASSES[full_class], full, u, |g| full_row[g]);
    interval_gap0[u] = full_row[0];
    println!("Universe {{1..{u}}}: {} ms. Every member with max ≤ {CHECK_UNIVERSE} ({checked_small} sets) matches `Solver` at every draw-parity gap ≤ its max.\n", start.elapsed().as_millis());

    let intervals: Vec<String> = (1..=u)
        .filter(|n| n % 4 == 0 || n % 4 == 3)
        .map(|n| format!("{n} ({:?}): {:?}", CLASSES[if n % 4 == 0 { 0 } else { 1 }], interval_gap0[n]))
        .collect();
    println!("Even-total intervals {{1..N}} in the classes, V at gap 0: {}\n", intervals.join(", "));

    println!("## V(S, g0) = draw?\n");
    println!("| class | p even: checked | not draws | p odd: checked | not draws | max ≤ {REPRODUCE_UNIVERSE}: p even, p odd |\n|---|---|---|---|---|---|");
    for (c, t) in CLASSES.iter().zip(&tallies) {
        let [(ce, be), (co, bo)] = t.by_parity;
        println!("| {c:?} | {ce} | {be} | {co} | {bo} | {}, {} |", t.small[0], t.small[1]);
    }
    println!();
    for (c, t) in CLASSES.iter().zip(&tallies) {
        let mut bad = t.bad.clone();
        bad.sort_by_key(|&(m, _)| (max_number(m), m));
        for &(m, v) in bad.iter().take(SHOWN) {
            let g0 = pairs(*c, m) as usize % 2;
            if m.count_ones() <= 22 {
                verify(m, g0, v);
            }
            println!("- {c:?} non-draw: {} at g0 = {g0}: {v:?}", show(m));
        }
    }

    println!("\n## E: first draw-parity gap that is not a draw\n");
    println!("Gaps g ≡ sum (mod 2), g0 ≤ g ≤ min(sum, {u}); 'none' = all draw.\n");
    println!("| first non-draw gap | E sets | examples |\n|---|---|---|");
    let t = &tallies[0];
    for (f, &n) in t.first_fail.iter().enumerate() {
        if n == 0 {
            continue;
        }
        let label = if f == u + 1 { "none".to_string() } else { f.to_string() };
        let ex: Vec<String> = t.first_fail_examples[f].iter().map(|&m| show(m)).collect();
        println!("| {label} | {n} | {} |", ex.join("; "));
    }
    println!("\nTotal {} ms", start.elapsed().as_millis());
}
