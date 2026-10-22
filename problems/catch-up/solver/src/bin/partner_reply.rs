//! Usage: partner_reply [max_n]   (default 20)
//! Is answering with the partner a drawing reply? Pairs are adjacent: {2j−1, 2j} for even n,
//! {2j, 2j+1} with 1 alone for odd n. On {1..n} with an even total, take every drawn turn start
//! (R, g) of the defender and every y ∉ R that the attacker's turn can have ended with (y ≥ g) and
//! whose partner p is in R. Is taking p a drawing pick (the defender's value stays a draw)? Tallied
//! by the broken pairs of R and by whether p ends the defender's turn (p ≥ g).

use catch_up::{interval, Solver};
use std::time::Instant;

const DEFAULT_MAX_N: usize = 20;
const MAX_N: usize = 24;
/// Broken-pair counts tallied separately up to this; larger counts share the last row.
const MAX_BROKEN: usize = 6;
const SHOWN: usize = 5;
const CHECK_MAX_N: usize = 12;

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

/// Mover's values V(mask, g), g ≤ n: gaps never exceed the largest number.
fn values(n: usize) -> Vec<u8> {
    let stride = n + 1;
    let mut v = vec![LOSS; (1 << n) * stride];
    let mut sums = vec![0usize; 1 << n];
    v[0] = DRAW;
    for mask in 1..1usize << n {
        sums[mask] = sums[mask & (mask - 1)] + mask.trailing_zeros() as usize + 1;
        for g in 0..=n.min(sums[mask]) {
            let mut best = LOSS;
            for x in (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1) {
                let next = (mask & !(1 << (x - 1))) * stride;
                best = best.max(if x >= g { neg(v[next + x - g]) } else { v[next + g - x] });
                if best == WIN {
                    break;
                }
            }
            v[mask * stride + g] = best;
        }
    }
    v
}

fn partner(x: usize, n: usize) -> Option<usize> {
    match (n % 2, x) {
        (0, _) => Some(if x % 2 == 1 { x + 1 } else { x - 1 }),
        (_, 1) => None,
        _ => Some(if x % 2 == 0 { x + 1 } else { x - 1 }),
    }
}

fn has(mask: usize, x: usize) -> bool {
    mask >> (x - 1) & 1 == 1
}

fn broken(mask: usize, n: usize) -> usize {
    (1..=n).filter(|&x| has(mask, x) && partner(x, n).is_some_and(|p| !has(mask, p))).count()
}

fn show(mask: usize, n: usize) -> String {
    let xs: Vec<String> = (1..=n).filter(|&x| has(mask, x)).map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

/// Game phase: numbers taken, n − |R|, in buckets of PHASE_WIDTH.
const PHASE_WIDTH: usize = 4;
const PHASES: usize = 6;
/// Phases are tallied for turn starts with at most this many broken pairs.
const PHASE_MAX_BROKEN: usize = 3;

/// Turn-ending replies with few broken pairs and at most this many numbers taken are split by
/// the opponent's new gap p − g (capped) and by which number of the pair the attacker took.
const FEATURE_MAX_TAKEN: usize = 11;
const MAX_NEW_GAP: usize = 6;

/// [broken][ends turn] → (cases, drawing replies); [phase][ends turn] for few broken pairs;
/// [attacker took the upper number][new gap] for early turn-ending replies; the first failures.
struct Tally {
    cells: [[(u64, u64); 2]; MAX_BROKEN + 1],
    phases: [[(u64, u64); 2]; PHASES],
    features: [[(u64, u64); MAX_NEW_GAP + 1]; 2],
    failures: Vec<(usize, usize, usize, usize)>,
}

fn tally(n: usize) -> Tally {
    let stride = n + 1;
    let v = values(n);
    let mut t = Tally {
        cells: [[(0, 0); 2]; MAX_BROKEN + 1],
        phases: [[(0, 0); 2]; PHASES],
        features: [[(0, 0); MAX_NEW_GAP + 1]; 2],
        failures: Vec::new(),
    };
    for r in 1..1usize << n {
        let b = broken(r, n).min(MAX_BROKEN);
        let phase = ((n - r.count_ones() as usize) / PHASE_WIDTH).min(PHASES - 1);
        for g in 0..=n {
            if v[r * stride + g] != DRAW {
                continue;
            }
            for y in (g.max(1)..=n).filter(|&y| !has(r, y)) {
                let Some(p) = partner(y, n).filter(|&p| has(r, p)) else { continue };
                let rest = r & !(1 << (p - 1));
                let ends = p >= g;
                let drawing = if ends { neg(v[rest * stride + p - g]) == DRAW } else { v[rest * stride + g - p] == DRAW };
                let cell = &mut t.cells[b][ends as usize];
                cell.0 += 1;
                cell.1 += drawing as u64;
                if b <= PHASE_MAX_BROKEN {
                    let cell = &mut t.phases[phase][ends as usize];
                    cell.0 += 1;
                    cell.1 += drawing as u64;
                    if ends && n - r.count_ones() as usize <= FEATURE_MAX_TAKEN {
                        let cell = &mut t.features[(y > p) as usize][(p - g).min(MAX_NEW_GAP)];
                        cell.0 += 1;
                        cell.1 += drawing as u64;
                    }
                }
                if !drawing && t.failures.len() < 1 << 16 {
                    t.failures.push((b, r.count_ones() as usize, r, g * 64 + y));
                }
            }
        }
    }
    t
}

fn check(n: usize) {
    let stride = n + 1;
    let v = values(n);
    let mut dfs = Solver::new(&interval(n as u64));
    for mask in 0..1usize << n {
        for g in 0..=n {
            assert_eq!(v[mask * stride + g], dfs.position(mask, g as u64) as u8, "n {n} mask {mask:b} gap {g}");
        }
    }
}

fn main() {
    let max_n: usize = std::env::args().nth(1).map_or(DEFAULT_MAX_N, |s| s.parse().expect("max_n must be a number"));
    assert!((1..=MAX_N).contains(&max_n), "max_n out of range");
    let start = Instant::now();
    for n in 1..=max_n.min(CHECK_MAX_N) {
        check(n);
    }
    println!("Values checked against `Solver` on every position, n ≤ {}.\n", max_n.min(CHECK_MAX_N));
    println!("Partner reply p to the attacker's last pick y: drawing replies / cases, by broken pairs of R (D's turn start) and whether p ends D's turn.\n");
    for n in (3..=max_n).filter(|&n| n * (n + 1) / 2 % 2 == 0) {
        let mut t = tally(n);
        println!("### N = {n}\n");
        println!("| broken pairs | p ends the turn | p doesn't |\n|---|---|---|");
        for (b, row) in t.cells.iter().enumerate() {
            let label = if b == MAX_BROKEN { format!("≥ {b}") } else { b.to_string() };
            println!("| {label} | {} / {} | {} / {} |", row[1].1, row[1].0, row[0].1, row[0].0);
        }
        println!("\nAt most {PHASE_MAX_BROKEN} broken pairs, by numbers taken (n − |R|):\n");
        println!("| taken | p ends the turn | p doesn't |\n|---|---|---|");
        for (ph, row) in t.phases.iter().enumerate() {
            let lo = ph * PHASE_WIDTH;
            let label = if ph == PHASES - 1 { format!("≥ {lo}") } else { format!("{lo}–{}", lo + PHASE_WIDTH - 1) };
            println!("| {label} | {} / {} | {} / {} |", row[1].1, row[1].0, row[0].1, row[0].0);
        }
        println!("\nTurn-ending replies, ≤ {PHASE_MAX_BROKEN} broken pairs, ≤ {FEATURE_MAX_TAKEN} taken, by the opponent's new gap p − g:\n");
        let gaps: Vec<String> = (0..=MAX_NEW_GAP).map(|d| if d == MAX_NEW_GAP { format!("≥ {d}") } else { d.to_string() }).collect();
        println!("| attacker took | {} |\n|---|{}", gaps.join(" | "), "---|".repeat(MAX_NEW_GAP + 1));
        for (upper, row) in t.features.iter().enumerate() {
            let cells: Vec<String> = row.iter().map(|(n, ok)| format!("{ok} / {n}")).collect();
            println!("| {} | {} |", if upper == 1 { "upper (p = y − 1)" } else { "lower (p = y + 1)" }, cells.join(" | "));
        }
        t.failures.sort();
        let shown: Vec<String> = t
            .failures
            .iter()
            .take(SHOWN)
            .map(|&(b, _, r, gy)| {
                let (g, y) = (gy / 64, gy % 64);
                format!("R = {}, g = {g}, y = {y} ({b} broken)", show(r, n))
            })
            .collect();
        println!("\nFewest broken pairs among failures: {}\n", shown.join("; "));
    }
    println!("Total {} ms", start.elapsed().as_millis());
}
