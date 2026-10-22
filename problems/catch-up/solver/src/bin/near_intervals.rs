//! Usage: near_intervals [universe]   (default 26)
//! Are sets close to {1..m} draws? R = {1..m} ∖ H, H ⊆ {1..m−1}, h = |H| ≤ MAX_HOLES, m ≤ U.
//! (a) Fresh games: value(R) = V(R, 0) for even sum(R).
//! (b) Moderate gaps: V(R, g) for draw-parity g (g ≡ sum(R) mod 2) with LOW_GAP ≤ g ≤ sum(R)/GAP_DEN,
//!     g ≤ U (the layered table stores gaps up to max = U).
//! One layered table on {1..U}; non-draws are re-solved with `Solver`.

use catch_up::layered::Layered;
use catch_up::{interval, Outcome, Solver};
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 26;
const MAX_HOLES: usize = 6;
const LOW_GAP: usize = 5;
const GAP_DEN: usize = 12;
const SHOWN: usize = 6;
/// Non-draws are re-solved with `Solver` when R has at most this many numbers.
const VERIFY_MAX_SIZE: u32 = 22;

/// Next larger mask with the same number of bits (Gosper's hack): colex order.
fn next_combination(mask: u64) -> u64 {
    if mask == 0 {
        return 0;
    }
    let t = mask | (mask - 1);
    (t + 1) | (((!t & (t + 1)) - 1) >> (mask.trailing_zeros() + 1))
}

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

/// Tallies per hole count: [h] → (sets or positions, non-draws, examples (m, mask, g, value)).
#[derive(Default, Clone)]
struct Tally {
    total: u64,
    bad: u64,
    largest_m: usize,
    examples: Vec<(usize, u64, usize, Outcome)>,
}

impl Tally {
    fn add(&mut self, m: usize, mask: u64, g: usize, v: Outcome) {
        self.total += 1;
        if v != Outcome::Draw {
            self.bad += 1;
            self.largest_m = self.largest_m.max(m);
            self.examples.push((m, mask, g, v));
        }
    }
}

/// Tallies one set; `value(g)` = V(mask, g) for g ≤ `max_gap`.
fn record(fresh: &mut [Tally], moderate: &mut [Tally], mask: u64, max_gap: usize, value: impl Fn(usize) -> Outcome) {
    let m = max_number(mask);
    let h = m - mask.count_ones() as usize;
    if mask == 0 || h > MAX_HOLES {
        return;
    }
    let sum: usize = numbers_of(mask).iter().sum::<u64>() as usize;
    if sum % 2 == 0 {
        fresh[h].add(m, mask, 0, value(0));
    }
    for g in (LOW_GAP + (LOW_GAP + sum) % 2..=(sum / GAP_DEN).min(max_gap)).step_by(2) {
        moderate[h].add(m, mask, g, value(g));
    }
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((MAX_HOLES + 2..=30).contains(&u), "universe out of range");
    let start = Instant::now();
    let l = Layered::new(&interval(u as u64));
    let mut fresh = vec![Tally::default(); MAX_HOLES + 1];
    let mut moderate = vec![Tally::default(); MAX_HOLES + 1];
    let last = l.run(|k, layer| {
        // Near-intervals with k numbers have max ≤ k + MAX_HOLES: stop at the first larger mask.
        let mut mask: u64 = (1 << k) - 1;
        for r in 0..l.layer_len(k) {
            if max_number(mask) > k + MAX_HOLES {
                break;
            }
            record(&mut fresh, &mut moderate, mask, u, |g| l.get(layer, r, g));
            mask = next_combination(mask);
        }
    });
    // `run` stops at layer u − 1; the full set's row by the recurrence, from layer u − 1.
    let full = (1u64 << u) - 1;
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
    if u <= VERIFY_MAX_SIZE as usize {
        let mut dfs = Solver::new(&interval(u as u64));
        for (g, &v) in full_row.iter().enumerate() {
            assert_eq!(v, dfs.position(full as usize, g as u64), "{{1..{u}}} at gap {g}");
        }
    }
    record(&mut fresh, &mut moderate, full, u, |g| full_row[g]);
    println!("Universe {{1..{u}}}: {} ms\n", start.elapsed().as_millis());
    report("(a) Even-sum {1..m} ∖ H as fresh games (gap 0)", &fresh, u);
    report(&format!("(b) Draw-parity gaps {LOW_GAP} ≤ g ≤ min(sum/{GAP_DEN}, {u})"), &moderate, u);
    println!("Every listed non-draw re-solved with `Solver` (sets of at most {VERIFY_MAX_SIZE} numbers). Total {} ms", start.elapsed().as_millis());
}

fn report(title: &str, tallies: &[Tally], u: usize) {
    println!("## {title}\n");
    println!("m ≤ {u}, H ⊆ {{1..m−1}}, h = |H|.\n");
    println!("| h | checked | not draws | largest m with a non-draw | non-draws at the largest m |\n|---|---|---|---|---|");
    for (h, t) in tallies.iter().enumerate() {
        let mut at_largest: Vec<&(usize, u64, usize, Outcome)> = t.examples.iter().filter(|e| e.0 == t.largest_m).collect();
        at_largest.sort_by_key(|e| (e.1, e.2));
        let shown: Vec<String> = at_largest
            .iter()
            .take(SHOWN)
            .map(|&&(_, mask, g, v)| {
                if mask.count_ones() <= VERIFY_MAX_SIZE && g <= max_number(mask) {
                    let mut dfs = Solver::new(&numbers_of(mask));
                    let all = (1usize << mask.count_ones()) - 1;
                    assert_eq!(dfs.position(all, g as u64), v, "{} at gap {g}", show(mask));
                }
                format!("{} g={g} {v:?}", show(mask))
            })
            .collect();
        let largest = if t.bad == 0 { "-".to_string() } else { t.largest_m.to_string() };
        println!("| {h} | {} | {} | {largest} | {} |", t.total, t.bad, shown.join("; "));
    }
    println!();
}
