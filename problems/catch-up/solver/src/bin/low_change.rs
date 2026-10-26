//! Usage: low_change [sample_every] [random_cores] [seed]   (defaults 6, 20, 1)
//! How much low change cures a sparse high core (B22)? Cores C: pair sets with 5 pairs whose value
//! at gap 1 (their draw-parity gap) is not a draw (O7). For S_k = {1..k} ∪ C, k ≤ MAX_LOW, g0(S_k) =
//! sum(S_k) mod 2; prints V(S_k, g0) for every k and k(C) = the least k from which every S_k draws
//! (up to MAX_LOW), against min C and 2·min C. Cores: every core with max 31–44 (count checked
//! against the refuter's 232), every `sample_every`-th of them profiled, plus random failing cores
//! with max ≤ RANDOM_MAX. One layered table on {1..MAX_LOW} ∪ C per core.

use catch_up::layered::Layered;
use catch_up::{Outcome, Solver};
use std::time::Instant;

const PAIRS: usize = 5;
const MAX_LOW: usize = 12;
const HUNT_MIN_MAX: u64 = 31;
const HUNT_MAX_MAX: u64 = 44;
/// Non-draw cores with max 31–44 found by the refuter (scratch/refuter/l8/hunt-E5-31-44.txt).
const REFUTER_COUNT: usize = 232;
const RANDOM_MAX: u64 = 60;
/// Random cores must lie above the low block.
const RANDOM_MIN: u64 = MAX_LOW as u64 + 1;

/// Pair sets with `PAIRS` pairs, bottoms ≥ lo, largest number ≤ hi.
fn cores(lo: u64, hi: u64) -> Vec<Vec<u64>> {
    fn go(from: u64, hi: u64, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        if cur.len() == 2 * PAIRS {
            out.push(cur.clone());
            return;
        }
        for a in from..hi {
            cur.extend([a, a + 1]);
            go(a + 2, hi, cur, out);
            cur.truncate(cur.len() - 2);
        }
    }
    let mut out = Vec::new();
    go(lo, hi, &mut Vec::new(), &mut out);
    out
}

fn fails(core: &[u64]) -> bool {
    let full = (1usize << core.len()) - 1;
    Solver::new(core).position(full, (PAIRS % 2) as u64) != Outcome::Draw
}

/// V({1..k} ∪ C, g0) for k = 0..=MAX_LOW.
fn profile(core: &[u64]) -> Vec<Outcome> {
    let numbers: Vec<u64> = (1..=MAX_LOW as u64).chain(core.iter().copied()).collect();
    let l = Layered::new(&numbers);
    let core_bits = ((1u64 << core.len()) - 1) << MAX_LOW;
    let core_sum: u64 = core.iter().sum();
    let mut out = vec![Outcome::Loss; MAX_LOW + 1];
    let last = l.run(|size, layer| {
        if size >= core.len() && size - core.len() < MAX_LOW {
            let k = size - core.len();
            let mask = core_bits | ((1u64 << k) - 1);
            let g0 = ((core_sum + (k * (k + 1) / 2) as u64) % 2) as usize;
            out[k] = l.get(layer, l.rank(mask), g0);
        }
    });
    // `run` stops at layer n − 1; k = MAX_LOW is the full set, by the recurrence from that layer.
    let full = (1u64 << numbers.len()) - 1;
    let g0 = ((core_sum + (MAX_LOW * (MAX_LOW + 1) / 2) as u64) % 2) as usize;
    out[MAX_LOW] = (0..numbers.len())
        .map(|i| {
            let x = numbers[i] as usize;
            let r = l.rank(full & !(1 << i));
            if x >= g0 { l.get(&last, r, x - g0).neg() } else { l.get(&last, r, g0 - x) }
        })
        .max()
        .unwrap();
    out
}

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

/// xorshift64
fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn main() {
    let mut args = std::env::args().skip(1).map(|a| a.parse::<u64>().expect("numbers"));
    let every = args.next().unwrap_or(6) as usize;
    let randoms = args.next().unwrap_or(20) as usize;
    let mut seed = args.next().unwrap_or(1).max(1);
    let start = Instant::now();
    let hunted: Vec<Vec<u64>> = cores(1, HUNT_MAX_MAX).into_iter().filter(|c| c[c.len() - 1] >= HUNT_MIN_MAX && fails(c)).collect();
    assert_eq!(hunted.len(), REFUTER_COUNT, "refuter's count of failing cores");
    let mut picked: Vec<Vec<u64>> = hunted.iter().step_by(every).cloned().collect();
    let mut found = 0;
    while found < randoms {
        let mut bottoms: Vec<u64> = Vec::new();
        while bottoms.len() < PAIRS {
            let a = RANDOM_MIN + next(&mut seed) % (RANDOM_MAX - RANDOM_MIN);
            if bottoms.iter().all(|&b| b.abs_diff(a) >= 2) {
                bottoms.push(a);
            }
        }
        bottoms.sort();
        let core: Vec<u64> = bottoms.iter().flat_map(|&a| [a, a + 1]).collect();
        if fails(&core) {
            picked.push(core);
            found += 1;
        }
    }
    println!("# low_change {every} {randoms}\n");
    println!("{} failing cores with 5 pairs and max {HUNT_MIN_MAX}–{HUNT_MAX_MAX} (matches the refuter's {REFUTER_COUNT}); every {every}th profiled, plus {randoms} random failing cores with numbers {RANDOM_MIN}–{RANDOM_MAX}.\n", hunted.len());
    println!("V({{1..k}} ∪ C, g0) for k = 0..{MAX_LOW}; k(C) = least k with draws for all k..{MAX_LOW}; T(k) = 1+…+k.\n");
    println!("| C | min C | 2·min C | V for k = 0..{MAX_LOW} | k(C) | T(k(C)) | T(k(C) − 1) |\n|---|---|---|---|---|---|---|");
    for core in &picked {
        let prof = profile(core);
        let kc = (0..=MAX_LOW).find(|&k| prof[k..].iter().all(|&o| o == Outcome::Draw));
        let (kcs, tk, tk1) = match kc {
            Some(k) => (k.to_string(), (k * (k + 1) / 2).to_string(), if k > 0 { ((k - 1) * k / 2).to_string() } else { "—".into() }),
            None => ("—".into(), "—".into(), "—".into()),
        };
        let xs: Vec<String> = core.iter().map(|x| x.to_string()).collect();
        println!("| {{{}}} | {} | {} | {} | {kcs} | {tk} | {tk1} |", xs.join(","), core[0], 2 * core[0], prof.iter().map(|&o| letter(o)).collect::<String>());
    }
    eprintln!("{:.1} s", start.elapsed().as_secs_f64());
}
