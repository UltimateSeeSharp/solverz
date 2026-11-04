//! Usage: e23_rank_perturbed <l_min> <l_max> <samples> <seed> <threads>
//! C84 (DI): M_ε = {j − ε_j : 1 ≤ j ≤ L}, ε ∈ {0, 1}^L, ε₁ = 0, is a draw at deficit g = sum(M_ε) mod 2.
//! Per L: ε = 0, the twins ε = [j even], and `samples` random ε (half uniform, half sparse: each ε_j = 1 with
//! probability 1/SPARSE_DEN). Each member gets its own outcome table over its sub-multisets (mixed radix by
//! multiplicity), storing only gaps d ≡ sum (mod 2), the parity every reachable position keeps.
//! First checks: table = `Solver` on every position of every member for L ≤ CHECK_L; every member draws for
//! L ≤ EXHAUSTIVE_L (the ideator's data, C84 Evidence); ε = 0 at gap 0 = E1 at even totals.

use catch_up::{Outcome, Solver};
use rayon::prelude::*;
use std::time::Instant;

const CHECK_L: usize = 8;
const EXHAUSTIVE_L: usize = 14;
const SPARSE_DEN: u64 = 8;
const E1_VALUES: &str = "WWDDWWDDLLDDWLDDWLDDWWDDWWDDWWD";
const LOSS: i8 = -1;
const DRAW: i8 = 0;
const WIN: i8 = 1;

/// Bit j − 1 of `eps` is ε_j.
fn multiset(l: usize, eps: u64) -> Vec<u64> {
    (1..=l).map(|j| (j as u64) - (eps >> (j - 1) & 1)).collect()
}

/// Outcome table of one multiset: state = remaining sub-multiset in mixed radix over its distinct values.
struct Table {
    values: Vec<u64>,
    pw: Vec<usize>,
    radix: Vec<usize>,
    /// Gap slots per state: d = 2k + parity(state), k < half.
    half: usize,
    o: Vec<i8>,
}

impl Table {
    fn new(xs: &[u64]) -> Self {
        let mut values: Vec<u64> = xs.to_vec();
        values.sort_unstable();
        values.dedup();
        let radix: Vec<usize> = values.iter().map(|v| xs.iter().filter(|&&x| x == *v).count() + 1).collect();
        let mut pw = vec![1usize; values.len() + 1];
        for i in 0..values.len() {
            pw[i + 1] = pw[i] * radix[i];
        }
        let max = *values.last().unwrap_or(&0) as usize;
        let half = max / 2 + 1;
        let states = pw[values.len()];
        let mut o = vec![DRAW; states * half];
        let mut best = vec![LOSS; half];
        for s in 0..states {
            let par = Self::parity_of(&values, &pw, &radix, s);
            let row = s * half;
            if s == 0 {
                for k in 0..half {
                    o[row + k] = if 2 * k + par == 0 { DRAW } else { LOSS };
                }
                continue;
            }
            best.fill(LOSS);
            for i in 0..values.len() {
                if (s / pw[i]) % radix[i] == 0 {
                    continue;
                }
                let x = values[i] as usize;
                let nx = s - pw[i];
                let npar = par ^ (x & 1);
                let nrow = nx * half;
                for k in 0..half {
                    let d = 2 * k + par;
                    let v = if x >= d { -o[nrow + (x - d - npar) / 2] } else { o[nrow + (d - x - npar) / 2] };
                    if v > best[k] {
                        best[k] = v;
                    }
                }
            }
            o[row..row + half].copy_from_slice(&best);
        }
        Table { values, pw, radix, half, o }
    }

    fn parity_of(values: &[u64], pw: &[usize], radix: &[usize], s: usize) -> usize {
        (0..values.len()).map(|i| (s / pw[i]) % radix[i] * values[i] as usize).sum::<usize>() & 1
    }

    fn full(&self) -> usize {
        self.pw[self.values.len()] - 1
    }

    /// Outcome for the mover trailing by d, d ≡ sum(state) (mod 2), d < 2·half.
    fn at(&self, s: usize, d: usize) -> i8 {
        let par = Self::parity_of(&self.values, &self.pw, &self.radix, s);
        assert_eq!(d & 1, par, "gap of the wrong parity");
        self.o[s * self.half + d / 2]
    }

    fn numbers(&self, s: usize) -> Vec<u64> {
        let mut xs = vec![];
        for i in 0..self.values.len() {
            for _ in 0..(s / self.pw[i]) % self.radix[i] {
                xs.push(self.values[i]);
            }
        }
        xs
    }
}

fn code(o: Outcome) -> i8 {
    o as i8 - 1
}

fn letter(v: i8) -> char {
    match v {
        WIN => 'W',
        DRAW => 'D',
        _ => 'L',
    }
}

/// Value at the parity deficit g = sum mod 2.
fn member_value(l: usize, eps: u64) -> i8 {
    let xs = multiset(l, eps);
    let g = (xs.iter().sum::<u64>() & 1) as usize;
    let t = Table::new(&xs);
    t.at(t.full(), g)
}

fn check() {
    let mut positions = 0usize;
    for l in 1..=CHECK_L {
        for eps in (0..1u64 << l).step_by(2) {
            let t = Table::new(&multiset(l, eps));
            for s in 0..=t.full() {
                let xs = t.numbers(s);
                let par = (xs.iter().sum::<u64>() & 1) as usize;
                let mut solver = Solver::new(&xs);
                let all = (1usize << xs.len()) - 1;
                for k in 0..t.half {
                    let d = 2 * k + par;
                    assert_eq!(t.at(s, d), code(solver.position(all, d as u64)), "L={l} {xs:?} d={d}");
                    positions += 1;
                }
            }
        }
    }
    println!("check: table = Solver on {positions} positions (every member, L ≤ {CHECK_L})");
    let members: usize = (2..=EXHAUSTIVE_L)
        .into_par_iter()
        .map(|l| {
            let bad: Vec<u64> = (0..1u64 << l).step_by(2).filter(|&e| member_value(l, e) != DRAW).collect();
            assert!(bad.is_empty(), "L={l}: non-draws {bad:?}");
            1usize << (l - 1)
        })
        .sum();
    println!("check: all {members} members draw for L ≤ {EXHAUSTIVE_L} (C84 Evidence)");
    for l in 1..=E1_VALUES.len().min(20) {
        if l * (l + 1) / 2 % 2 == 0 {
            let t = Table::new(&multiset(l, 0));
            assert_eq!(letter(t.at(t.full(), 0)), E1_VALUES.as_bytes()[l - 1] as char, "{{1..{l}}}");
        }
    }
    println!("check: ε = 0 at gap 0 = E1 for even totals, L ≤ 20");
}

struct SplitMix(u64);

impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn sample(l: usize, samples: usize, rng: &mut SplitMix) -> Vec<u64> {
    let mask = ((1u64 << l) - 1) & !1;
    let twins: u64 = (1..=l).filter(|j| j % 2 == 0).map(|j| 1u64 << (j - 1)).sum();
    let mut out = vec![0, twins];
    for n in 0..samples {
        let eps = if n % 2 == 0 {
            rng.next() & mask
        } else {
            (1..l).filter(|_| rng.next() % SPARSE_DEN == 0).map(|b| 1u64 << b).sum()
        };
        out.push(eps);
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn show(l: usize, eps: u64) -> String {
    let xs = multiset(l, eps);
    format!("{{{}}}", xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("l_min l_max samples seed threads")).collect();
    assert_eq!(a.len(), 5, "usage: e23_rank_perturbed <l_min> <l_max> <samples> <seed> <threads>");
    let (l_min, l_max, samples, threads) = (a[0] as usize, a[1] as usize, a[2] as usize, a[4] as usize);
    let mut rng = SplitMix(a[3]);
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    check();
    let mut total_bad = 0;
    for l in l_min..=l_max {
        let start = Instant::now();
        let members = sample(l, samples, &mut rng);
        let bad: Vec<(u64, i8)> =
            members.par_iter().map(|&e| (e, member_value(l, e))).filter(|&(_, v)| v != DRAW).collect();
        for &(e, v) in &bad {
            println!("L={l}: {} at g={} is {}", show(l, e), multiset(l, e).iter().sum::<u64>() % 2, letter(v));
        }
        total_bad += bad.len();
        println!("L={l}: {} members, {} non-draws ({:.1} s)", members.len(), bad.len(), start.elapsed().as_secs_f64());
    }
    println!("total non-draws: {total_bad}");
}
