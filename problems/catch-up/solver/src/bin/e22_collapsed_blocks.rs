//! Usage: e22_collapsed_blocks <p_min> <p_max> <threads>
//! C85 (PBT): F_t = ⊎_{i<p} {c + 2i, c + 2i + t_i}, t ∈ {0, 1}^p, is a draw at deficit |t| mod 2.
//! For each p and every c = 1..=C_PER_P·p, one margin table (C33) over every sub-multiset reachable from some F_t
//! answers all t; prints the t with m(F_t, |t| mod 2) ≠ 0. First checks the table's signs against `Solver` on
//! every position for p ≤ CHECK_P, c ≤ CHECK_C, and {1..2p} at gap 0 (c = 1, t = 1…1) against E1.

use catch_up::{Outcome, Solver};
use rayon::prelude::*;
use std::time::Instant;

/// Pair i's content, a = c + 2i: one base-5 digit per pair.
const NONE: usize = 0;
const ONE_A: usize = 1;
const TWO_A: usize = 2;
const ONLY_BUMP: usize = 3;
const A_AND_BUMP: usize = 4;
const DIGITS: usize = 5;
/// Taking a lowers the digit by 1 (1→0, 2→1, 4→3), taking a + 1 by 3 (3→0, 4→1).
const TAKE_A: usize = 1;
const TAKE_BUMP: usize = 3;
/// c runs over 1..=C_PER_P·p (I16 kill test (a): every c ≤ 2p).
const C_PER_P: usize = 2;
const CHECK_P: usize = 4;
const CHECK_C: usize = 5;
/// E1's value of {1..N} for player 1, N = 1..=E1_VALUES.len().
const E1_VALUES: &str = "WWDDWWDDLLDDWLDDWLDDWWDDWWDDWWD";
const SHOWN: usize = 8;

struct Table {
    p: usize,
    c: usize,
    /// Gaps 0..width; play keeps the gap ≤ the largest number c + 2p − 1.
    width: usize,
    pw: Vec<usize>,
    m: Vec<i16>,
}

impl Table {
    fn new(p: usize, c: usize) -> Self {
        let width = c + 2 * p;
        let pw: Vec<usize> = (0..=p).map(|i| DIGITS.pow(i as u32)).collect();
        let states = pw[p];
        let mut m = vec![0i16; states * width];
        let mut opts: Vec<(usize, usize)> = Vec::with_capacity(2 * p);
        for s in 0..states {
            opts.clear();
            for i in 0..p {
                let a = c + 2 * i;
                match (s / pw[i]) % DIGITS {
                    ONE_A | TWO_A => opts.push((a, s - TAKE_A * pw[i])),
                    ONLY_BUMP => opts.push((a + 1, s - TAKE_BUMP * pw[i])),
                    A_AND_BUMP => {
                        opts.push((a, s - TAKE_A * pw[i]));
                        opts.push((a + 1, s - TAKE_BUMP * pw[i]));
                    }
                    _ => {}
                }
            }
            for d in 0..width {
                let v = if opts.is_empty() {
                    -(d as i16)
                } else {
                    opts.iter()
                        .map(|&(x, nx)| if x >= d { -m[nx * width + (x - d)] } else { m[nx * width + (d - x)] })
                        .max()
                        .unwrap()
                };
                m[s * width + d] = v;
            }
        }
        Table { p, c, width, pw, m }
    }

    fn at(&self, s: usize, d: usize) -> i16 {
        self.m[s * self.width + d]
    }

    fn state_of(&self, t: usize) -> usize {
        (0..self.p).map(|i| if t >> i & 1 == 1 { A_AND_BUMP } else { TWO_A } * self.pw[i]).sum()
    }

    fn numbers(&self, s: usize) -> Vec<u64> {
        let mut xs = vec![];
        for i in 0..self.p {
            let a = (self.c + 2 * i) as u64;
            match (s / self.pw[i]) % DIGITS {
                ONE_A => xs.push(a),
                TWO_A => xs.extend([a, a]),
                ONLY_BUMP => xs.push(a + 1),
                A_AND_BUMP => xs.extend([a, a + 1]),
                NONE => {}
                _ => unreachable!(),
            }
        }
        xs
    }
}

fn sign(v: i16) -> Outcome {
    match v {
        v if v > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

fn check_against_solver() {
    let mut positions = 0usize;
    for p in 1..=CHECK_P {
        for c in 1..=CHECK_C {
            let t = Table::new(p, c);
            for s in 0..t.pw[p] {
                let xs = t.numbers(s);
                let mut solver = Solver::new(&xs);
                let full = (1usize << xs.len()) - 1;
                for d in 0..t.width {
                    assert_eq!(sign(t.at(s, d)), solver.position(full, d as u64), "p={p} c={c} {xs:?} d={d}");
                    positions += 1;
                }
            }
        }
    }
    println!("check: signs = Solver on {positions} positions (p ≤ {CHECK_P}, c ≤ {CHECK_C})");
}

fn check_e1(t: &Table) {
    if t.c != 1 {
        return;
    }
    let n = 2 * t.p;
    let all = (1usize << t.p) - 1;
    let got = letter(sign(t.at(t.state_of(all), 0)));
    let want = E1_VALUES.as_bytes()[n - 1] as char;
    assert_eq!(got, want, "value of {{1..{n}}}");
}

/// Non-draws at the parity deficit: (count, first few as "t=… m=…").
fn non_draws(t: &Table) -> (usize, Vec<String>) {
    let mut bad = vec![];
    let mut count = 0;
    for tv in 0..(1usize << t.p) {
        let v = t.at(t.state_of(tv), tv.count_ones() as usize % 2);
        if v != 0 {
            count += 1;
            if bad.len() < SHOWN {
                bad.push(format!("t={tv:0w$b} m={v}", w = t.p));
            }
        }
    }
    (count, bad)
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().expect("p_min p_max threads")).collect();
    assert_eq!(a.len(), 3, "usage: e22_collapsed_blocks <p_min> <p_max> <threads>");
    let (p_min, p_max, threads) = (a[0], a[1], a[2]);
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    check_against_solver();
    let mut total_bad = 0;
    for p in p_min..=p_max {
        let start = Instant::now();
        let mut rows: Vec<(usize, usize, Vec<String>)> = (1..=C_PER_P * p)
            .into_par_iter()
            .map(|c| {
                let t = Table::new(p, c);
                check_e1(&t);
                let (n, bad) = non_draws(&t);
                (c, n, bad)
            })
            .collect();
        rows.sort();
        for (c, n, bad) in &rows {
            total_bad += n;
            if *n > 0 {
                println!("p={p} c={c}: {n} of {} non-draws {bad:?}", 1usize << p);
            }
        }
        let bad_c = rows.iter().filter(|r| r.1 > 0).count();
        println!("p={p}: c = 1..={}, non-draw at {bad_c} heights ({:.1} s)", C_PER_P * p, start.elapsed().as_secs_f64());
    }
    println!("total non-draws: {total_bad}");
}
