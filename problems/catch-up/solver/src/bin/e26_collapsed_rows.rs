//! Usage: e26_collapsed_rows <p_min> <p_max> <threads>
//! C85's row form (as C24 has for blocks): for F_t = ⊎_{i<p} {c + 2i, c + 2i + t_i}, is the mover trailing by d, with
//! d ≡ |t| (mod 2) and d below the largest number, a draw exactly when d ≤ |t| and a loss when d > |t|? For each p
//! and every c = 1..=C_PER_P·p, E22's margin table (same encoding) answers every t and d; prints the counts and the
//! first exceptions of each kind. First checks the table's signs against `Solver` (p ≤ CHECK_P, c ≤ CHECK_C).

use catch_up::{Outcome, Solver};
use rayon::prelude::*;

const NONE: usize = 0;
const ONE_A: usize = 1;
const TWO_A: usize = 2;
const ONLY_BUMP: usize = 3;
const A_AND_BUMP: usize = 4;
const DIGITS: usize = 5;
const TAKE_A: usize = 1;
const TAKE_BUMP: usize = 3;
const C_PER_P: usize = 2;
const CHECK_P: usize = 4;
const CHECK_C: usize = 5;
const SHOWN: usize = 6;

/// E22's table: margins m(sub-multiset, d), d < width.
struct Table {
    p: usize,
    c: usize,
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
                m[s * width + d] = if opts.is_empty() {
                    -(d as i16)
                } else {
                    opts.iter()
                        .map(|&(x, nx)| if x >= d { -m[nx * width + (x - d)] } else { m[nx * width + (d - x)] })
                        .max()
                        .unwrap()
                };
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

fn check() {
    let mut n = 0;
    for p in 1..=CHECK_P {
        for c in 1..=CHECK_C {
            let t = Table::new(p, c);
            for s in 0..t.pw[p] {
                let xs = t.numbers(s);
                let mut solver = Solver::new(&xs);
                for d in 0..t.width {
                    assert_eq!(sign(t.at(s, d)), solver.position((1usize << xs.len()) - 1, d as u64), "{xs:?} d={d}");
                    n += 1;
                }
            }
        }
    }
    println!("check: signs = Solver on {n} positions (p ≤ {CHECK_P}, c ≤ {CHECK_C})");
}

/// Per (p, c): (positions, non-draws at d ≤ |t|, non-losses at d > |t|, examples, off-diagonal non-draws d < |t|).
fn rows(p: usize, c: usize) -> (usize, usize, usize, Vec<String>, usize) {
    let t = Table::new(p, c);
    let largest = c + 2 * p - 1;
    let (mut n, mut low_bad, mut high_bad, mut ex, mut off_diag) = (0, 0, 0, vec![], 0);
    for tv in 0..1usize << p {
        let k = tv.count_ones() as usize;
        let s = t.state_of(tv);
        for d in (k % 2..=largest).step_by(2) {
            n += 1;
            let v = t.at(s, d);
            let bad = if d <= k { v != 0 } else { v >= 0 };
            if bad {
                if d < k { off_diag += 1 }
                if d <= k { low_bad += 1 } else { high_bad += 1 }
                if ex.len() < SHOWN {
                    ex.push(format!("c={c} t={tv:0w$b} d={d}: m={v}", w = p));
                }
            }
        }
    }
    (n, low_bad, high_bad, ex, off_diag)
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().expect("p_min p_max threads")).collect();
    assert_eq!(a.len(), 3, "usage: e26_collapsed_rows <p_min> <p_max> <threads>");
    rayon::ThreadPoolBuilder::new().num_threads(a[2]).build_global().unwrap();
    check();
    for p in a[0]..=a[1] {
        let mut out: Vec<(usize, (usize, usize, usize, Vec<String>, usize))> =
            (1..=C_PER_P * p).into_par_iter().map(|c| (c, rows(p, c))).collect();
        out.sort_by_key(|x| x.0);
        let (n, lo, hi, off): (usize, usize, usize, usize) =
            out.iter().fold((0, 0, 0, 0), |s, x| (s.0 + x.1.0, s.1 + x.1.1, s.2 + x.1.2, s.3 + x.1.4));
        println!("p={p}: {n} row positions, {lo} non-draws at d ≤ |t| ({off} of them off the diagonal d < |t|), {hi} non-losses at d > |t|");
        for (c, (_, l, h, ex, _)) in &out {
            if l + h > 0 {
                println!("  c={c}: {l} + {h}; {ex:?}");
            }
        }
    }
}
