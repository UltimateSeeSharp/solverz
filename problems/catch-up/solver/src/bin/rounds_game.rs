//! Usage: rounds_game [universe]   (default 18)
//! The rounds game (I7, B20), Catch-Up on {a + o : o ∈ O} for large a. O ⊆ {0..U−1}, |O| even; the mover
//! trails by d. A round: the mover picks i, the other picks j; the mover's signed debt becomes d + j − i;
//! if ≥ 0 the mover keeps moving, else the other moves at the negated debt. O empty: draw at d = 0, else loss.
//! Debts d ≥ U are losses by U0 (d > c(O), the bottom-up matching cost, which is ≤ U − 1); the table keeps
//! d < U and is checked against an uncut recursion for U ≤ CHECK_UNIVERSE.
//! Reports: T1, the row of I_p = {0..2p−1} against t_p; T2, pair sets (unions of {x, x+1}) at d = 0, 1,
//! and whether any pair set wins at d ≥ 1; Law 1, R(O, 0) ≥ draw for every even O.

use rayon::prelude::*;
use std::collections::HashMap;
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 18;
const CHECK_UNIVERSE: usize = 10;
const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

fn letter(v: u8) -> char {
    ['L', 'D', 'W'][v as usize]
}

fn t(p: usize, d: usize) -> u8 {
    if d <= p && d % 2 == p % 2 {
        DRAW
    } else if d == 0 {
        WIN
    } else {
        LOSS
    }
}

fn elements(mask: u32) -> Vec<usize> {
    (0..32).filter(|&k| mask >> k & 1 == 1).collect()
}

/// Table of R(O, d) for d < u, indexed mask * u + d; odd masks unused.
struct Table {
    u: usize,
    vals: Vec<u8>,
}

impl Table {
    fn get(&self, mask: u32, d: usize) -> u8 {
        if d >= self.u { LOSS } else { self.vals[mask as usize * self.u + d] }
    }

    fn row(&self, mask: u32) -> Vec<u8> {
        let u = self.u;
        (0..u)
            .map(|d| {
                let xs = elements(mask);
                if xs.is_empty() {
                    return if d == 0 { DRAW } else { LOSS };
                }
                let mut best = LOSS;
                for &i in &xs {
                    let mut worst = WIN;
                    for &j in &xs {
                        if j == i {
                            continue;
                        }
                        let rest = mask & !(1 << i) & !(1 << j);
                        let e = d as i64 + j as i64 - i as i64;
                        let v = if e >= 0 { self.get(rest, e as usize) } else { neg(self.get(rest, (-e) as usize)) };
                        worst = worst.min(v);
                    }
                    best = best.max(worst);
                }
                best
            })
            .collect()
    }

    fn build(u: usize) -> Table {
        let mut tab = Table { u, vals: vec![LOSS; (1usize << u) * u] };
        for n in (0..=u).step_by(2) {
            let masks: Vec<u32> = (0..1u32 << u).filter(|m| m.count_ones() as usize == n).collect();
            let rows: Vec<(u32, Vec<u8>)> = masks.par_iter().map(|&m| (m, tab.row(m))).collect();
            for (m, r) in rows {
                tab.vals[m as usize * u..(m as usize + 1) * u].copy_from_slice(&r);
            }
        }
        tab
    }
}

/// Uncut recursion, debts unbounded.
fn exact(mask: u32, d: usize, memo: &mut HashMap<(u32, usize), u8>) -> u8 {
    if mask == 0 {
        return if d == 0 { DRAW } else { LOSS };
    }
    if let Some(&v) = memo.get(&(mask, d)) {
        return v;
    }
    let xs = elements(mask);
    let mut best = LOSS;
    for &i in &xs {
        let mut worst = WIN;
        for &j in &xs {
            if j == i {
                continue;
            }
            let rest = mask & !(1 << i) & !(1 << j);
            let e = d as i64 + j as i64 - i as i64;
            let v = if e >= 0 { exact(rest, e as usize, memo) } else { neg(exact(rest, (-e) as usize, memo)) };
            worst = worst.min(v);
        }
        best = best.max(worst);
    }
    memo.insert((mask, d), best);
    best
}

fn is_pair_set(mask: u32) -> bool {
    let mut m = mask;
    while m != 0 {
        let x = m.trailing_zeros();
        if m >> (x + 1) & 1 == 0 {
            return false;
        }
        m &= !(3 << x);
    }
    true
}

fn main() {
    let u: usize = std::env::args().nth(1).map(|a| a.parse().expect("universe")).unwrap_or(DEFAULT_UNIVERSE);
    assert!(u >= 2 && u <= 24, "universe in 2..=24");
    let start = Instant::now();
    println!("# rounds_game {u}\n");

    let cu = u.min(CHECK_UNIVERSE);
    let small = Table::build(cu);
    let mut memo = HashMap::new();
    let mut mism = 0;
    for m in (0..1u32 << cu).filter(|m| m.count_ones() % 2 == 0) {
        for d in 0..3 * cu {
            if small.get(m, d) != exact(m, d, &mut memo) {
                mism += 1;
            }
        }
    }
    println!("Cut table = uncut recursion on even O ⊆ {{0..{}}}, d < {}: {} mismatches\n", cu - 1, 3 * cu, mism);

    let tab = Table::build(u);
    println!("Built table for U = {u} in {:.1} s\n", start.elapsed().as_secs_f64());

    println!("## T1: rows of I_p (d < {u}; d ≥ {u} are losses, as t_p)\n");
    for p in 1..=u / 2 {
        let m = (1u32 << (2 * p)) - 1;
        let row: String = (0..u).map(|d| letter(tab.get(m, d))).collect();
        let ok = (0..u).all(|d| tab.get(m, d) == t(p, d));
        println!("- p = {p}: {row} {}", if ok { "= t_p" } else { "DIFFERS from t_p" });
    }

    let (mut sets, mut t2bad, mut winbad) = (0u64, Vec::new(), Vec::new());
    let (mut evens, mut law1bad) = (0u64, Vec::new());
    for m in (1..1u32 << u).filter(|m| m.count_ones() % 2 == 0 && m & 1 == 1) {
        evens += 1;
        if tab.get(m, 0) < DRAW {
            law1bad.push(m);
        }
        if is_pair_set(m) {
            sets += 1;
            let p = m.count_ones() as usize / 2;
            if tab.get(m, 0) != t(p, 0) || tab.get(m, 1) != t(p, 1) {
                t2bad.push(m);
            }
            if (1..u).any(|d| tab.get(m, d) == WIN) {
                winbad.push(m);
            }
        }
    }
    let show = |v: &Vec<u32>| v.iter().take(5).map(|&m| format!("{:?}", elements(m))).collect::<Vec<_>>().join(", ");
    println!("\n## T2 and Law 1 (sets containing 0; others are translates)\n");
    println!("- Pair sets: {sets}; differ from t_p at d = 0 or 1: {} {}", t2bad.len(), show(&t2bad));
    println!("- Pair sets winning at some d ≥ 1: {} {}", winbad.len(), show(&winbad));
    println!("- Even sets: {evens}; R(O, 0) = loss: {} {}", law1bad.len(), show(&law1bad));
    println!("\nRuntime {:.1} s", start.elapsed().as_secs_f64());
}
