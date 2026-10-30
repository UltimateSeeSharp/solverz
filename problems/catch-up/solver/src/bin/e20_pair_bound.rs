//! Usage: e20_pair_bound <u> <dmax> <v> <c> <mdmax>
//! Pairing bound (C60): m(S, d) ≥ −P(S ⊎ {d}), m the margin game (C33). P(V): sort V decreasingly, append 0, pair
//! from the top; the worst pair difference (the largest gap with an odd number of elements of V above it).
//! Sets: every S ⊆ {1..u}, 0 ≤ d ≤ dmax, after reproducing `Solver` as sign(m) on S ⊆ {1..min(u, SOLVER_CHECK_U)}.
//! Multisets: every multiset over {1..v} with multiplicity ≤ c, 0 ≤ d ≤ mdmax, by a memoized search first matched
//! against the set table on every S ⊆ {1..v}. Also G's analogue at ties, |m(S, 0)| ≤ P(S), and how often P < γ (C37).

use catch_up::{Outcome, Solver};
use std::collections::HashMap;

/// Sets up to this size are cross-checked against `Solver` (C33).
const SOLVER_CHECK_U: usize = 12;
/// Examples printed per kind.
const SHOWN: usize = 5;

fn sign(m: i64) -> Outcome {
    match m {
        m if m > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

fn members(mask: usize, u: usize) -> Vec<u64> {
    (0..u).filter(|&i| mask >> i & 1 == 1).map(|i| i as u64 + 1).collect()
}

/// Worst difference of the top-down pairing of `v` (0 appended when |v| is odd).
fn pair_bound(mut v: Vec<u64>) -> i64 {
    v.sort_unstable();
    if v.len() % 2 == 1 {
        v.insert(0, 0);
    }
    v.chunks(2).map(|p| (p[1] - p[0]) as i64).max().unwrap_or(0)
}

/// Largest gap of sorted `v` ∪ {0} (C37).
fn gamma(mut v: Vec<u64>) -> i64 {
    v.push(0);
    v.sort_unstable();
    v.windows(2).map(|w| (w[1] - w[0]) as i64).max().unwrap_or(0)
}

/// m(s, d) on a sorted multiset.
fn margin(s: &[u64], d: u64, memo: &mut HashMap<(Vec<u64>, u64), i64>) -> i64 {
    if s.is_empty() {
        return -(d as i64);
    }
    if let Some(&v) = memo.get(&(s.to_vec(), d)) {
        return v;
    }
    let mut best = i64::MIN;
    for i in 0..s.len() {
        if i > 0 && s[i] == s[i - 1] {
            continue;
        }
        let x = s[i];
        let mut rest = s.to_vec();
        rest.remove(i);
        let o = if x >= d { -margin(&rest, x - d, memo) } else { margin(&rest, d - x, memo) };
        best = best.max(o);
    }
    memo.insert((s.to_vec(), d), best);
    best
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("u dmax v c mdmax")).collect();
    let (u, dmax, v, c, mdmax) = (args[0], args[1], args[2], args[3], args[4]);
    let width = dmax.max(u) + 1; // deficits after a pick stay below the largest number
    let masks = 1usize << u;
    let mut m = vec![0i64; masks * width];
    for s in 0..masks {
        for d in 0..width {
            let at = s * width + d;
            if s == 0 {
                m[at] = -(d as i64);
                continue;
            }
            let mut best = i64::MIN;
            let mut rest = s;
            while rest != 0 {
                let i = rest.trailing_zeros() as usize;
                rest &= rest - 1;
                let x = i + 1;
                let next = s & !(1 << i);
                let o = if x >= d { -m[next * width + (x - d)] } else { m[next * width + (d - x)] };
                best = best.max(o);
            }
            m[at] = best;
        }
    }

    let cu = u.min(SOLVER_CHECK_U);
    let mut solver = Solver::new(&(1..=cu as u64).collect::<Vec<_>>());
    let mut mismatches = 0u64;
    for s in 0..(1usize << cu) {
        for d in 0..=cu.min(dmax) {
            if solver.position(s, d as u64) != sign(m[s * width + d]) {
                mismatches += 1;
            }
        }
    }
    println!("C33 check on every S ⊆ {{1..{cu}}}, d ≤ {}: sign(m) ≠ Solver at {mismatches} positions", cu.min(dmax));

    let (mut positions, mut violations, mut tight, mut sharper, mut g_violations) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut shown_violations = vec![];
    for s in 0..masks {
        let xs = members(s, u);
        for d in 0..=dmax {
            positions += 1;
            let mut with_d = xs.clone();
            with_d.push(d as u64);
            let bound = pair_bound(with_d.clone());
            let value = m[s * width + d];
            if value < -bound {
                violations += 1;
                if shown_violations.len() < SHOWN {
                    shown_violations.push(format!("{xs:?} d={d}: m={value}, P={bound}"));
                }
            }
            if value == -bound && bound > 0 {
                tight += 1;
            }
            if bound < gamma(with_d) {
                sharper += 1;
            }
            if d == 0 && value.abs() > pair_bound(xs.clone()) {
                g_violations += 1;
            }
        }
    }
    println!("PG on every S ⊆ {{1..{u}}}, d ≤ {dmax}: {positions} positions, {violations} violations {shown_violations:?}");
    println!("PG tight (m = −P, P ≥ 1) at {tight} positions; P < γ at {sharper}");
    println!("ties, |m(S, 0)| ≤ P(S): {g_violations} violations");

    let mut memo = HashMap::new();
    let mut memo_mismatches = 0u64;
    for s in 0..(1usize << v) {
        let xs = members(s, v);
        for d in 0..=v.min(dmax) {
            if margin(&xs, d as u64, &mut memo) != m[s * width + d] {
                memo_mismatches += 1;
            }
        }
    }
    println!("multiset search vs set table on every S ⊆ {{1..{v}}}, d ≤ {}: {memo_mismatches} mismatches", v.min(dmax));

    let (mut positions, mut violations, mut tight) = (0u64, 0u64, 0u64);
    let mut shown_violations = vec![];
    let mut counts = vec![0usize; v];
    loop {
        let xs: Vec<u64> = (0..v).flat_map(|i| std::iter::repeat_n(i as u64 + 1, counts[i])).collect();
        for d in 0..=mdmax {
            positions += 1;
            let value = margin(&xs, d as u64, &mut memo);
            let mut with_d = xs.clone();
            with_d.push(d as u64);
            let bound = pair_bound(with_d);
            if value < -bound {
                violations += 1;
                if shown_violations.len() < SHOWN {
                    shown_violations.push(format!("{xs:?} d={d}: m={value}, P={bound}"));
                }
            }
            if value == -bound && bound > 0 {
                tight += 1;
            }
        }
        let mut i = 0;
        while i < v && counts[i] == c {
            counts[i] = 0;
            i += 1;
        }
        if i == v {
            break;
        }
        counts[i] += 1;
    }
    println!(
        "PG on every multiset over {{1..{v}}}, multiplicity ≤ {c}, d ≤ {mdmax}: {positions} positions, \
         {violations} violations {shown_violations:?}; tight at {tight}"
    );
}
