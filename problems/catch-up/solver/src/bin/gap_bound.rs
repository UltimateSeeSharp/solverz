//! Usage: gap_bound <u> <dmax>
//! Does the player to move never lose by more than the largest gap (C37)? Margin game m(S, d) (C33): Catch-Up turns,
//! payoff the mover's final score minus the opponent's, no early-loss rule. γ(W) = the largest gap of sorted W ∪ {0}.
//! Checks, over every S ⊆ {1..u} and 0 ≤ d ≤ dmax: first that sign(m) equals `Solver::position` (C33) on all
//! S ⊆ {1..min(u, SOLVER_CHECK_U)}, d ≤ that bound; then LG, m(S, d) ≥ −γ(S ⊎ {d}), with the positions where it is
//! tight; G at ties, |m(S, 0)| ≤ γ(S); and prints m({1..N}, 0) for N ≤ u.

use catch_up::{Outcome, Solver};

/// Sets up to this size are cross-checked against `Solver` (C33).
const SOLVER_CHECK_U: usize = 12;
/// Examples printed per kind.
const SHOWN: usize = 5;

fn sign(m: i32) -> Outcome {
    match m {
        m if m > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

fn members(mask: usize, u: usize) -> Vec<usize> {
    (0..u).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).collect()
}

/// Largest gap between consecutive elements of sorted `xs` ∪ {0}.
fn gamma(mut xs: Vec<usize>) -> i32 {
    xs.push(0);
    xs.sort_unstable();
    xs.windows(2).map(|w| (w[1] - w[0]) as i32).max().unwrap_or(0)
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("u dmax")).collect();
    let (u, dmax) = (args[0], args[1]);
    let width = dmax.max(u) + 1; // deficits after a pick stay below the largest number
    let masks = 1usize << u;
    let mut m = vec![0i32; masks * width];
    for s in 0..masks {
        for d in 0..width {
            let at = s * width + d;
            if s == 0 {
                m[at] = -(d as i32);
                continue;
            }
            let mut best = i32::MIN;
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

    let (mut positions, mut violations, mut tight, mut g_violations) = (0u64, 0u64, 0u64, 0u64);
    let (mut shown_violations, mut shown_tight) = (vec![], vec![]);
    for s in 0..masks {
        let xs = members(s, u);
        for d in 0..=dmax {
            positions += 1;
            let mut with_d = xs.clone();
            with_d.push(d);
            let bound = gamma(with_d);
            let value = m[s * width + d];
            if value < -bound {
                violations += 1;
                if shown_violations.len() < SHOWN {
                    shown_violations.push(format!("{xs:?} d={d}: m={value}, γ={bound}"));
                }
            }
            if value == -bound && s != 0 {
                tight += 1;
                if d == 0 && shown_tight.len() < SHOWN {
                    shown_tight.push(format!("{xs:?}"));
                }
            }
            if d == 0 && value.abs() > gamma(xs.clone()) {
                g_violations += 1;
            }
        }
    }
    println!("LG on every S ⊆ {{1..{u}}}, d ≤ {dmax}: {positions} positions, {violations} violations {shown_violations:?}");
    println!("LG tight (m = −γ) at {tight} nonempty positions; at ties e.g. {shown_tight:?}");
    println!("G at ties, |m(S, 0)| ≤ γ(S): {g_violations} violations");
    let intervals: Vec<String> = (1..=u).map(|n| format!("{n}:{:+}", m[((1usize << n) - 1) * width])).collect();
    println!("m({{1..N}}, 0): {}", intervals.join(" "));
}
