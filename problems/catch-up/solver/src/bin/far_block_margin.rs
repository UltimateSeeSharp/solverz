//! Usage: far_block_margin <u> <k>
//! Do k far 4-blocks act on margins by a fixed map (L34)? E_k: blocks {x..x+3}, each above twice the total below it
//! plus 10. Margin game m (L33); ψ(X) = X − 2·sign(X) for |X| ≥ 2, X for |X| ≤ 1. Checks, for every S ⊆ {1..u} and
//! 0 ≤ d ≤ u, that m(S ∪ E_k, d) = ψ^k(m(S, d)) (position form), after checking sign(m) against `Solver` on
//! {1..u} ∪ E_k for every S ⊆ {1..min(u, SOLVER_CHECK_U)} with E_k left intact.

use catch_up::{Outcome, Solver};

/// Low sets up to this size are cross-checked against `Solver` (L33) with the blocks intact.
const SOLVER_CHECK_U: usize = 8;
/// Margin a block must clear above twice the total below it.
const FAR_MARGIN: usize = 10;
const BLOCK: usize = 4;
const SHOWN: usize = 5;

fn psi(x: i64) -> i64 {
    if x.abs() >= 2 { x - 2 * x.signum() } else { x }
}

fn sign(m: i64) -> Outcome {
    match m {
        m if m > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("u k")).collect();
    let (u, k) = (args[0], args[1]);
    let mut numbers: Vec<usize> = (1..=u).collect();
    let mut below: usize = numbers.iter().sum();
    for _ in 0..k {
        let x = 2 * below + FAR_MARGIN;
        numbers.extend(x..x + BLOCK);
        below += BLOCK * x + 6;
    }
    let n = numbers.len();
    let width = *numbers.last().unwrap() + 1;
    let masks = 1usize << n;
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
                let x = numbers[i];
                let next = s & !(1 << i);
                let o = if x >= d { -m[next * width + (x - d)] } else { m[next * width + (d - x)] };
                best = best.max(o);
            }
            m[at] = best;
        }
    }
    let blocks = (masks - 1) & !((1usize << u) - 1);

    let mut solver = Solver::new(&numbers.iter().map(|&x| x as u64).collect::<Vec<_>>());
    let cu = u.min(SOLVER_CHECK_U);
    let mut mismatches = 0u64;
    for s in 0..(1usize << cu) {
        for d in 0..=cu {
            if solver.position(s | blocks, d as u64) != sign(m[(s | blocks) * width + d]) {
                mismatches += 1;
            }
        }
    }
    println!("L33 check with {k} far blocks on every S ⊆ {{1..{cu}}}, d ≤ {cu}: sign(m) ≠ Solver at {mismatches} positions");

    let (mut checked, mut wrong) = (0u64, 0u64);
    let mut shown = vec![];
    for s in 0..(1usize << u) {
        for d in 0..=u {
            checked += 1;
            let low = m[s * width + d];
            let predicted = (0..k).fold(low, |x, _| psi(x));
            let actual = m[(s | blocks) * width + d];
            if actual != predicted {
                wrong += 1;
                if shown.len() < SHOWN {
                    let xs: Vec<usize> = (0..u).filter(|&i| s >> i & 1 == 1).map(|i| i + 1).collect();
                    shown.push(format!("{xs:?} d={d}: m(S)={low}, m(S ∪ E)={actual}, ψ^k={predicted}"));
                }
            }
        }
    }
    let starts: Vec<usize> = (0..k).map(|j| numbers[u + BLOCK * j]).collect();
    println!("blocks at {starts:?}: m(S ∪ E_k, d) = ψ^k(m(S, d)) fails at {wrong} of {checked} (S, d) {shown:?}");
}
