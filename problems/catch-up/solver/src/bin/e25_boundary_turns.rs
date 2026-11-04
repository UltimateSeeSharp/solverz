//! Usage: e25_boundary_turns <n_min> <n_max>
//! C83: for even-total N ≥ 11, 3 ≤ b ≤ N, R_b = {2..N} ∖ {b − 1, b}, y ∈ R_b ∩ {2, b − 2, b + 1, N}, the defender
//! trails by y on S = R_b ∖ {y}. Lists its safe first turns (a set A with sum(A) ≥ y > sum(A) − max(A), after which
//! the opponent is not winning) and asks which C77-style turns are among them: an exact-sum turn (sum(A) = y), and
//! the change turn (the longest bottom run s₁..s_k of S plus r = y − (s₁ + … + s_k) ∈ S, r > s_k; the run alone if
//! it sums to y).
//! Prints a summary per (N, kind of y) and every case where no exact-sum turn or the change turn is unsafe.
//! One `Solver` on {2..N} answers every position. First checks it against a fresh `Solver` per position for N ≤ CHECK_N.

use catch_up::{Outcome, Solver};

const CHECK_N: u64 = 12;
const SHOWN: usize = 12;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Two,
    BelowPair,
    AbovePair,
    Top,
}

const KINDS: [Kind; 4] = [Kind::Two, Kind::BelowPair, Kind::AbovePair, Kind::Top];

fn y_of(kind: Kind, n: u64, b: u64) -> u64 {
    match kind {
        Kind::Two => 2,
        Kind::BelowPair => b - 2,
        Kind::AbovePair => b + 1,
        Kind::Top => n,
    }
}

/// Bit i stands for the number i + 2.
fn mask_of(xs: &[u64]) -> usize {
    xs.iter().map(|&x| 1usize << (x - 2)).sum()
}

fn show(xs: &[u64]) -> String {
    format!("{{{}}}", xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

/// Every turn from S at deficit y: subsets A, sum(A) ≥ y > sum(A) − max(A); A in increasing order.
fn turns(s: &[u64], y: u64) -> Vec<Vec<u64>> {
    fn go(s: &[u64], k: usize, y: u64, cur: &mut Vec<u64>, sum: u64, out: &mut Vec<Vec<u64>>) {
        if sum >= y {
            return;
        }
        for i in k..s.len() {
            cur.push(s[i]);
            if sum + s[i] >= y {
                out.push(cur.clone());
            } else {
                go(s, i + 1, y, cur, sum + s[i], out);
            }
            cur.pop();
        }
    }
    let mut out = vec![];
    go(s, 0, y, &mut vec![], 0, &mut out);
    out
}

fn change_turn(s: &[u64], y: u64) -> Option<Vec<u64>> {
    (0..s.len()).rev().find_map(|k| {
        let run: u64 = s[..k].iter().sum();
        let r = y.checked_sub(run)?;
        if r == 0 && k > 0 {
            return Some(s[..k].to_vec());
        }
        let above = k == 0 || r > s[k - 1];
        (r > 0 && above && s[k..].contains(&r)).then(|| [&s[..k], &[r]].concat())
    })
}

struct Case {
    kind: Kind,
    b: u64,
    y: u64,
    value: Outcome,
    safe: usize,
    total: usize,
    exact_safe: usize,
    change: Option<(Vec<u64>, bool)>,
}

fn opponent_value(solver: &mut Solver, s: &[u64], a: &[u64], y: u64) -> Outcome {
    let rest = mask_of(s) & !mask_of(a);
    solver.position(rest, a.iter().sum::<u64>() - y)
}

fn cases(n: u64, solver: &mut Solver) -> Vec<Case> {
    let mut out = vec![];
    for b in 3..=n {
        let r: Vec<u64> = (2..=n).filter(|&x| x != b - 1 && x != b).collect();
        for kind in KINDS {
            let y = y_of(kind, n, b);
            if !r.contains(&y) || out.iter().any(|c: &Case| c.b == b && c.y == y) {
                continue;
            }
            let s: Vec<u64> = r.iter().copied().filter(|&x| x != y).collect();
            let value = solver.position(mask_of(&s), y);
            let all = turns(&s, y);
            let mut safe = 0;
            let mut exact_safe = 0;
            for a in &all {
                if opponent_value(solver, &s, a, y) != Outcome::Win {
                    safe += 1;
                    if a.iter().sum::<u64>() == y {
                        exact_safe += 1;
                    }
                }
            }
            let change = change_turn(&s, y).map(|a| {
                let ok = opponent_value(solver, &s, &a, y) != Outcome::Win;
                (a, ok)
            });
            out.push(Case { kind, b, y, value, safe, total: all.len(), exact_safe, change });
        }
    }
    out
}

fn check() {
    let mut n_pos = 0;
    for n in 4..=CHECK_N {
        let numbers: Vec<u64> = (2..=n).collect();
        let mut shared = Solver::new(&numbers);
        for mask in 0..1usize << numbers.len() {
            let xs: Vec<u64> = (0..numbers.len()).filter(|&i| mask >> i & 1 == 1).map(|i| numbers[i]).collect();
            let mut fresh = Solver::new(&xs);
            for gap in 0..=n {
                assert_eq!(shared.position(mask, gap), fresh.position((1usize << xs.len()) - 1, gap), "{xs:?} gap {gap}");
                n_pos += 1;
            }
        }
    }
    let s = [2, 3, 5, 9];
    // {2,3}, {2,5}, {2,9}, {3,5}, {3,9}, {5}, {9}
    assert_eq!(turns(&s, 5).len(), 7, "turns of {s:?} at 5");
    println!("check: shared Solver = fresh Solver on {n_pos} positions, N ≤ {CHECK_N}");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e25_boundary_turns <n_min> <n_max>");
    check();
    for n in a[0].max(11)..=a[1] {
        if n * (n + 1) / 2 % 2 == 1 {
            continue;
        }
        let numbers: Vec<u64> = (2..=n).collect();
        let mut solver = Solver::new(&numbers);
        let all = cases(n, &mut solver);
        for kind in KINDS {
            let cs: Vec<&Case> = all.iter().filter(|c| c.kind == kind).collect();
            let losses = cs.iter().filter(|c| c.value == Outcome::Loss).count();
            let no_exact: Vec<&&Case> = cs.iter().filter(|c| c.exact_safe == 0).collect();
            let change_bad: Vec<&&Case> = cs.iter().filter(|c| matches!(c.change, Some((_, false)) | None)).collect();
            let min_share = cs.iter().map(|c| c.safe as f64 / c.total.max(1) as f64).fold(1.0, f64::min);
            println!(
                "N={n} {kind:?}: {} cases, {losses} losses, safe share ≥ {min_share:.2}, no safe exact-sum turn in {}, change turn absent or unsafe in {}",
                cs.len(),
                no_exact.len(),
                change_bad.len()
            );
            for c in no_exact.iter().take(SHOWN) {
                println!("  no exact: b={} y={} value {:?}, {} of {} turns safe", c.b, c.y, c.value, c.safe, c.total);
            }
            for c in change_bad.iter().take(SHOWN) {
                let ch = c.change.as_ref().map_or("none".to_string(), |(t, _)| show(t));
                println!("  change {ch} unsafe or absent: b={} y={}, {} exact-sum turns safe", c.b, c.y, c.exact_safe);
            }
        }
    }
}
