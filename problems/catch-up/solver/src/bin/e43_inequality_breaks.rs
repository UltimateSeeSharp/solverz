//! Usage: e43_inequality_breaks
//! Rechecks ideator fresh07's counterexamples with two engines (`Margin` margins, `Solver` signs):
//!   C117 (deficit Lipschitz): m(S, d + 1) ≥ m(S, d) − 1 for every S and d;
//!   C118 (extra-number bound): |m(S ∪ {x}, e) − m(S, e)| ≤ x for every S, x ∉ S and e.
//! For C118's upper half it scans e ≤ 20 at S = {4, 7, 9, 10, 12, 15}, x ∈ {1, 2}.
//! First checks: m({1..N}, 0) = 0 at N = 3, 4, 7, 8, 11, 12 (C1); C117 holds on every subset of {1..10} at d ≤ 10.

use catch_up::margin::Margin;
use catch_up::{Outcome, Solver};

/// The margin of `numbers` at deficit `d`, its sign checked against `Solver`.
fn m(numbers: &[u64], d: u64) -> i64 {
    let mask = (1usize << numbers.len()) - 1;
    let v = Margin::new(numbers).margin(mask, d);
    let w = Solver::new(numbers).position(mask, d);
    let sign = match v {
        v if v > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    };
    assert_eq!(sign, w, "engines disagree at {numbers:?}, d {d}");
    v
}

fn with(s: &[u64], x: u64) -> Vec<u64> {
    let mut v = s.to_vec();
    v.push(x);
    v.sort_unstable();
    v
}

fn check() {
    for n in [3u64, 4, 7, 8, 11, 12] {
        assert_eq!(m(&(1..=n).collect::<Vec<_>>(), 0), 0, "C1 at N = {n}");
    }
    let numbers: Vec<u64> = (1..=10).collect();
    let mut e = Margin::new(&numbers);
    for mask in 1..1usize << numbers.len() {
        for d in 0..10u64 {
            assert!(e.margin(mask, d + 1) >= e.margin(mask, d) - 1, "C117 inside {{1..10}}");
        }
    }
    println!("check: m({{1..N}}, 0) = 0 at N = 3, 4, 7, 8, 11, 12; C117 holds on every subset of {{1..10}}, d ≤ 10");
}

fn main() {
    check();
    for (s, d) in [(vec![1u64, 5, 9, 11, 12, 14, 18], 1u64), (vec![1, 2, 5, 9, 11, 12, 14, 18], 0), (vec![4, 5, 6, 8, 9, 16, 18], 4)] {
        let (a, b) = (m(&s, d), m(&s, d + 1));
        println!("C117 at {s:?}: m(d = {d}) = {a}, m(d = {}) = {b}: {}", d + 1, if b < a - 1 { "BREAKS" } else { "holds" });
    }
    let s = [2u64, 5, 9, 11, 12, 14, 18];
    let (a, b) = (m(&s, 1), m(&with(&s, 1), 1));
    println!("C118 lower half at {s:?} + 1, e = 1: {a} → {b}: {}", if b < a - 1 { "BREAKS" } else { "holds" });
    let s = [4u64, 7, 9, 10, 12, 15];
    for x in [1u64, 2] {
        let breaks: Vec<String> = (0..=20u64)
            .filter_map(|e| {
                let (a, b) = (m(&s, e), m(&with(&s, x), e));
                (b - a > x as i64).then(|| format!("e = {e}: {a} → {b}"))
            })
            .collect();
        println!("C118 upper half at {s:?} + {x}: {}", if breaks.is_empty() { "holds".to_string() } else { format!("BREAKS at {}", breaks.join(", ")) });
    }
}
