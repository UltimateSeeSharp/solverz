//! Usage: e34_tied_odd_holes <k_max>
//! C105 (B1): B = {a..a+2k}, hole h = a + o with o ≡ k (mod 2): V(B − h, 0) = draw, for k = 2..=k_max at every height
//! a = 1..=2(2k+1) and at a = (2k+1)² (rounds regime). Margin form: max |m(B − h, 0)| over every hole, both parities.
//! Every position is evaluated by `Margin` and `Solver`; their signs must agree.
//! First checks: {1..N} = {1..N+1} − {N+1} draws for N = 4, 8, 12 (C1, a = 1, h = top); the wrong-parity hole
//! {1, 3, 4, 5} is a mover win (margin 1).

use catch_up::margin::Margin;
use catch_up::{Outcome, Solver};

const SHOWN: usize = 8;

fn sign(m: i64) -> Outcome {
    match m {
        m if m > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    }
}

/// Margin and outcome of the tied mover on B − B[o], both engines, signs asserted equal.
fn tied(m: &mut Margin, s: &mut Solver, n: usize, o: usize) -> (i64, Outcome) {
    let mask = ((1usize << n) - 1) & !(1 << o);
    let (v, w) = (m.margin(mask, 0), s.position(mask, 0));
    assert_eq!(sign(v), w, "engines disagree, hole offset {o}");
    (v, w)
}

fn check() {
    for top in [5u64, 9, 13] {
        let b: Vec<u64> = (1..=top).collect();
        let n = b.len();
        let (v, _) = tied(&mut Margin::new(&b), &mut Solver::new(&b), n, n - 1);
        assert_eq!(v, 0, "{{1..{}}} is a draw", top - 1);
    }
    let b = [1u64, 2, 3, 4, 5];
    let (v, w) = tied(&mut Margin::new(&b), &mut Solver::new(&b), 5, 1);
    assert_eq!((v, w), (1, Outcome::Win), "{{1, 3, 4, 5}} at a tie");
    println!("check: {{1..4}}, {{1..8}}, {{1..12}} draw; {{1, 3, 4, 5}} is W with margin 1");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("k_max")).collect();
    assert_eq!(a.len(), 1, "usage: e34_tied_odd_holes <k_max>");
    check();
    for k in 2..=a[0] {
        let n = 2 * k as usize + 1;
        let heights: Vec<u64> = (1..=2 * n as u64).chain([(n * n) as u64]).collect();
        let (mut entries, mut bad, mut max_abs) = (0, 0, 0);
        for &h in &heights {
            let b: Vec<u64> = (h..h + n as u64).collect();
            let (mut m, mut s) = (Margin::new(&b), Solver::new(&b));
            for o in 0..n {
                let (v, w) = tied(&mut m, &mut s, n, o);
                max_abs = max_abs.max(v.abs());
                if (o as u64 + k) % 2 == 0 {
                    entries += 1;
                    if w != Outcome::Draw {
                        bad += 1;
                        if bad <= SHOWN {
                            println!("  k={k} a={h} hole {}: {w:?} (margin {v})", h + o as u64);
                        }
                    }
                }
            }
        }
        println!("k={k}: heights 1..={} and {}: {entries} draw-parity entries, {bad} non-draws; max |m| over all holes {max_abs}",
            2 * n, n * n);
    }
}
