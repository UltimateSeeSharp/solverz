//! Usage: e38_one_hole_band <k_min> <k_max>
//! C110: B = {a..a+2k}, any h ∈ B, 0 ≤ d ≤ k − 1: V(B ∖ {h}, d) = draw when d + sum(B) − h is even (k ≥ 3), at every
//! height a = 1..=2(2k+1) and a = (2k+1)² (rounds regime). Margin form: |m(B ∖ {h}, d)| ≤ 1 for every such (h, d).
//! Also reports, per k, the least d ≤ 2k with a draw-parity non-draw or |m| > 1 at some height and hole (the band's end).
//! `Margin` and `Solver` evaluate every entry; their signs must agree.
//! First checks: C1's two families are entries: {1..8} = {1..9} ∖ {9} at d = 0 and {2..11} = {1..11} ∖ {1} at d = 1
//! draw; C47's {2, 3, 4, 5} = {1..5} ∖ {1} at d = 2 (k = 2, outside the band) is a mover win.

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

fn entry(m: &mut Margin, s: &mut Solver, n: usize, o: usize, d: u64) -> (i64, Outcome) {
    let mask = ((1usize << n) - 1) & !(1 << o);
    let (v, w) = (m.margin(mask, d), s.position(mask, d));
    assert_eq!(sign(v), w, "engines disagree, hole offset {o}, d {d}");
    (v, w)
}

fn block(a: u64, n: usize) -> (Margin, Solver) {
    let b: Vec<u64> = (a..a + n as u64).collect();
    (Margin::new(&b), Solver::new(&b))
}

fn check() {
    let (mut m, mut s) = block(1, 9);
    assert_eq!(entry(&mut m, &mut s, 9, 8, 0).1, Outcome::Draw, "{{1..8}} at 0");
    let (mut m, mut s) = block(1, 11);
    assert_eq!(entry(&mut m, &mut s, 11, 0, 1).1, Outcome::Draw, "{{2..11}} at 1");
    let (mut m, mut s) = block(1, 5);
    assert_eq!(entry(&mut m, &mut s, 5, 0, 2).1, Outcome::Win, "C47's {{2, 3, 4, 5}} at 2");
    println!("check: {{1..8}} at 0 and {{2..11}} at 1 draw; {{2, 3, 4, 5}} at 2 is W");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("k_min k_max")).collect();
    assert_eq!(a.len(), 2, "usage: e38_one_hole_band <k_min> <k_max>");
    assert!(a[0] >= 3, "the band needs k ≥ 3");
    check();
    for k in a[0]..=a[1] {
        let n = 2 * k as usize + 1;
        let heights: Vec<u64> = (1..=2 * n as u64).chain([(n * n) as u64]).collect();
        let (mut entries, mut bad, mut wide) = (0, 0, 0);
        let mut end = 2 * k + 1;
        for &h in &heights {
            let (mut m, mut s) = block(h, n);
            let sum: u64 = (h..h + n as u64).sum();
            for d in 0..=2 * k {
                for o in 0..n {
                    let (v, w) = entry(&mut m, &mut s, n, o, d);
                    let draw_parity = (d + sum - (h + o as u64)) % 2 == 0;
                    let fails = v.abs() > 1 || (draw_parity && w != Outcome::Draw);
                    if fails {
                        end = end.min(d);
                    }
                    if d < k {
                        if draw_parity {
                            entries += 1;
                            if w != Outcome::Draw {
                                bad += 1;
                                if bad <= SHOWN {
                                    println!("  k={k} a={h} hole {} d={d}: {w:?} (margin {v})", h + o as u64);
                                }
                            }
                        }
                        if v.abs() > 1 {
                            wide += 1;
                        }
                    }
                }
            }
        }
        println!("k={k}: heights 1..={} and {}: {entries} draw-parity entries with d ≤ k − 1, {bad} non-draws, \
            {wide} entries with |m| > 1; the band ends at d = {end}", 2 * n, n * n);
    }
}
