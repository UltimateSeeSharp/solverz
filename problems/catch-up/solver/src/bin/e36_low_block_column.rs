//! Usage: e36_low_block_column <n_min> <n_max>
//! C104 (EB): B = {a..a+n−1}, n = n_min..=n_max (n ≥ 6), every a = 1..=n/2, every d ≤ n − 1 with d + sum(B) even:
//! V(B, d) = draw. Also the margin form |m(B, d)| ≤ 1 for every d ≤ n − 1 (both parities), and per (n, a) the
//! first d with |m| > 1 or a draw-parity non-draw (the column's end). `Margin` and `Solver` evaluate every entry.
//! First checks: the excluded small exceptions, {2, 3, 4, 5} at 2 and {1..5} at 3, are mover wins (margin 2 at the
//! second); {1..8} at 0 and {2..11} at 1 draw (C1 at N = 8, 11 via C27).

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

fn entry(m: &mut Margin, s: &mut Solver, n: usize, d: u64) -> (i64, Outcome) {
    let mask = (1usize << n) - 1;
    let (v, w) = (m.margin(mask, d), s.position(mask, d));
    assert_eq!(sign(v), w, "engines disagree at d {d}");
    (v, w)
}

fn block(a: u64, n: usize) -> (Margin, Solver) {
    let b: Vec<u64> = (a..a + n as u64).collect();
    (Margin::new(&b), Solver::new(&b))
}

fn check() {
    let (mut m, mut s) = block(2, 4);
    assert_eq!(entry(&mut m, &mut s, 4, 2).1, Outcome::Win, "C47's {{2, 3, 4, 5}} at 2");
    let (mut m, mut s) = block(1, 5);
    assert_eq!(entry(&mut m, &mut s, 5, 3), (2, Outcome::Win), "{{1..5}} at 3");
    let (mut m, mut s) = block(1, 8);
    assert_eq!(entry(&mut m, &mut s, 8, 0).1, Outcome::Draw, "{{1..8}} at 0");
    let (mut m, mut s) = block(2, 10);
    assert_eq!(entry(&mut m, &mut s, 10, 1).1, Outcome::Draw, "{{2..11}} at 1");
    println!("check: {{2..5}} at 2 W, {{1..5}} at 3 W by 2, {{1..8}} at 0 and {{2..11}} at 1 draw");
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e36_low_block_column <n_min> <n_max>");
    assert!(a[0] >= 6, "EB starts at n = 6");
    check();
    for n in a[0]..=a[1] {
        let (mut entries, mut bad, mut wide) = (0, 0, 0);
        let mut ends = Vec::new();
        for h in 1..=(n / 2) as u64 {
            let (mut m, mut s) = block(h, n);
            let sum: u64 = (h..h + n as u64).sum();
            let mut end = None;
            for d in 0..=h + n as u64 - 1 {
                let (v, w) = entry(&mut m, &mut s, n, d);
                let draw_parity = (d + sum) % 2 == 0;
                let fails = v.abs() > 1 || (draw_parity && w != Outcome::Draw);
                if end.is_none() && fails {
                    end = Some(d);
                }
                if d < n as u64 {
                    if draw_parity {
                        entries += 1;
                        if w != Outcome::Draw {
                            bad += 1;
                            if bad <= SHOWN {
                                println!("  n={n} a={h} d={d}: {w:?} (margin {v})");
                            }
                        }
                    }
                    if v.abs() > 1 {
                        wide += 1;
                    }
                }
            }
            ends.push(end.map_or("none".to_string(), |d| d.to_string()));
        }
        println!("n={n}: {entries} draw-parity entries, {bad} non-draws, {wide} entries with |m| > 1 (d ≤ n − 1); \
            first failing d per a = 1..={}: {}", n / 2, ends.join(" "));
    }
}
