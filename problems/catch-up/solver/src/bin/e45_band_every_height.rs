//! Usage: e45_band_every_height <k_min> <k_max>
//! C110 at every height: B = {a..a+2k} minus one number, every d ≤ k − 1 of the draw parity, every height
//! a = 1..=k(2k + 1) + k + 1. Above a > d + Σ offsets (at most k(2k + 1) + k − 1) the value no longer depends on a
//! (C13, Lean `valueAux_map_add`), so these heights settle C110 at every height for the k in range.
//! `Margin` and `Solver` evaluate every entry; their signs must agree.
//! First checks: C1's families {1..8} at 0 and {2..11} at 1 are entries and draw; C47's ({2, 3, 4, 5}, 2), k = 2, is
//! a mover win (a non-draw is detected).

use catch_up::margin::Margin;
use catch_up::{Outcome, Solver};

fn outcome(m: &mut Margin, s: &mut Solver, mask: usize, d: u64) -> Outcome {
    let v = m.margin(mask, d);
    let w = s.position(mask, d);
    let sign = match v {
        v if v > 0 => Outcome::Win,
        0 => Outcome::Draw,
        _ => Outcome::Loss,
    };
    assert_eq!(sign, w, "engines disagree, mask {mask:b}, d {d}");
    w
}

fn entry(a: u64, n: usize, o: usize, d: u64) -> Outcome {
    let b: Vec<u64> = (a..a + n as u64).collect();
    let (mut m, mut s) = (Margin::new(&b), Solver::new(&b));
    outcome(&mut m, &mut s, ((1usize << n) - 1) & !(1 << o), d)
}

fn check() {
    assert_eq!(entry(1, 9, 8, 0), Outcome::Draw, "{{1..8}} at 0");
    assert_eq!(entry(1, 11, 0, 1), Outcome::Draw, "{{2..11}} at 1");
    assert_eq!(entry(1, 5, 0, 2), Outcome::Win, "C47");
    println!("check: {{1..8}} at 0 and {{2..11}} at 1 draw; ({{2, 3, 4, 5}}, 2) is W");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("k_min k_max")).collect();
    assert_eq!(a.len(), 2, "usage: e45_band_every_height <k_min> <k_max>");
    assert!(a[0] >= 3, "the band needs k ≥ 3");
    check();
    for k in a[0]..=a[1] {
        let n = 2 * k as usize + 1;
        let top = k * (2 * k + 1) + k + 1;
        let (mut entries, mut bad) = (0usize, 0usize);
        let mut shown = String::new();
        for h in 1..=top {
            let b: Vec<u64> = (h..h + n as u64).collect();
            let (mut m, mut s) = (Margin::new(&b), Solver::new(&b));
            let sum: u64 = b.iter().sum();
            for o in 0..n {
                for d in (0..k).filter(|d| (d + sum - b[o]) % 2 == 0) {
                    entries += 1;
                    let w = outcome(&mut m, &mut s, ((1usize << n) - 1) & !(1 << o), d);
                    if w != Outcome::Draw {
                        bad += 1;
                        if shown.len() < 200 {
                            shown += &format!(" a={h},hole={},d={d}:{w:?}", b[o]);
                        }
                    }
                }
            }
        }
        println!("k={k}, heights 1..={top}: {entries} draw-parity entries, {bad} non-draws;{shown}");
    }
}
