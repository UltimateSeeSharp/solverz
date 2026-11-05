//! Usage: e41_short_turns <k_min> <k_max> <n_max>
//! C114: the player holding the draw keeps it with turns of at most two numbers (`ShortTurns`, budget 2), in both
//! roles, on C110's band (B = {a..a+2k}, any hole, every d ≤ k − 1 of the draw parity, heights a = 1..=2(2k + 1))
//! and on C1 ({1..N} at a tie, every even-total N ≤ n_max).
//! First checks: with budget 1 the restriction loses C110 positions at k = 3 (the test can fail); C47's
//! ({2, 3, 4, 5}, 2) stays a mover win against the restricted player (a real win is not hidden).

use catch_up::short_turns::ShortTurns;

const BUDGET: usize = 2;

/// Restricted Z first (margin ≥ 0 keeps the draw) and second (the free mover's margin ≤ 0).
fn holds(s: &mut ShortTurns, mask: usize, d: u64) -> (bool, bool) {
    (s.margin(mask, d, true) >= 0, s.margin(mask, d, false) <= 0)
}

/// C110's draw-parity positions at height `a`; the number lost in either role.
fn band_losses(k: u64, a: u64, budget: usize, shown: &mut String) -> (usize, usize) {
    let n = 2 * k as usize + 1;
    let numbers: Vec<u64> = (a..a + n as u64).collect();
    let full = (1usize << n) - 1;
    let mut s = ShortTurns::new(&numbers, budget);
    let (mut positions, mut lost) = (0, 0);
    for o in 0..n {
        let mask = full & !(1 << o);
        let sum: u64 = numbers.iter().sum::<u64>() - numbers[o];
        for d in (0..k).filter(|d| (d + sum) % 2 == 0) {
            positions += 1;
            let (first, second) = holds(&mut s, mask, d);
            if !(first && second) {
                lost += 1;
                if shown.len() < 200 {
                    *shown += &format!(" a={a},hole={},d={d}{}{}", numbers[o], if first { "" } else { ":Z1" },
                        if second { "" } else { ":Z2" });
                }
            }
        }
    }
    (positions, lost)
}

fn check() {
    let mut shown = String::new();
    let lost: usize = (1..=6).map(|a| band_losses(3, a, 1, &mut shown).1).sum();
    assert!(lost > 0, "budget 1 must lose some C110 position at k = 3");
    let numbers = [2u64, 3, 4, 5];
    let mut s = ShortTurns::new(&numbers, BUDGET);
    assert!(s.margin(0b1111, 2, false) > 0, "C47's mover win");
    println!("check: budget 1 loses {lost} C110 positions at k = 3, a ≤ 6; ({{2, 3, 4, 5}}, 2) stays a mover win");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("k_min k_max n_max")).collect();
    assert_eq!(a.len(), 3, "usage: e41_short_turns <k_min> <k_max> <n_max>");
    check();
    for n in (3..=a[2]).filter(|n| n * (n + 1) / 2 % 2 == 0) {
        let numbers: Vec<u64> = (1..=n).collect();
        let mut s = ShortTurns::new(&numbers, BUDGET);
        let (first, second) = holds(&mut s, (1usize << n) - 1, 0);
        println!("C1 N={n}: restricted player holds the draw moving first {first}, second {second}");
    }
    for k in a[0]..=a[1] {
        let mut shown = String::new();
        let (mut positions, mut lost) = (0, 0);
        for h in 1..=2 * (2 * k + 1) {
            let (p, l) = band_losses(k, h, BUDGET, &mut shown);
            positions += p;
            lost += l;
        }
        println!("C110 k={k}, heights 1..={}: {positions} positions, {lost} lost by the restricted player;{shown}",
            2 * (2 * k + 1));
    }
}
