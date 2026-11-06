//! Usage: e42_largest_change <k_min> <k_max> <n_max>
//! C116: the player holding the draw keeps it in both roles with turns of one number, or the largest number below
//! its deficit followed by one number (`ShortTurns::with_largest_change`), on C110's band (k in range, every hole,
//! every d ≤ k − 1 of the draw parity, heights 1..=2(2k + 1)), on C1 ({1..N} at a tie) and on C92's three families
//! (({3..N}, 1), ({5..N}, 4), {3..N} minus each adjacent pair at 2), every even-total N ≤ n_max (C92's from N = 11).
//! First checks: the shaped player loses some draws inside {1..10} (the test can fail); C47's ({2, 3, 4, 5}, 2) stays
//! a mover win against it.

use catch_up::margin::Margin;
use catch_up::short_turns::ShortTurns;

/// The least N at which C92's three families are draws (E33).
const C92_FROM: u64 = 11;

/// Shaped Z first (margin ≥ 0) and second (the free mover's margin ≤ 0).
fn holds(s: &mut ShortTurns, mask: usize, d: u64) -> bool {
    s.margin(mask, d, true) >= 0 && s.margin(mask, d, false) <= 0
}

fn check() {
    let numbers: Vec<u64> = (1..=10).collect();
    let (mut s, mut m) = (ShortTurns::with_largest_change(&numbers), Margin::new(&numbers));
    let (mut draws, mut lost) = (0, 0);
    for mask in 1..1usize << numbers.len() {
        for d in 0..=10u64 {
            if m.margin(mask, d) == 0 {
                draws += 1;
                lost += !holds(&mut s, mask, d) as usize;
            }
        }
    }
    assert!(lost > 0, "the shape must lose some draw inside {{1..10}}");
    let mut s = ShortTurns::with_largest_change(&[2, 3, 4, 5]);
    assert!(s.margin(0b1111, 2, false) > 0, "C47's mover win");
    println!("check: the shaped player loses {lost} of {draws} draws inside {{1..10}}; ({{2, 3, 4, 5}}, 2) stays a mover win");
}

/// One family member (numbers, deficit): kept or not.
fn member(numbers: &[u64], d: u64) -> bool {
    let mut s = ShortTurns::with_largest_change(numbers);
    holds(&mut s, (1usize << numbers.len()) - 1, d)
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("k_min k_max n_max")).collect();
    assert_eq!(a.len(), 3, "usage: e42_largest_change <k_min> <k_max> <n_max>");
    check();
    for n in (3..=a[2]).filter(|n| n * (n + 1) / 2 % 2 == 0) {
        let c1 = member(&(1..=n).collect::<Vec<_>>(), 0);
        let mut c92 = vec![member(&(3..=n).collect::<Vec<_>>(), 1), member(&(5..=n).collect::<Vec<_>>(), 4)];
        for j in 3..n {
            c92.push(member(&(3..=n).filter(|&x| x != j && x != j + 1).collect::<Vec<_>>(), 2));
        }
        // C92's families are draws from N = 11 on.
        let lost = c92.iter().filter(|&&k| !k).count();
        if n >= C92_FROM {
            println!("N={n}: C1 kept {c1}; C92's families: {} members, {lost} lost", c92.len());
        } else {
            println!("N={n}: C1 kept {c1}");
        }
    }
    for k in a[0]..=a[1] {
        let n = 2 * k as usize + 1;
        let (mut positions, mut lost) = (0, 0);
        let mut shown = String::new();
        for h in 1..=2 * n as u64 {
            let numbers: Vec<u64> = (h..h + n as u64).collect();
            let mut s = ShortTurns::with_largest_change(&numbers);
            let full = (1usize << n) - 1;
            for o in 0..n {
                let sum: u64 = numbers.iter().sum::<u64>() - numbers[o];
                for d in (0..k).filter(|d| (d + sum) % 2 == 0) {
                    positions += 1;
                    if !holds(&mut s, full & !(1 << o), d) {
                        lost += 1;
                        if shown.len() < 200 {
                            shown += &format!(" a={h},hole={},d={d}", numbers[o]);
                        }
                    }
                }
            }
        }
        println!("C110 k={k}, heights 1..={}: {positions} positions, {lost} lost;{shown}", 2 * n);
    }
}
