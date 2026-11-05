//! Usage: e39_controller_games <n_min> <n_max>
//! C112: on I_N = {1..N} with an even total, neither controller wins its game G_X (C111): player 1's margin is 0 in
//! G_P1 (player 1 controls) and in G_P2 (player 2 controls). Prints, per N, player 1's margin in G_P1, in G_P2 and in
//! the real game (C33), and flags every even-total N where a controller game is not 0.
//! First checks: N = 3, 4 give 0 in all three games; the real margins match C1's known signs for N ≤ 12.

use catch_up::controller::Controller;
use catch_up::margin::Margin;

/// Player 1's margins (G_P1, G_P2, real) on {1..n}; player 1 is the mover at a tie.
fn margins(n: u64) -> (i64, i64, i64) {
    let numbers: Vec<u64> = (1..=n).collect();
    let full = (1usize << n) - 1;
    let mut c = Controller::new(&numbers);
    let (p1, p2) = (c.margin(full, 0, true), c.margin(full, 0, false));
    drop(c);
    (p1, p2, Margin::new(&numbers).margin(full, 0))
}

fn even_total(n: u64) -> bool {
    n * (n + 1) / 2 % 2 == 0
}

fn check() {
    for n in [3, 4] {
        assert_eq!(margins(n), (0, 0, 0), "N = {n}");
    }
    for n in 1..=12 {
        let real = margins(n).2;
        assert_eq!(real == 0, even_total(n), "C1's sign pattern at N = {n}");
    }
    println!("check: N = 3, 4 are 0 in every game; the real margin is 0 exactly at even totals for N ≤ 12");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e39_controller_games <n_min> <n_max>");
    check();
    let mut bad = 0;
    for n in a[0]..=a[1] {
        let (p1, p2, real) = margins(n);
        let flag = if even_total(n) && (p1 != 0 || p2 != 0) {
            bad += 1;
            "  <- C112 fails"
        } else {
            ""
        };
        println!("N={n} ({} total): G_P1 {p1}, G_P2 {p2}, real {real}{flag}", if even_total(n) { "even" } else { "odd" });
    }
    println!("{bad} even-total N with a controller win");
}
