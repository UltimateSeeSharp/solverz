//! Usage: e35_tied_block_holes <n_max>
//! C106 (B2): for every block B = {a..a+n−1}, n = 4..=n_max, and every hole h with sum(B − h) even (the draw parity):
//! V(B − h, 0) ≠ loss (the tied mover never loses), at every height a = 1..=2n and at a = n² (rounds regime); at a = 1
//! also ≠ win. Counts wins and the largest winning margin. Every position is evaluated by `Margin` and `Solver`; their
//! signs must agree.
//! First checks: {1..N} = {1..N+1} − {N+1} draws for N = 4, 7, 8 (C1); the tied mover on {1, 3} = {1, 2, 3} − 2 wins.

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

fn tied(m: &mut Margin, s: &mut Solver, n: usize, o: usize) -> (i64, Outcome) {
    let mask = ((1usize << n) - 1) & !(1 << o);
    let (v, w) = (m.margin(mask, 0), s.position(mask, 0));
    assert_eq!(sign(v), w, "engines disagree, hole offset {o}");
    (v, w)
}

fn check() {
    for top in [5u64, 8, 9] {
        let b: Vec<u64> = (1..=top).collect();
        let n = b.len();
        let (v, _) = tied(&mut Margin::new(&b), &mut Solver::new(&b), n, n - 1);
        assert_eq!(v, 0, "{{1..{}}} is a draw", top - 1);
    }
    let b = [1u64, 2, 3];
    assert_eq!(tied(&mut Margin::new(&b), &mut Solver::new(&b), 3, 1).1, Outcome::Win, "{{1, 3}} at a tie");
    println!("check: {{1..4}}, {{1..7}}, {{1..8}} draw; {{1, 3}} is W");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_max")).collect();
    assert_eq!(a.len(), 1, "usage: e35_tied_block_holes <n_max>");
    check();
    for n in 4..=a[0] as usize {
        let heights: Vec<u64> = (1..=2 * n as u64).chain([(n * n) as u64]).collect();
        let (mut entries, mut losses, mut wins_low, mut wins, mut max_win) = (0, 0, 0, 0, 0);
        for &h in &heights {
            let b: Vec<u64> = (h..h + n as u64).collect();
            let (mut m, mut s) = (Margin::new(&b), Solver::new(&b));
            let sum: u64 = b.iter().sum();
            for o in 0..n {
                if (sum - b[o]) % 2 == 1 {
                    continue;
                }
                entries += 1;
                let (v, w) = tied(&mut m, &mut s, n, o);
                if w == Outcome::Loss {
                    losses += 1;
                    if losses <= SHOWN {
                        println!("  LOSS n={n} a={h} hole {}: margin {v}", h + o as u64);
                    }
                }
                if w == Outcome::Win {
                    wins += 1;
                    max_win = max_win.max(v);
                    if h == 1 {
                        wins_low += 1;
                        println!("  WIN at a = 1: n={n} hole {}: margin {v}", 1 + o);
                    }
                }
            }
        }
        println!("n={n}: heights 1..={} and {}: {entries} draw-parity entries, {losses} losses, {wins_low} wins at a = 1; \
            {wins} wins in all, largest margin {max_win}", 2 * n, n * n);
    }
}
