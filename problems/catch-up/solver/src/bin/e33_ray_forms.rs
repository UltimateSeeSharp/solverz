//! Usage: e33_ray_forms <n_min> <n_max>
//! The hypotheses of the lower ray's two other forms (C91, C92), for every even-total N in range.
//! C91 (successor): ({3..N}, 1) draws; V({2..N} ∖ {b, b+1}, 2) ≠ win for 3 ≤ b < N; ({2..N−1}, N−1) ≠ loss.
//! C92 (canonical): ({3..N}, 1) draws; ({5..N}, 4) draws; V({3..N} ∖ {b−1, b}, 2) = draw for 4 ≤ b ≤ N.
//! One `Solver` on {1..N} per N; prints every failing position.
//! First check: ({3..7}, 1) and ({3..8}, 1) draw (Lean `base_seven`, `base_eight`).

use catch_up::{Outcome, Solver};

fn mask(numbers: impl Iterator<Item = u64>) -> usize {
    numbers.map(|x| 1usize << (x - 1)).sum()
}

fn even_total(n: u64) -> bool {
    (n * (n + 1) / 2) % 2 == 0
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e33_ray_forms <n_min> <n_max>");
    for n in [7u64, 8] {
        let mut s = Solver::new(&(1..=n).collect::<Vec<u64>>());
        assert_eq!(s.position(mask(3..=n), 1), Outcome::Draw, "({{3..{n}}}, 1) draws");
    }
    println!("check: ({{3..7}}, 1) and ({{3..8}}, 1) draw");
    for n in (a[0]..=a[1]).filter(|&n| even_total(n)) {
        let mut s = Solver::new(&(1..=n).collect::<Vec<u64>>());
        let start = s.position(mask(3..=n), 1);
        let top = s.position(mask(2..n), n - 1);
        let mut successor_wins = vec![];
        for b in 3..n {
            if s.position(mask((2..=n).filter(|&x| x != b && x != b + 1)), 2) == Outcome::Win {
                successor_wins.push(b);
            }
        }
        let four = s.position(mask(5..=n), 4);
        let mut canonical_fails = vec![];
        for b in 4..=n {
            let o = s.position(mask((3..=n).filter(|&x| x != b - 1 && x != b)), 2);
            if o != Outcome::Draw {
                canonical_fails.push((b, o));
            }
        }
        let c91 = start == Outcome::Draw && successor_wins.is_empty() && top != Outcome::Loss;
        let c92 = start == Outcome::Draw && four == Outcome::Draw && canonical_fails.is_empty();
        println!(
            "N={n}: start {start:?}, top {top:?}, successor wins at b {successor_wins:?} -> C91 {}; \
             ({{5..N}}, 4) {four:?}, canonical non-draws {canonical_fails:?} -> C92 {}; positions {}",
            if c91 { "holds" } else { "FAILS" },
            if c92 { "holds" } else { "FAILS" },
            s.positions
        );
    }
}
