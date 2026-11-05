//! Usage: e40_dense_endpoints <n_min> <n_max>
//! I20's kill test (1): the two deficit-1 endpoint families of `even_dense_loss_forces_upper_or_odd_prefix_endpoint`
//! (C99), at every even-total N in range:
//!   A: ({2..N} ∖ {d − 1, d, h}, 1), h odd, h ∉ {1, d}, 7 ≤ d ≤ N;
//!   B: ({3..N} ∖ {d − 2, d − 1, d}, 1), d odd, 7 ≤ d ≤ N.
//! Prints, per N and family, the positions and their losses and wins. `Margin` and `Solver` evaluate every position;
//! their signs must agree.
//! First checks: C99's N = 8 loss ({1, 5, 6, 7, 8}, 5) is a loss; ({2, 4, 6}, 2) is a loss (C99, N = 6).

use catch_up::margin::Margin;
use catch_up::{Outcome, Solver};

/// The engines' common outcome, from both.
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

fn single(xs: &[u64], d: u64) -> Outcome {
    let (mut m, mut s) = (Margin::new(xs), Solver::new(xs));
    outcome(&mut m, &mut s, (1usize << xs.len()) - 1, d)
}

fn check() {
    assert_eq!(single(&[1, 5, 6, 7, 8], 5), Outcome::Loss, "C99's N = 8 loss");
    assert_eq!(single(&[2, 4, 6], 2), Outcome::Loss, "C99's N = 6 loss");
    println!("check: ({{1, 5, 6, 7, 8}}, 5) and ({{2, 4, 6}}, 2) are losses");
}

#[derive(Default)]
struct Tally {
    positions: usize,
    losses: usize,
    wins: usize,
    shown: String,
}

impl Tally {
    fn add(&mut self, o: Outcome, label: String) {
        self.positions += 1;
        match o {
            Outcome::Loss => {
                self.losses += 1;
                self.shown += &format!(" {label}:L");
            }
            Outcome::Win => {
                self.wins += 1;
                self.shown += &format!(" {label}:W");
            }
            Outcome::Draw => {}
        }
    }
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e40_dense_endpoints <n_min> <n_max>");
    check();
    for n in a[0]..=a[1] {
        if n * (n + 1) / 2 % 2 == 1 {
            continue;
        }
        let xs: Vec<u64> = (2..=n).collect();
        let (mut m, mut s) = (Margin::new(&xs), Solver::new(&xs));
        let bit = |x: u64| 1usize << (x - 2);
        let full = (1usize << xs.len()) - 1;
        let (mut fa, mut fb) = (Tally::default(), Tally::default());
        for d in 7..=n {
            for h in (3..=n).step_by(2).filter(|&h| h != d && h != d - 1) {
                let mask = full & !bit(d - 1) & !bit(d) & !bit(h);
                fa.add(outcome(&mut m, &mut s, mask, 1), format!("A(d={d},h={h})"));
            }
            if d % 2 == 1 {
                let mask = full & !bit(2) & !bit(d - 2) & !bit(d - 1) & !bit(d);
                fb.add(outcome(&mut m, &mut s, mask, 1), format!("B(d={d})"));
            }
        }
        println!("N={n}: A {} positions, {} losses, {} wins; B {} positions, {} losses, {} wins;{}{}",
            fa.positions, fa.losses, fa.wins, fb.positions, fb.losses, fb.wins, fa.shown, fb.shown);
    }
}
