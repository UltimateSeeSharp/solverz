//! Usage: slide_quad <n_max> [n_min]
//! Does sliding the top quadruple of {1..N} up change the value (L35)? For every N ≤ n_max with an even total, the
//! value of {1..N−4} ∪ ({N−3..N} + c) from `Solver` at every integer c from 0 to T(N) + 1, T(N) = 1 + … + N. Every
//! comparison in the game is j·c + b with |j| ≤ 4 and |b| ≤ T(N), so the value is constant for c > T(N): the range is
//! exact for integer c. Prints, per N, the shifts where the value is not a draw. Control first: O19's base {5, 6, 7}
//! with {8..11} + c draws at c = 0, 1 and is a player-1 win from c = 2.

use catch_up::{Outcome, Solver};

const QUADRUPLE: u64 = 4;
/// O19's base and the shifts of its known values.
const CONTROL_BASE: [u64; 3] = [5, 6, 7];
const CONTROL_SHIFTS: [u64; 4] = [0, 1, 2, 3];

fn main() {
    let n_max: u64 = std::env::args().nth(1).expect("n_max").parse().expect("integer");
    let n_min: u64 = std::env::args().nth(2).map_or(QUADRUPLE, |a| a.parse().expect("integer"));
    let control: Vec<Outcome> = CONTROL_SHIFTS.iter().map(|&c| {
        let top = *CONTROL_BASE.last().unwrap();
        let numbers: Vec<u64> = CONTROL_BASE.iter().copied().chain((1..=QUADRUPLE).map(|t| top + t + c)).collect();
        Solver::new(&numbers).value() }).collect();
    println!("control (O19): {{5,6,7}} ∪ ({{8..11}} + c) for c = {CONTROL_SHIFTS:?}: {control:?} (expected Draw, Draw, Win, Win)");
    for n in n_min.max(QUADRUPLE)..=n_max {
        let total = n * (n + 1) / 2;
        if total % 2 != 0 {
            continue;
        }
        let mut non_draws = vec![];
        for c in 0..=total + 1 {
            let numbers: Vec<u64> = (1..=n).map(|x| if x + QUADRUPLE > n { x + c } else { x }).collect();
            let value = Solver::new(&numbers).value();
            if value != Outcome::Draw {
                non_draws.push((c, value));
            }
        }
        println!("N={n}: c in 0..={}: non-draws {non_draws:?}", total + 1);
    }
}
