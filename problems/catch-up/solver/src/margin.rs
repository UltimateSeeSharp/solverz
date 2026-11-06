//! Margin game m(S, d) (C33) on the subsets of one fixed list of numbers: the mover trails by d and keeps picking
//! while strictly behind; the payoff is the mover's final score minus the opponent's, both players optimizing it.
//! Its sign is the Catch-Up outcome (Lean `valueAux_eq_ofMargin`); the tests check it against `Solver`.

const UNKNOWN: i16 = i16::MIN;

/// Memoized margins over (remaining mask, deficit).
pub struct Margin {
    numbers: Vec<u64>,
    stride: usize,
    memo: Vec<i16>,
}

impl Margin {
    pub fn new(numbers: &[u64]) -> Self {
        assert!(numbers.len() <= crate::MAX_NUMBERS, "at most {} numbers", crate::MAX_NUMBERS);
        // Play keeps the deficit ≤ the largest number; larger starting deficits are not memoized.
        let stride = numbers.iter().copied().max().unwrap_or(0) as usize + 1;
        Margin { numbers: numbers.to_vec(), stride, memo: vec![UNKNOWN; (1usize << numbers.len()) * stride] }
    }

    /// m(S, d) with S = the numbers whose bits are set in `mask`.
    pub fn margin(&mut self, mask: usize, d: u64) -> i64 {
        if mask == 0 {
            return -(d as i64);
        }
        let memo = (d as usize) < self.stride;
        let slot = mask * self.stride + d as usize;
        if memo && self.memo[slot] != UNKNOWN {
            return self.memo[slot] as i64;
        }
        let mut best = i64::MIN;
        let mut rest = mask;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            // Catching up ends the turn and the opponent trails by the lead; otherwise the mover picks again.
            let o = if x >= d { -self.margin(next, x - d) } else { self.margin(next, d - x) };
            best = best.max(o);
        }
        if memo {
            self.memo[slot] = i16::try_from(best).expect("margin fits i16");
        }
        best
    }
}

#[cfg(test)]
mod tests {
    use super::Margin;
    use crate::{Outcome, Solver};

    fn sign(m: i64) -> Outcome {
        match m {
            m if m > 0 => Outcome::Win,
            0 => Outcome::Draw,
            _ => Outcome::Loss,
        }
    }

    #[test]
    fn sign_matches_solver_on_subsets_of_one_to_nine() {
        let numbers: Vec<u64> = (1..=9).collect();
        let (mut m, mut s) = (Margin::new(&numbers), Solver::new(&numbers));
        for mask in 0..1usize << numbers.len() {
            for d in 0..=9 {
                assert_eq!(sign(m.margin(mask, d)), s.position(mask, d), "mask {mask:b}, d {d}");
            }
        }
    }

    #[test]
    fn known_margins() {
        // {1, 3} at a tie: pick 3, the opponent takes 1 and trails by 2 at the end.
        assert_eq!(Margin::new(&[1, 3]).margin(0b11, 0), 2);
        // C47's exception: {2, 3, 4, 5} at deficit 2 is a mover win.
        assert!(Margin::new(&[2, 3, 4, 5]).margin(0b1111, 2) > 0);
    }
}
