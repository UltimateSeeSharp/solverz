//! Threshold variants of Catch-Up's margin game (I31, C120): a turn takes at least one number and continues while the
//! mover's total is below the opponent's + θ; θ = 0 is Catch-Up. Margins from the mover's side; memo over (remaining mask,
//! lead δ = mover − opponent), with δ ∈ [−(θ + max) − 1, θ) at every turn start and mid-turn.

const UNKNOWN: i16 = i16::MIN;

pub struct Threshold {
    numbers: Vec<u64>,
    theta: i64,
    lo: i64,
    width: usize,
    memo: Vec<i16>,
}

impl Threshold {
    pub fn new(numbers: &[u64], theta: u64) -> Self {
        assert!(numbers.len() <= crate::MAX_NUMBERS, "at most {} numbers", crate::MAX_NUMBERS);
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        let max = numbers.iter().copied().max().unwrap_or(0) as i64;
        let theta = theta as i64;
        let lo = -(theta + max) - 1;
        let width = (theta.max(1) - lo + 1) as usize;
        Threshold { numbers: numbers.to_vec(), theta, lo, width, memo: vec![UNKNOWN; (1usize << numbers.len()) * width] }
    }

    /// The mover's margin with `mask` left and lead `delta` (≤ 0 at a turn start, < θ mid-turn).
    pub fn margin(&mut self, mask: usize, delta: i64) -> i64 {
        if mask == 0 {
            return delta;
        }
        assert!(delta >= self.lo && delta < self.theta.max(1), "lead {delta} outside the table");
        let slot = mask * self.width + (delta - self.lo) as usize;
        if self.memo[slot] != UNKNOWN {
            return self.memo[slot] as i64;
        }
        let mut best = i64::MIN;
        let mut rest = mask;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let d2 = delta + self.numbers[i] as i64;
            let next = mask & !(1 << i);
            let v = if d2 >= self.theta { -self.margin(next, -d2) } else { self.margin(next, d2) };
            best = best.max(v);
        }
        self.memo[slot] = i16::try_from(best).expect("margin fits i16");
        best
    }
}

#[cfg(test)]
mod tests {
    use super::Threshold;
    use crate::margin::Margin;

    /// θ = 0 is Catch-Up: equal to `Margin` at every turn start (lead −d).
    #[test]
    fn theta_zero_is_catch_up() {
        let numbers: Vec<u64> = (1..=9).collect();
        let (mut t, mut m) = (Threshold::new(&numbers, 0), Margin::new(&numbers));
        for mask in 0..1usize << numbers.len() {
            for d in 0..=9u64 {
                assert_eq!(t.margin(mask, -(d as i64)), m.margin(mask, d), "mask {mask:b} d {d}");
            }
        }
    }

    /// Independent recursion over lists for θ = 3.
    fn brute(rest: &[u64], delta: i64, theta: i64) -> i64 {
        if rest.is_empty() {
            return delta;
        }
        (0..rest.len())
            .map(|i| {
                let r: Vec<u64> = rest.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, &x)| x).collect();
                let d2 = delta + rest[i] as i64;
                if d2 >= theta { -brute(&r, -d2, theta) } else { brute(&r, d2, theta) }
            })
            .max()
            .unwrap()
    }

    #[test]
    fn theta_three_matches_brute_force() {
        let numbers: Vec<u64> = (1..=7).collect();
        let mut t = Threshold::new(&numbers, 3);
        for mask in 0..1usize << numbers.len() {
            let xs: Vec<u64> = (0..7).filter(|&i| mask >> i & 1 == 1).map(|i| numbers[i]).collect();
            for d in 0..=7i64 {
                assert_eq!(t.margin(mask, -d), brute(&xs, -d, 3), "{xs:?} lead {}", -d);
            }
        }
    }
}
