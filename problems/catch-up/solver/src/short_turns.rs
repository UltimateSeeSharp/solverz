//! Margin game (C33) with one player, Z, restricted to short turns (C114): while Z can end its turn within `budget`
//! numbers, it only takes numbers that keep that possible (a number below the deficit is allowed only if the turn can
//! still end within the budget); when it cannot, its turn is free. The other player is free. Margins from the mover's
//! side; memo over (remaining mask, deficit, whether Z moves, numbers taken so far this turn, capped at the budget).

const UNKNOWN: i16 = i16::MIN;

pub struct ShortTurns {
    numbers: Vec<u64>,
    budget: usize,
    stride: usize,
    memo: Vec<i16>,
}

impl ShortTurns {
    pub fn new(numbers: &[u64], budget: usize) -> Self {
        assert!(numbers.len() <= crate::MAX_NUMBERS, "at most {} numbers", crate::MAX_NUMBERS);
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        assert!(budget >= 1, "a turn takes at least one number");
        let stride = numbers.iter().copied().max().unwrap_or(0) as usize + 1;
        let size = (1usize << numbers.len()) * stride * 2 * (budget + 1);
        ShortTurns { numbers: numbers.to_vec(), budget, stride, memo: vec![UNKNOWN; size] }
    }

    /// The mover's margin with `mask` left, trailing by `d`, at a turn start; `z`: the mover is Z.
    pub fn margin(&mut self, mask: usize, d: u64, z: bool) -> i64 {
        self.step(mask, d, z, 0)
    }

    /// Whether some turn of at most `left` numbers from `mask` reaches `d`.
    fn can_end(&self, mask: usize, d: u64, left: usize) -> bool {
        let mut top = [0u64; 2];
        let mut rest = mask;
        while rest != 0 {
            let x = self.numbers[rest.trailing_zeros() as usize];
            rest &= rest - 1;
            if x > top[0] {
                top = [x, top[0]];
            } else if x > top[1] {
                top[1] = x;
            }
        }
        assert!(left <= 2, "budgets above 2 are not implemented");
        (left >= 1 && top[0] >= d) || (left >= 2 && top[0] + top[1] >= d && mask.count_ones() >= 2)
    }

    fn step(&mut self, mask: usize, d: u64, z: bool, taken: usize) -> i64 {
        if mask == 0 {
            return -(d as i64);
        }
        let taken = taken.min(self.budget);
        let memo = (d as usize) < self.stride;
        let slot = (((mask * self.stride + d as usize) * 2 + z as usize) * (self.budget + 1)) + taken;
        if memo && self.memo[slot] != UNKNOWN {
            return self.memo[slot] as i64;
        }
        let restricted = z && taken < self.budget;
        let (mut best, mut best_allowed) = (i64::MIN, i64::MIN);
        let mut rest = mask;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            let ends = x >= d;
            let v = if ends { -self.step(next, x - d, !z, 0) } else { self.step(next, d - x, z, taken + 1) };
            best = best.max(v);
            if restricted && (ends || (taken + 1 < self.budget && self.can_end(next, d - x, self.budget - taken - 1))) {
                best_allowed = best_allowed.max(v);
            }
        }
        let res = if restricted && best_allowed != i64::MIN { best_allowed } else { best };
        if memo {
            self.memo[slot] = i16::try_from(res).expect("margin fits i16");
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use super::ShortTurns;
    use crate::margin::Margin;

    /// Budget 2 with turns that never need a second number: on numbers above every deficit each turn is one number,
    /// so the restriction is moot and the value is the margin game's.
    #[test]
    fn moot_when_every_turn_is_one_number() {
        let numbers: Vec<u64> = (20..=27).collect();
        let (mut s, mut m) = (ShortTurns::new(&numbers, 2), Margin::new(&numbers));
        for mask in 0..1usize << numbers.len() {
            for d in 0..=19u64 {
                for z in [false, true] {
                    assert_eq!(s.margin(mask, d, z), m.margin(mask, d), "mask {mask:b} d {d} z {z}");
                }
            }
        }
    }

    /// A restricted player never does better than free play, and the opponent never worse; on {1..9} the
    /// restriction binds somewhere (the engine is not the margin game in disguise).
    #[test]
    fn restriction_only_hurts_z_and_binds() {
        let numbers: Vec<u64> = (1..=9).collect();
        let (mut s, mut m) = (ShortTurns::new(&numbers, 2), Margin::new(&numbers));
        let mut binds = 0;
        for mask in 0..1usize << numbers.len() {
            for d in 0..=9u64 {
                let free = m.margin(mask, d);
                assert!(s.margin(mask, d, true) <= free, "Z first, mask {mask:b} d {d}");
                assert!(s.margin(mask, d, false) >= free, "Z second, mask {mask:b} d {d}");
                binds += (s.margin(mask, d, true) != free) as usize;
            }
        }
        assert!(binds > 0);
    }

    /// Hand-checked: ({1, 2, 3}, 4) with Z first. Free, Z takes all three (2, 1, then 3) and wins by 2. Within two
    /// numbers its best is 3 + 2 (or 2 + 3), leading by 1; the opponent ties with 1: margin 0. Z second: the
    /// opponent's free turn takes all three, +2 for it.
    #[test]
    fn small_case() {
        let numbers = [1u64, 2, 3];
        let mut s = ShortTurns::new(&numbers, 2);
        assert_eq!(Margin::new(&numbers).margin(0b111, 4), 2);
        assert_eq!(s.margin(0b111, 4, true), 0);
        assert_eq!(s.margin(0b111, 4, false), 2);
    }
}
