//! Controller games G_X (C111): the margin game (C33) in which one player, the controller, decides at every exact
//! catch-up (a pick x = d > 0 that brings the picker level) whether the turn ends (the real rule) or the picker takes
//! exactly one more number, after which it leads and the turn passes. Memo over (remaining mask, deficit, whether the
//! mover is the controller); margins from the mover's side.

const UNKNOWN: i16 = i16::MIN;

pub struct Controller {
    numbers: Vec<u64>,
    stride: usize,
    memo: Vec<i16>,
}

impl Controller {
    pub fn new(numbers: &[u64]) -> Self {
        assert!(numbers.len() <= crate::MAX_NUMBERS, "at most {} numbers", crate::MAX_NUMBERS);
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        let stride = numbers.iter().copied().max().unwrap_or(0) as usize + 1;
        Controller { numbers: numbers.to_vec(), stride, memo: vec![UNKNOWN; (1usize << numbers.len()) * stride * 2] }
    }

    /// The mover's margin with `mask` left, trailing by `d`; `ctl` = the mover is the controller.
    pub fn margin(&mut self, mask: usize, d: u64, ctl: bool) -> i64 {
        if mask == 0 {
            return -(d as i64);
        }
        let memo = (d as usize) < self.stride;
        let slot = (mask * self.stride + d as usize) * 2 + ctl as usize;
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
            let o = if x > d {
                -self.margin(next, x - d, !ctl)
            } else if x < d {
                self.margin(next, d - x, ctl)
            } else {
                // Exact catch-up: end the turn (the opponent moves at a tie) or take one more number.
                let end = -self.margin(next, 0, !ctl);
                let more = self.one_more(next, ctl);
                if ctl { end.max(more) } else { end.min(more) }
            };
            best = best.max(o);
        }
        if memo {
            self.memo[slot] = i16::try_from(best).expect("margin fits i16");
        }
        best
    }

    /// The picker, level, must take one more number and then leads by it (nothing left: the game ends level).
    fn one_more(&mut self, mask: usize, ctl: bool) -> i64 {
        let mut best = if mask == 0 { 0 } else { i64::MIN };
        let mut rest = mask;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let y = self.numbers[i];
            best = best.max(-self.margin(mask & !(1 << i), y, !ctl));
        }
        best
    }
}

#[cfg(test)]
mod tests {
    use super::Controller;
    use crate::margin::Margin;

    /// Independent whole-turn reference: `me`, `opp` scores, the picker strictly behind keeps picking; at an exact
    /// catch-up the controller chooses. Returns the margin of the player to move at the turn start.
    fn reference(rest: &[u64], me: i64, opp: i64, ctl: bool) -> i64 {
        if rest.is_empty() {
            return me - opp;
        }
        let mut outcomes = vec![];
        picks(rest, me, opp, ctl, &mut outcomes);
        outcomes.into_iter().max().unwrap()
    }

    /// Every way the current turn can go, as the mover's final margin.
    fn picks(rest: &[u64], me: i64, opp: i64, ctl: bool, out: &mut Vec<i64>) {
        if rest.is_empty() {
            out.push(me - opp);
            return;
        }
        for i in 0..rest.len() {
            let r: Vec<u64> = rest.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, &x)| x).collect();
            let me2 = me + rest[i] as i64;
            if me2 > opp {
                out.push(-reference(&r, opp, me2, !ctl));
            } else if me2 < opp {
                picks(&r, me2, opp, ctl, out);
            } else {
                let end = -reference(&r, opp, me2, !ctl);
                let more = if r.is_empty() {
                    0
                } else {
                    (0..r.len())
                        .map(|j| {
                            let r2: Vec<u64> = r.iter().enumerate().filter(|&(t, _)| t != j).map(|(_, &x)| x).collect();
                            -reference(&r2, opp, me2 + r[j] as i64, !ctl)
                        })
                        .max()
                        .unwrap()
                };
                out.push(if ctl { end.max(more) } else { end.min(more) });
            }
        }
    }

    #[test]
    fn agrees_with_reference_on_subsets_of_one_to_seven() {
        let numbers: Vec<u64> = (1..=7).collect();
        let mut c = Controller::new(&numbers);
        for mask in 0..1usize << numbers.len() {
            let xs: Vec<u64> = (0..7).filter(|&i| mask >> i & 1 == 1).map(|i| numbers[i]).collect();
            for d in 0..=7u64 {
                for ctl in [false, true] {
                    assert_eq!(c.margin(mask, d, ctl), reference(&xs, 0, d as i64, ctl), "{xs:?} d {d} ctl {ctl}");
                }
            }
        }
    }

    /// Without any exact catch-up the controller has nothing to decide: the margin game itself.
    #[test]
    fn equals_margin_on_even_numbers_at_odd_deficits() {
        let numbers: Vec<u64> = (1..=8).map(|x| 2 * x).collect();
        let (mut c, mut m) = (Controller::new(&numbers), Margin::new(&numbers));
        for mask in 0..1usize << numbers.len() {
            for d in (1..=15u64).step_by(2) {
                assert_eq!(c.margin(mask, d, true), m.margin(mask, d), "mask {mask:b} d {d}");
            }
        }
    }
}
