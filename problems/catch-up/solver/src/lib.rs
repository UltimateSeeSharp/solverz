//! Catch-Up solver. `Solver` mirrors `CatchUp.valueAux` in formal-conjectures
//! `FormalConjectures/Paper/CatchUpConjecture.lean`; `reference_value` is an independent
//! turn-by-turn implementation of the paper's rules, used only to cross-check it.

use std::cmp::Ordering;

#[cfg(feature = "cuda")]
pub mod cuda;
pub mod layered;
pub mod tiled;
#[cfg(feature = "cuda")]
pub mod tiled_cuda;

/// Game value from the point of view of the player about to move. Ordered Loss < Draw < Win.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Outcome {
    Loss,
    Draw,
    Win,
}

impl Outcome {
    /// The same result seen by the other player.
    pub fn neg(self) -> Self {
        match self {
            Outcome::Loss => Outcome::Win,
            Outcome::Draw => Outcome::Draw,
            Outcome::Win => Outcome::Loss,
        }
    }

    fn of_diff(diff: i64) -> Self {
        match diff.cmp(&0) {
            Ordering::Greater => Outcome::Win,
            Ordering::Equal => Outcome::Draw,
            Ordering::Less => Outcome::Loss,
        }
    }
}

const UNKNOWN: u8 = 0;
const ENTRIES_PER_BYTE: usize = 4;
const BITS_PER_ENTRY: usize = 2;
const ENTRY_MASK: u8 = 0b11;

/// Memo of outcomes, 2 bits per (remaining set, gap) position.
struct Table {
    bytes: Vec<u8>,
    stride: usize,
}

impl Table {
    fn new(n: usize, stride: usize) -> Self {
        let entries = (1usize << n) * stride;
        Table { bytes: vec![0; entries.div_ceil(ENTRIES_PER_BYTE)], stride }
    }

    fn slot(&self, mask: usize, gap: usize) -> (usize, usize) {
        let i = mask * self.stride + gap;
        (i / ENTRIES_PER_BYTE, BITS_PER_ENTRY * (i % ENTRIES_PER_BYTE))
    }

    fn get(&self, mask: usize, gap: usize) -> Option<Outcome> {
        let (byte, shift) = self.slot(mask, gap);
        match (self.bytes[byte] >> shift) & ENTRY_MASK {
            UNKNOWN => None,
            1 => Some(Outcome::Loss),
            2 => Some(Outcome::Draw),
            _ => Some(Outcome::Win),
        }
    }

    fn set(&mut self, mask: usize, gap: usize, o: Outcome) {
        let (byte, shift) = self.slot(mask, gap);
        self.bytes[byte] |= (o as u8 + 1) << shift;
    }
}

/// Exact solver for Catch-Up on one fixed set of distinct positive numbers.
pub struct Solver {
    numbers: Vec<u64>,
    table: Table,
    /// Distinct positions evaluated so far.
    pub positions: u64,
}

pub const MAX_NUMBERS: usize = 32;

impl Solver {
    pub fn new(numbers: &[u64]) -> Self {
        assert!(numbers.len() <= MAX_NUMBERS, "at most {MAX_NUMBERS} numbers");
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        let max = numbers.iter().copied().max().unwrap_or(0) as usize;
        // During play the mover trails by at most the largest number, so gap ∈ [0, max].
        Solver { numbers: numbers.to_vec(), table: Table::new(numbers.len(), max + 1), positions: 0 }
    }

    /// `CatchUp.value`: the outcome for player 1 under optimal play.
    pub fn value(&mut self) -> Outcome {
        self.openings().into_iter().map(|(_, o)| o).max().unwrap_or(Outcome::Draw)
    }

    /// Player 1's outcome after each possible opening pick.
    pub fn openings(&mut self) -> Vec<(u64, Outcome)> {
        let full = (1usize << self.numbers.len()) - 1;
        let total: u64 = self.numbers.iter().sum();
        (0..self.numbers.len())
            .map(|i| {
                let x = self.numbers[i];
                // The first move is exactly one pick, then the turn passes.
                (x, self.aux(full & !(1 << i), total - x, -(x as i64)).neg())
            })
            .collect()
    }

    /// The mover's value in a non-opening position: `mask` = numbers left, trailing by `gap`.
    pub fn position(&mut self, mask: usize, gap: u64) -> Outcome {
        let sum = (0..self.numbers.len()).filter(|&i| mask >> i & 1 == 1).map(|i| self.numbers[i]).sum();
        self.aux(mask, sum, -(gap as i64))
    }

    /// `valueAux` for a non-first move: `mask` = numbers left, `diff` = mover's score minus opponent's.
    fn aux(&mut self, mask: usize, remaining_sum: u64, diff: i64) -> Outcome {
        if mask == 0 {
            return Outcome::of_diff(diff);
        }
        if diff + (remaining_sum as i64) < 0 {
            return Outcome::Loss; // cannot catch up even by taking everything
        }
        let gap = (-diff) as usize;
        // Play keeps gap ≤ max; only `position` asks for more, and those gaps have no slot.
        let memo = gap < self.table.stride;
        if memo && let Some(o) = self.table.get(mask, gap) {
            return o;
        }
        self.positions += 1;
        let mut best = Outcome::Loss;
        let mut rest = mask;
        while rest != 0 && best != Outcome::Win {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            let d = diff + x as i64;
            let o = if d >= 0 {
                self.aux(next, remaining_sum - x, -d).neg() // caught up: turn passes
            } else {
                self.aux(next, remaining_sum - x, d) // still behind: keep picking
            };
            best = best.max(o);
        }
        if memo {
            self.table.set(mask, gap, best);
        }
        best
    }
}

/// Independent check: enumerates whole turns exactly as the paper states the rules.
/// Exponential time, small sets only.
pub fn reference_value(numbers: &[u64]) -> Outcome {
    (0..numbers.len())
        .map(|i| ref_turn(&without(numbers, i), 0, numbers[i]).neg())
        .max()
        .unwrap_or(Outcome::Draw)
}

/// Start of a normal turn: the mover has `me` points, the opponent `opp` ≥ `me`.
fn ref_turn(remaining: &[u64], me: u64, opp: u64) -> Outcome {
    if remaining.is_empty() {
        return Outcome::of_diff(me as i64 - opp as i64);
    }
    if me + remaining.iter().sum::<u64>() < opp {
        return Outcome::Loss; // takes everything and still trails
    }
    let mut best = Outcome::Loss;
    ref_picks(remaining, me, opp, &mut best);
    best
}

/// Within a turn: keep picking while strictly behind; the turn ends on the pick that catches up.
fn ref_picks(remaining: &[u64], me: u64, opp: u64, best: &mut Outcome) {
    for i in 0..remaining.len() {
        let rest = without(remaining, i);
        let me = me + remaining[i];
        if me >= opp {
            *best = (*best).max(ref_turn(&rest, opp, me).neg());
        } else {
            ref_picks(&rest, me, opp, best);
        }
    }
}

fn without(xs: &[u64], i: usize) -> Vec<u64> {
    xs.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, &x)| x).collect()
}

/// The set {1, ..., n}.
pub fn interval(n: u64) -> Vec<u64> {
    (1..=n).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// OEIS A278587, n = 3..20: 1 = player 1 wins, -1 = player 2 wins, 0 = draw.
    const A278587: [i8; 18] = [0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0];
    const A278587_OFFSET: u64 = 3;
    const REFERENCE_UNIVERSE: u64 = 8;

    fn oeis_code(o: Outcome) -> i8 {
        o as i8 - 1
    }

    #[test]
    fn matches_reference_on_all_small_subsets() {
        for bits in 0u32..(1 << REFERENCE_UNIVERSE) {
            let set: Vec<u64> = (1..=REFERENCE_UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            assert_eq!(Solver::new(&set).value(), reference_value(&set), "set {set:?}");
        }
    }

    #[test]
    fn matches_oeis_a278587() {
        for (k, &expected) in A278587.iter().enumerate() {
            let n = A278587_OFFSET + k as u64;
            assert_eq!(oeis_code(Solver::new(&interval(n)).value()), expected, "n = {n}");
        }
    }

    #[test]
    fn position_beyond_largest_number() {
        // A solver that also holds BIG has a memo slot for every gap below it; it is the reference.
        const UNIVERSE: u64 = 6;
        const BIG: u64 = 100;
        for bits in 1u32..(1 << UNIVERSE) {
            let set: Vec<u64> = (1..=UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            let full = (1usize << set.len()) - 1;
            let sum: u64 = set.iter().sum();
            let mut wide = Solver::new(&[set.as_slice(), &[BIG]].concat());
            let mut s = Solver::new(&set);
            for gap in (0..=sum + 1).rev() {
                assert_eq!(s.position(full, gap), wide.position(full, gap), "set {set:?} gap {gap}");
            }
        }
    }

    #[test]
    fn lean_example_line_is_a_draw() {
        // The Lean file's example play on {1,2,3,4} ends 5-5; optimal play is also a draw.
        assert_eq!(Solver::new(&interval(4)).value(), Outcome::Draw);
    }
}
