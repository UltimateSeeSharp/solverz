//! Layered (retrograde) solver. Every move removes one number, so positions with k numbers left
//! depend only on positions with k − 1 left: layers are computed in order, each in parallel, with
//! two layers in memory. Same recurrence as `Solver::aux`, written over the gap g = s_opp − s_me ≥ 0.
//!
//! Layer k stores one row per mask with k bits, ordered by colex rank (the combinatorial number
//! system); a row holds 2 bits per gap 0..=max.

use crate::Outcome;
use rayon::prelude::*;

const LOSS: u32 = 0;
const DRAW: u32 = 1;
const WIN: u32 = 2;
const BITS_PER_GAP: usize = 2;
const GAPS_PER_WORD: usize = 32 / BITS_PER_GAP;
const GAP_MASK: u32 = 0b11;
const MASKS_PER_TASK: usize = 1 << 14;
pub const MAX_NUMBERS: usize = 32;

/// Outcome seen by the other player: win ↔ loss.
fn neg(v: u32) -> u32 {
    WIN - v
}

fn decode(v: u32) -> Outcome {
    match v {
        LOSS => Outcome::Loss,
        DRAW => Outcome::Draw,
        _ => Outcome::Win,
    }
}

pub struct Layered {
    numbers: Vec<u64>,
    max_gap: usize,
    words_per_row: usize,
    /// binom[p][i] = C(p, i)
    binom: Vec<Vec<u64>>,
}

impl Layered {
    pub fn new(numbers: &[u64]) -> Self {
        assert!(numbers.len() <= MAX_NUMBERS, "at most {MAX_NUMBERS} numbers");
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        let max_gap = numbers.iter().copied().max().unwrap_or(0) as usize;
        let mut binom = vec![vec![0u64; MAX_NUMBERS + 2]; MAX_NUMBERS + 1];
        for p in 0..=MAX_NUMBERS {
            binom[p][0] = 1;
            for i in 1..=p {
                binom[p][i] = binom[p - 1][i - 1] + binom[p - 1][i];
            }
        }
        Layered {
            numbers: numbers.to_vec(),
            max_gap,
            words_per_row: (max_gap + 1).div_ceil(GAPS_PER_WORD),
            binom,
        }
    }

    pub fn n(&self) -> usize {
        self.numbers.len()
    }

    /// Masks with k bits.
    pub fn layer_len(&self, k: usize) -> usize {
        self.binom[self.n()][k] as usize
    }

    /// Colex rank of a mask among masks with the same number of bits.
    pub fn rank(&self, mask: u64) -> usize {
        let (mut r, mut m, mut i) = (0u64, mask, 1);
        while m != 0 {
            r += self.binom[m.trailing_zeros() as usize][i];
            m &= m - 1;
            i += 1;
        }
        r as usize
    }

    /// Inverse of `rank` for masks with k bits.
    fn unrank(&self, mut r: u64, k: usize) -> u64 {
        let mut mask = 0u64;
        for i in (1..=k).rev() {
            let mut p = i - 1;
            while self.binom[p + 1][i] <= r {
                p += 1;
            }
            mask |= 1 << p;
            r -= self.binom[p][i];
        }
        mask
    }

    pub fn get(&self, layer: &[u32], rank: usize, gap: usize) -> Outcome {
        decode(self.cell(layer, rank, gap))
    }

    fn cell(&self, layer: &[u32], rank: usize, gap: usize) -> u32 {
        let word = layer[rank * self.words_per_row + gap / GAPS_PER_WORD];
        (word >> (BITS_PER_GAP * (gap % GAPS_PER_WORD))) & GAP_MASK
    }

    /// Computes layers 0..=n−1, calling `on_layer(k, layer)` after each; returns layer n − 1.
    pub fn run(&self, mut on_layer: impl FnMut(usize, &[u32])) -> Vec<u32> {
        let mut prev: Vec<u32> = Vec::new();
        for k in 0..self.n() {
            let mut cur = vec![0u32; self.layer_len(k) * self.words_per_row];
            cur.par_chunks_mut(MASKS_PER_TASK * self.words_per_row).enumerate().for_each(|(t, out)| {
                let mut mask = self.unrank((t * MASKS_PER_TASK) as u64, k);
                for row in out.chunks_mut(self.words_per_row) {
                    self.fill_row(mask, k, &prev, row);
                    mask = next_combination(mask);
                }
            });
            on_layer(k, &cur);
            prev = cur;
        }
        prev
    }

    /// Player 1's outcome after each possible opening pick.
    pub fn openings(&self) -> Vec<(u64, Outcome)> {
        let n = self.n();
        if n == 0 {
            return Vec::new();
        }
        let last = self.run(|_, _| {});
        let full = (1u64 << n) - 1;
        (0..n)
            .map(|i| {
                // After the opening the opponent moves, trailing by the number taken.
                let x = self.numbers[i];
                (x, decode(neg(self.cell(&last, self.rank(full & !(1 << i)), x as usize))))
            })
            .collect()
    }

    pub fn value(&self) -> Outcome {
        self.openings().into_iter().map(|(_, o)| o).max().unwrap_or(Outcome::Draw)
    }

    /// Row of `mask` (k bits): the mover's value for every gap, from the rows of layer k − 1.
    fn fill_row(&self, mask: u64, k: usize, prev: &[u32], row: &mut [u32]) {
        let mut pos = [0usize; MAX_NUMBERS];
        let mut m = mask;
        for p in pos.iter_mut().take(k) {
            *p = m.trailing_zeros() as usize;
            m &= m - 1;
        }
        let sum: u64 = pos[..k].iter().map(|&p| self.numbers[p]).sum();
        // Removing the j-th set bit: bits below keep their index, bits above drop by one.
        let mut pred = [0usize; MAX_NUMBERS];
        let mut below = 0u64;
        let mut above: u64 = (1..k).map(|i| self.binom[pos[i]][i]).sum();
        for j in 0..k {
            pred[j] = (below + above) as usize;
            below += self.binom[pos[j]][j + 1];
            if j + 1 < k {
                above -= self.binom[pos[j + 1]][j + 1];
            }
        }
        for g in 0..=self.max_gap {
            let v = if (sum as usize) < g {
                LOSS // cannot catch up even by taking everything
            } else if k == 0 {
                DRAW // no numbers left, scores level
            } else {
                let mut best = LOSS;
                for j in 0..k {
                    let x = self.numbers[pos[j]] as usize;
                    let o = if x >= g {
                        neg(self.cell(prev, pred[j], x - g)) // caught up: opponent trails by x − g
                    } else {
                        self.cell(prev, pred[j], g - x) // still behind: same mover
                    };
                    best = best.max(o);
                    if best == WIN {
                        break;
                    }
                }
                best
            };
            row[g / GAPS_PER_WORD] |= v << (BITS_PER_GAP * (g % GAPS_PER_WORD));
        }
    }
}

/// Next larger mask with the same number of bits (Gosper's hack); colex order.
fn next_combination(mask: u64) -> u64 {
    if mask == 0 {
        return 0;
    }
    let t = mask | (mask - 1);
    (t + 1) | (((!t & (t + 1)) - 1) >> (mask.trailing_zeros() + 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{interval, Solver};

    const FULL_TABLE_MAX_N: u64 = 10;
    const OPENINGS_MAX_N: u64 = 18;
    const SUBSET_UNIVERSE: u64 = 8;

    #[test]
    fn rank_inverts_unrank() {
        let l = Layered::new(&interval(12));
        for k in 0..=12 {
            for r in 0..l.layer_len(k) {
                let mask = l.unrank(r as u64, k);
                assert_eq!(mask.count_ones() as usize, k);
                assert_eq!(l.rank(mask), r);
            }
        }
    }

    #[test]
    fn every_position_matches_dfs() {
        for n in 0..=FULL_TABLE_MAX_N {
            let numbers = interval(n);
            let layered = Layered::new(&numbers);
            let mut dfs = Solver::new(&numbers);
            layered.run(|k, layer| {
                for r in 0..layered.layer_len(k) {
                    let mask = layered.unrank(r as u64, k);
                    for g in 0..=layered.max_gap {
                        assert_eq!(layered.get(layer, r, g), dfs.position(mask as usize, g as u64), "n {n} mask {mask:b} gap {g}");
                    }
                }
            });
        }
    }

    #[test]
    fn openings_match_dfs() {
        for n in 0..=OPENINGS_MAX_N {
            assert_eq!(Layered::new(&interval(n)).openings(), Solver::new(&interval(n)).openings(), "n {n}");
        }
        for bits in 0u32..(1 << SUBSET_UNIVERSE) {
            let set: Vec<u64> = (1..=SUBSET_UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            assert_eq!(Layered::new(&set).openings(), Solver::new(&set).openings(), "set {set:?}");
        }
    }
}
