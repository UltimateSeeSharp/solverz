//! Tiled layered solver. Each layer is split into tiles by which of the `top` highest positions are
//! still left (the top pattern T); rows within a tile are ordered by the colex rank of the remaining
//! low positions. Tile (k, T) needs only tiles T and T − b of layer k − 1, and removing a top number
//! keeps the row index, so a tile's inputs move in a few large blocks (to a GPU or from disk).
//! This engine keeps whole layers in RAM; it fixes the layout the GPU and out-of-core engines reuse.

use crate::layered::{
    binomials, decode, evaluate_row, neg, next_combination, pred_ranks, rank, row_cell, unrank, words_per_row,
    MAX_NUMBERS,
};
use crate::Outcome;
use rayon::prelude::*;

const ROWS_PER_TASK: usize = 1 << 14;

pub struct Tiled {
    pub(crate) numbers: Vec<u64>,
    pub(crate) top: usize,
    pub(crate) low: usize,
    pub(crate) max_gap: usize,
    pub(crate) words: usize,
    binom: Vec<Vec<u64>>,
}

/// Start row of every tile of one layer, indexed by top pattern (bit i = position `low + i`).
pub struct Layout {
    pub(crate) offsets: Vec<Option<usize>>,
    pub(crate) rows: usize,
}

impl Tiled {
    /// `top` = how many of the highest positions define the tiles (0 = one tile per layer).
    pub fn new(numbers: &[u64], top: usize) -> Self {
        assert!(numbers.len() <= MAX_NUMBERS, "at most {MAX_NUMBERS} numbers");
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        assert!(top <= numbers.len(), "top must be at most the number count");
        let max_gap = numbers.iter().copied().max().unwrap_or(0) as usize;
        Tiled {
            numbers: numbers.to_vec(),
            top,
            low: numbers.len() - top,
            max_gap,
            words: words_per_row(max_gap),
            binom: binomials(),
        }
    }

    pub fn n(&self) -> usize {
        self.numbers.len()
    }

    /// Rows of tile (k, T) with |T| = t: low masks with k − t bits.
    pub(crate) fn tile_rows(&self, k: usize, t: usize) -> usize {
        if t > k || k - t > self.low { 0 } else { self.binom[self.low][k - t] as usize }
    }

    pub fn layout(&self, k: usize) -> Layout {
        let mut offsets = vec![None; 1 << self.top];
        let mut rows = 0;
        for (pattern, offset) in offsets.iter_mut().enumerate() {
            let tile = self.tile_rows(k, pattern.count_ones() as usize);
            if tile > 0 {
                *offset = Some(rows);
                rows += tile;
            }
        }
        Layout { offsets, rows }
    }

    /// Row index of `mask` within its layer.
    pub fn locate(&self, layout: &Layout, mask: u64) -> usize {
        let low_mask = mask & ((1u64 << self.low) - 1);
        layout.offsets[(mask >> self.low) as usize].expect("tile exists") + rank(&self.binom, low_mask)
    }

    pub(crate) fn row<'a>(&self, layer: &'a [u32], row: usize) -> &'a [u32] {
        &layer[row * self.words..][..self.words]
    }

    pub fn get(&self, layer: &[u32], row: usize, gap: usize) -> Outcome {
        decode(row_cell(self.row(layer, row), gap))
    }

    /// Computes layers 0..=n−1, calling `on_layer` after each; returns layer n − 1 and its layout.
    pub fn run(&self, mut on_layer: impl FnMut(usize, &Layout, &[u32])) -> (Layout, Vec<u32>) {
        let mut prev_layout = Layout { offsets: Vec::new(), rows: 0 };
        let mut prev: Vec<u32> = Vec::new();
        for k in 0..self.n() {
            let layout = self.layout(k);
            let mut cur = vec![0u32; layout.rows * self.words];
            let mut tiles: Vec<(usize, &mut [u32])> = Vec::new();
            let mut rest: &mut [u32] = &mut cur;
            for (pattern, offset) in layout.offsets.iter().enumerate() {
                if offset.is_some() {
                    let len = self.tile_rows(k, pattern.count_ones() as usize) * self.words;
                    let (tile, tail) = std::mem::take(&mut rest).split_at_mut(len);
                    tiles.push((pattern, tile));
                    rest = tail;
                }
            }
            tiles.into_par_iter().for_each(|(pattern, out)| self.fill_tile(k, pattern, &prev_layout, &prev, out));
            on_layer(k, &layout, &cur);
            prev = cur;
            prev_layout = layout;
        }
        (prev_layout, prev)
    }

    /// Tile (k, pattern) from layer k − 1: a low move reads tile `pattern` at the reduced low rank,
    /// a top move reads tile `pattern − b` at the same row.
    fn fill_tile(&self, k: usize, pattern: usize, prev_layout: &Layout, prev: &[u32], out: &mut [u32]) {
        let t = pattern.count_ones() as usize;
        let m = k - t;
        let same = if m > 0 { prev_layout.offsets[pattern] } else { None };
        let mut top_takes = [0usize; MAX_NUMBERS];
        let mut top_offsets = [0usize; MAX_NUMBERS];
        let mut p = pattern;
        for q in 0..t {
            let b = p.trailing_zeros() as usize;
            p &= p - 1;
            top_takes[q] = self.numbers[self.low + b] as usize;
            top_offsets[q] = prev_layout.offsets[pattern & !(1 << b)].expect("tile T − b exists");
        }
        out.par_chunks_mut(ROWS_PER_TASK * self.words).enumerate().for_each(|(c, chunk)| {
            let start = c * ROWS_PER_TASK;
            let mut low_mask = unrank(&self.binom, start as u64, m);
            for (i, row) in chunk.chunks_mut(self.words).enumerate() {
                let r = start + i;
                let mut pos = [0usize; MAX_NUMBERS];
                let mut lm = low_mask;
                for slot in pos.iter_mut().take(m) {
                    *slot = lm.trailing_zeros() as usize;
                    lm &= lm - 1;
                }
                let pred = pred_ranks(&pos[..m], &self.binom);
                let mut takes = [0usize; MAX_NUMBERS];
                let mut preds: [&[u32]; MAX_NUMBERS] = [&[]; MAX_NUMBERS];
                for j in 0..m {
                    takes[j] = self.numbers[pos[j]] as usize;
                    preds[j] = self.row(prev, same.expect("tile T exists") + pred[j]);
                }
                for q in 0..t {
                    takes[m + q] = top_takes[q];
                    preds[m + q] = self.row(prev, top_offsets[q] + r);
                }
                evaluate_row(&takes[..k], &preds[..k], self.max_gap, row);
                low_mask = next_combination(low_mask);
            }
        });
    }

    /// Player 1's outcome after each possible opening pick.
    pub fn openings(&self) -> Vec<(u64, Outcome)> {
        let n = self.n();
        if n == 0 {
            return Vec::new();
        }
        let (layout, last) = self.run(|_, _, _| {});
        self.openings_from(&layout, &last)
    }

    /// Openings read from layer n − 1.
    pub(crate) fn openings_from(&self, layout: &Layout, last: &[u32]) -> Vec<(u64, Outcome)> {
        let n = self.n();
        let full = (1u64 << n) - 1;
        (0..n)
            .map(|i| {
                // After the opening the opponent moves, trailing by the number taken.
                let x = self.numbers[i];
                let row = self.row(last, self.locate(layout, full & !(1 << i)));
                (x, decode(neg(row_cell(row, x as usize))))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval;
    use crate::layered::Layered;

    const FULL_TABLE_MAX_N: u64 = 10;
    const OPENINGS_MAX_N: u64 = 16;
    const SUBSET_UNIVERSE: u64 = 8;

    #[test]
    fn every_position_matches_layered() {
        for n in 0..=FULL_TABLE_MAX_N {
            let numbers = interval(n);
            let layered = Layered::new(&numbers);
            let mut reference: Vec<Vec<u32>> = Vec::new();
            layered.run(|_, layer| reference.push(layer.to_vec()));
            for top in 0..=n as usize {
                let tiled = Tiled::new(&numbers, top);
                tiled.run(|k, layout, layer| {
                    for mask in (0u64..1 << n).filter(|m| m.count_ones() as usize == k) {
                        for g in 0..=n as usize {
                            assert_eq!(
                                tiled.get(layer, tiled.locate(layout, mask), g),
                                layered.get(&reference[k], layered.rank(mask), g),
                                "n {n} top {top} mask {mask:b} gap {g}"
                            );
                        }
                    }
                });
            }
        }
    }

    #[test]
    fn openings_match_layered() {
        for n in 0..=OPENINGS_MAX_N {
            let expected = Layered::new(&interval(n)).openings();
            for top in [0, 1, n as usize / 2, n as usize].into_iter().filter(|&t| t <= n as usize) {
                assert_eq!(Tiled::new(&interval(n), top).openings(), expected, "n {n} top {top}");
            }
        }
        for bits in 0u32..(1 << SUBSET_UNIVERSE) {
            let set: Vec<u64> = (1..=SUBSET_UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            let expected = Layered::new(&set).openings();
            for top in 0..=set.len() {
                assert_eq!(Tiled::new(&set, top).openings(), expected, "set {set:?} top {top}");
            }
        }
    }
}
