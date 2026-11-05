//! Simulated annealing on `violations`: a move recolours one pair, and only
//! the triangles and 4-point sets through that pair are rescored.

use crate::{COLOURS, Colouring, K4E_EDGES, K4E_FREE, TRIANGLE_FREE};

/// xorshift64*: a small deterministic generator, so runs repeat from their seed.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// Uniform in [0, 1).
    pub fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// Violations among the triangles and 4-point sets that contain both i and j.
pub fn violations_through(c: &Colouring, i: usize, j: usize) -> usize {
    let n = c.n();
    let mut count = 0;
    for k in 0..n {
        if k == i || k == j {
            continue;
        }
        if c.get(i, j) == TRIANGLE_FREE && c.get(i, k) == TRIANGLE_FREE && c.get(j, k) == TRIANGLE_FREE {
            count += 1;
        }
        for l in k + 1..n {
            if l == i || l == j {
                continue;
            }
            let pairs = [c.get(i, j), c.get(i, k), c.get(i, l), c.get(j, k), c.get(j, l), c.get(k, l)];
            for colour in K4E_FREE {
                if pairs.iter().filter(|&&x| x == colour).count() >= K4E_EDGES {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Annealing schedule and budget.
#[derive(Clone, Copy)]
pub struct Schedule {
    /// Temperature at the start and end of each restart, in violations.
    pub t_start: f64,
    pub t_end: f64,
    /// Moves per restart.
    pub moves: u64,
    /// Restarts before giving up.
    pub restarts: u64,
}

/// The best colouring found and its violation count; stops at 0.
pub struct Outcome {
    pub best: Colouring,
    pub best_score: usize,
    pub moves: u64,
}

/// Anneals from random colourings of Kₙ; `on_restart` sees each restart's best score.
pub fn anneal(n: usize, schedule: &Schedule, rng: &mut Rng, on_restart: &mut dyn FnMut(usize)) -> Outcome {
    let pairs: Vec<(usize, usize)> = (0..n).flat_map(|i| (i + 1..n).map(move |j| (i, j))).collect();
    let mut best: Option<(Colouring, usize)> = None;
    let mut moves = 0;
    for _ in 0..schedule.restarts {
        let mut c = Colouring::new(n);
        for &(i, j) in &pairs {
            c.set(i, j, rng.below(COLOURS as usize) as u8);
        }
        let mut score = crate::violations(&c);
        let mut restart_best = score;
        let cooling = (schedule.t_end / schedule.t_start).powf(1.0 / schedule.moves as f64);
        let mut t = schedule.t_start;
        for _ in 0..schedule.moves {
            moves += 1;
            let (i, j) = pairs[rng.below(pairs.len())];
            let old = c.get(i, j);
            let new = (old + 1 + rng.below(COLOURS as usize - 1) as u8) % COLOURS;
            let before = violations_through(&c, i, j);
            c.set(i, j, new);
            let after = violations_through(&c, i, j);
            let delta = after as f64 - before as f64;
            if delta <= 0.0 || rng.unit() < (-delta / t).exp() {
                score = score + after - before;
                if score < restart_best {
                    restart_best = score;
                }
                if best.as_ref().is_none_or(|(_, s)| score < *s) {
                    best = Some((c.clone(), score));
                }
                if score == 0 {
                    on_restart(0);
                    let (best, best_score) = best.expect("set above");
                    return Outcome { best, best_score, moves };
                }
            } else {
                c.set(i, j, old);
            }
            t *= cooling;
        }
        on_restart(restart_best);
    }
    let (best, best_score) = best.expect("at least one restart");
    Outcome { best, best_score, moves }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::violations;

    #[test]
    fn incremental_score_matches_full_recount() {
        let mut rng = Rng::new(7);
        let n = 12;
        let mut c = Colouring::new(n);
        for i in 0..n {
            for j in i + 1..n {
                c.set(i, j, rng.below(3) as u8);
            }
        }
        let mut score = violations(&c);
        for _ in 0..2000 {
            let (i, j) = loop {
                let (a, b) = (rng.below(n), rng.below(n));
                if a != b {
                    break (a, b);
                }
            };
            let before = violations_through(&c, i, j);
            c.set(i, j, rng.below(3) as u8);
            score = score + violations_through(&c, i, j) - before;
            assert_eq!(score, violations(&c));
        }
    }
}
