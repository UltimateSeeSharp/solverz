//! Catch-Up over a real height (C32's parameter): the numbers h + o for given integer offsets o, the mover trailing by
//! k·h + c, valued as an exact piecewise-constant function of h on (0, ∞). Every comparison is linear in h and resolved
//! symbolically, so the result is exact, not sampled. Margin-game semantics (C33): the sign of the minimax margin.
//! Port of the refuter's `scratch/refuter/tir/param.rs` (C32, 2026-10-26); the tests check it against `Solver`.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

/// A positive-denominator rational.
#[derive(Clone, Copy, Debug)]
pub struct Q {
    pub n: i64,
    pub d: i64,
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

impl Q {
    pub fn new(n: i64, d: i64) -> Q {
        let (n, d) = if d < 0 { (-n, -d) } else { (n, d) };
        let g = gcd(n, d).max(1);
        Q { n: n / g, d: d / g }
    }

    fn cmp(&self, o: &Q) -> Ordering {
        ((self.n as i128) * (o.d as i128)).cmp(&((o.n as i128) * (self.d as i128)))
    }

    fn mid(&self, o: &Q) -> Q {
        Q::new(self.n * o.d + o.n * self.d, 2 * self.d * o.d)
    }
}

impl PartialEq for Q {
    fn eq(&self, o: &Q) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}

const LOSS: i8 = -1;
const SYMBOLS: [char; 3] = ['L', 'D', 'W'];

/// Values −1 (loss), 0 (draw), 1 (win), piecewise constant on (0, ∞): breakpoints `bps` ascending, `open[i]` on the
/// open interval before `bps[i]` (the last one after the last breakpoint), `at[i]` at `bps[i]`.
#[derive(Clone, Debug)]
pub struct Piecewise {
    pub bps: Vec<Q>,
    pub open: Vec<i8>,
    pub at: Vec<i8>,
}

impl Piecewise {
    pub fn value_at(&self, x: &Q) -> i8 {
        let (mut lo, mut hi) = (0usize, self.bps.len());
        while lo < hi {
            let m = (lo + hi) / 2;
            match self.bps[m].cmp(x) {
                Ordering::Less => lo = m + 1,
                Ordering::Equal => return self.at[m],
                Ordering::Greater => hi = m,
            }
        }
        self.open[lo]
    }

    /// Every value taken on (0, ∞), sorted.
    pub fn values(&self) -> Vec<i8> {
        let mut v: Vec<i8> = self.open.iter().chain(self.at.iter()).copied().collect();
        v.sort_unstable();
        v.dedup();
        v
    }

    fn simplify(mut self) -> Piecewise {
        let (mut bps, mut open, mut at) = (vec![], vec![self.open[0]], vec![]);
        for i in 0..self.bps.len() {
            let left = *open.last().unwrap();
            if self.at[i] == left && self.open[i + 1] == left {
                continue;
            }
            bps.push(self.bps[i]);
            at.push(self.at[i]);
            open.push(self.open[i + 1]);
        }
        self.bps = bps;
        self.open = open;
        self.at = at;
        self
    }

    /// Readable form, e.g. `(0,1/1):W [1/1]:D (1/1,inf):D`.
    pub fn show(&self) -> String {
        let c = |v: i8| SYMBOLS[(v - LOSS) as usize];
        let mut s = "(0,".to_string();
        for i in 0..self.bps.len() {
            let b = &self.bps[i];
            s += &format!("{}/{}):{} [{}/{}]:{} ({}/{},", b.n, b.d, c(self.open[i]), b.n, b.d, c(self.at[i]), b.n, b.d);
        }
        s + &format!("inf):{}", c(self.open[self.bps.len()]))
    }
}

/// Pointwise combination of several functions, with extra breakpoints.
fn combine(fs: &[&Piecewise], extra: &[Q], f: &dyn Fn(&Q, &[i8]) -> i8) -> Piecewise {
    let mut bps: Vec<Q> = extra.iter().filter(|q| q.n > 0).cloned().collect();
    for g in fs {
        bps.extend(g.bps.iter().cloned());
    }
    bps.sort_by(|a, b| a.cmp(b));
    bps.dedup_by(|a, b| a == b);
    let eval = |x: &Q| -> i8 {
        let vals: Vec<i8> = fs.iter().map(|g| g.value_at(x)).collect();
        f(x, &vals)
    };
    let reps: Vec<Q> = if bps.is_empty() {
        vec![Q::new(1, 1)]
    } else {
        let mut r = vec![Q::new(bps[0].n, 2 * bps[0].d)];
        for i in 1..bps.len() {
            r.push(bps[i - 1].mid(&bps[i]));
        }
        let last = bps[bps.len() - 1];
        r.push(Q::new(last.n + last.d, last.d));
        r
    };
    let open = reps.iter().map(eval).collect();
    let at = bps.iter().map(eval).collect();
    Piecewise { bps, open, at }.simplify()
}

/// Sign of a·x + b.
fn sign_linear(a: i64, b: i64, x: &Q) -> i8 {
    ((a as i128) * (x.n as i128) + (b as i128) * (x.d as i128)).signum() as i8
}

/// Exact values over the height, memoized over (offsets left, deficit k·h + c).
pub struct Param {
    offsets: Vec<i64>,
    memo: HashMap<(u32, i32, i64), Rc<Piecewise>>,
}

impl Param {
    pub fn new(offsets: &[i64]) -> Self {
        assert!(offsets.len() < 32, "fewer than 32 offsets");
        Param { offsets: offsets.to_vec(), memo: HashMap::new() }
    }

    /// The mover's value with the offsets in `left` remaining, trailing by k·h + c.
    pub fn value(&mut self, left: u32, k: i32, c: i64) -> Rc<Piecewise> {
        if let Some(r) = self.memo.get(&(left, k, c)) {
            return r.clone();
        }
        let res = if left == 0 {
            let extra = if k != 0 { vec![Q::new(-c, k as i64)] } else { vec![] };
            combine(&[], &extra, &|x, _| -sign_linear(k as i64, c, x))
        } else {
            let mut acc: Option<Piecewise> = None;
            let mut bits = left;
            while bits != 0 {
                let b = bits.trailing_zeros();
                bits &= bits - 1;
                let o = self.offsets[b as usize];
                let rest = left & !(1 << b);
                // The pick h + o catches up iff (h + o) − (k·h + c) = (1 − k)·h + (o − c) ≥ 0.
                let (a1, b1) = ((1 - k) as i64, o - c);
                let end = self.value(rest, 1 - k, o - c);
                let cont = self.value(rest, k - 1, c - o);
                let extra = if a1 != 0 { vec![Q::new(-b1, a1)] } else { vec![] };
                let child =
                    combine(&[&end, &cont], &extra, &|x, v| if sign_linear(a1, b1, x) >= 0 { -v[0] } else { v[1] });
                acc = Some(match acc {
                    None => child,
                    Some(a) => combine(&[&a, &child], &[], &|_, v| v[0].max(v[1])),
                });
            }
            acc.unwrap()
        };
        let r = Rc::new(res);
        self.memo.insert((left, k, c), r.clone());
        r
    }

    /// The tied mover's value with every offset left.
    pub fn tied(&mut self) -> Rc<Piecewise> {
        self.value((1u32 << self.offsets.len()) - 1, 0, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::{Param, Q};
    use crate::{Outcome, Solver};

    fn outcome(v: i8) -> Outcome {
        [Outcome::Loss, Outcome::Draw, Outcome::Win][(v + 1) as usize]
    }

    /// At h = r/q the game on the numbers h + o is the integer game on r + q·o (scaling), so `Solver` must agree.
    #[test]
    fn agrees_with_solver_at_rational_heights() {
        for mask in 1u32..1 << 7 {
            let offs: Vec<i64> = (0..7).filter(|&i| mask >> i & 1 == 1).collect();
            let f = Param::new(&offs).tied();
            for (r, q) in [(1, 1), (2, 1), (3, 1), (1, 2), (3, 2), (5, 3), (7, 4)] {
                let nums: Vec<u64> = offs.iter().map(|&o| (r + q * o) as u64).collect();
                let s = Solver::new(&nums).position((1 << nums.len()) - 1, 0);
                assert_eq!(outcome(f.value_at(&Q::new(r, q))), s, "offsets {offs:?} at h = {r}/{q}");
            }
        }
    }

    /// C32 at p = 1: {h, h + 1}, the mover trailing by 1, wins below h = 1 and draws from there.
    #[test]
    fn c32_pair() {
        let f = Param::new(&[0, 1]).value(0b11, 0, 1);
        assert_eq!(f.show(), "(0,1/1):W [1/1]:D (1/1,inf):D");
    }
}
