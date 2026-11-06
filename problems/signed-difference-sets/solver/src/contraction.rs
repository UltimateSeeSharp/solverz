//! Contraction (F3): an SDS (v, k, λ) on G pushed to a quotient H of order n gives integer
//! coset sums a on H with |a_h| ≤ c = v/n, Σ a_h² = k + λ(c − 1), Σ_h a_h a_{h+g} = λc for
//! g ≠ 0, and (so) Σ a_h = ±s. No such vector: no SDS.

use crate::Group;

/// A quotient ∏ ℤ_{dᵢ} of ∏ ℤ_{mᵢ}, dᵢ | mᵢ (the map Lean's `Proj` builds), and its
/// invariant factors.
pub struct Quotient {
    pub divisors: Vec<usize>,
    pub invariants: Vec<usize>,
}

/// The quotients ∏ ℤ_{dᵢ} of ∏ ℤ_{mᵢ}, dᵢ | mᵢ, one per isomorphism type (the first divisor
/// tuple found), H ≠ G, H ≠ 1, smallest first.
pub fn quotients(shape: &[usize]) -> Vec<Quotient> {
    let mut out: Vec<Quotient> = Vec::new();
    let mut d = vec![1; shape.len()];
    loop {
        let order: usize = d.iter().product();
        if order > 1 && order < shape.iter().product() {
            let inv = invariant_factors(&d);
            if !out.iter().any(|q| q.invariants == inv) {
                out.push(Quotient { divisors: d.clone(), invariants: inv });
            }
        }
        // Next divisor tuple.
        let mut i = 0;
        loop {
            if i == shape.len() {
                out.sort_by_key(|q| q.divisors.iter().product::<usize>());
                return out;
            }
            d[i] += 1;
            while d[i] <= shape[i] && shape[i] % d[i] != 0 {
                d[i] += 1;
            }
            if d[i] <= shape[i] {
                break;
            }
            d[i] = 1;
            i += 1;
        }
    }
}

/// Invariant factors d₁ | d₂ | … of ∏ ℤ_{nᵢ}, trivial factors dropped.
pub fn invariant_factors(ns: &[usize]) -> Vec<usize> {
    // Prime powers per prime, then combine largest with largest.
    let mut powers: Vec<(usize, Vec<usize>)> = Vec::new();
    for &n in ns {
        let mut n = n;
        let mut p = 2;
        while n > 1 {
            if n % p == 0 {
                let mut q = 1;
                while n % p == 0 {
                    n /= p;
                    q *= p;
                }
                match powers.iter_mut().find(|(r, _)| *r == p) {
                    Some((_, v)) => v.push(q),
                    None => powers.push((p, vec![q])),
                }
            }
            p += 1;
        }
    }
    let len = powers.iter().map(|(_, v)| v.len()).max().unwrap_or(0);
    let mut inv = vec![1; len];
    for (_, v) in powers.iter_mut() {
        v.sort_unstable_by(|a, b| b.cmp(a));
        for (i, q) in v.iter().enumerate() {
            inv[len - 1 - i] *= q;
        }
    }
    inv
}

/// What contraction to `h` demands: fibre size c, square sum, off-zero autocorrelation, sum.
pub struct Demand {
    pub c: i64,
    pub square: i64,
    pub target: i64,
    pub sum: i64,
}

impl Demand {
    pub fn new(v: usize, k: usize, lam: i64, h_order: usize) -> Option<Demand> {
        let c = (v / h_order) as i64;
        let total = k as i64 + lam * (v as i64 - 1);
        let s = (total as f64).sqrt().round() as i64;
        if s * s != total {
            return None;
        }
        Some(Demand { c, square: k as i64 + lam * (c - 1), target: lam * c, sum: s })
    }
}

/// Outcome of one vector search.
pub struct VectorSearch {
    /// A vector meeting every demand, if found.
    pub found: Option<Vec<i64>>,
    pub nodes: u64,
    /// The node cap was hit before the search finished.
    pub cut: bool,
}

/// Exact search for a vector on `h` meeting `dem`, Σ|a| ≤ k with k − Σ|a| even, a₀ of the
/// largest absolute value (translation), Σ a = +s (negation).
pub fn search(h: &Group, k: usize, dem: &Demand, max_nodes: u64) -> VectorSearch {
    let mut st = St { h, k: k as i64, dem, a: vec![0; h.order], nodes: 0, max_nodes, found: None };
    st.go(0, 0, 0, 0, 0);
    VectorSearch { found: st.found, nodes: st.nodes, cut: st.nodes > max_nodes }
}

struct St<'a> {
    h: &'a Group,
    k: i64,
    dem: &'a Demand,
    a: Vec<i64>,
    nodes: u64,
    max_nodes: u64,
    found: Option<Vec<i64>>,
}

impl St<'_> {
    fn go(&mut self, i: usize, sum: i64, sq: i64, abs: i64, top: i64) -> bool {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            return true;
        }
        let n = self.h.order;
        let (c, square, s) = (self.dem.c, self.dem.square, self.dem.sum);
        if i == n {
            if sum != s || sq != square || abs > self.k || (self.k - abs) % 2 != 0 {
                return false;
            }
            let ok = (1..n).all(|g| {
                (0..n).map(|x| self.a[x] * self.a[self.h.add[x][g]]).sum::<i64>() == self.dem.target
            });
            if ok {
                self.found = Some(self.a.clone());
            }
            return ok;
        }
        let rem = (n - i) as i64;
        let left_sq = square - sq;
        let left_sum = s - sum;
        // Cauchy–Schwarz on the rest, and the box bound.
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * c {
            return false;
        }
        let lim = if i == 0 { c } else { top };
        for x in -lim..=lim {
            if x * x > left_sq {
                continue;
            }
            self.a[i] = x;
            let t = if i == 0 { x.abs() } else { top };
            if self.go(i + 1, sum + x, sq + x * x, abs + x.abs(), t) {
                return true;
            }
        }
        self.a[i] = 0;
        false
    }
}

/// Vectors with |aᵢ| ≤ c, Σ a = s, Σ a² = square on n coordinates: what a Lean enumeration
/// without symmetry breaks visits at its leaves. Saturates at u64::MAX.
pub fn count_vectors(n: usize, dem: &Demand) -> u64 {
    // ways[sum offset][sq] after each coordinate.
    let c = dem.c;
    let (q, s) = (dem.square, dem.sum);
    if q < 0 {
        return 0;
    }
    let width = (2 * c * n as i64 + 1) as usize;
    let off = c * n as i64;
    let mut ways = vec![vec![0u64; q as usize + 1]; width];
    ways[off as usize][0] = 1;
    for _ in 0..n {
        let mut next = vec![vec![0u64; q as usize + 1]; width];
        for (si, row) in ways.iter().enumerate() {
            for (qi, &w) in row.iter().enumerate() {
                if w == 0 {
                    continue;
                }
                for x in -c..=c {
                    let nq = qi as i64 + x * x;
                    let ns = si as i64 + x;
                    if nq <= q && ns >= 0 && (ns as usize) < width {
                        let cell = &mut next[ns as usize][nq as usize];
                        *cell = cell.saturating_add(w);
                    }
                }
            }
        }
        ways = next;
    }
    let idx = s + off;
    if idx < 0 || idx as usize >= width { 0 } else { ways[idx as usize][q as usize] }
}
