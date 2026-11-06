//! Signed difference sets solver: exhaustive search of sign vectors on a finite abelian
//! group (idea I1), mirroring `SignedDifferenceSets.IsSDS`: k marked elements and
//! Σₓ D(x)·D(x + g) = λ for every g ≠ 0.

pub mod contraction;
pub mod cyclotomic;
pub mod instances;
pub mod orbits;

/// A finite abelian group ℤ_{m₁} × … × ℤ_{m_r}, elements indexed 0..v in mixed radix
/// (first factor most significant).
pub struct Group {
    pub shape: Vec<usize>,
    pub order: usize,
    /// `add[x][g]` is the index of x + g.
    pub add: Vec<Vec<usize>>,
    /// `sub[x][g]` is the index of x − g.
    pub sub: Vec<Vec<usize>>,
}

impl Group {
    pub fn new(shape: &[usize]) -> Self {
        let order = shape.iter().product();
        let add = (0..order)
            .map(|x| (0..order).map(|g| Self::sum(shape, x, g)).collect())
            .collect::<Vec<Vec<usize>>>();
        let mut sub = vec![vec![0; order]; order];
        for x in 0..order {
            for g in 0..order {
                sub[add[x][g]][g] = x;
            }
        }
        Group { shape: shape.to_vec(), order, add, sub }
    }

    fn sum(shape: &[usize], x: usize, g: usize) -> usize {
        let (mut x, mut g, mut out, mut place) = (x, g, 0, 1);
        for &m in shape.iter().rev() {
            out += ((x % m + g % m) % m) * place;
            place *= m;
            x /= m;
            g /= m;
        }
        out
    }

    /// Coordinates of element `x`, one per cyclic factor.
    pub fn coords(&self, mut x: usize) -> Vec<usize> {
        let mut c = vec![0; self.shape.len()];
        for (i, &m) in self.shape.iter().enumerate().rev() {
            c[i] = x % m;
            x /= m;
        }
        c
    }
}

/// Sign of an element: unmarked, plus or minus (`SignType` in Lean).
pub type Sign = i8;

/// Whether `d` is an SDS with parameters (|G|, k, λ): the definition, evaluated directly.
pub fn is_sds(group: &Group, k: usize, lam: i64, d: &[Sign]) -> bool {
    let marked = d.iter().filter(|&&s| s != 0).count();
    marked == k
        && (1..group.order).all(|g| {
            (0..group.order).map(|x| (d[x] * d[group.add[x][g]]) as i64).sum::<i64>() == lam
        })
}

/// Result of an exhaustive search of one case.
pub struct Outcome {
    /// Solutions with element 0 marked and sign sum +s (C1, C2); every SDS is a translate
    /// and possibly the negation of one of them.
    pub solutions: Vec<Vec<Sign>>,
    /// Search nodes visited.
    pub nodes: u64,
}

/// Every SDS (v, k, λ) on `group` with 0 marked and sign sum +s, up to `limit` solutions.
/// `None` when k + λ(v − 1) is not a perfect square (C1: no SDS at all).
pub fn search(group: &Group, k: usize, lam: i64, limit: usize) -> Option<Outcome> {
    search_capped(group, k, lam, limit, u64::MAX)
}

/// `search` stopped after `max_nodes` nodes; `Outcome::nodes > max_nodes` marks a cut-off run.
pub fn search_capped(
    group: &Group,
    k: usize,
    lam: i64,
    limit: usize,
    max_nodes: u64,
) -> Option<Outcome> {
    let v = group.order;
    let square = k as i64 + lam * (v as i64 - 1);
    if square < 0 {
        return None;
    }
    let s = (square as f64).sqrt().round() as i64;
    if s * s != square || (k as i64 + s) % 2 != 0 || s > k as i64 {
        return None;
    }
    let plus = ((k as i64 + s) / 2) as usize;
    let mut st = State {
        group,
        k,
        lam,
        plus,
        minus: k - plus,
        d: vec![0; v],
        partial: vec![0; v],
        open_terms: vec![v as i64; v],
        out: Outcome { solutions: Vec::new(), nodes: 0 },
        limit,
        max_nodes,
    };
    st.go(0, 0, 0);
    Some(st.out)
}

struct State<'a> {
    group: &'a Group,
    k: usize,
    lam: i64,
    plus: usize,
    minus: usize,
    d: Vec<Sign>,
    /// Σ over fully assigned terms x of D(x)·D(x + g), per g.
    partial: Vec<i64>,
    /// Terms x with x or x + g still unassigned, per g: the most the sum can still move.
    open_terms: Vec<i64>,
    out: Outcome,
    limit: usize,
    max_nodes: u64,
}

impl State<'_> {
    fn go(&mut self, i: usize, used_plus: usize, used_minus: usize) {
        self.out.nodes += 1;
        if self.out.solutions.len() >= self.limit || self.out.nodes > self.max_nodes {
            return;
        }
        let v = self.group.order;
        if i == v {
            if used_plus == self.plus && used_minus == self.minus {
                debug_assert!(is_sds(self.group, self.k, self.lam, &self.d));
                self.out.solutions.push(self.d.clone());
            }
            return;
        }
        let left = v - i;
        let need = (self.plus - used_plus) + (self.minus - used_minus);
        let signs: &[Sign] = if i == 0 { &[1, -1] } else { &[0, 1, -1] };
        for &s in signs {
            let (p, m) = match s {
                1 => (used_plus + 1, used_minus),
                -1 => (used_plus, used_minus + 1),
                _ => (used_plus, used_minus),
            };
            if p > self.plus || m > self.minus || (s == 0 && need >= left) {
                continue;
            }
            self.d[i] = s;
            let ok = self.close_terms(i, 1);
            if ok {
                self.go(i + 1, p, m);
            }
            self.close_terms(i, -1);
            self.d[i] = 0;
        }
    }

    /// Adds (`dir` = 1) or removes (−1) the terms that assigning element `i` completes;
    /// on adding, reports whether every g can still reach λ.
    fn close_terms(&mut self, i: usize, dir: i64) -> bool {
        let (g_add, g_sub) = (&self.group.add, &self.group.sub);
        let mut ok = true;
        for g in 1..self.group.order {
            // term x = i completes when i + g < i is assigned; term x = i − g when i − g < i.
            let fwd = g_add[i][g];
            if fwd < i {
                self.partial[g] += dir * (self.d[i] * self.d[fwd]) as i64;
                self.open_terms[g] -= dir;
            }
            let back = g_sub[i][g];
            if back < i {
                self.partial[g] += dir * (self.d[back] * self.d[i]) as i64;
                self.open_terms[g] -= dir;
            }
            if dir == 1 && (self.lam - self.partial[g]).abs() > self.open_terms[g] {
                ok = false;
            }
        }
        ok
    }
}
