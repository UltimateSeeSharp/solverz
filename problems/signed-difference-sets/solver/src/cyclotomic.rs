//! Pattern P2: sign vectors on the additive group of GF(q) constant on the cyclotomic
//! classes of order e: D = ε_z·[0] + Σⱼ εⱼ·Cⱼ, Cⱼ = {α^(e·t + j)}, every ε ∈ {−1, 0, +1}.
//! D(βx) = D(x) for β ∈ C₀, so Σₓ D(x)·D(x + g) is constant on each class: D is an SDS
//! iff its autocorrelations at α⁰, …, α^(e−1) agree.

use crate::Sign;

/// GF(p^m), elements indexed by their coefficients in the basis 1, α, …, α^(m−1) as
/// Σ cᵢ·pⁱ: addition is that of `Group::new(&[p; m])`.
pub struct Field {
    pub p: usize,
    pub m: u32,
    pub q: usize,
    /// `exp[i]` = αⁱ for i in 0..q − 1, α primitive.
    pub exp: Vec<usize>,
    /// `log[x]` = i with αⁱ = x, for x ≠ 0.
    pub log: Vec<usize>,
}

impl Field {
    /// GF(p^m) from the first monic f of degree m (lexicographic in f₀, …, f_{m−1}) whose
    /// root α has order q − 1; then f is irreducible and α primitive.
    pub fn new(p: usize, m: u32) -> Field {
        let q = p.pow(m);
        let mut f = vec![0; m as usize];
        loop {
            // Next candidate f₀ … f_{m−1}, f₀ ≠ 0.
            let mut i = 0;
            loop {
                f[i] = (f[i] + 1) % p;
                if f[i] != 0 {
                    break;
                }
                i += 1;
            }
            if f[0] == 0 {
                continue;
            }
            let mut exp = Vec::with_capacity(q - 1);
            let mut x = 1;
            loop {
                exp.push(x);
                x = Self::times_alpha(p, &f, x);
                if x == 1 {
                    break;
                }
            }
            if exp.len() == q - 1 {
                let mut log = vec![0; q];
                for (i, &x) in exp.iter().enumerate() {
                    log[x] = i;
                }
                return Field { p, m, q, exp, log };
            }
        }
    }

    /// x·α, reducing α^m = −Σ fᵢ αⁱ.
    fn times_alpha(p: usize, f: &[usize], x: usize) -> usize {
        let m = f.len();
        let top = x / p.pow(m as u32 - 1);
        let (mut out, mut place, mut rest) = (0, 1, x);
        for (i, &fi) in f.iter().enumerate() {
            let shifted = if i == 0 { 0 } else { rest % p };
            if i > 0 {
                rest /= p;
            }
            out += ((shifted + p * p - top * fi % p) % p) * place;
            place *= p;
        }
        out
    }

    /// x + y, digit by digit mod p.
    pub fn add(&self, mut x: usize, mut y: usize) -> usize {
        let (mut out, mut place) = (0, 1);
        for _ in 0..self.m {
            out += ((x % self.p + y % self.p) % self.p) * place;
            place *= self.p;
            x /= self.p;
            y /= self.p;
        }
        out
    }
}

/// Signs of one P2 vector: ε for C₀, …, C_{e−1}, then ε_z for {0}.
pub type ClassSigns = Vec<Sign>;

/// A P2 vector that is an SDS (q, k, λ).
pub struct Hit {
    pub signs: ClassSigns,
    pub k: usize,
    pub lam: i64,
}

/// The class of each element: log mod e, and e for 0.
pub fn classes(field: &Field, e: usize) -> Vec<usize> {
    (0..field.q).map(|x| if x == 0 { e } else { field.log[x] % e }).collect()
}

/// The sign vector on GF(q) of `signs`.
pub fn expand(field: &Field, e: usize, signs: &[Sign]) -> Vec<Sign> {
    classes(field, e).iter().map(|&c| signs[c]).collect()
}

/// Every nonzero sign choice that is an SDS, e | q − 1.
pub fn search(field: &Field, e: usize) -> Vec<Hit> {
    assert_eq!((field.q - 1) % e, 0, "e ∤ q − 1");
    let (q, n, f) = (field.q, e + 1, (field.q - 1) / e);
    let cls = classes(field, e);
    // pairs[j][a·n + b] = #{x : class(x) = a, class(x + αʲ) = b}.
    let pairs: Vec<Vec<i64>> = (0..e)
        .map(|j| {
            let mut c = vec![0; n * n];
            for x in 0..q {
                c[cls[x] * n + cls[field.add(x, field.exp[j])]] += 1;
            }
            c
        })
        .collect();
    let autocorr = |c: &[i64], s: &[Sign]| -> i64 {
        (0..n).map(|a| (0..n).map(|b| (s[a] * s[b]) as i64 * c[a * n + b]).sum::<i64>()).sum()
    };
    let mut hits = Vec::new();
    let mut s: ClassSigns = vec![0; n];
    for code in 1..3usize.pow(n as u32) {
        let mut c = code;
        for x in s.iter_mut() {
            *x = [0, 1, -1][c % 3];
            c /= 3;
        }
        let lam = autocorr(&pairs[0], &s);
        if (1..e).all(|j| autocorr(&pairs[j], &s) == lam) {
            let k = f * s[..e].iter().filter(|&&x| x != 0).count() + (s[e] != 0) as usize;
            hits.push(Hit { signs: s.clone(), k, lam });
        }
    }
    hits
}

/// The least of the images of `signs` under negation and the class relabellings
/// j ↦ pᵗ·j + r (multiplication by αʳ, Frobenius), all automorphisms of (GF(q), +).
pub fn canonical(signs: &[Sign], e: usize, p: usize) -> ClassSigns {
    let mut best = signs.to_vec();
    let mut mult = 1;
    loop {
        for r in 0..e {
            for neg in [1, -1] {
                let mut img = vec![0; e + 1];
                for j in 0..e {
                    img[(mult * j + r) % e] = neg * signs[j];
                }
                img[e] = neg * signs[e];
                if img < best {
                    best = img;
                }
            }
        }
        mult = mult * p % e;
        if mult == 1 {
            return best;
        }
    }
}
