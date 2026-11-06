//! Orbit exhaust (idea I5, A5): with gcd(v, n) = 1, C9 makes some translate of every SDS fixed
//! by each multiplier in M with sign sum +s, so it is a union of M-orbits with one sign per
//! orbit. Exhausting every sign choice on the orbits and finding no SDS shows there is none.

use crate::{Group, Sign, is_sds};

/// Greatest common divisor.
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The distinct prime divisors of `n`, ascending.
pub fn prime_divisors(mut n: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut p = 2;
    while p * p <= n {
        if n % p == 0 {
            out.push(p);
            while n % p == 0 {
                n /= p;
            }
        }
        p += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// Exponent of ∏ ℤ_{mᵢ}: the lcm of the mᵢ.
pub fn exponent(shape: &[usize]) -> usize {
    shape.iter().fold(1, |a, &m| a / gcd(a, m) * m)
}

/// ⟨p mod e⟩ in (ℤ/e)^* as p⁰, p¹, … in order; needs gcd(p, e) = 1.
fn powers(p: usize, e: usize) -> Vec<usize> {
    assert_eq!(gcd(p, e), 1, "{p} is not a unit mod {e}");
    let one = 1 % e;
    let mut out = vec![one];
    let mut x = p % e;
    while x != one {
        out.push(x);
        x = x * p % e;
    }
    out
}

/// The multiplier group of C9, as residues mod the exponent e of G.
pub struct Multipliers {
    pub exponent: usize,
    /// M's residues mod e, ascending.
    pub elements: Vec<usize>,
    /// A generator of M, which is cyclic.
    pub generator: usize,
}

/// The multipliers C9 uses. Gordon arXiv:2212.10630 Thm 5.1 (McFarland; Tan arXiv:1610.01914
/// Result 3.2): G abelian of order v and exponent e, D ∈ ℤ[G] with D D⁽⁻¹⁾ = n + λG,
/// gcd(v, n) = 1, n = p₁^a₁ ⋯ p_r^a_r; every t with gcd(t, v) = 1 and
/// t ≡ p₁^f₁ ≡ … ≡ p_r^f_r (mod e) for some fᵢ ≥ 0 is a multiplier. So
/// M = ⋂_{p | n} ⟨p mod e⟩ ≤ (ℤ/e)^*, cyclic as a subgroup of ⟨p₁⟩. `None` unless
/// gcd(v, n) = 1 and n ≥ 2 (no row of the table has n < 2).
pub fn multiplier_group(shape: &[usize], n: i64) -> Option<Multipliers> {
    let v: usize = shape.iter().product();
    if n < 2 || gcd(v, n as usize) != 1 {
        return None;
    }
    let e = exponent(shape);
    let primes = prime_divisors(n as usize);
    let first = powers(primes[0], e);
    let mut member = vec![false; e];
    for &t in &first {
        member[t] = true;
    }
    for &p in &primes[1..] {
        let mut in_p = vec![false; e];
        for t in powers(p, e) {
            in_p[t] = true;
        }
        for t in 0..e {
            member[t] &= in_p[t];
        }
    }
    let elements: Vec<usize> = (0..e).filter(|&t| member[t]).collect();
    // The subgroup of order m of the cyclic ⟨p₁⟩ (order N) is ⟨p₁^(N/m)⟩; p₁^N = p₁⁰.
    let generator = first[first.len() / elements.len() % first.len()];
    Some(Multipliers { exponent: e, elements, generator })
}

/// x ↦ t·x on ∏ ℤ_{mᵢ}, coordinatewise, on mixed-radix indices as `Group` numbers them.
pub fn scale(shape: &[usize], x: usize, t: usize) -> usize {
    let (mut x, mut out, mut place) = (x, 0, 1);
    for &m in shape.iter().rev() {
        out += (x % m) * (t % m) % m * place;
        place *= m;
        x /= m;
    }
    out
}

/// The orbits {t·x : t ∈ M} of M on G, each ascending, ordered by least element (orbit 0 is
/// {0}); computed as the cycles of x ↦ g·x for M's generator g.
pub fn orbits(shape: &[usize], mults: &Multipliers) -> Vec<Vec<usize>> {
    let v: usize = shape.iter().product();
    let mut seen = vec![false; v];
    let mut out = Vec::new();
    for x in 0..v {
        if seen[x] {
            continue;
        }
        let mut orbit = vec![x];
        seen[x] = true;
        let mut y = scale(shape, x, mults.generator);
        while y != x {
            seen[y] = true;
            orbit.push(y);
            y = scale(shape, y, mults.generator);
        }
        orbit.sort_unstable();
        out.push(orbit);
    }
    out
}

/// Why the exhaust does not apply to a case.
#[derive(Debug, PartialEq, Eq)]
pub enum NotApplicable {
    /// gcd(v, n) ≠ 1 or n < 2: C9 names no multiplier.
    NotCoprime,
    /// k + λ(v − 1) is not s² with s ≤ k and k + s even: C1 rules out every SDS.
    NoSquare,
}

/// What the exhaust concluded.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    /// An SDS constant on the orbits with sign sum +s, checked by `is_sds`.
    Found(Vec<Sign>),
    /// Every sign choice on the orbits exhausted: no SDS (given C9).
    NoSet,
    /// The node cap was hit first: inconclusive.
    Cut,
}

impl Verdict {
    pub const FOUND: &'static str = "found";
    pub const NO_SET: &'static str = "none";
    pub const CUT: &'static str = "cut";

    /// The label E10 prints.
    pub fn label(&self) -> &'static str {
        match self {
            Verdict::Found(_) => Self::FOUND,
            Verdict::NoSet => Self::NO_SET,
            Verdict::Cut => Self::CUT,
        }
    }
}

/// Result of one exhaust.
pub struct Outcome {
    pub verdict: Verdict,
    /// Search nodes visited.
    pub nodes: u64,
}

/// One case (G, k, λ) prepared for the exhaust.
pub struct OrbitCase {
    pub shape: Vec<usize>,
    pub k: usize,
    pub lam: i64,
    /// s ≥ 0 with s² = k + λ(v − 1) (C1); the exhaust fixes the sign sum to +s.
    pub s: i64,
    pub mults: Multipliers,
    pub orbits: Vec<Vec<usize>>,
}

/// Order in which each orbit's signs are tried.
const SIGN_ORDER: [Sign; 3] = [1, -1, 0];

impl OrbitCase {
    pub fn new(shape: &[usize], k: usize, lam: i64) -> Result<Self, NotApplicable> {
        let v: usize = shape.iter().product();
        let mults = multiplier_group(shape, k as i64 - lam).ok_or(NotApplicable::NotCoprime)?;
        let square = k as i64 + lam * (v as i64 - 1);
        if square < 0 {
            return Err(NotApplicable::NoSquare);
        }
        let s = (square as f64).sqrt().round() as i64;
        if s * s != square || s > k as i64 || (k as i64 + s) % 2 != 0 {
            return Err(NotApplicable::NoSquare);
        }
        let orbits = orbits(shape, &mults);
        Ok(OrbitCase { shape: shape.to_vec(), k, lam, s, mults, orbits })
    }

    /// Exhausts every sign in {+, −, 0} per orbit with k marked elements, sign sum +s and
    /// Σₓ D(x)·D(x + g) = λ for every g ≠ 0, stopping at the first set or after `max_nodes`.
    ///
    /// Why +s and one shift per orbit suffice: the translate C9 fixes has sign sum ±s (C1),
    /// and its negation is an SDS fixed by M too; for D fixed by M, the sum at t·g equals the
    /// sum at g (substitute x ↦ t·x), so checking the least element g of each nonzero orbit
    /// checks every g ≠ 0.
    pub fn exhaust(&self, max_nodes: u64) -> Outcome {
        let group = Group::new(&self.shape);
        let v = group.order;
        let r = self.orbits.len();
        let mut orbit_of = vec![0; v];
        for (i, o) in self.orbits.iter().enumerate() {
            for &x in o {
                orbit_of[x] = i;
            }
        }
        let shifts: Vec<usize> = self.orbits[1..].iter().map(|o| o[0]).collect();
        let weights = pair_weights(&group, &orbit_of, r, &shifts);
        let order = closure_order(&weights, &self.orbits);
        let mut pos = vec![0; r];
        for (d, &i) in order.iter().enumerate() {
            pos[i] = d;
        }
        let n_shifts = shifts.len();
        let links: Vec<Links> =
            (0..r).map(|d| Links::new(d, &weights[order[d]], &pos, n_shifts)).collect();
        let sizes: Vec<usize> = order.iter().map(|&i| self.orbits[i].len()).collect();
        let plus = ((self.k as i64 + self.s) / 2) as usize;
        let minus = self.k - plus;
        let reach = Reach::new(&sizes, plus, minus);
        let mut dfs = Dfs {
            sizes: &sizes,
            links: &links,
            reach: &reach,
            n_shifts,
            lam: self.lam as i32,
            plus,
            minus,
            eps: vec![0; r],
            partial: vec![0; (r + 1) * n_shifts],
            open: vec![0; (r + 1) * n_shifts],
            nodes: 0,
            max_nodes,
            cut: false,
        };
        // Depth 0: every term x of every shift is open.
        dfs.open[..n_shifts].fill(v as i32);
        let found = dfs.go(0, 0, 0) && !dfs.cut;
        let verdict = if found {
            let d: Vec<Sign> = (0..v).map(|x| dfs.eps[pos[orbit_of[x]]]).collect();
            let sum: i64 = d.iter().map(|&x| x as i64).sum();
            let ok = sum == self.s && is_sds(&group, self.k, self.lam, &d);
            assert!(ok, "engine output is not an SDS");
            Verdict::Found(d)
        } else if dfs.cut {
            Verdict::Cut
        } else {
            Verdict::NoSet
        };
        Outcome { verdict, nodes: dfs.nodes }
    }
}

/// For each orbit i: (shift index a, orbit j, w), w the number of terms x of Σₓ D(x)·D(x + g_a)
/// with {x, x + g_a} meeting orbits i and j (x ∈ O_i, x + g_a ∈ O_j or the reverse; for
/// j = i, both in O_i). Each term of each shift is counted once per orbit it touches.
fn pair_weights(
    group: &Group,
    orbit_of: &[usize],
    r: usize,
    shifts: &[usize],
) -> Vec<Vec<(u32, u32, i32)>> {
    let mut out = vec![Vec::new(); r];
    let mut pairs = Vec::with_capacity(group.order);
    for (a, &g) in shifts.iter().enumerate() {
        pairs.clear();
        for x in 0..group.order {
            let (i, j) = (orbit_of[x], orbit_of[group.add[x][g]]);
            pairs.push((i.min(j), i.max(j)));
        }
        pairs.sort_unstable();
        let mut t = 0;
        while t < pairs.len() {
            let (i, j) = pairs[t];
            let mut w = 0;
            while t < pairs.len() && pairs[t] == (i, j) {
                w += 1;
                t += 1;
            }
            out[i].push((a as u32, j as u32, w));
            if j != i {
                out[j].push((a as u32, i as u32, w));
            }
        }
    }
    out
}

/// The terms of each shift that touch orbit d (search order), by where their other end is.
struct Links {
    /// Per shift: terms with both ends in orbit d.
    own: Vec<i32>,
    /// Per shift: terms with the other end in an orbit after d.
    later: Vec<i32>,
    /// (shift, orbit j < d, terms between d and j), sorted by shift.
    earlier: Vec<(u32, u32, i32)>,
}

impl Links {
    /// From `pair_weights`' entries of orbit d, `pos` mapping orbits to search order.
    fn new(d: usize, weights: &[(u32, u32, i32)], pos: &[usize], n_shifts: usize) -> Self {
        let (mut own, mut later, mut earlier) = (vec![0; n_shifts], vec![0; n_shifts], Vec::new());
        for &(a, j, w) in weights {
            let j = pos[j as usize];
            match j.cmp(&d) {
                std::cmp::Ordering::Equal => own[a as usize] += w,
                std::cmp::Ordering::Greater => later[a as usize] += w,
                std::cmp::Ordering::Less => earlier.push((a, j as u32, w)),
            }
        }
        earlier.sort_unstable();
        Links { own, later, earlier }
    }
}

/// Search order: greedily the orbit that closes the most terms given those already placed
/// (ties: larger orbit, then lower index). Any order keeps the search exhaustive.
fn closure_order(weights: &[Vec<(u32, u32, i32)>], orbits: &[Vec<usize>]) -> Vec<usize> {
    let r = orbits.len();
    let mut closed: Vec<i64> = (0..r)
        .map(|i| {
            weights[i].iter().filter(|&&(_, j, _)| j as usize == i).map(|&(_, _, w)| w as i64).sum()
        })
        .collect();
    let mut placed = vec![false; r];
    let mut order = Vec::with_capacity(r);
    for _ in 0..r {
        let i = (0..r)
            .filter(|&i| !placed[i])
            .max_by_key(|&i| (closed[i], orbits[i].len(), std::cmp::Reverse(i)))
            .unwrap();
        placed[i] = true;
        order.push(i);
        for &(_, j, w) in &weights[i] {
            if !placed[j as usize] {
                closed[j as usize] += w as i64;
            }
        }
    }
    order
}

/// Suffix reachability of the marked counts: `contains(i, p, m)` iff the orbits i, i + 1, …
/// (search order) can be signed to give exactly p elements + and m elements −. It prunes
/// exactly the prefixes no completion can bring to (k + s)/2 plus and (k − s)/2 minus.
struct Reach {
    rows: usize,
    cols: usize,
    words: usize,
    bits: Vec<u64>,
}

impl Reach {
    fn new(sizes: &[usize], plus: usize, minus: usize) -> Self {
        let (rows, cols) = (plus + 1, minus + 1);
        let words = cols.div_ceil(64);
        let level = rows * words;
        let r = sizes.len();
        let mut bits = vec![0u64; (r + 1) * level];
        bits[r * level] = 1;
        let last_mask = if cols % 64 == 0 { u64::MAX } else { (1u64 << (cols % 64)) - 1 };
        for i in (0..r).rev() {
            let z = sizes[i];
            let (head, tail) = bits.split_at_mut((i + 1) * level);
            let src = &tail[..level];
            let dst = &mut head[i * level..];
            dst.copy_from_slice(src);
            for p in 0..rows {
                let row = &src[p * words..(p + 1) * words];
                if p + z < rows {
                    for (d, s) in dst[(p + z) * words..(p + z + 1) * words].iter_mut().zip(row) {
                        *d |= s;
                    }
                }
                let out = &mut dst[p * words..(p + 1) * words];
                let (ws, bs) = (z / 64, z % 64);
                for w in (ws..words).rev() {
                    let mut val = row[w - ws] << bs;
                    if bs > 0 && w > ws {
                        val |= row[w - ws - 1] >> (64 - bs);
                    }
                    out[w] |= val;
                }
                out[words - 1] &= last_mask;
            }
        }
        Reach { rows, cols, words, bits }
    }

    fn contains(&self, i: usize, p: usize, m: usize) -> bool {
        let at = (i * self.rows + p) * self.words + m / 64;
        p < self.rows && m < self.cols && (self.bits[at] >> (m % 64)) & 1 == 1
    }
}

/// Depth-first search over orbit signs, orbits in search order.
struct Dfs<'a> {
    sizes: &'a [usize],
    links: &'a [Links],
    reach: &'a Reach,
    n_shifts: usize,
    lam: i32,
    plus: usize,
    minus: usize,
    /// Sign of each orbit on the current path (search order).
    eps: Vec<Sign>,
    /// Per depth d (orbits < d signed), per shift: the sum over closed terms (both ends
    /// signed), and the number of open terms (neither end signed 0, not both signed).
    partial: Vec<i32>,
    open: Vec<i32>,
    nodes: u64,
    max_nodes: u64,
    cut: bool,
}

impl Dfs<'_> {
    /// Signs orbit `d` onward with `p` plus and `m` minus marked so far; true when the search
    /// stops (a set found, or the cap hit).
    fn go(&mut self, d: usize, p: usize, m: usize) -> bool {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return true;
        }
        if d == self.sizes.len() {
            // Every term closed and each bound met with no open term: every sum is λ.
            let row = &self.partial[d * self.n_shifts..];
            debug_assert!(row.iter().all(|&x| x == self.lam));
            return true;
        }
        let z = self.sizes[d];
        for e in SIGN_ORDER {
            let (p2, m2) = match e {
                1 => (p + z, m),
                -1 => (p, m + z),
                _ => (p, m),
            };
            if p2 > self.plus
                || m2 > self.minus
                || !self.reach.contains(d + 1, self.plus - p2, self.minus - m2)
            {
                continue;
            }
            self.eps[d] = e;
            if self.assign(d, e) && self.go(d + 1, p2, m2) {
                return true;
            }
        }
        self.eps[d] = 0;
        false
    }

    /// Writes depth d + 1's sums: depth d's plus the terms that signing orbit d with `e`
    /// settles. Whether every shift can still reach λ (false at the first that cannot; the
    /// rest of depth d + 1 is then left stale, and nothing reads it).
    ///
    /// Sound: a term D(x)·D(x + g) is exact once both ends are signed, 0 once either end is
    /// signed 0, and otherwise in {−1, 0, 1}; so the final sum lies within `open` of
    /// `partial`, and |λ − partial| > open rules the whole subtree out.
    fn assign(&mut self, d: usize, e: Sign) -> bool {
        let n = self.n_shifts;
        let (cur, next) = self.partial.split_at_mut((d + 1) * n);
        let (cur_open, next_open) = self.open.split_at_mut((d + 1) * n);
        let links = &self.links[d];
        let mut t = 0;
        for a in 0..n {
            let (mut s, mut o) = (cur[d * n + a], cur_open[d * n + a]);
            // Both ends in orbit d: e·e.
            if e != 0 {
                s += links.own[a];
            }
            o -= links.own[a];
            // Other end unsigned: the term is 0 once e = 0, else it stays open.
            if e == 0 {
                o -= links.later[a];
            }
            // Other end signed: exact; its terms left `open` already if it was signed 0.
            while t < links.earlier.len() && links.earlier[t].0 as usize == a {
                let (_, j, w) = links.earlier[t];
                let f = self.eps[j as usize];
                if f != 0 {
                    s += (e * f) as i32 * w;
                    o -= w;
                }
                t += 1;
            }
            next[a] = s;
            next_open[a] = o;
            if (self.lam - s).abs() > o {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn residues(m: &Multipliers) -> Vec<usize> {
        m.elements.clone()
    }

    #[test]
    fn primes_and_exponent() {
        assert_eq!(prime_divisors(38), vec![2, 19]);
        assert_eq!(prime_divisors(25), vec![5]);
        assert_eq!(prime_divisors(97), vec![97]);
        assert_eq!(exponent(&[2, 6]), 6);
        assert_eq!(exponent(&[4, 6]), 12);
        assert_eq!(exponent(&[3, 3]), 3);
    }

    /// Hand-checked multiplier groups.
    #[test]
    fn multiplier_groups_by_hand() {
        // (79, 40, 2): n = 38 = 2·19, ord₇₉(2) = ord₇₉(19) = 39, so M = the squares mod 79.
        let m = multiplier_group(&[79], 38).unwrap();
        let mut squares: Vec<usize> = (1..79).map(|x| x * x % 79).collect();
        squares.sort_unstable();
        squares.dedup();
        assert_eq!(residues(&m), squares);
        assert_eq!(orbits(&[79], &m).len(), 3);
        // (104, 29, 4): n = 25, ⟨5 mod 104⟩ = {1, 5, 25, 21} (5⁴ = 625 = 6·104 + 1).
        assert_eq!(residues(&multiplier_group(&[104], 25).unwrap()), vec![1, 5, 21, 25]);
        // (13, 12, 2): n = 10, 2 is primitive mod 13, ⟨5⟩ = {1, 5, 12, 8}: M = {1, 5, 8, 12}.
        let m = multiplier_group(&[13], 10).unwrap();
        assert_eq!(residues(&m), vec![1, 5, 8, 12]);
        assert_eq!(
            orbits(&[13], &m),
            vec![vec![0], vec![1, 5, 8, 12], vec![2, 3, 10, 11], vec![4, 6, 7, 9]]
        );
        // C₃ × C₃ with n = 7: e = 3, 7 ≡ 1, M = {1}; every element its own orbit.
        let m = multiplier_group(&[3, 3], 7).unwrap();
        assert_eq!(residues(&m), vec![1]);
        assert_eq!(orbits(&[3, 3], &m).len(), 9);
        // C₅ × C₅ with n = 2: M = ⟨2 mod 5⟩ = {1, 2, 3, 4}; orbits {0} and the six lines
        // through 0 without 0 (element (a, b) has index 5a + b).
        let m = multiplier_group(&[5, 5], 2).unwrap();
        assert_eq!(residues(&m), vec![1, 2, 3, 4]);
        let o = orbits(&[5, 5], &m);
        assert_eq!(o.len(), 7);
        assert!(o.contains(&vec![1, 2, 3, 4]) && o.contains(&vec![5, 10, 15, 20]));
        assert!(o.contains(&vec![6, 12, 18, 24]) && o[1..].iter().all(|x| x.len() == 4));
        // C₂ × C₆ with n = 5: e = 6, M = {1, 5} = {±1}: 4 elements with 2x = 0, 4 pairs.
        let m = multiplier_group(&[2, 6], 5).unwrap();
        assert_eq!(residues(&m), vec![1, 5]);
        assert_eq!(orbits(&[2, 6], &m).len(), 8);
        // No multiplier theorem: gcd(v, n) > 1, or n < 2.
        assert!(multiplier_group(&[10], 4).is_none());
        assert!(multiplier_group(&[9], 6).is_none());
        assert!(multiplier_group(&[11], 1).is_none());
    }

    /// The generator's cycles are the orbits {t·x : t ∈ M}, and M is the intersection.
    #[test]
    fn orbits_match_definition() {
        let shapes: [&[usize]; 9] =
            [&[7], &[13], &[2, 6], &[3, 9], &[5, 5], &[4, 8], &[3, 3, 3], &[55], &[2, 2, 14]];
        for shape in shapes {
            let v: usize = shape.iter().product();
            for n in 2..60 {
                let Some(m) = multiplier_group(shape, n as i64) else { continue };
                let e = m.exponent;
                // M by definition: units t with t ≡ some power of p for every prime p | n.
                let def: Vec<usize> = (0..e)
                    .filter(|&t| gcd(t, e) == 1)
                    .filter(|&t| {
                        prime_divisors(n).iter().all(|&p| {
                            let mut x = 1 % e;
                            (0..=e).any(|_| {
                                let hit = x == t;
                                x = x * p % e;
                                hit
                            })
                        })
                    })
                    .collect();
                assert_eq!(m.elements, def, "M for {shape:?}, n = {n}");
                let mut want: Vec<Vec<usize>> = Vec::new();
                for x in 0..v {
                    let mut o: Vec<usize> = def.iter().map(|&t| scale(shape, x, t)).collect();
                    o.sort_unstable();
                    o.dedup();
                    if !want.contains(&o) {
                        want.push(o);
                    }
                }
                assert_eq!(orbits(shape, &m), want, "orbits for {shape:?}, n = {n}");
            }
        }
    }

    #[test]
    fn reach_matches_naive() {
        let cases: [(&[usize], usize, usize); 4] = [
            (&[1, 3, 3, 6], 5, 4),
            (&[1, 2, 2, 2, 4, 4], 6, 3),
            (&[70, 1, 65, 3], 70, 68),
            (&[1], 0, 0),
        ];
        for (sizes, plus, minus) in cases {
            let reach = Reach::new(sizes, plus, minus);
            for i in 0..=sizes.len() {
                let mut set = std::collections::HashSet::from([(0, 0)]);
                for &z in &sizes[i..] {
                    let old: Vec<_> = set.iter().copied().collect();
                    for (p, m) in old {
                        set.insert((p + z, m));
                        set.insert((p, m + z));
                    }
                }
                for p in 0..=plus {
                    for m in 0..=minus {
                        let want = set.contains(&(p, m));
                        assert_eq!(reach.contains(i, p, m), want, "{sizes:?} {i} {p} {m}");
                    }
                }
            }
        }
    }

    /// Known sets are found; (79, 40, 2) dies at the root (a5-a3 report, by hand).
    #[test]
    fn known_cases() {
        let known = [(3, 1, vec![7]), (6, 1, vec![11]), (12, 4, vec![23]), (29, 4, vec![104])];
        for (k, lam, shape) in known {
            let out = OrbitCase::new(&shape, k, lam).unwrap().exhaust(u64::MAX);
            assert!(matches!(out.verdict, Verdict::Found(_)), "({k}, {lam}, {shape:?})");
        }
        let out = OrbitCase::new(&[79], 40, 2).unwrap().exhaust(u64::MAX);
        assert_eq!((out.verdict, out.nodes), (Verdict::NoSet, 1));
        assert_eq!(OrbitCase::new(&[9], 8, 2).err(), Some(NotApplicable::NotCoprime));
        assert_eq!(OrbitCase::new(&[7], 3, 0).err(), Some(NotApplicable::NoSquare));
    }

    /// Against a naive enumeration of every orbit sign vector checked by `is_sds`: the same
    /// verdict for every small case with gcd(v, n) = 1 and at most 11 orbits.
    #[test]
    fn agrees_with_naive_enumeration() {
        let shapes: [&[usize]; 20] = [
            &[7], &[8], &[2, 4], &[2, 2, 2], &[9], &[3, 3], &[10], &[11], &[12], &[2, 6], &[13],
            &[14], &[15], &[16], &[4, 4], &[17], &[19], &[21], &[5, 5], &[3, 9],
        ];
        let (mut checked, mut found_count) = (0, 0);
        for shape in shapes {
            let group = Group::new(shape);
            let v = group.order;
            for k in 1..=v {
                for lam in -(k as i64)..=(k as i64) {
                    let Ok(case) = OrbitCase::new(shape, k, lam) else { continue };
                    let r = case.orbits.len();
                    if r > 11 {
                        continue;
                    }
                    let mut naive = false;
                    for code in 0..3usize.pow(r as u32) {
                        let mut d = vec![0 as Sign; v];
                        let mut c = code;
                        for o in &case.orbits {
                            let e = [0, 1, -1][c % 3];
                            c /= 3;
                            for &x in o {
                                d[x] = e;
                            }
                        }
                        let sum: i64 = d.iter().map(|&x| x as i64).sum();
                        if sum == case.s && is_sds(&group, k, lam, &d) {
                            naive = true;
                            break;
                        }
                    }
                    let found = matches!(case.exhaust(u64::MAX).verdict, Verdict::Found(_));
                    assert_eq!(found, naive, "{shape:?} k = {k} λ = {lam}");
                    checked += 1;
                    found_count += found as usize;
                }
            }
        }
        // Both verdicts must be exercised.
        let both = checked >= 80 && found_count >= 20 && checked - found_count >= 20;
        assert!(both, "{found_count} found of {checked}");
        eprintln!("naive agreement: {found_count} found, {} none", checked - found_count);
    }
}
