// Can D force entry into a class where the Lean route covers the high phase (A8)? Real Catch-Up,
// both players free, from a start set at a deficit. The first position that is a high round start
// (|R| even, min R ≥ span R, mover's debt ≤ min R) is scored for D: draw if it lies in C, loss
// otherwise. With a = min R and offsets T = R − a, C is:
//   debts:   W ≤ a and the mover's debt ≤ a (L25: W never rises, so every later debt fits L22);
//   outcome: D to move at debt d: KZc(T, d) (L23); opponent to move at debt e: KYc(T, e) (L23) or
//            e ≥ c(T) (after Hyb2T's switch, L20).
// W (L25): Ψ(T) = 2·span − |T| + 2 − o₂(T) where D moves or e < c(T); max(e, min(e + c − o₂, Ψ))
// where the opponent moves at e ≥ c(T). Parity (C2) holds on every draw-parity start.
// Prints D's outcome per N for the start {lo..N} at the deficit (D as mover / as the other).
// Usage: formal_entry <lo> <n_max> <deficit> [parts]: parts `wo` (default) checks both, `w` only the
// debt part, `o` only the outcome part; `h` replaces the outcome part by Hyb2T's exact guarantee in
// the rounds game (≥ draw), the largest outcome class any proof of Hyb2T can use; `c` asserts that the
// outcome class lies inside Hyb2T's guarantee (L23 + L20) at every scored position.

use std::collections::HashMap;

const UNKNOWN: i8 = 2;

fn elems(mask: u32) -> Vec<i64> { (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64 + 1).collect() }
fn sum(mask: u32) -> i64 { elems(mask).iter().sum() }
// L20's matching cost: sorted numbers paired bottom-up.
fn cost(xs: &[i64]) -> i64 { xs.chunks(2).map(|c| if c.len() == 2 { c[1] - c[0] } else { 0 }).sum() }
// L23's depth: Σ (max − h) over holes h strictly between min and max.
fn depth(xs: &[i64]) -> i64 {
    if xs.len() < 2 { return 0; }
    let (lo, hi) = (xs[0], xs[xs.len() - 1]);
    (lo + 1..hi).filter(|h| !xs.contains(h)).map(|h| hi - h).sum()
}
fn kzc(t: &[i64], d: i64) -> bool {
    let n = t.len();
    if n == 0 { return d <= 1; }
    if n == 2 { return d <= t[1] - t[0] + 1; }
    d + depth(&t[..n - 1]) <= (n / 2) as i64
}
fn kyc(t: &[i64], e: i64) -> bool {
    let n = t.len();
    if n == 2 { return t[1] - t[0] <= e + 1; }
    if n >= 4 {
        let has_holes = t[n - 1] - t[0] + 1 > n as i64;
        return depth(t) <= e + (n / 2) as i64 && (!has_holes || e >= 1);
    }
    true
}
fn psi(t: &[i64]) -> i64 { 2 * (t[t.len() - 1] - t[0]) - t.len() as i64 + 2 - t[1] }

fn bits(mask: u32) -> Vec<i64> { (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64).collect() }

// Hyb2T in the rounds game on offsets: as mover the largest; as answerer the smallest j with
// e + j − i ≥ c of what is left, else AM+T (the largest, or the second largest at an exact tie).
fn hyb2t(m1: u32, e: i64, i: i64) -> i64 {
    let os = bits(m1);
    for &j in &os { if e + j - i >= cost(&bits(m1 & !(1 << j))) { return j; } }
    let top = os[os.len() - 1];
    if e + top == i && os.len() >= 2 { os[os.len() - 2] } else { top }
}

// Z's guaranteed outcome with Hyb2T against a perfect Y: Z moves at debt d (`z_moves`), else Y at d.
fn hyb(cache: &mut HashMap<(u32, i64, bool), i8>, mask: u32, d: i64, z_moves: bool) -> i8 {
    if mask == 0 { return if d == 0 { 0 } else if z_moves { -1 } else { 1 }; }
    if d > bits(mask).iter().sum::<i64>() { return if z_moves { -1 } else { 1 }; }
    if let Some(&v) = cache.get(&(mask, d, z_moves)) { return v; }
    let mut worst = 1;
    if z_moves {
        let i = 31 - mask.leading_zeros() as i64;
        let m1 = mask & !(1 << i);
        for j in bits(m1) {
            let (m2, delta) = (m1 & !(1 << j), d + j - i);
            worst = worst.min(if delta >= 0 { hyb(cache, m2, delta, true) } else { hyb(cache, m2, -delta, false) });
        }
    } else {
        for i in bits(mask) {
            let m1 = mask & !(1 << i);
            let j = hyb2t(m1, d, i);
            let (m2, delta) = (m1 & !(1 << j), d + j - i);
            worst = worst.min(if delta >= 0 { hyb(cache, m2, delta, false) } else { hyb(cache, m2, -delta, true) });
        }
    }
    cache.insert((mask, d, z_moves), worst);
    worst
}

// D's score at a high round start: Some(in C) if it is one.
fn score(cache: &mut HashMap<(u32, i64, bool), i8>, mask: u32, g: i64, d_moves: bool, part: Part) -> Option<bool> {
    let xs = elems(mask);
    if xs.len() % 2 == 1 { return None; }
    if xs.is_empty() { return Some(if d_moves { g == 0 } else { true }); }
    let a = xs[0];
    let span = xs[xs.len() - 1] - a;
    if a < span || g > a { return None; }
    let t: Vec<i64> = xs.iter().map(|x| x - a).collect();
    let c = cost(&t);
    let w = if d_moves || g < c { psi(&t) } else { g.max((g + c - t[1]).min(psi(&t))) };
    if part.check {
        let tm = t.iter().fold(0u32, |m, &o| m | 1 << o);
        let inside = if d_moves { kzc(&t, g) } else { kyc(&t, g) || g >= c };
        assert!(!inside || hyb(cache, tm, g, d_moves) >= 0, "class outside Hyb2T's guarantee: {:?} d = {} D moves {}", t, g, d_moves);
    }
    let outcome = if !part.outcome { true } else if part.exact {
        let tm = t.iter().fold(0u32, |m, &o| m | 1 << o);
        hyb(cache, tm, g, d_moves) >= 0
    } else if d_moves { kzc(&t, g) } else { kyc(&t, g) || g >= c };
    Some((!part.debt || w <= a) && outcome)
}

#[derive(Clone, Copy)]
struct Part { debt: bool, outcome: bool, exact: bool, check: bool }

struct G { n: usize, part: Part, cache: HashMap<(u32, i64, bool), i8>, md: Vec<i8>, ma: Vec<i8> }

impl G {
    fn key(&self, mask: u32, g: i64) -> usize { mask as usize * (self.n + 1) + g as usize }
    // D to move, trailing by g: 1 win, 0 draw, -1 loss for D.
    fn vd(&mut self, mask: u32, g: i64) -> i8 {
        if let Some(inside) = score(&mut self.cache, mask, g, true, self.part) { return if inside { 0 } else { -1 }; }
        if sum(mask) < g { return -1; }
        let k = self.key(mask, g);
        if self.md[k] != UNKNOWN { return self.md[k]; }
        let mut best = -1;
        for x in elems(mask) {
            let r = mask & !(1 << (x - 1));
            let v = if x >= g { self.va(r, x - g) } else { self.vd(r, g - x) };
            if v > best { best = v; if best == 1 { break; } }
        }
        self.md[k] = best;
        best
    }
    // The opponent to move, trailing by g.
    fn va(&mut self, mask: u32, g: i64) -> i8 {
        if let Some(inside) = score(&mut self.cache, mask, g, false, self.part) { return if inside { 0 } else { -1 }; }
        if sum(mask) < g { return 1; }
        let k = self.key(mask, g);
        if self.ma[k] != UNKNOWN { return self.ma[k]; }
        let mut worst = 1;
        for x in elems(mask) {
            let r = mask & !(1 << (x - 1));
            let v = if x >= g { self.vd(r, x - g) } else { self.va(r, g - x) };
            if v < worst { worst = v; if worst == -1 { break; } }
        }
        self.ma[k] = worst;
        worst
    }
}

fn letter(v: i8) -> char { ['L', 'D', 'W'][(v + 1) as usize] }

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<i64> = raw[..3].iter().map(|s| s.parse().unwrap()).collect();
    let (lo, n_max, deficit) = (a[0], a[1] as usize, a[2]);
    let parts = raw.get(3).map(String::as_str).unwrap_or("wo");
    let part = Part { debt: parts.contains('w'), outcome: parts.contains('o') || parts.contains('h'), exact: parts.contains('h'), check: parts.contains('c') };
    println!("| N | D as mover | D as other |\n|---|---|---|");
    for n in lo as usize..=n_max {
        let total: i64 = (lo..=n as i64).sum();
        if (total + deficit) % 2 != 0 { continue; }
        // Debts stay ≤ N (a turn ends within the last pick), plus the start's.
        let size = (1usize << n) * (n + 1);
        let mut gm = G { n, part, cache: HashMap::new(), md: vec![UNKNOWN; size], ma: vec![UNKNOWN; size] };
        let mask = (((1u64 << n) - 1) as u32) & !(((1u64 << (lo - 1)) - 1) as u32);
        println!("| {} | {} | {} |", n, letter(gm.vd(mask, deficit)), letter(gm.va(mask, deficit)));
    }
}
