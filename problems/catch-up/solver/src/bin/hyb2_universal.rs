// Is Hyb2 a universal high-phase strategy (I8)? In the rounds game (C13) on every even offset set
// O ⊆ {0..U−1} and every debt d with d + sum(O) even, compares Z's guaranteed outcome when Z plays
// Hyb2 against a perfect Y with the exact outcome, with Z as mover (trailing by d) and as the other.
// Hyb2: as first picker Z takes the largest; as answerer the smallest j leaving Y's debt ≥ c of what
// is left (a valid answer), else the largest. Counts where Hyb2 does worse, and where it loses a draw
// Z could secure (a failure); lists the first failures.
// Usage: hyb2_universal <U> [max_listed].

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;
const UNKNOWN: u8 = 3;

fn neg(v: u8) -> u8 { WIN - v }
fn letter(v: u8) -> char { ['L', 'D', 'W'][v as usize] }
fn offsets(mask: u32) -> Vec<i64> { (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64).collect() }
fn sum(mask: u32) -> i64 { offsets(mask).iter().sum() }
// C20's matching cost: sorted offsets paired bottom-up.
fn cost(mask: u32) -> i64 { offsets(mask).chunks(2).map(|c| c[1] - c[0]).sum() }

struct T { stride: usize, exact: Vec<u8>, hz: Vec<u8>, hy: Vec<u8> }

impl T {
    fn key(&self, mask: u32, d: i64) -> usize { mask as usize * self.stride + d as usize }
    // Exact value for the mover trailing by d.
    fn exact(&mut self, mask: u32, d: i64) -> u8 {
        if mask == 0 { return if d == 0 { DRAW } else { LOSS }; }
        if d > sum(mask) { return LOSS; }
        let k = self.key(mask, d);
        if self.exact[k] != UNKNOWN { return self.exact[k]; }
        let mut best = LOSS;
        'outer: for i in offsets(mask) {
            let m1 = mask & !(1 << i);
            let mut worst = WIN;
            for j in offsets(m1) {
                let (m2, delta) = (m1 & !(1 << j), d + j - i);
                let v = if delta >= 0 { self.exact(m2, delta) } else { neg(self.exact(m2, -delta)) };
                worst = worst.min(v);
                if worst <= best { break; }
            }
            best = best.max(worst);
            if best == WIN { break 'outer; }
        }
        self.exact[k] = best;
        best
    }
    // Hyb2's answer to Y's pick i, Y trailing by e, from `m1` (i already removed).
    fn answer(m1: u32, e: i64, i: i64) -> i64 {
        let os = offsets(m1);
        for &j in &os {
            if e + j - i >= cost(m1 & !(1 << j)) { return j; }
        }
        *os.last().unwrap()
    }
    // Z (Hyb2) is the mover trailing by d; Z's guaranteed value against a perfect Y.
    fn hz(&mut self, mask: u32, d: i64) -> u8 {
        if mask == 0 { return if d == 0 { DRAW } else { LOSS }; }
        if d > sum(mask) { return LOSS; }
        let k = self.key(mask, d);
        if self.hz[k] != UNKNOWN { return self.hz[k]; }
        let i = 31 - mask.leading_zeros() as i64;
        let m1 = mask & !(1 << i);
        let mut worst = WIN;
        for j in offsets(m1) {
            let (m2, delta) = (m1 & !(1 << j), d + j - i);
            let v = if delta >= 0 { self.hz(m2, delta) } else { self.hy(m2, -delta) };
            worst = worst.min(v);
        }
        self.hz[k] = worst;
        worst
    }
    // Y is the mover trailing by e; Z's guaranteed value.
    fn hy(&mut self, mask: u32, e: i64) -> u8 {
        if mask == 0 { return if e == 0 { DRAW } else { WIN }; }
        if e > sum(mask) { return WIN; }
        let k = self.key(mask, e);
        if self.hy[k] != UNKNOWN { return self.hy[k]; }
        let mut worst = WIN;
        for i in offsets(mask) {
            let m1 = mask & !(1 << i);
            let j = Self::answer(m1, e, i);
            let (m2, delta) = (m1 & !(1 << j), e + j - i);
            let v = if delta >= 0 { self.hy(m2, delta) } else { self.hz(m2, -delta) };
            worst = worst.min(v);
        }
        self.hy[k] = worst;
        worst
    }
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let u = args[0];
    let max_listed = args.get(1).copied().unwrap_or(30);
    let stride = u * (u - 1) / 2 + 1;
    let size = (1usize << u) * stride;
    let mut t = T { stride, exact: vec![UNKNOWN; size], hz: vec![UNKNOWN; size], hy: vec![UNKNOWN; size] };
    let (mut checked, mut worse_mover, mut worse_other, mut fail_mover, mut fail_other, mut listed) = (0u64, 0u64, 0u64, 0u64, 0u64, 0);
    // By size, then mask, so the smallest examples are listed first.
    let mut masks: Vec<u32> = (1..(1u32 << u)).filter(|m| m.count_ones() % 2 == 0).collect();
    masks.sort_by_key(|m| (m.count_ones(), *m));
    for mask in masks {
        let s = sum(mask);
        for d in 0..=s {
            if (d + s) % 2 != 0 { continue; }
            checked += 1;
            let ex = t.exact(mask, d);
            let (zm, zo) = (t.hz(mask, d), t.hy(mask, d));
            if zm < ex { worse_mover += 1; }
            if zo < neg(ex) { worse_other += 1; }
            let (fm, fo) = (ex >= DRAW && zm < DRAW, neg(ex) >= DRAW && zo < DRAW);
            if fm { fail_mover += 1; }
            if fo { fail_other += 1; }
            if (fm || fo) && listed < max_listed {
                listed += 1;
                println!("O = {:?}, d = {}: exact {} for the mover; Hyb2 as mover {}, as the other {} (exact {})",
                    offsets(mask), d, letter(ex), letter(zm), letter(zo), letter(neg(ex)));
            }
        }
    }
    // Check: full blocks {0..2p−1} at debt p mod 2 draw with Hyb2 in both roles (C24).
    for p in 1..=u / 2 {
        let (mask, d) = ((1u32 << (2 * p)) - 1, (p % 2) as i64);
        println!("block p = {}: exact {}, Hyb2 as mover {}, as the other {}", p, letter(t.exact(mask, d)), letter(t.hz(mask, d)), letter(t.hy(mask, d)));
    }
    println!("U = {}: {} positions (even O, d + sum even); Hyb2 worse than exact as mover at {}, as the other at {}; fails to secure a draw as mover at {}, as the other at {}",
        u, checked, worse_mover, worse_other, fail_mover, fail_other);
}
