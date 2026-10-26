// When must a two-ended defender pick from the top (B35)? On {1..N} at gap 0, D restricted to the k
// smallest and k largest numbers left, the opponent perfect. Walks every position reachable when D
// plays any drawing menu pick and the opponent anything, and sorts D's positions by which side has
// drawing picks: bottom only, top only, both. Lists the top-only positions.
// Usage: two_ended_sides <n> <k> [max_listed]. Dense memo [mask][gap], gap < 32.

use std::collections::HashSet;

const UNKNOWN: i16 = i16::MIN;
const GMAX: usize = 32;

struct G { nums: Vec<i64>, k: usize, md: Vec<i16>, ma: Vec<i16> }

impl G {
    fn lowest(&self, mask: u32) -> u32 {
        let (mut lo, mut m) = (0u32, mask);
        for _ in 0..self.k { if m != 0 { lo |= m & m.wrapping_neg(); m &= m - 1; } }
        lo
    }
    fn highest(&self, mask: u32) -> u32 {
        let (mut hi, mut n) = (0u32, mask);
        for _ in 0..self.k { if n != 0 { let b = 1u32 << (31 - n.leading_zeros()); hi |= b; n &= !b; } }
        hi
    }
    fn sum(&self, mask: u32) -> i64 { (0..self.nums.len()).filter(|&b| mask >> b & 1 == 1).map(|b| self.nums[b]).sum() }
    // D to move, trailing by g; returns D's final margin.
    fn vd(&mut self, mask: u32, g: i64) -> i64 {
        if mask == 0 { return -g; }
        let t = self.sum(mask);
        if t < g { return t - g; }
        let key = mask as usize * GMAX + g as usize;
        if self.md[key] != UNKNOWN { return self.md[key] as i64; }
        let al = self.lowest(mask) | self.highest(mask);
        let mut best = i64::MIN;
        for b in 0..self.nums.len() as u32 {
            if al >> b & 1 == 0 { continue; }
            best = best.max(self.after_d(mask, g, b));
        }
        self.md[key] = best as i16;
        best
    }
    // D's margin after D, trailing by g, picks bit b.
    fn after_d(&mut self, mask: u32, g: i64, b: u32) -> i64 {
        let x = self.nums[b as usize];
        let r = mask & !(1 << b);
        if x >= g { self.va(r, x - g) } else { self.vd(r, g - x) }
    }
    // The opponent to move, trailing by g; returns D's final margin.
    fn va(&mut self, mask: u32, g: i64) -> i64 {
        if mask == 0 { return g; }
        let t = self.sum(mask);
        if t < g { return g - t; }
        let key = mask as usize * GMAX + g as usize;
        if self.ma[key] != UNKNOWN { return self.ma[key] as i64; }
        let mut worst = i64::MAX;
        for b in 0..self.nums.len() as u32 {
            if mask >> b & 1 == 0 { continue; }
            worst = worst.min(self.after_a(mask, g, b));
        }
        self.ma[key] = worst as i16;
        worst
    }
    fn after_a(&mut self, mask: u32, g: i64, b: u32) -> i64 {
        let x = self.nums[b as usize];
        let r = mask & !(1 << b);
        if x >= g { self.vd(r, x - g) } else { self.va(r, g - x) }
    }
    fn set(&self, mask: u32) -> Vec<i64> { (0..self.nums.len()).filter(|&b| mask >> b & 1 == 1).map(|b| self.nums[b]).collect() }
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (n, k) = (args[0], args[1]);
    let max_listed = args.get(2).copied().unwrap_or(40);
    assert!(n < GMAX, "gaps must stay below GMAX");
    let nums: Vec<i64> = (1..=n as i64).collect();
    let mut gm = G { nums, k, md: vec![UNKNOWN; (1usize << n) * GMAX], ma: vec![UNKNOWN; (1usize << n) * GMAX] };
    let full = ((1u64 << n) - 1) as u32;
    let (p1, p2) = (gm.vd(full, 0), gm.va(full, 0));
    println!("N={} tb{}: D as player 1 margin {}, as player 2 margin {}", n, k, p1, p2);
    // (mask, gap, D to move?)
    let mut seen: HashSet<(u32, i64, bool)> = HashSet::new();
    let mut stack: Vec<(u32, i64, bool)> = vec![];
    if p1 >= 0 { stack.push((full, 0, true)); }
    if p2 >= 0 { stack.push((full, 0, false)); }
    let (mut bottom_only, mut top_only, mut both) = (0u64, 0u64, 0u64);
    let mut listed = 0;
    while let Some((mask, g, d_moves)) = stack.pop() {
        if mask == 0 || !seen.insert((mask, g, d_moves)) { continue; }
        if gm.sum(mask) < g { continue; }
        if d_moves {
            let (lo, hi) = (gm.lowest(mask), gm.highest(mask));
            let (mut lo_ok, mut hi_ok) = (false, false);
            for b in 0..n as u32 {
                if (lo | hi) >> b & 1 == 0 { continue; }
                if gm.after_d(mask, g, b) < 0 { continue; }
                if lo >> b & 1 == 1 { lo_ok = true; }
                if hi >> b & 1 == 1 { hi_ok = true; }
                let x = gm.nums[b as usize];
                let r = mask & !(1 << b);
                stack.push(if x >= g { (r, x - g, false) } else { (r, g - x, true) });
            }
            // A pick in both menus counts for both sides.
            match (lo_ok, hi_ok) {
                (true, false) => bottom_only += 1,
                (false, true) => {
                    top_only += 1;
                    if listed < max_listed {
                        listed += 1;
                        let bits: Vec<u32> = (0..n as u32)
                            .filter(|&b| hi >> b & 1 == 1 && gm.after_d(mask, g, b) >= 0).collect();
                        let picks: Vec<i64> = bits.iter().map(|&b| gm.nums[b as usize]).collect();
                        println!("top only: R = {:?}, gap {}, drawing picks {:?}", gm.set(mask), g, picks);
                    }
                }
                (true, true) => both += 1,
                (false, false) => {}
            }
        } else {
            for b in 0..n as u32 {
                if mask >> b & 1 == 0 { continue; }
                let x = gm.nums[b as usize];
                let r = mask & !(1 << b);
                stack.push(if x >= g { (r, x - g, true) } else { (r, g - x, false) });
            }
        }
    }
    println!("D positions along drawing play: bottom only {}, top only {}, both {}", bottom_only, top_only, both);
}
