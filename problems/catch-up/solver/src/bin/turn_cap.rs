// Can a defender draw with short turns on both sides, turn length measured exactly? Real Catch-Up on
// {1..N} at gap 0 (even totals) or a block {a..a+2p-1} at gap p mod 2. D takes at most `kd` picks per
// turn and must end each turn with the opponent behind by at most the sum of the `ka` smallest numbers
// left, so the opponent catches up within `ka` picks whatever it picks; the opponent is otherwise free.
// D with no allowed pick loses. Optional menu k > 0: D picks only among the k smallest and k largest
// numbers left (B35). Prints D's outcome in both roles (unrestricted: `kd`, `ka` large, k = 0).
// Usage: turn_cap intervals <n_max> <kd> <ka> [k] | blocks <p> <a_lo> <a_hi> <kd> <ka> [k]
//        | ranges <lo> <hi_max> <gap> <kd> <ka> [k] ({lo..hi} at the gap for hi ≤ hi_max with total + gap even).
// Dense memo [mask][gap][picks so far]; a gap never exceeds the largest number.

const UNKNOWN: i16 = i16::MIN;
const LOST: i64 = -10_000;

struct G { nums: Vec<i64>, kd: usize, ka: usize, k: usize, gs: usize, md: Vec<i16>, ma: Vec<i16> }

impl G {
    fn sum(&self, mask: u32) -> i64 { (0..self.nums.len()).filter(|&b| mask >> b & 1 == 1).map(|b| self.nums[b]).sum() }
    // Sum of the `ka` smallest numbers in `mask` (bits ascend with the numbers).
    fn cap(&self, mask: u32) -> i64 {
        let (mut s, mut m) = (0, mask);
        for _ in 0..self.ka { if m == 0 { break; } s += self.nums[m.trailing_zeros() as usize]; m &= m - 1; }
        s
    }
    // D's allowed picks: the k lowest and k highest set bits (bits ascend with the numbers), or all.
    fn menu(&self, mask: u32) -> u32 {
        if self.k == 0 { return mask; }
        let (mut lo, mut hi, mut m, mut n) = (0u32, 0u32, mask, mask);
        for _ in 0..self.k {
            if m != 0 { lo |= m & m.wrapping_neg(); m &= m - 1; }
            if n != 0 { let b = 1u32 << (31 - n.leading_zeros()); hi |= b; n &= !b; }
        }
        lo | hi
    }
    // D to move, trailing by g, having taken `t` picks this turn; returns D's final margin.
    fn vd(&mut self, mask: u32, g: i64, t: usize) -> i64 {
        if mask == 0 { return -g; }
        let total = self.sum(mask);
        if total < g { return total - g; }
        let key = (mask as usize * self.gs + g as usize) * self.kd + t;
        if self.md[key] != UNKNOWN { return self.md[key] as i64; }
        let mut best = LOST;
        let al = self.menu(mask);
        for b in 0..self.nums.len() as u32 {
            if al >> b & 1 == 0 { continue; }
            let x = self.nums[b as usize];
            let r = mask & !(1 << b);
            let o = if x >= g {
                // An opponent who cannot catch up at all has lost; otherwise it must within `ka` picks.
                if x - g <= self.sum(r) && x - g > self.cap(r) { continue; }
                self.va(r, x - g)
            } else {
                if t + 1 >= self.kd { continue; }
                self.vd(r, g - x, t + 1)
            };
            best = best.max(o);
        }
        self.md[key] = best as i16;
        best
    }
    // The opponent to move, trailing by g; returns D's final margin.
    fn va(&mut self, mask: u32, g: i64) -> i64 {
        if mask == 0 { return g; }
        let total = self.sum(mask);
        if total < g { return g - total; }
        let key = mask as usize * self.gs + g as usize;
        if self.ma[key] != UNKNOWN { return self.ma[key] as i64; }
        let mut worst = i64::MAX;
        for b in 0..self.nums.len() as u32 {
            if mask >> b & 1 == 0 { continue; }
            let x = self.nums[b as usize];
            let r = mask & !(1 << b);
            let o = if x >= g { self.vd(r, x - g, 0) } else { self.va(r, g - x) };
            worst = worst.min(o);
        }
        self.ma[key] = worst as i16;
        worst
    }
    fn new(nums: Vec<i64>, kd: usize, ka: usize, k: usize) -> G {
        let (n, gs) = (nums.len(), *nums.last().unwrap() as usize + 1);
        G { nums, kd, ka, k, gs, md: vec![UNKNOWN; (1usize << n) * gs * kd], ma: vec![UNKNOWN; (1usize << n) * gs] }
    }
}

fn outcome(m: i64) -> char { if m > 0 { 'W' } else if m == 0 { 'D' } else { 'L' } }

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let n = |i: usize| -> usize { raw[i].parse().unwrap() };
    let opt = |i: usize| -> usize { raw.get(i).map_or(0, |s| s.parse().unwrap()) };
    match raw[0].as_str() {
        "intervals" => {
            let (n_max, kd, ka, k) = (n(1), n(2), n(3), opt(4));
            let mut fails = vec![];
            for big_n in 1..=n_max {
                if (big_n * (big_n + 1) / 2) % 2 != 0 { continue; }
                let mut gm = G::new((1..=big_n as i64).collect(), kd, ka, k);
                let full = ((1u64 << big_n) - 1) as u32;
                // At gap 0 a non-opening turn is one pick, like the opening.
                let (p1, p2) = (gm.vd(full, 0, 0), gm.va(full, 0));
                println!("N={}: D as player 1 {}, as player 2 {}", big_n, outcome(p1), outcome(p2));
                if p1 < 0 || p2 < 0 { fails.push(big_n); }
            }
            println!("{{1..N}}, D <= {} picks, opponent <= {} picks, menu {}: D fails at {:?}", kd, ka, k, fails);
        }
        "blocks" => {
            let (p, a_lo, a_hi, kd, ka, k) = (n(1), n(2), n(3), n(4), n(5), opt(6));
            let g0 = (p % 2) as i64;
            let mut fails = vec![];
            for a in a_lo..=a_hi {
                let mut gm = G::new((a as i64..(a + 2 * p) as i64).collect(), kd, ka, k);
                let full = ((1u64 << (2 * p)) - 1) as u32;
                let (mov, oth) = (gm.vd(full, g0, 0), gm.va(full, g0));
                if mov < 0 || oth < 0 { fails.push((a, outcome(mov), outcome(oth))); }
            }
            println!("p={} blocks a in {}..={}, D <= {} picks, opponent <= {} picks, menu {}: D fails at (a, mover, other) {:?}", p, a_lo, a_hi, kd, ka, k, fails);
        }
        "ranges" => {
            let (lo, hi_max, gap, kd, ka, k) = (n(1), n(2), n(3) as i64, n(4), n(5), opt(6));
            let mut fails = vec![];
            for hi in lo..=hi_max {
                if ((lo..=hi).sum::<usize>() as i64 + gap) % 2 != 0 { continue; }
                let mut gm = G::new((lo as i64..=hi as i64).collect(), kd, ka, k);
                let full = ((1u64 << (hi - lo + 1)) - 1) as u32;
                let (mov, oth) = (gm.vd(full, gap, 0), gm.va(full, gap));
                println!("{{{}..{}}} at gap {}: D as mover {}, as the other {}", lo, hi, gap, outcome(mov), outcome(oth));
                if mov < 0 || oth < 0 { fails.push(hi); }
            }
            println!("{{{}..hi}} at gap {}, D <= {} picks, opponent <= {} picks, menu {}: D fails at hi = {:?}", lo, gap, kd, ka, k, fails);
        }
        _ => panic!("usage: turn_cap intervals <n_max> <kd> <ka> [k] | blocks <p> <a_lo> <a_hi> <kd> <ka> [k]"),
    }
}
