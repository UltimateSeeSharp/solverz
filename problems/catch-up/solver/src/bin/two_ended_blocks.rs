// Do two-ended menus draw even blocks (B35)? Real Catch-Up on {a..a+2p-1} at debt g0 = p mod 2: the
// defender D picks only among the k smallest and k largest numbers left, the opponent anything. Prints
// D's minimax final margin as mover trailing by g0 and as the other player leading by g0, per height.
// Usage: two_ended_blocks <p> <a_lo> <a_hi> <k>. Dense memo [mask][gap], gap < 64.

const UNKNOWN: i16 = i16::MIN;
const GMAX: usize = 64;
struct G { nums: Vec<i64>, k: usize, md: Vec<i16>, ma: Vec<i16> }
impl G {
    fn allowed(&self, mask: u32) -> u32 {
        let idx: Vec<u32> = (0..self.nums.len() as u32).filter(|&b| mask >> b & 1 == 1).collect();
        let lo = idx.iter().take(self.k).fold(0, |m, &b| m | 1 << b);
        let hi = idx.iter().rev().take(self.k).fold(0, |m, &b| m | 1 << b);
        lo | hi
    }
    fn sum(&self, mask: u32) -> i64 { (0..self.nums.len()).filter(|&b| mask >> b & 1 == 1).map(|b| self.nums[b]).sum() }
    // D to move, trailing by g; returns D's final margin.
    fn vd(&mut self, mask: u32, g: i64) -> i64 {
        if mask == 0 { return -g; }
        let t = self.sum(mask);
        if t < g { return t - g; }
        let key = mask as usize * GMAX + g as usize;
        if self.md[key] != UNKNOWN { return self.md[key] as i64; }
        let al = self.allowed(mask);
        let mut best = i64::MIN;
        for b in 0..self.nums.len() as u32 {
            if al >> b & 1 == 0 { continue; }
            let x = self.nums[b as usize];
            let r = mask & !(1 << b);
            let o = if x >= g { self.va(r, x - g) } else { self.vd(r, g - x) };
            best = best.max(o);
        }
        self.md[key] = best as i16;
        best
    }
    // A to move, trailing by g; returns D's final margin.
    fn va(&mut self, mask: u32, g: i64) -> i64 {
        if mask == 0 { return g; }
        let t = self.sum(mask);
        if t < g { return g - t; }
        let key = mask as usize * GMAX + g as usize;
        if self.ma[key] != UNKNOWN { return self.ma[key] as i64; }
        let mut worst = i64::MAX;
        for b in 0..self.nums.len() as u32 {
            if mask >> b & 1 == 0 { continue; }
            let x = self.nums[b as usize];
            let r = mask & !(1 << b);
            let o = if x >= g { self.vd(r, x - g) } else { self.va(r, g - x) };
            worst = worst.min(o);
        }
        self.ma[key] = worst as i16;
        worst
    }
}
fn main() {
    let args: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (p, a_lo, a_hi, k) = (args[0] as usize, args[1], args[2], args[3] as usize);
    let n = 2 * p;
    let g0 = (p % 2) as i64;
    let mut fails = vec![];
    for a in a_lo..=a_hi {
        assert!(a + n as i64 - 1 < GMAX as i64, "gaps must stay below GMAX");
        let nums: Vec<i64> = (a..a + n as i64).collect();
        let mut gm = G { nums, k, md: vec![UNKNOWN; (1usize << n) * GMAX], ma: vec![UNKNOWN; (1usize << n) * GMAX] };
        let full = ((1u64 << n) - 1) as u32;
        let mov = gm.vd(full, g0);
        let oth = gm.va(full, g0);
        println!("p={} a={} tb{}: mover margin {}, other margin {}", p, a, k, mov, oth);
        if mov < 0 || oth < 0 { fails.push(a); }
    }
    println!("p={} tb{} a in {}..={}: D fails at {:?}", p, k, a_lo, a_hi, fails);
}
