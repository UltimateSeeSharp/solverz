// Does a two-ended defender draw {1..N} (B35)? Real Catch-Up on {1..N} at gap 0, even totals: the
// defender D picks only among the k smallest and k largest numbers left, the opponent anything. Prints
// D's minimax final margin as player 1 (D opens) and as player 2, per N.
// Usage: two_ended_intervals <n_max> <k>. Dense memo [mask][gap], gap < 32.

const UNKNOWN: i16 = i16::MIN;
const GMAX: usize = 32;

struct G { nums: Vec<i64>, k: usize, md: Vec<i16>, ma: Vec<i16> }

impl G {
    // Bit b holds nums[b], sorted ascending: the k lowest and the k highest set bits.
    fn allowed(&self, mask: u32) -> u32 {
        let (mut lo, mut hi, mut m, mut n) = (0u32, 0u32, mask, mask);
        for _ in 0..self.k {
            if m != 0 { lo |= m & m.wrapping_neg(); m &= m - 1; }
            if n != 0 { let b = 1u32 << (31 - n.leading_zeros()); hi |= b; n &= !b; }
        }
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
    let args: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (n_max, k) = (args[0], args[1]);
    let mut fails = vec![];
    for n in 1..=n_max {
        if (n * (n + 1) / 2) % 2 != 0 { continue; }
        assert!(n < GMAX, "gaps must stay below GMAX");
        let nums: Vec<i64> = (1..=n as i64).collect();
        let mut gm = G { nums, k, md: vec![UNKNOWN; (1usize << n) * GMAX], ma: vec![UNKNOWN; (1usize << n) * GMAX] };
        let full = ((1u64 << n) - 1) as u32;
        // At gap 0 a non-opening turn is one pick, like the opening.
        let (p1, p2) = (gm.vd(full, 0), gm.va(full, 0));
        println!("N={} tb{}: D as player 1 margin {}, as player 2 margin {}", n, k, p1, p2);
        if p1 < 0 || p2 < 0 { fails.push(n); }
    }
    println!("tb{} on {{1..N}}, even totals N <= {}: D fails at {:?}", k, n_max, fails);
}
