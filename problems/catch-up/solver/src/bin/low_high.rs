// Can the defender play from the bottom while the set is low (B35)? Real Catch-Up on {1..N} at gap 0,
// even totals. D picks only among the k smallest numbers left while the set is low, min < (num/den)·span
// (span = max − min); once high, among the t largest (t = 0: any). The opponent is free. Prints D's
// outcome as player 1 and as player 2 per N.
// Usage: low_high <n_max> <k> <num> <den> <t>. Dense memo [mask][gap], outcomes only.

const UNKNOWN: i8 = 2;

struct G { n: usize, k: usize, num: i64, den: i64, t: usize, md: Vec<i8>, ma: Vec<i8> }

impl G {
    // Number b + 1 sits at bit b.
    fn sum(mask: u32) -> i64 { (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64 + 1).sum() }
    fn menu(&self, mask: u32) -> u32 {
        let (lo, hi) = (mask.trailing_zeros() as i64 + 1, 32 - mask.leading_zeros() as i64);
        let (count, mut m) = (if lo * self.den < self.num * (hi - lo) { self.k } else { self.t }, mask);
        if count == 0 { return mask; }
        let mut out = 0u32;
        if lo * self.den < self.num * (hi - lo) {
            for _ in 0..count { if m != 0 { out |= m & m.wrapping_neg(); m &= m - 1; } }
        } else {
            for _ in 0..count { if m != 0 { let b = 1u32 << (31 - m.leading_zeros()); out |= b; m &= !b; } }
        }
        out
    }
    // D to move, trailing by g: 1 win, 0 draw, -1 loss for D.
    fn vd(&mut self, mask: u32, g: i64) -> i8 {
        if mask == 0 { return if g > 0 { -1 } else { 0 }; }
        if Self::sum(mask) < g { return -1; }
        let key = mask as usize * (self.n + 1) + g as usize;
        if self.md[key] != UNKNOWN { return self.md[key]; }
        let al = self.menu(mask);
        let mut best = -1;
        for b in 0..self.n as u32 {
            if al >> b & 1 == 0 { continue; }
            let x = b as i64 + 1;
            let r = mask & !(1 << b);
            let v = if x >= g { self.va(r, x - g) } else { self.vd(r, g - x) };
            if v > best { best = v; if best == 1 { break; } }
        }
        self.md[key] = best;
        best
    }
    // The opponent to move, trailing by g.
    fn va(&mut self, mask: u32, g: i64) -> i8 {
        if mask == 0 { return if g > 0 { 1 } else { 0 }; }
        if Self::sum(mask) < g { return 1; }
        let key = mask as usize * (self.n + 1) + g as usize;
        if self.ma[key] != UNKNOWN { return self.ma[key]; }
        let mut worst = 1;
        for b in 0..self.n as u32 {
            if mask >> b & 1 == 0 { continue; }
            let x = b as i64 + 1;
            let r = mask & !(1 << b);
            let v = if x >= g { self.vd(r, x - g) } else { self.va(r, g - x) };
            if v < worst { worst = v; if worst == -1 { break; } }
        }
        self.ma[key] = worst;
        worst
    }
}

fn outcome(v: i8) -> char { ['L', 'D', 'W'][(v + 1) as usize] }

fn main() {
    let a: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (n_max, k, num, den, t) = (a[0] as usize, a[1] as usize, a[2], a[3], a[4] as usize);
    let mut fails = vec![];
    for n in 1..=n_max {
        if (n * (n + 1) / 2) % 2 != 0 { continue; }
        let size = (1usize << n) * (n + 1);
        let mut gm = G { n, k, num, den, t, md: vec![UNKNOWN; size], ma: vec![UNKNOWN; size] };
        let full = ((1u64 << n) - 1) as u32;
        // At gap 0 a non-opening turn is one pick, like the opening.
        let (p1, p2) = (gm.vd(full, 0), gm.va(full, 0));
        println!("N={}: D as player 1 {}, as player 2 {}", n, outcome(p1), outcome(p2));
        if p1 < 0 || p2 < 0 { fails.push(n); }
    }
    println!("bottom {} while min < {}/{}·span, then top {} (0 = any): D fails at {:?}", k, num, den, t, fails);
}
