// Can the defender play from the bottom while the set is low (B35)? Real Catch-Up on {1..N} at gap 0,
// even totals. D picks only among the k smallest numbers left while the set is low, min < (num/den)·span
// (span = max − min); once high, among the t largest (t = 0: any), or by Hyb2 (t = h): with an odd
// number left D answers with the smallest pick j leaving the opponent behind by ≥ c of what is left
// (C20's matching cost), else the largest; with an even number left it takes the largest. The opponent
// is free. Prints D's outcome as player 1 and as player 2 per N.
// Usage: low_high <n_max> <k> <num> <den> <t|h>. Dense memo [mask][gap], outcomes only.

const UNKNOWN: i8 = 2;

struct G { n: usize, k: usize, num: i64, den: i64, t: usize, hyb2: bool, md: Vec<i8>, ma: Vec<i8> }

impl G {
    // Number b + 1 sits at bit b.
    fn sum(mask: u32) -> i64 { (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64 + 1).sum() }
    // C20's matching cost: sorted numbers paired bottom-up.
    fn cost(mask: u32) -> i64 {
        let xs: Vec<i64> = (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64 + 1).collect();
        xs.chunks(2).map(|c| if c.len() == 2 { c[1] - c[0] } else { 0 }).sum()
    }
    // Hyb2's pick on a high set, D trailing by g.
    fn hyb2(mask: u32, g: i64) -> u32 {
        let top = 31 - mask.leading_zeros();
        if mask.count_ones() % 2 == 1 {
            for b in 0..32u32 {
                if mask >> b & 1 == 0 { continue; }
                let lead = b as i64 + 1 - g;
                if lead >= 0 && lead >= Self::cost(mask & !(1 << b)) { return 1 << b; }
            }
        }
        1 << top
    }
    fn menu(&self, mask: u32, g: i64) -> u32 {
        let (lo, hi) = (mask.trailing_zeros() as i64 + 1, 32 - mask.leading_zeros() as i64);
        if self.hyb2 && lo * self.den >= self.num * (hi - lo) { return Self::hyb2(mask, g); }
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
        let al = self.menu(mask, g);
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
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let hyb2 = raw[4] == "h";
    let a: Vec<i64> = raw.iter().map(|s| if s == "h" { 0 } else { s.parse().unwrap() }).collect();
    let (n_max, k, num, den, t) = (a[0] as usize, a[1] as usize, a[2], a[3], a[4] as usize);
    let mut fails = vec![];
    for n in 1..=n_max {
        if (n * (n + 1) / 2) % 2 != 0 { continue; }
        let size = (1usize << n) * (n + 1);
        let mut gm = G { n, k, num, den, t, hyb2, md: vec![UNKNOWN; size], ma: vec![UNKNOWN; size] };
        let full = ((1u64 << n) - 1) as u32;
        // At gap 0 a non-opening turn is one pick, like the opening.
        let (p1, p2) = (gm.vd(full, 0), gm.va(full, 0));
        println!("N={}: D as player 1 {}, as player 2 {}", n, outcome(p1), outcome(p2));
        if p1 < 0 || p2 < 0 { fails.push(n); }
    }
    let high = if hyb2 { "Hyb2".to_string() } else if t == 0 { "any".to_string() } else { format!("top {}", t) };
    println!("bottom {} while min < {}/{}·span, then {}: D fails at {:?}", k, num, den, high, fails);
}
