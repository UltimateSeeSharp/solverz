//! Usage: top_reserve <from> <to> <q>...   |   top_reserve compare <from> <to> <q>
//! Can the defender leave the top block for last (I6, B16)? Γ_N(q): the top 2q numbers T = {N−2q+1..N}
//! split into pairs {N−2q+1, N−2q+2}, …; the defender may take x ∈ T only to close a pair the attacker
//! opened (x's partner gone) or when only T is left. The attacker is free. Prints player 1's value with
//! the defender as player 2 and as player 1 (the defender holds iff both are draws), per even-total N
//! and q; q = 0 is the free game. Two full tables (defender to move, attacker to move), one u64 row per
//! set: 2 bits per gap ≤ N (during play the mover trails by at most N).
//! `compare` (B17, Lemma A): Γ'_N(q) bars the attacker the same way. At every position with T intact,
//! do Γ and Γ' agree (both tables, gaps ≤ min(N, sum))? Also prints Γ' openings (Lemma B: T played last).

use catch_up::{Outcome, Solver};
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Instant;

const LOSS: u64 = 0;
const DRAW: u64 = 1;
const WIN: u64 = 2;
const BITS_PER_GAP: usize = 2;
const CELL: u64 = 0b11;
/// 2 bits per gap in one u64 row.
const MAX_N: usize = 31;
/// Free game (q = 0) checked against `Solver` on every set and gap up to this N.
const SOLVER_CHECK_N: usize = 12;
/// Restricted tables checked against a plain recursion up to this N.
const RECURSION_CHECK_N: usize = 8;
const MASKS_PER_TASK: usize = 4096;
const SHOWN: usize = 8;

fn neg(v: u64) -> u64 {
    WIN - v
}

fn cell(row: u64, g: usize) -> u64 {
    row >> (BITS_PER_GAP * g) & CELL
}

fn letter(v: u64) -> char {
    match v {
        LOSS => 'L',
        DRAW => 'D',
        _ => 'W',
    }
}

/// Numbers the restricted defender may take from `mask` (number x ↔ bit x − 1).
fn allowed(mask: usize, top: usize, q: usize) -> usize {
    let free = mask & !top;
    if free == 0 {
        return mask;
    }
    let base = top.trailing_zeros() as usize;
    let mut a = free;
    for j in 0..q {
        let pair = 0b11 << (base + 2 * j);
        let left = mask & pair;
        if left.count_ones() == 1 {
            a |= left;
        }
    }
    a
}

struct Game {
    n: usize,
    q: usize,
    top: usize,
    /// Γ': the attacker obeys the defender's rule too.
    attacker_restricted: bool,
    /// Rows with the restricted defender to move.
    def: Vec<AtomicU64>,
    /// Rows with the free attacker to move.
    att: Vec<AtomicU64>,
}

impl Game {
    fn new(n: usize, q: usize, attacker_restricted: bool) -> Self {
        let size = 1usize << n;
        let top = if q == 0 { 0 } else { ((1usize << (2 * q)) - 1) << (n - 2 * q) };
        let g = Game { n, q, top, attacker_restricted, def: (0..size).map(|_| AtomicU64::new(0)).collect(), att: (0..size).map(|_| AtomicU64::new(0)).collect() };
        g.def[0].store(DRAW, Relaxed);
        g.att[0].store(DRAW, Relaxed);
        g
    }

    fn solve(&self) {
        let binom = binomials(self.n);
        for k in 1..=self.n {
            let count = binom[self.n][k] as usize;
            (0..count.div_ceil(MASKS_PER_TASK)).into_par_iter().for_each(|t| {
                let mut mask = unrank(&binom, (t * MASKS_PER_TASK) as u64, k);
                for _ in 0..MASKS_PER_TASK.min(count - t * MASKS_PER_TASK) {
                    self.fill(mask);
                    mask = next_combination(mask);
                }
            });
        }
    }

    fn fill(&self, mask: usize) {
        let sum: usize = (0..self.n).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
        let mut picks = Vec::with_capacity(self.n);
        let mut m = mask;
        while m != 0 {
            let i = m.trailing_zeros() as usize;
            m &= m - 1;
            let r = mask & !(1 << i);
            picks.push((i + 1, self.def[r].load(Relaxed), self.att[r].load(Relaxed)));
        }
        let ok = allowed(mask, self.top, self.q);
        let ok_att = if self.attacker_restricted { ok } else { mask };
        let (mut def_row, mut att_row) = (0u64, 0u64);
        for g in 0..=self.n.min(sum) {
            let (mut bd, mut ba) = (LOSS, LOSS);
            for &(x, d, a) in &picks {
                // x ≥ g ends the turn: the other side moves trailing by x − g.
                let (vd, va) = if x >= g { (neg(cell(a, x - g)), neg(cell(d, x - g))) } else { (cell(d, g - x), cell(a, g - x)) };
                if ok >> (x - 1) & 1 == 1 {
                    bd = bd.max(vd);
                }
                if ok_att >> (x - 1) & 1 == 1 {
                    ba = ba.max(va);
                }
            }
            def_row |= bd << (BITS_PER_GAP * g);
            att_row |= ba << (BITS_PER_GAP * g);
        }
        self.def[mask].store(def_row, Relaxed);
        self.att[mask].store(att_row, Relaxed);
    }

    /// Player 1's value: (defender = player 2, defender = player 1). An opening is one pick at gap 0.
    fn openings(&self) -> (u64, u64) {
        let full = (1usize << self.n) - 1;
        let after = |x: usize, t: &[AtomicU64]| neg(cell(t[full & !(1 << (x - 1))].load(Relaxed), x));
        let opens = |x: usize| !self.attacker_restricted || allowed(full, self.top, self.q) >> (x - 1) & 1 == 1;
        let as_p2 = (1..=self.n).filter(|&x| opens(x)).map(|x| after(x, &self.def)).max().unwrap();
        let as_p1 = (1..=self.n).filter(|&x| allowed(full, self.top, self.q) >> (x - 1) & 1 == 1).map(|x| after(x, &self.att)).max().unwrap();
        (as_p2, as_p1)
    }
}

/// Plain recursion over the same rules, for checking small tables.
fn recurse(n: usize, top: usize, q: usize, mask: usize, g: usize, defender: bool) -> u64 {
    if mask == 0 {
        return if g == 0 { DRAW } else { LOSS };
    }
    let sum: usize = (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
    if g > sum {
        return LOSS;
    }
    let ok = if defender { allowed(mask, top, q) } else { mask };
    (0..n)
        .filter(|&i| ok >> i & 1 == 1)
        .map(|i| {
            let (x, r) = (i + 1, mask & !(1 << i));
            if x >= g { neg(recurse(n, top, q, r, x - g, !defender)) } else { recurse(n, top, q, r, g - x, defender) }
        })
        .max()
        .unwrap()
}

fn binomials(n: usize) -> Vec<Vec<u64>> {
    let mut b = vec![vec![0u64; n + 2]; n + 2];
    for p in 0..=n + 1 {
        b[p][0] = 1;
        for i in 1..=p {
            b[p][i] = b[p - 1][i - 1] + if i < p { b[p - 1][i] } else { 0 };
        }
    }
    b
}

/// The r-th mask with k bits in colex order.
fn unrank(binom: &[Vec<u64>], mut r: u64, k: usize) -> usize {
    let mut mask = 0usize;
    for i in (1..=k).rev() {
        let mut c = i - 1;
        while binom[c + 1][i] <= r {
            c += 1;
        }
        mask |= 1 << c;
        r -= binom[c][i];
    }
    mask
}

/// Next larger mask with the same number of bits (Gosper's hack).
fn next_combination(x: usize) -> usize {
    let c = x & x.wrapping_neg();
    let r = x + c;
    (((r ^ x) >> 2) / c) | r
}

/// B17: Γ against Γ' at every position with T intact.
fn compare(from: usize, to: usize, q: usize) {
    println!("# top_reserve compare {from}..{to}, q = {q}
");
    println!("Positions (set ⊇ T, gap ≤ min(N, sum)) where Γ (free attacker) and Γ' (attacker barred too) differ; Γ' openings as in the main mode. Examples: payable positions only.
");
    println!("Payable: the gap is at most the sum of the numbers left outside T, so nobody is forced into T.
");
    println!("| N | positions | differ, defender to move | differ, attacker to move | payable positions | payable, differ D | payable, differ A | Γ' openings |
|---|---|---|---|---|---|---|---|");
    let mut examples = Vec::new();
    for n in from..=to {
        if n * (n + 1) / 2 % 2 == 1 || 2 * q >= n {
            continue;
        }
        let start = Instant::now();
        let (free, barred) = (Game::new(n, q, false), Game::new(n, q, true));
        free.solve();
        barred.solve();
        if n <= RECURSION_CHECK_N {
            for mask in 0..1usize << n {
                for g in 0..=n {
                    assert_eq!(cell(barred.att[mask].load(Relaxed), g), recurse_barred(n, barred.top, q, mask, g), "N = {n}, mask {mask:b}, g = {g}");
                }
            }
        }
        let (mut positions, mut diff_def, mut diff_att) = (0u64, 0u64, 0u64);
        let (mut payable, mut pay_def, mut pay_att) = (0u64, 0u64, 0u64);
        for mask in 0..1usize << n {
            if mask & free.top != free.top {
                continue;
            }
            let sum: usize = (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
            let low: usize = (0..n).filter(|&i| (mask & !free.top) >> i & 1 == 1).map(|i| i + 1).sum();
            for g in 0..=n.min(sum) {
                positions += 1;
                if g <= low {
                    payable += 1;
                    let differs = |a: &[AtomicU64], b: &[AtomicU64]| cell(a[mask].load(Relaxed), g) != cell(b[mask].load(Relaxed), g);
                    pay_def += differs(&free.def, &barred.def) as u64;
                    pay_att += differs(&free.att, &barred.att) as u64;
                }
                for (a, b, count, side) in [(&free.def, &barred.def, &mut diff_def, "D"), (&free.att, &barred.att, &mut diff_att, "A")] {
                    let (x, y) = (cell(a[mask].load(Relaxed), g), cell(b[mask].load(Relaxed), g));
                    if x != y {
                        *count += 1;
                        if g <= low && examples.len() < SHOWN {
                            let xs: Vec<String> = (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| (i + 1).to_string()).collect();
                            examples.push(format!("N = {n}, {side} to move, {{{}}} at g = {g}: Γ {} vs Γ' {}", xs.join(","), letter(x), letter(y)));
                        }
                    }
                }
            }
        }
        let (a, b) = barred.openings();
        eprintln!("N = {n}: {:.1} s", start.elapsed().as_secs_f64());
        println!("| {n} | {positions} | {diff_def} | {diff_att} | {payable} | {pay_def} | {pay_att} | {}{} |", letter(a), letter(b));
    }
    println!();
    for e in examples {
        println!("- {e}");
    }
}

/// Plain recursion with both sides barred.
fn recurse_barred(n: usize, top: usize, q: usize, mask: usize, g: usize) -> u64 {
    fn go(n: usize, top: usize, q: usize, mask: usize, g: usize) -> u64 {
        if mask == 0 {
            return if g == 0 { DRAW } else { LOSS };
        }
        let sum: usize = (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
        if g > sum {
            return LOSS;
        }
        let ok = allowed(mask, top, q);
        (0..n)
            .filter(|&i| ok >> i & 1 == 1)
            .map(|i| {
                let (x, r) = (i + 1, mask & !(1 << i));
                if x >= g { neg(go(n, top, q, r, x - g)) } else { go(n, top, q, r, g - x) }
            })
            .max()
            .unwrap()
    }
    go(n, top, q, mask, g)
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("compare") {
        let a: Vec<usize> = std::env::args().skip(2).map(|a| a.parse().expect("numbers")).collect();
        assert!(a.len() == 3 && a[1] <= MAX_N, "usage: top_reserve compare <from> <to> <q>");
        return compare(a[0], a[1], a[2]);
    }
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("numbers")).collect();
    assert!(args.len() >= 3, "usage: top_reserve <from> <to> <q>...");
    let (from, to, qs) = (args[0], args[1], &args[2..]);
    assert!(to <= MAX_N, "N ≤ {MAX_N}");
    println!("# top_reserve {from}..{to}, q = {qs:?}\n");
    println!("Player 1's value (defender = player 2, defender = player 1); the defender holds iff DD.\n");
    println!("| N | {} |\n|---|{}", qs.iter().map(|q| format!("q = {q}")).collect::<Vec<_>>().join(" | "), "---|".repeat(qs.len()));
    for n in from..=to {
        if n * (n + 1) / 2 % 2 == 1 {
            continue;
        }
        let mut cells = Vec::new();
        for &q in qs {
            if 2 * q >= n {
                cells.push("—".to_string());
                continue;
            }
            let start = Instant::now();
            let game = Game::new(n, q, false);
            game.solve();
            if q == 0 && n <= SOLVER_CHECK_N {
                let mut s = Solver::new(&(1..=n as u64).collect::<Vec<_>>());
                for mask in 0..1usize << n {
                    let sum: usize = (0..n).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
                    for g in 0..=n.min(sum) {
                        let want = match s.position(mask, g as u64) {
                            Outcome::Loss => LOSS,
                            Outcome::Draw => DRAW,
                            Outcome::Win => WIN,
                        };
                        let row = |t: &[AtomicU64]| cell(t[mask].load(Relaxed), g);
                        assert!(row(&game.def) == want && row(&game.att) == want, "N = {n}, mask {mask:b}, g = {g}");
                    }
                }
            }
            if n <= RECURSION_CHECK_N {
                for mask in 0..1usize << n {
                    for g in 0..=n {
                        for (t, defender) in [(&game.def, true), (&game.att, false)] {
                            assert_eq!(cell(t[mask].load(Relaxed), g), recurse(n, game.top, q, mask, g, defender), "N = {n}, q = {q}, mask {mask:b}, g = {g}");
                        }
                    }
                }
            }
            let (a, b) = game.openings();
            eprintln!("N = {n}, q = {q}: {:.1} s", start.elapsed().as_secs_f64());
            cells.push(format!("{}{}", letter(a), letter(b)));
        }
        println!("| {n} | {} |", cells.join(" | "));
    }
}
