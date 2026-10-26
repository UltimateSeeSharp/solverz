//! Usage: max_strategy [universe] [max_lead] [max|amx|amt]   (defaults 18, 6, max)
//! Rounds game (B20, rounds_game.rs). Player Z follows a greedy strategy, a perfect opponent minimizes Z's final
//! margin. Reports the least final margin per start type and pair count, over pair sets (unions of disjoint
//! {x, x+1}) containing 0 within {0..U−1}. Starts: Z the mover trailing by 0 or 1; Z the non-mover leading by l.
//! - max: always take the largest number left. Claim L15: margin ≥ −1 from every start listed; with parity
//!   (margin ≡ debt + pairs) always-max draws at debt p mod 2 in both roles.
//! - amx (B25, ideator): as max, except as second picker: if taking the largest number m would leave no
//!   half-taken pair and a tie with the opponent to move again, take the high of the highest other intact pair.
//!   Targets: t_p at debts 0 and 1 in both roles (the forced wins included) and margin ≥ 0 as leader by l ≥ 1.
//! - amt (B26): as max, except as second picker: if the largest number would give an exact tie (the opponent
//!   keeps the move), take the second largest. Targets as amx.
//! Also reports the intervals {0..2p−1} at every debt d ≤ p + 1 in both roles against t_p (T1).

use std::collections::HashMap;
use std::time::Instant;

const DEFAULT_UNIVERSE: u32 = 18;
const DEFAULT_LEAD: i64 = 6;

#[derive(Clone, Copy, PartialEq)]
enum Rule {
    Max,
    Amx,
    Amt,
}

struct Greedy {
    rule: Rule,
    lows: u32, // the lower number of each pair of the current set
    memo: HashMap<(u32, i64, bool), i64>,
}

impl Greedy {
    fn orphan_free(&self, mask: u32) -> bool {
        (mask & self.lows) << 1 == mask & !self.lows
    }

    /// Z's reply as second picker to the opponent's pick, `m1` = numbers left after it.
    fn reply(&self, m1: u32, s: i64, opp_pick: u32) -> u32 {
        let top = 31 - m1.leading_zeros();
        let tie = s + top as i64 - opp_pick as i64 == 0;
        if self.rule == Rule::Amt && tie && m1.count_ones() > 1 {
            return 31 - (m1 & !(1 << top)).leading_zeros();
        }
        if self.rule == Rule::Amx && tie && self.orphan_free(m1 & !(1 << top)) {
            let partner = |v: u32| if self.lows >> v & 1 == 1 { v + 1 } else { v - 1 };
            let mut v = top;
            while v > 0 {
                v -= 1;
                let intact_high = self.lows >> v & 1 == 0 && m1 >> v & 1 == 1 && m1 >> (v - 1) & 1 == 1;
                if intact_high && v != top && partner(v) != top {
                    return v;
                }
            }
        }
        top
    }

    /// Z's final margin under perfect minimization; `s` = Z's signed margin, `z_moves` = Z picks first this round.
    fn margin(&mut self, mask: u32, s: i64, z_moves: bool) -> i64 {
        if mask == 0 {
            return s;
        }
        if let Some(&v) = self.memo.get(&(mask, s, z_moves)) {
            return v;
        }
        let mut worst = i64::MAX;
        // The next round's mover: the player behind; a tie keeps this round's mover.
        let next = |s2: i64| if s2 == 0 { z_moves } else { s2 < 0 };
        if z_moves {
            let top = 31 - mask.leading_zeros();
            let m1 = mask & !(1 << top);
            let mut r = m1;
            while r != 0 {
                let j = r.trailing_zeros();
                r &= r - 1;
                let s2 = s + top as i64 - j as i64;
                worst = worst.min(self.margin(m1 & !(1 << j), s2, next(s2)));
            }
        } else {
            let mut rest = mask;
            while rest != 0 {
                let i = rest.trailing_zeros();
                rest &= rest - 1;
                let m1 = mask & !(1 << i);
                let j = self.reply(m1, s, i);
                let s2 = s + j as i64 - i as i64;
                worst = worst.min(self.margin(m1 & !(1 << j), s2, next(s2)));
            }
        }
        self.memo.insert((mask, s, z_moves), worst);
        worst
    }
}

fn pair_sets(u: u32, lo: u32, acc: u32, out: &mut Vec<u32>) {
    if acc != 0 {
        out.push(acc);
    }
    for x in lo..u.saturating_sub(1) {
        pair_sets(u, x + 2, acc | 3 << x, out);
    }
}

fn lows_of(set: u32) -> u32 {
    let (mut m, mut lows) = (set, 0u32);
    while m != 0 {
        let x = m.trailing_zeros();
        lows |= 1 << x;
        m &= !(3 << x);
    }
    lows
}

/// Least margin Z needs: t_p at debts 0, 1 in both roles; ≥ 0 as leader by l ≥ 1 (amx, amt).
fn target(p: usize, kind: usize) -> i64 {
    let odd = p % 2 == 1;
    match kind {
        0 => if odd { 1 } else { 0 },        // mover at 0: W (p odd) or D
        1 => if odd { 0 } else { i64::MIN }, // mover at 1: D (p odd) or L
        2 => if odd { i64::MIN } else { 0 }, // leader by 0: mover W (p odd) or D
        3 => if odd { 0 } else { 1 },        // leader by 1: mover D (p odd) or L
        _ => 0,
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let u: u32 = args.next().map(|a| a.parse().expect("universe")).unwrap_or(DEFAULT_UNIVERSE);
    let max_lead: i64 = args.next().map(|a| a.parse().expect("lead")).unwrap_or(DEFAULT_LEAD);
    let rule = match args.next().as_deref() {
        None | Some("max") => Rule::Max,
        Some("amx") => Rule::Amx,
        Some("amt") => Rule::Amt,
        Some(other) => panic!("strategy max, amx or amt, not {other}"),
    };
    let targeted = rule != Rule::Max;
    assert!(u <= 31);
    let start = Instant::now();
    let mut sets = Vec::new();
    pair_sets(u, 0, 0, &mut sets);
    sets.retain(|m| m & 1 == 1);
    let mut g = Greedy { rule, lows: 0, memo: HashMap::new() };
    // least[p][k]: k = 0, 1 mover trailing by k; k = 2 + l non-mover leading by l
    let kinds = 2 + (max_lead as usize + 1);
    let mut least = vec![vec![i64::MAX; kinds]; (u / 2 + 1) as usize];
    let mut example = vec![vec![0u32; kinds]; (u / 2 + 1) as usize];
    let mut states = 0usize;
    for &m in &sets {
        let p = (m.count_ones() / 2) as usize;
        if rule == Rule::Amx {
            // the reply depends on the pairing, so states are not shared across sets
            states += g.memo.len();
            g.memo.clear();
            g.lows = lows_of(m);
        } else {
            g.lows = lows_of(m) | !m; // unused by max and amt
        }
        for k in 0..kinds {
            let v = if k < 2 { g.margin(m, -(k as i64), true) } else { g.margin(m, (k - 2) as i64, false) };
            if v < least[p][k] {
                least[p][k] = v;
                example[p][k] = m;
            }
        }
    }
    states += g.memo.len();
    let name = match rule {
        Rule::Max => "max",
        Rule::Amx => "amx",
        Rule::Amt => "amt",
    };
    println!("# max_strategy {u} {max_lead} {name}\n");
    println!("{} pair sets containing 0 within {{0..{}}}; {states} memo states; {:.1} s\n", sets.len(), u - 1, start.elapsed().as_secs_f64());
    print!("| p | mover, debt 0 | mover, debt 1 |");
    for l in 0..=max_lead {
        print!(" leader by {l} |");
    }
    println!("\n|---|---|---|{}", "---|".repeat(max_lead as usize + 1));
    let mut fails = Vec::new();
    for p in 1..least.len() {
        print!("| {p} |");
        for k in 0..kinds {
            let need = if targeted { target(p, k) } else { -1 };
            if least[p][k] < need {
                fails.push((p, k));
            }
            print!(" {} |", least[p][k]);
        }
        println!();
    }
    let what = if targeted { "below its target (t_p at debts 0, 1; ≥ 0 as leader by l ≥ 1)" } else { "with least margin < −1" };
    println!("\nStarts {what}: {}", fails.len());
    for (p, k) in fails {
        let xs: Vec<u32> = (0..u).filter(|&b| example[p][k] >> b & 1 == 1).collect();
        println!("- p = {p}, start {k}: {xs:?}");
    }
    interval_rows(&mut g, u / 2);
}

/// T1: least margin on {0..2p−1} as mover at debt d and as leader by d, d ≤ p + 1; misses against t_p.
fn interval_rows(g: &mut Greedy, max_p: u32) {
    const NONE: i64 = i64::MIN;
    println!("
Intervals {{0..2p−1}}: least margin as mover at debt d / as leader by d (t_p(d) in brackets)
");
    let mut misses = Vec::new();
    for p in 1..=max_p {
        let m = (1u32 << (2 * p)) - 1;
        if g.rule == Rule::Amx {
            g.memo.clear();
        }
        g.lows = 0x5555_5555 & m;
        let mut row = format!("- p = {p}:");
        for d in 0..=(p as i64 + 1) {
            let t = if d <= p as i64 && d % 2 == p as i64 % 2 { 'D' } else if d == 0 { 'W' } else { 'L' };
            let mover = g.margin(m, -d, true);
            let leader = g.margin(m, d, false);
            let (need_mover, need_leader) = match t {
                'W' => (1, NONE),
                'D' => (0, 0),
                _ => (NONE, 1),
            };
            if mover < need_mover || leader < need_leader {
                misses.push((p, d));
            }
            row += &format!(" {d}[{t}] {mover}/{leader};");
        }
        println!("{row}");
    }
    println!("
Interval starts missing t_p: {} {:?}", misses.len(), misses);
}
