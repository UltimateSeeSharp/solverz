//! Usage: max_strategy [universe] [max_lead]   (defaults 18, 6)
//! Rounds game (B20, rounds_game.rs). Player Z always takes the largest number left, a perfect opponent
//! minimizes Z's final margin. Claim AM: on every pair set (union of disjoint {x, x+1}), Z's final margin
//! is ≥ −1 when Z starts as the mover trailing by 0 or 1, or as the non-mover leading by 0..max_lead.
//! With parity (margin ≡ debt + pairs), always-max then draws at debt p mod 2 in both roles.
//! Reports the least final margin per start type and pair count, over pair sets containing 0 within {0..U−1}.

use std::collections::HashMap;
use std::time::Instant;

const DEFAULT_UNIVERSE: u32 = 18;
const DEFAULT_LEAD: i64 = 6;

/// Z's final margin under perfect minimization; `s` = Z's signed margin, `z_moves` = Z picks first this round.
fn margin(mask: u32, s: i64, z_moves: bool, memo: &mut HashMap<(u32, i64, bool), i64>) -> i64 {
    if mask == 0 {
        return s;
    }
    if let Some(&v) = memo.get(&(mask, s, z_moves)) {
        return v;
    }
    let top = 31 - mask.leading_zeros();
    let mut worst = i64::MAX;
    let mut rest = mask;
    // The next round's mover: the player behind; a tie keeps this round's mover.
    let next = |s2: i64| if s2 == 0 { z_moves } else { s2 < 0 };
    if z_moves {
        let m1 = mask & !(1 << top);
        let mut r = m1;
        while r != 0 {
            let j = r.trailing_zeros();
            r &= r - 1;
            let s2 = s + top as i64 - j as i64;
            worst = worst.min(margin(m1 & !(1 << j), s2, next(s2), memo));
        }
    } else {
        while rest != 0 {
            let i = rest.trailing_zeros();
            rest &= rest - 1;
            let m1 = mask & !(1 << i);
            let j = 31 - m1.leading_zeros();
            let s2 = s + j as i64 - i as i64;
            worst = worst.min(margin(m1 & !(1 << j), s2, next(s2), memo));
        }
    }
    memo.insert((mask, s, z_moves), worst);
    worst
}

fn pair_sets(u: u32, lo: u32, acc: u32, out: &mut Vec<u32>) {
    if acc != 0 {
        out.push(acc);
    }
    for x in lo..u.saturating_sub(1) {
        pair_sets(u, x + 2, acc | 3 << x, out);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let u: u32 = args.next().map(|a| a.parse().expect("universe")).unwrap_or(DEFAULT_UNIVERSE);
    let max_lead: i64 = args.next().map(|a| a.parse().expect("lead")).unwrap_or(DEFAULT_LEAD);
    assert!(u <= 31);
    let start = Instant::now();
    let mut sets = Vec::new();
    pair_sets(u, 0, 0, &mut sets);
    sets.retain(|m| m & 1 == 1);
    let mut memo = HashMap::new();
    // least[p][k]: k = 0, 1 mover trailing by k; k = 2 + l non-mover leading by l
    let kinds = 2 + (max_lead as usize + 1);
    let mut least = vec![vec![i64::MAX; kinds]; (u / 2 + 1) as usize];
    let mut example = vec![vec![0u32; kinds]; (u / 2 + 1) as usize];
    for &m in &sets {
        let p = (m.count_ones() / 2) as usize;
        for k in 0..kinds {
            let v = if k < 2 { margin(m, -(k as i64), true, &mut memo) } else { margin(m, (k - 2) as i64, false, &mut memo) };
            if v < least[p][k] {
                least[p][k] = v;
                example[p][k] = m;
            }
        }
    }
    println!("# max_strategy {u} {max_lead}\n");
    println!("{} pair sets containing 0 within {{0..{}}}; {} memo states; {:.1} s\n", sets.len(), u - 1, memo.len(), start.elapsed().as_secs_f64());
    print!("| p | mover, debt 0 | mover, debt 1 |");
    for l in 0..=max_lead {
        print!(" leader by {l} |");
    }
    println!("\n|---|---|---|{}", "---|".repeat(max_lead as usize + 1));
    let mut fails = 0;
    for p in 1..least.len() {
        print!("| {p} |");
        for k in 0..kinds {
            if least[p][k] < -1 {
                fails += 1;
            }
            print!(" {} |", least[p][k]);
        }
        println!();
    }
    println!("\nStarts with least margin < −1: {fails}");
    for p in 1..least.len() {
        for k in 0..kinds {
            if least[p][k] < -1 {
                let xs: Vec<u32> = (0..u).filter(|&b| example[p][k] >> b & 1 == 1).collect();
                println!("- p = {p}, start {k}: {xs:?}");
            }
        }
    }
}
