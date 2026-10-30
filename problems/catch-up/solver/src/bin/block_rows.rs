//! Usage: block_rows [max_pairs] [max_height]   (defaults 8, 80)
//! Even blocks at any height (I7, B19). B(a, p) = {a..a+2p−1}, g0 = p mod 2. TI: V(B, g0) = draw.
//! t_p(g) = draw if g ≤ p and g ≡ p (mod 2); win if g = 0 and p odd; loss otherwise.
//! Per p: blocks where TI fails; the least a0 such that every a0 ≤ a ≤ max_height has row = t_p at
//! all g < a; blocks whose draws miss a draw-parity g ≤ p; the rows themselves at small a.

use catch_up::{Outcome, Solver};
use std::time::Instant;

const DEFAULT_PAIRS: u64 = 8;
const DEFAULT_HEIGHT: u64 = 80;
/// Rows printed in full for a ≤ this, over g ≤ min(sum, ROW_SPAN_FACTOR · p + 4).
const PRINTED_HEIGHT: u64 = 12;
const ROW_SPAN_FACTOR: u64 = 3;

fn t(p: u64, g: u64) -> Outcome {
    if g <= p && g % 2 == p % 2 {
        Outcome::Draw
    } else if g == 0 {
        Outcome::Win
    } else {
        Outcome::Loss
    }
}

fn letter(o: Outcome) -> char {
    match o {
        Outcome::Win => 'W',
        Outcome::Draw => 'D',
        Outcome::Loss => 'L',
    }
}

fn main() {
    let mut args = std::env::args().skip(1).map(|a| a.parse::<u64>().expect("numbers"));
    let max_p = args.next().unwrap_or(DEFAULT_PAIRS);
    let max_a = args.next().unwrap_or(DEFAULT_HEIGHT);
    let start = Instant::now();
    println!("# block_rows {max_p} {max_a}\n");
    println!("| p | TI fails at a | a0 (row = t_p on g < a for a0 ≤ a ≤ {max_a}) | a with a draw-parity g ≤ p not a draw |\n|---|---|---|---|");
    let mut printed = Vec::new();
    for p in 1..=max_p {
        let (mut ti_fails, mut band_misses) = (Vec::new(), Vec::new());
        let mut a0 = max_a + 1;
        for a in (1..=max_a).rev() {
            let xs: Vec<u64> = (a..a + 2 * p).collect();
            let sum: u64 = xs.iter().sum();
            let mut s = Solver::new(&xs);
            let full = (1usize << xs.len()) - 1;
            // Solver reads gaps ≤ the largest number only.
            let top_gap = sum.min(a + 2 * p - 1);
            let row: Vec<Outcome> = (0..=top_gap).map(|g| s.position(full, g)).collect();
            if row[(p % 2) as usize] != Outcome::Draw {
                ti_fails.push(a);
            }
            if (0..=p.min(top_gap)).filter(|g| g % 2 == p % 2).any(|g| row[g as usize] != Outcome::Draw) {
                band_misses.push(a);
            }
            if a0 == a + 1 && (0..a.min(top_gap + 1)).all(|g| row[g as usize] == t(p, g)) {
                a0 = a;
            }
            if a <= PRINTED_HEIGHT {
                let span = top_gap.min(ROW_SPAN_FACTOR * p + 4) as usize;
                printed.push((p, a, row[..=span].iter().map(|&o| letter(o)).collect::<String>()));
            }
        }
        ti_fails.sort();
        band_misses.sort();
        let a0s = if a0 > max_a { "none".to_string() } else { a0.to_string() };
        println!("| {p} | {ti_fails:?} | {a0s} | {band_misses:?} |");
    }
    println!("\n## Rows V(B(a, p), g), g = 0, 1, …\n");
    printed.sort();
    for (p, a, r) in printed {
        println!("- p = {p}, a = {a:2}: {r}");
    }
    eprintln!("{:.1} s", start.elapsed().as_secs_f64());
}
