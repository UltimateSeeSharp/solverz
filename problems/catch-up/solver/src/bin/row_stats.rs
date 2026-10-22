//! Usage: row_stats [max_n]   (default 22)
//! How compressible are the layered solver's rows (one value per gap for a set of numbers left)?
//! Decides the storage format of the out-of-core solver.

use catch_up::interval;
use catch_up::layered::Layered;
use std::collections::{HashMap, HashSet};

const DEFAULT_MAX_N: u64 = 22;
const FIRST_N: u64 = 4;
const SAMPLE_PATTERNS: usize = 8;

fn main() {
    let max_n = std::env::args().nth(1).map_or(DEFAULT_MAX_N, |s| s.parse().expect("max_n must be a number"));
    println!("| N | rows | distinct rows | dict bits/row | raw bits/row | non-increasing in gap | max value changes along a row |");
    println!("|---|---|---|---|---|---|---|");
    let mut last_patterns = HashMap::new();
    for n in FIRST_N..=max_n {
        let l = Layered::new(&interval(n));
        let gaps = n as usize + 1;
        let (mut rows, mut non_increasing, mut max_changes) = (0u64, 0u64, 0usize);
        let mut distinct: HashSet<u128> = HashSet::new();
        let mut patterns: HashMap<String, u64> = HashMap::new();
        l.run(|k, layer| {
            let words = layer.len() / l.layer_len(k);
            for r in 0..l.layer_len(k) {
                rows += 1;
                let key = layer[r * words..(r + 1) * words].iter().fold(0u128, |acc, &w| (acc << 32) | w as u128);
                if distinct.insert(key) || patterns.len() < usize::MAX {
                    let row: Vec<_> = (0..gaps).map(|g| l.get(layer, r, g)).collect();
                    if row.windows(2).all(|p| p[0] >= p[1]) {
                        non_increasing += 1;
                    }
                    max_changes = max_changes.max(row.windows(2).filter(|p| p[0] != p[1]).count());
                    let pattern: String = row.iter().map(|o| format!("{o:?}").chars().next().unwrap()).collect();
                    *patterns.entry(pattern).or_default() += 1;
                }
            }
        });
        println!(
            "| {n} | {rows} | {} | {} | {} | {:.1}% | {max_changes} |",
            distinct.len(),
            (distinct.len() as f64).log2().ceil(),
            2 * gaps,
            100.0 * non_increasing as f64 / rows as f64
        );
        last_patterns = patterns;
    }
    let mut top: Vec<_> = last_patterns.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1));
    println!("\nMost common rows at N = {max_n} (gap 0, 1, 2, …; W/D/L = win/draw/loss for the mover):");
    for (pattern, count) in top.into_iter().take(SAMPLE_PATTERNS) {
        println!("  {pattern}  ×{count}");
    }
}
