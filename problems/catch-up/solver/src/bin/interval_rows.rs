//! Usage: interval_rows [universe]   (default 20)
//! Where do interval positions break the parity rule? V(R, g) = the mover's value with R left,
//! trailing by g; the parity rule predicts Loss if g > sum(R), else Draw if g ≡ sum(R) (mod 2), else
//! Win. Lists every deviation over all gaps g ≤ sum(R) for R = {1..m} (m ≤ U) and, for even totals,
//! for the positions after each opening, R = {1..m} ∖ {x}. Then a census over every R ⊆ {1..U}:
//! how many draw-parity positions with lo ≤ g ≤ sum(R)/den are not draws, R complete or not.

use catch_up::{interval, Solver};
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 20;
const MAX_UNIVERSE: usize = 22;
/// The table is checked against `Solver` (gaps ≤ max) on every position up to this universe.
const CHECK_UNIVERSE: usize = 12;
/// Census bounds: lowest gap, and denominators of the highest gap as a fraction of sum(R).
const CENSUS_LOWS: [usize; 6] = [0, 1, 2, 3, 4, 5];
const CENSUS_DENS: [usize; 4] = [4, 6, 8, 12];
const SHOWN_EXCEPTIONS: usize = 12;

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

fn letter(v: u8) -> char {
    ['L', 'D', 'W'][v as usize]
}

fn total(m: usize) -> usize {
    m * (m + 1) / 2
}

/// V(R, g) for every R ⊆ {1..u} and every g ≤ total(u).
struct Table {
    stride: usize,
    values: Vec<u8>,
}

impl Table {
    fn new(u: usize) -> Self {
        let stride = total(u) + 1;
        let mut values = vec![LOSS; (1usize << u) * stride];
        let mut sums = vec![0usize; 1 << u];
        // Masks in increasing order: every move removes a bit, so successors come first.
        for mask in 0..1usize << u {
            if mask > 0 {
                sums[mask] = sums[mask & (mask - 1)] + mask.trailing_zeros() as usize + 1;
            }
            let base = mask * stride;
            if mask == 0 {
                values[base] = DRAW; // gaps > 0 with nothing left stay LOSS
                continue;
            }
            for g in 0..=sums[mask] {
                let mut best = LOSS;
                let mut rest = mask;
                while rest != 0 && best != WIN {
                    let x = rest.trailing_zeros() as usize + 1;
                    rest &= rest - 1;
                    let next = (mask & !(1 << (x - 1))) * stride;
                    let v = if x >= g { neg(values[next + x - g]) } else { values[next + g - x] };
                    best = best.max(v);
                }
                values[base + g] = best;
            }
        }
        Table { stride, values }
    }

    fn get(&self, mask: usize, g: usize) -> u8 {
        self.values[mask * self.stride + g]
    }
}

fn parity_rule(sum: usize, g: usize) -> u8 {
    if g > sum {
        LOSS
    } else if (g + sum) % 2 == 0 {
        DRAW
    } else {
        WIN
    }
}

/// Deviations from the parity rule along the row of `mask`, as "g:V" items.
fn deviations(t: &Table, mask: usize) -> Vec<String> {
    let sum: usize = (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
    (0..=sum)
        .filter(|&g| t.get(mask, g) != parity_rule(sum, g))
        .map(|g| format!("{g}:{}", letter(t.get(mask, g))))
        .collect()
}

fn check(t: &Table, u: usize) {
    let c = u.min(CHECK_UNIVERSE);
    let mut dfs = Solver::new(&interval(c as u64));
    for mask in 0..1usize << c {
        for g in 0..=c {
            let want = dfs.position(mask, g as u64) as u8;
            assert_eq!(t.get(mask, g), want, "mask {mask:b} gap {g}");
        }
    }
    for n in 1..=u {
        let full = (1 << n) - 1;
        let value = (0..n).map(|i| neg(t.get(full & !(1 << i), i + 1))).max().unwrap();
        assert_eq!(value, Solver::new(&interval(n as u64)).value() as u8, "value of {{1..{n}}}");
    }
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((1..=MAX_UNIVERSE).contains(&u), "universe out of range");
    let start = Instant::now();
    let t = Table::new(u);
    check(&t, u);
    println!(
        "Table {{1..{u}}}, all gaps: {} ms; matches `Solver` on every R ⊆ {{1..{}}} at gaps ≤ max (only), and on value({{1..N}}), N ≤ {u}.\n",
        start.elapsed().as_millis(),
        u.min(CHECK_UNIVERSE)
    );
    println!("Parity rule: L if g > sum(R), else D if g ≡ sum(R) (mod 2), else W. Deviations listed as g:V.\n");
    println!("## R = {{1..m}}\n");
    println!("| m | sum | deviations |\n|---|---|---|");
    for m in 0..=u {
        println!("| {m} | {} | {} |", total(m), deviations(&t, (1 << m) - 1).join(" "));
    }
    println!("\n## R = {{1..m}} ∖ {{x}}, even totals (after opening x the opponent trails by x)\n");
    println!("| m | x | sum | deviations |\n|---|---|---|---|");
    for m in (1..=u).filter(|&m| total(m) % 2 == 0) {
        for x in 1..=m {
            let mask = ((1 << m) - 1) & !(1 << (x - 1));
            println!("| {m} | {x} | {} | {} |", total(m) - x, deviations(&t, mask).join(" "));
        }
    }
    census(&t, u);
    println!("\nTotal {} ms", start.elapsed().as_millis());
}

/// Each element ≤ 1 + the sum of the smaller ones: every amount up to sum(R) can be paid exactly.
fn complete(mask: usize) -> bool {
    let mut prefix = 0;
    (0..32).filter(|&i| mask >> i & 1 == 1).all(|i| {
        let ok = i < prefix + 1; // number i + 1 ≤ prefix + 1
        prefix += i + 1;
        ok
    })
}

fn show(mask: usize) -> String {
    let xs: Vec<String> = (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| (i + 1).to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

fn census(t: &Table, u: usize) {
    // [complete][lo][den] → (draw-parity positions, non-draws)
    let mut cells = [[[(0u64, 0u64); CENSUS_DENS.len()]; CENSUS_LOWS.len()]; 2];
    let mut shown = Vec::new();
    let (lo_shown, den_shown) = (CENSUS_LOWS.len() - 1, 1);
    for mask in 1..1usize << u {
        let sum: usize = (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
        let c = complete(mask) as usize;
        for g in (sum % 2..=sum / CENSUS_DENS[0]).step_by(2) {
            let non_draw = t.get(mask, g) != DRAW;
            for (li, &lo) in CENSUS_LOWS.iter().enumerate() {
                for (di, &den) in CENSUS_DENS.iter().enumerate() {
                    if g >= lo && g * den <= sum {
                        cells[c][li][di].0 += 1;
                        cells[c][li][di].1 += non_draw as u64;
                    }
                }
            }
            if non_draw && c == 1 && g >= CENSUS_LOWS[lo_shown] && g * CENSUS_DENS[den_shown] <= sum {
                shown.push((mask.count_ones(), mask, g));
            }
        }
    }
    println!("\n## Census over every R ⊆ {{1..{u}}}\n");
    println!("Draw-parity positions (g ≡ sum(R) mod 2) with lo ≤ g ≤ sum(R)/den: non-draws / positions.\n");
    for (c, name) in [(1, "complete R"), (0, "R not complete")] {
        println!("{name}:\n");
        let dens: Vec<String> = CENSUS_DENS.iter().map(|d| format!("sum/{d}")).collect();
        println!("| lo | {} |\n|---|{}", dens.join(" | "), "---|".repeat(CENSUS_DENS.len()));
        for (li, lo) in CENSUS_LOWS.iter().enumerate() {
            let row: Vec<String> = cells[c][li].iter().map(|(n, bad)| format!("{bad} / {n}")).collect();
            println!("| {lo} | {} |", row.join(" | "));
        }
        println!();
    }
    shown.sort();
    println!(
        "Smallest complete R with a non-draw at {} ≤ g ≤ sum/{} ({} in all):\n",
        CENSUS_LOWS[lo_shown],
        CENSUS_DENS[den_shown],
        shown.len()
    );
    for &(_, mask, g) in shown.iter().take(SHOWN_EXCEPTIONS) {
        println!("- R = {}, g = {g}: {}", show(mask), letter(t.get(mask, g)));
    }
    holes_census(t, u);
}

/// The same census by holes = max(R) − |R| (numbers missing below the largest), R ≠ ∅.
fn holes_census(t: &Table, u: usize) {
    const LOW: usize = 5;
    const DENS: [usize; 3] = [4, 6, 12];
    const MAX_HOLES: usize = 8;
    // [holes][den] → (positions, non-draws); last row = MAX_HOLES or more.
    let mut cells = [[(0u64, 0u64); DENS.len()]; MAX_HOLES + 1];
    let mut first: Vec<Option<(u32, usize, usize)>> = vec![None; MAX_HOLES + 1];
    for mask in 1..1usize << u {
        let sum: usize = (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
        let max = (usize::BITS - mask.leading_zeros()) as usize;
        let h = (max - mask.count_ones() as usize).min(MAX_HOLES);
        for g in (LOW + (LOW + sum) % 2..=sum / DENS[0]).step_by(2) {
            let non_draw = t.get(mask, g) != DRAW;
            for (di, &den) in DENS.iter().enumerate() {
                if g * den <= sum {
                    cells[h][di].0 += 1;
                    cells[h][di].1 += non_draw as u64;
                    if non_draw && den == DENS[1] && first[h].is_none_or(|f| (mask.count_ones(), mask) < (f.0, f.1)) {
                        first[h] = Some((mask.count_ones(), mask, g));
                    }
                }
            }
        }
    }
    println!("\n## Census by holes (max(R) − |R|), draw-parity g with {LOW} ≤ g ≤ sum(R)/den\n");
    let dens: Vec<String> = DENS.iter().map(|d| format!("sum/{d}")).collect();
    println!("| holes | {} | smallest R with a non-draw (sum/{}) |\n|---|{}---|", dens.join(" | "), DENS[1], "---|".repeat(DENS.len()));
    for (h, row) in cells.iter().enumerate() {
        let shown: Vec<String> = row.iter().map(|(n, bad)| format!("{bad} / {n}")).collect();
        let example = first[h].map_or(String::new(), |(_, mask, g)| format!("{}, g = {g}: {}", show(mask), letter(t.get(mask, g))));
        let label = if h == MAX_HOLES { format!("≥ {h}") } else { h.to_string() };
        println!("| {label} | {} | {example} |", shown.join(" | "));
    }
    near_intervals(t, u);
}

/// Robustness of the conjecture: values of even-sum sets {1..m} ∖ H, H ⊆ {1..m−1}, |H| = h, as
/// fresh games (gap 0: one pick, like the opening).
fn near_intervals(t: &Table, u: usize) {
    const MAX_HOLES: u32 = 4;
    println!("\n## Even-sum {{1..m}} ∖ H as fresh games (gap 0), |H| = h, H ⊆ {{1..m−1}}\n");
    println!("| h | sets | not draws | smallest m with a non-draw | first non-draws | largest m with a non-draw: its non-draws |\n|---|---|---|---|---|---|");
    for h in 0..=MAX_HOLES {
        let (mut sets, mut bad, mut first_m, mut examples) = (0u64, 0u64, None, Vec::new());
        let mut last: (usize, Vec<String>) = (0, Vec::new());
        for m in 1..=u {
            let full = (1usize << m) - 1;
            for holes in 0..1usize << (m - 1) {
                if holes.count_ones() != h {
                    continue;
                }
                let mask = full & !holes;
                let sum: usize = (0..m).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
                if sum % 2 != 0 {
                    continue;
                }
                sets += 1;
                if t.get(mask, 0) != DRAW {
                    bad += 1;
                    first_m.get_or_insert(m);
                    let shown = format!("{} {}", show(mask), letter(t.get(mask, 0)));
                    if examples.len() < 4 {
                        examples.push(shown.clone());
                    }
                    if last.0 != m {
                        last = (m, Vec::new());
                    }
                    last.1.push(shown);
                }
            }
        }
        let m = first_m.map_or("-".to_string(), |m: usize| m.to_string());
        println!("| {h} | {sets} | {bad} | {m} | {} | {}: {} |", examples.join("; "), last.0, last.1.join("; "));
    }
}
