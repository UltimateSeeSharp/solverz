//! Usage: pair_step [universe]   (default 22)
//! Does adding two numbers above every remaining one act on a position's value by a local rule?
//! V(R, g) = the mover's value with R left, trailing by g.
//! 1. Twins: V(S ⊎ {x, x}, g) = V(S, g) for x ≥ max(S), g ≤ x? (multisets, `Solver`)
//! 2. Pairs: is V(R ∪ {x, x+1}, g) a function of V(R, g−1), V(R, g), V(R, g+1), for R ⊆ {1..U−2},
//!    x > max(R)? (one layered table on {1..U}). Sliced by where g lies and whether x = max(R) + 1.
//! 3. The same with wider windows V(R, g−w..g+w), over all R and over intervals only.

use catch_up::layered::Layered;
use catch_up::{interval, reference_value, Outcome, Solver};
use std::collections::BTreeMap;
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 22;
const TWIN_UNIVERSE: u64 = 12;
/// x − max(S) for the twins test.
const TWIN_OFFSETS: [u64; 3] = [0, 1, 3];
const TWIN_REFERENCE_MAX_SIZE: usize = 6;
const RANDOM_CHECKS: usize = 20_000;
const SHOWN_CONFLICTS: usize = 3;
const MAX_WINDOW: usize = 4;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Regime {
    /// g ≤ max(R)
    Inside,
    /// max(R) < g ≤ x
    Between,
    /// g > x
    Beyond,
}

/// (V(R, g−1), or none at g = 0; V(R, g); V(R, g+1))
type Key = (Option<Outcome>, Outcome, Outcome);

/// Slice of the pair test: regime of g, and whether x = max(R) + 1.
type Slice = (Regime, bool);

fn max_number(mask: usize) -> usize {
    (usize::BITS - mask.leading_zeros()) as usize
}

fn numbers_of(mask: usize) -> Vec<u64> {
    (0..usize::BITS as usize).filter(|&i| mask >> i & 1 == 1).map(|i| i as u64 + 1).collect()
}

fn show(mask: usize) -> String {
    let xs: Vec<String> = numbers_of(mask).iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

fn letter(o: Outcome) -> char {
    format!("{o:?}").chars().next().unwrap()
}

fn show_key(k: &Key) -> String {
    format!("{}{}{}", k.0.map_or('-', letter), letter(k.1), letter(k.2))
}

/// Next larger mask with the same number of bits (Gosper's hack): colex order.
fn next_combination(mask: u64) -> u64 {
    if mask == 0 {
        return 0;
    }
    let t = mask | (mask - 1);
    (t + 1) | (((!t & (t + 1)) - 1) >> (mask.trailing_zeros() + 1))
}

/// Every position with numbers from {1..u}: V(mask, g) for g ≤ u.
struct Table {
    layered: Layered,
    words: usize,
    rows: Vec<u32>,
    /// `Layered::run` stops before the full set; its row comes from `Solver`.
    full_row: Vec<Outcome>,
    u: usize,
}

impl Table {
    fn new(u: usize) -> Self {
        let layered = Layered::new(&interval(u as u64));
        let mut rows = Vec::new();
        let mut words = 0;
        layered.run(|k, layer| {
            words = layer.len() / layered.layer_len(k);
            if rows.is_empty() {
                rows = vec![0u32; (1 << u) * words];
            }
            // Layer rows are in colex rank order, which for masks with k bits is numeric order.
            let mut mask: u64 = (1 << k) - 1;
            for r in 0..layered.layer_len(k) {
                assert!(r % 4096 != 0 || layered.rank(mask) == r, "rank of {mask:b}");
                rows[mask as usize * words..][..words].copy_from_slice(&layer[r * words..][..words]);
                mask = next_combination(mask);
            }
        });
        let mut dfs = Solver::new(&interval(u as u64));
        let full_row = (0..=u).map(|g| dfs.position((1 << u) - 1, g as u64)).collect();
        Table { layered, words, rows, full_row, u }
    }

    fn get(&self, mask: usize, g: usize) -> Outcome {
        assert!(g <= self.u, "gap {g} beyond the table");
        if mask == (1 << self.u) - 1 {
            return self.full_row[g];
        }
        self.layered.get(&self.rows[mask * self.words..][..self.words], 0, g)
    }

    /// Random positions against `Solver` on {1..u}.
    fn cross_check(&self) {
        let mut dfs = Solver::new(&interval(self.u as u64));
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..RANDOM_CHECKS {
            // xorshift64
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let mask = (state as usize) & ((1 << self.u) - 1);
            let g = (state >> 40) as usize % (self.u + 1);
            assert_eq!(self.get(mask, g), dfs.position(mask, g as u64), "{} at gap {g}", show(mask));
        }
    }
}

/// Part 1: V(S ⊎ {x, x}, g) against V(S, g) for every S ⊆ {1..TWIN_UNIVERSE}.
fn twins() {
    let (mut checked, mut broken) = (0u64, Vec::new());
    for bits in 0usize..1 << TWIN_UNIVERSE {
        let s = numbers_of(bits);
        let m = s.last().copied().unwrap_or(1);
        for off in TWIN_OFFSETS {
            let x = m + off;
            let mut numbers = s.clone();
            numbers.extend([x, x]);
            let mut dfs = Solver::new(&numbers);
            if s.len() < TWIN_REFERENCE_MAX_SIZE {
                assert_eq!(dfs.value(), reference_value(&numbers), "value of {numbers:?}");
            }
            let all = (1 << numbers.len()) - 1;
            let low = (1 << s.len()) - 1;
            for g in 0..=x {
                checked += 1;
                let (with, without) = (dfs.position(all, g), dfs.position(low, g));
                if with != without {
                    broken.push(format!("S = {s:?}, x = {x}, g = {g}: {with:?} with the twins, {without:?} without"));
                }
            }
        }
    }
    println!("## Twins\n");
    println!("V(S ⊎ {{x, x}}, g) = V(S, g) for every S ⊆ {{1..{TWIN_UNIVERSE}}}, x − max(S) ∈ {TWIN_OFFSETS:?}, g ≤ x:");
    println!("{checked} positions, {} differ.", broken.len());
    for line in broken.iter().take(SHOWN_CONFLICTS * 4) {
        println!("- {line}");
    }
    println!();
}

/// Part 2: tallies V(R ∪ {x, x+1}, g) by the key of V(R, ·) around g.
fn pairs(t: &Table) {
    let u = t.u;
    t.cross_check();
    println!("Table matches `Solver` on {RANDOM_CHECKS} random positions.\n");

    let mut tally: BTreeMap<Slice, BTreeMap<Key, [u64; 3]>> = BTreeMap::new();
    // First example per (slice, key, outcome): (R, x, g).
    let mut example: BTreeMap<(Slice, Key, Outcome), (usize, usize, usize)> = BTreeMap::new();
    for r in 0usize..1 << (u - 2) {
        let m = max_number(r);
        for x in m + 1..u {
            let pair = 1 << (x - 1) | 1 << x;
            for g in 0..u {
                let key = ((g > 0).then(|| t.get(r, g - 1)), t.get(r, g), t.get(r, g + 1));
                let regime = if g <= m {
                    Regime::Inside
                } else if g <= x {
                    Regime::Between
                } else {
                    Regime::Beyond
                };
                let slice = (regime, x == m + 1);
                let v = t.get(r | pair, g);
                tally.entry(slice).or_default().entry(key).or_default()[v as usize] += 1;
                example.entry((slice, key, v)).or_insert((r, x, g));
            }
        }
    }

    println!("## Pairs on {{1..{u}}}\n");
    println!("Key: V(R, g−1) V(R, g) V(R, g+1) (L/D/W, '-' at g = 0). Columns: V(R ∪ {{x, x+1}}, g).\n");
    for (slice, keys) in &tally {
        let conflicts = keys.values().filter(|c| c.iter().filter(|&&n| n > 0).count() > 1).count();
        println!("### {:?}, x {} max(R) + 1: {} keys, {conflicts} not determined\n", slice.0, if slice.1 { "=" } else { ">" }, keys.len());
        println!("| key | Loss | Draw | Win | examples (R, x, g) |\n|---|---|---|---|---|");
        for (key, c) in keys {
            let shown: Vec<String> = [Outcome::Loss, Outcome::Draw, Outcome::Win]
                .iter()
                .filter(|&&o| c[o as usize] > 0 && c.iter().filter(|&&n| n > 0).count() > 1)
                .take(SHOWN_CONFLICTS)
                .map(|&o| {
                    let (r, x, g) = example[&(*slice, *key, o)];
                    verify(r, x, g, o);
                    format!("{}: {}, {x}, {g}", letter(o), show(r))
                })
                .collect();
            println!("| {} | {} | {} | {} | {} |", show_key(key), c[0], c[1], c[2], shown.join("; "));
        }
        println!();
    }
    println!("Every example agrees with `Solver` on R ∪ {{x, x+1}} alone (gaps ≤ x + 1).\n");
}

/// Part 3: does a wider window V(R, g−w..g+w) determine V(R ∪ {x, x+1}, g)? Over all R (g ≤ x), and
/// over intervals R = {1..m}, x = m + 1 only. Prints the interval rows.
fn windows(t: &Table) {
    let u = t.u;
    let window = |r: usize, g: usize, w: usize| -> Vec<Option<Outcome>> {
        (g as i64 - w as i64..=(g + w) as i64).map(|h| (h >= 0).then(|| t.get(r, h as usize))).collect()
    };
    println!("## Wider windows\n");
    println!("Keys V(R, g−w..g+w) that occur with two different values of V(R ∪ {{x, x+1}}, g), g + w ≤ {u}.\n");
    println!("| w | all R, g ≤ x: keys | not determined | intervals: keys | positions disagreeing with their key's first value | first interval conflict (m, g) |\n|---|---|---|---|---|---|");
    for w in 1..=MAX_WINDOW {
        let mut all: BTreeMap<Vec<Option<Outcome>>, [bool; 3]> = BTreeMap::new();
        for r in 0usize..1 << (u - 2) {
            for x in max_number(r) + 1..u {
                for g in 0..=x.min(u - w) {
                    all.entry(window(r, g, w)).or_default()[t.get(r | 1 << (x - 1) | 1 << x, g) as usize] = true;
                }
            }
        }
        let mut ivs: BTreeMap<Vec<Option<Outcome>>, (Outcome, usize, usize)> = BTreeMap::new();
        let (mut conflicts, mut first) = (0, None);
        for m in 0..u - 1 {
            for g in 0..=u - w {
                let v = t.get((1 << (m + 2)) - 1, g);
                let seen = *ivs.entry(window((1 << m) - 1, g, w)).or_insert((v, m, g));
                if seen.0 != v {
                    conflicts += 1;
                    first.get_or_insert(format!("({}, {}) vs ({m}, {g})", seen.1, seen.2));
                }
            }
        }
        let undetermined = |c: &[bool; 3]| c.iter().filter(|&&b| b).count() > 1;
        println!(
            "| {w} | {} | {} | {} | {conflicts} | {} |",
            all.len(),
            all.values().filter(|c| undetermined(c)).count(),
            ivs.len(),
            first.unwrap_or_default()
        );
    }
    println!("\nInterval rows V({{1..m}}, g), g = 0..{u}:\n");
    for m in 0..u {
        let row: String = (0..=u).map(|g| letter(t.get((1 << m) - 1, g))).collect();
        println!("    {m:>2} {row}");
    }
    println!();
}

/// Re-solves an example on its own numbers.
fn verify(r: usize, x: usize, g: usize, want: Outcome) {
    if g > x + 1 {
        return;
    }
    let mut numbers = numbers_of(r);
    numbers.extend([x as u64, x as u64 + 1]);
    let mut dfs = Solver::new(&numbers);
    assert_eq!(dfs.position((1 << numbers.len()) - 1, g as u64), want, "R = {}, x = {x}, g = {g}", show(r));
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((4..=28).contains(&u), "universe out of range");
    let start = Instant::now();
    twins();
    println!("Twins: {} ms\n", start.elapsed().as_millis());
    let table = Table::new(u);
    println!("Table {{1..{u}}}: {} ms\n", start.elapsed().as_millis());
    pairs(&table);
    windows(&table);
    println!("Total {} ms", start.elapsed().as_millis());
}
