//! Usage: pair_moves [universe]   (default 24)
//! Which first picks draw in a pair set at g0 (L8)? E: S = p pairs P_1 < … < P_p, P_i = {a_i, a_i + 1};
//! T: {1,2,3} ∪ an E set above 3; g0 = p mod 2. A pick x ≥ g0 ends the turn, so its value is
//! neg V(S − x, x − g0). Tallies, by the role of x (which pair, bottom or top half; for T also 1, 2, 3),
//! how often it draws, and lists the sets where the top of the lowest pair (a_1 + 1) does not draw.
//! Also, for E sets, V(S, g0 + 2j) (j ≤ MAX_STEPS) by p mod 2: a win there would break the upper bound
//! by partner replies (claim X: V(E', 2) ≤ draw for E' with an even number of pairs).

use catch_up::layered::Layered;
use catch_up::{interval, Outcome, Solver};
use std::collections::BTreeMap;
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 24;
/// Members with max ≤ CHECK_UNIVERSE are re-solved with `Solver`, pick by pick.
const CHECK_UNIVERSE: usize = 14;
const SHOWN: usize = 10;
/// Pairs are labelled by index from the bottom and from the top, capped here.
const LABEL_CAP: usize = 3;
const TRIPLE: u64 = 0b111;
/// Draw-parity gaps above g0 tallied for E sets: g0 + 2j, 1 ≤ j ≤ MAX_STEPS.
const MAX_STEPS: usize = 3;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Class {
    E,
    T,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Half {
    Bottom,
    Top,
}

/// Role of a pick: a member of the triple, or a half of the i-th pair counted from below / above.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Role {
    Triple(u64),
    FromBelow(usize, Half),
    FromAbove(usize, Half),
}

fn numbers_of(mask: u64) -> Vec<u64> {
    (0..64).filter(|&i| mask >> i & 1 == 1).map(|i| i as u64 + 1).collect()
}

fn max_number(mask: u64) -> usize {
    (u64::BITS - mask.leading_zeros()) as usize
}

fn show(mask: u64) -> String {
    let xs: Vec<String> = numbers_of(mask).iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

/// Every E set ⊆ {lo..u}, the empty set included.
fn e_sets(lo: usize, u: usize) -> Vec<u64> {
    fn go(x: usize, u: usize, mask: u64, out: &mut Vec<u64>) {
        if x > u {
            out.push(mask);
            return;
        }
        go(x + 1, u, mask, out);
        if x < u {
            go(x + 2, u, mask | 0b11 << (x - 1), out);
        }
    }
    let mut out = Vec::new();
    go(lo, u, 0, &mut out);
    out
}

/// Pair bottoms of the E part (above 3 for T), ascending.
fn bottoms(class: Class, mask: u64) -> Vec<u64> {
    let e = if class == Class::T { mask & !TRIPLE } else { mask };
    numbers_of(e).into_iter().step_by(2).collect()
}

/// Both roles of each pick (from below and from above), or the triple member.
fn roles(class: Class, mask: u64, x: u64) -> Vec<Role> {
    if class == Class::T && x <= 3 {
        return vec![Role::Triple(x)];
    }
    let bs = bottoms(class, mask);
    let i = bs.iter().position(|&a| a == x || a + 1 == x).expect("x in a pair");
    let half = if bs[i] == x { Half::Bottom } else { Half::Top };
    vec![Role::FromBelow((i + 1).min(LABEL_CAP), half), Role::FromAbove((bs.len() - i).min(LABEL_CAP), half)]
}

#[derive(Default)]
struct Tally {
    sets: u64,
    /// role → (sets with a pick in that role, sets where it draws)
    by_role: BTreeMap<Role, (u64, u64)>,
    /// Sets with a winning pick (L8 false) or no drawing pick.
    not_draw: Vec<u64>,
    /// E: sets where a_1 + 1 does not draw.
    lowest_top_fails: Vec<u64>,
    lowest_top_fail_count: u64,
    /// E: a_1 → sets where a_1 + 1 does not draw.
    lowest_top_fails_by_a1: BTreeMap<u64, u64>,
    /// E: drawing picks of the listed failures.
    lowest_top_fail_draws: Vec<Vec<u64>>,
    /// E: [p mod 2][j − 1] → (wins, draws, losses) of V(S, g0 + 2j), gaps ≤ min(sum, u).
    steps: [[(u64, u64, u64); MAX_STEPS]; 2],
    /// E: first sets with a win at g0 + 2j, by p mod 2.
    step_wins: [[Vec<u64>; MAX_STEPS]; 2],
    /// Number of drawing picks → sets.
    drawing_picks: BTreeMap<usize, u64>,
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((4..=30).contains(&u), "universe out of range");
    let start = Instant::now();
    let l = Layered::new(&interval(u as u64));
    let classes = [Class::E, Class::T];
    // Members by size.
    let mut by_size: Vec<Vec<(Class, u64)>> = vec![Vec::new(); u + 1];
    for m in e_sets(1, u).into_iter().filter(|&m| m != 0) {
        by_size[m.count_ones() as usize].push((Class::E, m));
    }
    for m in e_sets(4, u) {
        let m = m | TRIPLE;
        by_size[m.count_ones() as usize].push((Class::T, m));
    }
    let mut tallies: BTreeMap<Class, Tally> = classes.iter().map(|&c| (c, Tally::default())).collect();
    let mut checked = 0u64;
    // Layer k holds the rows of sets with k numbers: the positions after a pick from a set of k + 1.
    l.run(|k, layer| {
        // Own rows of E sets with k numbers.
        for &(class, mask) in &by_size[k] {
            if class != Class::E {
                continue;
            }
            let p = bottoms(class, mask).len();
            let sum: usize = numbers_of(mask).iter().sum::<u64>() as usize;
            let t = tallies.get_mut(&class).unwrap();
            for j in 1..=MAX_STEPS {
                let g = p % 2 + 2 * j;
                if g > sum.min(u) {
                    break;
                }
                let e = &mut t.steps[p % 2][j - 1];
                match l.get(layer, l.rank(mask), g) {
                    Outcome::Win => {
                        e.0 += 1;
                        if t.step_wins[p % 2][j - 1].len() < SHOWN {
                            t.step_wins[p % 2][j - 1].push(mask);
                        }
                    }
                    Outcome::Draw => e.1 += 1,
                    Outcome::Loss => e.2 += 1,
                }
            }
        }
        for &(class, mask) in &by_size[k + 1] {
            let p = bottoms(class, mask).len();
            let g0 = (p % 2) as u64;
            let picks: Vec<(u64, Outcome)> = numbers_of(mask)
                .into_iter()
                .map(|x| (x, l.get(layer, l.rank(mask & !(1 << (x - 1))), (x - g0) as usize).neg()))
                .collect();
            if max_number(mask) <= CHECK_UNIVERSE {
                let xs = numbers_of(mask);
                let mut dfs = Solver::new(&xs);
                let all = (1usize << xs.len()) - 1;
                for (i, &(x, o)) in picks.iter().enumerate() {
                    assert_eq!(dfs.position(all & !(1 << i), x - g0).neg(), o, "{} pick {x}", show(mask));
                }
                checked += 1;
            }
            let t = tallies.get_mut(&class).unwrap();
            t.sets += 1;
            let best = picks.iter().map(|&(_, o)| o).max().unwrap();
            if best != Outcome::Draw {
                t.not_draw.push(mask);
            }
            *t.drawing_picks.entry(picks.iter().filter(|&&(_, o)| o == Outcome::Draw).count()).or_default() += 1;
            // Per role, a set counts once: drawn if any pick in that role draws.
            let mut seen: BTreeMap<Role, bool> = BTreeMap::new();
            for &(x, o) in &picks {
                for r in roles(class, mask, x) {
                    *seen.entry(r).or_default() |= o == Outcome::Draw;
                }
            }
            for (r, d) in seen {
                let e = t.by_role.entry(r).or_default();
                e.0 += 1;
                e.1 += d as u64;
            }
            if class == Class::E {
                let a1 = bottoms(class, mask)[0];
                let o = picks.iter().find(|&&(x, _)| x == a1 + 1).unwrap().1;
                if o != Outcome::Draw {
                    t.lowest_top_fail_count += 1;
                    *t.lowest_top_fails_by_a1.entry(a1).or_default() += 1;
                    if t.lowest_top_fails.len() < SHOWN {
                        t.lowest_top_fails.push(mask);
                        t.lowest_top_fail_draws.push(picks.iter().filter(|&&(_, o)| o == Outcome::Draw).map(|&(x, _)| x).collect());
                    }
                }
            }
        }
    });
    println!("# pair_moves {u}\n");
    println!("Every E and T set ⊆ {{1..{u}}}, |S| ≥ 1. Members with max ≤ {CHECK_UNIVERSE} ({checked} sets) re-solved with `Solver` pick by pick: all match.\n");
    for (class, t) in &tallies {
        println!("## {class:?}: {} sets\n", t.sets);
        println!("Sets with no drawing pick or a winning pick (L8 false): {}\n", t.not_draw.len());
        for &m in t.not_draw.iter().take(SHOWN) {
            println!("- {}", show(m));
        }
        let dp: Vec<String> = t.drawing_picks.iter().map(|(n, s)| format!("{n}: {s}")).collect();
        println!("Drawing picks per set (count: sets): {}\n", dp.join(", "));
        println!("| role | sets with it | it draws | share |\n|---|---|---|---|");
        for (r, &(n, d)) in &t.by_role {
            println!("| {r:?} | {n} | {d} | {:.3} |", d as f64 / n as f64);
        }
        if *class == Class::E {
            println!("\nTop of the lowest pair (a_1 + 1) is not a drawing pick in {} sets.", t.lowest_top_fail_count);
            let by_a1: Vec<String> = t.lowest_top_fails_by_a1.iter().map(|(a, n)| format!("{a}: {n}")).collect();
            println!("By a_1 (a_1: sets): {}\n", by_a1.join(", "));
            for (&m, d) in t.lowest_top_fails.iter().zip(&t.lowest_top_fail_draws) {
                println!("- {}: drawing picks {d:?}", show(m));
            }
            println!("\nV(S, g0 + 2j), gaps ≤ min(sum, {u}), S ≠ {{1..{u}}}:\n");
            println!("| p mod 2 | j | wins | draws | losses |\n|---|---|---|---|---|");
            for (par, row) in t.steps.iter().enumerate() {
                for (j, &(w, d, lo)) in row.iter().enumerate() {
                    println!("| {par} | {} | {w} | {d} | {lo} |", j + 1);
                }
            }
            for (par, row) in t.step_wins.iter().enumerate() {
                for (j, ws) in row.iter().enumerate() {
                    let xs: Vec<String> = ws.iter().map(|&m| show(m)).collect();
                    println!("- p mod 2 = {par}, g = {}: wins {}", par + 2 * (j + 1), xs.join(" "));
                }
            }
        }
        println!();
    }
    eprintln!("{:.1} s", start.elapsed().as_secs_f64());
}
