//! Usage: quad_step [universe]   (default 24)
//! Induction by four: if S has even sum and is a draw, is S ∪ Q a draw for every balanced quadruple
//! Q = {a < b < c < d}, a + d = b + c, above max(S)? {1..N+4} = {1..N} ∪ {N+1..N+4} is the case
//! "Q = the next four numbers". Tests every S with S ∪ Q ⊆ {1..U} from one layered table:
//! value(S) is the mover's value with S left at gap 0 (a gap-0 turn is one pick, like the opening).
//! Also slices by complete S (each number ≤ 1 + sum of the smaller ones) and lists the complete
//! even-sum sets that are not draws.

use catch_up::layered::Layered;
use catch_up::{interval, reference_value, Outcome, Solver};
use std::time::Instant;

const DEFAULT_UNIVERSE: usize = 24;
/// Every subset of {1..CHECK_UNIVERSE} is re-solved with `Solver` to validate the table lookup.
const CHECK_UNIVERSE: usize = 10;
/// Printed sets are re-solved with `Solver`, and with `reference_value` up to this many numbers.
const REFERENCE_MAX_SIZE: u32 = 9;
const RANDOM_CHECKS: usize = 100;
const RANDOM_CHECK_MAX_SIZE: u32 = 16;
/// Spot-check of colex rank = position in numeric order, every RANK_CHECK_STRIDE-th mask.
const RANK_CHECK_STRIDE: usize = 1024;
const QUAD: usize = 4;
const SHOWN_COUNTEREXAMPLES: usize = 12;
const SHOWN_NON_DRAWS: usize = 30;
const KEPT_COUNTEREXAMPLES: usize = 1 << 20;
const OUTCOMES: [Outcome; 3] = [Outcome::Loss, Outcome::Draw, Outcome::Win];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// Q = {M+1, M+2, M+3, M+4}, M = max(S): the step {1..N} → {1..N+4}.
    Next,
    /// Q = {a, a+1, a+2, a+3} with a > M + 1: consecutive, but leaving a hole above S.
    ConsecutiveWithHole,
    /// Any other balanced quadruple above M.
    Spread,
}
const KINDS: [Kind; 3] = [Kind::Next, Kind::ConsecutiveWithHole, Kind::Spread];

fn numbers_of(mask: usize) -> Vec<u64> {
    numbers_iter(mask).collect()
}

fn max_number(mask: usize) -> usize {
    (usize::BITS - mask.leading_zeros()) as usize
}

/// Numbers in increasing order (number x ↔ bit x − 1), without allocating.
fn numbers_iter(mut mask: usize) -> impl Iterator<Item = u64> {
    std::iter::from_fn(move || {
        (mask != 0).then(|| {
            let x = mask.trailing_zeros() as u64 + 1;
            mask &= mask - 1;
            x
        })
    })
}

/// Every subset sum 0..=sum(S) is reachable: each element ≤ 1 + sum of the smaller ones.
fn complete(mask: usize) -> bool {
    let mut prefix = 0u64;
    numbers_iter(mask).all(|x| {
        let ok = x <= prefix + 1;
        prefix += x;
        ok
    })
}

fn show(mask: usize) -> String {
    let xs: Vec<String> = numbers_of(mask).iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

/// Next larger mask with the same number of bits (Gosper's hack): colex order.
fn next_combination(mask: u64) -> u64 {
    if mask == 0 {
        return 0;
    }
    let t = mask | (mask - 1);
    (t + 1) | (((!t & (t + 1)) - 1) >> (mask.trailing_zeros() + 1))
}

/// value(S) for every S ⊆ {1..u}, indexed by mask.
fn all_values(u: usize) -> Vec<Outcome> {
    let l = Layered::new(&interval(u as u64));
    let mut values = vec![Outcome::Draw; 1 << u];
    let last = l.run(|k, layer| {
        // Layer rows are in colex rank order, which for masks with k bits is numeric order.
        let mut mask: u64 = (1 << k) - 1;
        let len = l.layer_len(k);
        for r in 0..len {
            if r % RANK_CHECK_STRIDE == 0 || r + 1 == len {
                assert_eq!(l.rank(mask), r, "rank of {mask:b}");
            }
            values[mask as usize] = l.get(layer, r, 0);
            mask = next_combination(mask);
        }
    });
    // `run` stops at layer u − 1; the full set's value comes from its openings.
    let full = (1usize << u) - 1;
    values[full] = (0..u).map(|i| l.get(&last, l.rank((full & !(1 << i)) as u64), i + 1).neg()).max().unwrap();
    values
}

fn cross_check(values: &[Outcome], u: usize) {
    for mask in 0..1usize << CHECK_UNIVERSE.min(u) {
        assert_eq!(values[mask], Solver::new(&numbers_of(mask)).value(), "S = {}", show(mask));
    }
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut checked = 0;
    while checked < RANDOM_CHECKS {
        // xorshift64
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let mask = (state as usize) & ((1 << u) - 1);
        if mask.count_ones() > RANDOM_CHECK_MAX_SIZE {
            continue;
        }
        assert_eq!(values[mask], Solver::new(&numbers_of(mask)).value(), "S = {}", show(mask));
        checked += 1;
    }
}

/// Re-solves a printed set with the independent engines.
fn verify(values: &[Outcome], mask: usize) {
    let numbers = numbers_of(mask);
    assert_eq!(values[mask], Solver::new(&numbers).value(), "Solver disagrees on {}", show(mask));
    if mask.count_ones() <= REFERENCE_MAX_SIZE {
        assert_eq!(values[mask], reference_value(&numbers), "reference disagrees on {}", show(mask));
    }
}

struct Counterexample {
    top: usize,
    size: u32,
    s: usize,
    q: usize,
    value: Outcome,
}

#[derive(Default)]
struct Tally {
    /// [value(S)][value(S ∪ Q)] over even-sum S, and over complete even-sum S.
    matrix: [[u64; 3]; 3],
    complete_matrix: [[u64; 3]; 3],
    broken: Vec<Counterexample>,
    broken_total: u64,
    broken_complete: u64,
}

fn print_matrix(matrix: &[[u64; 3]; 3]) {
    println!("| | Loss | Draw | Win |\n|---|---|---|---|");
    for (i, row) in matrix.iter().enumerate() {
        println!("| {:?} | {} | {} | {} |", OUTCOMES[i], row[0], row[1], row[2]);
    }
}

/// Context: outcomes of all complete even-sum S ⊆ {1..u}, by max(S); lists the first non-draws.
fn complete_sets(values: &[Outcome], u: usize) {
    println!("## Complete even-sum S ⊆ {{1..{u}}}\n");
    println!("| max(S) | Loss | Draw | Win |\n|---|---|---|---|");
    let mut counts = vec![[0u64; 3]; u + 1];
    let mut non_draws = Vec::new();
    for s in 0..1usize << u {
        if numbers_iter(s).sum::<u64>() % 2 != 0 || !complete(s) {
            continue;
        }
        counts[max_number(s)][values[s] as usize] += 1;
        if values[s] != Outcome::Draw {
            non_draws.push(s);
        }
    }
    for (m, c) in counts.iter().enumerate() {
        println!("| {m} | {} | {} | {} |", c[0], c[1], c[2]);
    }
    non_draws.sort_by_key(|&s| (max_number(s), s.count_ones(), s));
    println!("\nFirst non-draws, with player 1's winning openings:\n");
    for &s in non_draws.iter().take(SHOWN_NON_DRAWS) {
        verify(values, s);
        let wins: Vec<String> = Solver::new(&numbers_of(s))
            .openings()
            .into_iter()
            .filter(|&(_, o)| o == Outcome::Win)
            .map(|(x, _)| x.to_string())
            .collect();
        println!("- {} {:?}, sum {}, winning openings {}", show(s), values[s], numbers_iter(s).sum::<u64>(), wins.join(","));
    }
    let losses: Vec<String> = non_draws
        .iter()
        .filter(|&&s| values[s] == Outcome::Loss)
        .take(SHOWN_NON_DRAWS)
        .map(|&s| {
            verify(values, s);
            show(s)
        })
        .collect();
    println!("\nPlayer-1 losses: {}\n", if losses.is_empty() { "none".to_string() } else { losses.join(" ") });
}

fn main() {
    let u: usize = std::env::args().nth(1).map_or(DEFAULT_UNIVERSE, |s| s.parse().expect("universe must be a number"));
    assert!((QUAD + 1..usize::BITS as usize).contains(&u), "universe out of range");
    let start = Instant::now();
    let values = all_values(u);
    let table_ms = start.elapsed().as_millis();
    cross_check(&values, u);
    println!("Universe {{1..{u}}}: table {table_ms} ms; values match `Solver` on all subsets of {{1..{CHECK_UNIVERSE}}} and {RANDOM_CHECKS} random subsets.\n");

    let interval_values: Vec<String> = (1..=u).map(|n| format!("{n}:{:?}", values[(1 << n) - 1])).collect();
    println!("value({{1..N}}): {}\n", interval_values.join(" "));

    let mut tallies: Vec<Tally> = KINDS.iter().map(|_| Tally::default()).collect();
    for s in 0..1usize << (u - QUAD) {
        let sum: u64 = numbers_iter(s).sum();
        if sum % 2 != 0 {
            continue;
        }
        let m = max_number(s);
        let vs = values[s];
        let s_complete = complete(s);
        for a in m + 1..=u {
            for b in a + 1..=u {
                for c in b + 1..=u {
                    let d = b + c - a;
                    if d > u {
                        break;
                    }
                    let kind = if d != a + 3 {
                        Kind::Spread
                    } else if a == m + 1 {
                        Kind::Next
                    } else {
                        Kind::ConsecutiveWithHole
                    };
                    let q = 1 << (a - 1) | 1 << (b - 1) | 1 << (c - 1) | 1 << (d - 1);
                    let vt = values[s | q];
                    let t = &mut tallies[kind as usize];
                    t.matrix[vs as usize][vt as usize] += 1;
                    if s_complete {
                        t.complete_matrix[vs as usize][vt as usize] += 1;
                    }
                    if vs == Outcome::Draw && vt != Outcome::Draw {
                        t.broken_total += 1;
                        t.broken_complete += s_complete as u64;
                        if t.broken.len() < KEPT_COUNTEREXAMPLES {
                            t.broken.push(Counterexample { top: d, size: s.count_ones(), s, q, value: vt });
                        }
                    }
                }
            }
        }
    }

    for (kind, t) in KINDS.iter().zip(tallies.iter_mut()) {
        println!("## {kind:?}\n");
        println!("Even-sum S, rows value(S), columns value(S ∪ Q):\n");
        print_matrix(&t.matrix);
        println!("\nComplete S only:\n");
        print_matrix(&t.complete_matrix);
        let draws: u64 = t.matrix[Outcome::Draw as usize].iter().sum();
        println!(
            "\nDraw S broken by Q: {} of {draws} (S complete in {} of them)",
            t.broken_total, t.broken_complete
        );
        t.broken.sort_by_key(|c| (c.top, c.size, c.s));
        for want_complete in [true, false] {
            let tag = if want_complete { "complete" } else { "not complete" };
            for c in t.broken.iter().filter(|c| complete(c.s) == want_complete).take(SHOWN_COUNTEREXAMPLES) {
                verify(&values, c.s);
                verify(&values, c.s | c.q);
                println!("- S = {} ({tag}), Q = {}: {:?}", show(c.s), show(c.q), c.value);
            }
        }
        println!();
    }
    complete_sets(&values, u);
    println!("Every printed set agrees with `Solver`, and with `reference_value` up to {REFERENCE_MAX_SIZE} numbers.");
    println!("Total {} ms", start.elapsed().as_millis());
}
