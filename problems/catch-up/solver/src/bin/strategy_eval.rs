//! Usage: strategy_eval [max_n]   (default 20)
//! Which simple pick rules hold a draw against a perfect opponent? For each N ≤ max_n and each rule,
//! player 1's value when player 1 follows the rule against a perfect player 2, and when player 2
//! follows it against a perfect player 1. A rule chooses one pick at a time from (numbers left, gap).

use catch_up::{interval, Outcome, Solver};
use std::time::Instant;

const DEFAULT_MAX_N: usize = 20;
const MAX_N: usize = 26;
/// The table evaluator is checked against a recursive one up to this N.
const RECURSIVE_CHECK_MAX_N: usize = 9;
const RANDOM_CHECKS: usize = 5_000;

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

fn decode(v: u8) -> Outcome {
    [Outcome::Loss, Outcome::Draw, Outcome::Win][v as usize]
}

/// A pick rule: the number to take with `mask` left (number x ↔ bit x − 1), trailing by `g`.
#[derive(Clone, Copy, Debug)]
enum Rule {
    Largest,
    Smallest,
    /// Smallest number that catches up (≥ g), else the largest.
    SmallestCatch,
    /// g itself if left (ties, so the opponent starts at gap 0), else smallest catch.
    Exact,
    /// g + 1 if left (lead by one), else g, else smallest catch.
    LeadOne,
    /// Largest number that keeps the mover behind (< g), else smallest catch.
    StayBehind,
    /// Repair a broken adjacent pair ({2j−1, 2j}, or {2j, 2j+1} with 1 alone for odd n) if one is
    /// broken: the smallest such number that catches up, else the largest that doesn't; with no
    /// broken pair, smallest catch.
    RepairThenSmallestCatch,
    /// The same repair, else the largest number.
    RepairThenLargest,
    /// Repair with the largest number of a broken pair, else the largest number.
    RepairLargest,
}

const RULES: [Rule; 9] = [
    Rule::Largest,
    Rule::Smallest,
    Rule::SmallestCatch,
    Rule::Exact,
    Rule::LeadOne,
    Rule::StayBehind,
    Rule::RepairThenSmallestCatch,
    Rule::RepairThenLargest,
    Rule::RepairLargest,
];

/// Adjacent partner of x on {1..n}: {2j−1, 2j} for even n; {2j, 2j+1} with 1 alone for odd n.
fn partner(x: usize, n: usize) -> Option<usize> {
    match (n % 2, x) {
        (0, _) => Some(if x % 2 == 1 { x + 1 } else { x - 1 }),
        (_, 1) => None,
        _ => Some(if x % 2 == 0 { x + 1 } else { x - 1 }),
    }
}

/// Numbers left whose partner is gone.
fn broken(mask: u32, n: usize) -> u32 {
    (1..=n)
        .filter(|&x| has(mask, x) && partner(x, n).is_some_and(|p| p <= n && !has(mask, p)))
        .fold(0, |b, x| b | 1 << (x - 1))
}

/// Among `candidates`: the smallest that catches up (≥ g), else the largest below g, else none.
fn repair(candidates: u32, g: usize) -> Option<usize> {
    (candidates != 0).then(|| smallest_catch(candidates, g))
}

fn has(mask: u32, x: usize) -> bool {
    x >= 1 && x <= 32 && mask >> (x - 1) & 1 == 1
}

fn largest(mask: u32) -> usize {
    (u32::BITS - mask.leading_zeros()) as usize
}

fn smallest_catch(mask: u32, g: usize) -> usize {
    let above = if g == 0 { mask } else { mask & !((1u32 << (g - 1)) - 1) };
    if above == 0 { largest(mask) } else { above.trailing_zeros() as usize + 1 }
}

impl Rule {
    fn pick(self, mask: u32, g: usize, n: usize) -> usize {
        debug_assert!(mask != 0);
        match self {
            Rule::RepairThenSmallestCatch => repair(broken(mask, n), g).unwrap_or_else(|| smallest_catch(mask, g)),
            Rule::RepairThenLargest => repair(broken(mask, n), g).unwrap_or_else(|| largest(mask)),
            Rule::RepairLargest => match broken(mask, n) {
                0 => largest(mask),
                b => largest(b),
            },
            Rule::Largest => largest(mask),
            Rule::Smallest => mask.trailing_zeros() as usize + 1,
            Rule::SmallestCatch => smallest_catch(mask, g),
            Rule::Exact => {
                if g > 0 && has(mask, g) { g } else { smallest_catch(mask, g) }
            }
            Rule::LeadOne => {
                if has(mask, g + 1) {
                    g + 1
                } else if g > 0 && has(mask, g) {
                    g
                } else {
                    smallest_catch(mask, g)
                }
            }
            Rule::StayBehind => {
                let below = if g <= 1 { 0 } else { mask & ((1u32 << (g - 1)) - 1) };
                if below == 0 { smallest_catch(mask, g) } else { largest(below) }
            }
        }
    }
}

/// Value tables over all positions of {1..n}: `rule[mask][g]` with the rule player to move,
/// `free[mask][g]` with the perfect player to move; values for the mover. With `rule = None`
/// both players are perfect and the two tables coincide.
struct Tables {
    n: usize,
    rule: Vec<u8>,
    free: Vec<u8>,
}

impl Tables {
    fn new(n: usize, rule: Option<Rule>) -> Self {
        let stride = n + 1;
        let size = (1usize << n) * stride;
        let (mut rt, mut ft) = (vec![0u8; size], vec![0u8; size]);
        let mut sums = vec![0usize; 1 << n];
        // Masks in increasing order: every move removes a bit, so successors come first.
        for mask in 0..1usize << n {
            if mask > 0 {
                sums[mask] = sums[mask & (mask - 1)] + mask.trailing_zeros() as usize + 1;
            }
            let m = mask as u32;
            for g in 0..=n {
                let i = mask * stride + g;
                if sums[mask] < g {
                    (rt[i], ft[i]) = (LOSS, LOSS); // cannot catch up even by taking everything
                    continue;
                }
                if mask == 0 {
                    (rt[i], ft[i]) = (DRAW, DRAW);
                    continue;
                }
                // Value of taking x for a mover whose own table is `own` and opponent's `opp`.
                let take = |x: usize, own: &[u8], opp: &[u8]| -> u8 {
                    let next = (mask & !(1 << (x - 1))) * stride;
                    if x >= g { neg(opp[next + x - g]) } else { own[next + g - x] }
                };
                let mut best = LOSS;
                let mut rest = m;
                while rest != 0 && best != WIN {
                    let x = rest.trailing_zeros() as usize + 1;
                    rest &= rest - 1;
                    best = best.max(match rule {
                        Some(_) => take(x, &ft, &rt),
                        None => take(x, &ft, &ft),
                    });
                }
                ft[i] = best;
                rt[i] = match rule {
                    Some(r) => take(r.pick(m, g, n), &rt, &ft),
                    None => best,
                };
            }
        }
        Tables { n, rule: rt, free: ft }
    }

    /// Player 1's value when player 1 follows the rule.
    fn rule_first(&self) -> u8 {
        self.rule[((1 << self.n) - 1) * (self.n + 1)]
    }

    /// Player 1's value when player 2 follows the rule.
    fn rule_second(&self) -> u8 {
        self.free[((1 << self.n) - 1) * (self.n + 1)]
    }
}

/// Independent recursive evaluation, no memo: the value for the mover; `rule_moves` says whether
/// the rule player is to move.
fn recursive(mask: u32, g: usize, rule: Rule, rule_moves: bool, n: usize) -> u8 {
    let sum: usize = (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum();
    if sum < g {
        return LOSS;
    }
    if mask == 0 {
        return DRAW;
    }
    let value_of = |x: usize| {
        let next = mask & !(1 << (x - 1));
        if x >= g { neg(recursive(next, x - g, rule, !rule_moves, n)) } else { recursive(next, g - x, rule, rule_moves, n) }
    };
    if rule_moves {
        value_of(rule.pick(mask, g, n))
    } else {
        (0..32).filter(|&i| mask >> i & 1 == 1).map(|i| value_of(i + 1)).max().unwrap()
    }
}

fn check(max_n: usize) {
    // Perfect play against `Solver`.
    for n in 1..=max_n.min(18) {
        let t = Tables::new(n, None);
        let mut dfs = Solver::new(&interval(n as u64));
        assert_eq!(decode(t.rule_first()), dfs.value(), "value of {{1..{n}}}");
        let mut state = 0x9E37_79B9_7F4A_7C15u64 ^ n as u64;
        for _ in 0..RANDOM_CHECKS {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let mask = (state as usize) & ((1 << n) - 1);
            let g = (state >> 40) as usize % (n + 1);
            assert_eq!(decode(t.free[mask * (n + 1) + g]), dfs.position(mask, g as u64), "n {n} mask {mask:b} gap {g}");
        }
    }
    // Rule tables against the recursive evaluation, every position.
    for n in 1..=RECURSIVE_CHECK_MAX_N {
        for rule in RULES {
            let t = Tables::new(n, Some(rule));
            for mask in 0..1u32 << n {
                for g in 0..=n {
                    let i = mask as usize * (n + 1) + g;
                    assert_eq!(t.rule[i], recursive(mask, g, rule, true, n), "{rule:?} n {n} mask {mask:b} gap {g}");
                    assert_eq!(t.free[i], recursive(mask, g, rule, false, n), "{rule:?} n {n} mask {mask:b} gap {g}");
                }
            }
        }
    }
}

fn letter(v: u8) -> char {
    ['L', 'D', 'W'][v as usize]
}

fn main() {
    let max_n: usize = std::env::args().nth(1).map_or(DEFAULT_MAX_N, |s| s.parse().expect("max_n must be a number"));
    assert!((1..=MAX_N).contains(&max_n), "max_n out of range");
    let start = Instant::now();
    check(max_n);
    println!("Checked: perfect play = `Solver` (N ≤ {}), rule tables = recursive evaluation (N ≤ {RECURSIVE_CHECK_MAX_N}). {} ms\n", max_n.min(18), start.elapsed().as_millis());
    println!("Player 1's value (W/D/L) with the rule as player 1 / as player 2, against a perfect opponent.");
    println!("A rule holds the draw at an even-total N when it shows D/D or better for its side: ≥ D / ≤ D.\n");
    let ns: Vec<usize> = (1..=max_n).collect();
    let header: Vec<String> = ns.iter().map(|n| if n * (n + 1) / 2 % 2 == 0 { format!("{n}*") } else { n.to_string() }).collect();
    println!("| rule | {} |", header.join(" | "));
    println!("|---|{}", "---|".repeat(ns.len()));
    let perfect: Vec<String> = ns.iter().map(|&n| letter(Tables::new(n, None).rule_first()).to_string()).collect();
    println!("| perfect | {} |", perfect.join(" | "));
    for rule in RULES {
        let cells: Vec<String> = ns
            .iter()
            .map(|&n| {
                let t = Tables::new(n, Some(rule));
                format!("{}/{}", letter(t.rule_first()), letter(t.rule_second()))
            })
            .collect();
        println!("| {rule:?} | {} |", cells.join(" | "));
    }
    println!("\n`*` = even total. Total {} ms", start.elapsed().as_millis());
}
