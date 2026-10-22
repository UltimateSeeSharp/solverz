//! Usage: partner_game [max_n]   (default 20)
//! When must a pairing defender refuse the partner? Pairs are adjacent: {2j−1, 2j} for even n,
//! {2j, 2j+1} with 1 alone for odd n. On even-total {1..n} the attacker makes any drawing pick; the
//! defender D starts each turn with the partner p of the attacker's last pick y when p is left and
//! taking it keeps the draw, and otherwise ("refuse", or no partner) makes any drawing pick. Over
//! every position this play can reach, tally D's turn starts where p is left: how often p loses,
//! by the opponent's deficit after p relative to what is left, and by numbers left.

use catch_up::{interval, Solver};
use std::time::Instant;

const DEFAULT_MAX_N: usize = 20;
const MAX_N: usize = 22;
const CHECK_MAX_N: usize = 12;
/// Buckets of r = (p − g) / sum(R ∖ p) for turn-ending replies: upper bounds.
const RATIO_BOUNDS: [f64; 6] = [0.05, 0.1, 0.15, 0.2, 0.3, f64::INFINITY];
const SHOWN: usize = 8;

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

/// Mover's values V(mask, g), g ≤ n: gaps never exceed the largest number.
fn values(n: usize) -> Vec<u8> {
    let stride = n + 1;
    let mut v = vec![LOSS; (1 << n) * stride];
    let mut sums = vec![0usize; 1 << n];
    v[0] = DRAW;
    for mask in 1..1usize << n {
        sums[mask] = sums[mask & (mask - 1)] + mask.trailing_zeros() as usize + 1;
        for g in 0..=n.min(sums[mask]) {
            let mut best = LOSS;
            for x in (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1) {
                let next = (mask & !(1 << (x - 1))) * stride;
                best = best.max(if x >= g { neg(v[next + x - g]) } else { v[next + g - x] });
                if best == WIN {
                    break;
                }
            }
            v[mask * stride + g] = best;
        }
    }
    v
}

fn partner(x: usize, n: usize) -> Option<usize> {
    match (n % 2, x) {
        (0, _) => Some(if x % 2 == 1 { x + 1 } else { x - 1 }),
        (_, 1) => None,
        _ => Some(if x % 2 == 0 { x + 1 } else { x - 1 }),
    }
}

fn has(mask: usize, x: usize) -> bool {
    mask >> (x - 1) & 1 == 1
}

fn sum_of(mask: usize) -> usize {
    (0..usize::BITS as usize).filter(|&i| mask >> i & 1 == 1).map(|i| i + 1).sum()
}

fn broken(mask: usize, n: usize) -> usize {
    (1..=n).filter(|&x| has(mask, x) && partner(x, n).is_some_and(|p| !has(mask, p))).count()
}

fn show(mask: usize, n: usize) -> String {
    let xs: Vec<String> = (1..=n).filter(|&x| has(mask, x)).map(|x| x.to_string()).collect();
    format!("{{{}}}", xs.join(","))
}

/// A bitset over (mask, gap[, last pick]) states.
struct Seen {
    bits: Vec<u64>,
}

impl Seen {
    fn new(states: usize) -> Self {
        Seen { bits: vec![0; states.div_ceil(64)] }
    }

    /// Marks a state; true if it was new.
    fn insert(&mut self, i: usize) -> bool {
        let (w, b) = (i / 64, 1u64 << (i % 64));
        let new = self.bits[w] & b == 0;
        self.bits[w] |= b;
        new
    }
}

#[derive(Clone, Copy)]
enum State {
    /// The attacker to pick at (mask, g).
    Attacker(usize, usize),
    /// D's turn start after the attacker's turn ended with pick y.
    DefenderStart(usize, usize, usize),
    /// D to pick, free (mid-turn, or a turn start without a partner to answer).
    Defender(usize, usize),
}

/// A turn start of D where the partner p of y is left.
struct Reply {
    mask: usize,
    g: usize,
    y: usize,
    p: usize,
    refuse: bool,
}

/// Explores the reachable states; returns D's turn starts with the partner left.
fn explore(n: usize, v: &[u8], d_first: bool) -> Vec<Reply> {
    let stride = n + 1;
    let full = (1usize << n) - 1;
    let (mut seen_a, mut seen_d) = (Seen::new((1 << n) * stride), Seen::new((1 << n) * stride));
    let mut seen_start = Seen::new((1 << n) * stride * stride);
    let mut replies = Vec::new();
    let mut stack = vec![if d_first { State::Defender(full, 0) } else { State::Attacker(full, 0) }];
    // Drawing picks of the mover at (mask, g): (x, next state for the given mover role).
    let drawing = |mask: usize, g: usize| -> Vec<(usize, usize, bool)> {
        (1..=n)
            .filter(|&x| has(mask, x))
            .filter_map(|x| {
                let rest = mask & !(1 << (x - 1));
                let ends = x >= g;
                let after = if ends { neg(v[rest * stride + x - g]) } else { v[rest * stride + g - x] };
                (after == DRAW).then_some((x, rest, ends))
            })
            .collect()
    };
    while let Some(s) = stack.pop() {
        match s {
            State::Attacker(mask, g) => {
                if mask == 0 || !seen_a.insert(mask * stride + g) {
                    continue;
                }
                for (x, rest, ends) in drawing(mask, g) {
                    stack.push(if ends { State::DefenderStart(rest, x - g, x) } else { State::Attacker(rest, g - x) });
                }
            }
            State::DefenderStart(mask, g, y) => {
                if mask == 0 || !seen_start.insert((mask * stride + g) * stride + y) {
                    continue;
                }
                let moves = drawing(mask, g);
                match partner(y, n).filter(|&p| has(mask, p)) {
                    Some(p) => {
                        let ok = moves.iter().find(|m| m.0 == p).copied();
                        replies.push(Reply { mask, g, y, p, refuse: ok.is_none() });
                        let chosen: Vec<(usize, usize, bool)> = match ok {
                            Some(m) => vec![m],
                            None => moves,
                        };
                        for (x, rest, ends) in chosen {
                            stack.push(if ends { State::Attacker(rest, x - g) } else { State::Defender(rest, g - x) });
                        }
                    }
                    None => stack.push(State::Defender(mask, g)),
                }
            }
            State::Defender(mask, g) => {
                if mask == 0 || !seen_d.insert(mask * stride + g) {
                    continue;
                }
                for (x, rest, ends) in drawing(mask, g) {
                    stack.push(if ends { State::Attacker(rest, x - g) } else { State::Defender(rest, g - x) });
                }
            }
        }
    }
    replies
}

fn check(n: usize) {
    let stride = n + 1;
    let v = values(n);
    let mut dfs = Solver::new(&interval(n as u64));
    for mask in 0..1usize << n {
        for g in 0..=n {
            assert_eq!(v[mask * stride + g], dfs.position(mask, g as u64) as u8, "n {n} mask {mask:b} gap {g}");
        }
    }
}

fn bucket(r: f64) -> usize {
    RATIO_BOUNDS.iter().position(|&b| r < b).unwrap()
}

fn report(n: usize, v: &[u8], d_first: bool, replies: &[Reply]) {
    let refused = replies.iter().filter(|r| r.refuse).count();
    println!("#### D = player {}: {} turn starts with the partner left, {refused} refusals\n", if d_first { 1 } else { 2 }, replies.len());
    // Turn-ending replies by r = new gap / sum left after p.
    let mut ratio = [(0u64, 0u64); RATIO_BOUNDS.len()];
    let mut continuing = (0u64, 0u64);
    for r in replies {
        let rest = r.mask & !(1 << (r.p - 1));
        if r.p >= r.g {
            let sum = sum_of(rest).max(1);
            let cell = &mut ratio[bucket((r.p - r.g) as f64 / sum as f64)];
            cell.0 += 1;
            cell.1 += r.refuse as u64;
        } else {
            continuing.0 += 1;
            continuing.1 += r.refuse as u64;
        }
    }
    // Refusals where p is the only pick that doesn't keep the draw.
    let stride = n + 1;
    let losing_picks = |r: &Reply| {
        (1..=n)
            .filter(|&x| has(r.mask, x))
            .filter(|&x| {
                let rr = r.mask & !(1 << (x - 1));
                (if x >= r.g { neg(v[rr * stride + x - r.g]) } else { v[rr * stride + r.g - x] }) != DRAW
            })
            .count()
    };
    let only = replies.iter().filter(|r| r.refuse && losing_picks(r) == 1).count();
    println!("Refusals where p is the only losing pick: {only} of {refused}.\n");
    let heads: Vec<String> = RATIO_BOUNDS.iter().map(|b| if b.is_infinite() { "≥ 0.3".to_string() } else { format!("< {b}") }).collect();
    println!("Turn-ending replies by (p − g) / sum(R ∖ p), refusals / cases:\n");
    println!("| {} | p < g (turn continues) |\n|{}---|", heads.join(" | "), "---|".repeat(RATIO_BOUNDS.len()));
    let cells: Vec<String> = ratio.iter().map(|(c, f)| format!("{f} / {c}")).collect();
    println!("| {} | {} / {} |\n", cells.join(" | "), continuing.1, continuing.0);
    let mut shown: Vec<&Reply> = replies.iter().filter(|r| r.refuse).collect();
    shown.sort_by_key(|r| (std::cmp::Reverse(r.mask.count_ones()), r.mask, r.g, r.y));
    println!("Refusals with the most numbers left:\n");
    for r in shown.iter().take(SHOWN) {
        let rest = r.mask & !(1 << (r.p - 1));
        let alts: Vec<String> = (1..=n)
            .filter(|&x| has(r.mask, x))
            .filter(|&x| {
                let rr = r.mask & !(1 << (x - 1));
                (if x >= r.g { neg(v[rr * stride + x - r.g]) } else { v[rr * stride + r.g - x] }) == DRAW
            })
            .map(|x| x.to_string())
            .collect();
        let after = if r.p >= r.g { format!("opponent trails by {} with sum {}", r.p - r.g, sum_of(rest)) } else { format!("D still behind by {}", r.g - r.p) };
        println!(
            "- R = {} (sum {}, {} broken), g = {}, y = {}, p = {}: {after}; drawing picks {}",
            show(r.mask, n),
            sum_of(r.mask),
            broken(r.mask, n),
            r.g,
            r.y,
            r.p,
            alts.join(",")
        );
    }
    println!();
}

fn main() {
    let max_n: usize = std::env::args().nth(1).map_or(DEFAULT_MAX_N, |s| s.parse().expect("max_n must be a number"));
    assert!((1..=MAX_N).contains(&max_n), "max_n out of range");
    let start = Instant::now();
    for n in 1..=max_n.min(CHECK_MAX_N) {
        check(n);
    }
    // The refuter's line at n = 11, D = player 1: D1 | A2 | D3 | A10 | D11 | A6, then the partner 7 loses.
    if max_n >= 11 {
        let v = values(11);
        let line_end = explore(11, &v, true);
        let mask = [4, 5, 7, 8, 9].iter().fold(0usize, |m, &x| m | 1 << (x - 1));
        assert!(line_end.iter().any(|r| r.mask == mask && r.g == 3 && r.y == 6 && r.refuse), "known refusal at n = 11");
    }
    println!("Values checked against `Solver` (n ≤ {}); the known refusal at n = 11 is found.\n", max_n.min(CHECK_MAX_N));
    for n in (7..=max_n).filter(|&n| n * (n + 1) / 2 % 2 == 0) {
        println!("### N = {n}\n");
        let v = values(n);
        for d_first in [true, false] {
            report(n, &v, d_first, &explore(n, &v, d_first));
        }
    }
    println!("Total {} ms", start.elapsed().as_millis());
}
