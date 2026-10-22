//! Usage: hole_game <n> [any] [measure]   (default 16)
//!        hole_game <n> line <measure> <defender 1|2> <h> [any]   prints one optimal line.
//! Can a defender keep the numbers left close to an interval until the endgame? On {1..n} the
//! defender D only makes picks that keep its value at least a draw; the attacker makes drawing picks
//! (a pick after which its value is still a draw), or any legal pick with `any`. Holes are checked
//! at D's turn starts (right after the attacker's turn ends). c(h) = the most numbers left at a turn
//! start of D with more than h holes that the attacker can force, 0 if none: a min-max value, D
//! minimizing. So D keeps holes ≤ h at every own turn start while more than c(h) numbers are left.
//! Four measures of holes (`Holes`), D = player 1 and D = player 2.

use catch_up::{interval, Solver};
use std::time::Instant;

const DEFAULT_N: usize = 16;
/// N = 24 needs about 7 GB.
const MAX_N: usize = 24;
/// Hole bounds h = 0..HOLE_BOUNDS−1.
const HOLE_BOUNDS: usize = 7;
const RECURSIVE_CHECK_MAX_N: usize = 8;
const VALUE_CHECK_MAX_N: usize = 12;

const LOSS: u8 = 0;
const DRAW: u8 = 1;
const WIN: u8 = 2;

fn neg(v: u8) -> u8 {
    WIN - v
}

fn max_number(mask: usize) -> usize {
    (usize::BITS - mask.leading_zeros()) as usize
}

/// How far the numbers left are from an interval.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Holes {
    /// Missing from {1..max}: max − |R|.
    BelowMax,
    /// Missing from {min..max}: max − min + 1 − |R|.
    Internal,
    /// Broken pairs among {2j−1, 2j} (n even) or {2j, 2j+1} with 1 alone (n odd): pairs with one
    /// number left.
    Adjacent,
    /// Broken pairs among {k, n+1−k}, the middle number alone when n is odd.
    Mirror,
}

const MEASURES: [Holes; 4] = [Holes::BelowMax, Holes::Internal, Holes::Adjacent, Holes::Mirror];

impl Holes {
    fn partner(self, x: usize, n: usize) -> Option<usize> {
        let p = match self {
            Holes::Adjacent if n % 2 == 0 => if x % 2 == 1 { x + 1 } else { x - 1 },
            Holes::Adjacent if x == 1 => return None,
            Holes::Adjacent => if x % 2 == 0 { x + 1 } else { x - 1 },
            Holes::Mirror => n + 1 - x,
            _ => unreachable!("only pairings have partners"),
        };
        (p != x).then_some(p)
    }

    fn count(self, mask: usize, n: usize) -> usize {
        match self {
            Holes::BelowMax => max_number(mask) - mask.count_ones() as usize,
            Holes::Internal if mask == 0 => 0,
            Holes::Internal => max_number(mask) - mask.trailing_zeros() as usize - mask.count_ones() as usize,
            Holes::Adjacent | Holes::Mirror => (1..=n)
                .filter(|&x| mask >> (x - 1) & 1 == 1)
                .filter(|&x| self.partner(x, n).is_some_and(|p| mask >> (p - 1) & 1 == 0))
                .count(),
        }
    }

    /// Numbers left if a turn start of D at `mask` breaks the bound h, else 0.
    fn cost(self, mask: usize, h: usize, n: usize) -> u8 {
        if self.count(mask, n) > h { mask.count_ones() as u8 } else { 0 }
    }
}

/// Which picks the attacker may make.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Attacker {
    /// Only picks after which its value is still a draw.
    Drawing,
    /// Any legal pick.
    Any,
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

/// One pick x from (mask, g): the remaining set, the index of the next position, whether it ends
/// the turn, and the mover's value after it.
fn step(v: &[u8], n: usize, mask: usize, g: usize, x: usize) -> (usize, usize, bool, u8) {
    let rest = mask & !(1 << (x - 1));
    let ends = x >= g;
    let j = rest * (n + 1) + if ends { x - g } else { g - x };
    (rest, j, ends, if ends { neg(v[j]) } else { v[j] })
}

/// May the mover make a pick leaving it at value `after`? D keeps at least a draw.
fn allowed(d_moves: bool, attacker: Attacker, after: u8) -> bool {
    match (d_moves, attacker) {
        (true, _) => after >= DRAW,
        (false, Attacker::Drawing) => after == DRAW,
        (false, Attacker::Any) => true,
    }
}

/// The two game tables, per bound h: `d` with D to pick (positions where D has at least a draw),
/// `a` with the attacker to pick (positions where the attacker has at most a draw).
struct Game {
    n: usize,
    holes: Holes,
    attacker: Attacker,
    v: Vec<u8>,
    d: Vec<[u8; HOLE_BOUNDS]>,
    a: Vec<[u8; HOLE_BOUNDS]>,
}

impl Game {
    fn new(n: usize, holes: Holes, attacker: Attacker) -> Self {
        let stride = n + 1;
        let v = values(n);
        let mut d = vec![[0u8; HOLE_BOUNDS]; (1 << n) * stride];
        let mut a = vec![[0u8; HOLE_BOUNDS]; (1 << n) * stride];
        let counts: Vec<usize> = (0..1usize << n).map(|mask| holes.count(mask, n)).collect();
        let cost = |mask: usize, h: usize| if counts[mask] > h { mask.count_ones() as u8 } else { 0 };
        let mut sums = vec![0usize; 1 << n];
        for mask in 1..1usize << n {
            sums[mask] = sums[mask & (mask - 1)] + mask.trailing_zeros() as usize + 1;
            // With g > sum the mover can't catch up: the game is over, both tables stay 0.
            for g in 0..=n.min(sums[mask]) {
                let i = mask * stride + g;
                let (mut dmin, mut amax) = ([u8::MAX; HOLE_BOUNDS], [0u8; HOLE_BOUNDS]);
                for x in (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1) {
                    let (rest, j, ends, after) = step(&v, n, mask, g, x);
                    for h in 0..HOLE_BOUNDS {
                        if v[i] >= DRAW && allowed(true, attacker, after) {
                            dmin[h] = dmin[h].min(if ends { a[j][h] } else { d[j][h] });
                        }
                        // The attacker's turn ends at a turn start of D: the bound is checked there.
                        if v[i] <= DRAW && allowed(false, attacker, after) {
                            amax[h] = amax[h].max(if ends { d[j][h].max(cost(rest, h)) } else { a[j][h] });
                        }
                    }
                }
                d[i] = if dmin[0] == u8::MAX { [0; HOLE_BOUNDS] } else { dmin };
                a[i] = amax;
            }
        }
        Game { n, holes, attacker, v, d, a }
    }

    fn start(&self) -> usize {
        ((1usize << self.n) - 1) * (self.n + 1)
    }

    /// c(h) with D = player 1 (the opening is a gap-0 turn of D) or player 2.
    fn value(&self, h: usize, d_first: bool) -> u8 {
        if d_first { self.d[self.start()][h] } else { self.a[self.start()][h] }
    }

    /// One optimal line for bound h from the opening: each turn's picks, the opponent's gap after it,
    /// D's holes at its turn starts; it stops at the first violation.
    fn line(&self, h: usize, d_first: bool) -> Vec<String> {
        let (n, stride) = (self.n, self.n + 1);
        let (mut mask, mut g, mut d_moves, mut player) = ((1usize << n) - 1, 0usize, d_first, 1);
        let (mut out, mut picks) = (Vec::new(), Vec::new());
        while mask != 0 && (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1).sum::<usize>() >= g {
            let i = mask * stride + g;
            let target = if d_moves { self.d[i][h] } else { self.a[i][h] };
            let x = (1..=n)
                .rev()
                .filter(|&x| mask >> (x - 1) & 1 == 1)
                .find(|&x| {
                    let (rest, j, ends, after) = step(&self.v, n, mask, g, x);
                    let val = match (d_moves, ends) {
                        (true, true) => self.a[j][h],
                        (true, false) => self.d[j][h],
                        (false, true) => self.d[j][h].max(self.holes.cost(rest, h, n)),
                        (false, false) => self.a[j][h],
                    };
                    allowed(d_moves, self.attacker, after) && val == target
                })
                .expect("an optimal allowed pick");
            picks.push(x.to_string());
            let (rest, _, ends, _) = step(&self.v, n, mask, g, x);
            if ends {
                let role = if d_moves { "D" } else { "A" };
                let mut s = format!("P{player} ({role}) takes {}, opponent trails by {}", picks.join(", "), x - g);
                if !d_moves {
                    let count = self.holes.count(rest, n);
                    s += &format!("; D's turn start with {} left: {count} {:?}", rest.count_ones(), self.holes);
                    if count > h {
                        out.push(s + &format!(" > {h}"));
                        break;
                    }
                }
                out.push(s);
                picks.clear();
                (g, d_moves, player) = (x - g, !d_moves, 3 - player);
            } else {
                g -= x;
            }
            mask = rest;
        }
        out
    }
}

/// Memo-free recursion over the same game: `d_moves` says who picks.
fn recursive(game: &Game, mask: usize, g: usize, h: usize, d_moves: bool) -> u8 {
    let n = game.n;
    if (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1).sum::<usize>() < g {
        return 0;
    }
    let mut out: Option<u8> = None;
    for x in (1..=n).filter(|&x| mask >> (x - 1) & 1 == 1) {
        let (rest, _, ends, after) = step(&game.v, n, mask, g, x);
        if !allowed(d_moves, game.attacker, after) {
            continue;
        }
        let next_g = if ends { x - g } else { g - x };
        let mut val = recursive(game, rest, next_g, h, if ends { !d_moves } else { d_moves });
        if ends && !d_moves {
            val = val.max(game.holes.cost(rest, h, n));
        }
        out = Some(match out {
            None => val,
            Some(o) if d_moves => o.min(val),
            Some(o) => o.max(val),
        });
    }
    out.unwrap_or(0)
}

fn check(n: usize, holes: Holes, attacker: Attacker) {
    let g = Game::new(n, holes, attacker);
    let stride = n + 1;
    let mut dfs = Solver::new(&interval(n as u64));
    for mask in 0..1usize << n {
        for gap in 0..=n {
            let i = mask * stride + gap;
            assert_eq!(g.v[i], dfs.position(mask, gap as u64) as u8, "value n {n} mask {mask:b} gap {gap}");
            if n > RECURSIVE_CHECK_MAX_N || mask == 0 {
                continue;
            }
            for h in 0..HOLE_BOUNDS {
                if g.v[i] >= DRAW {
                    assert_eq!(g.d[i][h], recursive(&g, mask, gap, h, true), "d n {n} mask {mask:b} gap {gap} h {h}");
                }
                if g.v[i] <= DRAW {
                    assert_eq!(g.a[i][h], recursive(&g, mask, gap, h, false), "a n {n} mask {mask:b} gap {gap} h {h}");
                }
            }
        }
    }
}

fn parse_measure(s: &str) -> Option<Holes> {
    MEASURES.iter().copied().find(|m| format!("{m:?}") == s)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).map_or(DEFAULT_N, |s| s.parse().expect("n must be a number"));
    assert!((1..=MAX_N).contains(&n), "n out of range");
    let attacker = if args.iter().any(|s| s == "any") { Attacker::Any } else { Attacker::Drawing };
    if args.get(2).is_some_and(|s| s == "line") {
        let holes = parse_measure(&args[3]).expect("measure name");
        let (d_first, h): (bool, usize) = (args[4] == "1", args[5].parse().expect("h"));
        let g = Game::new(n, holes, attacker);
        println!("N = {n}, {holes:?}, attacker {attacker:?}, D = player {}, h = {h}, c(h) = {}:", args[4], g.value(h, d_first));
        for s in g.line(h, d_first) {
            println!("- {s}");
        }
        return;
    }
    let measures: Vec<Holes> = match args.iter().skip(2).find_map(|s| parse_measure(s)) {
        Some(m) => vec![m],
        None => MEASURES.to_vec(),
    };
    let start = Instant::now();
    for &holes in &measures {
        for m in 1..=n.min(VALUE_CHECK_MAX_N) {
            check(m, holes, attacker);
        }
    }
    println!("Attacker {attacker:?}. Checked: values = `Solver` on every position (n ≤ {VALUE_CHECK_MAX_N}), game tables = recursion (n ≤ {RECURSIVE_CHECK_MAX_N}).\n");
    println!("c(h) = the most numbers left at a turn start of D with more than h holes that the attacker can force.\n");
    for &holes in &measures {
        println!("### Holes {holes:?}\n");
        let hs: Vec<String> = (0..HOLE_BOUNDS).map(|h| format!("h={h}")).collect();
        println!("| N | defender | {} |\n|---|---|{}", hs.join(" | "), "---|".repeat(HOLE_BOUNDS));
        for m in (1..=n).filter(|&m| m * (m + 1) / 2 % 2 == 0 && m >= 7) {
            let g = Game::new(m, holes, attacker);
            for (d_first, name) in [(true, "player 1"), (false, "player 2")] {
                let cells: Vec<String> = (0..HOLE_BOUNDS).map(|h| g.value(h, d_first).to_string()).collect();
                println!("| {m} | {name} | {} |", cells.join(" | "));
            }
        }
        println!();
    }
    println!("Total {} ms", start.elapsed().as_millis());
}
