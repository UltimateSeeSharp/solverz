//! Usage: lead_regime check
//!        lead_regime intervals <max_n> <num> <den> <off> <max_picks>
//!        lead_regime blocks <max_p> <max_a> <num> <den> <off> <max_picks>
//!        lead_regime rules <max_n> <num> <den> <off> <max_picks>
//!        lead_regime ranges <lo> <hi_max> <gap> <num> <den> <off> <max_picks>   ({lo..hi} at the gap, total + gap even)
//!        (in each, `<num> <den> <off>` may be `s2`: the cap is the sum of the two smallest numbers left)
//! Can the defender keep the game in a bounded-turn regime and still draw (B31)? The defender D must
//! end each of its turns with the opponent trailing by at most ⌊num·m/den⌋ + off, m the smallest
//! number left, using at most `max_picks` picks per turn; the opponent plays perfectly and freely.
//! D with no allowed turn loses. Prints D's value as player 1 and as player 2 on {1..N} (even
//! totals), or on blocks {a..a+2p−1} at gap p mod 2 as mover and as the other player.
//! `rules`: D follows one fixed choice among its allowed turns (A perfect); first failing N per rule.
//! `check`: with no restriction the engine must match `Solver` (random sets and intervals).

use catch_up::{interval, Outcome, Solver};
use std::time::Instant;

const CHECK_SETS: usize = 300;
const CHECK_MAX_NUMBERS: usize = 11;
const CHECK_MAX_VALUE: u64 = 30;
const CHECK_INTERVAL_MAX_N: u64 = 12;
const ENTRIES_PER_BYTE: usize = 4;
const UNKNOWN: u8 = 0;
const TWO_SMALLEST_ARG: &str = "s2";

/// 2-bit memo over (numbers left, gap).
struct Table {
    bytes: Vec<u8>,
    stride: usize,
}

impl Table {
    fn new(n: usize, stride: usize) -> Self {
        Table { bytes: vec![0; ((1usize << n) * stride).div_ceil(ENTRIES_PER_BYTE)], stride }
    }

    fn slot(&self, mask: usize, gap: u64) -> (usize, usize) {
        let i = mask * self.stride + gap as usize;
        (i / ENTRIES_PER_BYTE, 2 * (i % ENTRIES_PER_BYTE))
    }

    fn get(&self, mask: usize, gap: u64) -> Option<Outcome> {
        let (b, s) = self.slot(mask, gap);
        match (self.bytes[b] >> s) & 0b11 {
            UNKNOWN => None,
            1 => Some(Outcome::Loss),
            2 => Some(Outcome::Draw),
            _ => Some(Outcome::Win),
        }
    }

    fn set(&mut self, mask: usize, gap: u64, o: Outcome) {
        let (b, s) = self.slot(mask, gap);
        self.bytes[b] |= (o as u8 + 1) << s;
    }
}

/// The bound on the opponent's deficit after D's turn.
#[derive(Clone, Copy)]
enum Cap {
    /// ⌊num·m/den⌋ + off, m the smallest number left.
    Linear { num: u64, den: u64, off: i64 },
    /// The sum of the two smallest numbers left: the opponent catches up within two picks.
    TwoSmallest,
}

/// The defender's restriction; `None` cap means unrestricted.
#[derive(Clone, Copy)]
struct Regime {
    cap: Option<Cap>,
    max_picks: usize,
}

impl Regime {
    fn allows(&self, lead: u64, smallest: u64, two_smallest: u64) -> bool {
        match self.cap {
            None => true,
            Some(Cap::Linear { num, den, off }) => (lead as i64) <= (num * smallest / den) as i64 + off,
            Some(Cap::TwoSmallest) => lead <= two_smallest,
        }
    }
}

/// A fixed choice among D's allowed turns, by a key over (lead, picks, largest pick, sum taken).
#[derive(Clone, Copy, Debug)]
enum Rule {
    /// Least lead, then fewest picks, then the largest pick.
    MinLead,
    /// Greatest allowed lead, then fewest picks.
    MaxLead,
    /// Largest single pick, then least lead.
    LargestPick,
    /// Least amount taken, then least lead.
    LeastTaken,
    /// Fewest picks, then largest pick, then least lead.
    FewestLargest,
}

const RULES: [Rule; 5] = [Rule::MinLead, Rule::MaxLead, Rule::LargestPick, Rule::LeastTaken, Rule::FewestLargest];

/// One allowed D turn: numbers left after it, their sum, D's lead, picks, largest pick, amount taken.
#[derive(Clone, Copy)]
struct Turn {
    mask: usize,
    sum: u64,
    lead: u64,
    picks: usize,
    largest: u64,
    taken: u64,
}

impl Rule {
    fn key(self, t: &Turn) -> (i64, i64, i64) {
        let (l, k, m, s) = (t.lead as i64, t.picks as i64, t.largest as i64, t.taken as i64);
        match self {
            Rule::MinLead => (l, k, -m),
            Rule::MaxLead => (-l, k, 0),
            Rule::LargestPick => (-m, l, 0),
            Rule::LeastTaken => (s, l, 0),
            Rule::FewestLargest => (k, -m, l),
        }
    }
}

/// Values from D's point of view.
struct Game {
    numbers: Vec<u64>,
    regime: Regime,
    rule: Option<Rule>,
    d_table: Table,
    a_table: Table,
}

fn of_lead(lead: i64) -> Outcome {
    match lead.cmp(&0) {
        std::cmp::Ordering::Greater => Outcome::Win,
        std::cmp::Ordering::Equal => Outcome::Draw,
        std::cmp::Ordering::Less => Outcome::Loss,
    }
}

impl Game {
    fn new(numbers: &[u64], regime: Regime) -> Self {
        let stride = *numbers.iter().max().unwrap() as usize + 1;
        let n = numbers.len();
        Game { numbers: numbers.to_vec(), regime, rule: None, d_table: Table::new(n, stride), a_table: Table::new(n, stride) }
    }

    /// Every allowed D turn from `mask` trailing by `need`, `picks` picks in, `taken` so far.
    fn turns(&self, mask: usize, sum: u64, need: u64, picks: usize, largest: u64, taken: u64, out: &mut Vec<Turn>) {
        let mut rest = mask;
        while rest != 0 {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            if x >= need {
                // An opponent who cannot catch up at all has lost, whatever the cap.
                if next == 0 || x - need > sum - x || self.regime.allows(x - need, self.min_left(next), self.two_smallest(next)) {
                    out.push(Turn { mask: next, sum: sum - x, lead: x - need, picks: picks + 1, largest: largest.max(x), taken: taken + x });
                }
            } else if picks + 1 < self.regime.max_picks && next != 0 {
                self.turns(next, sum - x, need - x, picks + 1, largest.max(x), taken + x, out);
            }
        }
    }

    /// D's value when it plays `rule`'s turn.
    fn rule_turn(&mut self, rule: Rule, mask: usize, sum: u64, need: u64) -> Outcome {
        let mut ts = Vec::new();
        self.turns(mask, sum, need, 0, 0, 0, &mut ts);
        match ts.iter().min_by_key(|t| rule.key(t)) {
            Some(t) => {
                let t = *t;
                self.after_d_turn(t.mask, t.sum, t.lead).expect("allowed")
            }
            None => Outcome::Loss,
        }
    }

    fn min_left(&self, mask: usize) -> u64 {
        self.numbers[mask.trailing_zeros() as usize]
    }

    /// The sum of the two smallest numbers in `mask` (the one number if only one).
    fn two_smallest(&self, mask: usize) -> u64 {
        let rest = mask & (mask - 1);
        self.min_left(mask) + if rest == 0 { 0 } else { self.min_left(rest) }
    }

    fn sum(&self, mask: usize) -> u64 {
        (0..self.numbers.len()).filter(|&i| mask >> i & 1 == 1).map(|i| self.numbers[i]).sum()
    }

    /// D ended its turn leading by `lead` with `mask` left.
    fn after_d_turn(&mut self, mask: usize, sum: u64, lead: u64) -> Option<Outcome> {
        if mask == 0 {
            return Some(of_lead(lead as i64));
        }
        // A lead beyond everything left wins outright, whatever the cap.
        (lead > sum || self.regime.allows(lead, self.min_left(mask), self.two_smallest(mask))).then(|| self.a_node(mask, sum, lead))
    }

    /// D at a turn start trailing by `gap`.
    fn d_turn(&mut self, mask: usize, sum: u64, gap: u64) -> Outcome {
        if mask == 0 {
            return of_lead(-(gap as i64));
        }
        if sum < gap {
            return Outcome::Loss;
        }
        if let Some(o) = self.d_table.get(mask, gap) {
            return o;
        }
        let best = match self.rule {
            Some(rule) => self.rule_turn(rule, mask, sum, gap),
            None => self.d_picks(mask, sum, gap, 0, Outcome::Loss),
        };
        self.d_table.set(mask, gap, best);
        best
    }

    /// D mid-turn, still needing `need`, after `picks` picks; returns the best of `best` and every
    /// allowed completion of the turn.
    fn d_picks(&mut self, mask: usize, sum: u64, need: u64, picks: usize, mut best: Outcome) -> Outcome {
        let mut rest = mask;
        while rest != 0 && best != Outcome::Win {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            if x >= need {
                if let Some(o) = self.after_d_turn(next, sum - x, x - need) {
                    best = best.max(o);
                }
            } else if picks + 1 < self.regime.max_picks && next != 0 {
                best = self.d_picks(next, sum - x, need - x, picks + 1, best);
            }
        }
        best
    }

    /// A to move (turn start or mid-turn) trailing by `gap`.
    fn a_node(&mut self, mask: usize, sum: u64, gap: u64) -> Outcome {
        if mask == 0 {
            return of_lead(gap as i64);
        }
        if sum < gap {
            return Outcome::Win;
        }
        if let Some(o) = self.a_table.get(mask, gap) {
            return o;
        }
        let mut worst = Outcome::Win;
        let mut rest = mask;
        while rest != 0 && worst != Outcome::Loss {
            let i = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            let x = self.numbers[i];
            let next = mask & !(1 << i);
            let o = if x >= gap { self.d_turn(next, sum - x, x - gap) } else { self.a_node(next, sum - x, gap - x) };
            worst = worst.min(o);
        }
        self.a_table.set(mask, gap, worst);
        worst
    }

    fn full(&self) -> usize {
        (1usize << self.numbers.len()) - 1
    }

    /// D opens (one pick).
    fn d_first(&mut self) -> Outcome {
        let full = self.full();
        let total = self.sum(full);
        if let Some(rule) = self.rule {
            let saved = self.regime.max_picks;
            self.regime.max_picks = 1;
            let o = self.rule_turn(rule, full, total, 0);
            self.regime.max_picks = saved;
            return o;
        }
        let mut best = Outcome::Loss;
        for i in 0..self.numbers.len() {
            let x = self.numbers[i];
            if let Some(o) = self.after_d_turn(full & !(1 << i), total - x, x) {
                best = best.max(o);
            }
        }
        best
    }

    /// A opens (one pick).
    fn d_second(&mut self) -> Outcome {
        let full = self.full();
        let total = self.sum(full);
        (0..self.numbers.len())
            .map(|i| self.d_turn(full & !(1 << i), total - self.numbers[i], self.numbers[i]))
            .min()
            .unwrap()
    }
}

fn arg<T: std::str::FromStr>(args: &[String], i: usize) -> T {
    args.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| panic!("argument {i} missing or invalid"))
}

/// `<num> <den> <off> <max_picks>` (linear cap) or `s2 <max_picks>` (two smallest).
fn regime(args: &[String], at: usize) -> Regime {
    if args.get(at).map(String::as_str) == Some(TWO_SMALLEST_ARG) {
        return Regime { cap: Some(Cap::TwoSmallest), max_picks: arg(args, at + 1) };
    }
    let cap = Cap::Linear { num: arg(args, at), den: arg(args, at + 1), off: arg(args, at + 2) };
    Regime { cap: Some(cap), max_picks: arg(args, at + 3) }
}

fn show(o: Outcome) -> &'static str {
    match o {
        Outcome::Win => "W",
        Outcome::Draw => "D",
        Outcome::Loss => "L",
    }
}

/// Unrestricted engine against `Solver`.
fn check() {
    let free = Regime { cap: None, max_picks: usize::MAX };
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut sets: Vec<Vec<u64>> = (1..=CHECK_INTERVAL_MAX_N).map(interval).collect();
    for _ in 0..CHECK_SETS {
        let k = 1 + (next() as usize) % CHECK_MAX_NUMBERS;
        let mut xs: Vec<u64> = Vec::new();
        while xs.len() < k {
            let x = 1 + next() % CHECK_MAX_VALUE;
            if !xs.contains(&x) {
                xs.push(x);
            }
        }
        xs.sort();
        sets.push(xs);
    }
    let mut bad = 0;
    for xs in &sets {
        let mut s = Solver::new(xs);
        let v = s.value();
        let mut g = Game::new(xs, free);
        let (first, second) = (g.d_first(), g.d_second());
        let full = (1usize << xs.len()) - 1;
        let top = 3.min(*xs.iter().max().unwrap());
        let pos_ok = (0..=top).all(|gap| s.position(full, gap) == g.d_turn(full, g.sum(full), gap));
        if first != v || second != v.neg() || !pos_ok {
            bad += 1;
            println!("mismatch {xs:?}: solver {v:?}, engine {first:?}/{second:?}, positions ok {pos_ok}");
        }
    }
    println!("check: {} sets, {bad} mismatches", sets.len());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let start = Instant::now();
    match args.get(1).map(String::as_str) {
        Some("check") => check(),
        Some("intervals") => {
            let max_n: u64 = arg(&args, 2);
            let r = regime(&args, 3);
            println!("| N | D as player 1 | D as player 2 |\n|---|---|---|");
            for n in (1..=max_n).filter(|n| (n * (n + 1) / 2) % 2 == 0) {
                let mut g = Game::new(&interval(n), r);
                println!("| {n} | {} | {} |", show(g.d_first()), show(g.d_second()));
            }
        }
        Some("ranges") => {
            let (lo, hi_max, gap): (u64, u64, u64) = (arg(&args, 2), arg(&args, 3), arg(&args, 4));
            let r = regime(&args, 5);
            println!("| hi | D as mover | D as other |
|---|---|---|");
            for hi in (lo..=hi_max).filter(|hi| ((lo..=*hi).sum::<u64>() + gap) % 2 == 0) {
                let xs: Vec<u64> = (lo..=hi).collect();
                let mut g = Game::new(&xs, r);
                let full = g.full();
                let sum = g.sum(full);
                println!("| {hi} | {} | {} |", show(g.d_turn(full, sum, gap)), show(g.a_node(full, sum, gap)));
            }
        }
        Some("rules") => {
            let max_n: u64 = arg(&args, 2);
            let r = regime(&args, 3);
            for rule in RULES {
                let fail = (1..=max_n).filter(|n| (n * (n + 1) / 2) % 2 == 0).find_map(|n| {
                    let mut g = Game::new(&interval(n), r);
                    g.rule = Some(rule);
                    let (first, second) = (g.d_first(), g.d_second());
                    (first < Outcome::Draw || second < Outcome::Draw).then(|| format!("N = {n} ({}/{})", show(first), show(second)))
                });
                println!("{rule:?}: first failure {}", fail.unwrap_or_else(|| format!("none up to {max_n}")));
            }
        }
        Some("blocks") => {
            let (max_p, max_a): (u64, u64) = (arg(&args, 2), arg(&args, 3));
            let r = regime(&args, 4);
            println!("p: heights a ≤ {max_a} where D fails to draw at gap p mod 2 (as mover / as other)");
            for p in 1..=max_p {
                let mut fails = Vec::new();
                for a in 1..=max_a {
                    let xs: Vec<u64> = (a..a + 2 * p).collect();
                    let mut g = Game::new(&xs, r);
                    let full = g.full();
                    let sum = g.sum(full);
                    let (as_mover, as_other) = (g.d_turn(full, sum, p % 2), g.a_node(full, sum, p % 2));
                    if as_mover < Outcome::Draw || as_other < Outcome::Draw {
                        fails.push(format!("a={a} ({}/{})", show(as_mover), show(as_other)));
                    }
                }
                println!("p = {p}: {}", if fails.is_empty() { "none".to_string() } else { fails.join(", ") });
            }
        }
        _ => panic!("usage: lead_regime check | intervals <max_n> <num> <den> <off> <max_picks> | blocks <max_p> <max_a> <num> <den> <off> <max_picks>"),
    }
    eprintln!("{:.1} s", start.elapsed().as_secs_f64());
}
