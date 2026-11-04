//! Usage: e24_collapsed_rounds <p_min> <p_max> <threads>
//! I16 (b), (c): Z strategies in the rounds game (C13) on O_t = ⊎_{i<p} {2i, 2i + t_i} at debt |t| mod 2, both
//! roles, Y optimal. Answers: Hyb2 (C24: smallest valid j, else AM+T), Hyb2 with the partner as fallback, or the twin
//! of Y's pick when present, else Hyb2 on the part without full twin pairs ((c)); Free = Z's best. First picks: max,
//! the top of the highest or lowest bumped pair, or Free. A failure under a Free first pick means no first-pick rule
//! works with that answer. Prints per p and strategy the failing (t, role) count, over all t and over (c)'s family
//! t = 0^k 1^(p−k), 2k ≥ p. Free/Free only for p ≤ FREE_FREE_MAX_P. A mover trailing by more than spread(R) loses
//! outright (exact cut-off). For p ≤ EXTRACT_MAX_P it also lists, under Hyb2's answers with free first picks, the
//! reached Z starts where max R does not draw and the first picks that do (the data for a first-pick rule).
//! First checks: Free/Free = `Solver` on {a + o} with a = d + sum + 1 (C13) on every even sub-multiset for p ≤ CHECK_P,
//! d ≤ CHECK_D; Hyb2/Max never fails on t = 1…1 (C24, Lean); Hyb2/Max loses ({0, 1, 2, 2, 4, 4}, Z first at debt 1),
//! the ideator's `hyb2near` example.

use catch_up::{Outcome, Solver};
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Answer {
    Hyb2,
    Hyb2Partner,
    TwinHyb2,
    Free,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum First {
    Max,
    HighBumpTop,
    LowBumpTop,
    Free,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mover {
    Z,
    Y,
}

const STRATEGIES: [(Answer, First); 13] = [
    (Answer::Free, First::Free),
    (Answer::Hyb2, First::Free),
    (Answer::Hyb2, First::Max),
    (Answer::Hyb2, First::HighBumpTop),
    (Answer::Hyb2, First::LowBumpTop),
    (Answer::Hyb2Partner, First::Free),
    (Answer::Hyb2Partner, First::Max),
    (Answer::Hyb2Partner, First::HighBumpTop),
    (Answer::Hyb2Partner, First::LowBumpTop),
    (Answer::TwinHyb2, First::Free),
    (Answer::TwinHyb2, First::Max),
    (Answer::TwinHyb2, First::HighBumpTop),
    (Answer::TwinHyb2, First::LowBumpTop),
];
/// Free/Free (the exact rounds value) only up to this p: the baseline, with the most states.
const FREE_FREE_MAX_P: usize = 8;
/// Hyb2/Free's reached Z starts where max R fails are listed up to this p.
const EXTRACT_MAX_P: usize = 7;
const SHOWN_BREAKS: usize = 20;
const CHECK_P: usize = 3;
const CHECK_D: i32 = 3;
const IDEATOR_EXAMPLE: [u8; 6] = [0, 1, 2, 2, 4, 4];
const IDEATOR_DEBT: i32 = 1;
const WIN: i8 = 1;
const DRAW: i8 = 0;
const LOSS: i8 = -1;
const DEBT_BITS: u32 = 16;
const BASE: u64 = 3;

/// Sorted offsets, each value at most twice.
type Set = Vec<u8>;

/// Bottom-up matching cost c(R).
fn cost(r: &[u8]) -> i32 {
    r.chunks(2).map(|c| if c.len() == 2 { (c[1] - c[0]) as i32 } else { 0 }).sum()
}

/// Top half minus bottom half: each player takes |R|/2 numbers, so the mover's margin is ≤ spread(R) − d.
fn spread(r: &[u8]) -> i32 {
    let h = r.len() / 2;
    r[h..].iter().map(|&x| x as i32).sum::<i32>() - r[..h].iter().map(|&x| x as i32).sum::<i32>()
}

fn without(r: &[u8], k: usize) -> Set {
    let mut v = r.to_vec();
    v.remove(k);
    v
}

fn without_value(r: &[u8], x: i32) -> Set {
    without(r, r.iter().position(|&y| y as i32 == x).expect("value present"))
}

/// First index of each distinct value.
fn distinct(r: &[u8]) -> Vec<usize> {
    (0..r.len()).filter(|&k| k == 0 || r[k] != r[k - 1]).collect()
}

/// AM+T's answer on r1 = R − {i}: the largest, or on an exact tie with numbers left over the second largest.
fn am_t(r1: &[u8], e: i32, i: i32) -> i32 {
    let top = r1.len() - 1;
    if r1.len() >= 2 && e + r1[top] as i32 == i { r1[top - 1] as i32 } else { r1[top] as i32 }
}

/// The smallest valid answer j (e + j − i ≥ c(r1 − {j})), if any.
fn smallest_valid(r1: &[u8], e: i32, i: i32) -> Option<i32> {
    distinct(r1).into_iter().map(|q| (r1[q] as i32, q)).find(|&(j, q)| e + j - i >= cost(&without(r1, q))).map(|(j, _)| j)
}

/// The partner of R[k] (first copy) in R's bottom-up matching.
fn partner(r: &[u8], k: usize) -> i32 {
    r[k ^ 1] as i32
}

/// Without full twin pairs: values of count 2 removed.
fn non_twins(r: &[u8]) -> Set {
    r.iter().copied().filter(|&x| r.iter().filter(|&&y| y == x).count() == 1).collect()
}

fn bump_top(r: &[u8], highest: bool) -> Option<i32> {
    let tops = r.chunks(2).filter(|c| c[1] > c[0]).map(|c| c[1] as i32);
    if highest { tops.last() } else { tops.min() }
}

struct Game {
    answer: Answer,
    first: First,
    memo: HashMap<u64, i8>,
}

impl Game {
    fn new((answer, first): (Answer, First)) -> Self {
        Game { answer, first, memo: HashMap::new() }
    }

    fn key(r: &[u8], d: i32, m: Mover) -> u64 {
        assert!((0..1 << (DEBT_BITS - 1)).contains(&d));
        let s: u64 = r.iter().map(|&x| BASE.pow(x as u32)).sum();
        ((s << DEBT_BITS) | d as u64) << 1 | (m == Mover::Y) as u64
    }

    /// Z's answer value after Y, at debt e on R, picked R[k] = i.
    fn answer_of(&self, r: &[u8], k: usize, e: i32) -> i32 {
        let i = r[k] as i32;
        let r1 = without(r, k);
        match self.answer {
            Answer::Hyb2 => smallest_valid(&r1, e, i).unwrap_or_else(|| am_t(&r1, e, i)),
            Answer::Hyb2Partner => smallest_valid(&r1, e, i).unwrap_or_else(|| partner(r, k)),
            Answer::TwinHyb2 => {
                if r1.contains(&r[k]) {
                    return i;
                }
                let nt = non_twins(r);
                let nt1 = without_value(&nt, i);
                smallest_valid(&nt1, e, i).unwrap_or_else(|| am_t(&nt1, e, i))
            }
            Answer::Free => unreachable!(),
        }
    }

    fn first_picks(&self, r: &[u8]) -> Vec<usize> {
        let max = r.len() - 1;
        let pick = |x: Option<i32>| vec![x.map_or(max, |v| r.iter().position(|&y| y as i32 == v).unwrap())];
        match self.first {
            First::Max => vec![max],
            First::HighBumpTop => pick(bump_top(r, true)),
            First::LowBumpTop => pick(bump_top(r, false)),
            First::Free => distinct(r),
        }
    }

    /// The round's result for Z: the round's mover `m` ends it with debt δ on r2.
    fn next(&mut self, r2: &[u8], delta: i32, m: Mover) -> i8 {
        if delta >= 0 { self.value(r2, delta, m) } else { self.value(r2, -delta, other(m)) }
    }

    /// Z's outcome after first pick R[a] at a Z start with debt d, Y answering optimally.
    fn pick_value(&mut self, r: &[u8], d: i32, a: usize) -> i8 {
        let i = r[a] as i32;
        let r1 = without(r, a);
        let mut worst = WIN;
        for q in distinct(&r1) {
            worst = worst.min(self.next(&without(&r1, q), d + r1[q] as i32 - i, Mover::Z));
        }
        worst
    }

    /// Z's outcome at a round start: R, the mover m trailing by d ≥ 0.
    fn value(&mut self, r: &[u8], d: i32, m: Mover) -> i8 {
        if r.is_empty() {
            return if d == 0 { DRAW } else if m == Mover::Z { LOSS } else { WIN };
        }
        if d > spread(r) {
            return if m == Mover::Z { LOSS } else { WIN };
        }
        let key = Self::key(r, d, m);
        if let Some(&v) = self.memo.get(&key) {
            return v;
        }
        let mut best = if m == Mover::Z { LOSS } else { WIN };
        match m {
            Mover::Z => {
                for a in self.first_picks(r) {
                    best = best.max(self.pick_value(r, d, a));
                }
            }
            Mover::Y => {
                for a in distinct(r) {
                    let i = r[a] as i32;
                    let r1 = without(r, a);
                    let v = if self.answer == Answer::Free {
                        let mut top = LOSS;
                        for q in distinct(&r1) {
                            let delta = d + r1[q] as i32 - i;
                            top = top.max(self.next(&without(&r1, q), delta, Mover::Y));
                        }
                        top
                    } else {
                        let j = self.answer_of(r, a, d);
                        self.next(&without_value(&r1, j), d + j - i, Mover::Y)
                    };
                    best = best.min(v);
                }
            }
        }
        self.memo.insert(key, best);
        best
    }
}

fn other(m: Mover) -> Mover {
    if m == Mover::Z { Mover::Y } else { Mover::Z }
}

/// The next round start after a round of mover `m` that ends with debt δ on r2.
fn after(r2: Set, delta: i32, m: Mover) -> (Set, i32, Mover) {
    if delta >= 0 { (r2, delta, m) } else { (r2, -delta, other(m)) }
}

/// Hyb2's answers with free first picks: every Z start reached while Z keeps ≥ draw (Z follows each drawing
/// pick, Y plays anything) where max R is not a drawing pick, with the drawing picks.
fn max_breaks(p: usize, t: usize) -> Vec<(Set, i32, Vec<u8>)> {
    let o = offsets(p, t);
    let g0 = t.count_ones() as i32 % 2;
    let mut game = Game::new((Answer::Hyb2, First::Free));
    let mut seen = HashSet::new();
    let mut stack: Vec<(Set, i32, Mover)> = vec![];
    for m in [Mover::Z, Mover::Y] {
        if game.value(&o, g0, m) >= DRAW {
            stack.push((o.clone(), g0, m));
        }
    }
    let mut out = vec![];
    while let Some((r, d, m)) = stack.pop() {
        if r.is_empty() || d > spread(&r) || !seen.insert(Game::key(&r, d, m)) {
            continue;
        }
        if m == Mover::Z {
            let picks: Vec<(usize, i8)> = distinct(&r).into_iter().map(|a| (a, game.pick_value(&r, d, a))).collect();
            let drawing: Vec<u8> = picks.iter().filter(|x| x.1 >= DRAW).map(|x| r[x.0]).collect();
            if !drawing.contains(r.last().unwrap()) {
                out.push((r.clone(), d, drawing));
            }
            for &(a, v) in &picks {
                if v >= DRAW {
                    let i = r[a] as i32;
                    let r1 = without(&r, a);
                    for q in distinct(&r1) {
                        stack.push(after(without(&r1, q), d + r1[q] as i32 - i, Mover::Z));
                    }
                }
            }
        } else {
            for a in distinct(&r) {
                let i = r[a] as i32;
                let r1 = without(&r, a);
                let j = game.answer_of(&r, a, d);
                stack.push(after(without_value(&r1, j), d + j - i, Mover::Y));
            }
        }
    }
    out
}

fn offsets(p: usize, t: usize) -> Set {
    let mut o: Set = (0..p).flat_map(|i| [2 * i as u8, 2 * i as u8 + (t >> i & 1) as u8]).collect();
    o.sort_unstable();
    o
}

fn in_family_c(p: usize, t: usize) -> bool {
    (0..=p).any(|k| 2 * k >= p && t == ((1usize << p) - 1) & !((1usize << k) - 1))
}

fn code(o: Outcome) -> i8 {
    o as i8 - 1
}

fn check() {
    let mut n = 0;
    for p in 1..=CHECK_P {
        for t in 0..1usize << p {
            let o = offsets(p, t);
            for mask in 0..1usize << o.len() {
                let r: Set = (0..o.len()).filter(|&b| mask >> b & 1 == 1).map(|b| o[b]).collect();
                if r.len() % 2 == 1 {
                    continue;
                }
                let mut g = Game::new((Answer::Free, First::Free));
                for d in 0..=CHECK_D {
                    let a = d as u64 + r.iter().map(|&x| x as u64).sum::<u64>() + 1;
                    let xs: Vec<u64> = r.iter().map(|&x| a + x as u64).collect();
                    let real = code(Solver::new(&xs).position((1usize << xs.len()) - 1, d as u64));
                    assert_eq!(g.value(&r, d, Mover::Z), real, "rounds {r:?} d={d}");
                    n += 1;
                }
            }
        }
    }
    println!("check: Free/Free = Solver at a = d + sum + 1 (C13) on {n} positions, p ≤ {CHECK_P}, d ≤ {CHECK_D}");
    let mut g = Game::new((Answer::Hyb2, First::Max));
    assert_eq!(g.value(&IDEATOR_EXAMPLE, IDEATOR_DEBT, Mover::Z), LOSS, "ideator's Hyb2 example");
    println!("check: Hyb2/Max loses on {IDEATOR_EXAMPLE:?}, Z first at debt {IDEATOR_DEBT} (ideator)");
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().expect("p_min p_max threads")).collect();
    assert_eq!(a.len(), 3, "usage: e24_collapsed_rounds <p_min> <p_max> <threads>");
    rayon::ThreadPoolBuilder::new().num_threads(a[2]).build_global().unwrap();
    check();
    for p in a[0]..=a[1] {
        for s in STRATEGIES {
            if s == (Answer::Free, First::Free) && p > FREE_FREE_MAX_P {
                continue;
            }
            let fails: Vec<(usize, Mover)> = (0..1usize << p)
                .into_par_iter()
                .flat_map_iter(|t| {
                    let o = offsets(p, t);
                    let g0 = t.count_ones() as i32 % 2;
                    let mut game = Game::new(s);
                    [Mover::Z, Mover::Y].into_iter().filter(move |&m| game.value(&o, g0, m) == LOSS).map(move |m| (t, m))
                })
                .collect();
            if s == (Answer::Hyb2, First::Max) {
                assert!(!fails.iter().any(|&(t, _)| t == (1 << p) - 1), "Hyb2 fails on the full block, p = {p}");
            }
            let in_c = fails.iter().filter(|&&(t, _)| in_family_c(p, t)).count();
            let shown: Vec<String> = fails.iter().take(3).map(|&(t, m)| format!("{:?} {m:?} first", offsets(p, t))).collect();
            println!("p={p} {:?}/{:?}: {} failing (t, role) of {}, {in_c} in (c)'s family; {shown:?}", s.0, s.1, fails.len(), 2usize << p);
        }
        if p <= EXTRACT_MAX_P {
            let mut breaks: Vec<(Set, i32, Vec<u8>)> = (0..1usize << p).into_par_iter().flat_map_iter(|t| max_breaks(p, t)).collect();
            breaks.sort_by(|x, y| (x.0.len(), &x.0, x.1).cmp(&(y.0.len(), &y.0, y.1)));
            breaks.dedup();
            println!("p={p} Hyb2/Free: {} reached Z starts where max R does not draw; smallest:", breaks.len());
            for (r, d, drawing) in breaks.iter().take(SHOWN_BREAKS) {
                println!("  {r:?} Z trailing by {d}: drawing first picks {drawing:?}");
            }
        }
    }
}
