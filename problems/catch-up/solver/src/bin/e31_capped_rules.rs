//! Usage: e31_capped_rules <p_max>
//! C86 below C24's height: which simple Z rules keep the rounds structure (every round-start debt ≤ a + min R, so
//! the real game at height a is the rounds game, C22) and draw a band entry of the block {0..2p−1} in both roles?
//! For each answer rule × first-pick rule and each band entry (p, d), prints the least height a at which the rule
//! succeeds, next to the optimum over all Z strategies (E28's number, recomputed here with Free/Free).
//! Answers: Hyb2 (C24: smallest valid j, else AM+T); Tie (the j = i − e that leaves the mover exactly tied, when
//! present, else Hyb2); TieOver (Hyb2, but the tie answer when Hyb2's would put the next round start above the cap);
//! Free (Z's best). First picks: Max, Second (second largest), Free.
//! First checks: Hyb2/Max succeeds at a = 2p − 1 (C24, C25) for every entry.

const LOSS: i8 = -1;
const DRAW: i8 = 0;
const WIN: i8 = 1;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Answer {
    Hyb2,
    Tie,
    TieOver,
    /// The largest j ≤ i − e (Y tied or ahead by the least), else the smallest j.
    Undercut,
    /// Hyb2 while more than 4 offsets are left, Undercut from 4 on.
    Hyb2ThenUndercut,
    Free,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum First {
    Max,
    Second,
    Free,
}

const RULES: [(Answer, First); 14] = [
    (Answer::Undercut, First::Max),
    (Answer::Undercut, First::Free),
    (Answer::Hyb2ThenUndercut, First::Max),
    (Answer::Hyb2ThenUndercut, First::Free),
    (Answer::Free, First::Free),
    (Answer::Hyb2, First::Max),
    (Answer::Hyb2, First::Second),
    (Answer::Hyb2, First::Free),
    (Answer::Tie, First::Max),
    (Answer::Tie, First::Second),
    (Answer::Tie, First::Free),
    (Answer::TieOver, First::Max),
    (Answer::TieOver, First::Second),
    (Answer::TieOver, First::Free),
];

fn bits(mask: usize, n: usize) -> Vec<usize> {
    (0..n).filter(|&b| mask >> b & 1 == 1).collect()
}

/// Bottom-up matching cost of the offsets in `mask`.
fn cost(mask: usize, n: usize) -> i32 {
    let b = bits(mask, n);
    b.chunks(2).map(|c| if c.len() == 2 { (c[1] - c[0]) as i32 } else { 0 }).sum()
}

struct Game {
    n: usize,
    cap: i32,
    answer: Answer,
    first: First,
    max_debt: usize,
    memo: Vec<i8>,
}

impl Game {
    fn new(p: usize, cap: i32, (answer, first): (Answer, First)) -> Self {
        let n = 2 * p;
        let max_debt = p * (2 * p - 1) + p + 2;
        Game { n, cap, answer, first, max_debt, memo: vec![i8::MIN; (1usize << n) * (max_debt + 1) * 2] }
    }

    /// The next round start's cap test for the mover's debt δ on `rest`.
    fn within_cap(&self, rest: usize, delta: i32) -> bool {
        rest == 0 || delta.abs() <= self.cap + rest.trailing_zeros() as i32
    }

    fn hyb2(&self, r1: usize, e: i32, i: usize) -> usize {
        for j in bits(r1, self.n) {
            if e + j as i32 - i as i32 >= cost(r1 & !(1 << j), self.n) {
                return j;
            }
        }
        let b = bits(r1, self.n);
        let top = b[b.len() - 1];
        if b.len() >= 2 && e + top as i32 == i as i32 { b[b.len() - 2] } else { top }
    }

    fn answer_of(&self, r1: usize, e: i32, i: usize) -> usize {
        let tie = i as i32 - e;
        let has_tie = tie >= 0 && r1 >> tie as usize & 1 == 1;
        let h = self.hyb2(r1, e, i);
        match self.answer {
            Answer::Hyb2 => h,
            Answer::Tie => if has_tie { tie as usize } else { h },
            Answer::TieOver => {
                let over = !self.within_cap(r1 & !(1 << h), e + h as i32 - i as i32);
                if over && has_tie { tie as usize } else { h }
            }
            Answer::Undercut => self.undercut(r1, e, i),
            Answer::Hyb2ThenUndercut => if (r1.count_ones() + 1) <= 4 { self.undercut(r1, e, i) } else { h },
            Answer::Free => unreachable!(),
        }
    }

    fn undercut(&self, r1: usize, e: i32, i: usize) -> usize {
        let b = bits(r1, self.n);
        b.iter().copied().filter(|&j| j as i32 <= i as i32 - e).max().unwrap_or(b[0])
    }

    /// Z's outcome at a round start: offsets `mask`, the mover (Z if `z`) trailing by `d`.
    fn value(&mut self, mask: usize, d: i32, z: bool) -> i8 {
        if mask == 0 {
            return if d == 0 { DRAW } else if z { LOSS } else { WIN };
        }
        if d > self.cap + mask.trailing_zeros() as i32 {
            return LOSS;
        }
        let b = bits(mask, self.n);
        let h = b.len() / 2;
        let spread: i32 = b[h..].iter().sum::<usize>() as i32 - b[..h].iter().sum::<usize>() as i32;
        if d > spread {
            return if z { LOSS } else { WIN };
        }
        let k = (mask * (self.max_debt + 1) + d as usize) * 2 + z as usize;
        if self.memo[k] != i8::MIN {
            return self.memo[k];
        }
        let mut best = if z { LOSS } else { WIN };
        if z {
            let picks: Vec<usize> = match self.first {
                First::Max => vec![b[b.len() - 1]],
                First::Second => vec![b[b.len() - 2]],
                First::Free => b.clone(),
            };
            for i in picks {
                let mut worst = WIN;
                for &j in b.iter().filter(|&&j| j != i) {
                    let rest = mask & !(1 << i) & !(1 << j);
                    let delta = d + j as i32 - i as i32;
                    let v = if delta >= 0 { self.value(rest, delta, true) } else { self.value(rest, -delta, false) };
                    worst = worst.min(v);
                }
                best = best.max(worst);
            }
        } else {
            for &i in &b {
                let r1 = mask & !(1 << i);
                let v = if self.answer == Answer::Free {
                    let mut top = LOSS;
                    for &j in b.iter().filter(|&&j| j != i) {
                        let rest = r1 & !(1 << j);
                        let delta = d + j as i32 - i as i32;
                        let w = if delta >= 0 { self.value(rest, delta, false) } else { self.value(rest, -delta, true) };
                        top = top.max(w);
                    }
                    top
                } else {
                    let j = self.answer_of(r1, d, i);
                    let rest = r1 & !(1 << j);
                    let delta = d + j as i32 - i as i32;
                    if delta >= 0 { self.value(rest, delta, false) } else { self.value(rest, -delta, true) }
                };
                best = best.min(v);
            }
        }
        self.memo[k] = best;
        best
    }
}

fn succeeds(p: usize, d: i32, cap: i32, rule: (Answer, First)) -> bool {
    let full = (1usize << (2 * p)) - 1;
    let mut g = Game::new(p, cap, rule);
    g.value(full, d, true) >= DRAW && g.value(full, d, false) >= DRAW
}

/// At height `cap`, with Z free: the reached Y moves (Z following every drawing move) where Hyb2's answer does not
/// draw, with the answers that do. (offsets left, Y's debt, Y's pick, Hyb2's answer, drawing answers.)
fn hyb2_breaks(p: usize, d: i32, cap: i32) -> Vec<(Vec<usize>, i32, usize, usize, Vec<usize>)> {
    let n = 2 * p;
    let full = (1usize << n) - 1;
    let mut g = Game::new(p, cap, (Answer::Free, First::Free));
    let mut out = vec![];
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![];
    for z in [true, false] {
        if g.value(full, d, z) >= DRAW {
            stack.push((full, d, z));
        }
    }
    let after = |rest: usize, delta: i32, mover_z: bool| if delta >= 0 { (rest, delta, mover_z) } else { (rest, -delta, !mover_z) };
    while let Some((mask, e, z)) = stack.pop() {
        if mask == 0 || !seen.insert((mask, e, z)) || e > cap + mask.trailing_zeros() as i32 {
            continue;
        }
        let b = bits(mask, n);
        if z {
            for &i in &b {
                let mut ok = true;
                let mut kids = vec![];
                for &j in b.iter().filter(|&&j| j != i) {
                    let s = after(mask & !(1 << i) & !(1 << j), e + j as i32 - i as i32, true);
                    if g.value(s.0, s.1, s.2) < DRAW { ok = false; }
                    kids.push(s);
                }
                if ok { stack.extend(kids); }
            }
        } else {
            for &i in &b {
                let r1 = mask & !(1 << i);
                let mut drawing = vec![];
                for &j in b.iter().filter(|&&j| j != i) {
                    let s = after(r1 & !(1 << j), e + j as i32 - i as i32, false);
                    if g.value(s.0, s.1, s.2) >= DRAW {
                        drawing.push(j);
                        stack.push(s);
                    }
                }
                let h = g.hyb2(r1, e, i);
                if !drawing.contains(&h) {
                    out.push((b.clone(), e, i, h, drawing));
                }
            }
        }
    }
    out.sort_by_key(|x| (x.0.len(), x.0.clone(), x.1, x.2));
    out
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let p_max: usize = a[0].parse().expect("p_max");
    if a.get(1).map(|s| s.as_str()) == Some("breaks") {
        for p in 2..=p_max {
            for d in (p % 2..=p).step_by(2) {
                let d = d as i32;
                let least = (0..=2 * p as i32 - 1).find(|&x| succeeds(p, d, x, (Answer::Free, First::Free))).unwrap();
                let br = hyb2_breaks(p, d, least);
                println!("p={p} d={d} at height {least}: {} reached Y moves where Hyb2's answer fails; smallest:", br.len());
                for (r, e, i, h, ds) in br.iter().take(8) {
                    println!("  R={r:?} Y trails by {e}, takes {i}: Hyb2 answers {h}, drawing answers {ds:?}");
                }
            }
        }
        return;
    }
    for p in 2..=p_max {
        let c24 = 2 * p as i32 - 1;
        for d in (p % 2..=p).step_by(2) {
            let d = d as i32;
            assert!(succeeds(p, d, c24, (Answer::Hyb2, First::Max)), "Hyb2/Max at 2p − 1, p={p} d={d} (C24)");
            let row: Vec<String> = RULES
                .iter()
                .map(|&rule| {
                    let least = (0..=c24).find(|&a| succeeds(p, d, a, rule));
                    format!("{:?}/{:?} {}", rule.0, rule.1, least.map_or("-".to_string(), |a| a.to_string()))
                })
                .collect();
            println!("p={p} d={d} (C24 {c24}): {}", row.join(", "));
        }
    }
}
