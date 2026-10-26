//! Usage: hyb2_states <max_p> [rule]   (rule: hyb2 (default) | hyb | am)
//! Where does the frugal switch (B30) let the opponent take two numbers in one turn? Real Catch-Up on
//! blocks {a..a+2p−1}, a ∈ [2p−1, 4p], at gap p mod 2. Z follows the rule, Y plays perfectly.
//! Rules: `am` takes the largest number; `hyb` (L21) answers a round mover trailing by more than c of
//! the numbers left with its L20 partner, else the largest; `hyb2` answers with the smallest number
//! leaving Y's debt ≥ c of what is left, else the largest. A round: the mover picks until caught up,
//! then the other answers until caught up (if it falls short, it becomes the next round's mover).
//! Reports Z's guaranteed margin in both roles, and over every state reachable against Z: Y round
//! starts where Y trails by more than a + min left (a carry is possible), how many, the largest
//! excess, and Z's guarantee there. `reach` mode (`hyb2_states <max_p> <rule> reach`): the rounds
//! game (a huge), the largest debt minus smallest offset left at Y's and at Z's round starts.

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Debug)]
enum Rule {
    Am,
    Hyb,
    Hyb2,
}

/// Offsets of the numbers in `mask`, increasing.
fn offsets(mask: u32) -> Vec<i64> {
    (0..32).filter(|&b| mask >> b & 1 == 1).map(|b| b as i64).collect()
}

/// L20's matching cost of the offsets in `mask`.
fn cost(mask: u32) -> i64 {
    offsets(mask).chunks(2).map(|c| if c.len() == 2 { c[1] - c[0] } else { 0 }).sum()
}

fn top(mask: u32) -> u32 {
    31 - mask.leading_zeros()
}

/// L20 partner of `i` in `mask` (which contains `i`).
fn partner(mask: u32, i: u32) -> Option<u32> {
    let v = offsets(mask);
    let k = v.iter().position(|&x| x == i as i64)?;
    (if k % 2 == 0 { v.get(k + 1).copied() } else { Some(v[k - 1]) }).map(|x| x as u32)
}

/// A height at which the real game is the rounds game for every debt reached here.
const ROUNDS_HEIGHT: i64 = 1 << 20;

/// A node: numbers left, picker's deficit, Z picks?, answering phase?, Y's round-first pick.
type Key = (u32, i64, bool, bool, u32);

struct Engine {
    a: i64,
    rule: Rule,
    memo: HashMap<Key, i64>,
}

impl Engine {
    /// Z's pick with `mask` left, trailing by `d`; when answering, Y's round-first pick was `last`.
    fn z_pick(&self, mask: u32, d: i64, answering: bool, last: u32) -> u32 {
        let t = top(mask);
        if !answering {
            return t;
        }
        // Y's debt at the round start, and the numbers left then.
        let dy = self.a + last as i64 - d;
        let before = mask | 1 << last;
        match self.rule {
            Rule::Am => t,
            Rule::Hyb => {
                if dy > cost(before) {
                    partner(before, last).filter(|&q| mask >> q & 1 == 1).unwrap_or(t)
                } else {
                    t
                }
            }
            Rule::Hyb2 => offsets(mask)
                .into_iter()
                .map(|j| j as u32)
                .find(|&j| dy + j as i64 - last as i64 >= cost(mask & !(1 << j)))
                .unwrap_or(t),
        }
    }

    fn key(mask: u32, d: i64, z: bool, answering: bool, last: u32) -> Key {
        (mask, d, z, answering, if z && answering { last } else { u32::MAX })
    }

    /// Z's final margin under the rule against a perfect Y.
    fn go(&mut self, mask: u32, d: i64, z: bool, answering: bool, last: u32) -> i64 {
        if mask == 0 {
            return if z { -d } else { d };
        }
        let key = Self::key(mask, d, z, answering, last);
        if let Some(&v) = self.memo.get(&key) {
            return v;
        }
        let picks: Vec<u32> = if z { vec![self.z_pick(mask, d, answering, last)] } else { offsets(mask).into_iter().map(|x| x as u32).collect() };
        let mut res = if z { i64::MIN } else { i64::MAX };
        for x in picks {
            let (next, v) = (mask & !(1 << x), self.a + x as i64);
            let out = if v >= d { self.go(next, v - d, !z, !answering, x) } else { self.go(next, d - v, z, false, x) };
            res = if z { res.max(out) } else { res.min(out) };
        }
        self.memo.insert(key, res);
        res
    }

    /// Every node reachable against Z from the given one.
    fn reach(&self, mask: u32, d: i64, z: bool, answering: bool, last: u32, seen: &mut HashMap<Key, ()>) {
        if mask == 0 || seen.insert(Self::key(mask, d, z, answering, last), ()).is_some() {
            return;
        }
        let picks: Vec<u32> = if z { vec![self.z_pick(mask, d, answering, last)] } else { offsets(mask).into_iter().map(|x| x as u32).collect() };
        for x in picks {
            let (next, v) = (mask & !(1 << x), self.a + x as i64);
            if v >= d { self.reach(next, v - d, !z, !answering, x, seen) } else { self.reach(next, d - v, z, false, x, seen) }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let max_p: u32 = args.get(1).and_then(|s| s.parse().ok()).expect("max_p");
    let rule = match args.get(2).map(String::as_str) {
        None | Some("hyb2") => Rule::Hyb2,
        Some("hyb") => Rule::Hyb,
        Some("am") => Rule::Am,
        Some(r) => panic!("unknown rule {r}"),
    };
    println!("rule {rule:?}");
    if args.get(3).map(String::as_str) == Some("reach") {
        println!("| p | Y round starts | max (debt − min left), Y | Z round starts | max (debt − min left), Z | max debt, Y |");
        println!("|---|---|---|---|---|---|");
        for p in 1..=max_p {
            let full = (1u32 << (2 * p)) - 1;
            let e = Engine { a: ROUNDS_HEIGHT, rule, memo: HashMap::new() };
            let mut seen = HashMap::new();
            e.reach(full, (p % 2) as i64, true, false, 0, &mut seen);
            e.reach(full, (p % 2) as i64, false, false, 0, &mut seen);
            let starts = |zz: bool| -> Vec<(u32, i64)> {
                seen.keys().filter(|&&(_, _, z, ans, _)| z == zz && !ans).map(|&(m, d, ..)| (m, d)).collect()
            };
            let (ys, zs) = (starts(false), starts(true));
            let max_rel = |v: &[(u32, i64)]| v.iter().map(|&(m, d)| d - offsets(m)[0]).max().unwrap_or(0);
            let max_d = ys.iter().map(|&(_, d)| d).max().unwrap_or(0);
            println!("| {p} | {} | {} | {} | {} | {max_d} |", ys.len(), max_rel(&ys), zs.len(), max_rel(&zs));
            if args.get(4).map(String::as_str) == Some("stats") {
                let stat = |f: &dyn Fn(u32, i64) -> i64| ys.iter().map(|&(m, d)| f(m, d)).max().unwrap_or(0);
                let mx = |m: u32| *offsets(m).last().unwrap();
                let mn = |m: u32| offsets(m)[0];
                println!("  max d − c: {}, max d − max: {}, max d − span: {}, max d − c − min: {}, max d − c − 2min: {}",
                    stat(&|m, d| d - cost(m)), stat(&|m, d| d - mx(m)), stat(&|m, d| d - mx(m) + mn(m)),
                    stat(&|m, d| d - cost(m) - mn(m)), stat(&|m, d| d - cost(m) - 2 * mn(m)));
                let best = max_rel(&ys);
                for &(m, d) in ys.iter().filter(|&&(m, d)| d - offsets(m)[0] == best).take(4) {
                    println!("  witness: left {:?}, Y debt {d}, c {}", offsets(m), cost(m));
                }
            }
        }
        return;
    }
    println!("| p | a | Z as mover | Z as other | Y round starts | with a carry possible | max excess | least Z guarantee there |");
    println!("|---|---|---|---|---|---|---|---|");
    for p in 1..=max_p {
        let full = (1u32 << (2 * p)) - 1;
        let g0 = (p % 2) as i64;
        for a in (2 * p as i64 - 1).max(1)..=4 * p as i64 {
            let mut e = Engine { a, rule, memo: HashMap::new() };
            let (mv, other) = (e.go(full, g0, true, false, 0), e.go(full, g0, false, false, 0));
            let mut seen = HashMap::new();
            e.reach(full, g0, true, false, 0, &mut seen);
            e.reach(full, g0, false, false, 0, &mut seen);
            let starts: Vec<Key> = seen.keys().copied().filter(|&(_, _, z, ans, _)| !z && !ans).collect();
            let carries: Vec<Key> = starts.iter().copied().filter(|&(m, d, ..)| d > a + offsets(m)[0]).collect();
            let excess = carries.iter().map(|&(m, d, ..)| d - a - offsets(m)[0]).max();
            let least = carries.iter().map(|&(m, d, z, ans, l)| e.go(m, d, z, ans, l)).min();
            let show = |o: Option<i64>| o.map_or("—".to_string(), |v| v.to_string());
            println!("| {p} | {a} | {mv} | {other} | {} | {} | {} | {} |", starts.len(), carries.len(), show(excess), show(least));
        }
    }
}
