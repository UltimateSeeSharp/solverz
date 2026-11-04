//! Usage: e32_capped_collapsed <p_max>
//! C85's high base with one pick per turn: in the rounds game on O_t = ⊎_{i<p} {2i, 2i + t_i} at debt |t| mod 2, with
//! every round-start debt capped at a + min R (above it counts as a Z failure; below it the real game at height a
//! is the rounds game, C22), the least a at which Z draws every t in both roles: with free play (Z's best) and with
//! E24's rule (first pick the top of the highest bumped pair, answers Hyb2). Prints both next to C24's 2p − 1.
//! First check: uncapped, free play draws every t (E24's Free/Free), and so does the rule.

use std::collections::HashMap;

type Set = Vec<u8>;
const LOSS: i8 = -1;
const DRAW: i8 = 0;
const WIN: i8 = 1;
const NO_CAP: i32 = 1 << 20;

fn cost(r: &[u8]) -> i32 {
    r.chunks(2).map(|c| if c.len() == 2 { (c[1] - c[0]) as i32 } else { 0 }).sum()
}

fn without(r: &[u8], k: usize) -> Set {
    let mut v = r.to_vec();
    v.remove(k);
    v
}

fn without_value(r: &[u8], x: i32) -> Set {
    without(r, r.iter().position(|&y| y as i32 == x).unwrap())
}

fn distinct(r: &[u8]) -> Vec<usize> {
    (0..r.len()).filter(|&k| k == 0 || r[k] != r[k - 1]).collect()
}

fn hyb2(r1: &[u8], e: i32, i: i32) -> i32 {
    for q in distinct(r1) {
        let j = r1[q] as i32;
        if e + j - i >= cost(&without(r1, q)) {
            return j;
        }
    }
    let top = r1.len() - 1;
    if r1.len() >= 2 && e + r1[top] as i32 == i { r1[top - 1] as i32 } else { r1[top] as i32 }
}

fn rule_first(r: &[u8]) -> i32 {
    r.chunks(2).filter(|c| c[1] > c[0]).map(|c| c[1] as i32).last().unwrap_or(*r.last().unwrap() as i32)
}

struct Game {
    cap: i32,
    rule: bool,
    memo: HashMap<(Set, i32, bool), i8>,
}

impl Game {
    fn next(&mut self, r2: Set, delta: i32, mover_z: bool) -> i8 {
        if delta >= 0 { self.value(&r2, delta, mover_z) } else { self.value(&r2, -delta, !mover_z) }
    }

    fn value(&mut self, r: &[u8], d: i32, z: bool) -> i8 {
        if r.is_empty() {
            return if d == 0 { DRAW } else if z { LOSS } else { WIN };
        }
        if d > self.cap + r[0] as i32 {
            return LOSS;
        }
        let h = r.len() / 2;
        let spread: i32 = r[h..].iter().map(|&x| x as i32).sum::<i32>() - r[..h].iter().map(|&x| x as i32).sum::<i32>();
        if d > spread {
            return if z { LOSS } else { WIN };
        }
        if let Some(&v) = self.memo.get(&(r.to_vec(), d, z)) {
            return v;
        }
        let v = if z {
            let picks: Vec<i32> = if self.rule { vec![rule_first(r)] } else { distinct(r).iter().map(|&k| r[k] as i32).collect() };
            let mut best = LOSS;
            for i in picks {
                let r1 = without_value(r, i);
                let mut worst = WIN;
                for q in distinct(&r1) {
                    worst = worst.min(self.next(without(&r1, q), d + r1[q] as i32 - i, true));
                }
                best = best.max(worst);
            }
            best
        } else {
            let mut worst = WIN;
            for a in distinct(r) {
                let i = r[a] as i32;
                let r1 = without(r, a);
                let w = if self.rule {
                    let j = hyb2(&r1, d, i);
                    self.next(without_value(&r1, j), d + j - i, false)
                } else {
                    let mut top = LOSS;
                    for q in distinct(&r1) {
                        top = top.max(self.next(without(&r1, q), d + r1[q] as i32 - i, false));
                    }
                    top
                };
                worst = worst.min(w);
            }
            worst
        };
        self.memo.insert((r.to_vec(), d, z), v);
        v
    }
}

fn all_draw(p: usize, cap: i32, rule: bool) -> bool {
    (0..1usize << p).all(|t| {
        let mut o: Set = (0..p).flat_map(|i| [2 * i as u8, 2 * i as u8 + (t >> i & 1) as u8]).collect();
        o.sort_unstable();
        let g = t.count_ones() as i32 % 2;
        let mut game = Game { cap, rule, memo: HashMap::new() };
        game.value(&o, g, true) >= DRAW && game.value(&o, g, false) >= DRAW
    })
}

fn main() {
    let p_max: usize = std::env::args().nth(1).expect("p_max").parse().expect("p_max");
    for p in 1..=p_max {
        assert!(all_draw(p, NO_CAP, false), "uncapped free play should draw (E24), p = {p}");
        assert!(all_draw(p, NO_CAP, true), "uncapped rule should draw (E24), p = {p}");
        let c24 = 2 * p as i32 - 1;
        let limit = 4 * p as i32 + 2;
        let free = (0..=limit).find(|&a| all_draw(p, a, false));
        let rule = (0..=limit).find(|&a| all_draw(p, a, true));
        let show = |x: Option<i32>| x.map_or(format!("> {limit}"), |a| a.to_string());
        println!("p={p}: least height, free play {}, E24's rule {} (C24 for blocks: {c24})", show(free), show(rule));
    }
}
