//! Usage: e30_rule_states <p_max>
//! The round starts reached by E24's rule on collapsed blocks O_t = ⊎_{i<p} {2i, 2i + t_i} at debt |t| mod 2, both
//! roles: Z first picks the top of the highest bumped pair of the current bottom-up matching (else max R) and answers
//! by Hyb2 (smallest valid j, else AM+T); Y plays every move. For a proof of the rule this tallies, per p, the reached
//! Z starts by d − c(R) and the reached Y starts by e − c(R) (pre-switch < 0), each with the number of original pairs
//! broken (a value of R whose original partner is gone), and prints the extreme cases. One thread.

use std::collections::{BTreeMap, HashSet};

type Set = Vec<u8>;

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

fn hyb2_answer(r1: &[u8], e: i32, i: i32) -> i32 {
    for q in distinct(r1) {
        let j = r1[q] as i32;
        if e + j - i >= cost(&without(r1, q)) {
            return j;
        }
    }
    let top = r1.len() - 1;
    if r1.len() >= 2 && e + r1[top] as i32 == i { r1[top - 1] as i32 } else { r1[top] as i32 }
}

fn first_pick(r: &[u8]) -> i32 {
    r.chunks(2).filter(|c| c[1] > c[0]).map(|c| c[1] as i32).last().unwrap_or(*r.last().unwrap() as i32)
}

/// Values of R whose original pair {2i, 2i + t_i} lost its other element.
fn broken(r: &[u8], t: usize, p: usize) -> usize {
    (0..p)
        .filter(|&i| {
            let (a, b) = (2 * i as u8, 2 * i as u8 + (t >> i & 1) as u8);
            let ca = r.iter().filter(|&&x| x == a).count();
            let cb = r.iter().filter(|&&x| x == b).count();
            let n = if a == b { ca } else { ca + cb };
            n == 1
        })
        .count()
}

/// The values of R whose original pair lost its other element.
fn orphans(r: &[u8], t: usize, p: usize) -> Vec<u8> {
    let mut out = vec![];
    for i in 0..p {
        let (a, b) = (2 * i as u8, 2 * i as u8 + (t >> i & 1) as u8);
        let left: Vec<u8> = r.iter().copied().filter(|&x| x == a || x == b).collect();
        if left.len() == 1 {
            out.push(left[0]);
        }
    }
    out
}

/// Z's guaranteed final margin under the rule, Y minimizing: round start (R, mover trails by d, mover is Z if z).
fn rule_margin(r: &[u8], d: i32, z: bool, memo: &mut std::collections::HashMap<(Set, i32, bool), i32>) -> i32 {
    if r.is_empty() {
        return if z { -d } else { d };
    }
    if let Some(&v) = memo.get(&(r.to_vec(), d, z)) {
        return v;
    }
    let next = |r2: Set, delta: i32, mover_z: bool, memo: &mut std::collections::HashMap<(Set, i32, bool), i32>| {
        if delta >= 0 { rule_margin(&r2, delta, mover_z, memo) } else { rule_margin(&r2, -delta, !mover_z, memo) }
    };
    let v = if z {
        let i = first_pick(r);
        let r1 = without_value(r, i);
        distinct(&r1).into_iter().map(|q| next(without(&r1, q), d + r1[q] as i32 - i, true, memo)).min().unwrap()
    } else {
        distinct(r)
            .into_iter()
            .map(|a| {
                let i = r[a] as i32;
                let r1 = without(r, a);
                let j = hyb2_answer(&r1, d, i);
                next(without_value(&r1, j), d + j - i, false, memo)
            })
            .min()
            .unwrap()
    };
    memo.insert((r.to_vec(), d, z), v);
    v
}

/// Whether the bottom-up matching of R pairs u with v.
fn matched(r: &[u8], u: u8, v: u8) -> bool {
    r.chunks(2).any(|c| (c[0] == u && c[1] == v) || (c[0] == v && c[1] == u))
}

fn main() {
    let p_max: usize = std::env::args().nth(1).expect("p_max").parse().expect("p_max");
    for p in 1..=p_max {
        // (mover is Z, slack, broken) -> count
        let mut tally: BTreeMap<(bool, i32, usize), usize> = BTreeMap::new();
        let mut extreme: BTreeMap<(bool, i32), String> = BTreeMap::new();
        // Z starts with one orphan pair: (orphans matched together, gap, slack) -> count, example
        let mut orph: BTreeMap<(bool, u8, i32), (usize, String)> = BTreeMap::new();
        // (mover is Z, pre-switch) -> least rule margin over reached starts, example
        let mut least: BTreeMap<(bool, bool), (i32, String)> = BTreeMap::new();
        let mut memo = std::collections::HashMap::new();
        for t in 0..1usize << p {
            let mut o: Set = (0..p).flat_map(|i| [2 * i as u8, 2 * i as u8 + (t >> i & 1) as u8]).collect();
            o.sort_unstable();
            let g = t.count_ones() as i32 % 2;
            let mut seen = HashSet::new();
            let mut stack = vec![(o.clone(), g, true), (o, g, false)];
            while let Some((r, d, z)) = stack.pop() {
                if r.is_empty() || !seen.insert((r.clone(), d, z)) {
                    continue;
                }
                let slack = d - cost(&r);
                let m = rule_margin(&r, d, z, &mut memo);
                let key = (z, slack < 0);
                if least.get(&key).map_or(true, |x| m < x.0) {
                    least.insert(key, (m, format!("t={t:0w$b} {r:?} d={d}", w = p)));
                }
                *tally.entry((z, slack, broken(&r, t, p))).or_insert(0) += 1;
                extreme.entry((z, slack)).or_insert_with(|| format!("t={t:0w$b} {r:?} d={d}", w = p));
                if z {
                    let os = orphans(&r, t, p);
                    if os.len() == 2 {
                        let (u, v) = (os[0].min(os[1]), os[0].max(os[1]));
                        let e = orph.entry((matched(&r, u, v), v - u, slack)).or_insert((0, String::new()));
                        e.0 += 1;
                        if e.1.is_empty() {
                            e.1 = format!("t={t:0w$b} {r:?} d={d}", w = p);
                        }
                    }
                }
                let push = |r2: Set, delta: i32, mover_z: bool, st: &mut Vec<(Set, i32, bool)>| {
                    if delta >= 0 { st.push((r2, delta, mover_z)) } else { st.push((r2, -delta, !mover_z)) }
                };
                if z {
                    let i = first_pick(&r);
                    let r1 = without_value(&r, i);
                    for q in distinct(&r1) {
                        push(without(&r1, q), d + r1[q] as i32 - i, true, &mut stack);
                    }
                } else {
                    for a in distinct(&r) {
                        let i = r[a] as i32;
                        let r1 = without(&r, a);
                        let j = hyb2_answer(&r1, d, i);
                        push(without_value(&r1, j), d + j - i, false, &mut stack);
                    }
                }
            }
        }
        println!("p={p}: reached round starts by (mover, debt − c(R), broken pairs): count");
        for ((z, s, b), n) in &tally {
            println!("  {} slack {s:+} broken {b}: {n}", if *z { "Z" } else { "Y" });
        }
        for ((z, pre), (m, ex)) in &least {
            println!("  least rule margin, {} to move, {}: {m} ({ex})", if *z { "Z" } else { "Y" }, if *pre { "debt < c(R)" } else { "debt ≥ c(R)" });
        }
        for ((m, gap, s), (n, ex)) in &orph {
            println!("  Z with an orphan pair: matched together {m}, gap {gap}, slack {s:+}: {n} (e.g. {ex})");
        }
        for ((z, s), ex) in &extreme {
            println!("  first {} slack {s:+}: {ex}", if *z { "Z" } else { "Y" });
        }
    }
}
