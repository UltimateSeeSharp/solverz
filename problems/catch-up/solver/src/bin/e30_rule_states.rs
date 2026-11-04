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

fn main() {
    let p_max: usize = std::env::args().nth(1).expect("p_max").parse().expect("p_max");
    for p in 1..=p_max {
        // (mover is Z, slack, broken) -> count
        let mut tally: BTreeMap<(bool, i32, usize), usize> = BTreeMap::new();
        let mut extreme: BTreeMap<(bool, i32), String> = BTreeMap::new();
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
                *tally.entry((z, slack, broken(&r, t, p))).or_insert(0) += 1;
                extreme.entry((z, slack)).or_insert_with(|| format!("t={t:0w$b} {r:?} d={d}", w = p));
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
        for ((z, s), ex) in &extreme {
            println!("  first {} slack {s:+}: {ex}", if *z { "Z" } else { "Y" });
        }
    }
}
