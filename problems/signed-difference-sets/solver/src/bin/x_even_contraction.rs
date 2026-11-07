//! Exploration (C26): the even contraction. With 4 | n and a quotient H = C_(2^j) × K of G (2 self-conjugate mod exp K),
//! Ma's step makes the coset sums on L = H/<u> even; Z = sums/2 has |Z| ≤ c (c = v/|H|), Σ Z² = (k + λ(2c − 1))/4,
//! autocorrelation cλ/2, Σ Z = s/2, Σ|Z| ≤ k/2 with Σ|Z| ≡ s/2 (mod 2). A row dies when no such Z exists on some L
//! (or the demands are not integers). Usage: `x_even_contraction <instances.csv> <max |L|> <max_nodes> [ids file]`.

use signed_difference_sets::Group;
use signed_difference_sets::contraction::{search, Demand};
use signed_difference_sets::instances::read;
use std::collections::HashSet;

fn v2(mut x: usize) -> u32 {
    let mut e = 0;
    while x % 2 == 0 && x > 0 {
        x /= 2;
        e += 1;
    }
    e
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn lcm(a: usize, b: usize) -> usize {
    a / gcd(a, b) * b
}

/// 2^i ≡ −1 (mod m) for some i (m odd; m ≤ 2 counts).
fn self_conj2(m: usize) -> bool {
    if m <= 2 {
        return true;
    }
    let mut x = 2 % m;
    for _ in 0..m {
        if x == m - 1 {
            return true;
        }
        x = x * 2 % m;
    }
    false
}

fn divisors(n: usize) -> Vec<usize> {
    (1..=n).filter(|d| n % d == 0).collect()
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let insts = read(&a[1]);
    let max_l: usize = a[2].parse().unwrap();
    let max_nodes: u64 = a[3].parse().unwrap();
    let only: Option<HashSet<String>> = a.get(4).map(|f| {
        std::fs::read_to_string(f).unwrap().lines().map(|l| l.split_whitespace().next().unwrap_or("").to_string()).collect()
    });
    for inst in insts.iter().filter(|i| i.status == "open" || only.is_some()) {
        if let Some(o) = &only {
            if !o.contains(&inst.id) {
                continue;
            }
        }
        let n = inst.k as i64 - inst.lam;
        if n <= 0 || n % 4 != 0 || inst.v % 2 != 0 {
            continue;
        }
        let total = inst.k as i64 + inst.lam * (inst.v as i64 - 1);
        let s = (total as f64).sqrt().round() as i64;
        if s * s != total {
            continue;
        }
        let odd: Vec<usize> = inst.shape.iter().map(|&m| m >> v2(m)).collect();
        let jmax = inst.shape.iter().map(|&m| v2(m)).max().unwrap_or(0);
        let mut notes = Vec::new();
        let mut kill = None;
        let mut seen = HashSet::new();
        'outer: for j in 1..=jmax {
            let lists: Vec<Vec<usize>> = odd.iter().map(|&o| divisors(o)).collect();
            let mut idx = vec![0usize; lists.len()];
            loop {
                let ds: Vec<usize> = idx.iter().zip(&lists).map(|(&i, l)| l[i]).collect();
                let kexp = ds.iter().fold(1, |acc, &d| lcm(acc, d));
                if self_conj2(kexp) {
                    let mut lf: Vec<usize> = std::iter::once(1usize << (j - 1)).chain(ds.iter().copied()).filter(|&x| x > 1).collect();
                    if lf.is_empty() {
                        lf.push(1);
                    }
                    let lord: usize = lf.iter().product();
                    let c = (inst.v / (lord * 2)) as i64;
                    let mut key = lf.clone();
                    key.sort();
                    if lord <= max_l && seen.insert((key, c)) {
                        let sq = inst.k as i64 + inst.lam * (2 * c - 1);
                        let tg = c * inst.lam;
                        if sq % 4 != 0 || tg % 2 != 0 || s % 2 != 0 {
                            kill = Some(format!("{:?}:c{}:nonintegral", lf, c));
                            break 'outer;
                        }
                        let half_k = inst.k as i64 / 2;
                        let kz = if (half_k - s / 2).rem_euclid(2) == 0 { half_k } else { half_k - 1 };
                        let dem = Demand { c, square: sq / 4, target: tg / 2, sum: s / 2 };
                        let group = Group::new(&lf);
                        let out = search(&group, kz.max(0) as usize, &dem, max_nodes);
                        if out.cut {
                            notes.push(format!("{:?}:c{}:cut", lf, c));
                        } else if out.found.is_none() {
                            kill = Some(format!("{:?}:c{}:{}", lf, c, out.nodes));
                            break 'outer;
                        } else {
                            notes.push(format!("{:?}:c{}:found", lf, c));
                        }
                    }
                }
                let mut t = 0;
                loop {
                    if t == idx.len() {
                        break;
                    }
                    idx[t] += 1;
                    if idx[t] < lists[t].len() {
                        break;
                    }
                    idx[t] = 0;
                    t += 1;
                }
                if t == idx.len() {
                    break;
                }
            }
        }
        match kill {
            Some(k) => println!("{} {} KILL {}", inst.id, inst.key, k),
            None => println!("{} {} - {}", inst.id, inst.key, notes.join(" ")),
        }
    }
}
