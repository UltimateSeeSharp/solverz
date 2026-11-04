//! Usage: e29_pair_deletions <n_min> <n_max>
//! C89 (NLB*): R = {k..N} minus j disjoint adjacent pairs (any placement), |R| even, 4j ≤ |R|; is the mover ever
//! losing at a deficit d < min(k, |R|/2) with d + sum(R) even? One `Solver` on {1..N} answers every R; prints the
//! losses (at most SHOWN per N) and the count of positions.
//! First check: ({17, 18, 21, 22}, 2), at the excluded boundary d = |R|/2, is a mover loss (the ideator's census).

use catch_up::{Outcome, Solver};

const SHOWN: usize = 10;

/// Every set of `j` disjoint adjacent pairs {x, x + 1} inside [lo, hi], as start lists.
fn placements(lo: u64, hi: u64, j: usize, out: &mut Vec<Vec<u64>>, cur: &mut Vec<u64>) {
    if cur.len() == j {
        out.push(cur.clone());
        return;
    }
    let start = cur.last().map_or(lo, |&x| x + 2);
    let mut x = start;
    while x + 1 <= hi {
        cur.push(x);
        placements(lo, hi, j, out, cur);
        cur.pop();
        x += 1;
    }
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("n_min n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e29_pair_deletions <n_min> <n_max>");
    let check = [17u64, 18, 21, 22];
    assert_eq!(Solver::new(&check).position(0b1111, 2), Outcome::Loss, "the census's boundary loss");
    println!("check: ({check:?}, 2) is a mover loss");
    let mut total_losses = 0;
    for n in a[0]..=a[1] {
        let mut s = Solver::new(&(1..=n).collect::<Vec<u64>>());
        let (mut count, mut losses) = (0usize, 0usize);
        for k in 1..=n {
            let len = (n - k + 1) as usize;
            for j in 0..=len / 2 {
                let size = len - 2 * j;
                if size == 0 || size % 2 == 1 || 4 * j > size {
                    continue;
                }
                let mut ps = vec![];
                placements(k, n, j, &mut ps, &mut vec![]);
                for starts in ps {
                    let r: Vec<u64> = (k..=n).filter(|x| !starts.iter().any(|&y| *x == y || *x == y + 1)).collect();
                    let mask: usize = r.iter().map(|&x| 1usize << (x - 1)).sum();
                    let sum: u64 = r.iter().sum();
                    let half = (size / 2) as u64;
                    for d in 0..k.min(half) {
                        if (d + sum) % 2 == 1 {
                            continue;
                        }
                        count += 1;
                        if s.position(mask, d) == Outcome::Loss {
                            losses += 1;
                            if losses <= SHOWN {
                                println!("  N={n}: loss ({r:?}, d={d}) j={j}");
                            }
                        }
                    }
                }
            }
        }
        total_losses += losses;
        println!("N={n}: {count} positions, {losses} mover losses");
    }
    println!("total mover losses: {total_losses}");
}
