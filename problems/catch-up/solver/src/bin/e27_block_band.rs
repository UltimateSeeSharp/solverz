//! Usage: e27_block_band <p_max> <n_max>
//! C86 (BAND): V({a..a+2p−1}, d) for p ≤ p_max, every a = 1..=2p+1, every d ≤ p with d ≡ p (mod 2); prints each
//! non-draw, marking diagonal (d = p) and off-diagonal entries.
//! C87 (BAND-PD): R = {k..N} of even size minus j aligned pairs {k + 2t, k + 2t + 1}, 4j ≤ |R|, p = |R|/2, every
//! d < min(k, p) with d + sum(R) even, N ≤ n_max; one `Solver` on {1..N} answers every R. Prints non-draws per N.
//! First checks: {2, 3, 4, 5} at deficit 2 is a mover win (C47, the known exception); a shared `Solver` on {1..N} =
//! a fresh one on every subset, gaps ≤ N, for N ≤ CHECK_N. Independent of the ideator's `rows.rs` (own solver).

use catch_up::{Outcome, Solver};

const CHECK_N: u64 = 10;
const SHOWN: usize = 8;
const C47_SET: [u64; 4] = [2, 3, 4, 5];
const C47_GAP: u64 = 2;

fn full(n: usize) -> usize {
    (1usize << n) - 1
}

fn check() {
    let mut s = Solver::new(&C47_SET);
    assert_eq!(s.position(full(C47_SET.len()), C47_GAP), Outcome::Win, "C47's exception");
    let mut n_pos = 0;
    for n in 1..=CHECK_N {
        let numbers: Vec<u64> = (1..=n).collect();
        let mut shared = Solver::new(&numbers);
        for mask in 0..1usize << n {
            let xs: Vec<u64> = (0..n as usize).filter(|&i| mask >> i & 1 == 1).map(|i| numbers[i]).collect();
            let mut fresh = Solver::new(&xs);
            for gap in 0..=n {
                assert_eq!(shared.position(mask, gap), fresh.position(full(xs.len()), gap), "{xs:?} gap {gap}");
                n_pos += 1;
            }
        }
    }
    println!("check: C47's {C47_SET:?} at {C47_GAP} is W; shared = fresh Solver on {n_pos} positions, N ≤ {CHECK_N}");
}

fn blocks(p_max: u64) {
    println!("(1) blocks: non-draws with d ≤ p, d ≡ p (mod 2), a = 1..2p+1");
    let (mut total, mut diag, mut off) = (0, 0, 0);
    for p in 1..=p_max {
        for a in 1..=2 * p + 1 {
            let xs: Vec<u64> = (a..a + 2 * p).collect();
            let mut s = Solver::new(&xs);
            for d in (p % 2..=p).step_by(2) {
                total += 1;
                let v = s.position(full(xs.len()), d);
                if v != Outcome::Draw {
                    if d == p { diag += 1 } else { off += 1 }
                    println!("  p={p} a={a} d={d} ({}): {v:?}", if d == p { "diagonal" } else { "off-diagonal" });
                }
            }
        }
    }
    println!("  {total} entries: {diag} diagonal and {off} off-diagonal non-draws");
}

fn pair_sets(n_max: u64) {
    println!("(2) aligned dense pair sets, d < min(k, p)");
    for n in 4..=n_max {
        let mut s = Solver::new(&(1..=n).collect::<Vec<u64>>());
        let (mut count, mut bad) = (0usize, 0usize);
        for k in 1..=n {
            let len = n - k + 1;
            if len % 2 == 1 {
                continue;
            }
            let q = (len / 2) as usize;
            for del in 0..1usize << q {
                let j = del.count_ones() as usize;
                let size = 2 * (q - j);
                if size == 0 || 4 * j > size {
                    continue;
                }
                let r: Vec<u64> =
                    (0..q).filter(|&t| del >> t & 1 == 0).flat_map(|t| [k + 2 * t as u64, k + 2 * t as u64 + 1]).collect();
                let mask: usize = r.iter().map(|&x| 1usize << (x - 1)).sum();
                let sum: u64 = r.iter().sum();
                let p = (size / 2) as u64;
                for d in 0..k.min(p) {
                    if (d + sum) % 2 == 1 {
                        continue;
                    }
                    count += 1;
                    let v = s.position(mask, d);
                    if v != Outcome::Draw {
                        bad += 1;
                        if bad <= SHOWN {
                            println!("  N={n}: ({r:?}, d={d}) j={j}: {v:?}");
                        }
                    }
                }
            }
        }
        println!("  N={n}: {count} positions, {bad} non-draws");
    }
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("p_max n_max")).collect();
    assert_eq!(a.len(), 2, "usage: e27_block_band <p_max> <n_max>");
    check();
    blocks(a[0]);
    pair_sets(a[1]);
}
