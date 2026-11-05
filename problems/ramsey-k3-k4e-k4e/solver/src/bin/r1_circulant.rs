//! R1: every circulant 3-colouring of Kₙ (pair ij coloured by its distance
//! around ℤₙ), scored by `violations`. Usage: `r1_circulant <n>... [--out <dir>]`.
//! Per n: how many score 0, the best score, and one best colouring written
//! to `<dir>/circulant_<n>.txt` when `--out` is given.

use ramsey_k3_k4e_k4e::{COLOURS, Colouring, violations};
use std::path::PathBuf;

/// The colouring of Kₙ whose pair ij has colour `by_distance[d − 1]`, d the distance.
fn circulant(n: usize, by_distance: &[u8]) -> Colouring {
    let mut c = Colouring::new(n);
    for i in 0..n {
        for j in i + 1..n {
            let d = (j - i).min(n - (j - i));
            c.set(i, j, by_distance[d - 1]);
        }
    }
    c
}

fn main() {
    let mut sizes = Vec::new();
    let mut out: Option<PathBuf> = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        if a == "--out" {
            out = Some(PathBuf::from(args.next().expect("--out needs a directory")));
        } else {
            sizes.push(a.parse::<usize>().expect("n must be a number"));
        }
    }
    for n in sizes {
        let classes = n / 2;
        let total = (COLOURS as u64).pow(classes as u32);
        let mut by_distance = vec![0u8; classes];
        let (mut valid, mut best, mut best_c) = (0u64, usize::MAX, None);
        for code in 0..total {
            let mut x = code;
            for slot in by_distance.iter_mut() {
                *slot = (x % COLOURS as u64) as u8;
                x /= COLOURS as u64;
            }
            let c = circulant(n, &by_distance);
            let score = violations(&c);
            if score == 0 {
                valid += 1;
            }
            if score < best {
                best = score;
                best_c = Some(c);
            }
        }
        println!("n={n} circulants={total} valid={valid} best={best}");
        if let (Some(dir), Some(c)) = (&out, best_c) {
            std::fs::write(dir.join(format!("circulant_{n}.txt")), c.to_text()).expect("write");
        }
    }
}
