//! R1: validate the P1 engine on known objects O1–O5 and known non-existence, then search
//! cases S1, S2 exhaustively.
//! Usage: `r1_small_cases` (all), or `r1_small_cases <v> <k> <λ> <m1,m2,…>` for one case.

use signed_difference_sets::{search, Group};
use std::time::Instant;

fn run(k: usize, lam: i64, shape: &[usize]) -> usize {
    let group = Group::new(shape);
    let t = Instant::now();
    let label = format!("(v={}, k={k}, λ={lam}) in C{:?}", group.order, shape);
    match search(&group, k, lam, usize::MAX) {
        None => {
            println!("{label}: no SDS (square condition F1 fails)");
            0
        }
        Some(out) => {
            println!(
                "{label}: {} solutions with 0 marked, sum +s; {} nodes; {:.2?}",
                out.solutions.len(),
                out.nodes,
                t.elapsed()
            );
            if let Some(d) = out.solutions.first() {
                let marked: Vec<String> = (0..group.order)
                    .filter(|&x| d[x] != 0)
                    .map(|x| format!("{:?}{}", group.coords(x), if d[x] > 0 { '+' } else { '-' }))
                    .collect();
                println!("  first: {}", marked.join(" "));
            }
            out.solutions.len()
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() == 4 {
        let shape: Vec<usize> = args[3].split(',').map(|m| m.parse().unwrap()).collect();
        run(args[1].parse().unwrap(), args[2].parse().unwrap(), &shape);
        return;
    }
    println!("validation: known objects must be found");
    for (k, lam, shape) in [
        (3, 1, vec![7]),
        (4, 0, vec![7]),
        (4, 0, vec![4]),
        (4, -1, vec![5]),
        (8, -1, vec![3, 3]),
        (5, 2, vec![11]),
        (9, 0, vec![13]),
        (6, 2, vec![4, 4]),
    ] {
        assert!(run(k, lam, &shape) > 0, "engine misses a known SDS");
    }
    println!("validation: known non-existence must give none");
    // Proved in Lean (`Tests/Statement.lean`, by exhaustion).
    assert_eq!(run(3, -1, &[2, 2]), 0, "engine finds a set Lean rules out");
    println!("cases");
    run(8, 1, &[3, 3]);
    run(17, 8, &[2, 10]);
}
