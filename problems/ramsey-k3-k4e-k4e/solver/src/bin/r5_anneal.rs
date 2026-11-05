//! E5: simulated annealing on all pairs of Kₙ, one independent search per
//! thread, each from its own seed; stops at the first valid colouring.
//! Usage: `r5_anneal <n> <threads> <restarts> <moves> <t_start> <t_end> <seed> [--out <file>]`.
//! Prints each thread's best score, and writes the overall best colouring.

use ramsey_k3_k4e_k4e::anneal::{Rng, Schedule, anneal};
use ramsey_k3_k4e_k4e::violations;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = a[0].parse().expect("n");
    let threads: u64 = a[1].parse().expect("threads");
    let schedule = Schedule {
        restarts: a[2].parse().expect("restarts"),
        moves: a[3].parse().expect("moves"),
        t_start: a[4].parse().expect("t_start"),
        t_end: a[5].parse().expect("t_end"),
    };
    let seed: u64 = a[6].parse().expect("seed");
    let out = a.iter().position(|x| x == "--out").map(|i| a[i + 1].clone());
    let done = Arc::new(AtomicBool::new(false));
    let schedule = Arc::new(schedule);
    let handles: Vec<_> = (0..threads)
        .map(|k| {
            let (done, schedule) = (done.clone(), schedule.clone());
            std::thread::spawn(move || {
                let mut rng = Rng::new(seed + k);
                let mut restarts = 0u64;
                let one = Schedule { restarts: 1, ..*schedule };
                let mut best = None;
                while restarts < schedule.restarts && !done.load(Ordering::Relaxed) {
                    let o = anneal(n, &one, &mut rng, &mut |_| {});
                    restarts += 1;
                    if o.best_score == 0 {
                        done.store(true, Ordering::Relaxed);
                    }
                    if best.as_ref().is_none_or(|b: &ramsey_k3_k4e_k4e::anneal::Outcome| o.best_score < b.best_score) {
                        best = Some(o);
                    }
                }
                (k, restarts, best.expect("one restart"))
            })
        })
        .collect();
    let mut overall: Option<ramsey_k3_k4e_k4e::Colouring> = None;
    let mut overall_score = usize::MAX;
    for h in handles {
        let (k, restarts, o) = h.join().expect("thread");
        assert_eq!(violations(&o.best), o.best_score, "incremental score must match");
        println!("thread={k} restarts={restarts} best={}", o.best_score);
        if o.best_score < overall_score {
            overall_score = o.best_score;
            overall = Some(o.best);
        }
    }
    println!("n={n} best={overall_score}");
    if let (Some(path), Some(c)) = (out, overall) {
        std::fs::write(&path, c.to_text()).expect("write");
    }
}
