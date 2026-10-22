//! Usage: catch-up [--engine dfs|layered|tiled|cuda] [--top H] [--from N] [to]   (defaults: dfs, 8, 1, 20)
//! The cuda engine needs `--features cuda`.
//! Prints, for each N, the optimal-play outcome of Catch-Up on {1..N} and player 1's opening options.

use catch_up::layered::Layered;
use catch_up::tiled::Tiled;
use catch_up::{interval, Outcome, Solver};
use std::time::Instant;
#[cfg(feature = "cuda")]
use {catch_up::cuda::Cuda, std::sync::OnceLock};

const DEFAULT_TO: u64 = 20;
const DEFAULT_FROM: u64 = 1;
const DEFAULT_TOP: usize = 8;

#[derive(Clone, Copy, PartialEq)]
enum Engine {
    Dfs,
    Layered,
    Tiled,
    Cuda,
}

struct Args {
    engine: Engine,
    top: usize,
    from: u64,
    to: u64,
}

fn parse_args() -> Args {
    let mut args = Args { engine: Engine::Dfs, top: DEFAULT_TOP, from: DEFAULT_FROM, to: DEFAULT_TO };
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--engine" => {
                args.engine = match it.next().as_deref() {
                    Some("dfs") => Engine::Dfs,
                    Some("layered") => Engine::Layered,
                    Some("tiled") => Engine::Tiled,
                    Some("cuda") => Engine::Cuda,
                    other => panic!("unknown engine {other:?}; use dfs, layered, tiled or cuda"),
                }
            }
            "--top" => args.top = it.next().and_then(|s| s.parse().ok()).expect("--top needs a number"),
            "--from" => args.from = it.next().and_then(|s| s.parse().ok()).expect("--from needs a number"),
            n => args.to = n.parse().expect("expected a number"),
        }
    }
    args
}

#[cfg(feature = "cuda")]
fn cuda_openings(numbers: &[u64]) -> Vec<(u64, Outcome)> {
    static CUDA: OnceLock<Cuda> = OnceLock::new();
    let cuda = CUDA.get_or_init(|| {
        let cuda = Cuda::new().expect("no usable CUDA device");
        eprintln!("CUDA: {}", cuda.device);
        cuda
    });
    Layered::new(numbers).openings_cuda(cuda).expect("CUDA run failed")
}

#[cfg(not(feature = "cuda"))]
fn cuda_openings(_: &[u64]) -> Vec<(u64, Outcome)> {
    panic!("built without CUDA support; rebuild with --features cuda")
}

fn list(openings: &[(u64, Outcome)], want: Outcome) -> String {
    let xs: Vec<String> = openings.iter().filter(|&&(_, o)| o == want).map(|(x, _)| x.to_string()).collect();
    if xs.is_empty() { "-".into() } else { xs.join(",") }
}

fn main() {
    let args = parse_args();
    println!("| N | total even | value (P1) | openings that win | draw | lose | positions | ms |");
    println!("|---|---|---|---|---|---|---|---|");
    for n in args.from..=args.to {
        let start = Instant::now();
        let numbers = interval(n);
        let (openings, positions) = match args.engine {
            Engine::Dfs => {
                let mut solver = Solver::new(&numbers);
                let openings = solver.openings();
                (openings, solver.positions)
            }
            // The layered engines evaluate every position: 2^n masks × (n + 1) gaps.
            Engine::Layered => (Layered::new(&numbers).openings(), (1u64 << n) * (n + 1)),
            Engine::Tiled => (Tiled::new(&numbers, args.top.min(n as usize)).openings(), (1u64 << n) * (n + 1)),
            Engine::Cuda => (cuda_openings(&numbers), (1u64 << n) * (n + 1)),
        };
        let value = openings.iter().map(|&(_, o)| o).max().unwrap_or(Outcome::Draw);
        println!(
            "| {n} | {} | {value:?} | {} | {} | {} | {positions} | {} |",
            (n * (n + 1) / 2) % 2 == 0,
            list(&openings, Outcome::Win),
            list(&openings, Outcome::Draw),
            list(&openings, Outcome::Loss),
            start.elapsed().as_millis()
        );
    }
}
