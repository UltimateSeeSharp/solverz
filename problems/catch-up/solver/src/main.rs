//! Usage: catch-up [--engine dfs|layered|tiled|cuda|tiled-cuda] [--top H] [--ram GB] [--from N] [to]
//! (defaults: dfs, 8, 1, 20). The cuda engines need `--features cuda`; `--ram` is the RAM budget
//! for tiled-cuda's layers (default in `tiled_cuda::Config`).
//! Prints, for each N, the optimal-play outcome of Catch-Up on {1..N} and player 1's opening options.

use catch_up::layered::Layered;
use catch_up::tiled::Tiled;
use catch_up::{interval, Outcome, Solver};
use std::time::Instant;
#[cfg(feature = "cuda")]
use {
    catch_up::cuda::Cuda,
    catch_up::tiled_cuda::{Config, Gpu, TiledCuda},
    std::sync::OnceLock,
};

const DEFAULT_TO: u64 = 20;
const DEFAULT_FROM: u64 = 1;
const DEFAULT_TOP: usize = 8;
const BYTES_PER_GB: f64 = 1e9;

#[derive(Clone, Copy, PartialEq)]
enum Engine {
    Dfs,
    Layered,
    Tiled,
    Cuda,
    TiledCuda,
}

struct Args {
    engine: Engine,
    top: usize,
    ram_bytes: Option<usize>,
    from: u64,
    to: u64,
}

fn parse_args() -> Args {
    let mut args = Args { engine: Engine::Dfs, top: DEFAULT_TOP, ram_bytes: None, from: DEFAULT_FROM, to: DEFAULT_TO };
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--engine" => {
                args.engine = match it.next().as_deref() {
                    Some("dfs") => Engine::Dfs,
                    Some("layered") => Engine::Layered,
                    Some("tiled") => Engine::Tiled,
                    Some("cuda") => Engine::Cuda,
                    Some("tiled-cuda") => Engine::TiledCuda,
                    other => panic!("unknown engine {other:?}; use dfs, layered, tiled, cuda or tiled-cuda"),
                }
            }
            "--top" => args.top = it.next().and_then(|s| s.parse().ok()).expect("--top needs a number"),
            "--ram" => {
                let gb: f64 = it.next().and_then(|s| s.parse().ok()).expect("--ram needs a number of GB");
                args.ram_bytes = Some((gb * BYTES_PER_GB) as usize);
            }
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

/// Openings and positions stored; traffic goes to stderr.
#[cfg(feature = "cuda")]
fn tiled_cuda_openings(numbers: &[u64], top: usize, ram_bytes: Option<usize>) -> (Vec<(u64, Outcome)>, u64) {
    static GPU: OnceLock<Gpu> = OnceLock::new();
    let gpu = GPU.get_or_init(|| {
        let gpu = Gpu::new().expect("no usable CUDA device");
        eprintln!("CUDA: {}", gpu.device);
        gpu
    });
    let engine = TiledCuda::new(numbers, top);
    let default = Config::default();
    let config = Config { progress: true, ram_bytes: ram_bytes.unwrap_or(default.ram_bytes), ..default };
    let (openings, stats) = engine.openings(gpu, &config).expect("CUDA run failed");
    eprintln!("N = {}: {stats:?}", numbers.len());
    (openings, engine.positions())
}

#[cfg(not(feature = "cuda"))]
fn cuda_openings(_: &[u64]) -> Vec<(u64, Outcome)> {
    panic!("built without CUDA support; rebuild with --features cuda")
}

#[cfg(not(feature = "cuda"))]
fn tiled_cuda_openings(_: &[u64], _: usize, _: Option<usize>) -> (Vec<(u64, Outcome)>, u64) {
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
            // Only the gaps of each mask's parity: half of them.
            Engine::TiledCuda => tiled_cuda_openings(&numbers, args.top.min(n as usize), args.ram_bytes),
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
