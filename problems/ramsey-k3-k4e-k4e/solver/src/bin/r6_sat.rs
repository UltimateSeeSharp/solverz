//! E6: SAT search for a valid colouring of Kₙ by cube-and-conquer. Every
//! valid colouring can be relabelled so point 0's pairs are sorted
//! (colour 0 first, then 1, then 2) and recoloured 1 ↔ 2 so colour 1 is at
//! least as common as colour 2 there; one cube per such row, each solved by
//! its own CaDiCaL process. Models are decoded and rescored by `violations`.
//! Usage: `r6_sat <n> <threads> <seconds per cube, 0 = none> <cadical> <workdir> [--out <file>]`.
//! Prints one line per cube (SAT, UNSAT or UNKNOWN) and a summary.

use ramsey_k3_k4e_k4e::sat::{clauses, cube, decode, dimacs, vars};
use ramsey_k3_k4e_k4e::{K4E_FREE, TRIANGLE_FREE, violations};
use std::collections::HashSet;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

/// CaDiCaL's exit codes.
const EXIT_SAT: i32 = 10;
const EXIT_UNSAT: i32 = 20;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = a[0].parse().expect("n");
    let threads: usize = a[1].parse().expect("threads");
    let seconds: u64 = a[2].parse().expect("seconds");
    let cadical = PathBuf::from(&a[3]);
    let workdir = PathBuf::from(&a[4]);
    let out = a.iter().position(|x| x == "--out").map(|i| a[i + 1].clone());
    std::fs::create_dir_all(&workdir).expect("workdir");

    let base = clauses(n);
    let mut cubes = Vec::new();
    for zeros in 0..n {
        for ones in 0..n - zeros {
            let twos = n - 1 - zeros - ones;
            if ones >= twos {
                cubes.push((zeros, ones, twos));
            }
        }
    }
    let total = cubes.len();
    let cubes = Arc::new(Mutex::new(cubes.into_iter()));
    let found = Arc::new(AtomicBool::new(false));
    let unsat = Arc::new(AtomicUsize::new(0));
    let unknown = Arc::new(Mutex::new(Vec::new()));
    let answer = Arc::new(Mutex::new(None));
    let base = Arc::new(base);
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (cubes, found, unsat, unknown, answer, base) =
                (cubes.clone(), found.clone(), unsat.clone(), unknown.clone(), answer.clone(), base.clone());
            let (cadical, workdir) = (cadical.clone(), workdir.clone());
            std::thread::spawn(move || {
                loop {
                    let next = cubes.lock().expect("lock").next();
                    let Some((zeros, ones, twos)) = next else { break };
                    if found.load(Ordering::Relaxed) {
                        break;
                    }
                    let row: Vec<u8> = std::iter::repeat_n(TRIANGLE_FREE, zeros)
                        .chain(std::iter::repeat_n(K4E_FREE[0], ones))
                        .chain(std::iter::repeat_n(K4E_FREE[1], twos))
                        .collect();
                    let mut cls = (*base).clone();
                    cls.extend(cube(n, &row));
                    let file = workdir.join(format!("n{n}_{zeros}_{ones}_{twos}.cnf"));
                    std::fs::write(&file, dimacs(vars(n), &cls)).expect("write cnf");
                    let mut cmd = Command::new(&cadical);
                    if seconds > 0 {
                        cmd.arg("-t").arg(seconds.to_string());
                    }
                    let output = cmd.arg(&file).output().expect("run cadical");
                    let _ = std::fs::remove_file(&file);
                    let tag = format!("cube {zeros}/{ones}/{twos}");
                    match output.status.code() {
                        Some(EXIT_SAT) => {
                            let text = String::from_utf8_lossy(&output.stdout);
                            let lits: HashSet<i64> = text
                                .lines()
                                .filter(|l| l.starts_with("v "))
                                .flat_map(|l| l[2..].split_whitespace().map(|x| x.parse::<i64>().expect("literal")))
                                .filter(|&l| l > 0)
                                .collect();
                            let c = decode(n, &lits);
                            let score = violations(&c);
                            println!("{tag} SAT violations={score}");
                            assert_eq!(score, 0, "a model must be a valid colouring");
                            found.store(true, Ordering::Relaxed);
                            answer.lock().expect("lock").get_or_insert(c);
                        }
                        Some(EXIT_UNSAT) => {
                            println!("{tag} UNSAT");
                            unsat.fetch_add(1, Ordering::Relaxed);
                        }
                        other => {
                            println!("{tag} UNKNOWN (exit {other:?})");
                            unknown.lock().expect("lock").push(tag);
                        }
                    }
                }
            })
        })
        .collect();
    for w in workers {
        w.join().expect("worker");
    }
    let unknown = unknown.lock().expect("lock");
    println!(
        "n={n} cubes={total} unsat={} unknown={} found={}",
        unsat.load(Ordering::Relaxed),
        unknown.len(),
        found.load(Ordering::Relaxed)
    );
    if let (Some(path), Some(c)) = (out, answer.lock().expect("lock").as_ref()) {
        std::fs::write(&path, c.to_text()).expect("write");
        println!("answer written to {path}");
    }
}
