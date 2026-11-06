//! E10: the orbit exhaust (I5, A5; `orbits.rs`) on Instances of `instances.csv` with
//! gcd(v, n) = 1, fewest orbits first, `threads` Instances at a time, each stopped after
//! `max_nodes` nodes. Validates the engine first. Resumable: an ID with a complete line in
//! `out` is skipped; new lines are appended.
//! Usage: `e10_orbit_exhaust <instances.csv> <out> <threads> <max_nodes> [selection]`;
//! selection `open` (default: every open row), `exists` (every existing row), `N1,N2,…`, or
//! `@file` (the first token of each line; IDs of any status).
//! Line: `id key verdict r |M| nodes seconds set`: verdict `found` (set: `coords±` per marked
//! element, checked by `is_sds`), `none` (every orbit sign choice exhausted) or `cut`.

use signed_difference_sets::Group;
use signed_difference_sets::instances::{Instance, read};
use signed_difference_sets::orbits::{OrbitCase, Verdict};
use std::collections::HashSet;
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::time::Instant;

const STATUS_OPEN: &str = "open";
const STATUS_EXISTS: &str = "exists";
/// Fields of a complete output line before the set.
const LINE_FIELDS: usize = 7;
/// Worker stack: the search recurses once per orbit.
const STACK_BYTES: usize = 64 << 20;

/// Which Instances to run.
enum Selection {
    Status(&'static str),
    Ids(HashSet<String>),
}

impl Selection {
    fn parse(arg: Option<&str>) -> Self {
        match arg {
            None | Some(STATUS_OPEN) => Selection::Status(STATUS_OPEN),
            Some(STATUS_EXISTS) => Selection::Status(STATUS_EXISTS),
            Some(path) if path.starts_with('@') => Selection::Ids(
                std::fs::read_to_string(&path[1..])
                    .unwrap()
                    .lines()
                    .filter_map(|l| l.split_whitespace().next().map(str::to_string))
                    .collect(),
            ),
            Some(ids) => Selection::Ids(ids.split(',').map(str::to_string).collect()),
        }
    }

    fn takes(&self, inst: &Instance) -> bool {
        match self {
            Selection::Status(s) => inst.status == *s,
            Selection::Ids(ids) => ids.contains(&inst.id),
        }
    }
}

/// Runs one Instance; the output line.
fn run(inst: &Instance, case: &OrbitCase, max_nodes: u64) -> String {
    let t = Instant::now();
    let out = case.exhaust(max_nodes);
    let set = match &out.verdict {
        Verdict::Found(d) => {
            let group = Group::new(&inst.shape);
            (0..group.order)
                .filter(|&x| d[x] != 0)
                .map(|x| {
                    let c: Vec<String> = group.coords(x).iter().map(|c| c.to_string()).collect();
                    format!("{}{}", c.join("."), if d[x] > 0 { '+' } else { '-' })
                })
                .collect::<Vec<_>>()
                .join(" ")
        }
        _ => String::new(),
    };
    format!(
        "{} {} {} {} {} {} {:.3} {set}",
        inst.id,
        inst.key,
        out.verdict.label(),
        case.orbits.len(),
        case.mults.elements.len(),
        out.nodes,
        t.elapsed().as_secs_f64()
    )
}

/// The engine finds known sets (each checked by `is_sds` inside `exhaust`) and kills
/// (79, 40, 2) in C₇₉, ruled out by hand in the refuter's a5-a3 report.
fn validate() {
    for (k, lam, shape) in [
        (3, 1, vec![7]),
        (6, 1, vec![11]),
        (12, 4, vec![23]),
        (24, 10, vec![47]),
        (10, 1, vec![55]),
        (16, 3, vec![61]),
        (29, 4, vec![104]),
    ] {
        let out = OrbitCase::new(&shape, k, lam).unwrap().exhaust(u64::MAX);
        assert!(matches!(out.verdict, Verdict::Found(_)), "engine misses ({k}, {lam}, {shape:?})");
    }
    let case = OrbitCase::new(&[79], 40, 2).unwrap();
    assert_eq!(case.mults.elements.len(), 39, "M for (79, 40, 2) is not the squares");
    assert_eq!(case.exhaust(u64::MAX).verdict, Verdict::NoSet, "engine finds (79, 40, 2)");
    eprintln!("validation passed");
}

/// IDs with a complete line in `out`.
fn done_ids(out: &str) -> HashSet<String> {
    let labels = [Verdict::FOUND, Verdict::NO_SET, Verdict::CUT];
    std::fs::read_to_string(out)
        .unwrap_or_default()
        .lines()
        .map(|l| l.split(' ').collect::<Vec<_>>())
        .filter(|f| f.len() >= LINE_FIELDS && labels.contains(&f[2]))
        .map(|f| f[0].to_string())
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out_path = args[1].clone();
    let threads: usize = args[2].parse().unwrap();
    let max_nodes: u64 = args[3].parse().unwrap();
    let selection = Selection::parse(args.get(4).map(String::as_str));
    validate();
    let done = done_ids(&out_path);
    let (mut skipped, mut todo) = (0, Vec::new());
    for inst in read(&args[0]).into_iter().filter(|i| selection.takes(i)) {
        match OrbitCase::new(&inst.shape, inst.k, inst.lam) {
            Ok(case) if !done.contains(&inst.id) => todo.push((inst, case)),
            Ok(_) => {}
            Err(_) => skipped += 1,
        }
    }
    todo.sort_by_key(|(i, c)| (c.orbits.len(), i.v, i.id[1..].parse::<usize>().unwrap_or(0)));
    eprintln!("{} to run, {} already in {out_path}, {skipped} without C9", todo.len(), done.len());
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let file = std::fs::OpenOptions::new().create(true).append(true).open(&out_path).unwrap();
    let file = Arc::new(Mutex::new(file));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, file) = (Arc::clone(&queue), Arc::clone(&file));
            std::thread::Builder::new()
                .stack_size(STACK_BYTES)
                .spawn(move || {
                    loop {
                        // The guard must drop before the search, or the workers run one at a time.
                        let next = queue.lock().unwrap().pop();
                        let Some((inst, case)) = next else { break };
                        let line = run(&inst, &case, max_nodes);
                        let mut f = file.lock().unwrap();
                        writeln!(f, "{line}").unwrap();
                        f.flush().unwrap();
                    }
                })
                .unwrap()
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
}
