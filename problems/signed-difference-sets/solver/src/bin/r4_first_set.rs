//! E4: P1 on every open Instance of `instances.csv` with v ≤ `max_v`, stopping at the first
//! set or after `max_nodes` nodes, `threads` Instances at a time. Validates the engine first.
//! Usage: `r4_first_set <instances.csv> <max_v> <max_nodes> <threads> [ids]`, `ids` a
//! comma-separated list restricting the run (E7); one line per Instance: id, key,
//! yes/no/cut, nodes, time, set (`coords±` per marked element).

use signed_difference_sets::{search_capped, Group};
use std::sync::{Arc, Mutex};
use std::time::Instant;

/// One open Instance: id, key, k, λ, cyclic factors.
struct Instance {
    id: String,
    key: String,
    k: usize,
    lam: i64,
    shape: Vec<usize>,
}

/// Splits a CSV line, keeping quoted fields (keys contain commas) whole.
fn fields(line: &str) -> Vec<String> {
    let (mut out, mut cur, mut quoted) = (Vec::new(), String::new(), false);
    for c in line.chars() {
        match c {
            '"' => quoted = !quoted,
            ',' if !quoted => out.push(std::mem::take(&mut cur)),
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Parses `SDS(v,k,λ,[m1,…])`.
fn parse_key(id: &str, key: &str) -> Instance {
    let inner = &key[4..key.len() - 1];
    let (nums, shape) = inner.split_once(",[").unwrap();
    let nums: Vec<i64> = nums.split(',').map(|x| x.parse().unwrap()).collect();
    let shape: Vec<usize> =
        shape.trim_end_matches(']').split(',').map(|x| x.parse().unwrap()).collect();
    assert_eq!(nums[0] as usize, shape.iter().product::<usize>(), "{key}: v ≠ |G|");
    Instance { id: id.to_string(), key: key.to_string(), k: nums[1] as usize, lam: nums[2], shape }
}

/// Searches one Instance; the output line.
fn run(inst: &Instance, max_nodes: u64) -> String {
    let group = Group::new(&inst.shape);
    let t = Instant::now();
    let out = search_capped(&group, inst.k, inst.lam, 1, max_nodes).expect("F1 holds");
    let (result, set) = match out.solutions.first() {
        Some(d) => {
            let marked: Vec<String> = (0..group.order)
                .filter(|&x| d[x] != 0)
                .map(|x| {
                    let c: Vec<String> = group.coords(x).iter().map(|c| c.to_string()).collect();
                    format!("{}{}", c.join("."), if d[x] > 0 { '+' } else { '-' })
                })
                .collect();
            ("yes", marked.join(" "))
        }
        None if out.nodes > max_nodes => ("cut", String::new()),
        None => ("no", String::new()),
    };
    format!("{} {} {result} {} {:.1?} {set}", inst.id, inst.key, out.nodes, t.elapsed())
}

/// The engine finds known sets, finds none where Lean rules them out, and repeats E1.
fn validate() {
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
        let out = search_capped(&Group::new(&shape), k, lam, 1, u64::MAX).unwrap();
        assert!(!out.solutions.is_empty(), "engine misses a known SDS ({k}, {lam}, {shape:?})");
    }
    // F1 already rules it out: parity of k + s fails.
    let none = search_capped(&Group::new(&[2, 2]), 3, -1, 1, u64::MAX);
    assert!(none.is_none_or(|o| o.solutions.is_empty()), "engine finds a set Lean rules out");
    // E1's node counts: the search tree must not change.
    for (k, lam, shape, nodes) in [(8, 1, vec![3, 3], 525), (17, 8, vec![2, 10], 226_532)] {
        let out = search_capped(&Group::new(&shape), k, lam, usize::MAX, u64::MAX).unwrap();
        assert!(out.solutions.is_empty() && out.nodes == nodes, "E1 not reproduced");
    }
    eprintln!("validation passed");
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let max_v: usize = args[1].parse().unwrap();
    let max_nodes: u64 = args[2].parse().unwrap();
    let threads: usize = args[3].parse().unwrap();
    let only: Option<Vec<&str>> = args.get(4).map(|ids| ids.split(',').collect());
    validate();
    let text = std::fs::read_to_string(&args[0]).unwrap();
    let mut todo: Vec<Instance> = text
        .lines()
        .skip(1)
        .map(fields)
        .filter(|f| f[3] == "open")
        .filter(|f| only.as_ref().is_none_or(|ids| ids.contains(&f[0].as_str())))
        .map(|f| parse_key(&f[0], &f[1]))
        .filter(|i| i.shape.iter().product::<usize>() <= max_v)
        .collect();
    todo.reverse();
    let queue = Arc::new(Mutex::new(todo));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let queue = Arc::clone(&queue);
            std::thread::spawn(move || {
                loop {
                    // The guard must drop before the search, or the workers run one at a time.
                    let next = queue.lock().unwrap().pop();
                    let Some(inst) = next else { break };
                    println!("{}", run(&inst, max_nodes));
                }
            })
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
}
