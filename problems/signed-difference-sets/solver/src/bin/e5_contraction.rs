//! E5: contraction (C3) on every open Instance of `instances.csv` with v ≤ `max_v`: for each
//! quotient H = ∏ ℤ_{dᵢ} of G, smallest first, an exact search for coset sums meeting C3's
//! demands, on H numbered as Lean's `Indexed` numbers it (so Lean's `noVector` visits the
//! same nodes). First validates: no Instance with v ≤ `max_v` that exists is killed, and N32
//! dies at C₅. Usage: `e5_contraction <instances.csv> <max_v> <max_nodes> <threads>`; one
//! line per Instance: id, key, status, then `KILL d H nodes vectors` (d: the divisors dᵢ,
//! H: invariant factors; vectors: those with the right sums, no symmetry) or `open` with
//! each quotient's outcome (`found`, `cut`).

use signed_difference_sets::contraction::{count_vectors, quotients, search, Demand};
use signed_difference_sets::instances::{read, Instance};
use signed_difference_sets::Group;
use std::sync::{Arc, Mutex};

/// The first quotient that kills the Instance, or every quotient's outcome.
fn run(inst: &Instance, max_nodes: u64) -> (bool, String) {
    let mut notes = Vec::new();
    for quo in quotients(&inst.shape) {
        let group = Group::new(&quo.divisors);
        let dem = Demand::new(inst.v, inst.k, inst.lam, group.order).expect("C1 holds");
        let out = search(&group, inst.k, &dem, max_nodes);
        let name = format!("{:?}", quo.invariants).replace(' ', "");
        let divisors = format!("{:?}", quo.divisors).replace(' ', "");
        if out.cut {
            notes.push(format!("{name}:cut"));
        } else if out.found.is_none() {
            let vectors = count_vectors(group.order, &dem);
            return (true, format!("KILL {divisors} {name} {} {vectors}", out.nodes));
        } else {
            notes.push(format!("{name}:found"));
        }
    }
    (false, format!("open {}", notes.join(" ")))
}

fn parallel(todo: Vec<Instance>, threads: usize, max_nodes: u64, print: bool) -> Vec<String> {
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let lines = Arc::new(Mutex::new(Vec::new()));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, lines) = (Arc::clone(&queue), Arc::clone(&lines));
            std::thread::spawn(move || loop {
                // The guard must drop before the search, or the workers run one at a time.
                let next = queue.lock().unwrap().pop();
                let Some(inst) = next else { break };
                let (killed, text) = run(&inst, max_nodes);
                let line = format!("{} {} {} {text}", inst.id, inst.key, inst.status);
                if print {
                    println!("{line}");
                }
                if killed {
                    lines.lock().unwrap().push(line);
                }
            })
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
    Arc::try_unwrap(lines).unwrap().into_inner().unwrap()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let max_v: usize = args[1].parse().unwrap();
    let max_nodes: u64 = args[2].parse().unwrap();
    let threads: usize = args[3].parse().unwrap();
    let all = read(&args[0]);
    // Validation: a quotient never kills an Instance that has a set.
    let exists: Vec<Instance> = read(&args[0])
        .into_iter()
        .filter(|i| i.status == "exists" && i.v <= max_v)
        .collect();
    let n_exists = exists.len();
    let wrong = parallel(exists, threads, max_nodes, false);
    assert!(wrong.is_empty(), "contraction kills an Instance that exists: {wrong:?}");
    let n32 = all.iter().find(|i| i.id == "N32").unwrap();
    assert!(run(n32, max_nodes).1.starts_with("KILL [1,5] [5]"), "N32 not killed at C5");
    eprintln!("validation passed: {n_exists} existing Instances survive, N32 dies at C5");
    let todo: Vec<Instance> =
        all.into_iter().filter(|i| i.status == "open" && i.v <= max_v).collect();
    parallel(todo, threads, max_nodes, true);
}
