//! R3: P1 on table cases read from a file, one `SDS(v,k,λ,[m1,…])` key per line (other text
//! ignored), stopping at the first set or after `max_nodes` nodes per case.
//! Usage: `r3_open_cases <file> <max_nodes>`; one line per case: key, yes/no/cut, nodes, set.

use signed_difference_sets::{search_capped, Group};
use std::time::Instant;

fn parse(line: &str) -> Option<(usize, i64, Vec<usize>, String)> {
    let start = line.find("SDS(")?;
    let end = start + line[start..].find(")")? + 1;
    let key = &line[start..end];
    let inner = &key[4..key.len() - 1];
    let (nums, shape) = inner.split_once(",[")?;
    let nums: Vec<i64> = nums.split(',').map(|x| x.parse().unwrap()).collect();
    let shape: Vec<usize> =
        shape.trim_end_matches(']').split(',').map(|x| x.parse().unwrap()).collect();
    assert_eq!(nums[0] as usize, shape.iter().product::<usize>(), "{key}: v ≠ |G|");
    Some((nums[1] as usize, nums[2], shape, key.to_string()))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let text = std::fs::read_to_string(&args[0]).unwrap();
    let max_nodes: u64 = args[1].parse().unwrap();
    for (k, lam, shape, key) in text.lines().filter_map(parse) {
        let group = Group::new(&shape);
        let t = Instant::now();
        let out = search_capped(&group, k, lam, 1, max_nodes).expect("F1 holds for table cases");
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
        println!("{key} {result} {} {:.1?} {set}", out.nodes, t.elapsed());
    }
}
