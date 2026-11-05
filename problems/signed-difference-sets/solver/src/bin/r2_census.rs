//! R2: census of small cases. For every abelian group of order 2 ≤ v ≤ V and every (k, λ)
//! passing F1 with 2 ≤ k ≤ v, run P1 until the first set or exhaustion, capped per case.
//! Usage: `r2_census <V> <max_nodes>`; CSV on stdout: v,group,k,lambda,result,nodes
//! with result `yes` (a set found), `no` (exhausted) or `cut` (cap reached).

use signed_difference_sets::{abelian_groups, admissible_params, search_capped, Group};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let max_v: usize = args[0].parse().unwrap();
    let max_nodes: u64 = args[1].parse().unwrap();
    println!("v,group,k,lambda,result,nodes");
    for v in 2..=max_v {
        for shape in abelian_groups(v) {
            let group = Group::new(&shape);
            let name = shape.iter().map(|m| m.to_string()).collect::<Vec<_>>().join("x");
            for (k, lam) in admissible_params(v).into_iter().filter(|&(k, _)| k >= 2) {
                let out = search_capped(&group, k, lam, 1, max_nodes).expect("F1 holds");
                let result = if !out.solutions.is_empty() {
                    "yes"
                } else if out.nodes > max_nodes {
                    "cut"
                } else {
                    "no"
                };
                println!("{v},{name},{k},{lam},{result},{}", out.nodes);
            }
        }
    }
}
