//! R4: one-point extensions of valid block-circulant colourings (see
//! `block`), up to `limit` seeds in backtracking order. Per seed it runs
//! `extensions_with_depth`; it prints how many seeds were tried, how many
//! extend, and the deepest partial row, and writes the first extension
//! found to `--out`. Usage: `r4_extend_block <m> <rings> <limit> [--out <file>]`.

use ramsey_k3_k4e_k4e::block::{Classes, Search, constraints};
use ramsey_k3_k4e_k4e::{extensions_with_depth, violations};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let m: usize = args[0].parse().expect("m");
    let rings: usize = args[1].parse().expect("rings");
    let limit: u64 = args[2].parse().expect("limit");
    let out = args.iter().position(|a| a == "--out").map(|i| args[i + 1].clone());
    let cl = Classes::new(m, rings);
    let cons = constraints(&cl);
    let mut s = Search::new(cl.count, &cons);
    let (mut seeds, mut extendable, mut extensions, mut deepest) = (0u64, 0u64, 0u64, 0usize);
    let mut answer = None;
    s.run(&mut |a| {
        let seed = cl.colouring(a);
        let (found, depth) = extensions_with_depth(&seed);
        seeds += 1;
        deepest = deepest.max(depth);
        if !found.is_empty() {
            extendable += 1;
            extensions += found.len() as u64;
            if answer.is_none() {
                let c = seed.with_point(&found[0]);
                assert_eq!(violations(&c), 0, "an extension must be valid");
                answer = Some(c);
            }
        }
        seeds < limit
    });
    println!(
        "m={m} rings={rings} n={} seeds={seeds} extendable={extendable} extensions={extensions} deepest={deepest} search_complete={}",
        cl.n(),
        seeds < limit
    );
    if let (Some(path), Some(c)) = (out, answer) {
        std::fs::write(&path, c.to_text()).expect("write");
        println!("answer written to {path}");
    }
}
