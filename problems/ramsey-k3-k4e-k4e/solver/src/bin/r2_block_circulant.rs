//! R2: every block-circulant 3-colouring of Kₙ, n = rings·m: point (r, i),
//! r a ring, i ∈ ℤₘ; the pair (r, i)(s, j) is coloured by its class (r, s,
//! j − i), with i − j identified for r = s. Backtracking over the classes,
//! colours 1 and 2 swapped away (the first non-0 class takes colour 1).
//! Usage: `r2_block_circulant <m> <rings> [--brute] [--out <file>]`.
//! Prints the number of valid colourings up to the swap and writes the
//! first one to `--out`; `--brute` enumerates every assignment instead
//! (validation for small m).

use ramsey_k3_k4e_k4e::block::{Classes, Search, constraints};
use ramsey_k3_k4e_k4e::{COLOURS, K4E_FREE, TRIANGLE_FREE, violations};

/// Every assignment, scored on the full colouring; valid ones counted up to the swap.
fn brute(cl: &Classes) -> u64 {
    let total = (COLOURS as u64).pow(cl.count as u32);
    let mut colour_of = vec![0u8; cl.count];
    let mut valid = 0;
    for code in 0..total {
        let mut x = code;
        for slot in colour_of.iter_mut() {
            *slot = (x % COLOURS as u64) as u8;
            x /= COLOURS as u64;
        }
        let first_nonzero = colour_of.iter().find(|&&c| c != TRIANGLE_FREE);
        if first_nonzero == Some(&K4E_FREE[1]) {
            continue;
        }
        if violations(&cl.colouring(&colour_of)) == 0 {
            valid += 1;
        }
    }
    valid
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let m: usize = args[0].parse().expect("m");
    let rings: usize = args[1].parse().expect("rings");
    let out = args.iter().position(|a| a == "--out").map(|i| args[i + 1].clone());
    let cl = Classes::new(m, rings);
    if args.iter().any(|a| a == "--brute") {
        println!("m={m} rings={rings} classes={} brute valid={}", cl.count, brute(&cl));
        return;
    }
    let cons = constraints(&cl);
    let mut s = Search::new(cl.count, &cons);
    let mut first: Option<Vec<u8>> = None;
    s.run(&mut |a| {
        if first.is_none() {
            first = Some(a.to_vec());
        }
        true
    });
    println!(
        "m={m} rings={rings} classes={} triangles={} quads={} nodes={} valid={}",
        cl.count,
        cons.triangles.len(),
        cons.quads.len(),
        s.nodes,
        s.found
    );
    if let Some(first) = &first {
        let c = cl.colouring(first);
        assert_eq!(violations(&c), 0, "a found colouring must be valid");
        if let Some(path) = out {
            std::fs::write(&path, c.to_text()).expect("write");
            println!("first valid colouring written to {path}");
        }
    }
}
