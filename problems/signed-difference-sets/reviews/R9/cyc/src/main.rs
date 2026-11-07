//! Search unions of cyclotomic classes of order N in GF(2^d) (d = 2m) for NL_n(r) PDS, n = 2^m.
//! Usage: cyc <d> <N> <t> <mode>   mode: all (every t-subset containing class 0) | frob (unions of
//! Frobenius orbits i -> 2i mod N, every size-t union). Prints each hit and a count.
use std::env;

fn gf_mul(mut a: u32, mut b: u32, modp: u32, d: u32) -> u32 {
    let mut r = 0;
    while b != 0 {
        if b & 1 != 0 { r ^= a; }
        b >>= 1; a <<= 1;
        if a >> d & 1 != 0 { a ^= modp; }
    }
    r
}

fn primitive_poly(d: u32) -> u32 {
    let q = 1u32 << d;
    for modp in (q + 1..2 * q).step_by(2) {
        let (mut x, mut ord) = (1u32, 0u32);
        loop { x = gf_mul(x, 2, modp, d); ord += 1; if x == 1 || ord > q { break; } }
        if x == 1 && ord == q - 1 { return modp; }
    }
    panic!("no primitive polynomial");
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let d: u32 = a[1].parse().unwrap();
    let nn: usize = a[2].parse().unwrap();
    let t: usize = a[3].parse().unwrap();
    let mode = a[4].as_str();
    let max_nodes: u64 = if a.len() > 5 { a[5].parse().unwrap() } else { u64::MAX };
    let q = 1u32 << d;
    let n = 1i64 << (d / 2);
    assert!((q as usize - 1) % nn == 0);
    let modp = primitive_poly(d);
    // exp table, trace
    let mut exp = vec![0u32; q as usize - 1];
    let mut x = 1u32;
    for i in 0..(q - 1) as usize { exp[i] = x; x = gf_mul(x, 2, modp, d); }
    let tr = |y: u32| -> u32 { let (mut s, mut z) = (0u32, y); for _ in 0..d { s ^= z; z = gf_mul(z, z, modp, d); } s };
    let mut eta = vec![0i64; nn];
    for i in 0..(q - 1) as usize {
        let v = tr(exp[i]);
        assert!(v <= 1);
        eta[i % nn] += if v == 0 { 1 } else { -1 };
    }
    let csize = ((q - 1) as i64) / nn as i64;
    let k = csize * t as i64;
    if k % (n + 1) != 0 { println!("k = {} not a multiple of n+1 = {}", k, n + 1); return; }
    let r = k / (n + 1);
    println!("GF(2^{}) mod {:#x}, N = {}, class size {}, t = {}, k = {}, target NL_{}({}): values {{{}, {}}}",
             d, modp, nn, csize, t, k, n, r, r, r - n);
    println!("Gauss periods: {:?}", eta);
    // rows[i][j] = eta[(i + j) mod N]
    let blocks: Vec<Vec<usize>> = match mode {
        "all" => (0..nn).map(|i| vec![i]).collect(),
        "frob" => {
            let mut seen = vec![false; nn];
            let mut bl = Vec::new();
            for i in 0..nn {
                if seen[i] { continue; }
                let mut orb = Vec::new();
                let mut j = i;
                while !seen[j] { seen[j] = true; orb.push(j); j = 2 * j % nn; }
                bl.push(orb);
            }
            bl
        }
        _ => panic!("mode"),
    };
    println!("blocks: {} (sizes {:?})", blocks.len(), blocks.iter().map(|b| b.len()).collect::<Vec<_>>());
    let brow: Vec<Vec<i64>> = blocks.iter().map(|b| (0..nn).map(|j| b.iter().map(|&i| eta[(i + j) % nn]).sum()).collect()).collect();
    let bsz: Vec<usize> = blocks.iter().map(|b| b.len()).collect();
    let nbk = blocks.len();
    let mut pos = vec![vec![0i64; nn]; nbk + 1];
    let mut neg = vec![vec![0i64; nn]; nbk + 1];
    for b in (0..nbk).rev() { for j in 0..nn { pos[b][j] = pos[b + 1][j] + brow[b][j].max(0); neg[b][j] = neg[b + 1][j] + brow[b][j].min(0); } }
    let mut sums = vec![0i64; nn];
    let mut chosen: Vec<usize> = Vec::new();
    let mut hits = 0u64;
    let mut nodes = 0u64;
    // in mode all, force block 0 (class 0) in
    let start_forced = mode == "all";
    if start_forced { for j in 0..nn { sums[j] += brow[0][j]; } chosen.push(0); }
    let first = if start_forced { 1 } else { 0 };
    let size0 = if start_forced { 1 } else { 0 };
    fn dfs(idx: usize, size: usize, t: usize, nb: usize, brow: &Vec<Vec<i64>>, bsz: &Vec<usize>, sums: &mut Vec<i64>,
           chosen: &mut Vec<usize>, r: i64, n: i64, hits: &mut u64, nodes: &mut u64, blocks: &Vec<Vec<usize>>, max_nodes: u64,
           pos: &Vec<Vec<i64>>, neg: &Vec<Vec<i64>>) {
        *nodes += 1;
        if *nodes > max_nodes { return; }
        if size < t {
            for j in 0..sums.len() { if sums[j] + pos[idx][j] < r - n || sums[j] + neg[idx][j] > r { return; } }
        }
        if size == t {
            if sums.iter().all(|&s| s == r || s == r - n) {
                *hits += 1;
                if *hits <= 20 {
                    let mut cl: Vec<usize> = chosen.iter().flat_map(|&b| blocks[b].clone()).collect();
                    cl.sort();
                    let na = sums.iter().filter(|&&s| s == r - n).count();
                    println!("HIT classes {:?} (#shifts with r-n: {})", cl, na);
                }
            }
            return;
        }
        for b in idx..nb {
            if size + bsz[b] > t { continue; }
            for j in 0..sums.len() { sums[j] += brow[b][j]; }
            chosen.push(b);
            dfs(b + 1, size + bsz[b], t, nb, brow, bsz, sums, chosen, r, n, hits, nodes, blocks, max_nodes, pos, neg);
            chosen.pop();
            for j in 0..sums.len() { sums[j] -= brow[b][j]; }
        }
    }
    dfs(first, size0, t, blocks.len(), &brow, &bsz, &mut sums, &mut chosen, r, n, &mut hits, &mut nodes, &blocks, max_nodes, &pos, &neg);
    if nodes > max_nodes { println!("ABORTED at node limit {}", max_nodes); }
    println!("done: {} hits, {} nodes", hits, nodes);
}
