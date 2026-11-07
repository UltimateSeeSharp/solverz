//! Full enumeration of IsSDS on Z_{m1} x ... x Z_{mr}: every k-subset support, every sign
//! pattern; no symmetry break, no square condition. Usage: brute <m1,m2,..> <k> <lam>
use std::env;
fn main() {
    let a: Vec<String> = env::args().skip(1).collect();
    let shape: Vec<usize> = a[0].split(',').map(|m| m.parse().unwrap()).collect();
    let k: u32 = a[1].parse().unwrap();
    let lam: i32 = a[2].parse().unwrap();
    let v: usize = shape.iter().product();
    assert!(v <= 31);
    // coords: mixed radix, last factor least significant
    let coords = |mut x: usize| { let mut c = vec![0; shape.len()]; for i in (0..shape.len()).rev() { c[i] = x % shape[i]; x /= shape[i]; } c };
    let index = |c: &Vec<usize>| { let mut x = 0; for i in 0..shape.len() { x = x * shape[i] + c[i]; } x };
    let mut add = vec![vec![0usize; v]; v];
    for x in 0..v { for g in 0..v {
        let (cx, cg) = (coords(x), coords(g));
        let s: Vec<usize> = (0..shape.len()).map(|i| (cx[i] + cg[i]) % shape[i]).collect();
        add[x][g] = index(&s);
    }}
    let full: u64 = 1u64 << v;
    let mut supp: u64 = (1u64 << k) - 1; // Gosper over k-subsets
    let (mut found, mut supports, mut patterns) = (0u64, 0u64, 0u64);
    let mut first: Option<Vec<i32>> = None;
    let mut d = vec![0i32; v];
    let mut pos = vec![0usize; k as usize];
    while supp < full {
        supports += 1;
        let mut j = 0; for x in 0..v { if supp >> x & 1 == 1 { pos[j] = x; j += 1; } }
        for signs in 0u64..(1u64 << k) {
            patterns += 1;
            for x in 0..v { d[x] = 0; }
            for (t, &x) in pos.iter().enumerate() { d[x] = if signs >> t & 1 == 1 { -1 } else { 1 }; }
            let mut ok = true;
            for g in 1..v {
                let mut c = 0; for x in 0..v { c += d[x] * d[add[x][g]]; }
                if c != lam { ok = false; break; }
            }
            if ok { found += 1; if first.is_none() { first = Some(d.clone()); } }
        }
        if supp == 0 { break; }
        let c = supp & supp.wrapping_neg(); let r = supp + c; supp = (((r ^ supp) >> 2) / c) | r;
    }
    println!("shape {:?} v={v} k={k} lam={lam}: supports {supports}, patterns {patterns}, SDS found {found}", shape);
    if let Some(f) = first { println!("first: {:?}", f); }
}
