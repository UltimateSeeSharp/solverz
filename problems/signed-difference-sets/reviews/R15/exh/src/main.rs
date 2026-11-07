//! Exhaustive SDS search on a group Z_f1 x ... x Z_ft (args: factors). D(0) = +1 fixed
//! (translation, negation). For every SDS: check chi(D)^2 = n for each real character, the
//! h = 0 identity, and whether C17's closed form fires at r = R. Prints a summary per (k, lam).
use std::collections::BTreeMap;
fn v2(x: i64, cap: u32) -> u32 { if x == 0 { return cap; } let t = x.trailing_zeros(); t.min(cap) }
fn main() {
    let fs: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().unwrap()).collect();
    let v: usize = fs.iter().product();
    let coords: Vec<Vec<usize>> = (0..v).map(|mut i| { let mut c = vec![0; fs.len()];
        for j in (0..fs.len()).rev() { c[j] = i % fs[j]; i /= fs[j]; } c }).collect();
    let idx = |c: &Vec<usize>| c.iter().zip(&fs).fold(0, |a, (x, f)| a * f + x);
    let add: Vec<Vec<usize>> = (0..v).map(|x| (0..v).map(|g| { let c: Vec<usize> = coords[x].iter()
        .zip(&coords[g]).zip(&fs).map(|((a, b), f)| (a + b) % f).collect(); idx(&c) }).collect()).collect();
    let ev: Vec<usize> = (0..fs.len()).filter(|&i| fs[i] % 2 == 0).collect();
    let rr = ev.len() as u32;
    // real characters: chi_bits(x) = (-1)^(sum_i bit_i * x_{ev_i})
    let chis: Vec<Vec<i64>> = (0..(1usize << rr)).map(|b| (0..v).map(|x| {
        let p: usize = ev.iter().enumerate().map(|(j, &i)| ((b >> j) & 1) * coords[x][i]).sum();
        if p % 2 == 1 { -1 } else { 1 } }).collect()).collect();
    let h0: Vec<bool> = (0..v).map(|x| ev.iter().all(|&i| coords[x][i] % 2 == 0)).collect();
    let mut d = vec![0i8; v]; d[0] = 1;
    let mut ctrl = 0u64; // negative control: same test at r = R + 1 (not a quotient)
    let mut summary: BTreeMap<(i64, i64, i64), (u64, u64)> = BTreeMap::new(); // (k,lam,|s|) -> (count, fired)
    let mut bad_identity = 0u64;
    loop {
        // test
        let mut lam: Option<i64> = None; let mut ok = true;
        for g in 1..v {
            let a = &add; let mut c: i64 = 0;
            for x in 0..v { c += (d[x] as i64) * (d[a[x][g]] as i64); }
            match lam { None => lam = Some(c), Some(l) => if l != c { ok = false; break; } }
        }
        if ok {
            let lam = lam.unwrap_or(0);
            let k: i64 = d.iter().map(|&x| (x != 0) as i64).sum();
            let sp: i64 = d.iter().map(|&x| x as i64).sum();
            let n = k - lam;
            let mut fired = 0u64;
            if rr > 0 {
                let mut tot = 0i64;
                for (b, ch) in chis.iter().enumerate() {
                    let val: i64 = (0..v).map(|x| d[x] as i64 * ch[x]).sum();
                    if b > 0 && val * val != n { bad_identity += 1; }
                    tot += val;
                }
                let a0: i64 = (0..v).filter(|&x| h0[x]).map(|x| d[x] as i64).sum();
                if tot != (1i64 << rr) * a0 { bad_identity += 1; }
                let m = (n.max(0) as f64).sqrt().round() as i64;
                if m * m != n { bad_identity += 1; }
                if v2(sp.abs(), rr) != v2(m, rr) { fired = 1; }
                if v2(sp.abs(), rr + 1) != v2(m, rr + 1) { ctrl += 1; }
            }
            let e = summary.entry((k, lam, sp.abs())).or_insert((0, 0)); e.0 += 1; e.1 += fired;
        }
        // odometer over d[1..]
        let mut i = 1;
        loop {
            if i == v { 
                println!("group {:?} v={} R={} identity_violations={}", fs, v, rr, bad_identity);
                let mut fired_total = 0;
                for ((k, l, s), (c, f)) in &summary { println!("  k={} lam={} |s|={} sets={} fired={}", k, l, s, c, f); fired_total += f; }
                println!("  FIRED_TOTAL={} control_r_plus_1_fires={}", fired_total, ctrl);
                return;
            }
            d[i] = match d[i] { 0 => 1, 1 => -1, _ => 0 };
            if d[i] != 0 { break; }
            i += 1;
        }
    }
}
