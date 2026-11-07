// SDS (v,k,lam) on Z_{m1} x ... with few zeros: zero set Z (0 in Z by translation), filter
// |S cap (S-g)| = lam mod 2 and >= |lam|, then signs by backtracking (first support element +1).
use std::env;
fn main() {
  let a: Vec<i64> = env::args().skip(1).map(|x| x.parse().unwrap()).collect();
  let (k, lam) = (a[0] as usize, a[1] as i32); let ms: Vec<usize> = a[2..].iter().map(|&x| x as usize).collect();
  let v: usize = ms.iter().product(); let z = v - k;
  let coords = |mut x: usize| { let mut c = vec![0; ms.len()]; for i in (0..ms.len()).rev() { c[i] = x % ms[i]; x /= ms[i]; } c };
  let index = |c: &Vec<usize>| { let mut x = 0; for i in 0..ms.len() { x = x * ms[i] + c[i]; } x };
  let mut add = vec![vec![0; v]; v];
  for x in 0..v { for y in 0..v { let (cx, cy) = (coords(x), coords(y));
    add[x][y] = index(&(0..ms.len()).map(|i| (cx[i] + cy[i]) % ms[i]).collect()); } }
  let (mut nz, mut nsupp, mut nsol) = (0u64, 0u64, 0u64);
  // enumerate zero sets containing 0
  let mut comb: Vec<usize> = (1..z).collect(); // indices in 1..v
  if z == 0 { comb.clear(); }
  loop {
    let mut zs = vec![false; v]; zs[0] = z > 0; for &c in &comb { zs[c] = true; }
    nz += 1;
    let supp: Vec<usize> = (0..v).filter(|&x| !zs[x]).collect();
    let ok = (1..v).all(|g| { let p = supp.iter().filter(|&&x| !zs[add[x][g]]).count() as i32; (p - lam).rem_euclid(2) == 0 && p >= lam.abs() });
    if ok { nsupp += 1;
      // signs backtracking over supp
      let mut d = vec![0i32; v]; let mut c = vec![0i32; v];
      // rem[i][g]: pairs (x, x+g) in supp not both among supp[0..i]
      let pos: Vec<usize> = { let mut p = vec![usize::MAX; v]; for (i, &x) in supp.iter().enumerate() { p[x] = i; } p };
      let mut rem = vec![vec![0i32; v]; k + 1];
      for i in 0..=k { for g in 1..v { rem[i][g] = supp.iter().filter(|&&x| { let y = add[x][g]; pos[y] != usize::MAX && (pos[x] >= i || pos[y] >= i) }).count() as i32; } }
      fn bt(i: usize, k: usize, v: usize, lam: i32, supp: &Vec<usize>, add: &Vec<Vec<usize>>, d: &mut Vec<i32>, c: &mut Vec<i32>, rem: &Vec<Vec<i32>>, nsol: &mut u64) {
        if i == k { *nsol += 1; return; }
        let x = supp[i];
        for &s in if i == 0 { &[1][..] } else { &[1, -1][..] } {
          d[x] = s; let mut ch = vec![];
          for g in 1..v { let y = add[x][g]; if d[y] != 0 { c[g] += s * d[y]; ch.push((g, s * d[y])); }
            // pair (y', x) with y' + g = x handled when g' = g from y' side: count via inverse below
          }
          for g in 1..v { if let Some(yp) = (0..v).find(|&y| add[y][g] == x) { if d[yp] != 0 && yp != x { c[g] += d[yp] * s; ch.push((g, d[yp] * s)); } } }
          if (1..v).all(|g| (lam - c[g]).abs() <= rem[i + 1][g]) { bt(i + 1, k, v, lam, supp, add, d, c, rem, nsol); }
          for (g, p) in ch { c[g] -= p; } d[x] = 0;
        }
      }
      bt(0, k, v, lam, &supp, &add, &mut d, &mut c, &rem, &mut nsol);
    }
    // next combination of z-1 from 1..v-1
    if z <= 1 { break; }
    let r = z - 1; let mut i = r; let mut done = true;
    while i > 0 { i -= 1; if comb[i] < v - r + i { comb[i] += 1; for j in i + 1..r { comb[j] = comb[j - 1] + 1; } done = false; break; } }
    if done { break; }
  }
  println!("group {:?} k={} lam={} zero_sets={} parity_ok={} sds(D at first support = +1)={}", ms, k, lam, nz, nsupp, nsol);
}
