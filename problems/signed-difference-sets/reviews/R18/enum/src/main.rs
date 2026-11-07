// All SDS on Z_{m1} x ... (one translate with D(0)=+1, up to sign), per (k, lam) with k + lam(v-1) a square.
// For each found set: Gaussian character values on G/4G checked (norm n, real chars +-m, conj pairing,
// sum of real parts = N a0). Prints "k lam s count viol".
use std::env;
struct S { v: usize, add: Vec<Vec<usize>>, k: i32, lam: i32, d: Vec<i32>, c: Vec<i32>,
  rem: Vec<Vec<i32>>, // rem[pos][g]: pairs (x, x+g) with max(x, x+g) >= pos
  neg: Vec<usize>, cnt: u64, viol: u64, chars: Vec<Vec<u8>>, real: Vec<bool>, negc: Vec<usize>, ker: Vec<bool>, n: i32 }
impl S {
  fn check(&mut self) {
    let v = self.v; let nch = self.chars.len();
    let mut a = vec![0i32; nch]; let mut b = vec![0i32; nch];
    for ci in 0..nch { for x in 0..v { let dx = self.d[x]; if dx == 0 { continue; }
      match self.chars[ci][x] { 0 => a[ci] += dx, 1 => b[ci] += dx, 2 => a[ci] -= dx, _ => b[ci] -= dx } } }
    let m = (self.n as f64).sqrt().round() as i32;
    let mut bad = false; let mut tot = 0i32;
    for ci in 0..nch { tot += a[ci];
      if ci > 0 && a[ci]*a[ci] + b[ci]*b[ci] != self.n { bad = true; }
      if ci > 0 && self.real[ci] && (b[ci] != 0 || (a[ci] != m && a[ci] != -m)) { bad = true; }
      let j = self.negc[ci]; if a[j] != a[ci] || b[j] != -b[ci] { bad = true; } }
    let a0: i32 = (0..v).filter(|&x| self.ker[x]).map(|x| self.d[x]).sum();
    if tot != nch as i32 * a0 { bad = true; }
    if bad { self.viol += 1; }
  }
  fn go(&mut self, pos: usize, nz: i32) {
    let v = self.v;
    if pos == v { if nz == self.k { self.cnt += 1; self.check(); } return; }
    if nz + ((v - pos) as i32) < self.k { return; }
    let opts: &[i32] = if pos == 0 { &[1] } else { &[0, 1, -1] };
    for &val in opts.to_vec().iter() {
      if val != 0 && nz == self.k { continue; }
      self.d[pos] = val;
      // update c[g] for pairs whose max index is pos: (x, pos) with x < pos, g = pos - x and (pos, x): g = x - pos
      let mut changed: Vec<(usize, i32)> = Vec::new();
      if val != 0 { for g in 1..v { let y = self.add[pos][g]; // y = pos + g
          if y < pos && self.d[y] != 0 { // pair (pos, pos+g) both assigned now; also (y, y + (-g)) counted under -g
            let p = val * self.d[y]; self.c[g] += p; changed.push((g, p)); } }
      }
      // pairs (x, x+g) with x+g = pos and x < pos: x = pos - g, i.e. y=add[pos][g] gives pos+g; need pos-g
      if val != 0 { for g in 1..v { let x = self.add[pos][self.neg[g]]; if x < pos && self.d[x] != 0 {
            let p = self.d[x] * val; self.c[g] += p; changed.push((g, p)); } } }
      let mut ok = true;
      for g in 1..v { if (self.lam - self.c[g]).abs() > self.rem[pos + 1][g] { ok = false; break; } }
      if ok { self.go(pos + 1, nz + (val != 0) as i32); }
      for (g, p) in changed { self.c[g] -= p; }
      self.d[pos] = 0;
    }
  }
}
fn main() {
  let ms: Vec<usize> = env::args().skip(1).map(|a| a.parse().unwrap()).collect();
  let v: usize = ms.iter().product();
  let coords = |mut x: usize| -> Vec<usize> { let mut c = vec![0; ms.len()]; for i in (0..ms.len()).rev() { c[i] = x % ms[i]; x /= ms[i]; } c };
  let index = |c: &Vec<usize>| -> usize { let mut x = 0; for i in 0..ms.len() { x = x * ms[i] + c[i]; } x };
  let mut add = vec![vec![0; v]; v];
  for x in 0..v { for y in 0..v { let (cx, cy) = (coords(x), coords(y));
    let cz: Vec<usize> = (0..ms.len()).map(|i| (cx[i] + cy[i]) % ms[i]).collect(); add[x][y] = index(&cz); } }
  // characters of G/4G: exponent e_i * c_i * x_i mod 4
  let e: Vec<usize> = ms.iter().map(|&m| if m % 4 == 0 { 1 } else if m % 2 == 0 { 2 } else { 0 }).collect();
  let rng: Vec<usize> = e.iter().map(|&ei| if ei == 1 { 4 } else if ei == 2 { 2 } else { 1 }).collect();
  let nch: usize = rng.iter().product();
  let mut chars = vec![]; let mut real = vec![]; let mut cvecs = vec![];
  for t in 0..nch { let mut c = vec![0; ms.len()]; let mut u = t; for i in (0..ms.len()).rev() { c[i] = u % rng[i]; u /= rng[i]; }
    let row: Vec<u8> = (0..v).map(|x| { let cx = coords(x); ((0..ms.len()).map(|i| e[i] * c[i] * cx[i]).sum::<usize>() % 4) as u8 }).collect();
    real.push((0..ms.len()).all(|i| (e[i] * c[i] * 2) % 4 == 0)); chars.push(row); cvecs.push(c); }
  let negc: Vec<usize> = cvecs.iter().map(|c| { let nc: Vec<usize> = (0..ms.len()).map(|i| (rng[i] - c[i]) % rng[i]).collect();
    cvecs.iter().position(|d| *d == nc).unwrap() }).collect();
  let ker: Vec<bool> = (0..v).map(|x| { let cx = coords(x); (0..ms.len()).all(|i| rng[i] == 1 || cx[i] % rng[i] == 0) }).collect();
  let neg: Vec<usize> = (0..v).map(|g| (0..v).find(|&y| add[g][y] == 0).unwrap()).collect();
  // rem[pos][g]
  let mut rem = vec![vec![0i32; v]; v + 1];
  for pos in 0..=v { for g in 1..v { rem[pos][g] = (0..v).filter(|&x| x.max(add[x][g]) >= pos).count() as i32; } }
  println!("group {:?} v={} chars={} real={}", ms, v, nch, real.iter().filter(|&&r| r).count());
  for k in 1..=v as i32 { for lam in -(k as i32)..=k {
    let s2 = k + lam * (v as i32 - 1); if s2 < 0 { continue; } let s = (s2 as f64).sqrt().round() as i32; if s * s != s2 { continue; }
    let mut st = S { v, add: add.clone(), k, lam, d: vec![0; v], c: vec![0; v], rem: rem.clone(), neg: neg.clone(), cnt: 0, viol: 0,
      chars: chars.clone(), real: real.clone(), negc: negc.clone(), ker: ker.clone(), n: k - lam };
    st.go(0, 0);
    if st.cnt > 0 { println!("{} {} {} {} {}", k, lam, s, st.cnt, st.viol); } } }
}
