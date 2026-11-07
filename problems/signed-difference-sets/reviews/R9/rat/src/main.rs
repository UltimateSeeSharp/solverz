//! Exhaustive search for NL_n(r) PDS (n^2, r(n+1), -n+r^2+3r, r^2+r) in an abelian group
//! C_{a1} x ... x C_{as}. An NL PDS has integer character values, so it is a union of rational
//! classes {t x : t odd... gcd(t, exp) = 1}; we choose classes (DFS) and test the character values
//! r, r - n on every rational class of characters. Usage: rat <r> <max_nodes> <a1> <a2> ...
//! Prints hits as element lists (first 3) and the hit count. A hit is re-verified by direct counting.
use std::env;

fn gcd(a: usize, b: usize) -> usize { if b == 0 { a } else { gcd(b, a % b) } }

fn main() {
    let a: Vec<String> = env::args().collect();
    let r_arg: i64 = a[1].parse().unwrap();
    let latin = r_arg < 0; // negative r: Latin square type L_n(|r|)
    let r = r_arg.abs();
    let max_nodes: u64 = a[2].parse().unwrap();
    let ords: Vec<usize> = a[3..].iter().map(|s| s.parse().unwrap()).collect();
    let v: usize = ords.iter().product();
    let n = (v as f64).sqrt().round() as i64;
    assert_eq!((n * n) as usize, v);
    let k = if latin { (r * (n - 1)) as usize } else { (r * (n + 1)) as usize };
    let (hi, lo) = if latin { (n - r, -r) } else { (r, r - n) };
    let expo = ords.iter().fold(1, |x, &y| x / gcd(x, y) * y);
    let dec = |mut x: usize| -> Vec<usize> { let mut c = vec![0; ords.len()]; for i in (0..ords.len()).rev() { c[i] = x % ords[i]; x /= ords[i]; } c };
    let enc = |c: &Vec<usize>| -> usize { let mut x = 0; for i in 0..ords.len() { x = x * ords[i] + c[i] % ords[i]; } x };
    let units: Vec<usize> = (1..expo).filter(|&t| gcd(t, expo) == 1).collect();
    let mut cls = vec![usize::MAX; v];
    let mut classes: Vec<Vec<usize>> = Vec::new();
    for x in 1..v {
        if cls[x] != usize::MAX { continue; }
        let c = dec(x);
        let mut orb: Vec<usize> = units.iter().map(|&t| enc(&c.iter().map(|&ci| ci * t).collect())).collect();
        orb.sort(); orb.dedup();
        for &y in &orb { cls[y] = classes.len(); }
        classes.push(orb);
    }
    let nc = classes.len();
    // character class reps: characters indexed like elements (a . x / ord), same classes
    let reps: Vec<usize> = classes.iter().map(|c| c[0]).collect();
    let mut rows = vec![vec![0i64; nc]; nc]; // rows[class][charclass]
    for (ci, c) in classes.iter().enumerate() {
        for (j, &ch) in reps.iter().enumerate() {
            let av = dec(ch);
            let mut s = 0f64;
            for &x in c {
                let xv = dec(x);
                let mut ph = 0f64;
                for i in 0..ords.len() { ph += (av[i] * xv[i]) as f64 / ords[i] as f64; }
                s += (2.0 * std::f64::consts::PI * ph).cos();
            }
            let si = s.round();
            assert!((s - si).abs() < 1e-6);
            rows[ci][j] = si as i64;
        }
    }
    let sz: Vec<usize> = classes.iter().map(|c| c.len()).collect();
    println!("group {:?}: v = {}, n = {}, {}_{}({}) k = {}, values {{{}, {}}}, {} rational classes (sizes histogram {:?})",
             ords, v, n, if latin { "L" } else { "NL" }, n, r, k, hi, lo, nc,
             { let mut h = std::collections::BTreeMap::new(); for &s in &sz { *h.entry(s).or_insert(0) += 1; } h });
    // order classes by size descending for better pruning
    let mut order: Vec<usize> = (0..nc).collect();
    order.sort_by(|&x, &y| sz[y].cmp(&sz[x]));
    struct St<'a> { rows: &'a Vec<Vec<i64>>, sz: &'a Vec<usize>, order: &'a Vec<usize>, k: usize, lo: i64, hi: i64,
                    sums: Vec<i64>, chosen: Vec<usize>, hits: u64, nodes: u64, max_nodes: u64, out: Vec<Vec<usize>>,
                    suffix: Vec<usize>, pos: Vec<Vec<i64>>, neg: Vec<Vec<i64>> }
    fn dfs(st: &mut St, idx: usize, size: usize) {
        st.nodes += 1;
        if st.nodes > st.max_nodes { return; }
        let rem = (st.k - size) as i64;
        // prune: each remaining element contributes in [-1, 1] to every character sum
        for &s in st.sums.iter() { if s - rem > st.hi || s + rem < st.lo { return; } }
        if idx < st.order.len() && size < st.k {
            let (pp, nn_) = (&st.pos[idx], &st.neg[idx]);
            for j in 0..st.sums.len() { if st.sums[j] + pp[j] < st.lo || st.sums[j] + nn_[j] > st.hi { return; } }
        }
        if size == st.k {
            if st.sums.iter().all(|&s| s == st.hi || s == st.lo) { st.hits += 1; if st.out.len() < 3 { st.out.push(st.chosen.clone()); } }
            return;
        }
        if idx >= st.order.len() || st.suffix[idx] < st.k - size { return; }
        for p in idx..st.order.len() {
            let c = st.order[p];
            if size + st.sz[c] > st.k { continue; }
            if st.suffix[p] < st.k - size { break; }
            for j in 0..st.sums.len() { st.sums[j] += st.rows[c][j]; }
            st.chosen.push(c);
            dfs(st, p + 1, size + st.sz[c]);
            st.chosen.pop();
            for j in 0..st.sums.len() { st.sums[j] -= st.rows[c][j]; }
            if st.nodes > st.max_nodes { return; }
        }
    }
    let mut suffix = vec![0usize; nc + 1];
    for p in (0..nc).rev() { suffix[p] = suffix[p + 1] + sz[order[p]]; }
    let mut pos = vec![vec![0i64; nc]; nc + 1];
    let mut neg = vec![vec![0i64; nc]; nc + 1];
    for p in (0..nc).rev() { for j in 0..nc { pos[p][j] = pos[p + 1][j] + rows[order[p]][j].max(0); neg[p][j] = neg[p + 1][j] + rows[order[p]][j].min(0); } }
    let mut st = St { rows: &rows, sz: &sz, order: &order, k, lo, hi, sums: vec![0; nc], chosen: vec![], hits: 0,
                      nodes: 0, max_nodes, out: vec![], suffix, pos, neg };
    dfs(&mut st, 0, 0);
    let aborted = st.nodes > max_nodes;
    // re-verify hits by direct difference counting
    for h in &st.out {
        let mut p = vec![false; v];
        for &c in h { for &x in &classes[c] { p[x] = true; } }
        let pl: Vec<usize> = (0..v).filter(|&x| p[x]).collect();
        let sub = |x: usize, y: usize| -> usize { let (cx, cy) = (dec(x), dec(y)); enc(&cx.iter().zip(cy.iter()).zip(ords.iter()).map(|((a, b), o)| (a + o - b) % o).collect()) };
        let mut cnt = vec![0i64; v];
        for &x in &pl { for &y in &pl { if x != y { cnt[sub(x, y)] += 1; } } }
        let (lam, mu) = if latin { (n + r * r - 3 * r, r * r - r) } else { (-n + r * r + 3 * r, r * r + r) };
        let ok = pl.len() == k && (1..v).all(|g| cnt[g] == if p[g] { lam } else { mu }) && !p[0]
                 && pl.iter().all(|&x| p[sub(0, x)]);
        let elems: Vec<Vec<usize>> = pl.iter().map(|&x| dec(x)).collect();
        println!("HIT (direct PDS check {}): {:?}", ok, elems);
    }
    println!("{}: {} hits, {} nodes", if aborted { "ABORTED" } else { "done" }, st.hits, st.nodes);
}
