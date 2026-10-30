//! R2: every block-circulant 3-colouring of Kₙ, n = rings·m: point (r, i),
//! r a ring, i ∈ ℤₘ; the pair (r, i)(s, j) is coloured by its class (r, s,
//! j − i), with i − j identified for r = s. Backtracking over the classes,
//! colours 1 and 2 swapped away (the first non-0 class takes colour 1).
//! Usage: `r2_block_circulant <m> <rings> [--brute] [--out <file>]`.
//! Prints the number of valid colourings up to the swap and writes the
//! first one to `--out`; `--brute` enumerates every assignment instead
//! (validation for small m).

use ramsey_k3_k4e_k4e::{COLOURS, Colouring, K4E_FREE, TRIANGLE_FREE, violations};
use std::collections::HashSet;

/// A 4-point set holds a K₄−e in a colour when this many of its 6 pairs have it.
const K4E_EDGES: usize = 5;

struct Classes {
    m: usize,
    rings: usize,
    /// class id of the pair of points p, q (points numbered r·m + i).
    of_pair: Vec<usize>,
    count: usize,
}

impl Classes {
    fn new(m: usize, rings: usize) -> Self {
        let n = m * rings;
        let mut ids = std::collections::HashMap::new();
        let mut of_pair = vec![usize::MAX; n * n];
        for p in 0..n {
            for q in 0..n {
                if p == q {
                    continue;
                }
                let (r, i, s, j) = (p / m, p % m, q / m, q % m);
                let key = if r == s {
                    let d = (j + m - i) % m;
                    (r, r, d.min(m - d))
                } else if r < s {
                    (r, s, (j + m - i) % m)
                } else {
                    (s, r, (i + m - j) % m)
                };
                let next = ids.len();
                of_pair[p * n + q] = *ids.entry(key).or_insert(next);
            }
        }
        Self { m, rings, count: ids.len(), of_pair }
    }

    fn n(&self) -> usize {
        self.m * self.rings
    }

    fn class(&self, p: usize, q: usize) -> usize {
        self.of_pair[p * self.n() + q]
    }

    fn colouring(&self, colour_of: &[u8]) -> Colouring {
        let n = self.n();
        let mut c = Colouring::new(n);
        for p in 0..n {
            for q in p + 1..n {
                c.set(p, q, colour_of[self.class(p, q)]);
            }
        }
        c
    }
}

/// Forbidden sets as class lists, one per orbit representative: every
/// orbit under ℤₘ meets a set containing a point (r, 0).
struct Constraints {
    triangles: Vec<[usize; 3]>,
    quads: Vec<[usize; 6]>,
}

fn constraints(cl: &Classes) -> Constraints {
    let n = cl.n();
    let anchors: Vec<usize> = (0..cl.rings).map(|r| r * cl.m).collect();
    let (mut tri, mut quad) = (HashSet::new(), HashSet::new());
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                let set = [a, b, c];
                if set.iter().any(|x| anchors.contains(x)) {
                    let mut t = [cl.class(a, b), cl.class(a, c), cl.class(b, c)];
                    t.sort();
                    tri.insert(t);
                }
                for d in c + 1..n {
                    if [a, b, c, d].iter().any(|x| anchors.contains(x)) {
                        let mut q = [
                            cl.class(a, b),
                            cl.class(a, c),
                            cl.class(a, d),
                            cl.class(b, c),
                            cl.class(b, d),
                            cl.class(c, d),
                        ];
                        q.sort();
                        quad.insert(q);
                    }
                }
            }
        }
    }
    Constraints { triangles: tri.into_iter().collect(), quads: quad.into_iter().collect() }
}

fn triangle_ok(t: &[usize; 3], colour_of: &[u8]) -> bool {
    !t.iter().all(|&x| colour_of[x] == TRIANGLE_FREE)
}

fn quad_ok(q: &[usize; 6], colour_of: &[u8]) -> bool {
    K4E_FREE.iter().all(|&k| q.iter().filter(|&&x| colour_of[x] == k).count() < K4E_EDGES)
}

struct Search<'a> {
    /// constraints whose largest class is the index.
    tri_at: Vec<Vec<&'a [usize; 3]>>,
    quad_at: Vec<Vec<&'a [usize; 6]>>,
    colour_of: Vec<u8>,
    found: u64,
    first: Option<Vec<u8>>,
    nodes: u64,
}

impl<'a> Search<'a> {
    fn new(count: usize, cons: &'a Constraints) -> Self {
        let mut tri_at = vec![Vec::new(); count];
        let mut quad_at = vec![Vec::new(); count];
        for t in &cons.triangles {
            tri_at[t[2]].push(t);
        }
        for q in &cons.quads {
            quad_at[q[5]].push(q);
        }
        Self { tri_at, quad_at, colour_of: vec![0; count], found: 0, first: None, nodes: 0 }
    }

    fn run(&mut self, x: usize, seen_nonzero: bool) {
        self.nodes += 1;
        if x == self.colour_of.len() {
            self.found += 1;
            if self.first.is_none() {
                self.first = Some(self.colour_of.clone());
            }
            return;
        }
        for colour in 0..COLOURS {
            if !seen_nonzero && colour == K4E_FREE[1] {
                continue;
            }
            self.colour_of[x] = colour;
            let ok = self.tri_at[x].iter().all(|t| triangle_ok(t, &self.colour_of))
                && self.quad_at[x].iter().all(|q| quad_ok(q, &self.colour_of));
            if ok {
                self.run(x + 1, seen_nonzero || colour != TRIANGLE_FREE);
            }
        }
    }
}

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
    s.run(0, false);
    println!(
        "m={m} rings={rings} classes={} triangles={} quads={} nodes={} valid={}",
        cl.count,
        cons.triangles.len(),
        cons.quads.len(),
        s.nodes,
        s.found
    );
    if let Some(first) = &s.first {
        let c = cl.colouring(first);
        assert_eq!(violations(&c), 0, "a found colouring must be valid");
        if let Some(path) = out {
            std::fs::write(&path, c.to_text()).expect("write");
            println!("first valid colouring written to {path}");
        }
    }
}
