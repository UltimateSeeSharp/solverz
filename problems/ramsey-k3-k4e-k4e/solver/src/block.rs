//! Block-circulant colourings of Kₙ, n = rings·m: point (r, i), r a ring,
//! i ∈ ℤₘ; the pair (r, i)(s, j) is coloured by its class (r, s, j − i), with
//! i − j identified for r = s. Backtracking over the classes, colours 1 and
//! 2 swapped away (the first class not coloured 0 takes colour 1).

use crate::{COLOURS, Colouring, K4E_EDGES, K4E_FREE, TRIANGLE_FREE};
use std::collections::HashSet;

pub struct Classes {
    pub m: usize,
    pub rings: usize,
    /// class id of the pair of points p, q (points numbered r·m + i).
    of_pair: Vec<usize>,
    pub count: usize,
}

impl Classes {
    pub fn new(m: usize, rings: usize) -> Self {
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

    pub fn n(&self) -> usize {
        self.m * self.rings
    }

    pub fn class(&self, p: usize, q: usize) -> usize {
        self.of_pair[p * self.n() + q]
    }

    pub fn colouring(&self, colour_of: &[u8]) -> Colouring {
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
pub struct Constraints {
    pub triangles: Vec<[usize; 3]>,
    pub quads: Vec<[usize; 6]>,
}

pub fn constraints(cl: &Classes) -> Constraints {
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

/// Backtracking over the classes; `on_valid` sees every valid assignment
/// (up to the 1 ↔ 2 swap) and returns false to stop the search.
pub struct Search<'a> {
    /// constraints whose largest class is the index.
    tri_at: Vec<Vec<&'a [usize; 3]>>,
    quad_at: Vec<Vec<&'a [usize; 6]>>,
    colour_of: Vec<u8>,
    pub found: u64,
    pub nodes: u64,
    stopped: bool,
}

impl<'a> Search<'a> {
    pub fn new(count: usize, cons: &'a Constraints) -> Self {
        let mut tri_at = vec![Vec::new(); count];
        let mut quad_at = vec![Vec::new(); count];
        for t in &cons.triangles {
            tri_at[t[2]].push(t);
        }
        for q in &cons.quads {
            quad_at[q[5]].push(q);
        }
        Self { tri_at, quad_at, colour_of: vec![0; count], found: 0, nodes: 0, stopped: false }
    }

    pub fn run(&mut self, on_valid: &mut dyn FnMut(&[u8]) -> bool) {
        self.visit(0, false, on_valid);
    }

    fn visit(&mut self, x: usize, seen_nonzero: bool, on_valid: &mut dyn FnMut(&[u8]) -> bool) {
        if self.stopped {
            return;
        }
        self.nodes += 1;
        if x == self.colour_of.len() {
            self.found += 1;
            self.stopped = !on_valid(&self.colour_of);
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
                self.visit(x + 1, seen_nonzero || colour != TRIANGLE_FREE, on_valid);
            }
        }
    }
}
