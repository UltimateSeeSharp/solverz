//! R(K₃, K₄−e, K₄−e) solver: scores 3-colourings of Kₙ by their forbidden
//! subgraphs, mirroring Lean's `Checks` (and so `Valid`), and extends them.

pub mod anneal;
pub mod block;
pub mod sat;

use std::fs;
use std::path::Path;

/// The colour whose class must have no triangle (Lean 0; objects files 1).
pub const TRIANGLE_FREE: u8 = 0;
/// The colours whose classes must have no K₄−e (Lean 1, 2; objects files 2, 3).
pub const K4E_FREE: [u8; 2] = [1, 2];
/// Number of colours.
pub const COLOURS: u8 = 3;
/// A 4-point set holds a K₄−e in a colour when this many of its 6 pairs have it.
pub(crate) const K4E_EDGES: usize = 5;
/// Objects files write colour `c` as digit `c + FILE_OFFSET`, the diagonal as 0.
const FILE_OFFSET: u8 = 1;

/// A colouring of the pairs of n points, stored as a symmetric matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Colouring {
    n: usize,
    m: Vec<u8>,
}

impl Colouring {
    /// n points, every pair in `TRIANGLE_FREE`.
    pub fn new(n: usize) -> Self {
        Self { n, m: vec![TRIANGLE_FREE; n * n] }
    }

    pub fn n(&self) -> usize {
        self.n
    }

    pub fn get(&self, i: usize, j: usize) -> u8 {
        self.m[i * self.n + j]
    }

    pub fn set(&mut self, i: usize, j: usize, colour: u8) {
        self.m[i * self.n + j] = colour;
        self.m[j * self.n + i] = colour;
    }

    /// Parses the objects file format (see `objects/_objects.md`).
    pub fn parse(text: &str) -> Result<Self, String> {
        let rows: Vec<&str> = text.split_whitespace().collect();
        let n = rows.len();
        let mut c = Self::new(n);
        for (i, row) in rows.iter().enumerate() {
            let digits: Vec<u8> = row.bytes().map(|b| b.wrapping_sub(b'0')).collect();
            if digits.len() != n {
                return Err(format!("row {i} has {} entries, expected {n}", digits.len()));
            }
            for (j, &d) in digits.iter().enumerate() {
                if i == j {
                    if d != 0 {
                        return Err(format!("diagonal entry {i} is {d}, expected 0"));
                    }
                } else if (FILE_OFFSET..FILE_OFFSET + COLOURS).contains(&d) {
                    c.m[i * n + j] = d - FILE_OFFSET;
                } else {
                    return Err(format!("entry {i},{j} is {d}, not a colour"));
                }
            }
        }
        for i in 0..n {
            for j in 0..i {
                if c.get(i, j) != c.get(j, i) {
                    return Err(format!("entries {i},{j} and {j},{i} differ"));
                }
            }
        }
        Ok(c)
    }

    pub fn read(path: &Path) -> Result<Self, String> {
        let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::parse(&text)
    }

    /// The objects file format.
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        for i in 0..self.n {
            for j in 0..self.n {
                let digit = if i == j { 0 } else { self.get(i, j) + FILE_OFFSET };
                out.push((b'0' + digit) as char);
            }
            out.push('\n');
        }
        out
    }

    /// The colouring with point `v` removed; later points move down by one.
    pub fn without(&self, v: usize) -> Self {
        let keep: Vec<usize> = (0..self.n).filter(|&i| i != v).collect();
        let mut c = Self::new(keep.len());
        for (a, &i) in keep.iter().enumerate() {
            for (b, &j) in keep.iter().enumerate() {
                c.m[a * c.n + b] = self.get(i, j);
            }
        }
        c
    }

    /// The colouring with a new last point whose pair with point `i` has colour `row[i]`.
    pub fn with_point(&self, row: &[u8]) -> Self {
        assert_eq!(row.len(), self.n, "one colour per existing point");
        let mut c = Self::new(self.n + 1);
        for i in 0..self.n {
            for j in 0..self.n {
                c.m[i * c.n + j] = self.get(i, j);
            }
            c.set(i, self.n, row[i]);
        }
        c
    }
}

/// Colour-`TRIANGLE_FREE` triangles plus 4-point sets with a K₄−e in a
/// `K4E_FREE` colour; 0 iff the colouring satisfies Lean's `Valid`.
pub fn violations(c: &Colouring) -> usize {
    let n = c.n();
    let mut count = 0;
    for a in 0..n {
        for b in a + 1..n {
            for d in b + 1..n {
                let tri = [c.get(a, b), c.get(a, d), c.get(b, d)];
                if tri.iter().all(|&x| x == TRIANGLE_FREE) {
                    count += 1;
                }
                for e in d + 1..n {
                    let pairs = [
                        c.get(a, b),
                        c.get(a, d),
                        c.get(a, e),
                        c.get(b, d),
                        c.get(b, e),
                        c.get(d, e),
                    ];
                    for k in K4E_FREE {
                        if pairs.iter().filter(|&&x| x == k).count() >= K4E_EDGES {
                            count += 1;
                        }
                    }
                }
            }
        }
    }
    count
}

/// Every colour row for a new point that keeps a valid `c` valid.
pub fn extensions(c: &Colouring) -> Vec<Vec<u8>> {
    extensions_with_depth(c).0
}

/// `extensions`, plus how many of the new point's pairs the deepest partial
/// row coloured without a violation (`c.n()` when an extension exists).
pub fn extensions_with_depth(c: &Colouring) -> (Vec<Vec<u8>>, usize) {
    let mut found = Vec::new();
    let mut row = Vec::with_capacity(c.n());
    let mut depth = 0;
    extend(c, &mut row, &mut found, &mut depth);
    (found, depth)
}

/// Backtracking: `row` colours the new point's pairs with points `0..row.len()`.
fn extend(c: &Colouring, row: &mut Vec<u8>, found: &mut Vec<Vec<u8>>, depth: &mut usize) {
    *depth = (*depth).max(row.len());
    if row.len() == c.n() {
        found.push(row.clone());
        return;
    }
    for colour in 0..COLOURS {
        row.push(colour);
        if new_point_ok(c, row) {
            extend(c, row, found, depth);
        }
        row.pop();
    }
}

/// No violation uses the new point x and the latest point v = row.len() − 1.
fn new_point_ok(c: &Colouring, row: &[u8]) -> bool {
    let v = row.len() - 1;
    for u in 0..v {
        if row[u] == TRIANGLE_FREE && row[v] == TRIANGLE_FREE && c.get(u, v) == TRIANGLE_FREE {
            return false;
        }
        for w in u + 1..v {
            let pairs = [row[u], row[w], row[v], c.get(u, w), c.get(u, v), c.get(w, v)];
            for k in K4E_FREE {
                if pairs.iter().filter(|&&x| x == k).count() >= K4E_EDGES {
                    return false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    const O1: &str = include_str!("../../objects/O1.txt");

    fn o1() -> Colouring {
        Colouring::parse(O1).expect("O1 parses")
    }

    #[test]
    fn o1_is_valid() {
        let c = o1();
        assert_eq!(c.n(), 20);
        assert_eq!(violations(&c), 0);
    }

    #[test]
    fn file_format_round_trips() {
        assert_eq!(o1().to_text(), O1.replace("\r\n", "\n"));
    }

    #[test]
    fn broken_copies_are_rejected() {
        let mut triangle = o1();
        triangle.set(0, 1, TRIANGLE_FREE);
        assert!(violations(&triangle) > 0);
        let mut k4 = Colouring::new(4);
        for i in 0..4 {
            for j in i + 1..4 {
                k4.set(i, j, K4E_FREE[0]);
            }
        }
        assert_eq!(violations(&k4), 1);
    }

    #[test]
    fn o1_has_no_one_point_extension() {
        assert!(extensions(&o1()).is_empty());
    }

    #[test]
    fn o1_minus_a_point_has_two_extensions_including_itself() {
        let c = o1();
        for v in 0..c.n() {
            let smaller = c.without(v);
            let found = extensions(&smaller);
            assert_eq!(found.len(), 2, "point {v}");
            for row in &found {
                assert_eq!(violations(&smaller.with_point(row)), 0);
            }
            let removed: Vec<u8> = (0..c.n()).filter(|&i| i != v).map(|i| c.get(v, i)).collect();
            assert!(found.contains(&removed), "point {v}");
        }
    }
}
