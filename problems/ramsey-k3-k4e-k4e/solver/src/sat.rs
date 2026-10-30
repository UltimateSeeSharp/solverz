//! CNF encoding of `Valid` on Kₙ for an external SAT solver: variable
//! `var(i, j, c)` says pair ij has colour c; clauses give each pair exactly
//! one colour, forbid colour-`TRIANGLE_FREE` triangles, and forbid any 5
//! pairs of a 4-point set sharing a `K4E_FREE` colour. A cube adds unit
//! clauses fixing point 0's row.

use crate::{COLOURS, Colouring, K4E_FREE, TRIANGLE_FREE};
use std::fmt::Write;

/// DIMACS variable (from 1) for "pair ij, i ≠ j, has colour c".
pub fn var(n: usize, i: usize, j: usize, c: u8) -> i64 {
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    let pair = a * n - a * (a + 1) / 2 + (b - a - 1);
    (pair * COLOURS as usize + c as usize + 1) as i64
}

/// The clauses of `Valid` on Kₙ.
pub fn clauses(n: usize) -> Vec<Vec<i64>> {
    let mut cls = Vec::new();
    for i in 0..n {
        for j in i + 1..n {
            cls.push((0..COLOURS).map(|c| var(n, i, j, c)).collect());
            for c in 0..COLOURS {
                for d in c + 1..COLOURS {
                    cls.push(vec![-var(n, i, j, c), -var(n, i, j, d)]);
                }
            }
        }
    }
    for a in 0..n {
        for b in a + 1..n {
            for d in b + 1..n {
                let tri = [(a, b), (a, d), (b, d)];
                cls.push(tri.iter().map(|&(x, y)| -var(n, x, y, TRIANGLE_FREE)).collect());
                for e in d + 1..n {
                    let quad = [(a, b), (a, d), (a, e), (b, d), (b, e), (d, e)];
                    for k in K4E_FREE {
                        for skip in 0..quad.len() {
                            cls.push(
                                quad.iter()
                                    .enumerate()
                                    .filter(|&(p, _)| p != skip)
                                    .map(|(_, &(x, y))| -var(n, x, y, k))
                                    .collect(),
                            );
                        }
                    }
                }
            }
        }
    }
    cls
}

/// Unit clauses colouring point 0's pairs: `row[i − 1]` for pair (0, i).
pub fn cube(n: usize, row: &[u8]) -> Vec<Vec<i64>> {
    row.iter().enumerate().map(|(k, &c)| vec![var(n, 0, k + 1, c)]).collect()
}

pub fn dimacs(vars: usize, cls: &[Vec<i64>]) -> String {
    let mut s = format!("p cnf {vars} {}\n", cls.len());
    for c in cls {
        for l in c {
            write!(s, "{l} ").expect("string write");
        }
        s.push_str("0\n");
    }
    s
}

/// Number of variables for Kₙ.
pub fn vars(n: usize) -> usize {
    n * (n - 1) / 2 * COLOURS as usize
}

/// The colouring a model (the true literals) describes.
pub fn decode(n: usize, true_lits: &std::collections::HashSet<i64>) -> Colouring {
    let mut c = Colouring::new(n);
    for i in 0..n {
        for j in i + 1..n {
            let colour = (0..COLOURS).find(|&k| true_lits.contains(&var(n, i, j, k))).expect("a colour");
            c.set(i, j, colour);
        }
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::violations;

    #[test]
    fn variables_are_distinct_and_in_range() {
        let n = 9;
        let mut seen = std::collections::HashSet::new();
        for i in 0..n {
            for j in i + 1..n {
                for c in 0..COLOURS {
                    let v = var(n, i, j, c);
                    assert!(v >= 1 && v as usize <= vars(n));
                    assert!(seen.insert(v));
                    assert_eq!(v, var(n, j, i, c));
                }
            }
        }
    }

    #[test]
    fn a_colouring_satisfies_the_clauses_iff_it_is_valid() {
        let mut rng = crate::anneal::Rng::new(3);
        let n = 8;
        let cls = clauses(n);
        let (mut valid, mut invalid) = (0, 0);
        for _ in 0..300 {
            let mut c = Colouring::new(n);
            for i in 0..n {
                for j in i + 1..n {
                    // few colour-0 pairs, so valid colourings occur
                    let x = rng.below(5);
                    c.set(i, j, if x == 0 { 0 } else { 1 + (x % 2) as u8 });
                }
            }
            let truth: std::collections::HashSet<i64> = (0..n)
                .flat_map(|i| (i + 1..n).map(move |j| (i, j)))
                .map(|(i, j)| var(n, i, j, c.get(i, j)))
                .collect();
            let sat = cls.iter().all(|cl| cl.iter().any(|&l| if l > 0 { truth.contains(&l) } else { !truth.contains(&-l) }));
            assert_eq!(sat, violations(&c) == 0);
            assert_eq!(decode(n, &truth), c);
            if sat { valid += 1 } else { invalid += 1 }
        }
        assert!(valid > 0 && invalid > 0, "both outcomes exercised: {valid} {invalid}");
    }
}
