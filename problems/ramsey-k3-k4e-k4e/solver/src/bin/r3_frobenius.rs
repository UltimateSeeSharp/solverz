//! E3: every Cayley 3-colouring of K₂₁ over the Frobenius group ℤ₇ ⋊ ℤ₃,
//! scored by `violations`. Elements (a, b), a ∈ ℤ₇, b ∈ ℤ₃, with
//! (a, b)(c, d) = (a + 2ᵇc, b + d); x and y get the colour of the class
//! {x⁻¹y, y⁻¹x}. With `--cyclic` the same enumeration runs over ℤ₂₁ instead
//! (validation: it must reproduce E1's 0 valid of 59,049).
//! Usage: `r3_frobenius [--cyclic] [--out <file>]`.

use ramsey_k3_k4e_k4e::{COLOURS, Colouring, violations};

/// Order of the group.
const N: usize = 21;
/// 2 has order 3 mod 7, so b ↦ (a ↦ 2ᵇa) is a ℤ₃-action on ℤ₇.
const TWIST: [usize; 3] = [1, 2, 4];

/// The group as a multiplication table on element indices 0..N, identity 0.
fn table(cyclic: bool) -> Vec<Vec<usize>> {
    let idx = |a: usize, b: usize| b * 7 + a;
    let mut t = vec![vec![0; N]; N];
    for x in 0..N {
        for y in 0..N {
            t[x][y] = if cyclic {
                (x + y) % N
            } else {
                let (a, b, c, d) = (x % 7, x / 7, y % 7, y / 7);
                idx((a + TWIST[b] * c) % 7, (b + d) % 3)
            };
        }
    }
    t
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cyclic = args.iter().any(|a| a == "--cyclic");
    let out = args.iter().position(|a| a == "--out").map(|i| args[i + 1].clone());
    let t = table(cyclic);
    let identity = (0..N).find(|&e| (0..N).all(|x| t[e][x] == x && t[x][e] == x)).expect("identity");
    let inv: Vec<usize> = (0..N).map(|x| (0..N).find(|&y| t[x][y] == identity).expect("inverse")).collect();
    // associativity, so the table is a group
    for x in 0..N {
        for y in 0..N {
            for z in 0..N {
                assert_eq!(t[t[x][y]][z], t[x][t[y][z]], "not associative");
            }
        }
    }
    // the Frobenius group is non-abelian; ℤ₂₁ is abelian
    let abelian = (0..N).all(|x| (0..N).all(|y| t[x][y] == t[y][x]));
    assert_eq!(abelian, cyclic, "wrong group");
    // classes: {g, g⁻¹} for g ≠ identity
    let mut class_of = vec![usize::MAX; N];
    let mut classes = 0;
    for g in 0..N {
        if g != identity && class_of[g] == usize::MAX {
            class_of[g] = classes;
            class_of[inv[g]] = classes;
            classes += 1;
        }
    }
    let total = (COLOURS as u64).pow(classes as u32);
    let (mut valid, mut best, mut best_c) = (0u64, usize::MAX, None);
    let mut colour_of = vec![0u8; classes];
    for code in 0..total {
        let mut x = code;
        for slot in colour_of.iter_mut() {
            *slot = (x % COLOURS as u64) as u8;
            x /= COLOURS as u64;
        }
        let mut c = Colouring::new(N);
        for p in 0..N {
            for q in p + 1..N {
                c.set(p, q, colour_of[class_of[t[inv[p]][q]]]);
            }
        }
        let score = violations(&c);
        if score == 0 {
            valid += 1;
        }
        if score < best {
            best = score;
            best_c = Some(c);
        }
    }
    let group = if cyclic { "Z21" } else { "Z7:Z3" };
    println!("group={group} classes={classes} colourings={total} valid={valid} best={best}");
    if let (Some(path), Some(c)) = (out, best_c) {
        std::fs::write(&path, c.to_text()).expect("write");
    }
}
