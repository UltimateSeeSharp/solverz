//! Usage: e37_real_height_holes <k_min> <k_max>
//! C109: for every real h > 0, the tied mover on {h + x : x ∈ {0..2k} ∖ {o}} with o ≡ k (mod 2) draws. `Param` gives each
//! value exactly as a function of h on (0, ∞); prints every draw-parity hole whose function is not the constant draw,
//! and per k the number of breakpoints of the off-parity holes (where the sign flips).
//! First checks: C32 at p = 1 (offsets {0, 1}, the mover trailing by 1) wins exactly on (0, 1); C32 at p = 2 (the block
//! {0..3}, tied) draws on all of (0, ∞); C105's k = 2, o = 1 hole (off parity) is not the constant draw.

use catch_up::param::Param;

const DRAW: i8 = 0;

fn check() {
    let pair = Param::new(&[0, 1]).value(0b11, 0, 1);
    assert_eq!(pair.show(), "(0,1/1):W [1/1]:D (1/1,inf):D", "C32 at p = 1");
    assert_eq!(Param::new(&[0, 1, 2, 3]).tied().values(), vec![DRAW], "C32 at p = 2");
    assert_ne!(Param::new(&[0, 2, 3, 4]).tied().values(), vec![DRAW], "off-parity hole");
    println!("check: C32's pair wins on (0, 1) and draws from 1; {{0..3}} draws everywhere; {{0, 2, 3, 4}} does not");
}

fn main() {
    let a: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().expect("k_min k_max")).collect();
    assert_eq!(a.len(), 2, "usage: e37_real_height_holes <k_min> <k_max>");
    check();
    for k in a[0]..=a[1] {
        let (mut entries, mut bad, mut off_bps) = (0, 0, 0);
        for o in 0..=2 * k {
            let offs: Vec<i64> = (0..=2 * k).filter(|&x| x != o).collect();
            let f = Param::new(&offs).tied();
            if (o - k) % 2 == 0 {
                entries += 1;
                if f.values() != vec![DRAW] {
                    bad += 1;
                    println!("  k={k} o={o}: {}", f.show());
                }
            } else {
                off_bps += f.bps.len();
            }
        }
        println!("k={k}: {entries} draw-parity holes, {bad} not a draw at every h > 0; off-parity holes: {off_bps} breakpoints");
    }
}
