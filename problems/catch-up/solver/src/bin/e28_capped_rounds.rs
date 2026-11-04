//! Usage: e28_capped_rounds <p_max>
//! I17's mechanism: how low can a block keep the rounds-game structure? In the rounds game (C13) on offsets
//! {0..2p−1} from debt d (every band entry d ≤ p, d ≡ p mod 2), Z must reach ≥ draw while every round start keeps
//! the mover's debt ≤ a + min R (then every single pick catches up at height a and the real game is the rounds
//! game, C22); a round start above the cap counts as a Z failure. Prints, per (p, d), the least a ≥ 0 at which Z
//! succeeds in both roles, next to C24's 2p − 1.
//! First checks: with no cap Z draws every band entry in both roles (C24's rounds game, Lean); with cap a = 2p − 1
//! Z succeeds (Hyb2 and C25's debt bounds).

const LOSS: i8 = -1;
const DRAW: i8 = 0;
const WIN: i8 = 1;
/// Larger than any debt a round start can have here: no cap.
const NO_CAP: i32 = 1 << 20;

struct Game {
    p: usize,
    cap: i32,
    /// Z's outcome per (mask, debt, mover is Z); debts up to max_debt.
    memo: Vec<i8>,
    max_debt: usize,
}

impl Game {
    fn new(p: usize, cap: i32) -> Self {
        let max_debt = p * (2 * p - 1) + p + 2;
        Game { p, cap, memo: vec![i8::MIN; (1usize << (2 * p)) * (max_debt + 1) * 2], max_debt }
    }

    fn slot(&self, mask: usize, d: i32, z: bool) -> usize {
        (mask * (self.max_debt + 1) + d as usize) * 2 + z as usize
    }

    /// Z's outcome at a round start: offsets `mask`, the mover (Z if `z`) trailing by `d` ≥ 0.
    fn value(&mut self, mask: usize, d: i32, z: bool) -> i8 {
        if mask == 0 {
            return if d == 0 { DRAW } else if z { LOSS } else { WIN };
        }
        let min = mask.trailing_zeros() as i32;
        if d > self.cap + min {
            return LOSS;
        }
        let bits: Vec<usize> = (0..2 * self.p).filter(|&b| mask >> b & 1 == 1).collect();
        // Each player takes |R|/2 offsets: a mover trailing by more than top half − bottom half loses outright.
        let h = bits.len() / 2;
        let spread: i32 = bits[h..].iter().sum::<usize>() as i32 - bits[..h].iter().sum::<usize>() as i32;
        if d > spread {
            return if z { LOSS } else { WIN };
        }
        let k = self.slot(mask, d, z);
        if self.memo[k] != i8::MIN {
            return self.memo[k];
        }
        // The mover picks i, the other answers j; mover's new debt δ = d + j − i (δ ≥ 0: it moves again).
        let mut best = if z { LOSS } else { WIN };
        for &i in &bits {
            let mut worst_for_mover = if z { WIN } else { LOSS };
            for &j in bits.iter().filter(|&&j| j != i) {
                let rest = mask & !(1 << i) & !(1 << j);
                let delta = d + j as i32 - i as i32;
                let v = if delta >= 0 { self.value(rest, delta, z) } else { self.value(rest, -delta, !z) };
                worst_for_mover = if z { worst_for_mover.min(v) } else { worst_for_mover.max(v) };
            }
            best = if z { best.max(worst_for_mover) } else { best.min(worst_for_mover) };
        }
        self.memo[k] = best;
        best
    }
}

fn both_roles(p: usize, d: i32, cap: i32) -> bool {
    let full = (1usize << (2 * p)) - 1;
    let mut g = Game::new(p, cap);
    g.value(full, d, true) >= DRAW && g.value(full, d, false) >= DRAW
}

fn main() {
    let p_max: usize = std::env::args().nth(1).expect("p_max").parse().expect("p_max");
    for p in 1..=p_max {
        for d in (p % 2..=p).step_by(2) {
            let d = d as i32;
            assert!(both_roles(p, d, NO_CAP), "p={p} d={d}: the uncapped rounds game should draw (C24)");
            let c24 = 2 * p as i32 - 1;
            assert!(both_roles(p, d, c24), "p={p} d={d}: cap 2p − 1 should succeed (Hyb2, C25)");
            let least = (0..=c24).find(|&a| both_roles(p, d, a)).unwrap();
            println!("p={p} d={d}: least height keeping rounds structure {least} (C24: {c24})");
        }
    }
}
