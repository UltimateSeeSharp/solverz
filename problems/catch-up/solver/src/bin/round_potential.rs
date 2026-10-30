//! Usage: round_potential [max_pairs] [universe] [max_margin]   (defaults 7, 15, 60)
//! Is a round-by-round invariant K for C15 (always-max on pair sets, rounds game; B20) closed under play?
//! Answer (journal 2026-10-26): closed for p ≤ 5, not from p = 6; C15's proof measures Φ at balanced starts instead.
//! A round-start state: each number of a pair set E is left, held by Z (always-max) or held by Y, equal counts;
//! Z's margin s; the mover. A remainder is a left number whose partner is held; it is owed to the other player.
//! yh = remainders whose partner Y holds, zh = those whose partner Z holds; δ = (|yh| − |zh|) / 2;
//! Φ = s + Σ yh − Σ zh. K:
//! - every number Z holds exceeds every number left; s > 0 ⇒ Y moves, s < 0 ⇒ Z moves;
//! - Z moves ⇒ no remainders and s ∈ {−1, 0};  δ ≥ 0;
//! - δ = 0: Φ ≥ −1;
//! - δ ≥ 1, zh empty: Φ − 2·(sum of the δ largest yh) − h ≥ −1, h = fresh pairs above max yh;
//! - δ ≥ 1, zh nonempty: every Y move leads to a K-state (or ends the game at s ≥ −1).
//! Checked: every K-state's successors are K-states, and every game end from a K-state has s ≥ −1.

use std::time::Instant;

const DEFAULT_PAIRS: usize = 7;
const DEFAULT_UNIVERSE: u32 = 15;
const DEFAULT_MARGIN: i64 = 60;
const MIN_MARGIN: i64 = -3;
const LEFT: u8 = 0;
const ZHELD: u8 = 1;
const YHELD: u8 = 2;

#[derive(Clone)]
struct State {
    owner: Vec<u8>, // per number of E (sorted), LEFT / ZHELD / YHELD
    s: i64,
    z_moves: bool,
}

struct Game {
    nums: Vec<i64>,      // E sorted
    partner: Vec<usize>, // index of the partner
}

impl Game {
    fn left(&self, st: &State) -> Vec<usize> {
        (0..self.nums.len()).filter(|&k| st.owner[k] == LEFT).collect()
    }

    fn max_left(&self, st: &State) -> Option<usize> {
        (0..self.nums.len()).rev().find(|&k| st.owner[k] == LEFT)
    }

    fn successors(&self, st: &State) -> Vec<State> {
        let mut out = Vec::new();
        let next = |s2: i64| if s2 == 0 { st.z_moves } else { s2 < 0 };
        if st.z_moves {
            let i = self.max_left(st).expect("nonempty");
            for j in self.left(st) {
                if j == i {
                    continue;
                }
                let mut o = st.owner.clone();
                o[i] = ZHELD;
                o[j] = YHELD;
                let s2 = st.s + self.nums[i] - self.nums[j];
                out.push(State { owner: o, s: s2, z_moves: next(s2) });
            }
        } else {
            for j in self.left(st) {
                let mut o = st.owner.clone();
                o[j] = YHELD;
                let probe = State { owner: o.clone(), s: st.s, z_moves: st.z_moves };
                let i = self.max_left(&probe).expect("even count");
                o[i] = ZHELD;
                let s2 = st.s + self.nums[i] - self.nums[j];
                out.push(State { owner: o, s: s2, z_moves: next(s2) });
            }
        }
        out
    }

    fn is_empty(&self, st: &State) -> bool {
        st.owner.iter().all(|&o| o != LEFT)
    }

    /// Ok(()) if st is a K-state, else the failing condition.
    fn k(&self, st: &State) -> Result<(), &'static str> {
        let top = self.max_left(st).map(|k| self.nums[k]).unwrap_or(i64::MIN);
        if (0..self.nums.len()).any(|k| st.owner[k] == ZHELD && self.nums[k] <= top) {
            return Err("Z holds a number below one left");
        }
        if (st.s > 0 && st.z_moves) || (st.s < 0 && !st.z_moves) {
            return Err("mover");
        }
        let mut yh: Vec<i64> = Vec::new();
        let mut zh = 0usize;
        let mut zsum = 0i64;
        for k in 0..self.nums.len() {
            if st.owner[k] != LEFT {
                continue;
            }
            match st.owner[self.partner[k]] {
                YHELD => yh.push(self.nums[k]),
                ZHELD => {
                    zh += 1;
                    zsum += self.nums[k];
                }
                _ => {}
            }
        }
        if st.z_moves && (!yh.is_empty() || zh > 0 || !(st.s == -1 || st.s == 0)) {
            return Err("Z moves with remainders or margin outside {-1, 0}");
        }
        if (yh.len() + zh) % 2 == 1 || yh.len() < zh {
            return Err("delta");
        }
        let delta = (yh.len() - zh) / 2;
        let phi = st.s + yh.iter().sum::<i64>() - zsum;
        if delta == 0 {
            return if phi >= -1 { Ok(()) } else { Err("phi") };
        }
        if zh > 0 {
            for nx in self.successors(st) {
                if self.is_empty(&nx) {
                    if nx.s < -1 {
                        return Err("lookahead: end below -1");
                    }
                } else if self.k(&nx).is_err() {
                    return Err("lookahead");
                }
            }
            return Ok(());
        }
        yh.sort_unstable_by(|a, b| b.cmp(a));
        let reserve: i64 = 2 * yh[..delta].iter().sum::<i64>();
        let h = (0..self.nums.len())
            .filter(|&k| st.owner[k] == LEFT && st.owner[self.partner[k]] == LEFT && self.nums[k] > yh[0])
            .count() as i64
            / 2;
        if phi - reserve - h >= -1 { Ok(()) } else { Err("after-double potential") }
    }
}

fn pair_sets(u: u32, lo: u32, acc: Vec<u32>, p: usize, out: &mut Vec<Vec<u32>>) {
    if acc.len() == 2 * p {
        out.push(acc);
        return;
    }
    for x in lo..u.saturating_sub(1) {
        let mut a = acc.clone();
        a.push(x);
        a.push(x + 1);
        pair_sets(u, x + 2, a, p, out);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let max_p: usize = args.next().map(|a| a.parse().expect("pairs")).unwrap_or(DEFAULT_PAIRS);
    let u: u32 = args.next().map(|a| a.parse().expect("universe")).unwrap_or(DEFAULT_UNIVERSE);
    let smax: i64 = args.next().map(|a| a.parse().expect("margin")).unwrap_or(DEFAULT_MARGIN);
    let start = Instant::now();
    println!("# round_potential {max_p} {u} {smax}\n");
    let (mut checked, mut violations) = (0u64, 0u64);
    for p in 1..=max_p {
        let mut sets = Vec::new();
        pair_sets(u, 0, Vec::new(), p, &mut sets);
        sets.retain(|e| e[0] == 0);
        let (mut cp, mut vp) = (0u64, 0u64);
        for e in &sets {
            let n = e.len();
            let game = Game {
                nums: e.iter().map(|&x| x as i64).collect(),
                partner: (0..n).map(|k| k ^ 1).collect(),
            };
            // Labelings with equal holdings; Z's holdings must be a top segment of the taken numbers above all left,
            // which k() checks, so enumerate all and let it filter.
            let total = 3usize.pow(n as u32);
            for code in 0..total {
                let mut c = code;
                let owner: Vec<u8> = (0..n)
                    .map(|_| {
                        let d = (c % 3) as u8;
                        c /= 3;
                        d
                    })
                    .collect();
                let zc = owner.iter().filter(|&&o| o == ZHELD).count();
                let yc = owner.iter().filter(|&&o| o == YHELD).count();
                if zc != yc || zc * 2 == n {
                    continue;
                }
                // quick k0 filter
                let top = (0..n).rev().find(|&k| owner[k] == LEFT).unwrap();
                if (0..top).any(|k| owner[k] == ZHELD) {
                    continue;
                }
                for s in MIN_MARGIN..=smax {
                    for z_moves in [true, false] {
                        let st = State { owner: owner.clone(), s, z_moves };
                        if game.k(&st).is_err() {
                            continue;
                        }
                        cp += 1;
                        for nx in game.successors(&st) {
                            let bad = if game.is_empty(&nx) { nx.s < -1 } else { game.k(&nx).is_err() };
                            if bad {
                                vp += 1;
                                if vp <= 3 {
                                    let show = |o: &Vec<u8>, w: u8| -> Vec<u32> { (0..n).filter(|&k| o[k] == w).map(|k| e[k]).collect() };
                                    println!(
                                        "- violation: E {:?}, left {:?}, Z {:?}, Y {:?}, s {s}, Z moves {z_moves} -> left {:?}, s {}: {:?}",
                                        e,
                                        show(&owner, LEFT),
                                        show(&owner, ZHELD),
                                        show(&owner, YHELD),
                                        show(&nx.owner, LEFT),
                                        nx.s,
                                        game.k(&nx).err()
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        println!("p = {p}: {} pair sets, {cp} K-states, {vp} violations ({:.1} s)", sets.len(), start.elapsed().as_secs_f64());
        checked += cp;
        violations += vp;
    }
    println!("\nTotal: {checked} K-states, {violations} violations; {:.1} s", start.elapsed().as_secs_f64());
}
