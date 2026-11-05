//! E6: P2 on every prime power q ≡ 1 mod e, q ≤ `max_q`: every sign choice on the
//! cyclotomic classes of order e and on 0 that is an SDS. Validates the engine first.
//! Usage: `e6_cyclotomic <instances.csv> <e> <max_q> <threads>`; one line per hit up to
//! the symmetries of `canonical`: q, p^m, k, λ, signs (C₀ … C_{e−1} | 0), how many sign
//! choices it stands for, and the Instance of its key with its status, if any. A hit on an
//! open Instance adds a line in E4's format (`id key yes - - coords± …`) for `answer.py`.

use signed_difference_sets::cyclotomic::{canonical, expand, search, Field, Hit};
use signed_difference_sets::{instances, is_sds, Group, Sign};
use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

/// Fields up to this order get every sign choice rechecked by `is_sds`.
const RECHECK_MAX_Q: usize = 200;

/// Prime powers p^m ≤ max_q with p^m ≡ 1 mod e, ascending.
fn prime_powers(max_q: usize, e: usize) -> Vec<(usize, u32)> {
    let mut composite = vec![false; max_q + 1];
    let mut out = Vec::new();
    for p in 2..=max_q {
        if composite[p] {
            continue;
        }
        (p * p..=max_q).step_by(p).for_each(|x| composite[x] = true);
        let (mut q, mut m) = (p, 1);
        while q <= max_q {
            if q % e == 1 {
                out.push((p, m));
            }
            q *= p;
            m += 1;
        }
    }
    out.sort_by_key(|&(p, m)| p.pow(m));
    out
}

fn show(signs: &[Sign]) -> String {
    let s = |x: &Sign| ['-', '0', '+'][(x + 1) as usize];
    let e = signs.len() - 1;
    format!("{}|{}", signs[..e].iter().map(s).collect::<String>(), s(&signs[e]))
}

/// The marked elements of `signs` on GF(q) as `c₁.c₂…±`, coordinates in ℤ_p^m with the
/// most significant digit first (`Group`'s order).
fn set_tokens(field: &Field, e: usize, signs: &[Sign]) -> String {
    let d = expand(field, e, signs);
    let token = |x: usize| {
        let digits: Vec<String> = (0..field.m)
            .rev()
            .map(|i| (x / field.p.pow(i) % field.p).to_string())
            .collect();
        format!("{}{}", digits.join("."), if d[x] > 0 { '+' } else { '-' })
    };
    (0..field.q).filter(|&x| d[x] != 0).map(token).collect::<Vec<_>>().join(" ")
}

/// Every sign choice on GF(q), q ≤ RECHECK_MAX_Q, gets the same verdict from `search` and
/// from `is_sds` on the expanded vector: a hit is an SDS, a non-hit is not, for any λ.
fn recheck(field: &Field, e: usize, hits: &[Hit]) {
    let group = Group::new(&vec![field.p; field.m as usize]);
    let found: HashMap<&[Sign], &Hit> = hits.iter().map(|h| (h.signs.as_slice(), h)).collect();
    let n = e + 1;
    for code in 1..3usize.pow(n as u32) {
        let (mut c, mut s) = (code, vec![0; n]);
        for x in s.iter_mut() {
            *x = [0, 1, -1][c % 3];
            c /= 3;
        }
        let d = expand(field, e, &s);
        let k = d.iter().filter(|&&x| x != 0).count();
        // The autocorrelation at element 1 is the only λ the vector can have.
        let lam: i64 = (0..field.q).map(|x| (d[x] * d[group.add[x][1]]) as i64).sum();
        match found.get(s.as_slice()) {
            Some(h) => assert!(
                h.k == k && h.lam == lam && is_sds(&group, k, lam, &d),
                "q = {}: hit {} is not an SDS ({k}, {lam})",
                field.q,
                show(&s)
            ),
            None => assert!(!is_sds(&group, k, lam, &d), "q = {}: missed {}", field.q, show(&s)),
        }
    }
}

/// Known sets every run must reproduce, on the fields where they live.
fn validate_known(field: &Field, e: usize, hits: &[Hit]) {
    let has = |signs: &[Sign], k: usize, lam: i64| {
        hits.iter().any(|h| h.signs == signs && h.k == k && h.lam == lam)
    };
    let q = field.q;
    // Paley (Gordon): the quadratic character, (q, q − 1, −1); e is even, so it is a P2 vector.
    let mut chi: Vec<Sign> = (0..e).map(|j| if j % 2 == 0 { 1 } else { -1 }).collect();
    chi.push(0);
    assert!(has(&chi, q - 1, -1), "q = {q}: Paley missed");
    if e == 8 && q == 73 {
        // Lehmer's octic residue difference set (73, 9, 1): C₀ alone.
        let mut c0 = vec![0; 9];
        c0[0] = 1;
        assert!(has(&c0, 9, 1), "Lehmer's (73, 9, 1) missed");
    }
    if e == 8 && q == 25 {
        // O6 (N49) is affinely a P2 vector (refuter, r4-report.md).
        assert!(hits.iter().any(|h| h.k == 12 && h.lam == 1), "O6's (25, 12, 1) missed");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let e: usize = args[1].parse().unwrap();
    let max_q: usize = args[2].parse().unwrap();
    let threads: usize = args[3].parse().unwrap();
    let table: HashMap<String, (String, String)> = instances::read(&args[0])
        .into_iter()
        .map(|i| (i.key, (i.id, i.status)))
        .collect();
    let queue = Arc::new(Mutex::new(prime_powers(max_q, e)));
    let results = Arc::new(Mutex::new(BTreeMap::new()));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, results) = (Arc::clone(&queue), Arc::clone(&results));
            std::thread::spawn(move || {
                loop {
                    let next = queue.lock().unwrap().pop();
                    let Some((p, m)) = next else { break };
                    let field = Field::new(p, m);
                    let hits = search(&field, e);
                    validate_known(&field, e, &hits);
                    if field.q <= RECHECK_MAX_Q {
                        recheck(&field, e, &hits);
                    }
                    results.lock().unwrap().insert(field.q, (p, m, hits));
                }
            })
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
    eprintln!("validation passed");
    for (q, (p, m, hits)) in results.lock().unwrap().iter() {
        // Hits grouped by their canonical form, which every member shares; the first member
        // stands for the group.
        let mut orbits: BTreeMap<Vec<Sign>, (&Hit, usize)> = BTreeMap::new();
        for h in hits {
            orbits.entry(canonical(&h.signs, e, *p)).or_insert((h, 0)).1 += 1;
        }
        for (signs, (h, count)) in orbits {
            let (k, lam) = (h.k, h.lam);
            let shape = vec![p.to_string(); *m as usize].join(",");
            let key = format!("SDS({q},{k},{lam},[{shape}])");
            let inst = table.get(&key).map_or("-".to_string(), |(id, st)| format!("{id} {st}"));
            println!("{q} {p}^{m} {k} {lam} {} {count} {inst}", show(&signs));
            if let Some((id, _)) = table.get(&key).filter(|(_, st)| st == "open") {
                println!("{id} {key} yes - - {}", set_tokens(&Field::new(*p, *m), e, &h.signs));
            }
        }
    }
}
