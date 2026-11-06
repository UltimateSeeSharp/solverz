//! Usage: e46_threshold_variants <theta_min> <theta_max> <n_min> <n_max>
//! C120: the threshold-θ variant of Catch-Up (`Threshold`) on {1..N} at a tie, every even-total N in range: prints the
//! opener's margin (0 = draw).
//! First checks: θ = 0 (Catch-Up) is 0 at every even-total N ≤ 12; θ = 4 is −2 at N = 11 (I31's HashMap and array engines).

use catch_up::threshold::Threshold;

fn root(n: u64, theta: u64) -> i64 {
    let numbers: Vec<u64> = (1..=n).collect();
    Threshold::new(&numbers, theta).margin((1usize << n) - 1, 0)
}

fn even_total(n: u64) -> bool {
    n * (n + 1) / 2 % 2 == 0
}

fn check() {
    for n in (3..=12).filter(|&n| even_total(n)) {
        assert_eq!(root(n, 0), 0, "Catch-Up at N = {n}");
    }
    assert_eq!(root(11, 4), -2, "θ = 4 at N = 11");
    println!("check: θ = 0 draws every even total N ≤ 12; θ = 4 is −2 at N = 11");
}

fn main() {
    let a: Vec<u64> = std::env::args().skip(1).map(|s| s.parse().expect("theta_min theta_max n_min n_max")).collect();
    assert_eq!(a.len(), 4, "usage: e46_threshold_variants <theta_min> <theta_max> <n_min> <n_max>");
    check();
    for theta in a[0]..=a[1] {
        let row: Vec<String> = (a[2]..=a[3]).filter(|&n| even_total(n)).map(|n| format!("N{n}:{}", root(n, theta))).collect();
        println!("θ={theta}: {}", row.join(" "));
    }
}
