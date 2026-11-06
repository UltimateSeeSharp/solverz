//! Instances read from `instances.csv`.

/// One Instance: id, key, status, v, k, λ, cyclic factors.
pub struct Instance {
    pub id: String,
    pub key: String,
    pub status: String,
    pub v: usize,
    pub k: usize,
    pub lam: i64,
    pub shape: Vec<usize>,
}

/// Splits a CSV line, keeping quoted fields (keys contain commas) whole.
fn fields(line: &str) -> Vec<String> {
    let (mut out, mut cur, mut quoted) = (Vec::new(), String::new(), false);
    for c in line.chars() {
        match c {
            '"' => quoted = !quoted,
            ',' if !quoted => out.push(std::mem::take(&mut cur)),
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Parses `SDS(v,k,λ,[m1,…])`.
fn parse_key(id: &str, key: &str, status: &str) -> Instance {
    let inner = &key[4..key.len() - 1];
    let (nums, shape) = inner.split_once(",[").unwrap();
    let nums: Vec<i64> = nums.split(',').map(|x| x.parse().unwrap()).collect();
    let shape: Vec<usize> =
        shape.trim_end_matches(']').split(',').map(|x| x.parse().unwrap()).collect();
    let v = nums[0] as usize;
    assert_eq!(v, shape.iter().product::<usize>(), "{key}: v ≠ |G|");
    Instance {
        id: id.to_string(),
        key: key.to_string(),
        status: status.to_string(),
        v,
        k: nums[1] as usize,
        lam: nums[2],
        shape,
    }
}

/// Every Instance in the file, in file order.
pub fn read(path: &str) -> Vec<Instance> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .skip(1)
        .map(fields)
        .map(|f| parse_key(&f[0], &f[1], &f[3]))
        .collect()
}
