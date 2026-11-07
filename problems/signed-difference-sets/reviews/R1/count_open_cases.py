"""Count open cases and reproduce the cumulative exclusions in the paper.

The script reads the bundled ``sds.json`` snapshot and applies, in order,

1. the self-conjugate-prime obstruction;
2. the C_2-quotient obstruction;
3. the near-full-support parity obstruction; and
4. the small-defect parity obstruction.

Run

    python3 count_open_cases.py

to print the initial and cumulative counts. Add ``--write-csv`` to write a
row-by-row audit trail.
No third-party Python packages are required.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


MIN_V = 9
MAX_V = 499

# This hash identifies the exact database snapshot used for the paper counts.
EXPECTED_DATABASE_SHA256 = (
    "39bab9fce78d5c4353c22ba482ff5c3bb8b8b9931edc5ca0fc60062dfe80ca85"
)

EXPECTED_COUNTS = {
    "initial_open": 67_823,
    "self_conjugate_further": 44_872,
    "c2_further": 456,
    "near_full_further": 29,
    "small_defect_further": 4,
    "total_excluded": 45_361,
    "remaining": 22_462,
}

# Example key: SDS(49,48,2,[7,7])
PARAMETER_PATTERN = re.compile(
    r"^SDS\((-?\d+),(-?\d+),(-?\d+),\[([^]]*)\]\)$"
)


@dataclass(frozen=True)
class Case:
    """One group-specific database entry."""

    parameter: str
    v: int
    k: int
    lam: int
    group_factors: tuple[int, ...]

    @property
    def n(self) -> int:
        return self.k - self.lam

    @property
    def exponent(self) -> int:
        return math.lcm(*self.group_factors)


@dataclass(frozen=True)
class Exclusion:
    """An excluded case together with a human-readable theorem witness."""

    stage: str
    case: Case
    witness: str


def parse_case(parameter: str) -> Case:
    """Parse v, k, lambda, and the abelian-group invariant factors."""
    match = PARAMETER_PATTERN.match(parameter.replace(" ", ""))
    if match is None:
        raise ValueError(f"Cannot parse database key: {parameter}")

    v, k, lam = (int(match.group(i)) for i in range(1, 4))
    factors_text = match.group(4)
    factors = tuple(int(value) for value in factors_text.split(",") if value)
    if not factors:
        raise ValueError(f"No group invariant factors in: {parameter}")
    if math.prod(factors) != v:
        raise ValueError(
            f"Group factors in {parameter} have product {math.prod(factors)}, not {v}."
        )

    return Case(parameter, v, k, lam, factors)


def read_open_cases(database_path: Path) -> list[Case]:
    """Read the group-specific entries marked Open in the stated v-range."""
    with database_path.open("r", encoding="utf-8") as database_file:
        database = json.load(database_file)

    cases = []
    for parameter, record in database.items():
        if record.get("status") != "Open":
            continue
        case = parse_case(parameter)
        if MIN_V <= case.v <= MAX_V:
            cases.append(case)

    return sorted(cases, key=lambda case: case.parameter)


def is_prime(value: int) -> bool:
    """Return whether value is a rational prime."""
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


@lru_cache(maxsize=None)
def prime_factorization(value: int) -> tuple[tuple[int, int], ...]:
    """Return the prime factorization as (prime, valuation) pairs."""
    value = abs(value)
    factors: list[tuple[int, int]] = []
    prime = 2
    while prime * prime <= value:
        valuation = 0
        while value % prime == 0:
            value //= prime
            valuation += 1
        if valuation:
            factors.append((prime, valuation))
        prime = 3 if prime == 2 else prime + 2
    if value > 1:
        factors.append((value, 1))
    return tuple(factors)


@lru_cache(maxsize=None)
def divisors(value: int) -> tuple[int, ...]:
    """Return all positive divisors of value in increasing order."""
    result = [1]
    for prime, valuation in prime_factorization(value):
        old_result = list(result)
        prime_power = 1
        for _ in range(valuation):
            prime_power *= prime
            result.extend(divisor * prime_power for divisor in old_result)
    return tuple(sorted(result))


def minus_one_power_witness(prime: int, modulus: int) -> int | None:
    """Find j >= 1 with prime**j == -1 (mod modulus), if it exists."""
    if math.gcd(prime, modulus) != 1:
        return None

    target = (-1) % modulus
    residue = 1
    seen = {residue}
    j = 0
    while True:
        j += 1
        residue = (residue * prime) % modulus
        if residue == target:
            return j
        if residue in seen:
            return None
        seen.add(residue)


@lru_cache(maxsize=None)
def self_conjugate_witness(n: int, exponent: int) -> str | None:
    """Apply the self-conjugate-prime obstruction to (n, exp(G))."""
    if n <= 0:
        return None

    # Only primes having odd p-adic valuation can contradict the theorem.
    for prime, valuation in prime_factorization(n):
        if valuation % 2 == 0:
            continue
        for modulus in divisors(exponent):
            if modulus <= 1:
                continue
            j = minus_one_power_witness(prime, modulus)
            if j is not None:
                return (
                    f"n={n}; E={exponent}; p={prime}; "
                    f"v_p(n)={valuation}; m={modulus}; j={j}"
                )
    return None


def c2_quotient_witness(case: Case) -> str | None:
    """For even v, k-lambda must be a perfect square."""
    if case.v % 2 != 0 or case.n < 0:
        return None
    square_root = math.isqrt(case.n)
    if square_root * square_root != case.n:
        return f"v is even; n=k-lambda={case.n} is not a perfect square"
    return None


@lru_cache(maxsize=None)
def near_full_witness(v: int, k: int, lam: int) -> str | None:
    """Apply the near-full-support congruence for every eligible h."""
    if k != v - 1:
        return None

    # A finite abelian group has a subgroup of every divisor order. We use
    # nontrivial proper odd subgroup orders, so that G/H is nontrivial.
    for h in divisors(v):
        if h <= 1 or h >= v or h % 2 == 0:
            continue
        q = v // h
        lhs = (v - 1 + lam * (h - 1)) % 8
        allowed = {(q - 1) % 8, (q + 3) % 8}
        if lhs not in allowed:
            allowed_text = " or ".join(str(value) for value in sorted(allowed))
            return f"h={h}; q={q}; lhs mod 8={lhs}; allowed={allowed_text}"
    return None


def small_defect_witness(case: Case) -> str | None:
    """Apply the small-defect theorem when G is elementary abelian."""
    factors = case.group_factors
    prime = factors[0]
    if not is_prime(prime) or prime == 2 or any(x != prime for x in factors):
        return None

    m = len(factors)
    if prime**m != case.v:
        return None
    defect = case.v - case.k
    if not 1 <= defect <= m:
        return None

    lhs = (case.k - case.lam + case.lam * prime ** (m - 1)) % 8
    if defect % 2 == 0:
        allowed = {prime % 8}
    else:
        allowed = {(prime - 1) % 8, (prime + 3) % 8}

    if lhs not in allowed:
        allowed_text = " or ".join(str(value) for value in sorted(allowed))
        return (
            f"p={prime}; m={m}; d={defect}; "
            f"lhs mod 8={lhs}; allowed={allowed_text}"
        )
    return None


def apply_stage(
    remaining: dict[str, Case],
    stage: str,
    witness_function,
) -> list[Exclusion]:
    """Remove and return all cases excluded at the current stage."""
    exclusions = []
    for parameter, case in list(remaining.items()):
        witness = witness_function(case)
        if witness is None:
            continue
        exclusions.append(Exclusion(stage, case, witness))
        del remaining[parameter]
    return exclusions


def write_audit_files(
    output_directory: Path,
    exclusions: list[Exclusion],
    remaining: dict[str, Case],
) -> None:
    """Write every exclusion witness and the final remaining-case list."""
    output_directory.mkdir(parents=True, exist_ok=True)

    exclusions_path = output_directory / "cumulative_exclusions.csv"
    with exclusions_path.open("w", newline="", encoding="utf-8") as output_file:
        writer = csv.writer(output_file)
        writer.writerow(
            ["stage", "parameter", "v", "k", "lambda", "group", "witness"]
        )
        for exclusion in exclusions:
            case = exclusion.case
            writer.writerow(
                [
                    exclusion.stage,
                    case.parameter,
                    case.v,
                    case.k,
                    case.lam,
                    list(case.group_factors),
                    exclusion.witness,
                ]
            )

    remaining_path = output_directory / "remaining_open_cases.csv"
    with remaining_path.open("w", newline="", encoding="utf-8") as output_file:
        writer = csv.writer(output_file)
        writer.writerow(["parameter", "v", "k", "lambda", "group"])
        for case in sorted(remaining.values(), key=lambda item: item.parameter):
            writer.writerow(
                [case.parameter, case.v, case.k, case.lam, list(case.group_factors)]
            )

    print(f"Wrote: {exclusions_path}")
    print(f"Wrote: {remaining_path}")


def database_sha256(database_path: Path) -> str:
    """Return the SHA-256 checksum of the database snapshot."""
    digest = hashlib.sha256()
    with database_path.open("rb") as database_file:
        for block in iter(lambda: database_file.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def check_count(label: str, actual: int, expected_key: str) -> None:
    """Print PASS or FAIL against the count reported in the paper."""
    expected = EXPECTED_COUNTS[expected_key]
    result = "PASS" if actual == expected else "FAIL"
    print(f"[{result}] {label}: {actual:,} (expected {expected:,})")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-csv",
        action="store_true",
        help="write a row-by-row exclusion audit and the final remaining list",
    )
    arguments = parser.parse_args()

    script_directory = Path(__file__).resolve().parent
    database_path = script_directory / "sds.json"
    if not database_path.is_file():
        raise FileNotFoundError(f"Database not found: {database_path}")

    checksum = database_sha256(database_path)
    checksum_result = "PASS" if checksum == EXPECTED_DATABASE_SHA256 else "FAIL"
    print(f"[{checksum_result}] Database SHA-256: {checksum}")

    open_cases = read_open_cases(database_path)
    remaining = {case.parameter: case for case in open_cases}
    all_exclusions: list[Exclusion] = []

    check_count("Initial open cases", len(open_cases), "initial_open")

    self_exclusions = apply_stage(
        remaining,
        "self-conjugate prime",
        lambda case: self_conjugate_witness(case.n, case.exponent),
    )
    all_exclusions.extend(self_exclusions)
    check_count(
        "Further exclusions: self-conjugate prime",
        len(self_exclusions),
        "self_conjugate_further",
    )
    print(f"      Remaining after this stage: {len(remaining):,}")

    # Also report the stand-alone C_2 count, explaining why the cumulative
    # contribution is much smaller after the self-conjugate stage.
    c2_standalone = sum(
        c2_quotient_witness(case) is not None for case in open_cases
    )
    print(f"      C_2 stand-alone exclusions: {c2_standalone:,}")

    c2_exclusions = apply_stage(remaining, "C_2 quotient", c2_quotient_witness)
    all_exclusions.extend(c2_exclusions)
    check_count(
        "Further exclusions: C_2 quotient",
        len(c2_exclusions),
        "c2_further",
    )
    print(f"      Remaining after this stage: {len(remaining):,}")

    near_exclusions = apply_stage(
        remaining,
        "near-full support",
        lambda case: near_full_witness(case.v, case.k, case.lam),
    )
    all_exclusions.extend(near_exclusions)
    check_count(
        "Further exclusions: near-full support",
        len(near_exclusions),
        "near_full_further",
    )
    print(f"      Remaining after this stage: {len(remaining):,}")

    small_exclusions = apply_stage(
        remaining,
        "small defect",
        small_defect_witness,
    )
    all_exclusions.extend(small_exclusions)
    check_count(
        "Further exclusions: small defect",
        len(small_exclusions),
        "small_defect_further",
    )
    print(f"      Remaining after this stage: {len(remaining):,}")

    check_count("Total cumulative exclusions", len(all_exclusions), "total_excluded")
    check_count("Final remaining open cases", len(remaining), "remaining")

    if arguments.write_csv:
        write_audit_files(
            script_directory / "generated_witnesses",
            all_exclusions,
            remaining,
        )


if __name__ == "__main__":
    main()
