# Obstructions

- **O1 Arguments that also work for 5n+1**: one odd step plus one even step multiplies n by about 3/4 for 3n+1 but 5/4 for 5n+1, and 5n+1 has other cycles (13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13). Rules out: any proof that doesn't distinguish 3 from 5.
- **O2 Low-bit and residue arguments**: in the 2-adic numbers −1 = …111 is a fixed point of T, since (3·(−1)+1)/2 = −1, and −1 matches the residue 2^k − 1 for every k. Rules out: proofs that only look at finitely many low bits; a proof must use that integers have finitely many 1 bits.
- **O3 Arguments for general maps** (README, Known): generalized Collatz maps are undecidable (Conway). Rules out: proofs that don't use something specific to 3 and 2.
