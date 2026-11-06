module

public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.MarkedCounts
public import SignedDifferenceSets.OrbitSearch

/-!
# Coset sums fixed by a multiplier (A7, C10), checked by the kernel

C10: on a quotient `H` of order prime to `n = k − λ`, a translate `a` of the coset sums of an SDS
is fixed by every multiplier `t` of `H` (`FixedCosetSums`), so it is constant on the cycles of
`x ↦ t x`. `cosetCheck` labels the cycles on `Indexed`'s numbers as `OrbitSearch` does (checked
by `labelsOK`), sorts the classes by size, largest first, and tries every value per class
(`valSearch`, on values shifted into ℕ so the kernel uses `Nat` arithmetic), only those `spanN`
allows: a value is cut when the rest cannot reach `Σ a = s`, `Σ a² = n + λc` (Cauchy–Schwarz,
`|a| ≤ c`). A complete choice must meet `Σ |a| ≤ k`, `k − Σ |a|` even, `k ≤ Σ maxMarked c a`
(C3, C7) and miss `λc` at some shift. `cosetNodes` and `cosetSlice` split one search over
several declarations. `not_hasSDS_of_cosetSearch` takes C10 as a hypothesis (`C10Holds`);
`not_hasSDS_of_cosetRow` supplies it through C16 for squarefree `n`. Rows are checked by
`decide +kernel` (`solver/a7rows.py` writes them).
-/

@[expose] public section

namespace SignedDifferenceSets

namespace CosetSearch

open OrbitSearch

/-! ### The search, on values shifted into ℕ

A value `x ∈ [−C, C]` is kept as `u = x + C`, so the kernel computes with `Nat` alone (GMP):
`|x| = ndist C u`, `x² = (ndist C u)²`, and `Σ x = s` reads `Σ u = s + C v`. The hot definitions
call `Nat.add`, `Nat.mul`, `Nat.sub` directly (no instance unfolding); `ndist_eq`, `spanN_eq`,
`keepN_eq` and `valSearch_cons` restate them with the usual notation. -/

/-- `|a − b|` in ℕ. -/
def ndist (a b : ℕ) : ℕ := Nat.add (Nat.sub a b) (Nat.sub b a)

theorem ndist_eq (a b : ℕ) : ndist a b = (a - b) + (b - a) := rfl

/-- `maxMarked C x` for `x = u − C` (`C − x ≡ u` mod 2), in ℕ. -/
def mmN (C u : ℕ) : ℕ := if u % 2 = 0 then C else C - 1

/-- `p lo && p (lo + 1) && ⋯` over `m` numbers. -/
def allNat (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => p lo && allNat p (lo + 1) m

theorem allNat_iff (p : ℕ → Bool) (lo m : ℕ) :
    allNat p lo m = true ↔ ∀ u, lo ≤ u → u < lo + m → p u = true := by
  induction m generalizing lo with
  | zero =>
    simp only [allNat, true_iff]
    intro u h1 h2
    omega
  | succ m ih =>
    simp only [allNat, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h⟩ u h1 h2
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact h0
      · exact h u (by omega) (by omega)
    · intro h
      exact ⟨h lo le_rfl (by omega), fun u h1 h2 => h u (by omega) (by omega)⟩

/-- The shifted values `lo, …, lo + m − 1` tried on a class of size `z`, as `(lo, m)`: with the
rest, `rem − z` elements in `[0, 2C]`, the shifted sum can still reach `ST`. -/
def spanN (C ST z rem su : ℕ) : ℕ × ℕ :=
  if z = 0 then (0, 2 * C + 1) else
    let lo := Nat.div (Nat.sub (Nat.add (Nat.sub (Nat.sub ST su)
      (Nat.mul (Nat.mul 2 C) (Nat.sub rem z))) z) 1) z
    let hi := min (Nat.mul 2 C) (Nat.div (Nat.sub ST su) z)
    (lo, Nat.sub (Nat.add hi 1) lo)

theorem spanN_eq (C ST z rem su : ℕ) : spanN C ST z rem su = if z = 0 then (0, 2 * C + 1) else
    ((ST - su - 2 * C * (rem - z) + z - 1) / z,
      min (2 * C) ((ST - su) / z) + 1 - (ST - su - 2 * C * (rem - z) + z - 1) / z) := rfl

/-- The shifted value `u` on a class of size `z` can complete the node: the squares stay within
`QN`, the rest can still bring the shifted sum to `ST`, and Cauchy–Schwarz allows its squares. -/
def keepN (C QN ST z rem su sq u : ℕ) : Bool :=
  let su' := Nat.add su (Nat.mul z u)
  let d := ndist C u
  let sq' := Nat.add sq (Nat.mul z (Nat.mul d d))
  let R := Nat.sub rem z
  let e := ndist (Nat.mul C R) (Nat.sub ST su')
  Nat.ble sq' QN && Nat.ble su' ST && Nat.ble ST (Nat.add su' (Nat.mul (Nat.mul 2 C) R)) &&
    Nat.ble (Nat.mul e e) (Nat.mul R (Nat.sub QN sq'))

theorem keepN_eq (C QN ST z rem su sq u : ℕ) : keepN C QN ST z rem su sq u =
    (Nat.ble (sq + z * (ndist C u * ndist C u)) QN && Nat.ble (su + z * u) ST &&
      Nat.ble ST (su + z * u + 2 * C * (rem - z)) &&
      Nat.ble (ndist (C * (rem - z)) (ST - (su + z * u)) *
        ndist (C * (rem - z)) (ST - (su + z * u)))
        ((rem - z) * (QN - (sq + z * (ndist C u * ndist C u))))) := rfl

/-- A complete choice meets `Σ u = ST` (that is `Σ x = s`), `Σ x² = QN`, `Σ |x| ≤ k` with
`k − Σ |x|` even, and `k ≤ Σ maxMarked C x`. -/
def leafOK (QN k ST su sq ab mm : ℕ) : Bool :=
  Nat.beq su ST && Nat.beq sq QN && Nat.ble ab k && Nat.ble k mm && Nat.beq ((k - ab) % 2) 0

/-- The values `u − C` of shifted values. -/
def unshift (C : ℕ) (l : List ℕ) : List ℤ := l.map fun u : ℕ => (u : ℤ) - C

/-- `Σ w u` over the pairs of `row` and `us`. -/
def dotN : List ℕ → List ℕ → ℕ
  | w :: row, u :: us => Nat.add (Nat.mul w u) (dotN row us)
  | _, _ => 0

/-- `Σ w` over the pairs of `row` and `us`. -/
def wtN : List ℕ → List ℕ → ℕ
  | w :: row, _ :: us => Nat.add w (wtN row us)
  | _, _ => 0

/-- `Σ u · dotN row us` over the pairs of `W` and `ws`. -/
def corrA (us : List ℕ) : List (List ℕ) → List ℕ → ℕ
  | row :: W, u :: ws => Nat.add (Nat.mul u (dotN row us)) (corrA us W ws)
  | _, _ => 0

/-- `Σ (u · wtN row us + dotN row us)` over the pairs of `W` and `ws`. -/
def corrB (us : List ℕ) : List (List ℕ) → List ℕ → ℕ
  | row :: W, u :: ws => Nat.add (Nat.add (Nat.mul u (wtN row us)) (dotN row us)) (corrB us W ws)
  | _, _ => 0

/-- `Σ wtN row us` over the pairs of `W` and `ws`. -/
def corrN (us : List ℕ) : List (List ℕ) → List ℕ → ℕ
  | row :: W, _ :: ws => Nat.add (wtN row us) (corrN us W ws)
  | _, _ => 0

/-- `leafKilled` on the values `u − C`, in ℕ: the correlation `A − C B + C² N` (`corr_eq`) misses
`T` at a shift of `Ws`. -/
def leafKilledN (Ws : List (List (List ℕ))) (T : ℤ) (C : ℕ) (us : List ℕ) : Bool :=
  Ws.any fun W => !Nat.beq
    (Nat.add (Nat.add (corrA us W us) (Nat.mul (Nat.mul C C) (corrN us W us))) (-T).toNat)
    (Nat.add (Nat.mul C (corrB us W us)) T.toNat)

/-- Every choice of shifted values on the classes `cls` (root, size; `rem` elements in all)
after the reversed values `pre`, with weighted sums `su` (values), `sq` (squares), `ab` (`|x|`)
and `mm` (`maxMarked`), that meets the demands misses `T` at a shift of `Ws`. -/
def valSearch (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) :
    List (ℕ × ℕ) → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], _, pre, su, sq, ab, mm =>
    !leafOK QN k ST su sq ab mm || leafKilledN Ws T C pre.reverse
  | (_, z) :: cls, rem, pre, su, sq, ab, mm =>
    allNat (fun u => !keepN C QN ST z rem su sq u ||
        valSearch Ws C QN k ST T cls (Nat.sub rem z) (u :: pre) (Nat.add su (Nat.mul z u))
          (Nat.add sq (Nat.mul z (Nat.mul (ndist C u) (ndist C u))))
          (Nat.add ab (Nat.mul z (ndist C u))) (Nat.add mm (Nat.mul z (mmN C u))))
      (spanN C ST z rem su).1 (spanN C ST z rem su).2

theorem valSearch_cons (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) (r z : ℕ)
    (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ) :
    valSearch Ws C QN k ST T ((r, z) :: cls) rem pre su sq ab mm =
      allNat (fun u => !keepN C QN ST z rem su sq u ||
          valSearch Ws C QN k ST T cls (rem - z) (u :: pre) (su + z * u)
            (sq + z * (ndist C u * ndist C u)) (ab + z * ndist C u) (mm + z * mmN C u))
        (spanN C ST z rem su).1 (spanN C ST z rem su).2 := rfl

/-! ### Soundness of the search -/

/-- `Σ z · F root` over the classes `(root, z)`. -/
def wsum (F : ℕ → ℤ) : List (ℕ × ℕ) → ℤ
  | [] => 0
  | (r, z) :: cls => z * F r + wsum F cls

/-- Each class's value `τ root`, `z` times. -/
def expand (τ : ℕ → ℤ) : List (ℕ × ℕ) → List ℤ
  | [] => []
  | (r, z) :: cls => List.replicate z (τ r) ++ expand τ cls

theorem sum_expand (τ : ℕ → ℤ) : ∀ cls, (expand τ cls).sum = wsum τ cls
  | [] => rfl
  | (r, z) :: cls => by
    simp only [expand, wsum, List.sum_append, List.sum_replicate_int, sum_expand τ cls]

theorem length_expand (τ : ℕ → ℤ) :
    ∀ cls, ((expand τ cls).length : ℤ) = wsum (fun _ => 1) cls
  | [] => rfl
  | (r, z) :: cls => by
    simp only [expand, wsum, List.length_append, List.length_replicate, Nat.cast_add,
      length_expand τ cls, mul_one]

theorem sqSum_expand (τ : ℕ → ℤ) : ∀ cls, sqSum (expand τ cls) = wsum (fun r => τ r * τ r) cls
  | [] => rfl
  | (r, z) :: cls => by
    have ih := sqSum_expand τ cls
    simp only [sqSum] at ih
    simp only [expand, wsum, sqSum, List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate_int, ih]

/-- Cauchy–Schwarz with the class sizes as weights. -/
theorem wsum_mul_wsum_le (τ : ℕ → ℤ) (cls : List (ℕ × ℕ)) :
    wsum τ cls * wsum τ cls ≤ wsum (fun _ => 1) cls * wsum (fun r => τ r * τ r) cls := by
  have h := sum_mul_sum_le (expand τ cls)
  rwa [sum_expand, length_expand, sqSum_expand] at h

theorem wsum_sq_nonneg (τ : ℕ → ℤ) (cls : List (ℕ × ℕ)) :
    0 ≤ wsum (fun r => τ r * τ r) cls := by
  rw [← sqSum_expand]
  exact sqSum_nonneg _

theorem natCast_dotN (C : ℕ) : ∀ row us : List ℕ,
    (dotN row us : ℤ) - C * wtN row us =
      (List.zipWith (fun (w : ℕ) (b : ℤ) => (w : ℤ) * b) row (unshift C us)).sum
  | [], _ => by simp [dotN, wtN]
  | _ :: _, [] => by simp [dotN, wtN, unshift]
  | w :: row, u :: us => by
    have ih := natCast_dotN C row us
    simp only [unshift] at ih ⊢
    simp only [dotN, wtN, List.map_cons, List.zipWith_cons_cons, List.sum_cons, Nat.add_eq,
      Nat.mul_eq, Nat.cast_add, Nat.cast_mul]
    rw [← ih]
    ring

/-- The correlation of the values `u − C` from the parts in ℕ. -/
theorem corr_eq (C : ℕ) (us : List ℕ) : ∀ (W : List (List ℕ)) (ws : List ℕ),
    (corrA us W ws : ℤ) - C * corrB us W ws + C * C * corrN us W ws =
      (List.zipWith (fun (row : List ℕ) (a : ℤ) =>
        a * (List.zipWith (fun (w : ℕ) (b : ℤ) => (w : ℤ) * b) row (unshift C us)).sum)
        W (unshift C ws)).sum
  | [], _ => by simp [corrA, corrB, corrN]
  | _ :: _, [] => by simp [corrA, corrB, corrN, unshift]
  | row :: W, u :: ws => by
    have ih := corr_eq C us W ws
    have hd := natCast_dotN C row us
    simp only [unshift] at ih hd ⊢
    simp only [corrA, corrB, corrN, List.map_cons, List.zipWith_cons_cons, List.sum_cons,
      Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul]
    rw [← ih, ← hd]
    ring

theorem leafKilled_of_leafKilledN {Ws : List (List (List ℕ))} {T : ℤ} {C : ℕ} {us : List ℕ}
    (h : leafKilledN Ws T C us = true) : leafKilled Ws T (unshift C us) = true := by
  rw [leafKilledN, List.any_eq_true] at h
  obtain ⟨W, hW, hne⟩ := h
  rw [leafKilled, List.any_eq_true]
  refine ⟨W, hW, ?_⟩
  rw [bne_iff_ne, ne_eq]
  intro heq
  have e : corrW W (unshift C us) =
      (corrA us W us : ℤ) - C * corrB us W us + C * C * corrN us W us := (corr_eq C us W us).symm
  cases hb : Nat.beq
      (Nat.add (Nat.add (corrA us W us) (Nat.mul (Nat.mul C C) (corrN us W us))) (-T).toNat)
      (Nat.add (Nat.mul C (corrB us W us)) T.toNat)
  · have hne' := Nat.ne_of_beq_eq_false hb
    simp only [Nat.add_eq, Nat.mul_eq] at hne'
    apply hne'
    rw [heq] at e
    have key : ((corrA us W us + C * C * corrN us W us + (-T).toNat : ℕ) : ℤ) =
        ((C * corrB us W us + T.toNat : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [Int.toNat_eq_max, Int.toNat_eq_max]
      rcases le_total T 0 with hT | hT
      · rw [max_eq_left (neg_nonneg.2 hT), max_eq_right hT]
        linarith
      · rw [max_eq_right (neg_nonpos.2 hT), max_eq_left hT]
        linarith
    exact_mod_cast key
  · rw [hb] at hne
    exact absurd hne (by decide)

/-- `Σ z · F root` over the classes, in ℕ. -/
def wsumN (F : ℕ → ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (r, z) :: cls => z * F r + wsumN F cls

theorem natCast_wsumN (F : ℕ → ℕ) :
    ∀ cls, (wsumN F cls : ℤ) = wsum (fun r => (F r : ℤ)) cls
  | [] => rfl
  | (r, z) :: cls => by
    simp only [wsumN, wsum, Nat.cast_add, Nat.cast_mul, natCast_wsumN F cls]

theorem natCast_wsumN_one :
    ∀ cls : List (ℕ × ℕ), (wsumN (fun _ => 1) cls : ℤ) = wsum (fun _ => 1) cls
  | [] => rfl
  | (r, z) :: cls => by
    simp only [wsumN, wsum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, natCast_wsumN_one cls]

theorem wsum_congr {F G : ℕ → ℤ} :
    ∀ cls : List (ℕ × ℕ), (∀ cz ∈ cls, F cz.1 = G cz.1) → wsum F cls = wsum G cls
  | [], _ => rfl
  | (r, z) :: cls, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [wsum, h.1, wsum_congr cls h.2]

theorem wsum_mono {F G : ℕ → ℤ} :
    ∀ cls : List (ℕ × ℕ), (∀ cz ∈ cls, F cz.1 ≤ G cz.1) → wsum F cls ≤ wsum G cls
  | [], _ => le_rfl
  | (r, z) :: cls, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [wsum]
    exact add_le_add (mul_le_mul_of_nonneg_left h.1 (Int.natCast_nonneg z)) (wsum_mono cls h.2)

theorem wsum_add_const (F : ℕ → ℤ) (a : ℤ) :
    ∀ cls, wsum (fun r => F r + a) cls = wsum F cls + a * wsum (fun _ => 1) cls
  | [] => by simp [wsum]
  | (r, z) :: cls => by
    simp only [wsum, wsum_add_const F a cls]
    ring

/-- `x + C` in ℕ (for `|x| ≤ C`). -/
def shiftVal (C : ℕ) (x : ℤ) : ℕ := (x + C).toNat

theorem natCast_shiftVal {C : ℕ} {x : ℤ} (hx : |x| ≤ C) : (shiftVal C x : ℤ) = x + C :=
  Int.toNat_of_nonneg (by linarith [(abs_le.1 hx).1])

theorem shiftVal_le {C : ℕ} {x : ℤ} (hx : |x| ≤ C) : shiftVal C x ≤ 2 * C := by
  have h := natCast_shiftVal hx
  have := (abs_le.1 hx).2
  omega

theorem natCast_ndist (a b : ℕ) : (ndist a b : ℤ) = |(a : ℤ) - b| := by
  rw [ndist_eq]
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by omega)]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by omega)]

theorem ndist_shiftVal {C : ℕ} {x : ℤ} (hx : |x| ≤ C) : ndist C (shiftVal C x) = x.natAbs := by
  have h : (ndist C (shiftVal C x) : ℤ) = (x.natAbs : ℤ) := by
    rw [natCast_ndist, natCast_shiftVal hx, Int.natCast_natAbs,
      show (C : ℤ) - (x + C) = -x by ring, abs_neg]
  exact_mod_cast h

theorem natCast_natAbs_sq (x : ℤ) : ((x.natAbs * x.natAbs : ℕ) : ℤ) = x * x := by
  rw [Nat.cast_mul, Int.natCast_natAbs, abs_mul_abs_self]

theorem maxMarked_le_mmN {C : ℕ} {x : ℤ} (hx : |x| ≤ C) :
    maxMarked C x ≤ (mmN C (shiftVal C x) : ℤ) := by
  have h := natCast_shiftVal hx
  unfold mmN maxMarked
  split_ifs <;> omega

theorem natCast_wsumN_shift (τ : ℕ → ℤ) {C : ℕ} (cls : List (ℕ × ℕ))
    (hc : ∀ cz ∈ cls, |τ cz.1| ≤ C) :
    (wsumN (fun r => shiftVal C (τ r)) cls : ℤ) = wsum τ cls + C * wsum (fun _ => 1) cls := by
  rw [natCast_wsumN, wsum_congr (F := fun r => ((shiftVal C (τ r) : ℕ) : ℤ))
    (G := fun r => τ r + C) cls fun cz hcz => natCast_shiftVal (hc cz hcz), wsum_add_const]

theorem natCast_wsumN_sq (τ : ℕ → ℤ) (cls : List (ℕ × ℕ)) :
    (wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls : ℤ) = wsum (fun r => τ r * τ r) cls := by
  rw [natCast_wsumN]
  exact wsum_congr cls fun cz _ => natCast_natAbs_sq _

theorem natCast_wsumN_abs (τ : ℕ → ℤ) (cls : List (ℕ × ℕ)) :
    (wsumN (fun r => (τ r).natAbs) cls : ℤ) = wsum (fun r => |τ r|) cls := by
  rw [natCast_wsumN]
  exact wsum_congr cls fun cz _ => Int.natCast_natAbs _

theorem wsumN_shift_le (τ : ℕ → ℤ) {C : ℕ} :
    ∀ cls : List (ℕ × ℕ), (∀ cz ∈ cls, |τ cz.1| ≤ C) →
      wsumN (fun r => shiftVal C (τ r)) cls ≤ 2 * C * wsumN (fun _ => 1) cls
  | [], _ => le_rfl
  | (r, z) :: cls, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [wsumN, mul_one]
    calc z * shiftVal C (τ r) + wsumN (fun r => shiftVal C (τ r)) cls
        ≤ z * (2 * C) + 2 * C * wsumN (fun _ => 1) cls :=
          Nat.add_le_add (Nat.mul_le_mul_left z (shiftVal_le h.1)) (wsumN_shift_le τ cls h.2)
      _ = 2 * C * (z + wsumN (fun _ => 1) cls) := by ring

/-- Cauchy–Schwarz for the rest, in ℕ: its sum `W − C R` squared is at most `R` times its
squares. -/
theorem rest_cs (τ : ℕ → ℤ) {C : ℕ} (cls : List (ℕ × ℕ)) (hc : ∀ cz ∈ cls, |τ cz.1| ≤ C) :
    ndist (C * wsumN (fun _ => 1) cls) (wsumN (fun r => shiftVal C (τ r)) cls) *
        ndist (C * wsumN (fun _ => 1) cls) (wsumN (fun r => shiftVal C (τ r)) cls) ≤
      wsumN (fun _ => 1) cls * wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls := by
  have key : (ndist (C * wsumN (fun _ => 1) cls) (wsumN (fun r => shiftVal C (τ r)) cls) : ℤ) *
        ndist (C * wsumN (fun _ => 1) cls) (wsumN (fun r => shiftVal C (τ r)) cls) ≤
      (wsumN (fun _ => 1) cls : ℤ) * wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls := by
    rw [natCast_ndist, abs_mul_abs_self, Nat.cast_mul, natCast_wsumN_shift τ cls hc,
      natCast_wsumN_one, natCast_wsumN_sq,
      show (C : ℤ) * wsum (fun _ => 1) cls - (wsum τ cls + C * wsum (fun _ => 1) cls) =
        -wsum τ cls by ring, neg_mul_neg]
    exact wsum_mul_wsum_le τ cls
  exact_mod_cast key

/-- `valSearch` is sound: a choice `τ` on the classes that meets the demands is killed at some
shift. -/
theorem valSearch_sound {Ws : List (List (List ℕ))} {C QN k ST : ℕ} {T : ℤ} (τ : ℕ → ℤ) :
    ∀ (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ),
      valSearch Ws C QN k ST T cls rem pre su sq ab mm = true →
      rem = wsumN (fun _ => 1) cls → (∀ cz ∈ cls, |τ cz.1| ≤ C) →
      su + wsumN (fun r => shiftVal C (τ r)) cls = ST →
      sq + wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls = QN →
      ab + wsumN (fun r => (τ r).natAbs) cls ≤ k →
      (k - (ab + wsumN (fun r => (τ r).natAbs) cls)) % 2 = 0 →
      k ≤ mm + wsumN (fun r => mmN C (shiftVal C (τ r))) cls →
      leafKilled Ws T (unshift C (pre.reverse ++ cls.map fun cz => shiftVal C (τ cz.1))) = true
  | [], _, pre, su, sq, ab, mm, h, _, _, hs, hq, ha, hp, hm => by
    simp only [wsumN, add_zero] at hs hq ha hp hm
    have hl : leafOK QN k ST su sq ab mm = true := by
      simp only [leafOK, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
      exact ⟨⟨⟨⟨hs, hq⟩, ha⟩, hm⟩, hp⟩
    simp only [valSearch, hl, Bool.not_true, Bool.false_or] at h
    simpa using leafKilled_of_leafKilledN h
  | (r, z) :: cls, rem, pre, su, sq, ab, mm, h, hr, hc, hs, hq, ha, hp, hm => by
    simp only [List.mem_cons, forall_eq_or_imp] at hc
    simp only [wsumN, mul_one] at hr hs hq ha hp hm
    have hnd := ndist_shiftVal hc.1
    have hu2 := shiftVal_le hc.1
    have hW := wsumN_shift_le τ cls hc.2
    have hcs := rest_cs τ cls hc.2
    have hR : rem - z = wsumN (fun _ => 1) cls := by omega
    have e1 : ST - (su + z * shiftVal C (τ r)) = wsumN (fun r => shiftVal C (τ r)) cls := by
      omega
    have e2 : QN - (sq + z * ((τ r).natAbs * (τ r).natAbs)) =
        wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls := by
      omega
    have hkeep : keepN C QN ST z rem su sq (shiftVal C (τ r)) = true := by
      simp only [keepN_eq, Bool.and_eq_true, Nat.ble_eq, hnd, hR, e1, e2]
      exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, hcs⟩
    have hspan : (spanN C ST z rem su).1 ≤ shiftVal C (τ r) ∧
        shiftVal C (τ r) < (spanN C ST z rem su).1 + (spanN C ST z rem su).2 := by
      rw [spanN_eq]
      split_ifs with hz
      · exact ⟨Nat.zero_le _, by omega⟩
      · have hz' : 0 < z := Nat.pos_of_ne_zero hz
        have h1 : (ST - su - 2 * C * (rem - z) + z - 1) / z ≤ shiftVal C (τ r) := by
          refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hz').2 ?_)
          have e : (shiftVal C (τ r)).succ * z = z * shiftVal C (τ r) + z := by
            rw [Nat.succ_mul, Nat.mul_comm]
          rw [e, hR]
          omega
        have h2 : shiftVal C (τ r) ≤ (ST - su) / z := by
          rw [Nat.le_div_iff_mul_le hz', mul_comm]
          omega
        dsimp only
        exact ⟨h1, by omega⟩
    simp only [valSearch_cons, allNat_iff] at h
    have hx := h _ hspan.1 hspan.2
    rw [hkeep, Bool.not_true, Bool.false_or] at hx
    have ih := valSearch_sound τ cls _ _ _ _ _ _ hx hR hc.2 (by omega) (by rw [hnd]; omega)
      (by rw [hnd]; omega) (by rw [hnd]; omega) (by omega)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_cons]
      using ih

/-! ### Splitting one search over several declarations -/

/-- A node of `valSearch`: its arguments after `Ws C QN k ST T`. -/
structure Node where
  /-- The classes left. -/
  cls : List (ℕ × ℕ)
  /-- Their total size. -/
  rem : ℕ
  /-- The shifted values chosen, reversed. -/
  pre : List ℕ
  /-- Weighted `Σ u`. -/
  su : ℕ
  /-- Weighted `Σ x²`. -/
  sq : ℕ
  /-- Weighted `Σ |x|`. -/
  ab : ℕ
  /-- Weighted `Σ maxMarked C x`. -/
  mm : ℕ

/-- `valSearch` from the node `n`. -/
def Node.run (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) (n : Node) : Bool :=
  valSearch Ws C QN k ST T n.cls n.rem n.pre n.su n.sq n.ab n.mm

/-- `f lo ++ f (lo + 1) ++ ⋯` over `m` numbers. -/
def flatNat {α : Type} (f : ℕ → List α) (lo : ℕ) : ℕ → List α
  | 0 => []
  | m + 1 => f lo ++ flatNat f (lo + 1) m

theorem mem_flatNat {α : Type} (f : ℕ → List α) (a : α) (lo m : ℕ) :
    a ∈ flatNat f lo m ↔ ∃ u, lo ≤ u ∧ u < lo + m ∧ a ∈ f u := by
  induction m generalizing lo with
  | zero =>
    simp only [flatNat, List.not_mem_nil, false_iff, not_exists, not_and]
    intro u h1 h2
    exact absurd h2 (by omega)
  | succ m ih =>
    simp only [flatNat, List.mem_append, ih]
    constructor
    · rintro (h | ⟨u, h1, h2, h⟩)
      · exact ⟨lo, le_rfl, by omega, h⟩
      · exact ⟨u, by omega, by omega, h⟩
    · rintro ⟨u, h1, h2, h⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact Or.inl h
      · exact Or.inr ⟨u, by omega, by omega, h⟩

/-- The nodes `d` levels below `valSearch`'s node that it does not cut, in the order it visits
them; a complete choice above that depth is one of them. -/
def frontier (C QN ST : ℕ) :
    ℕ → List (ℕ × ℕ) → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → List Node
  | 0, cls, rem, pre, su, sq, ab, mm => [⟨cls, rem, pre, su, sq, ab, mm⟩]
  | _ + 1, [], rem, pre, su, sq, ab, mm => [⟨[], rem, pre, su, sq, ab, mm⟩]
  | d + 1, (_, z) :: cls, rem, pre, su, sq, ab, mm =>
    flatNat (fun u => if keepN C QN ST z rem su sq u then
        frontier C QN ST d cls (rem - z) (u :: pre) (su + z * u)
          (sq + z * (ndist C u * ndist C u)) (ab + z * ndist C u) (mm + z * mmN C u)
      else [])
      (spanN C ST z rem su).1 (spanN C ST z rem su).2

/-- `valSearch` holds at a node when it holds at every node of its frontier. -/
theorem valSearch_of_frontier {Ws : List (List (List ℕ))} {C QN k ST : ℕ} {T : ℤ} :
    ∀ (d : ℕ) (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ),
      (∀ n ∈ frontier C QN ST d cls rem pre su sq ab mm, n.run Ws C QN k ST T = true) →
      valSearch Ws C QN k ST T cls rem pre su sq ab mm = true
  | 0, _, _, _, _, _, _, _, h => h _ List.mem_cons_self
  | _ + 1, [], _, _, _, _, _, _, h => h _ List.mem_cons_self
  | d + 1, (r, z) :: cls, rem, pre, su, sq, ab, mm, h => by
    simp only [valSearch_cons, allNat_iff]
    intro u h1 h2
    cases hk : keepN C QN ST z rem su sq u
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      refine valSearch_of_frontier d cls _ _ _ _ _ _ fun n hn => h n ?_
      simp only [frontier, mem_flatNat]
      exact ⟨u, h1, h2, by simpa only [hk, ↓reduceIte] using hn⟩

/-- The nodes `a, …, b − 1` of `P` pass `run`. -/
def sliceOK (P : List Node) (run : Node → Bool) (a b : ℕ) : Bool :=
  ((P.drop a).take (b - a)).all run

/-- `f a b = true` for all consecutive cuts `a`, `b`. -/
def SlicesPass (f : ℕ → ℕ → Bool) : List ℕ → Prop
  | a :: b :: cuts => f a b = true ∧ SlicesPass f (b :: cuts)
  | _ => True

theorem SlicesPass.cons {f : ℕ → ℕ → Bool} {a b : ℕ} {cuts : List ℕ} (h : f a b = true)
    (h' : SlicesPass f (b :: cuts)) : SlicesPass f (a :: b :: cuts) :=
  show f a b = true ∧ SlicesPass f (b :: cuts) from ⟨h, h'⟩

theorem SlicesPass.single {f : ℕ → ℕ → Bool} {a : ℕ} : SlicesPass f [a] :=
  show True from trivial

/-- The last of `a :: cuts`. -/
def lastCut : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: cuts => lastCut b cuts

/-- Slices from `a` up to a last cut past the end cover every node from `a` on. -/
theorem all_of_slices {P : List Node} {run : Node → Bool} :
    ∀ (cuts : List ℕ) (a : ℕ), SlicesPass (sliceOK P run) (a :: cuts) →
      P.length ≤ lastCut a cuts → ∀ n ∈ P.drop a, run n = true
  | [], a, _, hl, n, hn => by
    simp only [lastCut] at hl
    rw [List.drop_eq_nil_of_le hl] at hn
    simp at hn
  | b :: cuts, a, h, hl, n, hn => by
    have h' : sliceOK P run a b = true ∧ SlicesPass (sliceOK P run) (b :: cuts) := h
    rw [← List.take_append_drop (b - a) (P.drop a), List.mem_append, List.drop_drop] at hn
    rcases hn with hn | hn
    · exact List.all_eq_true.1 h'.1 n hn
    · exact all_of_slices cuts b h'.2 hl n (List.drop_subset_drop_left P (by omega) hn)

/-! ### The search on numbers -/

/-- The labels and distances of the cycles of `y ↦ t y` on `0, …, v − 1`, as bit fields
(`OrbitSearch.scan`). -/
def cycles (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ × ℕ :=
  (scan v (Nat.log2 v + 1) (fun y => mulIdx add y t t) v 0 (0, 0, 0)).2

/-- Each number's label: the smallest element of its cycle. -/
def cycLab (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ → ℕ :=
  field (Nat.log2 v + 1) (cycles v add t).1

/-- Each number's distance to its cycle's label. -/
def cycDist (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ → ℕ :=
  field (Nat.log2 v + 1) (cycles v add t).2

/-- The labels pass `labelsOK`. -/
def cycLabelsOK (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : Bool :=
  labelsOK v (fun y => mulIdx add y t t) (cycLab v add t) (cycDist v add t)

/-- Inserts the class `a` before the first class no larger (`List.orderedInsert`, whose body
the kernel cannot see from here). -/
def insertBySize (a : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [a]
  | b :: l => if b.2 ≤ a.2 then a :: b :: l else b :: insertBySize a l

/-- Insertion sort by size, largest first; equal sizes keep their order. -/
def sortBySize : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | a :: l => insertBySize a (sortBySize l)

theorem perm_insertBySize (a : ℕ × ℕ) : ∀ l, (insertBySize a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    unfold insertBySize
    split_ifs
    · exact List.Perm.refl _
    · exact ((perm_insertBySize a l).cons b).trans (List.Perm.swap a b l)

theorem perm_sortBySize : ∀ l, (sortBySize l).Perm l
  | [] => List.Perm.refl _
  | a :: l => (perm_insertBySize a _).trans ((perm_sortBySize l).cons a)

/-- The classes (root, size), largest first; equal sizes keep the roots' order. -/
def sortedCls (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : List (ℕ × ℕ) :=
  sortBySize (classes v (cycLab v add t) (cycDist v add t))

/-- One shift per nonzero root, with its weights in `sortedCls`'s order. -/
def shiftWs (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : List (List (List ℕ)) :=
  ((roots v (cycDist v add t)).filter (· != 0)).map
    (weights v add (cycLab v add t) ((sortedCls v add t).map Prod.fst))

/-- The coset search on the numbers `0, …, v − 1` with addition `add`: `true` when no `f`
constant on the cycles of `t`, with `|f| ≤ c`, `Σ f = s`, `Σ f² = k + λ (c − 1)`, `Σ |f| ≤ k`,
`k − Σ |f|` even, `k ≤ Σ maxMarked c f` and correlation `λ c` at every shift exists
(`cosetCheck_sound`). The values are shifted by `c` (`Σ (f + c) = s + c v`). -/
def cosetCheck (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Bool :=
  cycLabelsOK v add t &&
    valSearch (shiftWs v add t) c (k + lam * (c - 1)).toNat k (s + c * v).toNat (lam * c)
      (sortedCls v add t) (wsumN (fun _ => 1) (sortedCls v add t)) [] 0 0 0 0

/-- `cosetCheck`'s nodes `d` levels down. -/
def cosetNodes (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (d : ℕ) :
    List Node :=
  frontier c (k + lam * (c - 1)).toNat (s + c * v).toNat d (sortedCls v add t)
    (wsumN (fun _ => 1) (sortedCls v add t)) [] 0 0 0 0

/-- `cosetCheck`'s search from a node. -/
def cosetRun (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (n : Node) : Bool :=
  n.run (shiftWs v add t) c (k + lam * (c - 1)).toNat k (s + c * v).toNat (lam * c)

theorem cosetCheck_of_nodes {v : ℕ} {add : ℕ → ℕ → ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {d : ℕ} (hl : cycLabelsOK v add t = true)
    (h : ∀ n ∈ cosetNodes v add c k lam t s d, cosetRun v add c k lam t s n = true) :
    cosetCheck v add c k lam t s = true := by
  rw [cosetCheck, hl, Bool.true_and]
  exact valSearch_of_frontier d _ _ _ _ _ _ _ h

theorem wsum_eq_map (F : ℕ → ℤ) :
    ∀ cls : List (ℕ × ℕ), wsum F cls = (cls.map fun cz => (cz.2 : ℤ) * F cz.1).sum
  | [] => rfl
  | (r, z) :: cls => by simp [wsum, wsum_eq_map F cls]

theorem wsum_perm (F : ℕ → ℤ) {l l' : List (ℕ × ℕ)} (h : l.Perm l') :
    wsum F l = wsum F l' := by
  rw [wsum_eq_map, wsum_eq_map]
  exact (h.map _).sum_eq

/-- With checked labels, a sum over `0, …, v − 1` of `F (f y)` is the classes' weighted sum. -/
theorem sum_range_eq_wsum {v : ℕ} {lab dist : ℕ → ℕ} {f : ℕ → ℤ}
    (hlab : ∀ y < v, lab y < v ∧ dist (lab y) = 0 ∧ f y = f (lab y)) (F : ℤ → ℤ) :
    ∑ y ∈ Finset.range v, F (f y) = wsum (fun r => F (f r)) (classes v lab dist) := by
  have hroot : ∀ y ∈ Finset.range v, lab y ∈ (roots v dist).toFinset := fun y hy => by
    have h := hlab y (Finset.mem_range.1 hy)
    simp only [List.mem_toFinset, roots, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨h.1, h.2.1⟩
  have hnodup : (roots v dist).Nodup := List.nodup_range.filter _
  calc ∑ y ∈ Finset.range v, F (f y)
      = ∑ y ∈ Finset.range v, F (f (lab y)) :=
        Finset.sum_congr rfl fun y hy => by rw [(hlab y (Finset.mem_range.1 hy)).2.2]
    _ = ∑ r ∈ (roots v dist).toFinset, ∑ y ∈ Finset.range v with lab y = r, F (f r) :=
        (Finset.sum_fiberwise_of_maps_to' hroot (fun r => F (f r))).symm
    _ = ∑ r ∈ (roots v dist).toFinset, (countTo (fun y => lab y == r) v : ℤ) * F (f r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have e : ((Finset.range v).filter fun i => (lab i == r) = true) =
            (Finset.range v).filter fun y => lab y = r :=
          Finset.filter_congr fun y _ => beq_iff_eq
        rw [Finset.sum_const, nsmul_eq_mul, countTo_eq, e]
    _ = wsum (fun r => F (f r)) (classes v lab dist) := by
        rw [List.sum_toFinset _ hnodup, wsum_eq_map, classes, List.map_map]
        rfl

/-- `cosetCheck` is `true` only if no `f` on `0, …, v − 1` fixed by `t` (through `mulIdx`) has
`|f| ≤ c`, `Σ f = s`, `Σ f² = k + λ (c − 1)`, `Σ |f| ≤ k`, `k − Σ |f|` even,
`k ≤ Σ maxMarked c f` and correlation `λ c` at every shift `0 < g < v`. -/
theorem cosetCheck_sound {v : ℕ} {add : ℕ → ℕ → ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : cosetCheck v add c k lam t s = true) (f : ℕ → ℤ) (hb : ∀ y < v, |f y| ≤ c)
    (hinv : ∀ y < v, f (mulIdx add y t t) = f y) (hs : ∑ y ∈ Finset.range v, f y = s)
    (hq : ∑ y ∈ Finset.range v, f y * f y = k + lam * ((c : ℤ) - 1))
    (ha : ∑ y ∈ Finset.range v, |f y| ≤ k)
    (hp : ((k : ℤ) - ∑ y ∈ Finset.range v, |f y|) % 2 = 0)
    (hm : (k : ℤ) ≤ ∑ y ∈ Finset.range v, maxMarked c (f y))
    (hadd : ∀ y g, y < v → g < v → add y g < v)
    (hcorr : ∀ g, 0 < g → g < v → ∑ y ∈ Finset.range v, f y * f (add y g) = lam * c) :
    False := by
  simp only [cosetCheck, Bool.and_eq_true] at h
  obtain ⟨hl, hv⟩ := h
  have hlab := labelsOK_spec (f := f) hl hinv
  have hperm : (sortedCls v add t).Perm (classes v (cycLab v add t) (cycDist v add t)) :=
    perm_sortBySize _
  have hw (F : ℤ → ℤ) :
      wsum (fun r => F (f r)) (sortedCls v add t) = ∑ y ∈ Finset.range v, F (f y) := by
    rw [wsum_perm _ hperm, sum_range_eq_wsum hlab F]
  have hkeys : (classes v (cycLab v add t) (cycDist v add t)).map Prod.fst =
      roots v (cycDist v add t) := by
    simp [classes, List.map_map, Function.comp_def]
  have hrs : ((sortedCls v add t).map Prod.fst).Perm (roots v (cycDist v add t)) := by
    rw [← hkeys]
    exact hperm.map Prod.fst
  have hnodup : ((sortedCls v add t).map Prod.fst).Nodup :=
    hrs.nodup_iff.2 (List.nodup_range.filter _)
  have hroot : ∀ y < v, cycLab v add t y ∈ (sortedCls v add t).map Prod.fst := fun y hy =>
    hrs.mem_iff.2 (by
      simp only [roots, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨(hlab y hy).1, (hlab y hy).2.1⟩)
  have hlt : ∀ cz ∈ sortedCls v add t, cz.1 < v := fun cz hcz => by
    have h := hrs.mem_iff.1 (List.mem_map_of_mem (f := Prod.fst) hcz)
    simp only [roots, List.mem_filter, List.mem_range] at h
    exact h.1
  have hb' : ∀ cz ∈ sortedCls v add t, |f cz.1| ≤ c := fun cz hcz => hb _ (hlt cz hcz)
  -- The sums over the classes, in ℕ.
  have hv1 : wsum (fun _ => 1) (sortedCls v add t) = v := by
    rw [hw fun _ => 1]
    simp
  have hsu : wsumN (fun r => shiftVal c (f r)) (sortedCls v add t) = (s + c * v).toNat := by
    have e : (wsumN (fun r => shiftVal c (f r)) (sortedCls v add t) : ℤ) = s + c * v := by
      rw [natCast_wsumN_shift f _ hb', hv1, ← hs]
      exact congrArg (· + (c : ℤ) * v) (hw fun x => x)
    rw [← e, Int.toNat_natCast]
  have hsq : wsumN (fun r => (f r).natAbs * (f r).natAbs) (sortedCls v add t) =
      (k + lam * (c - 1)).toNat := by
    have e : (wsumN (fun r => (f r).natAbs * (f r).natAbs) (sortedCls v add t) : ℤ) =
        k + lam * (c - 1) := by
      rw [natCast_wsumN_sq, ← hq]
      exact hw fun x => x * x
    rw [← e, Int.toNat_natCast]
  have hab : (wsumN (fun r => (f r).natAbs) (sortedCls v add t) : ℤ) =
      ∑ y ∈ Finset.range v, |f y| := by
    rw [natCast_wsumN_abs]
    exact hw fun x => |x|
  have hmm : (k : ℤ) ≤ wsumN (fun r => mmN c (shiftVal c (f r))) (sortedCls v add t) := by
    rw [natCast_wsumN]
    refine hm.trans (le_of_eq_of_le (hw fun x => maxMarked c x).symm ?_)
    exact wsum_mono _ fun cz hcz => maxMarked_le_mmN (hb' cz hcz)
  rw [← hab] at ha hp
  have hk := valSearch_sound f _ _ [] 0 0 0 0 hv rfl hb' (by rw [zero_add, hsu])
    (by rw [zero_add, hsq]) (by rw [zero_add]; exact_mod_cast ha) (by rw [zero_add]; omega)
    (by rw [zero_add]; exact_mod_cast hmm)
  have hsl : unshift c ([].reverse ++ (sortedCls v add t).map fun cz => shiftVal c (f cz.1)) =
      ((sortedCls v add t).map Prod.fst).map f := by
    simp only [unshift, List.reverse_nil, List.nil_append, List.map_map]
    refine List.map_congr_left fun cz hcz => ?_
    simp only [Function.comp_apply]
    rw [natCast_shiftVal (hb' cz hcz)]
    ring
  rw [hsl] at hk
  simp only [leafKilled, shiftWs, List.any_eq_true, List.mem_map, bne_iff_ne, ne_eq] at hk
  obtain ⟨_, ⟨g, hgm, rfl⟩, hne⟩ := hk
  have hgv : g < v ∧ g ≠ 0 := by
    simp only [roots, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hgm
    exact ⟨hgm.1.1, hgm.2⟩
  apply hne
  rw [corrW_weights hnodup hroot (fun y hy => hroot _ (hadd y g hy hgv.1)) f,
    ← hcorr g (Nat.pos_of_ne_zero hgv.2) hgv.1]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_range] at hy
  rw [← (hlab y hy).2.2, ← (hlab _ (hadd y g hy hgv.1)).2.2]

end CosetSearch

open CosetSearch OrbitSearch

/-! ### Soundness on a group -/

section Group

variable {H : Type*} [AddCommGroup H] [Fintype H] [Indexed H]

/-- If `cosetCheck` holds on `H`'s numbers, no `a : H → ℤ` fixed by `x ↦ t x` meets what C3
and C7 demand of coset sums with fibres of size `c` and has `Σ a = s`. -/
theorem false_of_cosetCheck {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : cosetCheck (Indexed.size H) (Indexed.addIdx H) c k lam t s = true) {a : H → ℤ}
    (hd : Demands c k lam a) (hm : (k : ℤ) ≤ ∑ x, maxMarked c (a x))
    (ht : ∀ x, a (t • x) = a x) (hs : ∑ x, a x = s) : False := by
  classical
  let f : ℕ → ℤ := fun y =>
    if hy : y < Indexed.size H then a (Indexed.equiv.symm ⟨y, hy⟩) else 0
  have hfe (x : H) : f (Indexed.equiv x) = a x := by simp [f]
  have hsurj (y : ℕ) (hy : y < Indexed.size H) : ∃ x : H, (Indexed.equiv x : ℕ) = y :=
    ⟨Indexed.equiv.symm ⟨y, hy⟩, by simp⟩
  have hsum (F : ℤ → ℤ) : ∑ y ∈ Finset.range (Indexed.size H), F (f y) = ∑ x, F (a x) := by
    rw [← sum_equiv (G := H) fun y => F (f y)]
    simp only [hfe]
  refine cosetCheck_sound h f (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
    (fun y g hy hg => ?_) (fun g hg0 hg => ?_)
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [hfe]
    exact hd.bound x
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [← Indexed.equiv_nsmul x t t le_rfl, hfe, hfe, ht]
  · rw [← hs]
    exact hsum fun x => x
  · rw [hsum fun x => x * x]
    exact hd.sq
  · rw [hsum fun x => |x|]
    exact hd.abs
  · rw [hsum fun x => |x|]
    exact hd.parity
  · rw [hsum fun x => maxMarked c x]
    exact hm
  · obtain ⟨x, rfl⟩ := hsurj y hy
    obtain ⟨x', rfl⟩ := hsurj g hg
    rw [← Indexed.equiv_add]
    exact (Indexed.equiv _).isLt
  · obtain ⟨gH, rfl⟩ := hsurj g hg
    have hne : gH ≠ 0 := by
      rintro rfl
      rw [Indexed.equiv_zero] at hg0
      omega
    rw [← hd.corr gH hne,
      ← sum_equiv (G := H) fun y => f y * f (Indexed.addIdx H y (Indexed.equiv gH))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Indexed.equiv_add, hfe, hfe]

end Group

/-! ### Rows -/

/-- `f` on `Indexed`'s numbering of `Grp ds`; `false` unless every factor is positive. -/
def onGrp (ds : List ℕ) (f : ℕ → (ℕ → ℕ → ℕ) → Bool) : Bool :=
  if h : ∀ d ∈ ds, 0 < d then
    f (@Indexed.size (Grp ds) _ (Grp.indexed ds h))
      (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds h))
  else false

theorem onGrp_spec {ds : List ℕ} {f : ℕ → (ℕ → ℕ → ℕ) → Bool} (h : onGrp ds f = true) :
    ∃ hds : ∀ d ∈ ds, 0 < d, f (@Indexed.size (Grp ds) _ (Grp.indexed ds hds))
      (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)) = true := by
  unfold onGrp at h
  split_ifs at h with hds
  exact ⟨hds, h⟩

/-- The coset search on the quotient `Grp ds` with fibres of size `c`. -/
def cosetSearch (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Bool :=
  onGrp ds fun v add => cosetCheck v add c k lam t s

/-- The split search's top: labels checked, at most `N` nodes `d` levels down. -/
def cosetTop (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (d N : ℕ) : Bool :=
  onGrp ds fun v add =>
    cycLabelsOK v add t && decide ((cosetNodes v add c k lam t s d).length ≤ N)

/-- The split search's nodes `a, …, b − 1`, `d` levels down, all pass. -/
def cosetSlice (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (d a b : ℕ) : Bool :=
  onGrp ds fun v add => sliceOK (cosetNodes v add c k lam t s d) (cosetRun v add c k lam t s) a b

/-- The search from its top and slices `[0, c₁), [c₁, c₂), …` of the nodes `d` levels down. -/
theorem cosetSearch_of_slices {ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ} {d : ℕ}
    (cuts : List ℕ) (htop : cosetTop ds c k lam t s d (lastCut 0 cuts) = true)
    (hsl : SlicesPass (cosetSlice ds c k lam t s d) (0 :: cuts)) :
    cosetSearch ds c k lam t s = true := by
  obtain ⟨hds, htop⟩ := onGrp_spec htop
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
  have e : cosetSlice ds c k lam t s d = fun a b =>
      sliceOK (cosetNodes (@Indexed.size (Grp ds) _ (Grp.indexed ds hds))
        (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)) c k lam t s d)
        (cosetRun (@Indexed.size (Grp ds) _ (Grp.indexed ds hds))
          (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)) c k lam t s) a b := by
    funext a b
    simp only [cosetSlice, onGrp, dite_eq_left hds]
  rw [e] at hsl
  simp only [cosetSearch, onGrp, dite_eq_left hds]
  exact cosetCheck_of_nodes htop.1 fun n hn =>
    all_of_slices cuts 0 hsl htop.2 n (by rwa [List.drop_zero])

/-- `n` is squarefree, by trial division. -/
def SquarefreeTD (n : ℕ) : Prop := ∀ d ∈ List.range (n + 1), 2 ≤ d → n % (d * d) ≠ 0

instance (n : ℕ) : Decidable (SquarefreeTD n) := by unfold SquarefreeTD; infer_instance

theorem SquarefreeTD.squarefree {n : ℕ} (hpos : 0 < n) (h : SquarefreeTD n) :
    Squarefree (n : ℤ) := by
  rw [Int.squarefree_natCast]
  intro x hx
  rw [Nat.isUnit_iff]
  by_contra hx1
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · obtain rfl : x = 0 := by omega
    rw [zero_mul, zero_dvd_iff] at hx
    omega
  · have hle : x ≤ n := (Nat.le_mul_self x).trans (Nat.le_of_dvd hpos hx)
    exact h x (List.mem_range.2 (by omega)) hx2 (Nat.mod_eq_zero_of_dvd hx)

/-- A row `Grp ms`, `k`, `λ` with quotient `Grp ds` (fibres of size `c`), multiplier `t` and
sign sum `s` meets C10's hypotheses (`n = k − λ > 0` prime to `|H|`; `t` prime to `|H|` and
`≡ p^f` on every factor of `ds` for each prime `p ∣ n`) and C1's (`s² = k + λ (v − 1)`). All by
trial division, for `decide +kernel`. -/
def CosetRow (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  Dvds ds ms ∧ ms.prod = c * ds.prod ∧ 0 < (k : ℤ) - lam ∧
    Nat.Coprime ds.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ds.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → ∃ f ∈ List.range ds.prod, ∀ d ∈ ds, t % d = p ^ f % d) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1)

instance (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    Decidable (CosetRow ms ds c k lam t s) := by
  unfold CosetRow; infer_instance

section C10

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
  [DecidableEq H]

/-- C10's conclusion for `D` along `φ`, `n = k − λ`: some translate of the coset sums is fixed
by every `t` prime to `|H|` that acts as a power of each prime `p ∣ n`. -/
def FixedCosetSums (n : ℤ) (φ : G →+ H) (D : G → SignType) : Prop :=
  ∃ b : H, ∀ t : ℕ, Nat.Coprime t (Fintype.card H) →
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → ∃ f : ℕ, ∀ x : H, t • x = p ^ f • x) →
      ∀ h, contract φ D (t • h + b) = contract φ D (h + b)

end C10

/-- C10 for the parameters `k`, `λ`: every SDS's coset sums along a surjection onto a group of
order prime to `n = k − λ` have a translate fixed by the multipliers (`FixedCosetSums`). -/
def C10Holds (k : ℕ) (lam : ℤ) : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : G → SignType) (φ : G →+ H) (c : ℕ), IsSDS k lam D → Function.Surjective φ →
    Fintype.card G = c * Fintype.card H → IsCoprime (Fintype.card H : ℤ) ((k : ℤ) - lam) →
    FixedCosetSums ((k : ℤ) - lam) φ D

/-- C16: C10 holds for squarefree `n`. -/
theorem c10Holds_of_squarefree {k : ℕ} {lam : ℤ} (hsq : Squarefree ((k : ℤ) - lam)) :
    C10Holds k lam := by
  intro G H _ _ _ _ _ D φ c hD hφ hc hcop
  exact hD.exists_translate_fixed_contract φ hφ hc hsq hcop

theorem maxMarked_neg (c x : ℤ) : maxMarked c (-x) = maxMarked c x := by
  unfold maxMarked
  split_ifs <;> omega

/-- A row meeting `CosetRow` whose coset search holds has no SDS, given C10 for `k`, `λ`: the
coset sums on `Grp ds` have a translate fixed by `t`, its sum is `±s` (C1), and negating turns
`−s` into `s`. -/
theorem not_hasSDS_of_cosetSearch {ms ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (hC10 : C10Holds k lam) (h : CosetRow ms ds c k lam t s)
    (hs : cosetSearch ds c k lam t s = true) (inst : Fintype (Grp ms)) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨hdv, hprod, hn, hcop, htH, hpf, hss⟩ := h
  obtain ⟨hds, hchk⟩ := onGrp_spec hs
  let _ : Fintype (Grp ds) := Grp.fintype ds hds
  have hφ := quot_surjective ms ds hdv
  have hcard : Fintype.card (Grp ms) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, Grp.card_eq, hprod]
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  have hpos : 0 < ((k : ℤ) - lam).toNat := by omega
  have hcopZ : IsCoprime (Fintype.card (Grp ds) : ℤ) ((k : ℤ) - lam) := by
    rw [Grp.card_eq, hnz]
    exact Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨b, hb⟩ := hC10 (Grp ms) (Grp ds) D (quot ms ds hdv) c hD hφ hcard hcopZ
  have hfix := hb t (by rw [Grp.card_eq]; exact htH) fun p hp hpn => by
    rw [hnz, Int.natCast_dvd_natCast] at hpn
    obtain ⟨f, -, hf⟩ := hpf p (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn)))
      (Nat.mod_eq_zero_of_dvd hpn) (isPrimeTD_of_prime hp)
    exact ⟨f, Grp.nsmul_eq_of_mod ds hf⟩
  have hfib := card_fibre_eq hφ hcard
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card (Grp ms))
      rw [hcard, h0, zero_mul] at this
      omega
    · exact h0
  set a := contract (quot ms ds hdv) D
  have hdem : Demands c k lam a :=
    { bound := fun h => by
        have := abs_contract_le (quot ms ds hdv) D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq (quot ms ds hdv), hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr (quot ms ds hdv) g hg, hfib]
      abs := hD.sum_abs_contract_le (quot ms ds hdv)
      parity := hD.sum_abs_contract_parity (quot ms ds hdv) }
  have hmm : (k : ℤ) ≤ ∑ h, maxMarked c (a h) := by
    rw [← hD.sum_marked (quot ms ds hdv)]
    refine Finset.sum_le_sum fun h _ => marked_le_maxMarked _ D h ?_
    have := marked_le_card (quot ms ds hdv) D h
    rw [hfib] at this
    exact_mod_cast this
  -- The fixed translate `a'` and its sum `±s`.
  let a' : Grp ds → ℤ := fun h => a (h + b)
  have hda : Demands c k lam a' := hdem.translate b
  have hma : (k : ℤ) ≤ ∑ h, maxMarked c (a' h) := by
    rw [Fintype.sum_equiv (Equiv.addRight b) (fun h => maxMarked c (a' h))
      (fun u => maxMarked c (a u)) fun _ => rfl]
    exact hmm
  have hta : ∀ x, a' (t • x) = a' x := hfix
  have hH1 : 1 ≤ Fintype.card (Grp ds) := Fintype.card_pos
  have hv : ((ms.prod : ℕ) : ℤ) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, hprod, Nat.cast_mul]
  have hsq : (∑ h, a' h) * (∑ h, a' h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hda.sq, Finset.sum_congr rfl fun g hg => hda.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hss,
      nsmul_eq_mul, Nat.cast_sub hH1, hv]
    push_cast
    ring
  have key : ∀ a' : Grp ds → ℤ, Demands c k lam a' → (k : ℤ) ≤ ∑ h, maxMarked c (a' h) →
      (∀ x, a' (t • x) = a' x) → ∑ h, a' h = s → False := fun a' h1 h2 h3 h4 =>
    @false_of_cosetCheck (Grp ds) _ _ (Grp.indexed ds hds) _ _ _ _ _ hchk a' h1 h2 h3 h4
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key a' hda hma hta h1
  · have hna : ∀ x, -a' (t • x) = -a' x := fun x => by rw [hta]
    have hns : ∑ h, -a' h = s := by rw [Finset.sum_neg_distrib, h1, neg_neg]
    exact key (fun h => -a' h) hda.neg (by simpa only [maxMarked_neg] using hma) hna hns

/-- A row through C16 (squarefree `n`, by trial division): no SDS when `CosetRow` and the coset
search hold. -/
theorem not_hasSDS_of_cosetRow {ms ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (hsq : SquarefreeTD ((k : ℤ) - lam).toNat) (h : CosetRow ms ds c k lam t s)
    (hs : cosetSearch ds c k lam t s = true) (inst : Fintype (Grp ms)) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  have hn := h.2.2.1
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  refine not_hasSDS_of_cosetSearch (c10Holds_of_squarefree ?_) h hs inst
  rw [hnz]
  exact hsq.squarefree (by omega)

end SignedDifferenceSets
