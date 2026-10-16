module

public import Mathlib

public section

/-!
# A congruence modulo 16 for sums of Dedekind sums over subgroups of odd order

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each headline result with
`sorry`. `Solution.lean` proves every statement below with the same name and type, using the
proof development in `DedekindSubgroups/`.

## Objects

* `sawtooth x` is the sawtooth function `((x))`: `x - ⌊x⌋ - 1/2` when `x ∉ ℤ`, and `0` when
  `x ∈ ℤ`.
* `dedekindSum h k` is the classical Dedekind sum `s(h,k) = ∑_{r mod k} ((r/k)) ((hr/k))`,
  with `h` and `k` natural numbers.
* For a subgroup `H` of `(ℤ/kℤ)ˣ`, `subgroupSum H` is `S(H,k) = ∑_{h ∈ H} s(h,k)`, where each
  unit is represented by its least nonnegative residue `(u : ZMod k).val`.
* `sig h k z = h z mod k`, and `inv h k` is the number of inversions of `z ↦ h z mod k` on
  `{0, …, k-1}`: pairs `x < y < k` with `h y mod k < h x mod k`.

## Results

* `theorem_1_1` (Theorem 1.1): if `H` has odd order `n`, then `12 k S(H,k)` is an integer
  congruent to `n (k-1)(k-2)` modulo `16`.
* `theorem_1_1_optimal`: the modulus `16` cannot be raised to `32`; two subgroups of order `3`
  of `(ℤ/63ℤ)ˣ` give values of `12 · 63 · S(H,63)` that are incongruent modulo `32`.
* `remark_3_4` (Remark 3.4): for every subgroup `H`, `12 k S(H,k)` is an integer congruent to
  `|H| (k-1)(k-2) - 4 ∑_{h ∈ H, h² = 1} I(h,k)` modulo `8`.
* `corollary_4_1` (Corollary 4.1): if `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k)` is an
  integer `x` with `2x ≡ 3 n (k-1)(k-2)` modulo `16`.
* `theorem_1_2` (Theorem 1.2): for a prime `p > 3` and a subgroup `H` of odd order `n > 1`,
  `2 S(H,p)` is an integer congruent to `n (p-1)/2` modulo `8`.
* `theorem_1_2_louboutin`: in the same setting, `N(H,p) = 12 S(H,p) - p` is an integer
  congruent to `3 n (p-1) - p` modulo `48`.
-/

open Finset

namespace DedekindSubgroups

/-- The sawtooth function `((x))`: `x - ⌊x⌋ - 1/2` if `x ∉ ℤ`, and `0` if `x ∈ ℤ`. -/
noncomputable def sawtooth (x : ℚ) : ℚ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The Dedekind sum `s(h,k) = ∑_{r mod k} ((r/k)) ((hr/k))`. -/
noncomputable def dedekindSum (h k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)

/-- `σ_h(z) = h z mod k`, as a natural number. -/
def sig (h k z : ℕ) : ℕ := h * z % k

/-- The number of inversions of `z ↦ h z mod k` on `{0, …, k-1}`:
pairs `x < y < k` with `σ(y) < σ(x)`. (Pairs with `x = 0` never count, since `σ(0) = 0`.) -/
def inv (h k : ℕ) : ℕ :=
  ∑ y ∈ range k, ∑ x ∈ range y, if sig h k y < sig h k x then 1 else 0

section Subgroups

variable {k : ℕ} [NeZero k]

/-- `S(H,k) = ∑_{h ∈ H} s(h,k)`. -/
noncomputable def subgroupSum (H : Subgroup (ZMod k)ˣ) : ℚ := by
  classical exact ∑ u ∈ univ.filter (· ∈ H), dedekindSum (u : ZMod k).val k

/-- **Theorem 1.1.** For a subgroup `H` of odd order of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer
congruent to `|H| (k-1)(k-2)` modulo `16`. -/
theorem theorem_1_1 (hk : 1 < k) (H : Subgroup (ZMod k)ˣ)
    (hodd : Odd (Nat.card H)) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by
  sorry

open Classical in
/-- **Remark 3.4.** For every subgroup `H` of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer congruent to
`|H|(k-1)(k-2) - 4 ∑_{h ∈ H, h² = 1} I(h,k)` modulo `8`. -/
theorem remark_3_4 (hk : 1 < k) (H : Subgroup (ZMod k)ˣ) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2))
        - 4 * ∑ u ∈ (univ.filter (· ∈ H)).filter (fun u => u * u = 1),
            (inv (u : ZMod k).val k : ℤ) [ZMOD 8] := by
  sorry

end Subgroups

/-- **Optimality in Theorem 1.1.** Two subgroups of order `3` of `(ℤ/63ℤ)ˣ` whose values of
`12 k S(H,k)` are incongruent modulo `32`; so no congruence modulo `32` whose right-hand side depends
only on `k` and `n` can hold. -/
theorem theorem_1_1_optimal :
    ∃ H₁ H₂ : Subgroup (ZMod 63)ˣ, Nat.card H₁ = 3 ∧ Nat.card H₂ = 3 ∧
      12 * (63 : ℚ) * subgroupSum H₁ = 5586 ∧ 12 * (63 : ℚ) * subgroupSum H₂ = 4290 ∧
      ¬ ((5586 : ℤ) ≡ 4290 [ZMOD 32]) := by
  sorry

/-- **Corollary 4.1.** If `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k) ∈ ℤ` and
`2 k S(H,k) ≡ 3 n (k-1)(k-2)/2 (mod 8)`. -/
theorem corollary_4_1 {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ 3 * (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by
  sorry

/-- **Theorem 1.2.** For a prime `p > 3` and a subgroup `H` of `(ℤ/pℤ)ˣ` of odd order `n > 1`,
`2 S(H,p)` is an integer congruent to `n (p-1)/2` modulo `8`. -/
theorem theorem_1_2 {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] := by
  sorry

/-- **Theorem 1.2, Louboutin's normalization.** In the setting of `theorem_1_2`,
`N(H,p) = 12 S(H,p) - p` is an integer congruent to `3 n (p-1) - p` modulo `48`. -/
theorem theorem_1_2_louboutin {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ N : ℤ, (N : ℚ) = 12 * subgroupSum H - p ∧
      N ≡ 3 * (Nat.card H : ℤ) * ((p : ℤ) - 1) - p [ZMOD 48] := by
  sorry

end DedekindSubgroups
