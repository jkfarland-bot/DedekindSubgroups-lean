module

public import DedekindSubgroups

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `DedekindSubgroups/`. The definitions `sawtooth`, `dedekindSum`,
`sig`, `inv` and `subgroupSum` used in the statements come from that development and are
compared with the copies in `Challenge.lean`.
-/

open Finset

namespace DedekindSubgroups

section Subgroups

variable {k : ℕ} [NeZero k]

/-- **Theorem 1.1.** For a subgroup `H` of odd order of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer
congruent to `|H| (k-1)(k-2)` modulo `16`. -/
theorem theorem_1_1 (hk : 1 < k) (H : Subgroup (ZMod k)ˣ)
    (hodd : Odd (Nat.card H)) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] :=
  twelve_mul_subgroupSum_modEq hk H hodd

open Classical in
/-- **Remark 3.4.** For every subgroup `H` of `(ℤ/kℤ)ˣ`, `12 k S(H,k)` is an integer congruent to
`|H|(k-1)(k-2) - 4 ∑_{h ∈ H, h² = 1} I(h,k)` modulo `8`. -/
theorem remark_3_4 (hk : 1 < k) (H : Subgroup (ZMod k)ˣ) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2))
        - 4 * ∑ u ∈ (univ.filter (· ∈ H)).filter (fun u => u * u = 1),
            (inv (u : ZMod k).val k : ℤ) [ZMOD 8] :=
  twelve_mul_subgroupSum_modEq_eight hk H

end Subgroups

/-- **Optimality in Theorem 1.1.** Two subgroups of order `3` of `(ℤ/63ℤ)ˣ` whose values of
`12 k S(H,k)` are incongruent modulo `32`; so no congruence modulo `32` whose right-hand side depends
only on `k` and `n` can hold. -/
theorem theorem_1_1_optimal :
    ∃ H₁ H₂ : Subgroup (ZMod 63)ˣ, Nat.card H₁ = 3 ∧ Nat.card H₂ = 3 ∧
      12 * (63 : ℚ) * subgroupSum H₁ = 5586 ∧ 12 * (63 : ℚ) * subgroupSum H₂ = 4290 ∧
      ¬ ((5586 : ℤ) ≡ 4290 [ZMOD 32]) :=
  modulus_sixteen_optimal

/-- **Corollary 4.1.** If `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k) ∈ ℤ` and
`2 k S(H,k) ≡ 3 n (k-1)(k-2)/2 (mod 8)`. -/
theorem corollary_4_1 {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ 3 * (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] :=
  two_mul_k_subgroupSum_modEq hk h3 H hodd

/-- **Theorem 1.2.** For a prime `p > 3` and a subgroup `H` of `(ℤ/pℤ)ˣ` of odd order `n > 1`,
`2 S(H,p)` is an integer congruent to `n (p-1)/2` modulo `8`. -/
theorem theorem_1_2 {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] :=
  two_mul_subgroupSum_prime hp3 H hodd hn

/-- **Theorem 1.2, Louboutin's normalization.** In the setting of `theorem_1_2`,
`N(H,p) = 12 S(H,p) - p` is an integer congruent to `3 n (p-1) - p` modulo `48`. -/
theorem theorem_1_2_louboutin {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ N : ℤ, (N : ℚ) = 12 * subgroupSum H - p ∧
      N ≡ 3 * (Nat.card H : ℤ) * ((p : ℤ) - 1) - p [ZMOD 48] :=
  louboutin_N_modEq hp3 H hodd hn

end DedekindSubgroups
