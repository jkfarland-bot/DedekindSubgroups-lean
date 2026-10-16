/-
  Optimality of the modulus 16 in Theorem 1.1: the subgroups `⟨4⟩ = {1, 4, 16}` and
  `⟨22⟩ = {1, 22, 43}` of `(ℤ/63ℤ)ˣ` both have order 3, and `12·63·S(H,63)` equals `5586` and `4290`,
  which are incongruent modulo 32.
-/
import DedekindSubgroups.Prime

open Finset

namespace DedekindSubgroups

theorem subgroupSum_eq_of_mem_iff {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ)
    (t : Finset (ZMod k)ˣ) (ht : ∀ x, x ∈ H ↔ x ∈ t) :
    subgroupSum H = ∑ u ∈ t, dedekindSum (u : ZMod k).val k := by
  classical
  unfold subgroupSum
  congr 1
  ext x
  simp [ht]

/-- `4` as a unit modulo `63` (inverse `16`). -/
def u4 : (ZMod 63)ˣ := ⟨4, 16, by decide, by decide⟩

/-- `22` as a unit modulo `63` (inverse `43`). -/
def u22 : (ZMod 63)ˣ := ⟨22, 43, by decide, by decide⟩

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem orderOf_u4 : orderOf u4 = 3 := orderOf_eq_prime (by decide) (by decide)

theorem orderOf_u22 : orderOf u22 = 3 := orderOf_eq_prime (by decide) (by decide)

theorem mem_zpowers_of_orderOf_three {u x : (ZMod 63)ˣ} (hu : orderOf u = 3) :
    x ∈ Subgroup.zpowers u ↔ x ∈ ({1, u, u ^ 2} : Finset (ZMod 63)ˣ) := by
  rw [mem_zpowers_iff_mem_range_orderOf, hu]
  simp only [mem_image, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (h | h | h) <;> rw [h]
    · exact ⟨0, by norm_num, pow_zero u⟩
    · exact ⟨1, by norm_num, pow_one u⟩
    · exact ⟨2, by norm_num, rfl⟩

set_option maxRecDepth 100000 in
theorem inv_values : inv 4 63 = 720 ∧ inv 16 63 = 720 ∧ inv 22 63 = 882 ∧ inv 43 63 = 882 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem twelve_k_subgroupSum_u4 : 12 * (63 : ℚ) * subgroupSum (Subgroup.zpowers u4) = 5586 := by
  rw [subgroupSum_eq_of_mem_iff _ _ (fun x => mem_zpowers_of_orderOf_three orderOf_u4)]
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have v1 : ((1 : (ZMod 63)ˣ) : ZMod 63).val = 1 := rfl
  have v2 : ((u4 : (ZMod 63)ˣ) : ZMod 63).val = 4 := rfl
  have v3 : ((u4 ^ 2 : (ZMod 63)ˣ) : ZMod 63).val = 16 := rfl
  rw [v1, v2, v3]
  have m1 := meyer (h := 1) (h' := 1) (k := 63) (by norm_num) (by norm_num)
  have m2 := meyer (h := 4) (h' := 16) (k := 63) (by norm_num) (by norm_num)
  have m3 := meyer (h := 16) (h' := 4) (k := 63) (by norm_num) (by norm_num)
  obtain ⟨i4, i16, -, -⟩ := inv_values
  rw [inv_one_eq_zero] at m1
  rw [i4] at m2
  rw [i16] at m3
  push_cast at m1 m2 m3
  linear_combination m1 + m2 + m3

theorem twelve_k_subgroupSum_u22 : 12 * (63 : ℚ) * subgroupSum (Subgroup.zpowers u22) = 4290 := by
  rw [subgroupSum_eq_of_mem_iff _ _ (fun x => mem_zpowers_of_orderOf_three orderOf_u22)]
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have v1 : ((1 : (ZMod 63)ˣ) : ZMod 63).val = 1 := rfl
  have v2 : ((u22 : (ZMod 63)ˣ) : ZMod 63).val = 22 := rfl
  have v3 : ((u22 ^ 2 : (ZMod 63)ˣ) : ZMod 63).val = 43 := rfl
  rw [v1, v2, v3]
  have m1 := meyer (h := 1) (h' := 1) (k := 63) (by norm_num) (by norm_num)
  have m2 := meyer (h := 22) (h' := 43) (k := 63) (by norm_num) (by norm_num)
  have m3 := meyer (h := 43) (h' := 22) (k := 63) (by norm_num) (by norm_num)
  obtain ⟨-, -, i22, i43⟩ := inv_values
  rw [inv_one_eq_zero] at m1
  rw [i22] at m2
  rw [i43] at m3
  push_cast at m1 m2 m3
  linear_combination m1 + m2 + m3

/-- **Optimality in Theorem 1.1.** Two subgroups of order `3` of `(ℤ/63ℤ)ˣ` whose values of
`12 k S(H,k)` are incongruent modulo `32`; so no congruence modulo `32` whose right-hand side depends
only on `k` and `n` can hold. -/
theorem modulus_sixteen_optimal :
    ∃ H₁ H₂ : Subgroup (ZMod 63)ˣ, Nat.card H₁ = 3 ∧ Nat.card H₂ = 3 ∧
      12 * (63 : ℚ) * subgroupSum H₁ = 5586 ∧ 12 * (63 : ℚ) * subgroupSum H₂ = 4290 ∧
      ¬ ((5586 : ℤ) ≡ 4290 [ZMOD 32]) :=
  ⟨Subgroup.zpowers u4, Subgroup.zpowers u22, by rw [Nat.card_zpowers, orderOf_u4],
    by rw [Nat.card_zpowers, orderOf_u22], twelve_k_subgroupSum_u4, twelve_k_subgroupSum_u22,
    by decide⟩

end DedekindSubgroups
