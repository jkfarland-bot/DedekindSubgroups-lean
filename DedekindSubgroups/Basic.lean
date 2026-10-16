module

/-
  Dedekind sums over subgroups: basic definitions and finite-sum identities.
  Formalization accompanying J. S. Farland, "A congruence modulo 16 for sums of Dedekind sums
  over subgroups of odd order".
-/
public import Mathlib

@[expose] public section

open Finset

namespace DedekindSubgroups

/-- The sawtooth function `((x))`: `x - ⌊x⌋ - 1/2` if `x ∉ ℤ`, and `0` if `x ∈ ℤ`. -/
noncomputable def sawtooth (x : ℚ) : ℚ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The Dedekind sum `s(h,k) = ∑_{r mod k} ((r/k)) ((hr/k))`. -/
noncomputable def dedekindSum (h k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)

/-! ### Generic identities for sums over pairs `x < y < m` -/

/-- `∑_{x<y} f (y - x) = ∑_{j<y} f (j + 1)`. -/
theorem sum_range_sub_reflect (f : ℕ → ℤ) (y : ℕ) :
    ∑ x ∈ range y, f (y - x) = ∑ j ∈ range y, f (j + 1) := by
  rw [← Finset.sum_range_reflect (fun j => f (j + 1)) y]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp only [mem_range] at hx
  congr 1
  omega

/-- `∑_{y<m} ∑_{x<y} f x = ∑_{x<m} (m-1-x) f x`. -/
theorem sum_pairs_left (f : ℕ → ℤ) (m : ℕ) :
    ∑ y ∈ range m, ∑ x ∈ range y, f x = ∑ x ∈ range m, ((m : ℤ) - 1 - x) * f x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ, ← sum_add_distrib]
    push_cast
    have : ((m : ℤ) + 1 - 1 - m) * f m = 0 := by ring
    rw [this, add_zero]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring

/-- `∑_{y<m} ∑_{x<y} g y = ∑_{y<m} y g y`. -/
theorem sum_pairs_right (g : ℕ → ℤ) (m : ℕ) :
    ∑ y ∈ range m, ∑ _x ∈ range y, g y = ∑ y ∈ range m, (y : ℤ) * g y := by
  refine Finset.sum_congr rfl ?_
  intro y _
  simp [sum_const, card_range]

/-- `∑_{y<m} ∑_{x<y} f (y - x) = ∑_{u<m} (m-u) f u`, assuming `f 0 = 0`. -/
theorem sum_pairs_diff (f : ℕ → ℤ) (hf : f 0 = 0) (m : ℕ) :
    ∑ y ∈ range m, ∑ x ∈ range y, f (y - x) = ∑ u ∈ range m, ((m : ℤ) - u) * f u := by
  have h1 : ∀ y, ∑ x ∈ range y, f (y - x) = ∑ j ∈ range y, f (j + 1) :=
    fun y => sum_range_sub_reflect f y
  simp_rw [h1]
  rw [sum_pairs_left (fun j => f (j + 1)) m]
  -- shift the index `u = j + 1`
  have h2 : ∑ u ∈ range (m + 1), ((m : ℤ) - u) * f u
      = ∑ j ∈ range m, ((m : ℤ) - 1 - j) * f (j + 1) := by
    rw [sum_range_succ']
    simp only [hf, mul_zero, add_zero]
    refine Finset.sum_congr rfl ?_
    intro j _
    push_cast
    ring
  rw [← h2, sum_range_succ]
  simp

end DedekindSubgroups
