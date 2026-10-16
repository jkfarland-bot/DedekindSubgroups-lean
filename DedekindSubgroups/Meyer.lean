/-
  Meyer's formula `12 k s(h,k) = (k-1)(k-2) - 4 I(h,k)`.
-/
import DedekindSubgroups.Basic

open Finset

namespace DedekindSubgroups

/-- `σ_h(z) = h z mod k`, as a natural number. -/
def sig (h k z : ℕ) : ℕ := h * z % k

/-- The number of inversions of `z ↦ h z mod k` on `{0, …, k-1}`:
pairs `x < y < k` with `σ(y) < σ(x)`. (Pairs with `x = 0` never count, since `σ(0) = 0`.) -/
def inv (h k : ℕ) : ℕ :=
  ∑ y ∈ range k, ∑ x ∈ range y, if sig h k y < sig h k x then 1 else 0

/-- The basic pointwise identity: for `x ≤ y`,
`σ(y) - σ(x) = σ(y - x) - k [σ(y) < σ(x)]`. -/
theorem sig_sub (h k x y : ℕ) (hk : 0 < k) (hxy : x ≤ y) :
    (sig h k y : ℤ) - sig h k x
      = sig h k (y - x) - k * (if sig h k y < sig h k x then 1 else 0) := by
  unfold sig
  set A := h * y
  set B := h * x
  have hAB : h * (y - x) = A - B := Nat.mul_sub h y x
  have hBA : B ≤ A := Nat.mul_le_mul_left h hxy
  rw [hAB]
  have eA := Nat.div_add_mod A k
  have eB := Nat.div_add_mod B k
  have eC := Nat.div_add_mod (A - B) k
  have lA := Nat.mod_lt A hk
  have lB := Nat.mod_lt B hk
  have lC := Nat.mod_lt (A - B) hk
  -- integer version of the three divisions
  have key : ((A % k : ℕ) : ℤ) - (B % k : ℕ) - ((A - B) % k : ℕ)
      = (k : ℤ) * (((A - B) / k : ℕ) - (A / k : ℕ) + (B / k : ℕ)) := by
    have : ((A : ℕ) : ℤ) - (B : ℕ) = ((A - B : ℕ) : ℤ) := by push_cast [hBA]; ring
    have eA' : ((k * (A / k) + A % k : ℕ) : ℤ) = (A : ℤ) := by exact_mod_cast eA
    have eB' : ((k * (B / k) + B % k : ℕ) : ℤ) = (B : ℤ) := by exact_mod_cast eB
    have eC' : ((k * ((A - B) / k) + (A - B) % k : ℕ) : ℤ) = ((A - B : ℕ) : ℤ) := by exact_mod_cast eC
    simp only [Nat.cast_add, Nat.cast_mul] at eA' eB' eC'
    linarith
  set t : ℤ := ((A - B) / k : ℕ) - (A / k : ℕ) + (B / k : ℕ)
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have lA' : ((A % k : ℕ) : ℤ) < k := by exact_mod_cast lA
  have lB' : ((B % k : ℕ) : ℤ) < k := by exact_mod_cast lB
  have lC' : (((A - B) % k : ℕ) : ℤ) < k := by exact_mod_cast lC
  have nA : (0 : ℤ) ≤ ((A % k : ℕ) : ℤ) := by positivity
  have nB : (0 : ℤ) ≤ ((B % k : ℕ) : ℤ) := by positivity
  have nC : (0 : ℤ) ≤ (((A - B) % k : ℕ) : ℤ) := by positivity
  split_ifs with hlt
  · -- σ(y) < σ(x): the multiple of k is -k
    have hlt' : ((A % k : ℕ) : ℤ) < (B % k : ℕ) := by exact_mod_cast hlt
    have ht1 : t < 0 := by
      by_contra hc
      push Not at hc
      have : (0 : ℤ) ≤ (k : ℤ) * t := mul_nonneg hk'.le hc
      linarith
    have ht2 : -1 ≤ t := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * t ≤ (k : ℤ) * (-2) := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have : t = -1 := by omega
    rw [this] at key
    linarith
  · have hge : ((B % k : ℕ) : ℤ) ≤ (A % k : ℕ) := by
      exact_mod_cast (not_lt.mp hlt)
    have ht1 : t ≤ 0 := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * 1 ≤ (k : ℤ) * t := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have ht2 : 0 ≤ t := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * t ≤ (k : ℤ) * (-1) := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have : t = 0 := by omega
    rw [this, mul_zero] at key
    linarith

/-- Meyer's identity in integer form, valid for every `h`:
`k · I(h,k) = ∑_{r<k} (2k - 1 - 3r) σ(r)`. -/
theorem meyer_int (h k : ℕ) (hk : 0 < k) :
    (k : ℤ) * inv h k = ∑ r ∈ range k, (2 * (k : ℤ) - 1 - 3 * r) * sig h k r := by
  -- sum the pointwise identity over all pairs x < y < k
  have hpair : ∀ y ∈ range k, ∀ x ∈ range y,
      (k : ℤ) * (if sig h k y < sig h k x then 1 else 0)
        = (sig h k (y - x) : ℤ) - ((sig h k y : ℤ) - sig h k x) := by
    intro y _ x hx
    have := sig_sub h k x y hk (le_of_lt (mem_range.mp hx))
    linarith
  have h0 : sig h k 0 = 0 := by simp [sig]
  calc (k : ℤ) * inv h k
      = ∑ y ∈ range k, ∑ x ∈ range y, (k : ℤ) * (if sig h k y < sig h k x then 1 else 0) := by
        unfold inv; push_cast; rw [mul_sum]; refine sum_congr rfl ?_; intro y _; rw [mul_sum]
    _ = ∑ y ∈ range k, ∑ x ∈ range y,
          ((sig h k (y - x) : ℤ) - ((sig h k y : ℤ) - sig h k x)) := by
        refine sum_congr rfl ?_; intro y hy; refine sum_congr rfl ?_; intro x hx
        exact hpair y hy x hx
    _ = ∑ y ∈ range k, ∑ x ∈ range y, (sig h k (y - x) : ℤ)
          - ∑ y ∈ range k, ∑ _x ∈ range y, (sig h k y : ℤ)
          + ∑ y ∈ range k, ∑ x ∈ range y, (sig h k x : ℤ) := by
        simp only [← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl ?_; intro y _; refine sum_congr rfl ?_; intro x _; ring
    _ = ∑ u ∈ range k, ((k : ℤ) - u) * sig h k u
          - ∑ y ∈ range k, (y : ℤ) * sig h k y
          + ∑ x ∈ range k, ((k : ℤ) - 1 - x) * sig h k x := by
        rw [sum_pairs_diff (fun z => (sig h k z : ℤ)) (by simp [h0]) k,
          sum_pairs_right (fun z => (sig h k z : ℤ)) k, sum_pairs_left (fun z => (sig h k z : ℤ)) k]
    _ = ∑ r ∈ range k, (2 * (k : ℤ) - 1 - 3 * r) * sig h k r := by
        simp only [← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl ?_; intro r _; ring



/-! ### From inversions to the Dedekind sum -/

section Residue

variable {h h' k : ℕ}

theorem one_lt_of_inv (hk : 0 < k) (hinv : h * h' % k = 1) : 1 < k := by
  by_contra hc
  have : k = 1 := by omega
  subst this
  rw [Nat.mod_one] at hinv
  exact absurd hinv (by norm_num)

/-- Multiplication by an invertible `h` permutes `{0, …, k-1}`. -/
theorem sum_sig_perm {M : Type*} [AddCommMonoid M] (hk : 0 < k) (hinv : h * h' % k = 1)
    (f : ℕ → M) : ∑ r ∈ range k, f (sig h k r) = ∑ r ∈ range k, f r := by
  have back : ∀ r < k, h' * (h * r % k) % k = r := by
    intro r hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  have forth : ∀ r < k, h * (h' * r % k) % k = r := by
    intro r hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  refine Finset.sum_nbij' (fun r => h * r % k) (fun r => h' * r % k) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact mem_range.mpr (Nat.mod_lt _ hk)
  · intro r _; exact mem_range.mpr (Nat.mod_lt _ hk)
  · intro r hr; exact back r (by simpa using hr)
  · intro r hr; exact forth r (by simpa using hr)
  · intro r _; rfl

theorem sig_ne_zero (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sig h k r ≠ 0 := by
  intro hz
  have : h' * (h * r % k) % k = r := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hrk]
  unfold sig at hz
  rw [hz, mul_zero, Nat.zero_mod] at this
  omega

theorem sawtooth_div_of_lt {r k : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast lt_trans hr0 hrk
  have hfr : Int.fract ((r : ℚ) / k) = (r : ℚ) / k := by
    rw [Int.fract_eq_self]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hk]; exact_mod_cast hrk
  have hne : (r : ℚ) / k ≠ 0 := by
    have : (0 : ℚ) < r := by exact_mod_cast hr0
    positivity
  simp [sawtooth, hfr, hne]

theorem sawtooth_mul_div (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((h * r : ℚ) / k) = (sig h k r : ℚ) / k - 1 / 2 := by
  have hk1 := one_lt_of_inv (lt_trans hr0 hrk) hinv
  have hk : (0 : ℚ) < k := by exact_mod_cast (lt_trans Nat.zero_lt_one hk1)
  have hsplit : (h * r : ℚ) / k = ((h * r / k : ℕ) : ℚ) + (sig h k r : ℚ) / k := by
    have e := Nat.div_add_mod (h * r) k
    have e' : ((h * r : ℕ) : ℚ) = (k : ℚ) * ((h * r / k : ℕ) : ℚ) + ((h * r % k : ℕ) : ℚ) := by
      exact_mod_cast e.symm
    unfold sig
    field_simp
    push_cast at e' ⊢
    linarith
  have hlt : sig h k r < k := Nat.mod_lt _ (lt_trans Nat.zero_lt_one hk1)
  have hpos : 0 < sig h k r := Nat.pos_of_ne_zero (sig_ne_zero hinv hr0 hrk)
  have hs := sawtooth_div_of_lt hpos hlt
  unfold sawtooth at hs ⊢
  rw [hsplit, Int.fract_natCast_add]
  exact hs

theorem sum_range_cast_id (k : ℕ) : (∑ r ∈ range k, (r : ℚ)) = (k : ℚ) * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The residue form `s(h,k) = k⁻² ∑_r r σ(r) - (k-1)/4`. -/
theorem dedekindSum_residue (hk : 0 < k) (hinv : h * h' % k = 1) :
    dedekindSum h k = (∑ r ∈ range k, (r : ℚ) * sig h k r) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by
  have hk1 := one_lt_of_inv hk hinv
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h0 : sig h k 0 = 0 := by simp [sig]
  have hterm : ∀ r ∈ range k,
      sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)
        = (r : ℚ) * sig h k r / (k : ℚ) ^ 2 - (sig h k r : ℚ) / (2 * k) - (r : ℚ) / (2 * k) + 1 / 4
          - (if r = 0 then 1 / 4 else 0) := by
    intro r hr
    rw [mem_range] at hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [sawtooth, h0]
    · rw [sawtooth_div_of_lt hr0 hr, sawtooth_mul_div hinv hr0 hr, ite_eq_right hr0.ne']
      field_simp
      ring
  unfold dedekindSum
  rw [sum_congr rfl hterm]
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul,
    sum_ite_eq', mem_range, ite_eq_left hk]
  have hS : (∑ r ∈ range k, (sig h k r : ℚ)) = ∑ r ∈ range k, (r : ℚ) :=
    sum_sig_perm hk hinv (fun z => (z : ℚ))
  rw [hS, sum_range_cast_id]
  field_simp
  ring

/-- **Meyer's formula**: `12 k s(h,k) = (k-1)(k-2) - 4 I(h,k)`. -/
theorem meyer (hk : 0 < k) (hinv : h * h' % k = 1) :
    12 * (k : ℚ) * dedekindSum h k = ((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * inv h k := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hM := congrArg (fun z : ℤ => (z : ℚ)) (meyer_int h k hk)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_sub, Int.cast_ofNat,
    Int.cast_one] at hM
  have hsplit : ∑ r ∈ range k, (2 * (k : ℚ) - 1 - 3 * r) * (sig h k r : ℚ)
      = (2 * (k : ℚ) - 1) * ∑ r ∈ range k, (sig h k r : ℚ) - 3 * ∑ r ∈ range k, (r : ℚ) * sig h k r := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl ?_; intro r _; ring
  have hS : (∑ r ∈ range k, (sig h k r : ℚ)) = ∑ r ∈ range k, (r : ℚ) :=
    sum_sig_perm hk hinv (fun z => (z : ℚ))
  rw [hsplit, hS, sum_range_cast_id] at hM
  rw [dedekindSum_residue hk hinv]
  field_simp
  linear_combination (16 : ℚ) * hM

end Residue

end DedekindSubgroups
