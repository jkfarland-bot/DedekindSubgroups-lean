module

/-
  Moduli prime to 3, and prime moduli.

  * `two_mul_dedekindSum_int` : if `3 ∤ k` then `2 k s(h,k) ∈ ℤ` (Lemma 2.3).
  * `E_modp` : for a prime `p > 3`, `∑_r r σ_h(r) = p e` with `12 e ≡ h + h̄ (mod p)` (Lemma 4.2).
  * `two_mul_k_subgroupSum_modEq` : Corollary 4.1.
  * `two_mul_subgroupSum_prime` : Theorem 1.2, `2 S(H,p) ∈ ℤ` and `2 S(H,p) ≡ n (p-1)/2 (mod 8)`.
  * `louboutin_N_modEq` : `N(H,p) = 12 S(H,p) - p ≡ 3 n (p-1) - p (mod 48)`.
-/
public import DedekindSubgroups.Main

@[expose] public section

open Finset

namespace DedekindSubgroups

/-- `6 ∑_{r<m} r² = m (m-1) (2m-1)`. -/
theorem six_mul_sum_sq (m : ℕ) :
    6 * ∑ r ∈ range m, (r : ℤ) ^ 2 = (m : ℤ) * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- `E(h,k) = ∑_{r<k} r σ_h(r)`, as an integer. -/
def E (h k : ℕ) : ℤ := ∑ r ∈ range k, (r : ℤ) * sig h k r

theorem E_cast (h k : ℕ) : ((E h k : ℤ) : ℚ) = ∑ r ∈ range k, (r : ℚ) * sig h k r := by
  unfold E; push_cast; rfl

/-- `σ_h(r) = h r - k ⌊h r / k⌋`. -/
theorem sig_eq_sub (h k r : ℕ) :
    (sig h k r : ℤ) = h * r - k * ((h * r / k : ℕ) : ℤ) := by
  unfold sig
  have h1 := Nat.div_add_mod (h * r) k
  have h2 : ((k * (h * r / k) + h * r % k : ℕ) : ℤ) = ((h * r : ℕ) : ℤ) := by rw [h1]
  simp only [Nat.cast_add, Nat.cast_mul] at h2
  linear_combination h2

/-- `E(h,k) = h ∑ r² - k ∑ r q_r`, where `q_r = ⌊h r / k⌋`. -/
theorem E_eq (h k : ℕ) :
    E h k = h * ∑ r ∈ range k, (r : ℤ) ^ 2 - k * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ) := by
  unfold E
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun r _ => ?_)
  rw [sig_eq_sub]; ring

/-- `12 ≠ 0` in `ZMod p` for a prime `p > 3`. -/
theorem twelve_ne_zero {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p) : (12 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 12 := by
    have : ((12 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  have hpr := hp.out
  rcases (Nat.Prime.dvd_mul hpr).mp (show p ∣ 4 * 3 from hdvd) with h4 | h3
  · rcases (Nat.Prime.dvd_mul hpr).mp (show p ∣ 2 * 2 from h4) with h2 | h2 <;>
      · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega

section Residue

variable {h h' k : ℕ}

/-- `2 h E = (h² + 1) ∑ r² - k² ∑ q_r²`. -/
theorem two_h_E (hk : 0 < k) (hinv : h * h' % k = 1) :
    2 * (h : ℤ) * E h k = ((h : ℤ) ^ 2 + 1) * ∑ r ∈ range k, (r : ℤ) ^ 2
      - (k : ℤ) ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 := by
  have hsq : ∑ r ∈ range k, (sig h k r : ℤ) ^ 2 = ∑ r ∈ range k, (r : ℤ) ^ 2 :=
    sum_sig_perm hk hinv (fun z => (z : ℤ) ^ 2)
  have hQ : ∑ r ∈ range k, (sig h k r : ℤ) ^ 2
      = (h : ℤ) ^ 2 * ∑ r ∈ range k, (r : ℤ) ^ 2
        - 2 * h * k * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ)
        + (k : ℤ) ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun r _ => ?_)
    rw [sig_eq_sub]; ring
  rw [E_eq]
  linear_combination hsq - hQ

/-- **Lemma 2.3.** If `3 ∤ k`, then `k ∣ 2 E(h,k)`, hence `2 k s(h,k) ∈ ℤ`. -/
theorem k_dvd_two_E (h3 : ¬ 3 ∣ k) : (k : ℤ) ∣ 2 * E h k := by
  have hcop : IsCoprime (k : ℤ) 3 := by
    have : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    exact Nat.isCoprime_iff_coprime.mpr this.symm
  have hQ : (k : ℤ) ∣ 2 * ∑ r ∈ range k, (r : ℤ) ^ 2 := by
    refine hcop.dvd_of_dvd_mul_left ⟨(k - 1) * (2 * k - 1), ?_⟩
    linear_combination six_mul_sum_sq k
  rw [E_eq]
  obtain ⟨c, hc⟩ := hQ
  exact ⟨h * c - 2 * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ), by linear_combination h * hc⟩

theorem two_mul_dedekindSum_int (hk : 0 < k) (hinv : h * h' % k = 1) (h3 : ¬ 3 ∣ k) :
    ∃ c : ℤ, (c : ℚ) = 2 * k * dedekindSum h k := by
  obtain ⟨c, hc⟩ := k_dvd_two_E (h := h) h3
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self ((k : ℤ) - 1)
  refine ⟨c - j, ?_⟩
  rw [dedekindSum_residue hk hinv, ← E_cast]
  have hc' : (2 : ℚ) * E h k = k * c := by exact_mod_cast hc
  have hj' : ((k : ℚ) - 1) * ((k : ℚ) - 1 + 1) = j + j := by exact_mod_cast hj
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [show (2 : ℚ) * k * ((E h k : ℚ) / k ^ 2 - ((k : ℚ) - 1) / 4)
      = (2 * E h k) / k - ((k : ℚ) - 1) * ((k : ℚ) - 1 + 1) / 2 by field_simp; ring, hc', hj']
  field_simp
  ring

/-- **Lemma 4.2.** For a prime `p > 3` and `h h̄ ≡ 1 (mod p)`, `E(h,p) = p e` with
`12 e ≡ h + h̄ (mod p)`. Equivalently `y_h = 2 p s(h,p)` is an integer with `6 y_h ≡ h + h̄`. -/
theorem E_modp {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p) (hinv : h * h' % p = 1) :
    ∃ e : ℤ, E h p = p * e ∧ (((12 * e : ℤ)) : ZMod p) = (h : ZMod p) + (h' : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  have h12 : (12 : ZMod p) ≠ 0 := twelve_ne_zero hp3
  have hhh : (h : ZMod p) * (h' : ZMod p) = 1 := by
    have : ((h * h' % p : ℕ) : ZMod p) = 1 := by rw [hinv, Nat.cast_one]
    rwa [ZMod.natCast_mod, Nat.cast_mul] at this
  have hkey : 12 * (h : ℤ) * E h p = ((h : ℤ) ^ 2 + 1) * ((p : ℤ) * (p - 1) * (2 * p - 1))
      - 6 * (p : ℤ) ^ 2 * ∑ r ∈ range p, ((h * r / p : ℕ) : ℤ) ^ 2 := by
    linear_combination 6 * two_h_E hp0 hinv + ((h : ℤ) ^ 2 + 1) * six_mul_sum_sq p
  -- `p ∣ E`
  have hE0 : ((E h p : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hkey
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one,
      Int.cast_natCast, Int.cast_ofNat, ZMod.natCast_self, zero_mul, mul_zero, zero_pow two_ne_zero,
      sub_zero] at this
    have hh0 : (h : ZMod p) ≠ 0 := left_ne_zero_of_mul_eq_one hhh
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (mul_ne_zero h12 hh0)
    · exact h1
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hE0
  refine ⟨e, he, ?_⟩
  have hred : 12 * (h : ℤ) * e = ((h : ℤ) ^ 2 + 1) * ((p - 1) * (2 * p - 1))
      - 6 * p * ∑ r ∈ range p, ((h * r / p : ℕ) : ℤ) ^ 2 := by
    have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
    refine mul_left_cancel₀ hp0' ?_
    rw [he] at hkey
    linear_combination hkey
  have hredp := congrArg (fun z : ℤ => (z : ZMod p)) hred
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one,
    Int.cast_natCast, Int.cast_ofNat, ZMod.natCast_self, zero_mul, mul_zero, sub_zero,
    zero_sub] at hredp
  push_cast
  linear_combination (h' : ZMod p) * hredp + ((h : ZMod p) - 12 * (e : ZMod p)) * hhh

end Residue

/-! ### Sums over a subgroup of `(ℤ/pℤ)ˣ` -/

section SubgroupSums

variable {p : ℕ} [Fact p.Prime]

theorem sum_inv_eq_sum (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] :
    ∑ u ∈ univ.filter (· ∈ H), ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
      = ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) := by
  refine sum_nbij' (fun u => u⁻¹) (fun u => u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu).2⟩
  · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu).2⟩
  · intro u _; exact inv_inv u
  · intro u _; exact inv_inv u
  · intro u _; rfl

/-- For a nontrivial subgroup `H`, `∑_{h ∈ H} h ≡ 0 (mod p)`. -/
theorem sum_subgroup_eq_zero (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] (hH : H ≠ ⊥) :
    ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) = 0 := by
  obtain ⟨⟨g, hgH⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hg1' : (g : ZMod p) ≠ 1 := by
    intro h; apply hg1; ext; simpa using h
  have hmul : ∑ u ∈ univ.filter (· ∈ H), (g : ZMod p) * ((u : (ZMod p)ˣ) : ZMod p)
      = ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) := by
    refine sum_nbij' (fun u => g * u) (fun u => g⁻¹ * u) ?_ ?_ ?_ ?_ ?_
    · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.mul_mem hgH (mem_filter.mp hu).2⟩
    · intro u hu
      exact mem_filter.mpr ⟨mem_univ _, H.mul_mem (H.inv_mem hgH) (mem_filter.mp hu).2⟩
    · intro u _; simp
    · intro u _; simp
    · intro u _; simp
  rw [← mul_sum] at hmul
  have : ((g : ZMod p) - 1) * ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) = 0 := by
    rw [sub_mul, hmul, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hg1')

end SubgroupSums

/-! ### Corollary 4.1 and Theorem 1.2 -/

theorem card_filter_mem {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ) [DecidablePred (· ∈ H)] :
    (univ.filter (· ∈ H)).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card]
  convert (Fintype.card_subtype (· ∈ H)).symm

/-- **Corollary 4.1.** If `3 ∤ k` and `H` has odd order `n`, then `2 k S(H,k) ∈ ℤ` and
`2 k S(H,k) ≡ 3 n (k-1)(k-2)/2 (mod 8)`. -/
theorem two_mul_k_subgroupSum_modEq {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ 3 * (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by
  classical
  have hk0 : 0 < k := lt_trans Nat.zero_lt_one hk
  have hc : ∀ u : (ZMod k)ˣ, ∃ c : ℤ, (c : ℚ) = 2 * k * dedekindSum (u : ZMod k).val k :=
    fun u => two_mul_dedekindSum_int hk0 (val_mul_val_inv hk u) h3
  choose c hc using hc
  refine ⟨∑ u ∈ univ.filter (· ∈ H), c u, ?_, ?_⟩
  · unfold subgroupSum; push_cast; rw [mul_sum]; exact sum_congr rfl (fun u _ => hc u)
  · obtain ⟨N, hN, hNmod⟩ := twelve_mul_subgroupSum_modEq hk H hodd
    have h6 : N = 6 * ∑ u ∈ univ.filter (· ∈ H), c u := by
      have : (N : ℚ) = 6 * ∑ u ∈ univ.filter (· ∈ H), (c u : ℚ) := by
        rw [hN, mul_sum]; unfold subgroupSum; rw [mul_sum]
        refine sum_congr rfl (fun u _ => ?_); rw [hc u]; ring
      exact_mod_cast this
    rw [h6] at hNmod
    obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp hNmod.symm)
    exact Int.modEq_iff_dvd.mpr
      ⟨∑ u ∈ univ.filter (· ∈ H), c u - 3 * t, by linear_combination (-3 : ℤ) * ht⟩

/-- Corollary 4.1 for odd `k`: `2 k S(H,k) ≡ n k (k-1)/2 (mod 8)`. -/
theorem two_mul_k_subgroupSum_modEq_odd {k : ℕ} [NeZero k] (hk : 1 < k) (h3 : ¬ 3 ∣ k)
    (hkodd : Odd k) (H : Subgroup (ZMod k)ˣ) (hodd : Odd (Nat.card H)) :
    ∃ x : ℤ, (x : ℚ) = 2 * k * subgroupSum H ∧
      2 * x ≡ (Nat.card H : ℤ) * ((k : ℤ) * ((k : ℤ) - 1)) [ZMOD 16] := by
  obtain ⟨x, hx, hmod⟩ := two_mul_k_subgroupSum_modEq hk h3 H hodd
  refine ⟨x, hx, hmod.trans ?_⟩
  obtain ⟨m, hm⟩ := hkodd
  obtain ⟨a, ha⟩ := Int.even_mul_succ_self ((m : ℤ) - 1)
  have hm' : (k : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  refine Int.modEq_iff_dvd.mpr ⟨-(Nat.card H : ℤ) * a, ?_⟩
  rw [hm']
  linear_combination (-8 : ℤ) * (Nat.card H : ℤ) * ha

/-- **Theorem 1.2.** Let `p > 3` be prime and `H ≤ (ℤ/pℤ)ˣ` of odd order `n > 1`. Then `2 S(H,p)`
is an integer and `2 S(H,p) ≡ n (p-1)/2 (mod 8)`. -/
theorem two_mul_subgroupSum_prime {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hp0 : 0 < p := hp.out.pos
  have hH : H ≠ ⊥ := fun h => by rw [(Subgroup.eq_bot_iff_card H).mp h] at hn; omega
  set s := univ.filter (· ∈ H) with hs
  have hcard : s.card = Nat.card H := card_filter_mem H
  -- `p` is odd
  obtain ⟨m, hm⟩ : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpm : (p : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hhalf : ((p : ℤ) - 1) / 2 = m := by omega
  -- the integers `e_u`
  have he : ∀ u : (ZMod p)ˣ, ∃ e : ℤ, E (u : ZMod p).val p = p * e ∧
      (((12 * e : ℤ)) : ZMod p) = (((u : ZMod p).val : ℕ) : ZMod p)
        + ((((u⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) :=
    fun u => E_modp hp3 (val_mul_val_inv hp1 u)
  choose e heE hemod using he
  -- `p ∣ ∑ e_u`
  have h12 : (12 : ZMod p) ≠ 0 := twelve_ne_zero hp3
  have hsum0 : ((∑ u ∈ s, e u : ℤ) : ZMod p) = 0 := by
    have h1 : (12 : ZMod p) * ((∑ u ∈ s, e u : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [mul_sum]
      have : ∀ u ∈ s, (12 : ZMod p) * (e u : ZMod p)
          = ((u : (ZMod p)ˣ) : ZMod p) + ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        intro u _
        have := hemod u
        push_cast at this
        rw [this, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_inv_eq_inv_val]
      rw [sum_congr rfl this, sum_add_distrib, sum_inv_eq_sum, sum_subgroup_eq_zero H hH, add_zero]
    exact (mul_eq_zero.mp h1).resolve_left h12
  obtain ⟨f, hf⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum0
  -- `2 S(H,p) = 2 f - n m`
  set n : ℕ := Nat.card H with hn_def
  have hS : subgroupSum H = (f : ℚ) - n * (2 * m) / 4 := by
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hterm : ∀ u ∈ s, dedekindSum (u : ZMod p).val p = (e u : ℚ) / p - ((p : ℚ) - 1) / 4 := by
      intro u _
      rw [dedekindSum_residue hp0 (val_mul_val_inv hp1 u), ← E_cast, heE u]
      push_cast
      field_simp
    unfold subgroupSum
    rw [← hs, sum_congr rfl hterm, sum_sub_distrib, ← sum_div, sum_const, hcard, nsmul_eq_mul]
    have hf' : (∑ u ∈ s, (e u : ℚ)) = p * f := by exact_mod_cast hf
    have hpm' : (p : ℚ) = 2 * m + 1 := by exact_mod_cast hpm
    rw [hf']
    field_simp
    rw [hpm']
    ring
  refine ⟨2 * f - n * m, ?_, ?_⟩
  · rw [hS]; push_cast; ring
  · -- the congruence, from Theorem 1.1
    rw [hhalf]
    obtain ⟨N, hN, hNmod⟩ := twelve_mul_subgroupSum_modEq hp1 H hodd
    have h6 : N = 6 * p * (2 * f - n * m) := by
      have : (N : ℚ) = 6 * p * (2 * f - n * m) := by
        rw [hN, hS]
        have hpm' : (p : ℚ) = 2 * m + 1 := by exact_mod_cast hpm
        rw [hpm']; ring
      exact_mod_cast this
    rw [h6] at hNmod
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hNmod
    rw [hpm] at ht
    -- halve
    have ht2 : (n : ℤ) * m * (2 * m - 1) - 3 * (2 * m + 1) * (2 * f - n * m) = 8 * t := by
      refine mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_
      linear_combination ht
    obtain ⟨a, ha⟩ := Int.even_mul_succ_self (m : ℤ)
    refine (Int.modEq_iff_dvd.mpr ⟨-(3 * t * (2 * m + 1) - n * (3 * a * (m - 1) + m)
      + 9 * a * (2 * f - n * m) + (2 * f - n * m)), ?_⟩).symm
    linear_combination (-3) * (2 * (m : ℤ) + 1) * ht2
      + (12 * (n : ℤ) * (m - 1) - 36 * (2 * f - n * m)) * ha

/-- **Theorem 1.2, Louboutin's normalization.** `N(H,p) = 12 S(H,p) - p` is an integer and
`N(H,p) ≡ 3 n (p-1) - p (mod 48)`. -/
theorem louboutin_N_modEq {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ N : ℤ, (N : ℚ) = 12 * subgroupSum H - p ∧
      N ≡ 3 * (Nat.card H : ℤ) * ((p : ℤ) - 1) - p [ZMOD 48] := by
  obtain ⟨y, hy, hmod⟩ := two_mul_subgroupSum_prime hp3 H hodd hn
  refine ⟨6 * y - p, by push_cast; rw [hy]; ring, ?_⟩
  obtain ⟨m, hm⟩ : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpm : (p : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hhalf : ((p : ℤ) - 1) / 2 = m := by omega
  rw [hhalf] at hmod
  obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.mp hmod
  exact Int.modEq_iff_dvd.mpr ⟨w, by rw [hpm]; linear_combination (6 : ℤ) * hw⟩

end DedekindSubgroups
