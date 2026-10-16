module

/-
  Inversions of `z ↦ h z mod k`: symmetry under `h ↦ h⁻¹`, and evenness for squares.
-/
public import DedekindSubgroups.Meyer

@[expose] public section

open Finset Equiv

namespace DedekindSubgroups

section Inversions

variable {h h' k : ℕ}

theorem sig_lt (hk : 0 < k) (h z : ℕ) : sig h k z < k := Nat.mod_lt _ hk

theorem sig_sig (hinv : h * h' % k = 1) {r : ℕ} (hr : r < k) : sig h' k (sig h k r) = r := by
  unfold sig
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
    one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]

theorem sig_injOn (hinv : h * h' % k = 1) {x y : ℕ} (hx : x < k) (hy : y < k)
    (he : sig h k x = sig h k y) : x = y := by
  rw [← sig_sig hinv hx, ← sig_sig hinv hy, he]

/-- The set of inversion pairs `(x, y)`, `x < y < k`, `σ(y) < σ(x)`. -/
def invSet (h k : ℕ) : Finset (ℕ × ℕ) :=
  (range k ×ˢ range k).filter (fun p => p.1 < p.2 ∧ sig h k p.2 < sig h k p.1)

theorem inv_eq_card (h k : ℕ) : inv h k = (invSet h k).card := by
  unfold inv invSet
  rw [card_filter, sum_product, sum_comm]
  refine sum_congr rfl ?_
  intro y hy
  rw [mem_range] at hy
  dsimp only
  have : (range k).filter (fun x => x < y ∧ sig h k y < sig h k x)
      = (range y).filter (fun x => sig h k y < sig h k x) := by
    ext x; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
  conv_rhs => rw [← sum_filter, this]
  rw [sum_filter]

/-- `I(h⁻¹, k) = I(h, k)`: `(x, y) ↦ (σ(y), σ(x))` maps inversions of `σ_h` onto those of `σ_{h⁻¹}`. -/
theorem inv_symm (hk : 0 < k) (hinv : h * h' % k = 1) : inv h' k = inv h k := by
  have hinv' : h' * h % k = 1 := by rwa [mul_comm]
  rw [inv_eq_card, inv_eq_card]
  refine Finset.card_nbij' (fun p => (sig h' k p.2, sig h' k p.1))
    (fun p => (sig h k p.2, sig h k p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    refine ⟨⟨sig_lt hk _ _, sig_lt hk _ _⟩, hs, ?_⟩
    rw [sig_sig hinv' hx, sig_sig hinv' hy]; exact hxy
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    refine ⟨⟨sig_lt hk _ _, sig_lt hk _ _⟩, hs, ?_⟩
    rw [sig_sig hinv hx, sig_sig hinv hy]; exact hxy
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hx, hy⟩, _, _⟩ := hp
    simp [sig_sig hinv' hx, sig_sig hinv' hy]
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hx, hy⟩, _, _⟩ := hp
    simp [sig_sig hinv hx, sig_sig hinv hy]

/-- Multiplication by an invertible `h` as a permutation of `Fin k`. -/
def mulPerm (hk : 0 < k) (hinv : h * h' % k = 1) : Perm (Fin k) where
  toFun r := ⟨sig h k r, sig_lt hk _ _⟩
  invFun r := ⟨sig h' k r, sig_lt hk _ _⟩
  left_inv r := by ext; exact sig_sig hinv r.2
  right_inv r := by ext; exact sig_sig (by rwa [mul_comm] : h' * h % k = 1) r.2

theorem signAux_mulPerm (hk : 0 < k) (hinv : h * h' % k = 1) :
    Perm.signAux (mulPerm hk hinv) = (-1) ^ inv h k := by
  unfold Perm.signAux
  rw [prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  rw [inv_eq_card]
  refine Finset.card_bij' (fun a _ => ((a.2 : ℕ), (a.1 : ℕ)))
    (fun p hp => ⟨⟨p.2, ?_⟩, ⟨p.1, ?_⟩⟩) ?_ ?_ ?_ ?_
  · simp only [invSet, mem_filter, mem_product, mem_range] at hp; exact hp.1.2
  · simp only [invSet, mem_filter, mem_product, mem_range] at hp; exact hp.1.1
  · rintro ⟨a, b⟩ ha
    simp only [mem_filter, Perm.mem_finPairsLT] at ha
    obtain ⟨hba, hle⟩ := ha
    simp only [invSet, mem_filter, mem_product, mem_range]
    refine ⟨⟨b.2, a.2⟩, hba, ?_⟩
    have hle' : sig h k a ≤ sig h k b := hle
    rcases lt_or_eq_of_le hle' with hlt | heq
    · exact hlt
    · exact absurd (sig_injOn hinv a.2 b.2 heq) (by
        have : (b : ℕ) < a := hba; omega)
  · rintro ⟨x, y⟩ hp
    simp only [invSet, mem_filter, mem_product, mem_range] at hp
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    simp only [mem_filter, Perm.mem_finPairsLT]
    refine ⟨Fin.mk_lt_mk.mpr hxy, ?_⟩
    show sig h k y ≤ sig h k x
    exact le_of_lt hs
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨x, y⟩ _; rfl

/-- Inversions of a square are even: `σ_{g²} = σ_g ∘ σ_g`, and the sign is multiplicative. -/
theorem even_inv_sq {g g' : ℕ} (hk : 0 < k) (hinv : g * g' % k = 1) :
    Even (inv (g * g % k) k) := by
  have hinv2 : (g * g % k) * (g' * g' % k) % k = 1 := by
    rw [← Nat.mul_mod, show g * g * (g' * g') = (g * g') * (g * g') by ring, Nat.mul_mod, hinv,
      one_mul]
    exact Nat.mod_eq_of_lt (one_lt_of_inv hk hinv)
  have hcomp : mulPerm hk hinv2 = mulPerm hk hinv * mulPerm hk hinv := by
    ext r
    simp only [mulPerm, Perm.coe_mul, Function.comp_apply, Equiv.coe_fn_mk, sig]
    rw [Nat.mod_mul_mod, Nat.mul_mod g, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
  have hs := signAux_mulPerm hk hinv2
  rw [hcomp, Perm.signAux_mul, Int.units_mul_self] at hs
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hs.symm

end Inversions

end DedekindSubgroups
