# DedekindSubgroups

Lean 4 / Mathlib formalization accompanying J. S. Farland, *A congruence modulo 16 for sums of
Dedekind sums over subgroups of odd order*.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every main theorem depends only on `propext`, `Classical.choice`
and `Quot.sound` (`#print axioms`).

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (residue form) | `dedekindSum_residue` | Meyer |
| Lemma 2.2 (Meyer) | `meyer`, `meyer_int` | Meyer |
| Lemma 2.3 (`3 ∤ k` ⇒ `2k s(h,k) ∈ ℤ`) | `k_dvd_two_E`, `two_mul_dedekindSum_int` | Prime |
| Lemma 3.1 (`I(h⁻¹) = I(h)`) | `inv_symm` | Parity |
| Lemma 3.2 (squares are even) | `signAux_mulPerm`, `even_inv_sq` | Parity |
| Lemma 3.3 (odd-order groups) | `sq_root_of_odd`, `eq_one_of_inv_eq` | Main |
| **Theorem 1.1** (mod 16) | `twelve_mul_subgroupSum_modEq` | Main |
| Optimality (`k = 63`) | `modulus_sixteen_optimal` | Optimality |
| Remark 3.4 (all subgroups, mod 8) | `twelve_mul_subgroupSum_modEq_eight` | General |
| Corollary 4.1 (`3 ∤ k`) | `two_mul_k_subgroupSum_modEq`, `..._odd` | Prime |
| Lemma 4.2 | `E_modp` | Prime |
| `∑_{h∈H} h ≡ 0 (mod p)` | `sum_subgroup_eq_zero` | Prime |
| **Theorem 1.2** (prime case) | `two_mul_subgroupSum_prime`, `louboutin_N_modEq` | Prime |

Definitions: `sawtooth` (via `Int.fract` on `ℚ`), `dedekindSum h k`, `subgroupSum H` for
`H : Subgroup (ZMod k)ˣ` (sum of `dedekindSum u.val k` over `u ∈ H`), `inv h k` (inversions of
`z ↦ h z mod k` on `{0, …, k-1}`).

## Verify the axioms

In any file importing `DedekindSubgroups`:

```
#print axioms DedekindSubgroups.twelve_mul_subgroupSum_modEq
#print axioms DedekindSubgroups.two_mul_subgroupSum_prime
#print axioms DedekindSubgroups.modulus_sixteen_optimal
```

Each should report only `propext`, `Classical.choice`, `Quot.sound`.
