/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ModularRepresentation
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Explicit

/-!
# Modular invariance of the diagonal Chern–Simons–Witten partition function

The genus-one diagonal partition function `Z = Σ_a |χ_a|²` (`torusPartitionFunction`, Hayashi (5.19)) is
**invariant under the modular `S` transformation** `χ_a ↦ Σ_b S_{ab} χ_b`. This links the `S`-matrix unitarity
(`cswSMatrix_unitary`) directly to the partition-function structure: the diagonal modular invariant is a genuine
modular invariant because the rows of `S` are orthonormal.

* `cswSMatrix_colOrthogonal`: the columns of `S` are orthonormal too,
  `Σ_a \overline{S_{ab}} S_{ac} = δ_{bc}` (from row orthonormality + symmetry).
* `torusPartitionFunction_S_invariant`: `Z[Sχ] = Z[χ]`.

## References

* E. Witten (1989); Hayashi (CSW-gravity torus theorem, (5.19)). `Physlib` (`cswSMatrix_unitary`,
  `torusPartitionFunction`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-- **[Columns of `S` are orthonormal]** `Σ_a \overline{S_{ab}} S_{ac} = δ_{bc}` — from row orthonormality
(`cswSMatrix_unitary`) and symmetry (`cswSMatrix_symm`). -/
theorem cswSMatrix_colOrthogonal (k : ℕ) (hk : 0 < k) (b c : Fin k) :
    (∑ a : Fin k, (starRingEnd ℂ) (cswSMatrix k a b) * cswSMatrix k a c)
      = if b = c then 1 else 0 := by
  have hswap : (∑ a : Fin k, (starRingEnd ℂ) (cswSMatrix k a b) * cswSMatrix k a c)
      = ∑ a : Fin k, cswSMatrix k c a * (starRingEnd ℂ) (cswSMatrix k b a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [cswSMatrix_symm k a b, cswSMatrix_symm k a c, mul_comm]
  rw [hswap, cswSMatrix_unitary k hk c b]
  by_cases h : b = c
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun he => h he.symm]

/-- **[Modular `S` invariance of the diagonal partition function]** `Z[Sχ] = Z[χ]` where `(Sχ)_a = Σ_b S_{ab}
χ_b`. The diagonal modular invariant `Σ_a |χ_a|²` is genuinely modular invariant, by `S`-unitarity. -/
theorem torusPartitionFunction_S_invariant (k : ℕ) (hk : 0 < k) (χ : Fin k → ℂ) :
    torusPartitionFunction k (fun a => ∑ b : Fin k, cswSMatrix k a b * χ b)
      = torusPartitionFunction k χ := by
  show (∑ a : Fin k, (starRingEnd ℂ) (∑ b : Fin k, cswSMatrix k a b * χ b)
          * (∑ b : Fin k, cswSMatrix k a b * χ b))
    = ∑ a : Fin k, (starRingEnd ℂ) (χ a) * χ a
  calc (∑ a : Fin k, (starRingEnd ℂ) (∑ b : Fin k, cswSMatrix k a b * χ b)
            * (∑ b : Fin k, cswSMatrix k a b * χ b))
      = ∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k,
          ((starRingEnd ℂ) (cswSMatrix k a b) * cswSMatrix k a c)
            * ((starRingEnd ℂ) (χ b) * χ c) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]; ring
    _ = ∑ b : Fin k, ∑ c : Fin k,
          (∑ a : Fin k, (starRingEnd ℂ) (cswSMatrix k a b) * cswSMatrix k a c)
            * ((starRingEnd ℂ) (χ b) * χ c) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_mul]
    _ = ∑ b : Fin k, ∑ c : Fin k,
          (if b = c then 1 else 0) * ((starRingEnd ℂ) (χ b) * χ c) := by
        simp_rw [cswSMatrix_colOrthogonal k hk]
    _ = ∑ b : Fin k, (starRingEnd ℂ) (χ b) * χ b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp_rw [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ b)]

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
