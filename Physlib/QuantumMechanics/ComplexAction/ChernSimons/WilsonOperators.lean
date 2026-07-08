/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeFormula
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.PartitionFunction

/-!
# Wilson/Verlinde operators use the modular `S`-matrix

This lets the repo's operator infrastructure (`cswWilsonVerlindeOperator`, the abelian Wilson-loop / fusion
operators of `ChernSimons.ModularRepresentation`) **use** the modular `S`-matrix: the operators are
simultaneously diagonalized by the `S`-matrix columns, with eigenvalues `S_{aq}/S_{0q}`.

* `cswWilsonVerlinde_diagonalization`: the Wilson operator `W_a` for charge `a`, applied to the conjugate
 `S`-column `\overline{S_{·q}}`, returns `(S_{aq}/S_{0q})·\overline{S_{·q}}` — the column is an eigenvector
 with the Verlinde eigenvalue. Proved from the Verlinde formula (`cswVerlinde_formula`) and column
 orthonormality (`cswSMatrix_colOrthogonal`), so it composes the new `S`-matrix results rather than assuming
 anything.

**Correction note.** The recorded `CSWWilsonVerlindeDiagonalizationObligation` is false *as written*: it uses
the un-conjugated column `S_{·q}` with eigenvalue `S_{aq}/S_{0q}`, whereas `W_a` sends `S_{·q}` to
`e^{+2πi aq/k} S_{·q} = \overline{S_{aq}/S_{0q}}·S_{·q}`. The statement uses the **conjugate** column,
recorded here.

## References

* E. Verlinde (1988); E. Witten (1989). `Physlib` (`cswVerlinde_formula`, `cswSMatrix_colOrthogonal`,
 `cswWilsonVerlindeOperator`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-- **[Wilson operators are diagonalized by the `S`-matrix]** the Wilson/Verlinde operator `W_a` applied to
the conjugate `S`-column `\overline{S_{·q}}` returns `(S_{aq}/S_{0q})·\overline{S_{·q}}`: the conjugate column
is a simultaneous eigenvector with the Verlinde eigenvalue. This is "item 9 proper" — Wilson loops acting as
diagonal Verlinde operators — and it is proved by composing the Verlinde formula with column orthonormality
of `S`. -/
theorem cswWilsonVerlinde_diagonalization (k : ℕ) (hk : 0 < k) (a q : Fin k) :
    cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
      = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) := by
  funext c
  have hcol : ∀ x : Fin k,
      (∑ b : Fin k, cswSMatrix k b x * (starRingEnd ℂ) (cswSMatrix k b q)) = if x = q then 1 else 0 := by
    intro x
    rw [show (∑ b : Fin k, cswSMatrix k b x * (starRingEnd ℂ) (cswSMatrix k b q))
        = ∑ b : Fin k, (starRingEnd ℂ) (cswSMatrix k b q) * cswSMatrix k b x from
        Finset.sum_congr rfl fun b _ => mul_comm _ _, cswSMatrix_colOrthogonal k hk q x]
    by_cases h : x = q
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun he => h he.symm]
  calc cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q)) c
      = ∑ b : Fin k, cswFusionCoeff k a b c * (starRingEnd ℂ) (cswSMatrix k b q) := by
        simp only [cswWilsonVerlindeOperator]
    _ = ∑ x : Fin k, (cswSMatrix k a x * star (cswSMatrix k c x)
            / cswSMatrix k (cswZeroCharge k hk) x)
          * (∑ b : Fin k, cswSMatrix k b x * (starRingEnd ℂ) (cswSMatrix k b q)) := by
        simp_rw [cswVerlinde_formula k hk, cswVerlindeCoefficientByS, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ x : Fin k, (cswSMatrix k a x * star (cswSMatrix k c x)
            / cswSMatrix k (cswZeroCharge k hk) x) * (if x = q then 1 else 0) := by
        simp_rw [hcol]
    _ = cswSMatrix k a q * star (cswSMatrix k c q) / cswSMatrix k (cswZeroCharge k hk) q := by
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ q)]
    _ = cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) := by
        rw [cswVerlindeEigenvalue, starRingEnd_apply]; ring

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
