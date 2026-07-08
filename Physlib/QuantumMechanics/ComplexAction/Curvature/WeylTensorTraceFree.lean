/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

/-!
# The Weyl tensor is trace-free

Formalizes the central result of F. Moulin, *Generalization of Einstein's gravitational field equations*
(Eur. Phys. J. C, arXiv:2405.03698): the Weyl conformal tensor `C_{ijkl}` (`weylTensor`, the paper's Eq. 35)
is **completely trace-free**, `gⁱᵏ C_{ijkl} = 0` (the paper's Eq. 37). In the index convention of
`Curvature.RiemannCurvatureTensor` the Ricci contraction is over the first and third slots, so the trace-free statement
*is* `ricci gInv (weylTensor …) = 0` — "the Ricci contraction of the Weyl tensor vanishes".

The proof reproduces the paper's contraction lemmas (its Eqs. 9–11), valid for a symmetric metric `g` with a
symmetric inverse `gInv` (`gInv · g = 1`) in dimension `n = card ι`:

* `contraction_metricStructure` — `gᵃᶜ(g_{ac}g_{bd} − g_{ad}g_{bc}) = (n−1) g_{bd}`  (Eq. 11),
* `contraction_metricRicci` — `gᵃᶜ(g_{ac}R_{bd} − g_{ad}R_{bc} − g_{bc}R_{ad} + g_{bd}R_{ac})
  = (n−2) R_{bd} + g_{bd} R`  (Eq. 10),

with `R_{bd} = gᵃᶜ R_{abcd}` the Ricci tensor (Eq. 9, definitional) and `R = gᵃᶜ R_{ac}` the scalar curvature.
Assembling them with the conformal coefficients `1/(n−2)` and `1/((n−1)(n−2))` gives, for `n ≠ 1, 2`,

  `gᵃᶜ C_{abcd} = R_{bd} − R_{bd} − g_{bd}R/(n−2) + g_{bd}R/(n−2) = 0`   (`weyl_traceFree`).

## References

* F. Moulin (2024), *Generalization of Einstein's gravitational field equations*, arXiv:2405.03698, §4.3 and
  Eqs. 9–11, 35, 37. structure: `Physlib` (`Curvature.RiemannCurvatureTensor`).

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {g gInv : Matrix ι ι ℝ}

/-! ## §A — the contraction identities (Moulin Eqs. 9–11) -/

/-- **[Metric-structure contraction, Moulin Eq. 11] `gᵃᶜ(g_{ac}g_{bd} − g_{ad}g_{bc}) = (n−1) g_{bd}`.** -/
theorem contraction_metricStructure (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (b d : ι) :
    (∑ a, ∑ c, gInv a c * (g a c * g b d - g a d * g b c)) = ((Fintype.card ι : ℝ) - 1) * g b d := by
  have gi_symm : ∀ a c, gInv a c = gInv c a := fun a c => by
    have h2 := congrFun (congrFun hgi c) a; rwa [Matrix.transpose_apply] at h2
  have g_symm : ∀ a c, g a c = g c a := fun a c => by
    have h2 := congrFun (congrFun hg c) a; rwa [Matrix.transpose_apply] at h2
  have hδ1 : ∀ c e, (∑ a, gInv a c * g a e) = (1 : Matrix ι ι ℝ) c e := fun c e => by
    rw [← hinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [gi_symm a c]
  have htrace : (∑ a, ∑ c, gInv a c * g a c) = (Fintype.card ι : ℝ) := by
    have e1 : (gInv * g).trace = ∑ a, ∑ c, gInv a c * g a c := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [g_symm c a]
    rw [← e1, hinv, Matrix.trace_one]
  have h1 : (∑ a, ∑ c, gInv a c * (g a c * g b d)) = (Fintype.card ι : ℝ) * g b d := by
    simp_rw [← mul_assoc, ← Finset.sum_mul]; rw [htrace]
  have h2 : (∑ a, ∑ c, gInv a c * (g a d * g b c)) = g b d := by
    have hc : ∀ c, (∑ a, gInv a c * (g a d * g b c)) = (1 : Matrix ι ι ℝ) c d * g b c := fun c => by
      rw [← hδ1 c d, Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_comm]
    simp_rw [hc]
    rw [Finset.sum_eq_single d]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro c _ hcd; rw [Matrix.one_apply_ne hcd, zero_mul]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  simp_rw [mul_sub, Finset.sum_sub_distrib]; rw [h1, h2]; ring

/-- **[Metric-Ricci contraction, Moulin Eq. 10]** `gᵃᶜ(g_{ac}R_{bd} − g_{ad}R_{bc} − g_{bc}R_{ad} + g_{bd}R_{ac})
= (n−2) R_{bd} + g_{bd} R`, with `R_{··} = ricci gInv Rm` and `R = scalarCurvature gInv Rm`. -/
theorem contraction_metricRicci (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) (b d : ι) :
    (∑ a, ∑ c, gInv a c * (g a c * ricci gInv Rm b d - g a d * ricci gInv Rm b c
        - g b c * ricci gInv Rm a d + g b d * ricci gInv Rm a c))
      = ((Fintype.card ι : ℝ) - 2) * ricci gInv Rm b d + g b d * scalarCurvature gInv Rm := by
  have gi_symm : ∀ a c, gInv a c = gInv c a := fun a c => by
    have h2 := congrFun (congrFun hgi c) a; rwa [Matrix.transpose_apply] at h2
  have g_symm : ∀ a c, g a c = g c a := fun a c => by
    have h2 := congrFun (congrFun hg c) a; rwa [Matrix.transpose_apply] at h2
  have hδ1 : ∀ c e, (∑ a, gInv a c * g a e) = (1 : Matrix ι ι ℝ) c e := fun c e => by
    rw [← hinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [gi_symm a c]
  have hδ2 : ∀ a e, (∑ c, gInv a c * g e c) = (1 : Matrix ι ι ℝ) a e := fun a e => by
    rw [← hinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [g_symm e c]
  have htrace : (∑ a, ∑ c, gInv a c * g a c) = (Fintype.card ι : ℝ) := by
    have e1 : (gInv * g).trace = ∑ a, ∑ c, gInv a c * g a c := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [g_symm c a]
    rw [← e1, hinv, Matrix.trace_one]
  have hscalar : (∑ a, ∑ c, gInv a c * ricci gInv Rm a c) = scalarCurvature gInv Rm := by
    simp only [scalarCurvature, ricciScalarContraction, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by
      rw [ricci_symm gInv Rm hgi h a c]
  have S1 : (∑ a, ∑ c, gInv a c * (g a c * ricci gInv Rm b d))
      = (Fintype.card ι : ℝ) * ricci gInv Rm b d := by
    simp_rw [← mul_assoc, ← Finset.sum_mul]; rw [htrace]
  have S2 : (∑ a, ∑ c, gInv a c * (g a d * ricci gInv Rm b c)) = ricci gInv Rm b d := by
    have hc : ∀ c, (∑ a, gInv a c * (g a d * ricci gInv Rm b c))
        = (1 : Matrix ι ι ℝ) c d * ricci gInv Rm b c := fun c => by
      rw [← hδ1 c d, Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_comm]
    simp_rw [hc]
    rw [Finset.sum_eq_single d]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro c _ hcd; rw [Matrix.one_apply_ne hcd, zero_mul]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  have S3 : (∑ a, ∑ c, gInv a c * (g b c * ricci gInv Rm a d)) = ricci gInv Rm b d := by
    have ha : ∀ a, (∑ c, gInv a c * (g b c * ricci gInv Rm a d))
        = (1 : Matrix ι ι ℝ) a b * ricci gInv Rm a d := fun a => by
      rw [← hδ2 a b, Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    simp_rw [ha]
    rw [Finset.sum_eq_single b]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro a _ hab; rw [Matrix.one_apply_ne hab, zero_mul]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have S4 : (∑ a, ∑ c, gInv a c * (g b d * ricci gInv Rm a c))
      = g b d * scalarCurvature gInv Rm := by
    simp_rw [show ∀ a c, gInv a c * (g b d * ricci gInv Rm a c)
      = g b d * (gInv a c * ricci gInv Rm a c) from fun a c => by ring, ← Finset.mul_sum]
    rw [hscalar]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [S1, S2, S3, S4]; ring

/-! ## §B — the Weyl tensor is trace-free (Moulin Eq. 37) -/

/-- **[The Weyl tensor is completely trace-free, Moulin Eq. 37] `gᵃᶜ C_{abcd} = 0`.** The Ricci contraction of
the Weyl tensor vanishes — the defining property of the conformal curvature tensor — for a symmetric metric `g`
with symmetric inverse `gInv` (`gInv·g = 1`) in dimension `n = card ι` with `n ≠ 1, 2`. -/
theorem weyl_traceFree (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) (b d : ι) :
    ricci gInv (weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) b d = 0 := by
  have hn12 : ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) ≠ 0 := mul_ne_zero hn1 hn2
  show (∑ a, ∑ c, gInv a c *
    weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm a b c d) = 0
  have expand : ∀ a c, gInv a c *
      weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm a b c d
      = gInv a c * Rm a b c d
        - (1 / ((Fintype.card ι : ℝ) - 2)) * (gInv a c * (g a c * ricci gInv Rm b d
            - g a d * ricci gInv Rm b c - g b c * ricci gInv Rm a d + g b d * ricci gInv Rm a c))
        + (scalarCurvature gInv Rm / (((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)))
            * (gInv a c * (g a c * g b d - g a d * g b c)) := by
    intro a c; simp only [weylTensor]; ring
  simp only [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [contraction_metricRicci hg hgi hinv h, contraction_metricStructure hg hgi hinv,
    show (∑ a, ∑ c, gInv a c * Rm a b c d) = ricci gInv Rm b d from rfl]
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
