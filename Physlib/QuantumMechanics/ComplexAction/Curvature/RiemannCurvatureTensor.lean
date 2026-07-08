/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

/-!
# The 4-index Riemann curvature tensor, its contractions and the Weyl tensor

Completes the 4-index Riemann tensor that physlib's matrix-valued general relativity lacked (its Ricci was a
2-index `Matrix`, and `Curvature.RicciWeylDecompositionTetrad` could only treat the Weyl tensor through its trace
shadow). Here the Riemann tensor is a genuine 4-index object `Rm : ι → ι → ι → ι → ℝ` with the **algebraic
curvature symmetries** of a Levi-Civita connection (`IsRiemannCurvature`):

* antisymmetry in the first pair `R_{abcd} = −R_{bacd}` and the second pair `R_{abcd} = −R_{abdc}`,
* pair-exchange symmetry `R_{abcd} = R_{cdab}`,
* the first (algebraic) Bianchi identity `R_{abcd} + R_{acdb} + R_{adbc} = 0`.

From it the **Ricci tensor** `R_{bd} = gᵃᶜ R_{abcd}` (`ricci`, a `Matrix`, feeding the existing
`einsteinTensor` / `tracelessRicci`), the **scalar curvature** `R = gᵇᵈ R_{bd}` (`ricciScalarContraction`),
and the **Weyl tensor** `C` (`weylTensor`) — the totally trace-free part of `Rm` — all follow.

* **§A — the Riemann tensor and its symmetries** (`RiemannTensor`, `IsRiemannCurvature`, `diag_left_zero`,
  `diag_right_zero`).
* **§B — witnesses** (`isRiemannCurvature_zero`; the maximally symmetric / constant-curvature model
  `constantCurvature K g = K(g_{ac}g_{bd} − g_{ad}g_{bc})`, `isRiemannCurvature_constantCurvature`).
* **§C — contractions** (`ricci`, `ricci_symm`, `ricci_zero`, `scalarCurvature`, and the bridge
  `flat_riemann_curvature_vanishes` feeding the matrix decomposition).
* **§D — the Weyl tensor** (`weylTensor`, `weyl_zero_of_flat`, and the tensor-level statement that **vacuum
  curvature is pure Weyl**, `weyl_eq_riemann_of_vacuum`).

## References

* L. P. Eisenhart, *Riemannian Geometry*; H. Weyl (the conformal tensor). structure: `Physlib`
  (`Curvature.RicciWeylDecompositionTetrad`).

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι]

/-! ## §A — the Riemann tensor and its symmetries -/

/-- **The 4-index Riemann curvature tensor** (all indices lowered), `R_{abcd}`. -/
abbrev RiemannTensor (ι : Type*) : Type _ := ι → ι → ι → ι → ℝ

/-- **The algebraic (curvature) symmetries of a Riemann tensor.** -/
structure IsRiemannCurvature (Rm : RiemannTensor ι) : Prop where
  /-- Antisymmetry in the first pair `R_{abcd} = −R_{bacd}`. -/
  antisymm_left : ∀ a b c d, Rm a b c d = - Rm b a c d
  /-- Antisymmetry in the second pair `R_{abcd} = −R_{abdc}`. -/
  antisymm_right : ∀ a b c d, Rm a b c d = - Rm a b d c
  /-- Pair-exchange symmetry `R_{abcd} = R_{cdab}`. -/
  pair_symm : ∀ a b c d, Rm a b c d = Rm c d a b
  /-- First (algebraic) Bianchi identity `R_{abcd} + R_{acdb} + R_{adbc} = 0`. -/
  bianchi : ∀ a b c d, Rm a b c d + Rm a c d b + Rm a d b c = 0

variable {Rm : RiemannTensor ι}

omit [Fintype ι] in
/-- **[Diagonal in the first pair vanishes] `R_{aacd} = 0`.** -/
theorem IsRiemannCurvature.diag_left_zero (h : IsRiemannCurvature Rm) (a c d : ι) :
    Rm a a c d = 0 := by
  have := h.antisymm_left a a c d; linarith

omit [Fintype ι] in
/-- **[Diagonal in the second pair vanishes] `R_{abcc} = 0`.** -/
theorem IsRiemannCurvature.diag_right_zero (h : IsRiemannCurvature Rm) (a b c : ι) :
    Rm a b c c = 0 := by
  have := h.antisymm_right a b c c; linarith

/-! ## §B — witnesses -/

omit [Fintype ι] in
/-- **The zero (flat) tensor is a Riemann tensor.** -/
theorem isRiemannCurvature_zero : IsRiemannCurvature (0 : RiemannTensor ι) :=
  ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

/-- **The maximally symmetric / constant-curvature Riemann tensor** `R_{abcd} = K(g_{ac}g_{bd} −
g_{ad}g_{bc})` of a space of constant curvature `K`. -/
def constantCurvature (K : ℝ) (g : Matrix ι ι ℝ) : RiemannTensor ι :=
  fun a b c d => K * (g a c * g b d - g a d * g b c)

omit [Fintype ι] in
/-- **The constant-curvature model is a genuine Riemann tensor** (for a symmetric metric `g`). A non-trivial
witness that the four algebraic symmetries are mutually consistent. -/
theorem isRiemannCurvature_constantCurvature (K : ℝ) (g : Matrix ι ι ℝ)
    (hg : ∀ i j, g i j = g j i) : IsRiemannCurvature (constantCurvature K g) := by
  refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_⟩
  · simp only [constantCurvature]; ring
  · simp only [constantCurvature]; ring
  · simp only [constantCurvature]; rw [hg c a, hg d b, hg c b, hg d a]; ring
  · simp only [constantCurvature]; rw [hg c b, hg d c, hg d b]; ring

/-! ## §C — contractions -/

/-- **The Ricci tensor** `R_{bd} = gᵃᶜ R_{abcd}`, the metric contraction of the Riemann tensor over its first
and third indices — a 2-index `Matrix`, feeding the existing `einsteinTensor` / `tracelessRicci`. -/
noncomputable def ricci (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : Matrix ι ι ℝ :=
  Matrix.of fun b d => ∑ a, ∑ c, gInv a c * Rm a b c d

/-- **[The Ricci tensor is symmetric] `R_{bd} = R_{db}`** for a symmetric inverse metric — from the
pair-exchange symmetry of the Riemann tensor. -/
theorem ricci_symm (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι)
    (hg : gInvᵀ = gInv) (h : IsRiemannCurvature Rm) (b d : ι) :
    ricci gInv Rm b d = ricci gInv Rm d b := by
  simp only [ricci, Matrix.of_apply]
  rw [show (∑ a, ∑ c, gInv a c * Rm a b c d) = ∑ a, ∑ c, gInv a c * Rm c d a b from
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [h.pair_symm]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [show gInv y x = gInv x y from by
    have h2 := congrFun (congrFun hg x) y; rwa [Matrix.transpose_apply] at h2]

/-- **[Flat Riemann ⇒ zero Ricci] `R_{abcd} = 0 ⇒ R_{bd} = 0`.** -/
@[simp] theorem ricci_zero (gInv : Matrix ι ι ℝ) : ricci gInv (0 : RiemannTensor ι) = 0 := by
  ext b d; simp [ricci]

/-- **The scalar curvature** `R = gᵇᵈ R_{bd}` — the metric trace of the (contracted) Ricci tensor, reusing
`ricciScalarContraction`. -/
noncomputable def scalarCurvature (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : ℝ :=
  ricciScalarContraction gInv (ricci gInv Rm)

/-- **[Flat 4-index Riemann ⇒ the whole matrix curvature decomposition is trivial].** A vanishing Riemann
tensor gives vanishing Ricci, scalar curvature and Einstein tensor — bridging the 4-index tensor to the
matrix Weyl / traceless-Ricci / Ricci-scalar decomposition. -/
theorem flat_riemann_curvature_vanishes (gInv g : Matrix ι ι ℝ) :
    ricci gInv (0 : RiemannTensor ι) = 0 ∧ scalarCurvature gInv (0 : RiemannTensor ι) = 0
      ∧ einsteinTensor (ricci gInv (0 : RiemannTensor ι)) (scalarCurvature gInv 0) g = 0 := by
  refine ⟨ricci_zero gInv, ?_, ?_⟩
  · simp [scalarCurvature, ricciScalarContraction]
  · simp [scalarCurvature, ricciScalarContraction, einsteinTensor]

/-! ## §D — the Weyl tensor -/

/-- **The Weyl conformal curvature tensor** in dimension `n`,

  `C_{abcd} = R_{abcd} − (1/(n−2))(g_{ac}R_{bd} − g_{ad}R_{bc} − g_{bc}R_{ad} + g_{bd}R_{ac})`
  `           + (R/((n−1)(n−2)))(g_{ac}g_{bd} − g_{ad}g_{bc})`,

the totally trace-free part of the Riemann tensor (`Ric` the Ricci tensor, `scalarR` the scalar curvature). -/
noncomputable def weylTensor (n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) : RiemannTensor ι :=
  fun a b c d => Rm a b c d
    - (1 / (n - 2)) * (g a c * Ric b d - g a d * Ric b c - g b c * Ric a d + g b d * Ric a c)
    + (scalarR / ((n - 1) * (n - 2))) * (g a c * g b d - g a d * g b c)

omit [Fintype ι] in
/-- **[Vacuum curvature is pure Weyl, at the tensor level] `Ric = 0 ∧ R = 0 ⇒ C = R`.** When the Ricci tensor
and scalar curvature vanish, the Weyl tensor *is* the Riemann tensor — all curvature is conformal. This is the
tensor-level upgrade of `vacuum_pure_weyl`. -/
theorem weyl_eq_riemann_of_vacuum (n : ℝ) (g : Matrix ι ι ℝ) (Rm : RiemannTensor ι) :
    weylTensor n g 0 0 Rm = Rm := by
  funext a b c d; simp [weylTensor]

omit [Fintype ι] in
/-- **[Flat ⇒ zero Weyl] `R_{abcd} = 0 ⇒ C = 0`.** A flat geometry is conformally flat. -/
theorem weyl_zero_of_flat (n : ℝ) (g : Matrix ι ι ℝ) :
    weylTensor n g 0 0 (0 : RiemannTensor ι) = 0 := by
  funext a b c d; simp [weylTensor]

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
