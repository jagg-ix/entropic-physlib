/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
meta import Zil

/-!
# The projection decomposition of the Riemann tensor (Gowdy §V)

Projecting the first index of the Riemann tensor `R_{abcd}` with a projection tensor `H`,
`(H·R)_{abcd} = H^p_a R_{pbcd}`, and using `I = H + V`, the Riemann tensor splits into an `H`-projected
and a `V`-projected part on that index:

`R_{abcd} = (H·R)_{abcd} + (V·R)_{abcd}`.

Iterating over the four indices gives the full Gowdy §V projection decomposition.  The single-index
projection preserves the algebraic symmetries not touching that index (e.g. the antisymmetry of the
second pair passes straight through).

* `projectRiemannFirst` — `(H·R)_{abcd} = ∑_p H^p_a R_{pbcd}`.
* `projectRiemannFirst_one` — projecting by the identity returns `R`.
* `riemann_first_decomposition` — `R = (H·R) + (V·R)` on the first index.
* `projectRiemannFirst_antisymm_right` — the second-pair antisymmetry `R_{abcd} = −R_{abdc}` is inherited.

Honest scope: the algebraic single-index projection decomposition and the passthrough of the
untouched-index symmetries; the full four-index symmetry inheritance and the Gauss–Codazzi identification
of the projected blocks are not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The first-index projection of the Riemann tensor** `(H·R)_{abcd} = ∑_p H^p_a R_{pbcd}`. -/
def projectRiemannFirst (H : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : RiemannTensor ι :=
  fun a b c d => ∑ p, H p a * Rm p b c d

/-- **Projecting by the identity returns the Riemann tensor** `(I·R) = R`. -/
@[zil_level physical_theorem]
theorem projectRiemannFirst_one (Rm : RiemannTensor ι) (a b c d : ι) :
    projectRiemannFirst 1 Rm a b c d = Rm a b c d := by
  unfold projectRiemannFirst
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ a (fun p => Rm p b c d)]
  simp

/-- **The first-index projection decomposition** `R = (H·R) + (V·R)` (with `V = I − H`) — the Riemann
tensor splits into its `H`-projected and `V`-projected parts on the first index. -/
@[zil_level physical_theorem]
theorem riemann_first_decomposition (H : Matrix ι ι ℝ) (Rm : RiemannTensor ι) (a b c d : ι) :
    Rm a b c d
      = projectRiemannFirst H Rm a b c d + projectRiemannFirst (complementProjection H) Rm a b c d := by
  unfold projectRiemannFirst complementProjection
  have step : ∀ p, H p a * Rm p b c d + (1 - H) p a * Rm p b c d
      = (if p = a then Rm p b c d else 0) := by
    intro p; rw [Matrix.sub_apply, Matrix.one_apply]; split <;> ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun p _ => step p),
    Finset.sum_ite_eq' Finset.univ a (fun p => Rm p b c d)]
  simp

/-- **The second-pair antisymmetry is inherited by the first-index projection**
`(H·R)_{abcd} = −(H·R)_{abdc}` — a symmetry not touching the projected index passes through. -/
@[zil_level physical_theorem]
theorem projectRiemannFirst_antisymm_right (H : Matrix ι ι ℝ) (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) (a b c d : ι) :
    projectRiemannFirst H Rm a b c d = -projectRiemannFirst H Rm a b d c := by
  unfold projectRiemannFirst
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h.antisymm_right p b c d]
  ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition

zil attach projectRiemannFirst_one where
  supported_by @ "lean:HermitianMat.one_apply",
  formalizes @ "claim:projecting-the-first-index-of-the-riemann-tensor-by-the-identity-tensor-returns-the-riemann-tensor"

zil attach riemann_first_decomposition where
  supported_by @ "lean:HermitianMat.one_apply",
  formalizes @ "claim:the-riemann-tensor-splits-on-its-first-index-into-the-h-projected-part-plus-the-v-projected-part-the-single-index-projection-decomposition-from-the-identity-splitting-h-plus-v"

zil attach projectRiemannFirst_antisymm_right where
  formalizes @ "claim:the-first-index-projection-of-the-riemann-tensor-inherits-the-second-pair-antisymmetry-a-symmetry-not-touching-the-projected-index-passes-through"

zil_file_contract physlib.projectedRiemannDecomposition where
  promises "The projection decomposition of the Riemann tensor of Gowdy section five. Projecting the first index of the Riemann tensor with a projection tensor gives the sum over p of H upper p lower a times the Riemann tensor with p in the first slot. Projecting by the identity tensor returns the Riemann tensor. From the identity splitting H plus V equals the identity, the Riemann tensor splits on its first index into the H-projected part plus the V-projected part, the single-index projection decomposition; iterating over the four indices gives the full projection decomposition. The single-index projection inherits the symmetries not touching the projected index: the second-pair antisymmetry passes straight through. Honest scope: the algebraic single-index projection decomposition and the passthrough of untouched-index symmetries; the full four-index symmetry inheritance and the Gauss-Codazzi identification of the projected blocks are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.complementProjection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.IsRiemannCurvature"
  ]
  forbids_substitutes [
    "reading the single-index projection decomposition as the full four-index Gauss-Codazzi decomposition of the Riemann curvature"
  ]
  witnessed_by [
    projectRiemannFirst_one,
    riemann_first_decomposition,
    projectRiemannFirst_antisymm_right
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.projectedRiemannDecomposition
