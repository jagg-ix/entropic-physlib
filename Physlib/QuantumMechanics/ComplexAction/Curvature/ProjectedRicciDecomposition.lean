/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
meta import Zil

/-!
# The projection decomposition of the Ricci tensor (Gowdy §V)

A projection tensor `H` (with complement `V = I − H`) decomposes the metric Ricci tensor `R_{ab}`
(a symmetric `(0,2)` matrix) into projected blocks.  Projecting both indices with `H` gives
`(H·R)_{ab} = H^p_a H^q_b R_{pq} = (Hᵀ R H)_{ab}`, and from `I = H + V` the Ricci tensor splits into four
blocks — the intrinsic (`HH`), the mixed (`HV`, `VH`) and the transverse (`VV`) parts:

`R = HᵀR H + HᵀR V + VᵀR H + VᵀR V`.

* `projectRicci` — `HᵀR H`, the fully `H`-projected Ricci.
* `projectRicci_symm` — the projected Ricci is symmetric when `R` is.
* `projectRicci_idem` — `H`-projection is idempotent (for a projection tensor).
* `ricci_projection_decomposition` — the four-block decomposition `R = HᵀR H + HᵀR V + VᵀR H + VᵀR V`.

Honest scope: the algebraic projection decomposition of a symmetric `(0,2)` tensor; the identification of
`HᵀR H` with the intrinsic Ricci of the subsurface (the Gauss equation) is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `H`-projected Ricci tensor** `(H·R)_{ab} = H^p_a H^q_b R_{pq} = HᵀR H`. -/
def projectRicci (H Ric : Matrix ι ι ℝ) : Matrix ι ι ℝ := Hᵀ * Ric * H

/-- **The projected Ricci is symmetric** when the Ricci tensor is. -/
@[zil_level physical_theorem]
theorem projectRicci_symm (H Ric : Matrix ι ι ℝ) (hRic : Ricᵀ = Ric) :
    (projectRicci H Ric)ᵀ = projectRicci H Ric := by
  unfold projectRicci
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hRic, mul_assoc]

/-- **The `H`-projection of the Ricci is idempotent** `H·(H·R) = H·R` (for a projection tensor). -/
@[zil_level physical_theorem]
theorem projectRicci_idem (H Ric : Matrix ι ι ℝ) (hH : H * H = H) :
    projectRicci H (projectRicci H Ric) = projectRicci H Ric := by
  unfold projectRicci
  have hTT : Hᵀ * Hᵀ = Hᵀ := (show IsProjectionTensor H from hH).transpose
  rw [show Hᵀ * (Hᵀ * Ric * H) * H = Hᵀ * Hᵀ * Ric * (H * H) from by simp only [mul_assoc],
    hTT, hH]

/-- **The four-block projection decomposition of the Ricci tensor**
`R = HᵀR H + HᵀR V + VᵀR H + VᵀR V` (with `V = I − H`) — the intrinsic, mixed and transverse blocks
from `I = H + V`. -/
@[zil_level physical_theorem]
theorem ricci_projection_decomposition (H Ric : Matrix ι ι ℝ) :
    Ric = projectRicci H Ric + Hᵀ * Ric * complementProjection H
        + (complementProjection H)ᵀ * Ric * H
        + (complementProjection H)ᵀ * Ric * complementProjection H := by
  unfold projectRicci
  have hsum : H + complementProjection H = 1 := add_complementProjection H
  calc Ric = (H + complementProjection H)ᵀ * Ric * (H + complementProjection H) := by
        rw [hsum, Matrix.transpose_one, one_mul, mul_one]
    _ = Hᵀ * Ric * H + Hᵀ * Ric * complementProjection H
          + (complementProjection H)ᵀ * Ric * H
          + (complementProjection H)ᵀ * Ric * complementProjection H := by
        rw [Matrix.transpose_add]
        simp only [add_mul, mul_add]
        abel

end Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition

zil attach projectRicci_symm where
  supported_by @ "lean:LorentzGroup.transpose_mul",
  formalizes @ "claim:the-h-projected-ricci-tensor-h-transpose-times-ricci-times-h-is-symmetric-when-the-ricci-tensor-is-symmetric"

zil attach projectRicci_idem where
  supported_by @ "lean:IsProjectionTensor.transpose",
  formalizes @ "claim:the-h-projection-of-the-ricci-tensor-is-idempotent-projecting-twice-equals-projecting-once-for-a-projection-tensor"

zil attach ricci_projection_decomposition where
  supported_by @ "lean:LorentzGroup.transpose_one",
  formalizes @ "claim:the-metric-ricci-tensor-decomposes-into-four-projection-blocks-the-intrinsic-h-h-the-mixed-h-v-and-v-h-and-the-transverse-v-v-parts-from-the-identity-splitting-h-plus-v"

zil_file_contract physlib.projectedRicciDecomposition where
  promises "The projection decomposition of the metric Ricci tensor of Gowdy section five. A projection tensor with complement V equals identity minus H decomposes the symmetric Ricci tensor into projection blocks. Projecting both indices with H gives H transpose times Ricci times H. The projected Ricci is symmetric when the Ricci tensor is, and the H-projection is idempotent, projecting twice equals projecting once, for a projection tensor. From the identity splitting H plus V equals the identity, the Ricci tensor decomposes into four blocks: the intrinsic H-H block, the mixed H-V and V-H blocks, and the transverse V-V block. Honest scope: the algebraic projection decomposition of a symmetric zero-two tensor; the identification of the intrinsic block with the intrinsic Ricci of the subsurface, the Gauss equation, is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.complementProjection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor"
  ]
  forbids_substitutes [
    "reading the algebraic four-block projection decomposition as the Gauss equation identifying the intrinsic block with the subsurface Ricci tensor"
  ]
  witnessed_by [
    projectRicci_symm,
    projectRicci_idem,
    ricci_projection_decomposition
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.projectedRicciDecomposition
