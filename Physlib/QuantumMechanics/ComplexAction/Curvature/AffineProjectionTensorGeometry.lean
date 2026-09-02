/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry -/

/-!
# Affine projection tensor geometry

Following R. H. Gowdy, *Affine projection tensor geometry*, J. Math. Phys. **35** (1994) 1274 — the
geometry of a projection tensor field `H` (an idempotent endomorphism `H² = H`, §II Eq. 1) valid for an
*arbitrary* connection and a *tilted* (not necessarily metric-orthogonal) projection.  The complement
`V = I − H` is the complementary projection, `VH = HV = 0`; together they split every tangent space into
`HT_P ⊕ VT_P`.  A projection is **normal** (orthogonal, §III.A) exactly when its lowered form `H_{αβ}`
is symmetric.

* `IsProjectionTensor` — `H² = H`.
* `complementProjection`, `add_complementProjection` — `V = I − H`, `H + V = I`.
* `IsProjectionTensor.complement`, `mul_complement`, `complement_mul` — `V² = V`, `HV = 0`, `VH = 0`.
* `IsProjectionTensor.transpose` — the pull-back `H*` is a projection.
* `IsProjectionTensor.mulVec_fixed` — `H` acts as the identity on its image `HT_P`.
* `IsNormalProjection` — the lowered projection `g H` is symmetric (the §III.A normality criterion).

Honest scope: the projection-tensor algebra (§II–III) at the endomorphism/matrix level; the projection
decompositions of the connection and curvature (§IV–V) and the projected Bianchi identities are not
carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A projection tensor field** is an idempotent endomorphism `H² = H` (Gowdy Eq. 1). -/
def IsProjectionTensor (H : Matrix ι ι ℝ) : Prop := H * H = H

/-- **The complementary projection** `V = I − H` (Gowdy Eq. 2). -/
def complementProjection (H : Matrix ι ι ℝ) : Matrix ι ι ℝ := 1 - H

/-- **`H` and its complement sum to the identity** `H + V = I`. -/
theorem add_complementProjection (H : Matrix ι ι ℝ) : H + complementProjection H = 1 := by
  unfold complementProjection; abel

/-- **The complement of a projection is a projection** `V² = V`. -/
@[zil_level structural]
theorem IsProjectionTensor.complement {H : Matrix ι ι ℝ} (h : IsProjectionTensor H) :
    IsProjectionTensor (complementProjection H) := by
  unfold IsProjectionTensor complementProjection at *
  rw [sub_mul, one_mul, mul_sub, mul_one, h, sub_self, sub_zero]

/-- **A projection annihilates its complement** `HV = 0`. -/
@[zil_level structural]
theorem IsProjectionTensor.mul_complement {H : Matrix ι ι ℝ} (h : IsProjectionTensor H) :
    H * complementProjection H = 0 := by
  unfold IsProjectionTensor complementProjection at *
  rw [mul_sub, mul_one, h, sub_self]

/-- **The complement annihilates the projection** `VH = 0`. -/
@[zil_level structural]
theorem IsProjectionTensor.complement_mul {H : Matrix ι ι ℝ} (h : IsProjectionTensor H) :
    complementProjection H * H = 0 := by
  unfold IsProjectionTensor complementProjection at *
  rw [sub_mul, one_mul, h, sub_self]

/-- **The pull-back `H*` is also a projection** `(Hᵀ)² = Hᵀ` — the projection acts on cotangent spaces. -/
@[zil_level structural]
theorem IsProjectionTensor.transpose {H : Matrix ι ι ℝ} (h : IsProjectionTensor H) :
    IsProjectionTensor Hᵀ := by
  unfold IsProjectionTensor at *
  calc Hᵀ * Hᵀ = (H * H)ᵀ := by rw [Matrix.transpose_mul]
    _ = Hᵀ := congrArg Matrix.transpose h

/-- **A projection acts as the identity on its image** `H(Hv) = Hv` for every `v` — the projection
identity `Hv = v` on `HT_P`. -/
@[zil_level structural]
theorem IsProjectionTensor.mulVec_fixed {H : Matrix ι ι ℝ} (h : IsProjectionTensor H) (v : ι → ℝ) :
    H.mulVec (H.mulVec v) = H.mulVec v := by
  rw [Matrix.mulVec_mulVec, h]

/-- **A normal (orthogonal) projection** — the lowered projection `H_{αβ} = g_{αγ}H^γ_β` is symmetric
(Gowdy §III.A: `H` normal ⟺ `H_{αβ} = H_{βα}`). -/
def IsNormalProjection (g H : Matrix ι ι ℝ) : Prop := (g * H)ᵀ = g * H

end Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

zil attach IsProjectionTensor.complement where
  formalizes @ "claim:the-complement-of-an-affine-projection-tensor-i-minus-h-is-itself-a-projection-tensor-v-squared-equals-v"

zil attach IsProjectionTensor.mul_complement where
  formalizes @ "claim:an-affine-projection-tensor-annihilates-its-complement-h-times-v-equals-zero"

zil attach IsProjectionTensor.transpose where
  formalizes @ "claim:the-pull-back-transpose-of-an-affine-projection-tensor-is-also-a-projection-tensor-acting-on-cotangent-spaces"

zil attach IsProjectionTensor.mulVec_fixed where
  formalizes @ "claim:an-affine-projection-tensor-acts-as-the-identity-on-its-image-h-of-h-v-equals-h-v-the-projection-identity"

zil_file_contract physlib.affineProjectionTensorGeometry where
  promises "The affine projection tensor geometry of Gowdy, the geometry of a projection tensor field, an idempotent endomorphism H squared equals H, valid for an arbitrary connection and a tilted not necessarily metric-orthogonal projection. The complement V equals identity minus H is the complementary projection: it is itself a projection, V squared equals V; the projection annihilates its complement, H times V equals zero, and the complement annihilates the projection, V times H equals zero; and H plus V equals the identity, splitting every tangent space. The pull-back transpose of H is also a projection, acting on cotangent spaces. A projection acts as the identity on its image, H of H v equals H v, the projection identity. A projection is normal, orthogonal, exactly when its lowered form the product g H is symmetric. Honest scope: the projection-tensor algebra at the endomorphism or matrix level; the projection decompositions of the connection and curvature and the projected Bianchi identities are not carried here."
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.complementProjection"
  ]
  forbids_substitutes [
    "reading the projection-tensor algebra as the full projection decomposition of the curvature tensor or the projected Bianchi identities"
  ]
  witnessed_by [
    IsProjectionTensor.complement,
    IsProjectionTensor.mul_complement,
    IsProjectionTensor.complement_mul,
    IsProjectionTensor.transpose,
    IsProjectionTensor.mulVec_fixed
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.affineProjectionTensorGeometry

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace -/

/-!
# The rest-space / spatial projection tensor

The canonical example of an affine projection tensor (Gowdy §III.A) is the rank-one deformation of the
identity by a timelike unit vector `u`:

`H^α_β = δ^α_β + u^α u_β`,   `u_β = g_{βγ}u^γ`.

This is idempotent **iff** `u_α u^α = −1` — and then it is simultaneously

* the **fluid rest-space projector** (with `u` the four-velocity, projecting onto the local rest space), and
* the **ADM spatial projector** onto a spacelike hypersurface (with `u` the unit timelike normal, Eq. 5).

Its complement `V = −u⊗u` is the projector onto the `u`-line (the fluid world-line / normal direction).
For a symmetric metric the rest-space projector is a **normal** (orthogonal) projection.

* `restSpaceProjector` — `H = I + u⊗u^♭`.
* `restSpaceProjector_isProjection` — idempotent when `⟨u,u⟩ = −1`.
* `worldlineProjector_eq_complement` — the complement is `−u⊗u^♭`.
* `restSpaceProjector_isNormal` — normal (orthogonal) for a symmetric metric.

Honest scope: the algebraic idempotency/normality of the rank-one deformation projector; its use in the
3+1 curvature decomposition (Gauss–Codazzi) is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The rest-space / spatial projector** `H^α_β = δ^α_β + u^α u_β` (with `u_β = g_{βγ}u^γ`). -/
def restSpaceProjector (g : Matrix ι ι ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  1 + Matrix.vecMulVec u (g.mulVec u)

/-- **Left-multiplying a rank-one tensor by the metric lowers the first factor**
`g · (u ⊗ w) = (gu) ⊗ w`. -/
theorem mul_vecMulVec (g : Matrix ι ι ℝ) (u w : ι → ℝ) :
    g * Matrix.vecMulVec u w = Matrix.vecMulVec (g.mulVec u) w := by
  ext i j
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The rest-space projector is idempotent when `u` is a timelike unit vector** `⟨u,u⟩ = −1`
(`u_α u^α = −1`). -/
@[zil_level physical_theorem]
theorem restSpaceProjector_isProjection (g : Matrix ι ι ℝ) (u : ι → ℝ)
    (h : dotProduct (g.mulVec u) u = -1) : IsProjectionTensor (restSpaceProjector g u) := by
  unfold IsProjectionTensor restSpaceProjector
  have hM : Matrix.vecMulVec u (g.mulVec u) * Matrix.vecMulVec u (g.mulVec u)
      = (-1 : ℝ) • Matrix.vecMulVec u (g.mulVec u) := by
    rw [← h]
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [add_mul, one_mul, mul_add, mul_one, hM, neg_one_smul]
  abel

/-- **The complement of the rest-space projector is the world-line projector** `V = −u⊗u^♭` — the
projector onto the `u`-direction (fluid world-line / hypersurface normal). -/
@[zil_level physical_theorem]
theorem worldlineProjector_eq_complement (g : Matrix ι ι ℝ) (u : ι → ℝ) :
    complementProjection (restSpaceProjector g u) = -Matrix.vecMulVec u (g.mulVec u) := by
  unfold complementProjection restSpaceProjector
  abel

/-- **The rest-space projector is a normal (orthogonal) projection** for a symmetric metric — its lowered
form `g H = g + u^♭⊗u^♭` is symmetric. -/
@[zil_level physical_theorem]
theorem restSpaceProjector_isNormal (g : Matrix ι ι ℝ) (u : ι → ℝ) (hg : gᵀ = g) :
    IsNormalProjection g (restSpaceProjector g u) := by
  unfold IsNormalProjection restSpaceProjector
  rw [mul_add, mul_one, mul_vecMulVec, Matrix.transpose_add, hg]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace

zil attach restSpaceProjector_isProjection where
  formalizes @ "claim:the-rest-space-spatial-projector-identity-plus-u-outer-u-lowered-is-idempotent-a-projection-tensor-exactly-when-u-is-a-timelike-unit-vector-u-dot-u-equals-minus-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor"

zil attach worldlineProjector_eq_complement where
  formalizes @ "claim:the-complement-of-the-rest-space-projector-is-the-world-line-projector-minus-u-outer-u-lowered-the-projector-onto-the-fluid-world-line-or-hypersurface-normal"

zil attach restSpaceProjector_isNormal where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.mul_vecMulVec",
  formalizes @ "claim:the-rest-space-projector-is-a-normal-orthogonal-projection-for-a-symmetric-metric-its-lowered-form-is-symmetric"

zil_file_contract physlib.projectionTensorRestSpace where
  promises "The rest-space or spatial projection tensor, the canonical example of a Gowdy affine projection tensor: the rank-one deformation of the identity by a timelike unit vector, the identity plus u outer u lowered by the metric. It is idempotent, a projection tensor, exactly when u is a timelike unit vector with u dot u equal to minus one, and then it is simultaneously the fluid rest-space projector with u the four-velocity and the ADM spatial projector onto a spacelike hypersurface with u the unit timelike normal. Its complement is the world-line projector minus u outer u lowered, the projector onto the fluid world-line or hypersurface normal direction. For a symmetric metric the rest-space projector is a normal orthogonal projection, its lowered form being symmetric. Honest scope: the algebraic idempotency and normality of the rank-one deformation projector; its use in the three-plus-one Gauss-Codazzi curvature decomposition is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsNormalProjection"
  ]
  forbids_substitutes [
    "reading the algebraic idempotency of the rank-one projector as a three-plus-one Gauss-Codazzi decomposition of the curvature"
  ]
  witnessed_by [
    restSpaceProjector_isProjection,
    worldlineProjector_eq_complement,
    restSpaceProjector_isNormal
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.projectionTensorRestSpace

