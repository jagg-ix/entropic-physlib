/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition -/

/-!
# The projection gradient decomposition (Gowdy 1994 §IV)

Differentiating the projection constraint `H² = H` gives the **differentiated projection identity**
`(∇H)·H + H·(∇H) = ∇H` (`IsProjectionGradient`).  From it alone the projection gradient `∇H` decomposes
into two cross-projected pieces — the extrinsic and transpose curvatures — with the two *diagonal*
projections vanishing:

`H·(∇H)·H = 0`,   `V·(∇H)·V = 0`,   `∇H = H·(∇H)·V + V·(∇H)·H`   (Gowdy Eq. 12).

Here `V·(∇H)·H` is the **extrinsic curvature** `h_H` (Eq. 7, the second fundamental form of the projection)
and `H·(∇H)·V` is the **transpose curvature** `h_H^T` (Eq. 9).  This is the metric-free, connection-agnostic
core of Gowdy §IV.B, obtained purely from the projection algebra.

* `IsProjectionGradient` — the differentiated constraint `(∇H)H + H(∇H) = ∇H`.
* `extrinsicCurvature` / `transposeCurvature` — `V(∇H)H` / `H(∇H)V`.
* `projection_hh_zero`, `projection_vv_zero` — the diagonal projections vanish.
* `projectionGradient_decomposition` — `∇H = h_H^T + h_H` (Eq. 12).
* `extrinsicCurvature_projection_identity` — `V h_H H = h_H` (the Eq. 8 projection identity).

Honest scope: the algebraic decomposition of the projection gradient from the differentiated constraint;
the constraint stands for the covariant derivative of `H² = H`, but the connection/derivative operator
itself is not formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The differentiated projection identity** `(∇H)·H + H·(∇H) = ∇H` — the covariant derivative of the
constraint `H² = H`. -/
def IsProjectionGradient (H dH : Matrix ι ι ℝ) : Prop := dH * H + H * dH = dH

/-- **The extrinsic curvature** `h_H = V·(∇H)·H` (Gowdy Eq. 7, the second fundamental form). -/
def extrinsicCurvature (H dH : Matrix ι ι ℝ) : Matrix ι ι ℝ := complementProjection H * dH * H

/-- **The transpose curvature** `h_H^T = H·(∇H)·V` (Gowdy Eq. 9). -/
def transposeCurvature (H dH : Matrix ι ι ℝ) : Matrix ι ι ℝ := H * dH * complementProjection H

/-- **The `HH` projection of the gradient vanishes** `H·(∇H)·H = 0`. -/
@[zil_level physical_theorem]
theorem projection_hh_zero (H dH : Matrix ι ι ℝ) (hH : H * H = H) (hd : IsProjectionGradient H dH) :
    H * dH * H = 0 := by
  unfold IsProjectionGradient at hd
  have hkey : H * (dH * H) + H * (H * dH) = H * dH := by rw [← mul_add, hd]
  rw [← mul_assoc, ← mul_assoc, hH] at hkey
  have hz := eq_sub_of_add_eq hkey
  rwa [sub_self] at hz

/-- **The differentiated constraint holds for the complement too** `(∇H)·V + V·(∇H) = ∇H`. -/
theorem isProjectionGradient_complement (H dH : Matrix ι ι ℝ) (hd : IsProjectionGradient H dH) :
    IsProjectionGradient (complementProjection H) dH := by
  unfold IsProjectionGradient complementProjection at *
  rw [mul_sub, mul_one, sub_mul, one_mul, sub_add_sub_comm, hd]
  abel

/-- **The `VV` projection of the gradient vanishes** `V·(∇H)·V = 0`. -/
@[zil_level physical_theorem]
theorem projection_vv_zero (H dH : Matrix ι ι ℝ) (hH : H * H = H) (hd : IsProjectionGradient H dH) :
    complementProjection H * dH * complementProjection H = 0 :=
  projection_hh_zero (complementProjection H) dH ((show IsProjectionTensor H from hH).complement)
    (isProjectionGradient_complement H dH hd)

/-- **The projection gradient decomposition** `∇H = H·(∇H)·V + V·(∇H)·H = h_H^T + h_H` (Gowdy Eq. 12) —
the gradient of a projection tensor is the sum of its transpose and extrinsic curvatures. -/
@[zil_level physical_theorem]
theorem projectionGradient_decomposition (H dH : Matrix ι ι ℝ) (hH : H * H = H)
    (hd : IsProjectionGradient H dH) :
    dH = transposeCurvature H dH + extrinsicCurvature H dH := by
  unfold transposeCurvature extrinsicCurvature
  have hhh := projection_hh_zero H dH hH hd
  have hvv := projection_vv_zero H dH hH hd
  have hexpand : (H + complementProjection H) * dH * (H + complementProjection H)
      = H * dH * H + H * dH * complementProjection H
        + complementProjection H * dH * H + complementProjection H * dH * complementProjection H := by
    simp only [add_mul, mul_add]; abel
  rw [add_complementProjection, one_mul, mul_one] at hexpand
  conv_lhs => rw [hexpand]
  rw [hhh, hvv]
  abel

/-- **The extrinsic curvature obeys the projection identity** `V·h_H·H = h_H` (Gowdy Eq. 8) — it lives in
the `V ⊗ H` projection subspace. -/
@[zil_level physical_theorem]
theorem extrinsicCurvature_projection_identity (H dH : Matrix ι ι ℝ) (hH : H * H = H) :
    complementProjection H * extrinsicCurvature H dH * H = extrinsicCurvature H dH := by
  unfold extrinsicCurvature
  have hV : complementProjection H * complementProjection H = complementProjection H :=
    (show IsProjectionTensor H from hH).complement
  rw [show complementProjection H * (complementProjection H * dH * H) * H
      = complementProjection H * complementProjection H * dH * (H * H) from by
        simp only [mul_assoc], hV, hH]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

zil attach projection_hh_zero where
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:the-h-h-diagonal-projection-of-the-gradient-of-a-projection-tensor-vanishes-h-times-grad-h-times-h-equals-zero-from-the-differentiated-idempotency-constraint"

zil attach projectionGradient_decomposition where
  formalizes @ "claim:the-gradient-of-a-projection-tensor-decomposes-as-the-sum-of-its-transpose-curvature-h-grad-h-v-and-extrinsic-curvature-v-grad-h-h-gowdy-equation-twelve",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_hh_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_vv_zero"

zil attach extrinsicCurvature_projection_identity where
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:the-extrinsic-curvature-v-grad-h-h-obeys-the-projection-identity-v-times-it-times-h-equals-itself-it-lives-in-the-v-tensor-h-projection-subspace-gowdy-equation-eight"

zil_file_contract physlib.projectionGradientDecomposition where
  promises "The projection gradient decomposition of Gowdy section four. Differentiating the projection constraint H squared equals H gives the differentiated projection identity, the gradient of H times H plus H times the gradient equals the gradient. From it the gradient of a projection tensor decomposes into two cross-projected pieces with the diagonal projections vanishing: H times the gradient times H is zero, V times the gradient times V is zero, and the gradient equals H times the gradient times V plus V times the gradient times H, Gowdy equation twelve. The piece V times the gradient times H is the extrinsic curvature, the second fundamental form of the projection, and H times the gradient times V is the transpose curvature. The extrinsic curvature obeys the projection identity that V times it times H equals itself, so it lives in the V-tensor-H projection subspace. Honest scope: the algebraic decomposition of the projection gradient from the differentiated constraint; the constraint stands for the covariant derivative of the idempotency constraint, but the connection or derivative operator itself is not formalized here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.complementProjection"
  ]
  forbids_substitutes [
    "reading the algebraic gradient decomposition from the differentiated constraint as a formalization of the covariant-derivative operator or the full projected Bianchi identities"
  ]
  witnessed_by [
    projection_hh_zero,
    projection_vv_zero,
    projectionGradient_decomposition,
    extrinsicCurvature_projection_identity
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.projectionGradientDecomposition

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism -/

/-!
# The covariant derivative of a mixed `(1,1)` tensor (endomorphism)

The repository carries the covariant derivative of vectors (`covariantDerivVectorAt`) and `(2,0)` tensors,
but not the **mixed `(1,1)`** case in endomorphism (matrix) form.  For a `(1,1)` tensor `M^α_β` and a
connection whose direction-`μ` matrix is `(Γ_μ)^α_ρ = Γ^α_{μρ}`,

`(∇_μ M)^α_β = ∂_μ M^α_β + Γ^α_{μρ}M^ρ_β − Γ^ρ_{μβ}M^α_ρ`,   i.e.   `∇_μ M = ∂_μ M + Γ_μ M − M Γ_μ`,

the covariant derivative is the partial derivative plus the matrix commutator `[Γ_μ, M]`.  This is exactly
the operator a projection tensor (an endomorphism) requires.  It obeys the Leibniz rule, annihilates the
identity, and reduces to `∂` at a normal frame — and, crucially, applied to a **projection field**
(`H² = H`) it produces a Gowdy *projection gradient*, discharging the hypothesis of
`ProjectionGradientDecomposition`.

* `covariantDerivEndo` — `∇_μ M = ∂_μ M + Γ_μ M − M Γ_μ`.
* `covariantDerivEndo_flat`, `covariantDerivEndo_one` — reduces to `∂` at `Γ = 0`; `∇I = 0`.
* `covariantDerivEndo_leibniz` — `∇_μ(MN) = (∇_μ M)N + M(∇_μ N)`.
* `covariantDerivEndo_isProjectionGradient` — the covariant derivative of a projection field satisfies
  the differentiated constraint `(∇H)H + H(∇H) = ∇H`, closing the Gowdy §IV gap.

Honest scope: the endomorphism covariant derivative and its algebraic identities; the partial-derivative
data `∂_μ M` and the product rule for it are supplied as inputs (matching the repository's pointwise-jet
covariant-derivative carriers), not a differential-geometric derivative object.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The covariant derivative of a mixed `(1,1)` tensor** `∇_μ M = ∂_μ M + Γ_μ M − M Γ_μ`, the partial
derivative plus the matrix commutator `[Γ_μ, M]`.  (`Γ μ` is the direction-`μ` connection matrix,
`dM μ = ∂_μ M`.) -/
def covariantDerivEndo (Γ dM : ι → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (μ : ι) : Matrix ι ι ℝ :=
  dM μ + Γ μ * M - M * Γ μ

/-- **At a normal frame `Γ = 0` the covariant derivative is the partial derivative.** -/
@[zil_level physical_theorem]
theorem covariantDerivEndo_flat (dM : ι → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (μ : ι) :
    covariantDerivEndo (fun _ => 0) dM M μ = dM μ := by
  simp [covariantDerivEndo]

/-- **The covariant derivative annihilates the identity** `∇_μ I = 0`. -/
@[zil_level physical_theorem]
theorem covariantDerivEndo_one (Γ : ι → Matrix ι ι ℝ) (μ : ι) :
    covariantDerivEndo Γ (fun _ => 0) 1 μ = 0 := by
  simp [covariantDerivEndo]

/-- **The Leibniz (product) rule** `∇_μ(MN) = (∇_μ M)N + M(∇_μ N)` — the `M Γ_μ N` cross terms cancel.
(`dM, dN` are `∂M, ∂N`; the product-rule partial `∂(MN) = (∂M)N + M(∂N)` is used on the left.) -/
@[zil_level physical_theorem]
theorem covariantDerivEndo_leibniz (Γ dM dN : ι → Matrix ι ι ℝ) (M N : Matrix ι ι ℝ) (μ : ι) :
    covariantDerivEndo Γ (fun ν => dM ν * N + M * dN ν) (M * N) μ
      = covariantDerivEndo Γ dM M μ * N + M * covariantDerivEndo Γ dN N μ := by
  unfold covariantDerivEndo
  simp only [add_mul, mul_add, mul_sub, sub_mul, mul_assoc]
  abel

/-- **The covariant derivative of a projection field is a projection gradient** — if `H² = H` and its
partial derivative obeys the differentiated constraint `(∂H)H + H(∂H) = ∂H`, then `∇_μ H` satisfies
`(∇_μ H)H + H(∇_μ H) = ∇_μ H`, discharging the hypothesis of the Gowdy §IV decomposition. -/
@[zil_level bridge_theorem]
theorem covariantDerivEndo_isProjectionGradient (Γ dH : ι → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (μ : ι)
    (hH : H * H = H) (hdH : dH μ * H + H * dH μ = dH μ) :
    IsProjectionGradient H (covariantDerivEndo Γ dH H μ) := by
  unfold IsProjectionGradient covariantDerivEndo
  have hΓHH : Γ μ * H * H = Γ μ * H := by rw [mul_assoc, hH]
  have hHHΓ : H * (H * Γ μ) = H * Γ μ := by rw [← mul_assoc, hH]
  have key : (dH μ + Γ μ * H - H * Γ μ) * H + H * (dH μ + Γ μ * H - H * Γ μ)
      = dH μ * H + H * dH μ + Γ μ * H - H * Γ μ := by
    simp only [add_mul, mul_add, mul_sub, sub_mul]
    rw [hΓHH, hHHΓ, mul_assoc H (Γ μ) H]
    abel
  rw [key, hdH]

end Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

zil attach covariantDerivEndo_one where
  formalizes @ "claim:the-mixed-one-one-endomorphism-covariant-derivative-partial-plus-the-connection-commutator-annihilates-the-identity-tensor"

zil attach covariantDerivEndo_leibniz where
  formalizes @ "claim:the-mixed-one-one-endomorphism-covariant-derivative-obeys-the-leibniz-product-rule-with-the-connection-commutator-cross-terms-cancelling"

zil attach covariantDerivEndo_isProjectionGradient where
  formalizes @ "claim:the-covariant-derivative-of-a-projection-tensor-field-h-squared-equals-h-is-a-gowdy-projection-gradient-satisfying-the-differentiated-idempotency-constraint-discharging-the-section-four-hypothesis",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projectionGradient_decomposition"

zil_file_contract physlib.covariantDerivativeEndomorphism where
  promises "The covariant derivative of a mixed one-one tensor in endomorphism matrix form, the gap complementing the repository's vector and two-contravariant covariant derivatives. For a one-one tensor and a connection whose direction-mu matrix is the Christoffel with the derivative index fixed, the covariant derivative is the partial derivative plus the matrix commutator of the connection with the tensor. It reduces to the partial derivative at a normal frame where the connection vanishes, annihilates the identity tensor, and obeys the Leibniz product rule with the connection-commutator cross terms cancelling. Crucially, applied to a projection field with H squared equals H whose partial derivative obeys the differentiated idempotency constraint, it produces a Gowdy projection gradient satisfying that same constraint, discharging the hypothesis of the projection gradient decomposition. Honest scope: the endomorphism covariant derivative and its algebraic identities; the partial-derivative data and its product rule are supplied as pointwise-jet inputs, matching the repository's covariant-derivative carriers, not a differential-geometric derivative object."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.IsProjectionGradient"
  ]
  forbids_substitutes [
    "reading the pointwise-jet endomorphism covariant derivative as a differential-geometric covariant-derivative operator with an actual partial-derivative functor"
  ]
  witnessed_by [
    covariantDerivEndo_flat,
    covariantDerivEndo_one,
    covariantDerivEndo_leibniz,
    covariantDerivEndo_isProjectionGradient
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.covariantDerivativeEndomorphism

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature -/

/-!
# Curvature from the covariant derivative: the Ricci identity

The curvature of the connection is the obstruction to commuting two covariant derivatives.  With the
endomorphism covariant derivative `∇_μ M = ∂_μ M + [Γ_μ, M]`, the second covariant derivative is
`∇_μ ∇_ν M`, and the **curvature two-form**

`F_{μν} = ∂_μ Γ_ν − ∂_ν Γ_μ + [Γ_μ, Γ_ν]`

controls its antisymmetric part by the **Ricci identity**

`[∇_μ, ∇_ν] M = [F_{μν}, M]`.

This connects the covariant-derivative operator to curvature — the algebraic heart of the projection
curvature decomposition (Gowdy §V) and the field-strength `F = dA + A∧A` of gauge theory.

* `curvatureTwoForm`, `curvatureTwoForm_antisymm` — `F_{μν}` and `F_{μν} = −F_{νμ}`.
* `ricci_identity` — `[∇_μ, ∇_ν] M = [F_{μν}, M]` (with commuting mixed partials `∂_μ∂_ν M = ∂_ν∂_μ M`).
* `ricci_identity_flat` — a flat connection (`F_{μν} = 0`) has commuting covariant derivatives.

Honest scope: the algebraic Ricci identity from the pointwise-jet data `(Γ, ∂Γ, M, ∂M, ∂∂M)` with the
commuting-partials hypothesis; the differential-geometric derivative object is not formalized.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature

open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The curvature two-form** `F_{μν} = ∂_μ Γ_ν − ∂_ν Γ_μ + [Γ_μ, Γ_ν]` (`dΓ μ ν = ∂_μ Γ_ν`). -/
def curvatureTwoForm (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (μ ν : ι) : Matrix ι ι ℝ :=
  dΓ μ ν - dΓ ν μ + Γ μ * Γ ν - Γ ν * Γ μ

/-- **The curvature two-form is antisymmetric** `F_{μν} = −F_{νμ}`. -/
@[zil_level physical_theorem]
theorem curvatureTwoForm_antisymm (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (μ ν : ι) :
    curvatureTwoForm Γ dΓ μ ν = -curvatureTwoForm Γ dΓ ν μ := by
  unfold curvatureTwoForm; abel

/-- **The second covariant derivative** `∇_μ ∇_ν M` — the derivative in direction `μ` of `∇_ν M`, with
`∂_μ(∇_ν M) = ∂_μ∂_ν M + (∂_μ Γ_ν)M + Γ_ν ∂_μ M − (∂_μ M)Γ_ν − M(∂_μ Γ_ν)`. -/
def covariantSecondDerivEndo (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (dM : ι → Matrix ι ι ℝ) (ddM : ι → ι → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (μ ν : ι) :
    Matrix ι ι ℝ :=
  (ddM μ ν + dΓ μ ν * M + Γ ν * dM μ - dM μ * Γ ν - M * dΓ μ ν)
    + Γ μ * (dM ν + Γ ν * M - M * Γ ν)
    - (dM ν + Γ ν * M - M * Γ ν) * Γ μ

/-- **The Ricci identity** `[∇_μ, ∇_ν] M = [F_{μν}, M]` — the antisymmetrized second covariant derivative
of a `(1,1)` tensor equals the commutator of the curvature two-form with the tensor (for commuting mixed
partials `∂_μ∂_ν M = ∂_ν∂_μ M`).  Curvature is the obstruction to commuting covariant derivatives. -/
@[zil_level physical_theorem]
theorem ricci_identity (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (dM : ι → Matrix ι ι ℝ)
    (ddM : ι → ι → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (μ ν : ι) (hsym : ddM μ ν = ddM ν μ) :
    covariantSecondDerivEndo Γ dΓ dM ddM M μ ν - covariantSecondDerivEndo Γ dΓ dM ddM M ν μ
      = curvatureTwoForm Γ dΓ μ ν * M - M * curvatureTwoForm Γ dΓ μ ν := by
  unfold covariantSecondDerivEndo curvatureTwoForm
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  rw [hsym]
  abel

/-- **A flat connection has commuting covariant derivatives** `F_{μν} = 0 ⇒ [∇_μ, ∇_ν] M = 0`. -/
@[zil_level physical_theorem]
theorem ricci_identity_flat (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ) (dM : ι → Matrix ι ι ℝ)
    (ddM : ι → ι → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (μ ν : ι) (hsym : ddM μ ν = ddM ν μ)
    (hflat : curvatureTwoForm Γ dΓ μ ν = 0) :
    covariantSecondDerivEndo Γ dΓ dM ddM M μ ν - covariantSecondDerivEndo Γ dΓ dM ddM M ν μ = 0 := by
  rw [ricci_identity Γ dΓ dM ddM M μ ν hsym, hflat, zero_mul, mul_zero, sub_zero]

end Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature

zil attach curvatureTwoForm_antisymm where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-curvature-two-form-field-strength-partial-mu-gamma-nu-minus-partial-nu-gamma-mu-plus-the-connection-commutator-is-antisymmetric-in-its-two-indices"

zil attach ricci_identity where
  formalizes @ "claim:the-ricci-identity-the-antisymmetrized-second-covariant-derivative-of-a-one-one-tensor-equals-the-commutator-of-the-curvature-two-form-with-the-tensor-curvature-is-the-obstruction-to-commuting-covariant-derivatives",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism.covariantDerivEndo"

zil attach ricci_identity_flat where
  supported_by @ "lean:ricci_identity",
  formalizes @ "claim:a-flat-connection-with-vanishing-curvature-two-form-has-commuting-covariant-derivatives"

zil_file_contract physlib.covariantDerivativeCurvature where
  promises "Curvature from the covariant derivative, the Ricci identity. The curvature of the connection is the obstruction to commuting two covariant derivatives. The curvature two-form is the partial derivative of the connection antisymmetrized plus the connection commutator, and it is antisymmetric in its two indices. With the endomorphism covariant derivative, the second covariant derivative in direction mu of the covariant derivative in direction nu satisfies the Ricci identity: the antisymmetrized second covariant derivative of a one-one tensor equals the commutator of the curvature two-form with the tensor, provided the mixed partials commute. A flat connection with vanishing curvature two-form therefore has commuting covariant derivatives. This connects the covariant-derivative operator to curvature, the algebraic heart of the projection curvature decomposition and the gauge field strength. Honest scope: the algebraic Ricci identity from the pointwise-jet data of connection, its derivative, and the tensor with its first and second derivatives, under the commuting-partials hypothesis; the differential-geometric derivative object is not formalized here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism.covariantDerivEndo"
  ]
  forbids_substitutes [
    "reading the algebraic pointwise-jet Ricci identity as a differential-geometric curvature-operator theorem with an actual second-covariant-derivative functor"
  ]
  witnessed_by [
    curvatureTwoForm_antisymm,
    ricci_identity,
    ricci_identity_flat
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.covariantDerivativeCurvature

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative -/

/-!
# The projected covariant derivative (Gowdy §IV.C)

A projection tensor `H` splits the covariant derivative of a vector into a **projected** part `Dv = H(∇v)`
(the derivative within the projection subspace, Gowdy Eq. 13) and an **antiprojected** part `D̄v = V(∇v)`
(Eq. 14), with `∇v = Dv + D̄v` from `H + V = I`.  Applied to the projection tensor itself, the covariant
derivative decomposes into the Gowdy transpose and extrinsic curvatures — grounding the §IV decomposition
on the actual `(1,1)` covariant-derivative operator.

* `projectedCovariantDeriv` / `antiprojectedCovariantDeriv` — `H(∇v)` and `V(∇v)`.
* `covariantDeriv_split` — `∇v = Dv + D̄v` (Gowdy Eqs. 13–14).
* `projectedCovariantDeriv_idem` — `Dv` lies in the projection subspace `H(Dv) = Dv`.
* `covariantDerivEndo_projection_decomposition` — the covariant derivative of a projection field equals
  its transpose plus extrinsic curvature (Gowdy Eq. 12 grounded on `∇`).

Honest scope: the projected/antiprojected split of a supplied covariant derivative and the projection-field
decomposition; the covariant-derivative data itself is taken from the endomorphism operator.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The projected covariant derivative** `Dv = H(∇v)` (Gowdy Eq. 13) — the derivative within the
projection subspace (`cdv` is the covariant derivative `∇_μ v`). -/
def projectedCovariantDeriv (H : Matrix ι ι ℝ) (cdv : ι → ℝ) : ι → ℝ := H.mulVec cdv

/-- **The antiprojected covariant derivative** `D̄v = V(∇v)` (Gowdy Eq. 14). -/
def antiprojectedCovariantDeriv (H : Matrix ι ι ℝ) (cdv : ι → ℝ) : ι → ℝ :=
  (complementProjection H).mulVec cdv

/-- **The covariant derivative splits** `∇v = Dv + D̄v` (Gowdy Eqs. 13–14) — from `H + V = I`. -/
@[zil_level physical_theorem]
theorem covariantDeriv_split (H : Matrix ι ι ℝ) (cdv : ι → ℝ) :
    projectedCovariantDeriv H cdv + antiprojectedCovariantDeriv H cdv = cdv := by
  unfold projectedCovariantDeriv antiprojectedCovariantDeriv complementProjection
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- **The projected covariant derivative lies in the projection subspace** `H(Dv) = Dv`. -/
@[zil_level physical_theorem]
theorem projectedCovariantDeriv_idem (H : Matrix ι ι ℝ) (cdv : ι → ℝ) (hH : H * H = H) :
    H.mulVec (projectedCovariantDeriv H cdv) = projectedCovariantDeriv H cdv :=
  (show IsProjectionTensor H from hH).mulVec_fixed cdv

/-- **The covariant derivative of a projection field decomposes** `∇_μ H = h_H^T + h_H` — grounding the
Gowdy Eq. 12 decomposition on the actual `(1,1)` covariant-derivative operator (for a projection field
`H² = H` whose partial derivative obeys the differentiated constraint). -/
@[zil_level bridge_theorem]
theorem covariantDerivEndo_projection_decomposition (Γ dH : ι → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (μ : ι)
    (hH : H * H = H) (hdH : dH μ * H + H * dH μ = dH μ) :
    covariantDerivEndo Γ dH H μ
      = transposeCurvature H (covariantDerivEndo Γ dH H μ)
        + extrinsicCurvature H (covariantDerivEndo Γ dH H μ) :=
  projectionGradient_decomposition H (covariantDerivEndo Γ dH H μ) hH
    (covariantDerivEndo_isProjectionGradient Γ dH H μ hH hdH)

end Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative

zil attach covariantDeriv_split where
  formalizes @ "claim:the-covariant-derivative-of-a-vector-splits-as-the-projected-covariant-derivative-h-grad-v-plus-the-antiprojected-covariant-derivative-v-grad-v-gowdy-equations-thirteen-and-fourteen"

zil attach projectedCovariantDeriv_idem where
  supported_by @ "lean:IsProjectionTensor.mulVec_fixed",
  formalizes @ "claim:the-projected-covariant-derivative-lies-in-the-projection-subspace-h-of-d-v-equals-d-v"

zil attach covariantDerivEndo_projection_decomposition where
  formalizes @ "claim:the-covariant-derivative-of-a-projection-field-decomposes-into-its-transpose-curvature-plus-extrinsic-curvature-grounding-the-gowdy-decomposition-on-the-actual-covariant-derivative-operator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism.covariantDerivEndo_isProjectionGradient"

zil_file_contract physlib.projectedCovariantDerivative where
  promises "The projected covariant derivative of Gowdy section four C. A projection tensor splits the covariant derivative of a vector into a projected part H times the covariant derivative, the derivative within the projection subspace, and an antiprojected part V times the covariant derivative, and the covariant derivative equals the projected plus antiprojected parts from H plus V equals the identity. The projected covariant derivative lies in the projection subspace, H of it equals it. Applied to a projection field with H squared equals H whose partial derivative obeys the differentiated constraint, the covariant derivative decomposes into the transpose curvature plus the extrinsic curvature, grounding the Gowdy decomposition on the actual one-one covariant-derivative operator. Honest scope: the projected and antiprojected split of a supplied covariant derivative and the projection-field decomposition; the covariant-derivative data itself is taken from the endomorphism operator."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.complementProjection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism.covariantDerivEndo"
  ]
  forbids_substitutes [
    "reading the algebraic projected/antiprojected split as a differential-geometric intrinsic covariant derivative on the projected subbundle"
  ]
  witnessed_by [
    covariantDeriv_split,
    projectedCovariantDeriv_idem,
    covariantDerivEndo_projection_decomposition
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.projectedCovariantDerivative

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi -/

/-!
# The Bianchi identity for the curvature two-form

The curvature two-form `F_{μν} = ∂_μ Γ_ν − ∂_ν Γ_μ + [Γ_μ, Γ_ν]` (`CovariantDerivativeCurvature`) obeys
the **differential (second) Bianchi identity**

`D_μ F_{νρ} + D_ν F_{ρμ} + D_ρ F_{μν} = 0`,   `D_μ F_{νρ} = ∂_μ F_{νρ} + [Γ_μ, F_{νρ}]`,

the cyclic sum of its gauge-covariant derivatives.  This is the gauge/connection form of the second Bianchi
identity: the `[Γ,[Γ,Γ]]` terms cancel by the Jacobi identity and the `∂∂Γ` terms cancel by commuting
mixed partials — the same structure as `SecondBianchiFromConnection`, now for the curvature two-form.

* `dCurvatureTwoForm` — `∂_μ F_{νρ}`.
* `gaugeCovariantDerivCurvature` — `D_μ F_{νρ} = ∂_μ F_{νρ} + [Γ_μ, F_{νρ}]`.
* `curvatureTwoForm_bianchi` — the cyclic sum vanishes.

Honest scope: the algebraic Bianchi identity from the pointwise-jet data `(Γ, ∂Γ, ∂∂Γ)` with the
commuting-partials hypothesis on `∂∂Γ`; no differential-geometric derivative object.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi

open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The partial derivative of the curvature two-form** `∂_μ F_{νρ}` (`ddΓ μ ν ρ = ∂_μ∂_ν Γ_ρ`). -/
def dCurvatureTwoForm (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (μ ν ρ : ι) : Matrix ι ι ℝ :=
  ddΓ μ ν ρ - ddΓ μ ρ ν + dΓ μ ν * Γ ρ + Γ ν * dΓ μ ρ - dΓ μ ρ * Γ ν - Γ ρ * dΓ μ ν

/-- **The gauge-covariant derivative of the curvature two-form** `D_μ F_{νρ} = ∂_μ F_{νρ} + [Γ_μ, F_{νρ}]`
(the curvature is Lie-algebra valued, transforming in the adjoint). -/
def gaugeCovariantDerivCurvature (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (μ ν ρ : ι) : Matrix ι ι ℝ :=
  dCurvatureTwoForm Γ dΓ ddΓ μ ν ρ
    + Γ μ * curvatureTwoForm Γ dΓ ν ρ - curvatureTwoForm Γ dΓ ν ρ * Γ μ

/-- **The Bianchi identity** `D_μ F_{νρ} + D_ν F_{ρμ} + D_ρ F_{μν} = 0` — the cyclic sum of gauge-covariant
derivatives of the curvature two-form vanishes.  The `[Γ,[Γ,Γ]]` terms cancel by the Jacobi identity and
the `∂∂Γ` terms by commuting mixed partials (`ddΓ` symmetric in its first two indices). -/
@[zil_level physical_theorem]
theorem curvatureTwoForm_bianchi (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (ddΓ : ι → ι → ι → Matrix ι ι ℝ) (μ ν ρ : ι)
    (hsym : ∀ a b c, ddΓ a b c = ddΓ b a c) :
    gaugeCovariantDerivCurvature Γ dΓ ddΓ μ ν ρ + gaugeCovariantDerivCurvature Γ dΓ ddΓ ν ρ μ
      + gaugeCovariantDerivCurvature Γ dΓ ddΓ ρ μ ν = 0 := by
  unfold gaugeCovariantDerivCurvature dCurvatureTwoForm curvatureTwoForm
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  rw [hsym ν μ ρ, hsym ρ μ ν, hsym ρ ν μ]
  abel

end Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi

zil attach curvatureTwoForm_bianchi where
  formalizes @ "claim:the-differential-second-bianchi-identity-for-the-curvature-two-form-the-cyclic-sum-of-its-gauge-covariant-derivatives-vanishes-the-jacobi-terms-cancel-and-the-double-partial-terms-cancel-by-commuting-mixed-partials",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.curvatureTwoForm"

zil_file_contract physlib.curvatureTwoFormBianchi where
  promises "The differential second Bianchi identity for the curvature two-form. The curvature two-form obeys the identity that the cyclic sum of its gauge-covariant derivatives vanishes: the gauge-covariant derivative of the curvature is its partial derivative plus the commutator of the connection with the curvature, and the cyclic sum over the three indices is zero. This is the gauge or connection form of the second Bianchi identity: the nested-commutator Jacobi terms cancel by the Jacobi identity, and the double-partial-derivative terms cancel by commuting mixed partials, the same structure as the second Bianchi from a connection, now for the curvature two-form. Honest scope: the algebraic Bianchi identity from the pointwise-jet data of connection and its first and second derivatives, under the commuting-partials hypothesis on the second derivative; no differential-geometric derivative object is formalized."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.curvatureTwoForm"
  ]
  forbids_substitutes [
    "reading the algebraic pointwise-jet Bianchi identity as a differential-geometric second Bianchi theorem with an actual covariant-derivative functor on curvature two-forms"
  ]
  witnessed_by [
    curvatureTwoForm_bianchi
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.curvatureTwoFormBianchi

