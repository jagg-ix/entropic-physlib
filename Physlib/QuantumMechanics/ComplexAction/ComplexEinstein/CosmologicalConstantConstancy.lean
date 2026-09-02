/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
meta import Zil

/-!
# Constancy of the cosmological constant from the contracted Bianchi identity

Jacobson's *Thermodynamics of Spacetime* derivation (`EinsteinEquationOfState`,
`JacobsonClausiusEinstein`) produces the Einstein field equation with cosmological term
`G_{ab} + Λ g_{ab} = κ T_{ab}`, but with the cosmological scalar `Λ` fixed only pointwise (as the
trace part of the equation of state).  Its **spacetime constancy** is the remaining link — and it is
exactly the content of the contracted Bianchi identity together with local conservation.

Applying the covariant divergence `∇^a(·)_{ab}` to the field equation gives, using the contracted
Bianchi identity `∇^a G_{ab} = 0`, conservation `∇^a T_{ab} = 0`, and metric compatibility
`∇^a g_{ab} = 0` (so `∇^a(Λ g_{ab}) = ∇_b Λ` by the Leibniz rule),

`0 + ∇_b Λ = κ · 0`,  hence  `∇_b Λ = 0`,

i.e. the cosmological scalar has vanishing gradient — it is (locally) constant.

* `cosmologicalConstant_gradient_zero` — the abstract Bianchi argument: for a linear divergence
  `Div`, if `G + Λg = κ T`, `Div G = 0`, `Div T = 0`, and `Div (Λg) = gradΛ`, then `gradΛ = 0`.
* `cosmologicalConstant_gradient_zero_matrix` — the same on the repository's matrix Einstein tensor,
  reusing `einsteinFieldEquationCosmological` and the `Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)` of
  `bianchi_implies_conservation`.

Honest scope: `Div` (the covariant divergence), the metric-compatible Leibniz identity
`Div (Λ g) = ∇_b Λ`, and the contracted Bianchi identity are taken as the standard differential-geometry
inputs (mirroring the repository's abstract `Div` in `bianchi_implies_conservation`); the differential
geometry of covariant derivatives is not rebuilt here.  The conclusion `∇_b Λ = 0` is vanishing of the
gradient — the local statement of constancy; promotion to a global constant on a connected spacetime is
the standard `∇Λ = 0 ⟹ Λ` constant fact.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-- **Constancy of the cosmological constant (abstract Bianchi argument).**  For a linear covariant
divergence `Div : Tn →ₗ[ℝ] Cv` (tensors to covectors), if the Einstein field equation with
cosmological term holds, `einstein + metricΛ = κ • stress`, and the contracted Bianchi identity
`Div einstein = 0`, local conservation `Div stress = 0`, and the metric-compatible Leibniz identity
`Div metricΛ = gradΛ` (encoding `∇^a(Λ g_{ab}) = ∇_b Λ`) hold, then the gradient of the cosmological
scalar vanishes: `gradΛ = 0`. -/
@[zil_level bridge_theorem]
theorem cosmologicalConstant_gradient_zero
    {Tn Cv : Type*} [AddCommGroup Tn] [Module ℝ Tn] [AddCommGroup Cv] [Module ℝ Cv]
    (Div : Tn →ₗ[ℝ] Cv) (gradΛ : Cv) (κ : ℝ) (einstein metricΛ stress : Tn)
    (hEFE : einstein + metricΛ = κ • stress)
    (hBianchi : Div einstein = 0)
    (hConservation : Div stress = 0)
    (hMetricLeibniz : Div metricΛ = gradΛ) :
    gradΛ = 0 := by
  have h := congrArg Div hEFE
  rw [map_add, map_smul, hBianchi, zero_add, hConservation, smul_zero, hMetricLeibniz] at h
  exact h

/-- **Constancy of the cosmological constant on the matrix Einstein tensor.**  Instantiation of the
Bianchi argument for the repository's `einsteinTensor` / `einsteinFieldEquationCosmological`: with a
linear divergence `Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)`, the contracted Bianchi identity on `G`,
conservation on `T`, and the metric-compatible Leibniz identity for the cosmological term, the
cosmological gradient vanishes. -/
@[zil_level bridge_theorem]
theorem cosmologicalConstant_gradient_zero_matrix
    {ι : Type*} (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric g T cosmologicalTerm : Matrix ι ι ℝ) (scalarR Λ κ : ℝ) (gradΛ : ι → ℝ)
    (hEFE : einsteinTensor Ric scalarR g + cosmologicalTerm = κ • T)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hConservation : Div T = 0)
    (hMetricLeibniz : Div cosmologicalTerm = gradΛ) :
    gradΛ = 0 :=
  cosmologicalConstant_gradient_zero Div gradΛ κ (einsteinTensor Ric scalarR g) cosmologicalTerm T
    hEFE hBianchi hConservation hMetricLeibniz

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy

zil attach cosmologicalConstant_gradient_zero where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:applying-the-covariant-divergence-to-the-einstein-field-equation-with-cosmological-term-with-the-contracted-bianchi-identity-conservation-and-metric-compatibility-forces-the-gradient-of-the-cosmological-scalar-to-vanish-the-cosmological-constant-is-locally-constant"

zil attach cosmologicalConstant_gradient_zero_matrix where
  formalizes @ "claim:the-cosmological-constant-constancy-holds-on-the-repository-matrix-einstein-tensor-via-the-linear-divergence-of-bianchi-implies-conservation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor"

zil_file_contract physlib.cosmologicalConstantConstancy where
  promises "The constancy of the cosmological constant from the contracted Bianchi identity, closing the remaining differential link of Jacobson's thermodynamic derivation of the Einstein equation. Applying the linear covariant divergence to the Einstein field equation with cosmological term, with the contracted Bianchi identity that the divergence of the Einstein tensor is zero, local conservation that the divergence of the stress tensor is zero, and the metric-compatible Leibniz identity that the divergence of the cosmological term Lambda times the metric equals the gradient of Lambda, forces the gradient of the cosmological scalar to vanish, so the cosmological constant is locally constant. This holds abstractly for any linear divergence and instantiates on the repository matrix Einstein tensor, reusing the einsteinTensor and the abstract linear divergence style of bianchi implies conservation. Honest scope: the covariant divergence, the metric-compatible Leibniz identity, and the contracted Bianchi identity are the standard differential-geometry inputs, not rebuilt here; the vanishing gradient is the local statement of constancy, with promotion to a global constant on a connected spacetime the standard zero-gradient-implies-constant fact."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor"
  ]
  forbids_substitutes [
    "reading the abstract-divergence Bianchi argument as a construction of the covariant-derivative differential geometry or as the global promotion of vanishing gradient to a spacetime constant"
  ]
  witnessed_by [
    cosmologicalConstant_gradient_zero,
    cosmologicalConstant_gradient_zero_matrix
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.cosmologicalConstantConstancy
