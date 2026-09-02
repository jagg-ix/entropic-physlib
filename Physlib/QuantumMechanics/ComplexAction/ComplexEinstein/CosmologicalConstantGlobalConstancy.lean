/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
meta import Zil

/-!
# Global constancy of the cosmological constant

`CosmologicalConstantConstancy` shows that the contracted Bianchi identity together with local
conservation forces the gradient of the cosmological scalar to vanish at each point,
`∇_b Λ = 0` (`cosmologicalConstant_gradient_zero`).  That is the *local* statement of constancy.

This module supplies the remaining promotion from vanishing gradient to a single global constant:
a differentiable scalar field on a normed space whose Fréchet derivative vanishes everywhere is
constant.  Composed with the pointwise Bianchi result (which gives `fderiv ℝ Λ x = 0` at **every**
point `x`), it yields that the cosmological scalar produced by Jacobson's equation of state is one
and the same constant throughout spacetime — closing the last link of the thermodynamic derivation.

* `cosmologicalConstant_globally_constant` — a differentiable cosmological scalar field `Λ` with
  `fderiv ℝ Λ x = 0` for all `x` satisfies `Λ x = Λ y` for all `x, y`: it is globally constant.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy

/-- **Global constancy of the cosmological constant.**  A differentiable cosmological scalar field
`Λ : E → ℝ` whose gradient vanishes at every point — the everywhere-holding contracted-Bianchi
consequence `fderiv ℝ Λ x = 0` supplied pointwise by `cosmologicalConstant_gradient_zero` — takes the
same value at any two points, `Λ x = Λ y`.  The cosmological constant is one global constant
throughout spacetime.  This promotes the local (vanishing-gradient) constancy to the global
statement, completing Jacobson's derivation. -/
@[zil_level physical_theorem]
theorem cosmologicalConstant_globally_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : E → ℝ) (hΛdiff : Differentiable ℝ Λ)
    (hBianchi : ∀ x, fderiv ℝ Λ x = 0) (x y : E) :
    Λ x = Λ y :=
  is_const_of_fderiv_eq_zero hΛdiff hBianchi x y

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy

zil attach cosmologicalConstant_globally_constant where
  formalizes @ "claim:a-differentiable-cosmological-scalar-field-whose-gradient-vanishes-at-every-point-the-everywhere-holding-contracted-bianchi-consequence-is-globally-constant-taking-the-same-value-at-any-two-points-so-the-cosmological-constant-is-one-global-constant-throughout-spacetime"

zil_file_contract physlib.cosmologicalConstantGlobalConstancy where
  promises "The global constancy of the cosmological constant, promoting the local vanishing-gradient result of the contracted Bianchi identity to a single global constant and closing the last link of Jacobson's thermodynamic derivation of the Einstein equation. A differentiable cosmological scalar field on a normed space whose Frechet derivative vanishes at every point, the everywhere-holding contracted-Bianchi consequence supplied pointwise by the cosmological-constant gradient-zero theorem, takes the same value at any two points, so it is globally constant. The cosmological constant produced by Jacobson's equation of state is therefore one and the same constant throughout spacetime. Honest scope: the everywhere-vanishing gradient is the pointwise Bianchi input; this module supplies only the mean-value promotion from vanishing gradient to global constant on a normed space."
  at_level physical_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes [
    "reading the mean-value promotion as also establishing the pointwise Bianchi vanishing-gradient input, which is the separate contracted-Bianchi content"
  ]
  witnessed_by [
    cosmologicalConstant_globally_constant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.cosmologicalConstantGlobalConstancy
