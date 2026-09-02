/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
meta import Zil

/-!
# The Kerr–Newman irreducible mass

The irreducible mass of a Kerr–Newman black hole is `M_irr = √(r_+² + a²)/2 = √(𝒜/16π)`, so the horizon
area is `𝒜 = 16π M_irr²`.  Because rotation and charge store extractable energy, the irreducible mass is a
**lower bound** on the total mass — `M_irr ≤ M`, saturated only for Schwarzschild (`a = Q = 0`).

* `knIrreducibleMass` — `M_irr = √(r_+² + a²)/2`.
* `knIrreducibleMass_sq` — `M_irr² = (r_+² + a²)/4`.
* `knHorizonArea_eq_irreducible` — `𝒜 = 16π M_irr²`.
* `knMass_ge_irreducibleMass` — `M_irr ≤ M` (the irreducibility / energy-extraction bound).

Honest scope: the algebraic irreducible-mass bound; the dynamical Penrose/superradiant extraction that
saturates it is not modelled here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities

/-- **The irreducible mass** `M_irr = √(r_+² + a²)/2`. -/
def knIrreducibleMass (M a Q : ℝ) : ℝ := Real.sqrt (knOuterHorizon M a Q ^ 2 + a ^ 2) / 2

/-- **The squared irreducible mass** `M_irr² = (r_+² + a²)/4`. -/
theorem knIrreducibleMass_sq (M a Q : ℝ) :
    knIrreducibleMass M a Q ^ 2 = (knOuterHorizon M a Q ^ 2 + a ^ 2) / 4 := by
  unfold knIrreducibleMass
  rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  ring

/-- **The horizon area in terms of the irreducible mass** `𝒜 = 16π M_irr²`. -/
@[zil_level physical_theorem]
theorem knHorizonArea_eq_irreducible (M a Q : ℝ) :
    knHorizonArea M a Q = 16 * Real.pi * knIrreducibleMass M a Q ^ 2 := by
  simp only [knHorizonArea]
  rw [knIrreducibleMass_sq]; ring

/-- **The irreducibility bound** `M_irr ≤ M`: the irreducible mass is a lower bound on the total mass. -/
@[zil_level physical_theorem]
theorem knMass_ge_irreducibleMass (M a Q : ℝ) (h : a ^ 2 + Q ^ 2 ≤ M ^ 2) (hM : 0 < M) :
    knIrreducibleMass M a Q ≤ M := by
  have hnn : (0 : ℝ) ≤ M ^ 2 - a ^ 2 - Q ^ 2 := by linarith
  have hsq : Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - a ^ 2 - Q ^ 2 := Real.sq_sqrt hnn
  have hsle : Real.sqrt (M ^ 2 - a ^ 2 - Q ^ 2) ≤ M := by
    have hs := Real.sqrt_le_sqrt (show M ^ 2 - a ^ 2 - Q ^ 2 ≤ M ^ 2 from by
      nlinarith [sq_nonneg a, sq_nonneg Q])
    rwa [Real.sqrt_sq hM.le] at hs
  have hSumLe : knOuterHorizon M a Q ^ 2 + a ^ 2 ≤ 4 * M ^ 2 := by
    unfold knOuterHorizon
    nlinarith [hsle, Real.sqrt_nonneg (M ^ 2 - a ^ 2 - Q ^ 2), hsq, hM, sq_nonneg Q]
  have h2M : Real.sqrt (knOuterHorizon M a Q ^ 2 + a ^ 2) ≤ 2 * M := by
    have hle := Real.sqrt_le_sqrt hSumLe
    rwa [show (4 : ℝ) * M ^ 2 = (2 * M) ^ 2 from by ring, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * M)]
      at hle
  unfold knIrreducibleMass
  linarith [h2M]

end Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass

zil attach knHorizonArea_eq_irreducible where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knIrreducibleMass_sq",
  formalizes @ "claim:the-kerr-newman-horizon-area-equals-sixteen-pi-times-the-irreducible-mass-squared-so-the-irreducible-mass-is-the-square-root-of-the-area-over-sixteen-pi"

zil attach knMass_ge_irreducibleMass where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  supported_by @ "lean:HermitianMat.sqrt_nonneg",
  formalizes @ "claim:the-kerr-newman-irreducibility-bound-the-irreducible-mass-is-a-lower-bound-on-the-total-mass-since-rotation-and-charge-store-extractable-energy"

zil_file_contract physlib.kerrNewmanIrreducibleMass where
  promises "The Kerr-Newman irreducible mass. The irreducible mass is the square root of r-plus-squared plus a-squared over two, so its square is r-plus-squared plus a-squared over four and the horizon area equals sixteen pi times the irreducible mass squared, meaning the irreducible mass is the square root of the area over sixteen pi. Because rotation and charge store extractable energy, the irreducible mass is a lower bound on the total mass, saturated only for Schwarzschild. Honest scope: the algebraic irreducible-mass bound; the dynamical Penrose or superradiant extraction that saturates it is not modelled here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities.knHorizonArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knOuterHorizon"
  ]
  forbids_substitutes [
    "reading the algebraic irreducible-mass bound as a dynamical model of the Penrose or superradiant energy-extraction process"
  ]
  witnessed_by [
    knHorizonArea_eq_irreducible,
    knMass_ge_irreducibleMass
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.kerrNewmanIrreducibleMass
