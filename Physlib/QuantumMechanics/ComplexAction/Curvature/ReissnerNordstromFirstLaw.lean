/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
meta import Zil

/-!
# The first law of Reissner–Nordström black-hole thermodynamics

Taking the outer-horizon radius `r` and charge `Q` as independent variables
(`ReissnerNordstromRadialThermodynamics`), the first law `dM = T dS + Φ dQ` holds as a **genuine
variation** — the partial derivatives of `M(r,Q)` are exactly the thermodynamic coefficients:

* `firstLaw_charge` — `∂M/∂Q = Φ` (the horizon electric potential);
* `firstLaw_radius` — `∂M/∂r = T · ∂S/∂r` (temperature times the entropy variation).

Together these say the exact one-form `dM` equals `T dS + Φ dQ`.  This closes the boundary flagged by the
static Smarr identity (`ReissnerNordstromSmarrFormula`), which gave the integral relation but not the
differential first law as an actual derivative.

Honest scope: geometric units `G = ℏ = c = k_B = 1`; `M, S, T, Φ` are the radius-parametrized functions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics

/-- **The entropy variation** `∂S/∂r = 2π r`. -/
theorem deriv_rnEntropyR (r : ℝ) : deriv rnEntropyR r = 2 * Real.pi * r := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h : HasDerivAt rnEntropyR (Real.pi * (2 * r)) r := hp.const_mul Real.pi
  rw [h.deriv]; ring

/-- **The mass–charge derivative** `∂M/∂Q = Q/r`. -/
theorem deriv_rnMassR_charge (r Q : ℝ) (hr : r ≠ 0) :
    deriv (fun q => rnMassR r q) Q = Q / r := by
  have hp : HasDerivAt (fun q : ℝ => q ^ 2) (2 * Q) Q := by simpa using hasDerivAt_pow 2 Q
  have h : HasDerivAt (fun q => rnMassR r q) (2 * Q / r / 2) Q :=
    ((hp.div_const r).const_add r).div_const 2
  rw [h.deriv]; ring

/-- **The mass–radius derivative** `∂M/∂r = 1/2 − Q²/(2r²)`. -/
theorem deriv_rnMassR_radius (r Q : ℝ) (hr : r ≠ 0) :
    deriv (fun x => rnMassR x Q) r = 1 / 2 - Q ^ 2 / (2 * r ^ 2) := by
  have h : HasDerivAt (fun x => rnMassR x Q) ((1 + (0 * r - Q ^ 2 * 1) / r ^ 2) / 2) r :=
    ((hasDerivAt_id r).add ((hasDerivAt_const r (Q ^ 2)).div (hasDerivAt_id r) hr)).div_const 2
  rw [h.deriv]; ring

/-- **First law, charge sector** `∂M/∂Q = Φ`. -/
@[zil_level physical_theorem]
theorem firstLaw_charge (r Q : ℝ) (hr : r ≠ 0) :
    deriv (fun q => rnMassR r q) Q = rnPotentialR r Q := by
  rw [deriv_rnMassR_charge r Q hr]; rfl

/-- **First law, radius sector** `∂M/∂r = T · ∂S/∂r` — the mass variation with horizon radius is the
temperature times the entropy variation. -/
@[zil_level physical_theorem]
theorem firstLaw_radius (r Q : ℝ) (hr : r ≠ 0) :
    deriv (fun x => rnMassR x Q) r = rnTempR r Q * deriv rnEntropyR r := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [deriv_rnMassR_radius r Q hr, deriv_rnEntropyR r]
  simp only [rnTempR, rnSurfaceGravityR]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw

zil attach firstLaw_charge where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw.deriv_rnMassR_charge",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-first-law-of-reissner-nordstrom-thermodynamics-charge-sector-the-partial-derivative-of-the-mass-with-respect-to-charge-equals-the-horizon-electric-potential"

zil attach firstLaw_radius where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw.deriv_rnEntropyR",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromFirstLaw.deriv_rnMassR_radius",
  formalizes @ "claim:the-first-law-of-reissner-nordstrom-thermodynamics-radius-sector-the-partial-derivative-of-the-mass-with-respect-to-horizon-radius-equals-the-temperature-times-the-entropy-variation-as-a-genuine-derivative"

zil_file_contract physlib.reissnerNordstromFirstLaw where
  promises "The first law of Reissner-Nordstrom black-hole thermodynamics as a genuine variation, taking the outer-horizon radius and charge as independent variables in geometric units. The partial derivative of the mass with respect to charge at fixed radius equals the horizon electric potential, and the partial derivative of the mass with respect to radius at fixed charge equals the temperature times the entropy variation, computed as an actual derivative via the calculus of the radius-parametrized functions. Together these state that the exact one-form dM equals T dS plus Phi dQ. This closes the boundary flagged by the static Smarr identity, which gave the integral relation but not the differential first law as an actual derivative. Honest scope: geometric units with the constants set to one; the mass, entropy, temperature, and potential are the radius-parametrized functions."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics.rnMassR",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics.rnTempR",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromRadialThermodynamics.rnEntropyR"
  ]
  forbids_substitutes [
    "reading the differential first law as the static integral Smarr identity rather than an actual partial-derivative computation"
  ]
  witnessed_by [
    firstLaw_charge,
    firstLaw_radius
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromFirstLaw
