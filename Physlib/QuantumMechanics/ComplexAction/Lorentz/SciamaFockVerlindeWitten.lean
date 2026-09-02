/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir

/-!
# The thermal Fock oscillator between Verlinde's entropy and Witten's central charge

The thermal Fock oscillator of this arc has two faces that this module ties down — the **entropic** (Verlinde)
and the **topological** (Witten):

## Verlinde — equipartition as the high-temperature oscillator

Verlinde's equipartition `E = ½ N k_B T` (`Thermodynamics.VerlindeEquipartitionDerivation`,
`equipartitionEnergy`) is *derived* as the high-temperature limit of `N` quadratic degrees of freedom — the
thermal Fock oscillators here.  The full quantum energy per oscillator is the **Callen–Welton** form

`thermalOscillatorMeanEnergy β E = E·(½ + n̄) = (E/2)·(e^{βE}+1)/(e^{βE}−1) = (E/2)·coth(βE/2)`,

(`thermalOscillatorMeanEnergy_callenWelton`, from `SciamaFluctuationDissipation.fluctuationDissipation`), which
interpolates the zero-point `E/2` (`βE → ∞`, low `T`) and the classical equipartition `k_B T`
(`βE → 0`, high `T`) — so the thermal Fock oscillator *is* Verlinde's screen bit, and its first law
`S = βU + ln Z` (`SciamaFockThermodynamics`) is the thermodynamics behind the entropic force `F = T ∇S`
(`Thermodynamics.VerlindeEntropicForce`).

## Witten — the `c/24` Casimir from `ζ(−1)`

The Virasoro / Chern–Simons ground-state (Casimir) energy on the cylinder is `−c/24`, and Witten's framing
anomaly rotates the Chern–Simons / Jones invariant by the phase `e^{2πi·c/24}`
(`ChernSimons.WittenJonesPolynomialChernSimons`; `WittenAnalyticContinuationChernSimons` for the
Lefschetz-thimble analytic continuation of that partition function).  This `c/24` is exactly the
ζ-regularized zero-point of `c` modes:

`virasoroCasimir_from_zeta` — `c·½·ζ(−1) = −c/24`,

the same `ζ(−1) = −1/12` (`SciamaFockZetaCasimir.riemannZeta_neg_one`) that fixes the string critical dimension.
Witten's steepest-descent contour for the Chern–Simons integral is the convergence cone `cos 2θ > 0`
(`ComplexDelta.Contour`, `SciamaFockNagaoNielsenZeta`) on which the ζ-continuation of the mode tower is honest.

So Verlinde's temperature/entropy and Witten's central-charge/framing are the thermal and topological faces of
one ζ-regularized oscillator: `coth(βE/2)` carries the temperature, `ζ(−1) = −1/12` carries the anomaly.

Honest scope: the Callen–Welton oscillator energy and the `−c/24` Casimir arithmetic from the proved `ζ(−1)`.
The equipartition high-`T` limit, the entropic-force derivation, and the Chern–Simons thimble sum are
contextualized (they live in the referenced modules), not re-derived here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockVerlindeWitten

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockZetaCasimir

/-- **The quantum thermal oscillator energy** `E·(½ + n̄)` (zero-point plus thermal occupation). -/
def thermalOscillatorMeanEnergy (β E : ℝ) : ℝ := E * (1 / 2 + boseEinstein β E)

/-- **[Callen–Welton / Verlinde equipartition] `E·(½+n̄) = (E/2)·coth(βE/2)`.**  The quantum thermal oscillator
energy interpolates the zero-point `E/2` (low `T`) and the classical equipartition `k_B T` (high `T`); the
high-`T` limit is Verlinde's `equipartitionEnergy`. -/
theorem thermalOscillatorMeanEnergy_callenWelton (β E : ℝ) (h : Real.exp (β * E) ≠ 1) :
    thermalOscillatorMeanEnergy β E
      = E / 2 * ((Real.exp (β * E) + 1) / (Real.exp (β * E) - 1)) := by
  rw [thermalOscillatorMeanEnergy,
    show E * (1 / 2 + boseEinstein β E) = E / 2 * (1 + 2 * boseEinstein β E) from by ring,
    fluctuationDissipation β E h]

/-- **[Witten framing / Virasoro Casimir] `c·½·ζ(−1) = −c/24`.**  The Chern–Simons / Virasoro ground-state
Casimir energy `−c/24` (and the framing-anomaly phase `e^{2πi c/24}`) is the ζ-regularized zero-point of `c`
modes, governed by `ζ(−1) = −1/12`. -/
theorem virasoroCasimir_from_zeta (c : ℝ) :
    c * (1 / 2 * (riemannZeta (-1)).re) = -c / 24 := by
  rw [riemannZeta_neg_one_re]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockVerlindeWitten

end
