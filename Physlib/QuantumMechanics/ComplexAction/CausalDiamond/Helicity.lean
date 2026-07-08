/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum

/-!
# Deriving Appendices A and B from the helicity / Bogoliubov arc

The conformal-Killing structure of a de Sitter causal diamond (Jacobson–Visser Appendices A, B) is
built from `cosh`, `sinh`, `tanh` of the **conformal-Killing-horizon rapidity** `η = R_*/L`. This file
shows those hyperbolic functions are exactly the **Bogoliubov / helicity** dispersion of
`EntropicTime.HelicityEntropicComplexMomentum`, via one recognition:

> the diamond rapidity `η` defines a Bogoliubov mode with off-diagonal momentum `ξ = sinh η`, gap
> `Δ = 1`, and energy `E = cosh η`, because `bogoliubovEnergy(sinh η, 1) = √(sinh²η + 1) = cosh η`
> is precisely the hyperbolic identity `cosh² = sinh² + 1` (`diamond_horizon_energy`).

So the **helicity momentum** `|p| = sinh(R_*/L)`, the **Bogoliubov energy** `E = cosh(R_*/L)`, and the
**velocity** `ξ/E = tanh(R_*/L) = R/L` (the area-radius ratio, Eq. 2.3). Everything in Appendices A, B
then reuses the arc:

* **App A** — the conformal Killing coefficient `A(u) = cosh(R_*/L) − cosh(u/L)` is a **difference of
  Bogoliubov energies** (`confKillingCoeff_eq_bogoliubov`);
* **App B** — the conformal factor `C⁻¹` and the mean curvature `K` are built from the Bogoliubov
  energy `cosh(R_*/L) = E` and momentum `sinh(R_*/L) = ξ = |p|`
  (`confTimeCInv_eq_bogoliubov`); the relativistic factor `√(1−(R/L)²)` is the **Bogoliubov mass ratio**
  `Δ/E = sech(R_*/L)` (`sqrtFactor_diamond`);
* **the de Sitter static patch** `R = L` (`tanh(R_*/L) = 1`) is exactly the **luminal / reversible
  helicity** `|p|/E = 1`, `τ_ent = 0` (`diamond_entropicTime_zero_iff_luminal`) — unifying the
  `k = 0` static patch (`adsExtrinsicK_staticPatch`), the massless Dirac mode, and the reversible
  (zero entropic-time) helicity.

The single key recognition `|p| = ξ = sinh(R_*/L)` makes this a genuine identification of variables,
not an analogy: the same momentum scale feeds the diamond geometry (App A, B) and the entropic-time /
complex-momentum machinery.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, App. A, B. This development:
  `CausalDiamond.ConformalIsometry`, `EntropicTime.HelicityEntropicComplexMomentum`, `CausalDiamond.AdS`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdS
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime

/-! ## §A — the diamond rapidity is a Bogoliubov mode (`E = cosh η`, `ξ = sinh η`, `Δ = 1`) -/

/-- **The conformal-Killing-horizon energy is the Bogoliubov energy** `cosh η = bogoliubovEnergy(sinh η,
1) = √(sinh²η + 1)` — the diamond rapidity `η = R_*/L` is the Bogoliubov mode `(ξ = sinh η, Δ = 1,
E = cosh η)`, the dispersion being the hyperbolic identity `cosh² = sinh² + 1`. -/
theorem diamond_horizon_energy (η : ℝ) : bogoliubovEnergy (Real.sinh η) 1 = Real.cosh η := by
  rw [bogoliubovEnergy, one_pow, ← Real.cosh_sq]
  exact Real.sqrt_sq (Real.cosh_pos η).le

/-- **The diamond velocity is the Bogoliubov velocity** `R/L = tanh η = ξ/E = |p|/E`. -/
theorem diamond_velocity_eq_bogoliubov (η : ℝ) :
    Real.tanh η = Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 := by
  rw [diamond_horizon_energy]; exact Real.tanh_eq_sinh_div_cosh η

/-! ## §B — Appendix A from the Bogoliubov energy -/

/-- **Appendix A: the conformal Killing coefficient is a difference of Bogoliubov energies**
`A(u) = cosh(R_*/L) − cosh(u/L) = E(R_*) − E(u)` with `E(·) = bogoliubovEnergy(sinh(·/L), 1)`. -/
theorem confKillingCoeff_eq_bogoliubov (L Rstar u : ℝ) :
    confKillingCoeff L Rstar u
      = bogoliubovEnergy (Real.sinh (Rstar / L)) 1 - bogoliubovEnergy (Real.sinh (u / L)) 1 := by
  rw [confKillingCoeff, diamond_horizon_energy, diamond_horizon_energy]

/-! ## §C — Appendix B from the Bogoliubov energy and momentum -/

/-- **Appendix B: the conformal factor `C⁻¹` is built from the Bogoliubov energy** `cosh(R_*/L) = E`
and momentum `sinh(R_*/L) = ξ`. -/
theorem confTimeCInv_eq_bogoliubov (L Rstar s x : ℝ) :
    confTimeCInv L Rstar s x
      = (Real.cosh s + Real.cosh x * bogoliubovEnergy (Real.sinh (Rstar / L)) 1)
        / (L * Real.sinh (Rstar / L)) := by
  rw [confTimeCInv, diamond_horizon_energy]

/-- **Appendix B / AdS bridge: the relativistic factor is the Bogoliubov mass ratio**
`√(1 − (R/L)²) = sech(R_*/L) = Δ/E = 1/cosh(R_*/L)` (with `R = L tanh(R_*/L)`, Eq. 2.3). -/
theorem sqrtFactor_diamond (L Rstar : ℝ) (hL : L ≠ 0) :
    sqrtFactor L (L * Real.tanh (Rstar / L)) = 1 / Real.cosh (Rstar / L) := by
  have hcpos : 0 < Real.cosh (Rstar / L) := Real.cosh_pos _
  have htanh : 1 - Real.tanh (Rstar / L) ^ 2 = 1 / Real.cosh (Rstar / L) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    have hc : Real.cosh (Rstar / L) ^ 2 ≠ 0 := by positivity
    field_simp
    linarith [Real.cosh_sq_sub_sinh_sq (Rstar / L)]
  rw [sqrtFactor]
  have h1 : L * Real.tanh (Rstar / L) / L = Real.tanh (Rstar / L) := by field_simp
  rw [h1, htanh, show (1 : ℝ) / Real.cosh (Rstar / L) ^ 2 = (1 / Real.cosh (Rstar / L)) ^ 2 by
    rw [div_pow, one_pow]]
  exact Real.sqrt_sq (div_pos one_pos hcpos).le

/-- **The relativistic factor is the Bogoliubov mass ratio** `Δ/E = 1/bogoliubovEnergy(sinh(R_*/L), 1)`
(with `Δ = 1`). -/
theorem sqrtFactor_diamond_eq_massRatio (L Rstar : ℝ) (hL : L ≠ 0) :
    sqrtFactor L (L * Real.tanh (Rstar / L)) = 1 / bogoliubovEnergy (Real.sinh (Rstar / L)) 1 := by
  rw [sqrtFactor_diamond L Rstar hL, diamond_horizon_energy]

/-! ## §D — the static patch is the luminal / reversible helicity -/

/-- **The de Sitter static patch is the luminal / reversible helicity**: the diamond's entropic proper
time `τ_ent` (the binary entropy of the Bogoliubov occupation `v² = (1 − tanh(R_*/L))/2`) vanishes iff
`tanh(R_*/L) = ±1`, i.e. iff `R/L = ±1` — the cosmological-horizon / static-patch limit. So the
`k = 0` static patch (`CausalDiamond.AdS.adsExtrinsicK_staticPatch`), the massless Dirac mode, and
the reversible (`τ_ent = 0`) helicity are the same luminal point. -/
theorem diamond_entropicTime_zero_iff_luminal (η : ℝ) :
    bogoliubovEntropicTime (Real.sinh η) 1 = 0 ↔ Real.tanh η = 1 ∨ Real.tanh η = -1 := by
  rw [entropicTime_zero_iff_metric_luminal, diamond_horizon_energy, ← Real.tanh_eq_sinh_div_cosh]

/-- **A momentum realizing the diamond as a helicity sector**: for a 3-momentum `p` whose helicity
momentum is `|p| = sinh(R_*/L)`, the helicity energy is the diamond horizon energy `cosh(R_*/L)`, so the
diamond's conformal-Killing geometry is the helicity sector of `EntropicTime.HelicityEntropicComplexMomentum`. -/
theorem helicity_realizes_diamond (p : Fin 3 → ℝ) (η : ℝ) (hp : helicityMomentum p = Real.sinh η) :
    bogoliubovEnergy (helicityMomentum p) 1 = Real.cosh η := by
  rw [hp, diamond_horizon_energy]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

end
