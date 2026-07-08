/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter

/-!
# Joining the Dirac matter field to the metric common root

`CausalDiamond.DiracMatter` gave the Dirac matter field of the causal diamond its energy
`E_D = √(p² + m²)`. `CausalDiamond.MetricCommonRoot` identified the velocity `v = ξ/E = tanh(R_*/L)` as
the single root of gravity (equivalence principle), information (entropic time), and dissipation
(Nagao–Nielsen complex action). This file **joins them**: the Dirac field is itself a metric-common-root
(Bogoliubov) mode, because

  `E_D = √(p² + m²) = bogoliubovEnergy(|p|, m)`   (`diracEnergy_eq_bogoliubov`),

with off-diagonal `ξ = |p|` (the helicity momentum) and gap `Δ = m`. So the Dirac field includes the
*same* metric-root structure as the diamond:

* **group velocity** `|p|/E_D = tanh η` is a relativistic boost velocity (`dirac_metric_velocity`);
* **Lorentz factor** `E_D = γ m` (`dirac_lorentzFactor` — the inertial/relativistic mass);
* **entropic proper time** `τ_ent = binEntropy((1 − |p|/E_D)/2)` (`dirac_entropicTime`);
* **complex action** — complexifying the Dirac mass `m`, the weight converges iff `Im m > 0`
  (`dirac_complexMass_converges`).

And the **massless Dirac field** (`m = 0`, `E_D = |p|`, group velocity `1`) is the **luminal** point —
`τ_ent = 0` (reversible, `dirac_massless_reversible`): the same luminal point as the de Sitter static
patch (`CausalDiamond.Helicity.diamond_entropicTime_zero_iff_luminal`) and the massless
Stefan–Boltzmann gas. So the Dirac matter field and the diamond geometry meet at one metric common root.

## References

* This development: `CausalDiamond.DiracMatter`, `CausalDiamond.MetricCommonRoot`,
  `EntropicTime.HelicityEntropicComplexMomentum`, `Bogoliubov.DiracEinsteinMass`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMetricRoot

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MetricCommonRoot
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HelicityEntropicComplexMomentum
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-! ## §A — the Dirac energy is the Bogoliubov energy (the join) -/

/-- **The Dirac matter energy is the Bogoliubov energy** `E_D = √(p² + m²) = bogoliubovEnergy(|p|, m)`:
the Dirac field is a metric-common-root (Bogoliubov) mode with off-diagonal `ξ = |p|` (helicity
momentum) and gap `Δ = m`. -/
theorem diracEnergy_eq_bogoliubov (p : Fin 3 → ℝ) (m : ℝ) :
    diracEnergy (p 0) (p 1) (p 2) m = bogoliubovEnergy (helicityMomentum p) m := by
  rw [helicity_bogoliubov_energy, diracEnergy]
  congr 1
  unfold dotR
  ring

/-! ## §B — the Dirac field includes the metric-common-root structure -/

/-- **The Dirac group velocity is a relativistic boost velocity** `|p|/E_D = tanh η` — the
metric-common-root velocity, identical in kind to the diamond's `R/L = tanh(R_*/L)`. -/
theorem dirac_metric_velocity (p : Fin 3 → ℝ) (m : ℝ) (hm : 0 < m) :
    ∃ η : ℝ, helicityMomentum p / diracEnergy (p 0) (p 1) (p 2) m = Real.tanh η := by
  rw [diracEnergy_eq_bogoliubov]
  exact metricVelocity_eq_tanh (helicityMomentum p) m hm

/-- **The Dirac Lorentz factor** `E_D = γ m` — the relativistic (inertial) energy is `γ` times the rest
mass (the equivalence-principle / inertial-mass face). -/
theorem dirac_lorentzFactor (p : Fin 3 → ℝ) (m : ℝ) (hm : 0 < m) :
    ∃ η : ℝ, diracEnergy (p 0) (p 1) (p 2) m = lorentzFactor η * m := by
  rw [diracEnergy_eq_bogoliubov]
  exact einstein_energy_eq_gamma_rest_energy (helicityMomentum p) m hm

/-- **The Dirac field's entropic proper time** `τ_ent = binEntropy((1 − |p|/E_D)/2)` — the information
face, the same `binEntropy` of the metric velocity as the diamond. -/
theorem dirac_entropicTime (p : Fin 3 → ℝ) (m : ℝ) :
    bogoliubovEntropicTime (helicityMomentum p) m
      = Real.binEntropy ((1 - helicityMomentum p / diracEnergy (p 0) (p 1) (p 2) m) / 2) := by
  rw [diracEnergy_eq_bogoliubov]
  exact helicity_entropicTime p m

/-! ## §C — the massless Dirac field is the luminal / static-patch point -/

/-- **The Bogoliubov energy at zero gap is the momentum** `bogoliubovEnergy(ξ, 0) = ξ` (`ξ ≥ 0`). -/
theorem bogoliubovEnergy_zero_gap (ξ : ℝ) (hξ : 0 ≤ ξ) : bogoliubovEnergy ξ 0 = ξ := by
  rw [bogoliubovEnergy, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq hξ]

/-- **The massless Dirac energy is the momentum** `E_D = |p|` — the lightlike dispersion. -/
theorem dirac_massless_eq_helicityMomentum (p : Fin 3 → ℝ) :
    diracEnergy (p 0) (p 1) (p 2) 0 = helicityMomentum p := by
  rw [diracEnergy_eq_bogoliubov]
  exact bogoliubovEnergy_zero_gap (helicityMomentum p) (Real.sqrt_nonneg _)

/-- **The massless Dirac group velocity is luminal** `|p|/E_D = 1` (for `|p| ≠ 0`): the massless Dirac
mode moves at the speed of light — the `45°` light cone. -/
theorem dirac_massless_velocity (p : Fin 3 → ℝ) (hp : helicityMomentum p ≠ 0) :
    helicityMomentum p / diracEnergy (p 0) (p 1) (p 2) 0 = 1 := by
  rw [dirac_massless_eq_helicityMomentum, div_self hp]

/-- **The massless Dirac field is reversible** `τ_ent = 0`: the luminal Dirac mode (`m = 0`) has zero
entropic proper time — the same reversible / luminal point as the de Sitter static patch
(`CausalDiamond.Helicity.diamond_entropicTime_zero_iff_luminal`) and the massless
Stefan–Boltzmann gas. -/
theorem dirac_massless_reversible (p : Fin 3 → ℝ) (hp : helicityMomentum p ≠ 0) :
    bogoliubovEntropicTime (helicityMomentum p) 0 = 0 := by
  rw [entropicTime_zero_iff_metric_luminal]
  left
  rw [bogoliubovEnergy_zero_gap (helicityMomentum p) (Real.sqrt_nonneg _), div_self hp]

/-! ## §D — the Nagao–Nielsen complex Dirac mass -/

/-- **The complexified Dirac mass gives a convergent complex action iff `Im m > 0`** — complexifying
the Dirac mass `m` to the Nagao–Nielsen complex mass, the momentum Gaussian / complex-action weight
`e^{−S_I/ℏ}` converges exactly when `Im m > 0` (the dissipative face). -/
theorem dirac_complexMass_converges (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  diamond_complexAction_converges m hℏ hdt hm

/-! ## §E — the grand join: the Dirac field meets the diamond at the metric common root -/

/-- **The Dirac matter field and the diamond geometry meet at one metric common root.** For a Dirac
mode `(p, m)` with `m > 0` and complex mass `mc ≠ 0`:

* `E_D = √(p² + m²) = bogoliubovEnergy(|p|, m)` (the Dirac field is a Bogoliubov / metric-root mode);
* **(gravity)** group velocity `|p|/E_D = tanh η`, Lorentz factor `E_D = γ m`;
* **(information)** entropic proper time `τ_ent = binEntropy((1 − |p|/E_D)/2)`;
* **(dissipation)** the complex Dirac mass converges iff `Im mc > 0`.

So the Dirac matter field formalized for the first law includes the *same* metric common root
`v = |p|/E_D` that governs the diamond geometry — gravity, information, and dissipation in one. -/
theorem dirac_metricRoot_join (p : Fin 3 → ℝ) (m : ℝ) (hm : 0 < m) (mc : ℂ)
    {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hmc : mc ≠ 0) :
    diracEnergy (p 0) (p 1) (p 2) m = bogoliubovEnergy (helicityMomentum p) m
      ∧ (∃ η : ℝ, helicityMomentum p / diracEnergy (p 0) (p 1) (p 2) m = Real.tanh η)
      ∧ (∃ η : ℝ, diracEnergy (p 0) (p 1) (p 2) m = lorentzFactor η * m)
      ∧ bogoliubovEntropicTime (helicityMomentum p) m
          = Real.binEntropy ((1 - helicityMomentum p / diracEnergy (p 0) (p 1) (p 2) m) / 2)
      ∧ (0 < (momentumGaussianCoeff mc ℏ dt).re ↔ 0 < mc.im) :=
  ⟨diracEnergy_eq_bogoliubov p m, dirac_metric_velocity p m hm, dirac_lorentzFactor p m hm,
   dirac_entropicTime p m, dirac_complexMass_converges mc hℏ hdt hmc⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMetricRoot

end
