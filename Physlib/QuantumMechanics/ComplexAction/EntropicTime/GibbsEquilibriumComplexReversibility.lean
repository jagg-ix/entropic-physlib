/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The entropic equilibrium is the complex-Einstein reversibility (vanishing of the entropic sector)

Links the free-energy / probability-metric side of the entropic-dynamics arc
(`EntropicDynamicsFreeEnergyRelativeEntropy`, the Wasserstein gradient flow and its Gibbs equilibrium) to the
**complex Einstein field equations** (`ComplexEinstein.ComplexMassEinsteinEquations`). The two sectors share one
structure: an **energy + entropic decomposition** whose entropic part vanishes at equilibrium / reversibility.

The complex mass `m = m_R + i m_I` (`complexMass`) splits into a real energy part `m_R` and an imaginary
**entropic** part `m_I`, giving the complex Einstein energy `E_C = m c²` with real rest energy `Re E_C = m_R c²` and
imaginary **entropic / dissipative energy** `Im E_C = m_I c²`. This mirrors the Jordan–Kinderlehrer–Otto free energy
`F = E + β⁻¹S` (energy plus `β⁻¹` times the entropy). And the two "vanishing entropic sector" conditions coincide:

* **complex-Einstein reversibility** `Im E_C = 0 ⟺ m_I = 0` (`complexEFE_reversible_iff_entropicEnergy_zero`) — the
 imaginary (entropic) Einstein energy vanishes exactly when the mass is reversible, reusing `complexEinsteinEnergy_im`;
* **entropic-dynamics equilibrium** `∂_χ(δF/δρ)|_{ρ_s} = 0` (`gibbs_free_energy_gradient_vanishes`) — at the Gibbs
 distribution `ρ_s = Z⁻¹e^{−βΨ}` the first variation `δF/δρ` is spatially constant (`gibbs_variation_constant`), so
 its gradient — the Fokker–Planck velocity — vanishes: zero dissipation, the reversible equilibrium.

So the entropic-dynamics probability flow reaches equilibrium (zero Fokker–Planck velocity, stationary relative
entropy at the Gibbs state) exactly where the complex Einstein field equations become reversible (`m_I = 0`,
`Im E_C = 0`, real rest energy): both are the vanishing of the entropic sector — the imaginary Einstein energy on
the gravity side, the free-energy dissipation on the probability side, the same reversible / equilibrium limit of
one energy-plus-entropy structure.

* **§A — complex-Einstein reversibility is the vanishing entropic energy** (`complexEFE_reversible_iff_entropicEnergy_zero`).
* **§B — the Gibbs equilibrium has zero Fokker–Planck velocity** (`gibbs_free_energy_gradient_vanishes`).

The reversibility equivalence and the Gibbs-equilibrium stationarity are exact algebra, reusing
`complexEinsteinEnergy_im`, `gibbs_variation_constant`, and `freeEnergyVariation`. The identification is structural
(an energy-plus-entropy decomposition whose entropic part vanishes at reversibility/equilibrium); the dynamical
sourcing of the imaginary Einstein energy by the entropy production is the referenced content. No new axioms.

## References

* R. Jordan, D. Kinderlehrer, F. Otto (free-energy Lyapunov); K. Nagao, H.B. Nielsen (complex mass). Repo dependencies:
 `EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy` (`gibbs_variation_constant`),
 `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy_im`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.GibbsEquilibriumComplexReversibility

/-! ## §A — complex-Einstein reversibility is the vanishing entropic energy -/

/-- **[Complex-Einstein reversibility is the vanishing entropic energy] `Im E_C = 0 ⟺ m_I = 0`.** The imaginary
(entropic / dissipative) part of the complex Einstein energy `Im E_C = m_I c²` vanishes exactly when the mass is
reversible (`m_I = 0`) — the real, non-dissipative Einstein relation. -/
theorem complexEFE_reversible_iff_entropicEnergy_zero (m_R m_I c : ℝ) (hc : c ≠ 0) :
    (complexEinsteinEnergy m_R m_I c).im = 0 ↔ m_I = 0 := by
  rw [complexEinsteinEnergy_im, mul_eq_zero]
  simp [pow_eq_zero_iff, hc]

/-! ## §B — the Gibbs equilibrium has zero Fokker–Planck velocity -/

/-- **[The Gibbs equilibrium has zero Fokker–Planck velocity] `∂_χ(δF/δρ)|_{ρ_s} = 0`.** At the Gibbs distribution
`ρ_s = Z⁻¹e^{−βΨ}` the first variation `δF/δρ` is spatially constant (`gibbs_variation_constant`), so its gradient —
the Fokker–Planck velocity `v = −∇(δF/δρ)` — vanishes: zero dissipation, the reversible entropic equilibrium, the
probability-side counterpart of complex-Einstein reversibility. -/
theorem gibbs_free_energy_gradient_vanishes (Ψ : ℝ → ℝ) (β Z x : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) :
    HasDerivAt (fun y => freeEnergyVariation (Ψ y) β (Real.exp (-(β * Ψ y)) / Z)) 0 x := by
  have hconst : (fun y => freeEnergyVariation (Ψ y) β (Real.exp (-(β * Ψ y)) / Z))
      = fun _ => (1 / β) * (1 - Real.log Z) := by
    funext y
    exact gibbs_variation_constant (Ψ y) β Z hβ hZ
  rw [hconst]
  exact hasDerivAt_const x _

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.GibbsEquilibriumComplexReversibility

end
