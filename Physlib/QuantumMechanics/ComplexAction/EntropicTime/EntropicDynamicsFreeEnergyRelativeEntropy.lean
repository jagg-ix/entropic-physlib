/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow

/-!
# The free energy is the relative entropy above the Gibbs minimum (Jordan–Kinderlehrer–Otto Lyapunov functional)

Completes the variational (gradient-flow) picture of the Fokker–Planck equation
(`EntropicDynamicsWassersteinGradientFlow`) with its **Lyapunov functional / H-theorem** content
(Jordan–Kinderlehrer–Otto): the free energy `F(ρ) = ∫ Ψρ + β⁻¹ρ log ρ`, measured above its Gibbs minimum
`F(ρ_s)` (at `ρ_s = Z⁻¹e^{−βΨ}`), is `β⁻¹` times the **relative entropy** (Kullback–Leibler divergence)

`F(ρ) − F(ρ_s) = β⁻¹ ∫ ρ log(ρ/ρ_s) = β⁻¹ D_{KL}(ρ ‖ ρ_s) ≥ 0`,

so the Gibbs distribution **minimizes** `F` and the relative entropy is the Lyapunov functional that decreases along
the gradient flow (the H-theorem). The pointwise seed of the inequality is the Gibbs inequality
`ρ log(ρ/ρ_s) ≥ ρ − ρ_s`, which integrates (`∫ρ = ∫ρ_s`) to `D_{KL} ≥ 0`.

* the **free energy is the relative entropy** `β F(ρ) = ρ log(ρ/ρ_s) − ρ log Z`
 (`freeEnergyDensity_eq_relativeEntropy`) — the free-energy density equals the KL-divergence density
 `ρ log(ρ/ρ_s)` plus a `Z`-constant, with `ρ_s = Z⁻¹e^{−βΨ}` the Gibbs distribution;
* the **pointwise Gibbs inequality** `ρ − ρ_s ≤ ρ log(ρ/ρ_s)` (`relativeEntropy_density_ge`) — the KL-divergence
 density is bounded below by the mass difference (`Real.log_le_sub_one_of_pos`), integrating to `D_{KL} ≥ 0`;
* the **free energy is minimized at Gibbs** `ρ − ρ_s ≤ β F(ρ) + ρ log Z` (`freeEnergy_ge_gibbs`) — combining the
 two, the free-energy density is bounded below by the Gibbs reference, whose integral gives `F(ρ) ≥ F(ρ_s)`: the
 variational principle and the Lyapunov (H-theorem) property of the free energy.

So the free energy of the entropic-dynamics / Fokker–Planck flow is the relative entropy above the Gibbs minimum: a
non-negative Lyapunov functional, minimized by the Gibbs equilibrium, decreasing along the Wasserstein gradient flow
— the H-theorem of the variational Fokker–Planck equation.

* **§A — the free energy is the relative entropy** (`freeEnergyDensity_eq_relativeEntropy`).
* **§B — the pointwise Gibbs inequality** (`relativeEntropy_density_ge`).
* **§C — the free energy is minimized at Gibbs** (`freeEnergy_ge_gibbs`).

The relative-entropy identity, the pointwise Gibbs inequality, and the free-energy lower bound
are exact `Real.log` algebra, reusing `freeEnergyDensity` and `Real.log_le_sub_one_of_pos`. The integral relative
entropy `D_{KL} ≥ 0`, the monotone decrease `dF/dt ≤ 0` along the flow, and the JKO convergence are the referenced
content; here the pointwise (density-level) core is proved. No new axioms.

## References

* R. Jordan, D. Kinderlehrer, F. Otto, SIAM J. Math. Anal. 29 (1998) 1 (Eqs. 4–7; free energy Lyapunov functional).
 Repo structure: `EntropicTime.EntropicDynamicsWassersteinGradientFlow` (`freeEnergyDensity`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy

/-! ## §A — the free energy is the relative entropy -/

/-- **[The free energy is the relative entropy above the Gibbs minimum] `β F(ρ) = ρ log(ρ/ρ_s) − ρ log Z`.** With
the Gibbs distribution `ρ_s = Z⁻¹e^{−βΨ}` (Jordan–Kinderlehrer–Otto Eq. 4), the free-energy density equals the
Kullback–Leibler divergence density `ρ log(ρ/ρ_s)` plus the `Z`-constant `−ρ log Z`: the free energy is the relative
entropy `β⁻¹ D_{KL}(ρ‖ρ_s)` above its minimum. -/
theorem freeEnergyDensity_eq_relativeEntropy (Ψ β Z ρ : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) (hρ : 0 < ρ) :
    β * freeEnergyDensity Ψ β ρ = ρ * Real.log (ρ / (Real.exp (-(β * Ψ)) / Z)) - ρ * Real.log Z := by
  unfold freeEnergyDensity
  rw [Real.log_div (ne_of_gt hρ) (div_ne_zero (Real.exp_ne_zero _) (ne_of_gt hZ)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
  field_simp
  ring

/-! ## §B — the pointwise Gibbs inequality -/

/-- **[The pointwise Gibbs inequality] `ρ − ρ_s ≤ ρ log(ρ/ρ_s)`.** The Kullback–Leibler-divergence density is
bounded below by the mass difference, from `log(ρ_s/ρ) ≤ ρ_s/ρ − 1` (`Real.log_le_sub_one_of_pos`); integrating over
normalized densities (`∫ρ = ∫ρ_s`) gives the non-negativity of the relative entropy `D_{KL}(ρ‖ρ_s) ≥ 0`. -/
theorem relativeEntropy_density_ge (ρ ρs : ℝ) (hρ : 0 < ρ) (hρs : 0 < ρs) :
    ρ - ρs ≤ ρ * Real.log (ρ / ρs) := by
  have hlog : Real.log (ρ / ρs) = -Real.log (ρs / ρ) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  have h := Real.log_le_sub_one_of_pos (div_pos hρs hρ)
  have hd : ρ * (ρs / ρ - 1) = ρs - ρ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hρ.le, hd]

/-! ## §C — the free energy is minimized at Gibbs -/

/-- **[The free energy is minimized at the Gibbs distribution] `ρ − ρ_s ≤ β F(ρ) + ρ log Z`.** Combining the
relative-entropy identity with the Gibbs inequality, the free-energy density is bounded below by the Gibbs reference
`ρ_s = Z⁻¹e^{−βΨ}`; integrating (`∫(ρ − ρ_s) = 0`) gives `F(ρ) ≥ F(ρ_s)` — the Gibbs distribution minimizes the free
energy, which is therefore a non-negative Lyapunov functional (the H-theorem). -/
theorem freeEnergy_ge_gibbs (Ψ β Z ρ : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) (hρ : 0 < ρ) :
    ρ - Real.exp (-(β * Ψ)) / Z ≤ β * freeEnergyDensity Ψ β ρ + ρ * Real.log Z := by
  have hA := freeEnergyDensity_eq_relativeEntropy Ψ β Z ρ hβ hZ hρ
  have hρs : 0 < Real.exp (-(β * Ψ)) / Z := by positivity
  have hB := relativeEntropy_density_ge ρ (Real.exp (-(β * Ψ)) / Z) hρ hρs
  linarith [hA, hB]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy

end
