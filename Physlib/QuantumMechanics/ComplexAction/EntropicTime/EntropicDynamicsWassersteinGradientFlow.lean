/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

/-!
# The Fokker–Planck equation as the Wasserstein gradient flow of the free energy (Jordan–Kinderlehrer–Otto)

Extends the local-time Fokker–Planck equations (`EntropicDynamicsLocalTimeFokkerPlanck`) with the **variational
(gradient-flow) formulation** of Jordan–Kinderlehrer–Otto (*The Variational Formulation of the Fokker–Planck
Equation*, SIAM J. Math. Anal. 29 (1998); Eqs. 2, 4–7): the Fokker–Planck equation
`∂ρ/∂t = div(∇Ψ ρ) + β⁻¹Δρ` is the **steepest descent** of the free energy

`F(ρ) = E(ρ) + β⁻¹ S(ρ)`, `E(ρ) = ∫ Ψ ρ`, `S(ρ) = ∫ ρ log ρ`,

with respect to the Wasserstein metric. The Fokker–Planck velocity is minus the gradient of the first variation
`δF/δρ = Ψ + β⁻¹(log ρ + 1)`, so `v = −∇(δF/δρ) = −∇Ψ − β⁻¹(∇ρ)/ρ`, and `∂ρ/∂t = −div(ρ v) = div(ρ∇(δF/δρ))` — a
gradient flow. This is *exactly* the entropic-dynamics local-time Fokker–Planck current velocity
`∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ` (`currentPotential`) once the drift potential is `φ = −Ψ` and the diffusion coefficient is
`β⁻¹ = ½`: **the entropic-dynamics probability flow is the JKO Wasserstein gradient flow of the free energy**, and
the osmotic velocity `½(∂_χρ)/ρ` is the entropy gradient `β⁻¹∇ log ρ`.

* the **free energy density** `Ψρ + β⁻¹ρ log ρ` (`freeEnergyDensity`, Eqs. 5–7: energy plus `β⁻¹` times the
 negative Gibbs–Boltzmann entropy);
* the **first variation** `δF/δρ = Ψ + β⁻¹(log ρ + 1)` (`freeEnergyVariation`, `freeEnergyDensity_hasDerivAt_rho`) —
 the `ρ`-derivative of the free-energy density;
* the **free-energy gradient** `∇(δF/δρ) = ∇Ψ + β⁻¹(∇ρ)/ρ` (`freeEnergyVariation_hasDerivAt`) — the Fokker–Planck
 velocity is minus this;
* the **entropic dynamics is the JKO gradient flow** (`ltfp_velocity_is_neg_free_energy_gradient`): the local-time
 Fokker–Planck current velocity `∂_χΦ` (with `φ = −Ψ`, `β = 2`) equals `−∇(δF/δρ)` — the ED probability flow is the
 Wasserstein steepest descent of the free energy;
* the **Gibbs state is stationary** (`gibbs_variation_constant`): at the Gibbs distribution `ρ_s = Z⁻¹e^{−βΨ}`
 (Eq. 4) the first variation `δF/δρ = β⁻¹(1 − log Z)` is spatially constant, so its gradient — the Fokker–Planck
 velocity — vanishes: the Gibbs state minimizes `F` and is the equilibrium of the gradient flow.

So the entropic-dynamics local-time Fokker–Planck flow is the JKO steepest descent of the free energy `F = E + β⁻¹S`
in the Wasserstein metric, its diffusion is the entropy gradient, and its equilibrium is the free-energy-minimizing
Gibbs distribution.

* **§A — the free energy** (`freeEnergyDensity`).
* **§B — the first variation** (`freeEnergyVariation`, `freeEnergyDensity_hasDerivAt_rho`).
* **§C — the free-energy gradient** (`freeEnergyVariation_hasDerivAt`).
* **§D — the entropic dynamics is the JKO gradient flow** (`ltfp_velocity_is_neg_free_energy_gradient`).
* **§E — the Gibbs state is stationary** (`gibbs_variation_constant`).

The free-energy density, its first variation and gradient, the gradient-flow identification,
and the Gibbs stationarity are exact one-dimensional calculus, reusing `currentPotential`/`currentPotential_hasDerivAt`
and the `Real.log` derivative. The full JKO minimizing-movement scheme, the Wasserstein metric, and the convergence
proof are the referenced content. No new axioms.

## References

* R. Jordan, D. Kinderlehrer, F. Otto, SIAM J. Math. Anal. 29 (1998) 1 (Eqs. 2, 4–7); S. Ipek, M. Abedi, A.
 Caticha, arXiv:1803.07493. Repo structure: `EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck` (`currentPotential`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow

/-! ## §A — the free energy -/

/-- **The free-energy density** `Ψρ + β⁻¹ρ log ρ` (Jordan–Kinderlehrer–Otto Eqs. 5–7) — the energy density `Ψρ`
plus `β⁻¹` times the negative Gibbs–Boltzmann entropy density `ρ log ρ`. -/
noncomputable def freeEnergyDensity (Ψ β ρ : ℝ) : ℝ := Ψ * ρ + (1 / β) * (ρ * Real.log ρ)

/-! ## §B — the first variation -/

/-- **The first variation of the free energy** `δF/δρ = Ψ + β⁻¹(log ρ + 1)` (Jordan–Kinderlehrer–Otto) — the
`ρ`-derivative of the free-energy density, whose gradient is minus the Fokker–Planck velocity. -/
noncomputable def freeEnergyVariation (Ψ β ρ : ℝ) : ℝ := Ψ + (1 / β) * (Real.log ρ + 1)

/-- **[The first variation is the `ρ`-derivative of the free-energy density] `∂F/∂ρ = δF/δρ`.** -/
theorem freeEnergyDensity_hasDerivAt_rho (Ψ β ρ : ℝ) (hpos : ρ ≠ 0) :
    HasDerivAt (fun r => freeEnergyDensity Ψ β r) (freeEnergyVariation Ψ β ρ) ρ := by
  have h1 : HasDerivAt (fun r => Ψ * r) Ψ ρ := by simpa using (hasDerivAt_id ρ).const_mul Ψ
  have h2 : HasDerivAt (fun r => r * Real.log r) (Real.log ρ + 1) ρ := by
    have h := (hasDerivAt_id ρ).mul (Real.hasDerivAt_log hpos)
    exact h.congr_deriv (by simp [mul_inv_cancel₀ hpos])
  have := h1.add (h2.const_mul (1 / β))
  unfold freeEnergyDensity freeEnergyVariation
  exact this.congr_deriv (by ring)

/-! ## §C — the free-energy gradient -/

/-- **[The gradient of the first variation] `∇(δF/δρ) = ∇Ψ + β⁻¹(∇ρ)/ρ`.** The Fokker–Planck velocity is minus this
gradient: `v = −∇(δF/δρ) = −∇Ψ − β⁻¹(∇ρ)/ρ` — the drift `−∇Ψ` plus the diffusion (entropy-gradient) `−β⁻¹(∇ρ)/ρ`. -/
theorem freeEnergyVariation_hasDerivAt (Ψ ρ : ℝ → ℝ) (β Ψ' ρ' x : ℝ) (hΨ : HasDerivAt Ψ Ψ' x)
    (hρ : HasDerivAt ρ ρ' x) (hpos : ρ x ≠ 0) :
    HasDerivAt (fun y => freeEnergyVariation (Ψ y) β (ρ y)) (Ψ' + (1 / β) * (ρ' / ρ x)) x := by
  have hlog : HasDerivAt (fun y => Real.log (ρ y)) (ρ' / ρ x) x := hρ.log hpos
  unfold freeEnergyVariation
  have := hΨ.add ((hlog.add_const 1).const_mul (1 / β))
  exact this.congr_deriv (by ring)

/-! ## §D — the entropic dynamics is the JKO gradient flow -/

/-- **[The entropic-dynamics probability flow is the JKO Wasserstein gradient flow] `∂_χΦ = −∇(δF/δρ)`.** With drift
potential `φ = −Ψ` and diffusion coefficient `β⁻¹ = ½`, the local-time Fokker–Planck current velocity
`∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ` (`currentPotential`) equals minus the gradient of the free-energy first variation
`−∇(δF/δρ) = −∇Ψ − ½(∂_χρ)/ρ` — the entropic-dynamics probability flow is the steepest descent of the free energy
`F = E + β⁻¹S` in the Wasserstein metric (Jordan–Kinderlehrer–Otto), the osmotic velocity being the entropy
gradient. -/
theorem ltfp_velocity_is_neg_free_energy_gradient (Ψ ρ : ℝ → ℝ) (Ψ' ρ' x : ℝ)
    (hΨ : HasDerivAt Ψ Ψ' x) (hρ : HasDerivAt ρ ρ' x) (hpos : ρ x ≠ 0) :
    HasDerivAt (fun y => currentPotential (-Ψ y) (ρ y)) (-(Ψ' + (1 / 2) * (ρ' / ρ x))) x := by
  have := currentPotential_hasDerivAt (fun y => -Ψ y) ρ (-Ψ') ρ' x hΨ.neg hρ hpos
  convert this using 1
  ring

/-! ## §E — the Gibbs state is stationary -/

/-- **[The Gibbs distribution has spatially constant free-energy variation] `δF/δρ|_{ρ_s} = β⁻¹(1 − log Z)`.** At
the Gibbs distribution `ρ_s = Z⁻¹e^{−βΨ}` (Jordan–Kinderlehrer–Otto Eq. 4) the first variation is a spatial
constant, independent of `Ψ`, so its gradient — the Fokker–Planck velocity — vanishes: the Gibbs state minimizes
the free energy and is the stationary equilibrium of the gradient flow. -/
theorem gibbs_variation_constant (Ψ β Z : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) :
    freeEnergyVariation Ψ β (Real.exp (-(β * Ψ)) / Z) = (1 / β) * (1 - Real.log Z) := by
  unfold freeEnergyVariation
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow

end
