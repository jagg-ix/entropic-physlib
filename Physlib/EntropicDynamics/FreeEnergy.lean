/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Free energy, the Gibbs equilibrium, and the vanishing Fokker–Planck velocity

The Lyapunov / equilibrium layer of the entropic-dynamics probability flow. The Jordan–Kinderlehrer–Otto free
energy `F = E + β⁻¹ S` is a Lyapunov functional for the Fokker–Planck flow (its first variation drives the drift).
At the **Gibbs distribution** `ρ_s = Z⁻¹ e^{−βΨ}` the first variation `δF/δρ` becomes **spatially constant**, so
its gradient — the Fokker–Planck velocity `v = −∇(δF/δρ)` — vanishes: zero dissipation, the reversible
equilibrium (the probability-side counterpart of complex-Einstein reversibility).

References: R. Jordan, D. Kinderlehrer, F. Otto (free-energy Lyapunov). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.EntropicDynamics.FreeEnergy

/-- **The free energy** `F = E + β⁻¹ S` (energy plus `β⁻¹` times entropy) — the Jordan–Kinderlehrer–Otto Lyapunov
functional of the Fokker–Planck flow. -/
noncomputable def freeEnergy (E S β : ℝ) : ℝ := E + β⁻¹ * S

/-- **The first variation of the free energy** `δF/δρ = Ψ + β⁻¹(log ρ + 1)` — the potential whose gradient is the
Fokker–Planck drift velocity. -/
noncomputable def freeEnergyVariation (Ψ β ρ : ℝ) : ℝ := Ψ + β⁻¹ * (Real.log ρ + 1)

/-- **The Gibbs distribution** `ρ_s = Z⁻¹ e^{−βΨ}` — the equilibrium of the entropic-dynamics flow. -/
noncomputable def gibbsDistribution (Ψ β Z : ℝ) : ℝ := Real.exp (-(β * Ψ)) / Z

/-- **At the Gibbs distribution the free-energy variation is constant** `δF/δρ|_{ρ_s} = β⁻¹(1 − log Z)` —
independent of `Ψ`. This spatial constancy is what makes the equilibrium stationary. -/
theorem gibbs_variation_constant (Ψ β Z : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) :
    freeEnergyVariation Ψ β (gibbsDistribution Ψ β Z) = β⁻¹ * (1 - Real.log Z) := by
  unfold freeEnergyVariation gibbsDistribution
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
  field_simp
  ring

/-- **The Gibbs equilibrium has zero Fokker–Planck velocity** `∂_x(δF/δρ)|_{ρ_s} = 0`. Since the first variation is
spatially constant at the Gibbs distribution (`gibbs_variation_constant`), its gradient — the Fokker–Planck
velocity `v = −∇(δF/δρ)` — vanishes: zero dissipation, the reversible entropic equilibrium. -/
theorem gibbs_velocity_vanishes (Ψ : ℝ → ℝ) (β Z x : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) :
    HasDerivAt (fun y => freeEnergyVariation (Ψ y) β (gibbsDistribution (Ψ y) β Z)) 0 x := by
  have h : (fun y => freeEnergyVariation (Ψ y) β (gibbsDistribution (Ψ y) β Z))
      = fun _ => β⁻¹ * (1 - Real.log Z) := by
    funext y
    exact gibbs_variation_constant (Ψ y) β Z hβ hZ
  rw [h]
  exact hasDerivAt_const x _

end Physlib.EntropicDynamics.FreeEnergy

end
