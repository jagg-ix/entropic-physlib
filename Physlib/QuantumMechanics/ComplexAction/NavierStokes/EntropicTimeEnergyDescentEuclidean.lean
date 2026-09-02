/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-!
# Navier–Stokes in entropic time, and its Euclidean signature

Describing Navier–Stokes through the velocity field carries the whole nonlinearity (`(u·∇)u`, the enstrophy
`Ω`, the palinstrophy `P`).  Reparametrizing by the **entropic time** `τ = (ν/ℏ)∫Ω` removes it from the energy
law: the velocity-dependent enstrophy that drives both `dE/dt = −νΩ` and `dτ/dt = (ν/ℏ)Ω` **cancels**, and the
kinetic energy descends at the *constant, velocity-free* rate

  `dE/dτ = −ℏ`     (`energyDissipation_per_entropicTime`, `kineticEnergy_hasDerivAt_entropicTime`),

so `E(τ) = E₀ − ℏτ`.  In entropic time the fluid's energy is a straight line of slope `−ℏ`; the velocity has
been integrated out.

## Which signature — Euclidean or Lorentzian?

The entropic time is the **imaginary (Euclidean)** coordinate, not a Lorentzian proper time.  In the CAT/EPT
complex action `S = S_R + iS_I`, the master weight factorises
`e^{(i/ℏ)(S_R + iS_I)} = e^{(i/ℏ)S_R}·e^{−S_I/ℏ}` (`ComplexActionPathIntegralWeight`):

* `S_R` — the *real* geometric proper time — enters as a **unimodular Lorentzian phase**;
* `S_I` — the *imaginary entropic* action — enters as a **real Euclidean damping** `e^{−S_I/ℏ}`.

The modulus of the weight depends **only** on `S_I` (`master_modulus_is_kuiken`): the entropic time controls a
monotone real damping, not a phase.  Viscous Navier–Stokes is dissipative — parabolic (heat/diffusion), the
Wick rotation of the reversible wave/Euler dynamics — so its natural clock is `S_I` and its signature is
**Euclidean**.  The energy descent `E(τ) = E₀ − ℏτ` is precisely the linear exponent of that damping: the
straight-line energy loss *is* the Euclidean-time entropy production.  The Lorentzian (real proper time `S_R`)
face is the reversible `ν = 0` Euler limit, where the damping is absent.

## Honest scope

Algebraic reparametrization identities on the repo's energy/entropic-time rates (`dE/dt = −νΩ` of
`NavierStokes.IntegratedEnergyDissipationFisher`, `τ = (ν/ℏ)∫Ω`) and the complex-action weight modulus.  This
is the correct *description* of dissipative Navier–Stokes as a Euclidean gradient descent in entropic time; it
is not a regularity result.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeEnergyDescentEuclidean

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-! ### The velocity drops out: energy descent in entropic time -/

/-- **The energy dissipation is velocity-free in entropic time: `dE/dτ = −ℏ`.**  The energy rate `dE/dt = −νΩ`
and the entropic-time rate `dτ/dt = (ν/ℏ)Ω` share the velocity-driven enstrophy `Ω`; their ratio cancels both
`Ω` and `ν`, leaving the universal descent rate `−ℏ`.  The whole velocity dependence is absorbed into the
clock. -/
theorem energyDissipation_per_entropicTime (ν ℏ Ω : ℝ) (hν : ν ≠ 0) (hℏ : ℏ ≠ 0) (hΩ : Ω ≠ 0) :
    (-(ν * Ω)) / ((ν / ℏ) * Ω) = -ℏ := by
  field_simp

/-- **The kinetic energy is affine in entropic time, slope `−ℏ`.**  `E(τ) = E₀ − ℏτ`: a straight line, the
velocity integrated out — the derivative in entropic time is the constant `−ℏ`. -/
theorem kineticEnergy_hasDerivAt_entropicTime (E0 ℏ τ : ℝ) :
    HasDerivAt (fun s => E0 - ℏ * s) (-ℏ) τ := by
  simpa using ((hasDerivAt_id τ).const_mul ℏ).const_sub E0

/-! ### The signature is Euclidean: the entropic time is a damping, not a phase -/

/-- **The entropic time enters as a Euclidean damping (real modulus).**  Writing the entropic action
`S_I = ℏτ`, the modulus of the complex-action weight is the Kuiken/entropy-production damping
`‖e^{(i/ℏ)(S_R + iℏτ)}‖ = kuikenWeight ℏ (ℏτ)` (`master_modulus_is_kuiken`): the entropic time controls a real
damping, the hallmark of the **Euclidean** (imaginary-time) sector. -/
theorem entropicTime_euclidean_modulus (S_R ℏ τ : ℝ) :
    ‖complexActionPathIntegralWeight S_R (ℏ * τ) ℏ‖ = kuikenWeight ℏ (ℏ * τ) :=
  master_modulus_is_kuiken S_R (ℏ * τ) ℏ

/-- **The Euclidean damping is `e^{−τ}`.**  With `S_I = ℏτ` the damping is `kuikenWeight ℏ (ℏτ) = e^{−τ}`: a
monotone real decay in the entropic time — the straight-line energy loss `E₀ − ℏτ` read as the exponent of the
Euclidean-time entropy production. -/
theorem entropicTime_damping_eq (ℏ τ : ℝ) (hℏ : ℏ ≠ 0) :
    kuikenWeight ℏ (ℏ * τ) = Real.exp (-τ) := by
  unfold kuikenWeight
  congr 1
  field_simp

/-- **The real proper time is a pure Lorentzian phase.**  The weight's modulus is independent of the real
geometric proper time `S_R`: `‖weight S_R₁ (ℏτ) ℏ‖ = ‖weight S_R₂ (ℏτ) ℏ‖`.  The real action only rotates the
phase (unimodular, Lorentzian); all damping comes from the imaginary entropic action — so the reversible face
is Lorentzian and the dissipative Navier–Stokes face is Euclidean. -/
theorem realProperTime_lorentzian_phase (S_R₁ S_R₂ ℏ τ : ℝ) :
    ‖complexActionPathIntegralWeight S_R₁ (ℏ * τ) ℏ‖
      = ‖complexActionPathIntegralWeight S_R₂ (ℏ * τ) ℏ‖ := by
  rw [master_modulus_is_kuiken, master_modulus_is_kuiken]

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeEnergyDescentEuclidean

end
