/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-!
# The confined photon: effective mass from confinement and the Dirac doublet (Saito 2024)

This file formalizes the dispersion of **S. Saito, *Dirac equation for photons in a fibre:
Origin of polarisation*, Heliyon 10 (2024) e28367**, and links it to the massless-boson
inertial mass (`MassOrigin.BosonicInertialMass`) and the fermionic oscillator (`ComplexOscillator.ComplexFermionicOscillator`).

A photon confined in a graded-index fibre acquires a **massive relativistic dispersion**

  `E = ±√(Δ² + (v₀ p)²)`   (Saito Eq., the `±` Dirac branches; `v₀ = c/n₀` the renormalised speed),

where the gap `Δ = m*·v₀²` is the **confinement-induced effective mass** `m*` times `v₀²`: the
confinement "makes a photon massive." This is the physical realization of a *massless boson
acquiring an inertial mass*, and the `±` branches are the Klein–Gordon → Dirac factorisation
that gives the photon its spin/polarisation — the bosonic → fermionic expansion.

## Main results

* `photonDispersion Δ v₀ p = √(Δ² + (v₀p)²)`; `photonDispersion_sq` (the Klein–Gordon relation
  `E² = Δ² + (v₀p)²`), `photonDispersion_rest` (`E(0) = |Δ|`), `photonDispersion_massless`
  (`Δ = 0 ⟹ E = v₀|p|`, the gapless unconfined photon).
* `photonEffectiveMass Δ v₀ = Δ/v₀²` — the confinement-induced mass; **`= relativisticInertialMass`**
  (`photonEffectiveMass_eq_relativisticInertialMass`), `gap_eq_effectiveMass_velocity_sq`
  (`Δ = m*·v₀²`, the rest energy), `photonEffectiveMass_massless` (`Δ = 0 ⟹ m* = 0`).
* `photonDiracBranch` (the `±` branches); `photonDirac_branches_sum_zero` (`E₊ + E₋ = 0`,
  particle–antiparticle symmetry).
* `photonDirac_rest_eq_fermionic_excited` / `_ground` — **at rest the photon Dirac doublet is
  the fermionic oscillator doublet** `±ℏω/2` (gap `Δ = ℏω/2`): the confined-photon spin doublet
  *is* the fermionic two-level system.

## References

* S. Saito, Heliyon 10 (2024) e28367 (confined-photon Dirac dispersion, effective mass).
* `MassOrigin.BosonicInertialMass`, `ComplexOscillator.ComplexFermionicOscillator` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion

/-! ## §A — the confined-photon relativistic dispersion `E = √(Δ² + (v₀p)²)` -/

/-- **The confined-photon dispersion** (positive branch) `E₊ = √(Δ² + (v₀p)²)` (Saito), with
gap `Δ` and renormalised speed `v₀ = c/n₀`. -/
def photonDispersion (Δ v₀ p : ℝ) : ℝ := Real.sqrt (Δ ^ 2 + (v₀ * p) ^ 2)

/-- The dispersion is non-negative. -/
theorem photonDispersion_nonneg (Δ v₀ p : ℝ) : 0 ≤ photonDispersion Δ v₀ p :=
  Real.sqrt_nonneg _

/-- **The Klein–Gordon relation** `E² = Δ² + (v₀p)²`. -/
theorem photonDispersion_sq (Δ v₀ p : ℝ) :
    photonDispersion Δ v₀ p ^ 2 = Δ ^ 2 + (v₀ * p) ^ 2 := by
  unfold photonDispersion
  rw [Real.sq_sqrt (by positivity)]

/-- **At rest** (`p = 0`) the energy is the gap `E(0) = |Δ|`. -/
theorem photonDispersion_rest (Δ v₀ : ℝ) : photonDispersion Δ v₀ 0 = |Δ| := by
  unfold photonDispersion
  rw [mul_zero, zero_pow (by norm_num), add_zero, Real.sqrt_sq_eq_abs]

/-- **The massless (unconfined) limit** `Δ = 0 ⟹ E = v₀|p|`, the gapless photon. -/
theorem photonDispersion_massless (v₀ p : ℝ) : photonDispersion 0 v₀ p = |v₀ * p| := by
  unfold photonDispersion
  rw [zero_pow (by norm_num), zero_add, Real.sqrt_sq_eq_abs]

/-! ## §B — the confinement-induced effective mass `m* = Δ/v₀²` -/

/-- **The confinement-induced effective mass** `m* = Δ/v₀²` — the photon's inertial mass from
confinement. -/
def photonEffectiveMass (Δ v₀ : ℝ) : ℝ := Δ / v₀ ^ 2

/-- **The photon effective mass is the relativistic inertial mass of its gap energy**:
`m* = Δ/v₀² = relativisticInertialMass Δ v₀` (`E = m·c²` with `c → v₀`). -/
theorem photonEffectiveMass_eq_relativisticInertialMass (Δ v₀ : ℝ) :
    photonEffectiveMass Δ v₀ = relativisticInertialMass Δ v₀ := rfl

/-- **The gap is the rest energy** `Δ = m*·v₀²` (`E_rest = m c²`). -/
theorem gap_eq_effectiveMass_velocity_sq (Δ v₀ : ℝ) (hv : v₀ ≠ 0) :
    Δ = photonEffectiveMass Δ v₀ * v₀ ^ 2 := by
  unfold photonEffectiveMass
  field_simp

/-- **No confinement ⟹ massless** (`Δ = 0 ⟹ m* = 0`): the unconfined photon has no rest mass.
Confinement (`Δ > 0`) gives `m* > 0` — a massless boson acquiring inertial mass. -/
theorem photonEffectiveMass_massless (v₀ : ℝ) : photonEffectiveMass 0 v₀ = 0 := by
  unfold photonEffectiveMass; simp

/-- Confinement gives a positive effective mass (`Δ, v₀ > 0`). -/
theorem photonEffectiveMass_pos (Δ v₀ : ℝ) (hΔ : 0 < Δ) (hv : 0 < v₀) :
    0 < photonEffectiveMass Δ v₀ := by
  unfold photonEffectiveMass; positivity

/-! ## §C — the Dirac `±` branches and the fermionic doublet -/

/-- **The two Dirac branches** `E₊ = +√…`, `E₋ = −√…` (the Klein–Gordon factorisation /
particle–antiparticle pair). -/
def photonDiracBranch (Δ v₀ p : ℝ) (s : Bool) : ℝ :=
  if s then photonDispersion Δ v₀ p else -photonDispersion Δ v₀ p

/-- **Particle–antiparticle symmetry**: `E₊ + E₋ = 0` (the two Dirac branches are negatives),
the relativistic analogue of the SUSY bosonic–fermionic zero-point cancellation. -/
theorem photonDirac_branches_sum_zero (Δ v₀ p : ℝ) :
    photonDiracBranch Δ v₀ p true + photonDiracBranch Δ v₀ p false = 0 := by
  unfold photonDiracBranch; simp

/-- **At rest the photon's upper Dirac branch is the fermionic excited level** `+ℏω/2`
(gap `Δ = ℏω/2`): the confined-photon spin doublet is the fermionic two-level system. -/
theorem photonDirac_rest_eq_fermionic_excited (ℏ ω v₀ : ℝ) (hℏ : 0 ≤ ℏ) (hω : 0 ≤ ω) :
    photonDiracBranch (ℏ * ω / 2) v₀ 0 true = fermionicEnergyReal ℏ ω 1 := by
  unfold photonDiracBranch
  rw [if_pos rfl, photonDispersion_rest, fermionicEnergyReal_excited, abs_of_nonneg (by positivity)]

/-- **At rest the photon's lower Dirac branch is the fermionic ground level** `−ℏω/2`. -/
theorem photonDirac_rest_eq_fermionic_ground (ℏ ω v₀ : ℝ) (hℏ : 0 ≤ ℏ) (hω : 0 ≤ ω) :
    photonDiracBranch (ℏ * ω / 2) v₀ 0 false = fermionicEnergyReal ℏ ω 0 := by
  unfold photonDiracBranch
  rw [if_neg (by simp), photonDispersion_rest, fermionicEnergyReal_ground,
    abs_of_nonneg (by positivity)]

end Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion

end
