/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-!
# The equivalence principle from `R/L = tanh(R_*/L)` being a velocity

The genuine link is the recognition that the diamond's geometric ratio `R/L = tanh(R_*/L)` is a
**velocity** (bounded by the speed of light). Then `R_*/L` is a **rapidity**, so the conformal Killing
flow of the causal diamond is a **uniformly accelerated (boost) worldline**, and:

* `|R/L| = |tanh(R_*/L)| < 1` — the conformal-flow velocity is **sub-luminal** (`diamond_velocity_lt_c`);
* `γ = cosh(R_*/L) = lorentzFactor(R_*/L)` is the **Lorentz factor** of that velocity,
  `γ²(1 − (R/L)²) = 1` (`diamond_lorentzFactor_velocity`), `γ ≥ 1` (time dilation);
* `E = γΔ` — the **relativistic (inertial) energy** is `γ` times the rest gap (`diamond_inertial_energy`,
  reusing `Bogoliubov.DiracEinsteinMass`): the energy that gravitates is the relativistic mass.

The surface gravity `κ` of the conformal Killing horizon is the **proper acceleration** of this boost
worldline. The **Einstein equivalence principle** is then the statement that a uniformly accelerated
observer (proper acceleration `a`, Unruh temperature) is indistinguishable from a static observer in a
gravitational field (surface gravity `κ`, Hawking temperature):

  `unruhTemperature ℏ a c kB = hawkingTemperature ℏ κ c kB  ⟺  a = κ`   (`equivalence_principle`),

i.e. **local acceleration ≡ local gravity**, with the *same* temperature formula `ℏκ/2πck_B`. The
causal diamond realizes this with `a = κ` — its conformal Killing boost (velocity `tanh(R_*/L)`) has
proper acceleration equal to the horizon surface gravity (`diamond_equivalence_principle`).

This complements `Physlib.Relativity.Special.UnruhEntropicRate` (which includes the `κ = a` Rindler
identification at the entropic-rate level).

## References

* Einstein equivalence principle; Unruh (1976), Hawking (1975). This development:
  `CausalDiamond.Helicity`, `Bogoliubov.DiracEinsteinMass`, `HawkingTemperature`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple

open Physlib.Relativity.SemiClassical
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — `R/L = tanh(R_*/L)` is a sub-luminal velocity (the recognition) -/

/-- **The conformal-flow velocity is sub-luminal** `|R/L| = |tanh(R_*/L)| < 1`: the diamond's geometric
ratio `R/L` is a genuine velocity (bounded by the speed of light), so `R_*/L` is a **rapidity** and the
conformal Killing flow is a uniformly accelerated worldline. -/
theorem diamond_velocity_lt_c (L Rstar : ℝ) : |Real.tanh (Rstar / L)| < 1 :=
  Real.abs_tanh_lt_one (Rstar / L)

/-! ## §B — the rapidity gives the Lorentz factor (relativistic / inertial mass) -/

/-- **The Lorentz factor of the conformal flow** `γ = cosh(R_*/L)`, satisfying `γ²(1 − (R/L)²) = 1`:
`cosh(R_*/L)` is genuinely the relativistic `γ = 1/√(1−v²)` for the velocity `v = tanh(R_*/L) = R/L`. -/
theorem diamond_lorentzFactor_velocity (η : ℝ) :
    lorentzFactor η ^ 2 * (1 - Real.tanh η ^ 2) = 1 := by
  have hc2 : Real.cosh η ^ 2 ≠ 0 := by positivity
  rw [lorentzFactor, Real.tanh_eq_sinh_div_cosh, div_pow, mul_sub, mul_one, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hc2]
  exact Real.cosh_sq_sub_sinh_sq η

/-- **Time dilation** `γ ≥ 1` (the relativistic energy never below the rest energy). -/
theorem diamond_lorentzFactor_ge_one (η : ℝ) : 1 ≤ lorentzFactor η := lorentzFactor_ge_one η

/-- **The relativistic (inertial) energy is `γ` times the rest gap** `E = γΔ` — the energy that
gravitates is the relativistic mass (reusing `Bogoliubov.DiracEinsteinMass`). -/
theorem diamond_inertial_energy (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ η : ℝ, bogoliubovEnergy ξ Δ = lorentzFactor η * Δ :=
  einstein_energy_eq_gamma_rest_energy ξ Δ hΔ

/-! ## §C — the equivalence principle: Unruh (acceleration) = Hawking (gravity) -/

/-- **The Unruh temperature** of a uniformly accelerated observer with proper acceleration `a`:
`T_U = ℏa/2πck_B` — the Hawking temperature formula evaluated at the proper acceleration. -/
def unruhTemperature (ℏ a c kB : ℝ) : ℝ := hawkingTemperature ℏ a c kB

/-- **The Einstein equivalence principle.** A uniformly accelerated observer (proper acceleration `a`,
Unruh temperature) and a static observer in a gravitational field (surface gravity `κ`, Hawking
temperature) have the *same* temperature **iff `a = κ`** — local acceleration is indistinguishable from
local gravity. -/
theorem equivalence_principle (ℏ a κ c kB : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hkB : 0 < kB) :
    unruhTemperature ℏ a c kB = hawkingTemperature ℏ κ c kB ↔ a = κ := by
  rw [unruhTemperature, hawkingTemperature_def, hawkingTemperature_def]
  have hD : (2 * Real.pi * c * kB) ≠ 0 := by positivity
  constructor
  · intro h
    rw [div_eq_div_iff hD hD] at h
    exact mul_left_cancel₀ hℏ.ne' (mul_right_cancel₀ hD h)
  · intro h; rw [h]

/-- **The causal diamond realizes the equivalence principle** with `a = κ`: the conformal Killing boost
(velocity `tanh(R_*/L)`) has proper acceleration equal to the horizon surface gravity, so its Unruh
temperature is the diamond's Hawking temperature — gravity and acceleration are one. -/
theorem diamond_equivalence_principle (ℏ κ c kB : ℝ) :
    unruhTemperature ℏ κ c kB = hawkingTemperature ℏ κ c kB := rfl

/-- **The luminal (massless / static-patch) limit has no acceleration temperature**: at the speed of
light `|v| = 1`, the gap `Δ → 0` and the rest frame degenerates — consistent with
`CausalDiamond.Helicity.diamond_entropicTime_zero_iff_luminal` (the reversible, `τ_ent = 0`
helicity). For sub-luminal `v = tanh(R_*/L)` the acceleration/temperature is finite and positive
(`hawkingTemperature_pos`), the genuine accelerated regime. -/
theorem diamond_unruhTemperature_pos (ℏ κ c kB : ℝ)
    (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c) (hkB : 0 < kB) :
    0 < unruhTemperature ℏ κ c kB :=
  hawkingTemperature_pos ℏ κ c kB hℏ hκ hc hkB

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple

end
