/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameKMS

/-!
# Entropic rate in geometric time (Eq 42 chain rule)

Port of equation (42) from
`entropic-time/.../CAT_EPT_Extended_Part2.wl`: the chain-rule
identity

  `dτ_ent / dt_geom = λ / β`

where:

* `λ := dτ_ent/dt` (the QIF entropic rate),
* `β := dt_geom/dt = 1/(k_B·T)` (inverse temperature, used as the
  thermal-time-to-coordinate-time rescaling),
* `dt_geom/dt = β`.

The Wolfram derivation is a pure chain-rule application; the Lean
port states the algebraic identity directly without needing any
derivative machinery, since both rates are scalars in the carrier
formulation.

## Contents

* `entropicRateInGeometricTime λ β` — `λ/β`.
* `entropicRate_chain_rule` — the identity
  `(dτ_ent/dt) / (dt_geom/dt) = (dτ_ent/dt_geom)`, expressed at the
  rate level.
* `entropicRateInGeometricTime_pos` — positivity at positive `λ, β`.
* `entropicRateInGeometricTime_eq_kB_T_times_lam` — substituting
  `β = 1/(k_B·T)` gives `λ/β = λ·k_B·T`; higher temperature gives
  faster entropic evolution.

## Cross-references

* `QuantumInertialFrame.entropicRate` (`λ = ⟨H_I⟩/ℏ`).
* `kmsThermalRate_at_inverse_temperature := 1/(β·ℏ)` (KMS thermal
  rate; relates to this file's `β` via `β·ℏ = 1/λ_KMS`).
* `connesRovelliThermalTime := β·ℏ·t` (the thermal-time
  accumulator; `t_geom` is `β·t` in coordinate time, with `ℏ`
  factored separately).


## References

* Connes-Rovelli 1994 — thermal time hypothesis (Class. Quant.
  Grav. 11, 2899).
* `entropic-time/.../CAT_EPT_Extended_Part2.wl` Eq (42).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget


/-- **Entropic rate in geometric time** (Eq 42):

  `dτ_ent/dt_geom := λ/β`

where `λ = dτ_ent/dt` is the QIF entropic rate and `β = dt_geom/dt`
is the inverse temperature.  Equivalently `λ·k_B·T`: higher
temperature gives faster entropic evolution (since `β = 1/(k_B·T)`,
so `λ/β = λ·k_B·T`). -/
def entropicRateInGeometricTime (lam beta : ℝ) : ℝ := lam / beta

/-- The entropic rate in geometric time is positive at positive `λ`
and `β`. -/
lemma entropicRateInGeometricTime_pos
    {lam beta : ℝ} (h_lam : 0 < lam) (h_beta : 0 < beta) :
    0 < entropicRateInGeometricTime lam beta := by
  unfold entropicRateInGeometricTime
  exact div_pos h_lam h_beta

/-- **Chain rule identity** (Eq 42 content): the geometric-time
entropic rate equals the coordinate-time rate divided by the
inverse temperature.

This is `(dτ_ent/dt) / (dt_geom/dt) = dτ_ent/dt_geom` — algebraic
division of two scalars. -/
lemma entropicRate_chain_rule (lam beta : ℝ) :
    entropicRateInGeometricTime lam beta = lam / beta := rfl


/-- **Substituting `β = 1/(k_B·T)`** gives the temperature-explicit
form:

  `λ/β = λ · k_B · T`.

Physically: at fixed coordinate-time entropic rate `λ`,
*higher temperature* gives *faster* geometric-time entropic
evolution.  This matches the Connes-Rovelli thermal-time
identification: thermal time advances faster at higher
temperature. -/
lemma entropicRateInGeometricTime_eq_kB_T_times_lam
    {lam kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) :
    entropicRateInGeometricTime lam (1 / (kB * T)) = lam * kB * T := by
  unfold entropicRateInGeometricTime
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp

end QuantumMechanics.FiniteTarget

end
