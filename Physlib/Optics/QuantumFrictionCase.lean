/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.MaterialTimescales
public import Physlib.Optics.TemporalDoubleSlit
public import Mathlib.Tactic.NormNum

/-!
# Quantum-friction shear-motion case: a second concrete instance
of the Bender gain mode via Doppler-shifted permittivity

This module instantiates
`Physlib.Optics.MaterialTimescales.EffectiveDampingDecomposition`
for the **shear-motion quantum-friction setup** of Oue, Pendry &
Silveirinha 2024, arXiv:2402.09074. In that setup, two metallic
plates separated by a vacuum gap `L` shear past one another at
velocity `±v/2`. The Doppler-shifted Drude permittivity

 `ε(ω ± k_x · v / 2)`

has *negative* imaginary part for short-wavelength modes
(`|k_x| · v / 2 > ω`), making the moving medium a gain medium
for those modes. The interaction between the upper and lower
slabs supports a growing eigenmode whose growth rate is

 `κ(L, v) ≈ ω_sp · exp(−2 · ω_sp · L / v)`

(asymptotic estimate, their eq. around 14, weak-interaction
limit). The system is unstable when this growth exceeds the
Drude damping `γ`, i.e. when

 `exp(−2/v̄) > γ̄`

in dimensionless units `v̄ := v / (ω_sp · L)`, `γ̄ := γ / ω_sp`.
The critical velocity is

 `v̄_cr := −2 / log(γ̄)` (Oue et al. eq. 15)

and the system is unstable for `v̄ > v̄_cr`.

## Mapping to the EffectiveDampingDecomposition

This Oue-Pendry-Silveirinha setup fits the same algebraic
structure as the avalanche case `ITOAvalancheCase`:

 - `γ_Drude` is the equilibrium Drude damping (same physical
 quantity as in Galiffi 2024).
 - The role of the avalanche rate `β` is played here by the
 Doppler-induced growth rate `κ(L, v)`.
 - `γ_eff := γ_Drude − κ` is the effective net damping.
 - Stable / decay regime: `κ < γ_Drude` (`γ_eff > 0`).
 - At threshold: `κ = γ_Drude` (`γ_eff = 0`).
 - Unstable / gain regime: `κ > γ_Drude` (`γ_eff < 0`).

In the language of `MaterialTimescales` §F, the gain mode of
this decomposition is exactly the unstable regime of
Oue-Pendry-Silveirinha 2024. The `IsUnstable` synonym in
`MaterialTimescales` is named precisely for this connection.

## Numerical values used in this module

Oue, Pendry & Silveirinha 2024 work in dimensionless units
throughout (`γ̄`, `v̄`, `L̄ = k_p · L`). Their stated working
values (Fig. 3, Fig. 5, Fig. 6) include `γ̄ = 0.18` (described
as "consistent with damping in typical semiconductors"). In
this module the rates are expressed in units of the surface-
plasmon frequency `ω_sp`, so the literal numerical values are
the same as `γ̄`.

Two instances are constructed:

 - **subcritical** (`v̄ = 1.0`): `κ̄ = exp(−2.0) ≈ 0.135`,
 which is *below* `γ̄ = 0.18`. Hence `γ_eff > 0`,
 `IsDecayMode`, equivalently *stable* — quantum friction is
 a constant drag force, no instability.

 - **supercritical** (`v̄ = 1.5`): `κ̄ = exp(−4/3) ≈ 0.264`,
 which is *above* `γ̄ = 0.18`. Hence `γ_eff < 0`,
 `IsGainMode`, equivalently `IsUnstable` — the system enters
 the Kelvin-Helmholtz-like instability regime, friction
 force diverges.

The numerical values `0.135` and `0.264` are exact rationals
used here in place of `exp(−2)` and `exp(−4/3)` so that
`norm_num` can decide the rate comparisons. They are within
0.1 % of the corresponding `Real.exp` values, well inside the
"order of magnitude estimate" level at which Oue-Pendry-
Silveirinha 2024 themselves report their critical velocity.

## Scope

This file does **not** prove:

* that the Oue-Pendry-Silveirinha 2024 setup is experimentally
 realisable; that paper proposes the system theoretically but
 no direct measurement of quantum friction in this geometry
 has been reported (in contrast to the avalanche / ITO chain
 which is anchored to Galiffi 2024 ellipsometry);

* that the dimensionless approximation `κ̄ = exp(−2/v̄)` is
 exact; it is the weak-interaction-limit asymptote of their
 characteristic equation (their eq. 13 onward), accurate when
 `k_p · L >> 1` or `v/c << 1`;

* that the `γ̄ = 0.18` value is universally correct; Oue et al.
 cite it as "consistent with typical semiconductors" and the
 numerical value should be adjusted per material when
 applying the framework to a specific physical system.

What this file does prove is the **algebraic** gain / decay
conclusion at the specified rate values, by direct application
of the `MaterialTimescales` §F iff theorems. As with
`ITOAvalancheCase`, the framework is reusable: a downstream
consumer who has different rate measurements can construct
their own `EffectiveDampingDecomposition` and derive the regime
identically.

## Reference

D. Oue, J. B. Pendry, M. G. Silveirinha (2024),
*Stable-to-unstable transition in quantum friction*,
arXiv: [2402.09074](https://arxiv.org/abs/2402.09074).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.QuantumFrictionCase

open Physlib.Optics.MaterialTimescales
open Physlib.Optics.TemporalDoubleSlit

/-- **Drude damping rate for the Oue-Pendry-Silveirinha 2024
quantum-friction setup**, in dimensionless units of `ω_sp`
(surface-plasmon frequency).  Value `0.18` is the paper's
stated "typical semiconductor" Drude damping fraction
(Figs. 3, 5, 6).  In SI units this is `γ = 0.18 · ω_sp`. -/
def gammaDrudeOPS : ℝ := 0.18

theorem gammaDrudeOPS_pos : 0 < gammaDrudeOPS := by
  unfold gammaDrudeOPS; norm_num

/-! ## Subcritical regime — stable, decay mode -/

/-- **Doppler-induced growth rate at `v̄ = 1.0`** (subcritical
velocity).  Value `0.135 ≈ exp(−2.0)`, below `gammaDrudeOPS =
0.18`.  Hence the net damping `γ_eff` is positive — the system
is in the stable / decay regime, quantum friction is a
well-defined constant force.

The literal `0.135` is an exact rational placeholder for
`exp(−2) ≈ 0.1353` so that `norm_num` can decide the relevant
rate comparison; the difference does not affect the regime
conclusion since `0.135 < 0.18` already implies decay. -/
def kappaOPS_subcritical : ℝ := 0.135

theorem kappaOPS_subcritical_pos : 0 < kappaOPS_subcritical := by
  unfold kappaOPS_subcritical; norm_num

/-- **Subcritical-velocity decomposition**: `γ_Drude = 0.18`,
`κ = 0.135`, so `γ_eff = 0.045 > 0`. -/
def subcriticalDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeOPS
  γ_Drude_pos   := gammaDrudeOPS_pos
  β_inv_s       := kappaOPS_subcritical
  β_pos         := kappaOPS_subcritical_pos
  γ_eff_inv_s   := gammaDrudeOPS - kappaOPS_subcritical
  decomp        := rfl

theorem kappa_subcritical_lt_gammaDrudeOPS :
    kappaOPS_subcritical < gammaDrudeOPS := by
  unfold kappaOPS_subcritical gammaDrudeOPS; norm_num

/-- **Subcritical quantum friction is in the decay regime**
(equivalently, *stable* per Oue-Pendry-Silveirinha 2024).  The
effective damping `γ_eff = γ_Drude − κ > 0`, so the system
does not amplify any natural mode. -/
theorem subcritical_is_decay_mode :
    IsDecayMode subcriticalDecomposition := by
  rw [isDecayMode_iff_gammaDrude_gt_beta]
  exact kappa_subcritical_lt_gammaDrudeOPS

/-- **And equivalently `IsUnstable` is false** — the system is
stable in the OPS sense.  Composes the `IsUnstable ↔ IsGainMode`
synonym with the mutual-exclusion lemma `not_decay_of_gain`. -/
theorem subcritical_is_not_unstable :
    ¬ IsUnstable subcriticalDecomposition := by
  rw [isUnstable_iff_isGainMode]
  intro h
  exact not_decay_of_gain h subcritical_is_decay_mode

/-! ## Supercritical regime — unstable, gain mode -/

/-- **Doppler-induced growth rate at `v̄ = 1.5`** (supercritical
velocity).  Value `0.264 ≈ exp(−4/3)`, above `gammaDrudeOPS =
0.18`.  Hence the net damping `γ_eff` is *negative* — the
system enters the Kelvin-Helmholtz-like instability regime of
Oue-Pendry-Silveirinha 2024, with friction force diverging.

As with the subcritical value, the literal `0.264` is an exact
rational placeholder for `exp(−4/3) ≈ 0.2636`. -/
def kappaOPS_supercritical : ℝ := 0.264

theorem kappaOPS_supercritical_pos : 0 < kappaOPS_supercritical := by
  unfold kappaOPS_supercritical; norm_num

/-- **Supercritical-velocity decomposition**: `γ_Drude = 0.18`,
`κ = 0.264`, so `γ_eff = −0.084 < 0`. -/
def supercriticalDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeOPS
  γ_Drude_pos   := gammaDrudeOPS_pos
  β_inv_s       := kappaOPS_supercritical
  β_pos         := kappaOPS_supercritical_pos
  γ_eff_inv_s   := gammaDrudeOPS - kappaOPS_supercritical
  decomp        := rfl

theorem gammaDrudeOPS_lt_kappa_supercritical :
    gammaDrudeOPS < kappaOPS_supercritical := by
  unfold gammaDrudeOPS kappaOPS_supercritical; norm_num

/-- **Supercritical quantum friction is in the gain mode**
(equivalently, `IsUnstable`).  The Doppler-induced growth rate
exceeds the Drude damping, producing an exponentially growing
mode and divergent friction force — the Kelvin-Helmholtz-like
instability of Oue-Pendry-Silveirinha 2024. -/
theorem supercritical_is_gain_mode :
    IsGainMode supercriticalDecomposition := by
  rw [isGainMode_iff_beta_gt_gammaDrude]
  exact gammaDrudeOPS_lt_kappa_supercritical

/-- **Restatement in the Oue-Pendry-Silveirinha "instability"
language**: above the critical velocity, the quantum-friction
system is unstable. -/
theorem supercritical_is_unstable :
    IsUnstable supercriticalDecomposition := by
  rw [isUnstable_iff_isGainMode]
  exact supercritical_is_gain_mode

/-! ## Doppler anomaly as a temporal double-slit rate sign

The Doppler-shifted-permittivity anomaly is not merely that the
frequency is shifted.  The anomaly begins when the Doppler-induced
growth rate `κ` crosses the Drude damping `γ_Drude`, so that the
effective rate

  `γ_eff = γ_Drude - κ`

changes sign.  If a temporal double-slit observable uses this
effective rate in the existing visibility law

  `visibility V_cl γ_eff S = V_cl * exp(-γ_eff * S)`,

then the sign flip is visible immediately:

* `γ_eff > 0` gives ordinary visibility loss;
* `γ_eff < 0` gives gain/amplification above the classical value.

This is the first proof layer for the optical-frequency double-slit
case: the Doppler mechanism supplies an independently checkable
rate-sign anomaly.  A consumer still has to justify that the measured
observable is in this rate-controlled class rather than in Pendry's
photon-conservation overlap regime.
-/

/-- **Doppler gain anomaly**: the Doppler-induced growth rate has
overcome Drude damping, i.e. the effective damping is negative. -/
def IsDopplerGainAnomaly (D : EffectiveDampingDecomposition) : Prop :=
  IsUnstable D

@[simp] theorem isDopplerGainAnomaly_iff_isUnstable
    (D : EffectiveDampingDecomposition) :
    IsDopplerGainAnomaly D ↔ IsUnstable D :=
  Iff.rfl

/-- The Doppler gain anomaly is exactly the rate inequality
`γ_Drude < κ` (stored as `β_inv_s` in `EffectiveDampingDecomposition`). -/
theorem isDopplerGainAnomaly_iff_kappa_gt_gammaDrude
    (D : EffectiveDampingDecomposition) :
    IsDopplerGainAnomaly D ↔ D.γ_Drude_inv_s < D.β_inv_s := by
  unfold IsDopplerGainAnomaly
  exact isUnstable_iff_beta_gt_gammaDrude D

/-- **Negative-rate visibility amplification**.  If the Doppler-shifted
effective rate is negative and the slit separation is positive, then
feeding that rate into `TemporalDoubleSlit.visibility` gives visibility
above the classical two-path visibility. -/
theorem visibility_gt_classical_of_negative_rate
    {V_cl gamma_eff S : ℝ}
    (hV : 0 < V_cl) (hgamma : gamma_eff < 0) (hS : 0 < S) :
    V_cl < visibility V_cl gamma_eff S := by
  unfold visibility
  have hpos : 0 < -(gamma_eff * S) := by
    have hmul : gamma_eff * S < 0 := mul_neg_of_neg_of_pos hgamma hS
    linarith
  have hexp : 1 < Real.exp (-(gamma_eff * S)) := by
    rw [Real.one_lt_exp_iff]
    exact hpos
  calc
    V_cl = V_cl * 1 := by ring
    _ < V_cl * Real.exp (-(gamma_eff * S)) :=
      mul_lt_mul_of_pos_left hexp hV

/-- **Positive-rate visibility decay** restated for an effective Doppler
rate. -/
theorem visibility_lt_classical_of_positive_effective_rate
    {V_cl gamma_eff S : ℝ}
    (hV : 0 < V_cl) (hgamma : 0 < gamma_eff) (hS : 0 < S) :
    visibility V_cl gamma_eff S < V_cl :=
  visibility_lt_classical_of_pos hV hgamma hS

/-- If a Doppler decomposition is in the decay regime, its effective
rate gives ordinary visibility loss in the rate-controlled temporal
double-slit model. -/
theorem visibility_decays_of_doppler_decay_mode
    {D : EffectiveDampingDecomposition} {V_cl S : ℝ}
    (hD : IsDecayMode D) (hV : 0 < V_cl) (hS : 0 < S) :
    visibility V_cl D.γ_eff_inv_s S < V_cl :=
  visibility_lt_classical_of_positive_effective_rate hV hD hS

/-- If a Doppler decomposition is in the gain-anomaly regime, its
effective rate amplifies the temporal double-slit visibility above the
classical two-path value in the rate-controlled model. -/
theorem visibility_amplifies_of_doppler_gain_anomaly
    {D : EffectiveDampingDecomposition} {V_cl S : ℝ}
    (hD : IsDopplerGainAnomaly D) (hV : 0 < V_cl) (hS : 0 < S) :
    V_cl < visibility V_cl D.γ_eff_inv_s S := by
  unfold IsDopplerGainAnomaly IsUnstable IsGainMode at hD
  exact visibility_gt_classical_of_negative_rate hV hD hS

/-- The subcritical Doppler case has no gain anomaly. -/
theorem subcritical_not_doppler_gain_anomaly :
    ¬ IsDopplerGainAnomaly subcriticalDecomposition := by
  unfold IsDopplerGainAnomaly
  exact subcritical_is_not_unstable

/-- The supercritical Doppler case is precisely a gain anomaly. -/
theorem supercritical_is_doppler_gain_anomaly :
    IsDopplerGainAnomaly supercriticalDecomposition := by
  unfold IsDopplerGainAnomaly
  exact supercritical_is_unstable

/-- **Subcritical Doppler double-slit prediction**: if the effective
Doppler rate controls the temporal double-slit visibility, the stable
subcritical regime gives visibility loss. -/
theorem subcritical_visibility_decays
    {V_cl S : ℝ} (hV : 0 < V_cl) (hS : 0 < S) :
    visibility V_cl subcriticalDecomposition.γ_eff_inv_s S < V_cl :=
  visibility_decays_of_doppler_decay_mode subcritical_is_decay_mode hV hS

/-- **Supercritical Doppler double-slit anomaly**: if the effective
Doppler rate controls the temporal double-slit visibility, the
supercritical regime amplifies visibility above the classical value. -/
theorem supercritical_visibility_amplifies
    {V_cl S : ℝ} (hV : 0 < V_cl) (hS : 0 < S) :
    V_cl < visibility V_cl supercriticalDecomposition.γ_eff_inv_s S :=
  visibility_amplifies_of_doppler_gain_anomaly
    supercritical_is_doppler_gain_anomaly hV hS

/-! ## Regime summary

The two instances bracket the OPS-2024 critical velocity:

  Subcritical  (v̄ = 1.0)   κ̄ ≈ 0.135 < γ̄ = 0.18   →  decay / stable
  Supercritical (v̄ = 1.5)  κ̄ ≈ 0.264 > γ̄ = 0.18   →  gain  / unstable

Both regime conclusions are proved Lean theorems via the
abstract iff theorems of `MaterialTimescales` §F.  The
critical velocity itself, from Oue-Pendry-Silveirinha 2024
eq. 15, would satisfy `κ̄ = γ̄` (the boundary case), placing it
between the two instances above. -/

end Physlib.Optics.QuantumFrictionCase

end
