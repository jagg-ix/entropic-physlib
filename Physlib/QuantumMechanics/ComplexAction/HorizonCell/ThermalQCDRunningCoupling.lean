/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
meta import Zil

/-!
# Temperature dependence of the QCD coupling: vacuum asymptotic freedom vs high-`T` strong coupling

Formalizes van Eijck–Stephens–van Weert (*Temperature Dependence of the QCD Coupling*, hep-ph/9308227): a
one-loop gauge-invariant finite-temperature QCD β-function, and the running coupling `α_s(κ, τ)` as a function of
momentum scale `κ` and temperature `τ`. This extends `QCDBetaFunctionAsymptoticFreedom` (the vacuum, `T = 0`,
asymptotically-free running) into the thermal regime.

The finite-temperature running coupling (their Eq. 22) is
`α_s(κ, τ) = [(11/6 N_c − 1/3 N_f) ln(κ/Λ) − f(κ/2τ)]⁻¹`, with the **same vacuum coefficient**
`11/6 N_c − 1/3 N_f` as the ordinary one-loop β-function and a thermal function `f` that vanishes as `T → 0`.

Two regimes, both tied to the vacuum module:

* the **`T → 0` limit recovers the vacuum coupling** (`alphaFT_zero_temp`): with `f = 0` the thermal coupling
  is the standard one-loop `[coeff · ln(κ/Λ)]⁻¹`, and the coefficient `betaCoeffFT 3 N_f = 2π · betaZeroCoeff N_f`
  is exactly `2π` times the PDG `b₀` (`betaCoeffFT_eq_vacuum`) — same asymptotic-freedom threshold
  `N_f < 11 N_c/2` (`betaCoeffFT_pos_iff`), the paper's condition for asymptotic freedom at zero temperature;
* the **high-`T` limit is strongly coupled** (their Eq. 26): `β^(κ) → −N_c α_s²(21π²/16)(τ/κ)`, which is negative
  (`betaHighTemp_neg`) and grows in magnitude with temperature (`betaHighTemp_antitone_temp`). As the authors note,
  a function of `τ/κ` alone means *raising `T` at fixed `κ` is going into the infrared* — high-`T` QCD is driven
  into the strong-coupling / dimensionally-reduced 3D confining regime, not toward asymptotic freedom.

So the same coupling is asymptotically free in the vacuum / high-momentum limit and strongly coupled at high
temperature — the thermal continuation of the arc's UV/IR complementarity: high `T` is IR is confinement.

* **§A — the vacuum β-coefficient = `2π b₀`** (`betaCoeffFT`, `betaCoeffFT_eq_vacuum`).
* **§B — asymptotic-freedom threshold `N_f < 11 N_c/2`** (`betaCoeffFT_pos_iff`).
* **§C — the finite-`T` running coupling; `T → 0` recovers vacuum** (`alphaFT`, `alphaFT_zero_temp`).
* **§D — high-`T` β is large & negative** (`betaHighTemp`, `betaHighTemp_neg`, `betaHighTemp_antitone_temp`).
* **§E — assembled** (`thermal_qcd_coupling`).

**Honest layering.** The coefficient identity `betaCoeffFT 3 N_f = 2π betaZeroCoeff N_f`, the threshold, the
`T → 0` reduction, and the high-`T` sign/monotonicity are exact algebra. The thermal function `f` and its integral
representation (their Eqs. 8–19), and the full RGE integration, are *recorded* — `alphaFT` carries `f` as an
opaque argument. ## References

* M.A. van Eijck, C.R. Stephens, Ch.G. van Weert, hep-ph/9308227, Eqs. 20–27 (finite-`T` running coupling and
  β-function). Repo carrier: `HorizonCell.QCDBetaFunctionAsymptoticFreedom`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling


/-- **The vacuum one-loop β-coefficient** `11/6 N_c − 1/3 N_f` (hep-ph/9308227 Eqs. 20–23) — the coefficient of
the finite-temperature running coupling, identical to the ordinary vacuum one-loop coefficient. -/
noncomputable def betaCoeffFT (N_c N_f : ℝ) : ℝ := 11 / 6 * N_c - 1 / 3 * N_f

/-- **[The thermal-paper coefficient is `2π` times the PDG `b₀`] `11/6·3 − N_f/3 = 2π·(33−2N_f)/(12π)`.** For
`N_c = 3` the finite-temperature β-coefficient equals `2π · betaZeroCoeff N_f` — the same one-loop content as the
vacuum module, in the paper's `α_s = g²/4π²` normalization. -/
@[zil_level physical_theorem]
lemma betaCoeffFT_eq_vacuum (N_f : ℝ) :
    betaCoeffFT 3 N_f = 2 * Real.pi * betaZeroCoeff N_f := by
  unfold betaCoeffFT betaZeroCoeff
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring


/-- **[Asymptotic freedom at `T = 0` ⟺ `N_f < 11 N_c/2`] `0 < 11/6 N_c − 1/3 N_f ⟺ N_f < 11 N_c/2`.** The
finite-temperature coefficient is positive — the coupling is asymptotically free in the high-momentum / vacuum
limit — exactly when there are few enough fermions, the paper's `N_f < 11/2 N_c` (for `N_c = 3`, `N_f < 33/2`,
matching the vacuum `asymptotic_freedom_iff`). -/
@[zil_level physical_theorem]
lemma betaCoeffFT_pos_iff (N_c N_f : ℝ) : 0 < betaCoeffFT N_c N_f ↔ N_f < 11 * N_c / 2 := by
  unfold betaCoeffFT
  constructor <;> intro h <;> linarith


/-- **The finite-temperature running coupling** `α_s(κ,τ) = [coeff·ln(κ/Λ) − f]⁻¹` (hep-ph/9308227 Eq. 22) —
`coeff = 11/6 N_c − 1/3 N_f`, `f = f(κ/2τ)` the thermal function (carried opaquely). -/
noncomputable def alphaFT (coeff κ Λ fval : ℝ) : ℝ := (coeff * Real.log (κ / Λ) - fval)⁻¹

/-- **[The `T → 0` limit is the vacuum one-loop coupling] `α_s(κ,τ)|_{f=0} = [coeff·ln(κ/Λ)]⁻¹`.** As the
temperature goes to zero the thermal function `f` vanishes, and the finite-temperature coupling reduces to the
standard vacuum one-loop QCD coupling with `Λ = Λ_QCD` — the vacuum running coupling of the asymptotic-freedom
module. -/
@[zil_level physical_theorem]
lemma alphaFT_zero_temp (coeff κ Λ : ℝ) :
    alphaFT coeff κ Λ 0 = (coeff * Real.log (κ / Λ))⁻¹ := by
  unfold alphaFT; rw [sub_zero]


/-- **The high-temperature β-function** `β^(κ) → −N_c α_s²(21π²/16)(τ/κ)` (hep-ph/9308227 Eq. 26), the leading
behaviour as `τ/κ → ∞`. -/
noncomputable def betaHighTemp (N_c αs τ κ : ℝ) : ℝ :=
  -N_c * αs ^ 2 * (21 * Real.pi ^ 2 / 16) * (τ / κ)

/-- **[High-temperature QCD is strongly coupled: `β < 0`].** At high temperature the β-function is negative and
`O(τ/κ)`-large — for positive `N_c`, temperature and momentum, and nonzero coupling. Unlike the vacuum, raising
`T` does not weaken the coupling; the strong-coupling infrared is entered. -/
@[zil_level physical_theorem]
lemma betaHighTemp_neg (N_c αs τ κ : ℝ) (hNc : 0 < N_c) (ha : αs ≠ 0) (hτ : 0 < τ) (hκ : 0 < κ) :
    betaHighTemp N_c αs τ κ < 0 := by
  have hpos : 0 < N_c * αs ^ 2 * (21 * Real.pi ^ 2 / 16) * (τ / κ) := by positivity
  have heq : betaHighTemp N_c αs τ κ = -(N_c * αs ^ 2 * (21 * Real.pi ^ 2 / 16) * (τ / κ)) := by
    unfold betaHighTemp; ring
  rw [heq]; linarith

/-- **[The high-temperature β grows in magnitude with temperature].** For fixed positive momentum scale and
non-negative `N_c`, raising the temperature `τ` makes the (negative) β-function more negative: `β(τ₂) ≤ β(τ₁)`
when `τ₁ ≤ τ₂`. Increasing `T` at fixed `κ` drives the coupling deeper into strong coupling — the paper's "raising
`T` is going into the infrared." -/
@[zil_level physical_theorem]
lemma betaHighTemp_antitone_temp (N_c αs κ : ℝ) (hNc : 0 ≤ N_c) (hκ : 0 < κ)
    {τ1 τ2 : ℝ} (h : τ1 ≤ τ2) : betaHighTemp N_c αs τ2 κ ≤ betaHighTemp N_c αs τ1 κ := by
  have key : betaHighTemp N_c αs τ2 κ - betaHighTemp N_c αs τ1 κ
      = N_c * αs ^ 2 * (21 * Real.pi ^ 2 / 16) / κ * (τ1 - τ2) := by unfold betaHighTemp; ring
  have hfac : N_c * αs ^ 2 * (21 * Real.pi ^ 2 / 16) / κ * (τ1 - τ2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith [key ▸ hfac]


/-- **[The temperature dependence of the QCD coupling, assembled].** For positive `N_c`, temperature `τ`,
momentum `κ` and nonzero coupling:

* the finite-temperature β-coefficient is the vacuum one: `betaCoeffFT 3 N_f = 2π betaZeroCoeff N_f`, positive
  (asymptotically free) iff `N_f < 11 N_c/2`;
* at `T → 0` the coupling reduces to the vacuum one-loop `[coeff·ln(κ/Λ)]⁻¹`;
* at high `T` the β-function `−N_c α_s²(21π²/16)(τ/κ)` is negative and grows with temperature — strong coupling.

The QCD coupling is asymptotically free in the vacuum and strongly coupled at high temperature: the thermal
continuation of the arc's UV/IR complementarity (high `T` = IR = confinement). -/
@[zil_level physical_theorem]
lemma thermal_qcd_coupling (N_c αs τ κ N_f : ℝ) (hNc : 0 < N_c) (ha : αs ≠ 0)
    (hτ : 0 < τ) (hκ : 0 < κ) :
    betaCoeffFT 3 N_f = 2 * Real.pi * betaZeroCoeff N_f
      ∧ (0 < betaCoeffFT N_c N_f ↔ N_f < 11 * N_c / 2)
      ∧ alphaFT (betaCoeffFT N_c N_f) κ 1 0 = (betaCoeffFT N_c N_f * Real.log (κ / 1))⁻¹
      ∧ betaHighTemp N_c αs τ κ < 0 :=
  ⟨betaCoeffFT_eq_vacuum N_f, betaCoeffFT_pos_iff N_c N_f,
    alphaFT_zero_temp (betaCoeffFT N_c N_f) κ 1, betaHighTemp_neg N_c αs τ κ hNc ha hτ hκ⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaCoeffFT_pos_iff where
  formalizes @ "claim:the-finite-temperature-qcd-beta-coefficient-is-positive-asymptotic-freedom-if-and-only-if-the-number-of-flavours-is-below-eleven-half-the-number-of-colours",
  supported_by @ "paper:van-eijck-stephens-van-weert-temperature-dependence-of-the-qcd-coupling-hep-ph-9308227"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp_neg where
  formalizes @ "claim:the-high-temperature-qcd-beta-function-is-negative-driving-the-coupling-into-the-infrared-strong-coupling-dimensionally-reduced-confining-regime",
  supported_by @ "paper:van-eijck-stephens-van-weert-temperature-dependence-of-the-qcd-coupling-hep-ph-9308227"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.thermal_qcd_coupling where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaCoeffFT_pos_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp_neg",
  formalizes @ "claim:the-same-qcd-coupling-is-asymptotically-free-in-the-vacuum-high-momentum-limit-and-strongly-coupled-at-high-temperature-the-thermal-uv-ir-complementarity",
  requires @ "claim:the-finite-temperature-qcd-beta-coefficient-is-positive-asymptotic-freedom-if-and-only-if-the-number-of-flavours-is-below-eleven-half-the-number-of-colours",
  requires @ "claim:the-high-temperature-qcd-beta-function-is-negative-driving-the-coupling-into-the-infrared-strong-coupling-dimensionally-reduced-confining-regime"

zil_file_contract physlib.thermalQcdRunningCoupling where
  promises "The temperature dependence of the QCD coupling (van Eijck-Stephens-van Weert, hep-ph/9308227): a one-loop gauge-invariant finite-temperature beta-function and running coupling alpha_s(kappa, tau) as a function of momentum scale kappa and temperature tau, extending the vacuum asymptotic-freedom running of QCDBetaFunctionAsymptoticFreedom into the thermal regime. The finite-temperature coefficient 11/6 N_c - 1/3 N_f equals the vacuum one and gives the same asymptotic-freedom threshold N_f < 11 N_c/2; the T -> 0 limit recovers the standard one-loop vacuum coupling (betaCoeffFT_eq_vacuum, alphaFT_zero_temp), while the high-T limit beta ~ -N_c alpha_s^2 (21 pi^2/16)(tau/kappa) is negative (betaHighTemp_neg) and grows in magnitude with temperature (betaHighTemp_antitone_temp) -- raising T at fixed kappa goes into the infrared, so high-T QCD is driven into the strong-coupling / dimensionally-reduced 3D confining regime, not toward asymptotic freedom. The thermal function f and the effective-action derivation are recorded from the paper, not re-derived from the path integral."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaCoeffFT",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.betaZeroCoeff"]
  forbids_substitutes ["a temperature-independent coupling, whereas the beta-function acquires an explicit thermal function of tau/kappa",
    "asymptotic freedom at high temperature, whereas high T drives the coupling into the infrared strong-coupling regime"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaCoeffFT_eq_vacuum,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaCoeffFT_pos_iff,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.alphaFT_zero_temp,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp_neg,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.betaHighTemp_antitone_temp,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling.thermal_qcd_coupling]

#zil_formalization_lint physlib.thermalQcdRunningCoupling

/- ZIL-END -/
