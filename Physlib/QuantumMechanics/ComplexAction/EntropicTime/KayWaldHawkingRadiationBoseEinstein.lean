/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT

meta import Zil

/-!
# Hawking radiation is thermal: the Bose–Einstein spectrum and KMS detailed balance at `T = κ/2π` (Kay–Wald)

Completes the Kay–Wald thermal picture: the KMS state at the Hawking temperature `T = κ/2π` on the bifurcate
Killing horizon (`KayWaldHawkingKMSHorizon`) radiates with a **thermal Bose–Einstein spectrum**, and the KMS
condition is the **detailed balance** between emission and absorption — the Boltzmann factor `e^{−βω}` — which is
the arc's entropic weight.

* the **Hawking occupation number** is Bose–Einstein `n(ω) = 1/(e^{βω} − 1)` at the Hawking inverse temperature
  `β = 2π/κ` (`hawkingOccupation`) — the thermal spectrum of black-hole / Killing-horizon radiation, the same
  `boseEinstein` occupation as the repository's thermofield oscillator;
* the **KMS detailed balance** `n/(n+1) = e^{−βω}` (`hawking_detailed_balance`) — the ratio of stimulated to total
  emission is the Boltzmann factor, the defining thermal (KMS) relation of the Hawking state;
* the **detailed-balance factor is the entropic weight** `e^{−βω} = kuikenWeight (1/β) ω = kuikenWeight T_H ω`
  (`detailed_balance_is_kuiken`) — the Hawking radiation's Boltzmann factor at `T_H = κ/2π` sits on the same
  `kuikenWeight = e^{−·/·}` hub as the quasi-free state, confinement, and the entropic-dynamics transition
  probability.

So the Kay–Wald KMS state on a bifurcate Killing horizon emits a thermal Bose–Einstein spectrum at the Hawking
temperature, its detailed-balance Boltzmann factor is the arc's entropic weight — the Hawking effect, from the
horizon geometry (`U = e^{κv}`) through the KMS periodicity (`2π/κ`) to the thermal radiation spectrum, all on the
`kuikenWeight` hub.

* **§A — the Bose–Einstein occupation** (`hawkingOccupation`).
* **§B — KMS detailed balance = the Boltzmann factor** (`hawking_detailed_balance`).
* **§C — the Boltzmann factor is the entropic weight** (`detailed_balance_is_kuiken`).
* **§D — Bekenstein's greybody spectrum** (`greybodyHawkingOccupation_eq`).
* **§E — absorption versus stimulated emission** (`superradiant_reflection_iff`).
* **§F — the Hawking population is the KMS kinetic fixed point**
  (`hawkingOccupation_eq_kmsEquilibrium`).

**Honest layering.** The Bose–Einstein occupation, the detailed-balance identity, and the `kuikenWeight`
identification are exact `Real.exp` algebra. Section D now includes the greybody factor as a supplied
mode-transmission coefficient and proves its ordinary-mode positivity and attenuation bounds; it does not derive
that coefficient from the black-hole radial scattering problem. Section E proves Bekenstein's exact sign criterion
for superradiant amplification from supplied quantum absorption and stimulated-emission coefficients. Section F
identifies the Hawking population with the repository's existing KMS gain/loss equilibrium. The mode-by-mode
Bogoliubov/scattering derivation and the full KMS analyticity remain referenced analytic content.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; S.W. Hawking (thermal radiation). Repo carriers:
  `EntropicTime.KayWaldHawkingKMSHorizon`, `ThermoFieldDynamics.MatsubaraThermalOscillator` (`boseEinstein`).
* J.D. Bekenstein, "Black-hole thermodynamics," Physics Today 33 (1980) 24–31: greybody occupation,
  absorption minus stimulated emission, and the superradiant reflection criterion.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open _root_.QuantumMechanics.FiniteTarget

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein


/-- **The Hawking occupation number** `n(ω) = 1/(e^{βω} − 1)` at the Hawking inverse temperature `β = 2π/κ` — the
thermal Bose–Einstein spectrum of radiation from a bifurcate Killing horizon (the same `boseEinstein` occupation
as the thermofield oscillator). -/
noncomputable def hawkingOccupation (β ω : ℝ) : ℝ := 1 / (Real.exp (β * ω) - 1)


/-- **[KMS detailed balance: `n/(n+1) = e^{−βω}`].** The ratio of stimulated emission to total emission of the
Hawking thermal state is the Boltzmann factor `e^{−βω}`: `n = 1/(e^{βω}−1)`, `n+1 = e^{βω}/(e^{βω}−1)`, so
`n/(n+1) = e^{−βω}` — the detailed-balance / KMS condition defining thermal equilibrium at the Hawking
temperature. -/
lemma hawking_detailed_balance (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    hawkingOccupation β ω / (hawkingOccupation β ω + 1) = Real.exp (-(β * ω)) := by
  unfold hawkingOccupation
  have hE : Real.exp (β * ω) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg]
  field_simp
  ring


/-- **[The Hawking Boltzmann factor is the entropic weight] `e^{−βω} = kuikenWeight (1/β) ω`.** The
detailed-balance Boltzmann factor of the Hawking thermal state is the complex-action entropic weight
`kuikenWeight c Π = e^{−Π/c}` at `c = 1/β = T_H = κ/2π`: the Hawking radiation spectrum lives on the arc's
`kuikenWeight` hub. -/
lemma detailed_balance_is_kuiken (β ω : ℝ) :
    Real.exp (-(β * ω)) = kuikenWeight (1 / β) ω := by
  unfold kuikenWeight
  rw [one_div, div_inv_eq_mul]
  ring_nf


/-! ## D. Bekenstein's greybody Hawking spectrum -/

/-- The emitted occupation after transmission through the black-hole potential barrier. Bekenstein's
1980 review writes the mean bosonic occupation as
`Γ / (exp (βω) - 1)`, where `Γ` is the mode absorptivity (greybody factor). This definition deliberately
takes `Γ` as scattering data; it does not manufacture the radial black-hole scattering problem. -/
noncomputable def greybodyHawkingOccupation (Γ β ω : ℝ) : ℝ :=
  Γ * hawkingOccupation β ω

/-- **[Bekenstein 1980, greybody Hawking occupation].** Multiplying the horizon Bose–Einstein
population by the supplied mode-transmission coefficient gives
`Γ / (exp (βω) - 1)`. -/
lemma greybodyHawkingOccupation_eq (Γ β ω : ℝ) :
    greybodyHawkingOccupation Γ β ω = Γ / (Real.exp (β * ω) - 1) := by
  simp [greybodyHawkingOccupation, hawkingOccupation, div_eq_mul_inv]

/-- An ordinary positive-frequency mode with nonnegative transmission has nonnegative emitted
occupation. The assumptions exclude the superradiant sign convention, which is treated separately
through the absorption/stimulated-emission balance below. -/
lemma greybodyHawkingOccupation_nonneg (Γ β ω : ℝ)
    (hΓ : 0 ≤ Γ) (hβω : 0 < β * ω) :
    0 ≤ greybodyHawkingOccupation Γ β ω := by
  rw [greybodyHawkingOccupation_eq]
  have hden : 0 < Real.exp (β * ω) - 1 := by
    rw [sub_pos]
    simpa using (Real.exp_lt_exp.mpr hβω : Real.exp 0 < Real.exp (β * ω))
  exact div_nonneg hΓ hden.le

/-- The upper bound `Γ ≤ 1` makes an ordinary-mode greybody factor attenuate, rather than amplify,
the nonnegative horizon Bose–Einstein population. Combine with
`greybodyHawkingOccupation_nonneg` when the physical lower bound `0 ≤ Γ` is also required. -/
lemma greybodyHawkingOccupation_le (Γ β ω : ℝ)
    (hΓ1 : Γ ≤ 1) (hβω : 0 < β * ω) :
    greybodyHawkingOccupation Γ β ω ≤ hawkingOccupation β ω := by
  have hn : 0 ≤ hawkingOccupation β ω := by
    unfold hawkingOccupation
    have hden : 0 < Real.exp (β * ω) - 1 := by
      rw [sub_pos]
      simpa using (Real.exp_lt_exp.mpr hβω : Real.exp 0 < Real.exp (β * ω))
    exact one_div_nonneg.mpr hden.le
  unfold greybodyHawkingOccupation
  nlinarith [mul_nonneg (sub_nonneg.mpr hΓ1) hn]


/-! ## E. Absorption, stimulated emission, and superradiance -/

/-- The classical reflection coefficient obtained from the net absorptivity. The repository reuses
`dampingRate Γabs Γstim = Γabs - Γstim`: Bekenstein's classical absorptivity is quantum absorption
minus stimulated emission, hence reflection is `1 - (Γabs - Γstim)`. -/
def classicalReflectionCoefficient (Γabs Γstim : ℝ) : ℝ :=
  1 - dampingRate Γabs Γstim

/-- **[Bekenstein 1980, superradiance criterion].** The reflected classical wave is amplified
(`R > 1`) exactly when stimulated emission exceeds quantum absorption. This is the sign theorem behind
black-hole superradiance; the coefficients themselves remain outputs of the mode-scattering problem. -/
theorem superradiant_reflection_iff (Γabs Γstim : ℝ) :
    1 < classicalReflectionCoefficient Γabs Γstim ↔ Γabs < Γstim := by
  unfold classicalReflectionCoefficient dampingRate
  constructor <;> intro h <;> linarith

/-- Outside the superradiant regime, reflection is at most unity exactly when stimulated emission
does not exceed quantum absorption. -/
lemma nonsuperradiant_reflection_iff (Γabs Γstim : ℝ) :
    classicalReflectionCoefficient Γabs Γstim ≤ 1 ↔ Γstim ≤ Γabs := by
  unfold classicalReflectionCoefficient dampingRate
  constructor <;> intro h <;> linarith

/-- The threshold between absorption and amplification has unit reflection exactly when the two
quantum coefficients balance. -/
lemma unit_reflection_iff_absorption_eq_stimulated (Γabs Γstim : ℝ) :
    classicalReflectionCoefficient Γabs Γstim = 1 ↔ Γabs = Γstim := by
  unfold classicalReflectionCoefficient dampingRate
  constructor <;> intro h <;> linarith


/-! ## F. Hawking radiation as the KMS kinetic fixed point -/

/-- **[Hawking population = KMS gain/loss equilibrium].** The horizon occupation is not a second
thermal distribution parallel to the QFT kinetic layer: under the existing KMS detailed-balance
carrier it is exactly `Γ</(Γ> - Γ<)`, the fixed population of the gain/loss Boltzmann equation. -/
theorem hawkingOccupation_eq_kmsEquilibrium (κ : KMSDetailedBalance) (ω : ℝ)
    (hW : κ.W_minus ω ≠ 0) (hexp : Real.exp (κ.beta * ω) - 1 ≠ 0) :
    hawkingOccupation κ.beta ω =
      equilibriumOccupation (κ.W_plus ω) (κ.W_minus ω) := by
  simpa [hawkingOccupation, boseEinstein] using
    (equilibriumOccupation_eq_boseEinstein κ ω hW hexp).symm

/-- The Bekenstein statistical-radiance layer on the shared carriers: the supplied greybody
coefficient multiplies the Hawking spectrum, KMS rates make that spectrum the kinetic fixed point,
and stimulated emission exceeding absorption is exactly the superradiant amplification condition. -/
theorem bekensteinRadiance_statistical_layer (Γ β ω Γabs Γstim : ℝ)
    (κ : KMSDetailedBalance) (hβ : β = κ.beta)
    (hW : κ.W_minus ω ≠ 0) (hexp : Real.exp (κ.beta * ω) - 1 ≠ 0) :
    greybodyHawkingOccupation Γ β ω = Γ / (Real.exp (β * ω) - 1)
      ∧ hawkingOccupation β ω =
        equilibriumOccupation (κ.W_plus ω) (κ.W_minus ω)
      ∧ (1 < classicalReflectionCoefficient Γabs Γstim ↔ Γabs < Γstim) := by
  subst β
  exact ⟨greybodyHawkingOccupation_eq Γ κ.beta ω,
    hawkingOccupation_eq_kmsEquilibrium κ ω hW hexp,
    superradiant_reflection_iff Γabs Γstim⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.greybodyHawkingOccupation_eq where
  formalizes @ "claim:bekenstein-1980-greybody-hawking-occupation-is-transmission-times-bose-einstein",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-greybody-coefficient-is-supplied-scattering-data-not-derived-from-the-radial-black-hole-wave-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.superradiant_reflection_iff where
  formalizes @ "claim:bekenstein-1980-superradiant-amplification-iff-stimulated-emission-exceeds-absorption",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-theorem-proves-the-coefficient-sign-criterion-not-the-kerr-mode-scattering-coefficients"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.hawkingOccupation_eq_kmsEquilibrium where
  formalizes @ "claim:hawking-bose-einstein-population-is-the-kms-gain-loss-fixed-point",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  requires @ "claim:kms-detailed-balance",
  epistemic_status @ "conditional-model",
  caveat @ "claim:kms-correlators-and-their-nonzero-rate-hypotheses-are-explicit-inputs"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.bekensteinRadiance_statistical_layer where
  formalizes @ "claim:bekenstein-1980-greybody-kms-superradiance-statistical-layer",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  requires @ "claim:bekenstein-1980-greybody-hawking-occupation-is-transmission-times-bose-einstein",
  requires @ "claim:hawking-bose-einstein-population-is-the-kms-gain-loss-fixed-point",
  requires @ "claim:bekenstein-1980-superradiant-amplification-iff-stimulated-emission-exceeds-absorption",
  caveat @ "claim:this-composes-the-statistical-identities-but-does-not-formalize-the-bogoliubov-or-kerr-radial-scattering-derivation"

zil_file_contract physlib.kayWaldHawkingRadiationBoseEinstein where
  promises "The Hawking Bose-Einstein occupation, KMS detailed balance, entropic Boltzmann weight, Bekenstein greybody occupation, absorption-versus-stimulated-emission superradiance criterion, and identification of the Hawking population with the existing KMS gain/loss equilibrium."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:KMSDetailedBalance", "lean:BoltzmannFromQFT.equilibriumOccupation"]
  forbids_substitutes ["deriving the greybody coefficient from algebra alone",
    "claiming a Kerr mode-scattering or Bogoliubov theorem",
    "claiming that this file formalizes the whole 1980 review"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.hawking_detailed_balance,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.detailed_balance_is_kuiken,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.greybodyHawkingOccupation_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.superradiant_reflection_iff,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.hawkingOccupation_eq_kmsEquilibrium,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein.bekensteinRadiance_statistical_layer]

/- ZIL-END -/
