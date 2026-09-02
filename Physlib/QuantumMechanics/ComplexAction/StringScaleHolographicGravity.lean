/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir
public import Mathlib.Tactic.FieldSimp
meta import Zil

/-!
# The string-theory face: Newton's constant is the Regge slope

`HolographicGravityFromModularFlow` read Einstein's coupling out of the spacetime modular flow at the
holographic Newton constant `G = ℏc/m²`.  String theory quantizes gravity by a different route — the
**graviton is the massless spin-2 mode of the closed string** — yet the two meet at one number.  Setting
the mass scale to the **string mass** `m_s = ℏ/(c√α')` collapses the holographic identities onto the
string scale, and Newton's constant becomes the **Regge slope** `α'`.

## The graviton is the massless leading Regge state, consistent at `D = 26`

On the leading Regge trajectory `M² = (J − α₀)/α'` (`Yukawa.ReggeStringMassYukawaReplacement.reggeMassSq`)
the state at `J = α₀` is massless (`reggeMassSq_eq_zero_iff`): for the closed string `α₀ = 2`, that is the
**spin-2 graviton**.  It is consistent only in the critical dimension: the ζ-regularized transverse
Casimir intercept `a = (D−2)/24` (`Lorentz.SciamaFockStringCasimir.stringIntercept`, resting on the
honestly-proved `SciamaFockZetaCasimir.riemannZeta_neg_one`, ζ(−1) = −1/12) equals `1` exactly at
`D = 26` (`stringIntercept_critical`, `stringIntercept_eq_one_iff`).  That is string theory's own
quantization of gravity — a graviton in the spectrum — and it fixes the slope `α'` as the one scale of
the whole tower.

## The string mass and the four collapses

`stringMass α' c ħ = ℏ/(c√α')` is the mass whose reduced Compton wavelength is the string length
`ℓ_s = √α'`.  Feeding it into the holographic identities:

* `comptonWavelength_stringMass` — `λ_C(m_s) = √α' = ℓ_s`: the Compton wavelength of the string mass is
  the string length.
* `holographicG_stringMass` — `G = ℏc/m_s² = c³α'/ℏ`: **Newton's constant is the Regge slope** (in
  natural units `G = α'`).  The gravitational coupling *is* the string tension scale `1/α'` inverted —
  the identity behind the prose analogy the repository already carries between
  `MassOrigin.GravitationalMassHorizonEntropyNoYukawa` (the `c³/4G` side) and
  `ReggeStringMassYukawaReplacement` (the `1/α'` side).
* `reggeSlope_eq_planckLengthSq` — `α' = ℓ_P² = Gℏ/c³` (`ComptonClock.ZeroPointLength.planckLengthSq`):
  the Regge slope is the Planck area; the string length is the Planck length.
* `bekensteinHawking_stringMass_eq_reggeCells` — `S = 𝒜c³/(4Gℏ) = A/(4α')`: the Bekenstein–Hawking
  horizon entropy counts its area in string cells `α'`.

`string_quantized_gravity_synthesis` bundles the four.

## Honest scope: two different modular structures

This is a statement about the **mass/length scale** — the Regge slope equals the Planck area — reached
from the **spacetime** Tomita–Takesaki modular flow of `HolographicGravityFromModularFlow` (the
Bisognano–Wichmann boost, the Unruh temperature).  String theory's own modular structure is the
**worldsheet** `SL(2,ℤ)` invariance of the one-loop torus (the repository's `ChernSimons/` theta
characters, the Verlinde `cswSMatrix`, `torusPartitionFunction_S_invariant`).  Those are *distinct*
modular groups — worldsheet `τ` versus spacetime boost — and are **not** conflated here: the bridge is
the scale identification `α' = ℓ_P²`, not a claim that the two modular flows are the same.  The classical
substrate stays kernel-clean; the full string quantization (worldsheet path integral, the graviton
vertex operator) is not formalized — only the scale identity and the massless-Regge/`D=26` facts it
rests on.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity

open Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength
open Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir

/-- **The string mass** `m_s = ℏ/(c√α')` — the mass whose reduced Compton wavelength `λ_C = ℏ/(m_s c)` is
the string length `ℓ_s = √α'`. -/
noncomputable def stringMass (α' c ħ : ℝ) : ℝ := ħ / (c * Real.sqrt α')

theorem stringMass_ne_zero (α' c ħ : ℝ) (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    stringMass α' c ħ ≠ 0 := by
  unfold stringMass
  exact div_ne_zero hħ (mul_ne_zero hc (Real.sqrt_pos.mpr hα).ne')

/-- `m_s² = ℏ²/(c²α')` — squaring `stringMass` clears the square root. -/
theorem stringMass_sq (α' c ħ : ℝ) (hα : 0 < α') :
    stringMass α' c ħ ^ 2 = ħ ^ 2 / (c ^ 2 * α') := by
  unfold stringMass
  rw [div_pow, mul_pow, Real.sq_sqrt hα.le]

/-- **`λ_C(m_s) = √α' = ℓ_s`.**  The reduced Compton wavelength of the string mass is the string
length. -/
theorem comptonWavelength_stringMass (α' c ħ : ℝ) (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonWavelength (stringMass α' c ħ) c ħ = Real.sqrt α' := by
  unfold comptonWavelength stringMass
  have hs : Real.sqrt α' ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  field_simp

/-- **`G = ℏc/m_s² = c³α'/ℏ`: Newton's constant is the Regge slope.**  The holographic Newton constant
evaluated at the string mass is `c³` times the Regge slope `α'` over `ℏ` — in natural units, `G = α'`. -/
theorem holographicG_stringMass (α' c ħ : ℝ) (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    ħ * c / stringMass α' c ħ ^ 2 = c ^ 3 * α' / ħ := by
  rw [stringMass_sq α' c ħ hα]
  field_simp

/-- **`α' = ℓ_P² = Gℏ/c³`: the Regge slope is the Planck area.**  The Planck-area combination
`planckLengthSq` of the holographic Newton constant at the string mass is exactly the Regge slope. -/
theorem reggeSlope_eq_planckLengthSq (α' c ħ : ℝ) (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    planckLengthSq (ħ * c / stringMass α' c ħ ^ 2) ħ c = α' := by
  unfold planckLengthSq
  rw [holographicG_stringMass α' c ħ hα hc hħ]
  field_simp

/-- **`S = 𝒜c³/(4Gℏ) = A/(4α')`: Bekenstein–Hawking entropy in string cells.**  At the string mass the
horizon entropy counts its area `A` in string cells `α'` (= Planck cells `ℓ_P²`). -/
theorem bekensteinHawking_stringMass_eq_reggeCells (A α' c ħ : ℝ)
    (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    A * c ^ 3 / (4 * ((ħ * c / stringMass α' c ħ ^ 2) * ħ)) = A / (4 * α') := by
  rw [bekensteinHawking_holographicG_eq_comptonCells A (stringMass α' c ħ) c ħ
        (stringMass_ne_zero α' c ħ hα hc hħ) hc hħ,
      comptonWavelength_stringMass α' c ħ hα hc hħ, Real.sq_sqrt hα.le]

/-- **The graviton is the massless leading Regge state, consistent at `D = 26`.**  At `J = α₀` the Regge
mass vanishes (`reggeMassSq_eq_zero_iff`) — the closed-string graviton (`α₀ = 2`, spin 2) — and the
ζ-regularized intercept is critical exactly at `D = 26` (`stringIntercept_critical`). -/
theorem graviton_massless_regge_critical_dimension (α₀ α' : ℝ) (hα' : α' ≠ 0) :
    reggeMassSq α₀ α₀ α' = 0 ∧ stringIntercept 26 = 1 :=
  ⟨(reggeMassSq_eq_zero_iff α₀ α₀ α' hα').mpr rfl, stringIntercept_critical⟩

/-- **The string-scale collapse in one statement.**  At the string mass `m_s = ℏ/(c√α')`: the Compton
wavelength is the string length `√α'`; Newton's constant is the Regge slope, `G = c³α'/ℏ`; that `G`'s
Planck area is the Regge slope, `α' = ℓ_P²`; and the horizon entropy counts area in string cells,
`S = A/(4α')`. -/
theorem string_quantized_gravity_synthesis (A α' c ħ : ℝ)
    (hα : 0 < α') (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonWavelength (stringMass α' c ħ) c ħ = Real.sqrt α'
      ∧ ħ * c / stringMass α' c ħ ^ 2 = c ^ 3 * α' / ħ
      ∧ planckLengthSq (ħ * c / stringMass α' c ħ ^ 2) ħ c = α'
      ∧ A * c ^ 3 / (4 * ((ħ * c / stringMass α' c ħ ^ 2) * ħ)) = A / (4 * α') :=
  ⟨comptonWavelength_stringMass α' c ħ hα hc hħ,
    holographicG_stringMass α' c ħ hα hc hħ,
    reggeSlope_eq_planckLengthSq α' c ħ hα hc hħ,
    bekensteinHawking_stringMass_eq_reggeCells A α' c ħ hα hc hħ⟩

end Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.holographicG_stringMass where
  formalizes @ "claim:at-the-string-mass-hbar-over-c-root-alpha-prime-the-holographic-newton-constant-g-equals-hbar-c-over-mass-squared-becomes-c-cubed-alpha-prime-over-hbar-so-newtons-constant-is-the-regge-slope",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.holographicG_planckArea_eq_comptonArea"

zil attach Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.reggeSlope_eq_planckLengthSq where
  formalizes @ "claim:at-the-string-mass-the-planck-area-of-the-holographic-newton-constant-equals-the-regge-slope-alpha-prime-equals-planck-length-squared-equals-g-hbar-over-c-cubed",
  requires @ "claim:at-the-string-mass-hbar-over-c-root-alpha-prime-the-holographic-newton-constant-g-equals-hbar-c-over-mass-squared-becomes-c-cubed-alpha-prime-over-hbar-so-newtons-constant-is-the-regge-slope",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLengthSq"

zil attach Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.bekensteinHawking_stringMass_eq_reggeCells where
  formalizes @ "claim:at-the-string-mass-the-bekenstein-hawking-horizon-entropy-a-c-cubed-over-four-g-hbar-counts-its-area-in-string-cells-a-over-four-alpha-prime",
  requires @ "claim:at-the-string-mass-the-planck-area-of-the-holographic-newton-constant-equals-the-regge-slope-alpha-prime-equals-planck-length-squared-equals-g-hbar-over-c-cubed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.bekensteinHawking_holographicG_eq_comptonCells"

zil attach Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.graviton_massless_regge_critical_dimension where
  formalizes @ "claim:the-graviton-is-the-massless-leading-regge-state-at-spin-equals-intercept-and-the-zeta-regularized-string-intercept-is-critical-exactly-at-dimension-twenty-six",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement.reggeMassSq_eq_zero_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir.stringIntercept_critical"

zil_file_contract physlib.stringScaleHolographicGravity where
  promises "The string-theory face of the modular-flow holographic gravity: setting the mass scale to the string mass m_s = hbar/(c root alpha-prime), whose reduced Compton wavelength is the string length root alpha-prime, collapses the holographic identities onto the string scale and makes Newton's constant the Regge slope. The holographic G = hbar c/m^2 becomes G = c^3 alpha-prime/hbar (Newton's constant is the Regge slope; in natural units G = alpha-prime), its Planck area planckLengthSq equals the Regge slope alpha-prime = ell_P^2 = G hbar/c^3, and the Bekenstein-Hawking horizon entropy A c^3/(4 G hbar) counts its area in string cells A/(4 alpha-prime). The graviton is the massless leading Regge state at spin equal to the intercept (reggeMassSq zero iff J equals alpha_0; the closed-string graviton is spin two), consistent only in the critical dimension where the zeta-regularized transverse intercept (D-2)/24 equals one, D = 26, resting on the honestly proved zeta(-1) = -1/12. Honest scope: this is a scale identification alpha-prime = ell_P^2 reached from the spacetime Tomita-Takesaki modular flow (Bisognano-Wichmann boost, Unruh temperature); string theory's own worldsheet SL(2,Z) modular invariance of the one-loop torus is a distinct modular structure and is not conflated with the spacetime boost-modular flow. The full worldsheet string quantization is not formalized -- only the scale identity and the massless-Regge and D=26 facts it rests on."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.holographicG_planckArea_eq_comptonArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.bekensteinHawking_holographicG_eq_comptonCells",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLengthSq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
    "lean:Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement.reggeMassSq",
    "lean:Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement.reggeMassSq_eq_zero_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockStringCasimir.stringIntercept_critical"]
  forbids_substitutes [
    "conflating the worldsheet SL(2,Z) modular invariance of the string one-loop torus with the spacetime Tomita-Takesaki modular flow: the bridge is the scale identity alpha-prime = ell_P^2, not an identity of the two modular groups",
    "claiming a full worldsheet string quantization: only the scale identity and the massless-Regge / D=26 facts are formalized"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.stringMass_ne_zero,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.stringMass_sq,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.comptonWavelength_stringMass,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.holographicG_stringMass,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.reggeSlope_eq_planckLengthSq,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.bekensteinHawking_stringMass_eq_reggeCells,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.graviton_massless_regge_critical_dimension,
    Physlib.QuantumMechanics.ComplexAction.StringScaleHolographicGravity.string_quantized_gravity_synthesis]

#zil_horn_grounding physlib.stringScaleHolographicGravity

/- ZIL-END -/
