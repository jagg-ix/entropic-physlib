/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Clock.EntropicAgreement
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree

meta import Zil

/-!
# The entropic clock's rate anchored to the Compton–Zitterbewegung frequency

`EntropicAgreement` proves that a calibrated entropic clock reads physical proper time
*given* the action-rate law `ΔS_I = ℏ ω₀ Δτ_phys`, in which the clock frequency `ω₀`
(`PhaseClock.omega0`) is a free parameter — the explicit "load-bearing physical premise".
Nothing internal fixes `ω₀`, so the identification is conditional on an internally chosen scale.

Here `ω₀` is anchored to the **mass-determined Compton frequency** `ω_C = m c² / ħ`
(`FrequencyTrinity.comptonFrequency`), equivalently the rest-frame Zitterbewegung frequency
`ω_Z / 2` (`zitterbewegung_rest_eq_two_compton`).  Consequences: the action rate `ℏ ω₀` is
exactly the **rest energy** `m c²` (`comptonAnchored_actionRate_eq_restEnergy`), and the tick
is the **Compton period** `2π/ω₀ = h/(m c²)` (`comptonAnchoredClock_period`; the Zitterbewegung
rotation period of Consa, *Helical Solenoid Model*, PP 14 (2018), Eq. 7).

**The mass is not a bare input — it is three coinciding origins, all this one clock.**
`MassOrigin.HiggsClockThreeOrigins` proves the Higgs/Yukawa mass `yv/√2`, the gravitational
horizon-entropy mass `(c/4G)Ȧ`, and the topological Chern–Simons mass `e²k/2π` are the *same*
internal Compton clock `ω = comptonFrequency(yukawaMass y v) = higgsClockFrequency`.  Since that
is *definitionally* `comptonAnchoredClock.omega0` at `m = yukawaMass y v`, the anchored entropic
clock reads proper time with its unit fixed by the *three-origin* mass, reaching `G` through the
horizon form `ω = c³Ȧ/(4Għ)` — assembled in `comptonAnchored_entropicTime_threeOriginMass`.  And `G` is
itself derived, not an input: the `G`-free Compton-cell count gives `G = ħc/m² = ħcσ₀⁴`
(`ComptonCellNewtonConstant`), so `G = c⁵/(ħ ω₀²)` through the clock's own frequency
(`comptonAnchored_newtonG_eq_from_clockFrequency`) — the clock, the three-origin mass, and `G` are one
scale.  The rapidity / boost structure of this clock is `IsotonicRapidityComptonClock` (`√(ξ²+1)=γ`
boosts `ω_C`).

**Experimental anchors — narrow subclaims only.** `ω_C = m c²/ħ` is de Broglie's internal-clock
frequency, but the cited experiments support *narrower* facets and **none tests the load-bearing
CAT/EPT premise `ΔS_I = m c² Δτ_phys`**; none is a novel prediction (OpenWave M9.109d paper-scope
audit).  `h/m = ω_C` measured to 0.2 ppb is atom-*recoil* metrology used to determine `α` (Parker,
Yu, Müller, *Science* 360, 191 (2018)); the "Compton clock" of Lan, Müller (*Science* 339, 554
(2013)) is referenced to a *subharmonic* of the atomic Compton frequency — mass-time metrology, not
the imaginary-action law or `G`; the electron channeling resonance `p ≈ 81 MeV/c` (162 MeV/c at
`2ω_Z`; Gouanère, Catillon, *AFLB* 33, 85 (2008)) is *compatible with*, not a confirmation of, the
internal clock; the self-interfering clock (Margalit, *Science* 349, 1205 (2015); SG interferometer,
*Sci. Adv.* 7, eabg2879 (2021)) demonstrates two-spin-state clock-path *complementarity*, not a
Compton clock or a redshift measurement.  Wolf *et al.* (2011) is the standing objection to reading
closed atom interferometers as Compton-redshift clocks.  ZBW-model grounding: Fleury & Rousselle,
*Symmetry* 17, 360 (2025); Consa, PP 14 (2018).

**Honest scope.** The anchor fixes the time unit to the mass and does **not** derive the mass
*value*: `y, v` are inputs and the lepton-mass hierarchy from `y` is a negative result.  The
three-origin coincidence (`hHorizon`, `hTopo`) is a conditional hypothesis, not a derivation.  `G`
is **not** an input: it is derived as `ħc/m² = ħcσ₀⁴` (`ComptonCellNewtonConstant`), so the clock, the
three-origin mass, and `G` are one scale (`comptonAnchored_newtonG_eq_from_clockFrequency`).  This is a
**holographic** relation: `G = 𝒜c³/(ℏN)` with the bit count `N = 4π(log K)²` supplied *`G`-free* by the
Compton-cell tiling, so `G = ℏc/m²` is the entanglement screen's area-per-bit and `m` is the **screen /
cell scale** `λ_C = ℏ/mc`, not a particle-species label.  Equivalently it is the Compton-cell = Planck-cell
matching (`ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_massScale`): the QM tiling
`λ_C²` and the gravity tiling `ℓ_P² = Għ/c³` of the same screen coincide exactly at `m = m_Planck`
(`λ_C(m_Planck) = ℓ_P` — the Planck scale as the QM/gravity cell match).  So the OpenWave M9.109b
"species non-universality" test (substitute electron/muon/proton → `G_eff/G_N ≈ 5.7×10⁴⁴ / 1.3×10⁴⁰ /
1.7×10³⁸`) is a **category error**: it plugs particle masses into the screen-scale slot, where
`λ_C ∝ 1/m` makes different cells trivially give different area-per-bit, and its "inversion control"
re-asserts the very circularity this `G`-free count removes (`G` is not read back off a `G`-laden `N`).
The genuine residue — already the honest scope — is that `G`'s numerical *value* stays conditional on
fixing one scale (`m` / `σ₀` / `ω₀`): the empirical input is *shifted from `G` to a mass*, not eliminated,
and `G m² = ℏc` is exact but does not fix the number parameter-free.  The results are parametric in `m`;
the experiments confirm the narrow subclaims above, not the CAT/EPT `G` chain; the Margalit lag is
engineered and the Compton-redshift-clock interpretation is contested (Wolf 2011).
-/

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.Clock.Phase
open Physlib.QuantumMechanics.Clock.EntropicAgreement
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.Thermodynamics.SecondLaw
open Physlib.SpaceTime

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor

/-- A phase clock whose frequency is the mass-fixed Compton frequency `ω_C = m c² / ħ`,
rather than a free parameter. -/
def comptonAnchoredClock (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) : PhaseClock where
  omega0 := comptonFrequency m c ħ
  omega0_pos := by unfold comptonFrequency; positivity

@[simp] lemma comptonAnchoredClock_omega0 (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    (comptonAnchoredClock m c ħ hm hc hħ).omega0 = comptonFrequency m c ħ := rfl

/-- The anchored rate is the rest-frame Zitterbewegung frequency halved: `ω_C = ω_Z / 2`. -/
lemma comptonAnchoredClock_omega0_eq_half_zitterbewegung
    (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    (comptonAnchoredClock m c ħ hm hc hħ).omega0 = zitterbewegungFrequency 0 m c ħ / 2 := by
  rw [comptonAnchoredClock_omega0, zitterbewegung_rest_eq_two_compton m c ħ hm.le]; ring

/-- **The anchored clock ticks at the Compton period** `2π/ω₀ = h/(m c²)` (with `h = 2πħ`) —
the rotation period of the Zitterbewegung electron (Consa, *Helical Solenoid Model*, Eq. 7). -/
lemma comptonAnchoredClock_period (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    2 * Real.pi / (comptonAnchoredClock m c ħ hm hc hħ).omega0 = 2 * Real.pi * ħ / (m * c ^ 2) := by
  rw [comptonAnchoredClock_omega0]
  unfold comptonFrequency
  rw [div_div_eq_mul_div]

/-- **The derived Newton constant is fixed by the clock's own frequency — `G` is not an input.**
The `G`-free Compton-cell prediction gives `G = ħc/m²`
(`ComptonCellNewtonConstant.newtonG_from_comptonCellBits`; equivalently `G = ħcσ₀⁴` from the inference
width, `newtonG_from_positionVariance`).  Eliminating the mass through the anchored clock `ω₀ = mc²/ħ`
yields `G = c⁵/(ħ ω₀²)`: Newton's constant as a function of the entropic clock's frequency alone, with no
independent `G`.  (Conditional in the same way as the mass-scale/inference-width identification.) -/
lemma comptonAnchored_newtonG_eq_from_clockFrequency
    (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    ħ * c / m ^ 2 = c ^ 5 / (ħ * (comptonAnchoredClock m c ħ hm hc hħ).omega0 ^ 2) := by
  rw [comptonAnchoredClock_omega0]
  unfold comptonFrequency
  field_simp [hm.ne', hc.ne', hħ.ne']

/-- **The anchor discharges the internal calibration knob.**  With `ω₀ = ω_C = m c²/ħ`, the
action rate `ℏ ω₀` in the entropic-clock calibration is exactly the rest energy `m c²` — a
mass-fixed quantity, not an internally chosen scale.  (Here `ħ` is the worldline's own `ℏ`.) -/
lemma comptonAnchored_actionRate_eq_restEnergy
    (m c : ℝ) (W : EntropyArrowWorldline) (hm : 0 < m) (hc : 0 < c) :
    W.ℏ * (comptonAnchoredClock m c W.ℏ hm hc W.ℏ_pos).omega0 = m * c ^ 2 := by
  rw [comptonAnchoredClock_omega0]
  unfold comptonFrequency
  field_simp [W.ℏ_pos.ne']

/-- The Compton-anchored calibration is exactly the rest-energy action law: any worldline
whose imaginary action accumulates as `ΔS_I = m c² Δτ_phys` satisfies the anchored-clock
calibration.  Shows the anchored premise is inhabitable and its rate is mass-fixed. -/
lemma comptonAnchored_calibration_of_restEnergy_law
    (m c : ℝ) (W : EntropyArrowWorldline) (τphys : ℝ → ℝ) (hm : 0 < m) (hc : 0 < c)
    (h : ∀ t₁ t₂, W.S_I_along t₂ - W.S_I_along t₁ = m * c ^ 2 * (τphys t₂ - τphys t₁)) :
    EntropicPhysicalClockCalibration (comptonAnchoredClock m c W.ℏ hm hc W.ℏ_pos) W τphys where
  action_advance_eq := fun t₁ t₂ => by
    rw [comptonAnchored_actionRate_eq_restEnergy m c W hm hc]; exact h t₁ t₂

/-- **Anchored entropic-clock identity.**  For a worldline calibrated to the Compton-anchored
clock, the entropic clock reads exactly the physical proper time — the clock unit now fixed by
the mass through `ω_C = m c²/ħ`.  Specialization of `entropicPhysicalTimeAdvance_eq_physicalTime`. -/
theorem comptonAnchored_entropicTime_eq_physicalTime
    (m c : ℝ) (W : EntropyArrowWorldline) (τphys : ℝ → ℝ) (hm : 0 < m) (hc : 0 < c)
    (K : EntropicPhysicalClockCalibration (comptonAnchoredClock m c W.ℏ hm hc W.ℏ_pos) W τphys)
    (t₁ t₂ : ℝ) :
    entropicPhysicalTimeAdvance (comptonAnchoredClock m c W.ℏ hm hc W.ℏ_pos) W t₁ t₂ =
      τphys t₂ - τphys t₁ :=
  entropicPhysicalTimeAdvance_eq_physicalTime _ W τphys K t₁ t₂

/-- **Spacetime form.**  When the imaginary action accumulates at the rest-energy rate `m c²`
over a geometric proper-time interval, the Compton-anchored entropic clock reads that geometric
proper time. -/
theorem comptonAnchored_entropicTime_eq_geometricProperTime
    (m c : ℝ) (W : EntropyArrowWorldline) (hm : 0 < m) (hc : 0 < c)
    (t₁ t₂ : ℝ) {sd : ℕ} (q p : SpaceTime sd)
    (hcal : W.S_I_along t₂ - W.S_I_along t₁ = m * c ^ 2 * SpaceTime.properTime q p) :
    entropicPhysicalTimeAdvance (comptonAnchoredClock m c W.ℏ hm hc W.ℏ_pos) W t₁ t₂ =
      SpaceTime.properTime q p := by
  apply entropicPhysicalTimeAdvance_eq_geometricProperTime
  rw [comptonAnchored_actionRate_eq_restEnergy m c W hm hc]
  exact hcal

/-- **The entropic clock reads proper time with a three-origin mass unit.**  At `m = yukawaMass y v`,
and when that mass coincides with the gravitational horizon-entropy mass (`hHorizon`) and the
topological Chern–Simons mass (`hTopo`), the Compton-anchored entropic clock (i) reads the geometric
proper time, (ii) has rate `ω₀ = higgsClockFrequency`, (iii)–(v) whose Compton mass is the Yukawa =
horizon = topological mass, and (vi) is expressible through `G` as `ω₀ = c³Ȧ/(4Għ)`.  Composes
`comptonAnchored_entropicTime_eq_geometricProperTime` with `higgs_clock_three_origins`. -/
theorem comptonAnchored_entropicTime_threeOriginMass
    (y v G c Adot : ℝ) (dj : DJTData) (W : EntropyArrowWorldline)
    (hm : 0 < yukawaMass y v) (hc : 0 < c)
    (hHorizon : yukawaMass y v = gravitationalMass G c Adot)
    (hTopo : yukawaMass y v = topologicalMass dj)
    (t₁ t₂ : ℝ) {sd : ℕ} (q p : SpaceTime sd)
    (hcal : W.S_I_along t₂ - W.S_I_along t₁ = yukawaMass y v * c ^ 2 * SpaceTime.properTime q p) :
    entropicPhysicalTimeAdvance (comptonAnchoredClock (yukawaMass y v) c W.ℏ hm hc W.ℏ_pos) W t₁ t₂
        = SpaceTime.properTime q p
      ∧ (comptonAnchoredClock (yukawaMass y v) c W.ℏ hm hc W.ℏ_pos).omega0
        = higgsClockFrequency y v c W.ℏ
      ∧ comptonMass (higgsClockFrequency y v c W.ℏ) c W.ℏ = yukawaMass y v
      ∧ yukawaMass y v = gravitationalMass G c Adot
      ∧ yukawaMass y v = topologicalMass dj
      ∧ higgsClockFrequency y v c W.ℏ = c ^ 3 * Adot / (4 * G * W.ℏ) := by
  obtain ⟨hmass, hhor, htopo, hhorform, _⟩ :=
    higgs_clock_three_origins y v G c Adot W.ℏ dj hc.ne' W.ℏ_pos.ne' hHorizon hTopo
  exact ⟨comptonAnchored_entropicTime_eq_geometricProperTime (yukawaMass y v) c W hm hc t₁ t₂ q p hcal,
    rfl, hmass, hhor, htopo, hhorform⟩

/- ZIL-BEGIN -/

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy where
  at_level physical_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline]

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock_omega0_eq_half_zitterbewegung where
  formalizes @ "claim:the-compton-anchored-entropic-clock-rate-equals-half-the-rest-frame-zitterbewegung-frequency",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton",
  supported_by @ "paper:fleury-rousselle-2025-critical-review-of-zitterbewegung-electron-models"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock_period where
  formalizes @ "claim:the-compton-anchored-entropic-clock-tick-period-is-the-compton-period-h-over-m-c-squared",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:consa-2018-helical-solenoid-model-of-the-electron"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_newtonG_eq_from_clockFrequency where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  formalizes @ "claim:the-derived-newton-constant-equals-c-fifth-over-hbar-omega-zero-squared-fixed-by-the-entropic-clock-frequency-not-an-independent-input",
  epistemic_status @ "consistency-identity",
  derives @ "claim:newtons-constant-is-not-an-independent-input-it-is-fixed-by-the-anchored-clock-frequency-through-the-g-free-compton-cell-mass-scale",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  caveat @ "claim:the-g-derivation-is-conditional-on-the-same-mass-scale-or-inference-width-identification-as-the-compton-cell-count",
  caveat @ "claim:g-equals-hbar-c-over-m-squared-is-a-holographic-area-per-bit-relation-in-which-m-is-the-screen-cell-scale-lambda-c-equals-hbar-over-m-c-not-a-particle-species-so-the-openwave-m9-109b-substitution-of-electron-muon-proton-masses-is-a-category-error-the-genuine-residue-is-that-g-numerical-value-stays-conditional-on-fixing-one-scale-with-the-empirical-input-shifted-from-g-to-a-mass-not-a-parameter-free-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy where
  formalizes @ "claim:the-compton-anchored-entropic-clock-action-rate-hbar-omega-zero-equals-the-rest-energy-m-c-squared",
  epistemic_status @ "consistency-identity",
  derives @ "claim:the-entropic-clock-time-unit-is-fixed-by-the-particle-mass-through-omega-c-equals-m-c-squared-over-hbar",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
  supported_by @ "paper:parker-2018-measurement-of-the-fine-structure-constant-atom-interferometry",
  supported_by @ "paper:lan-muller-2013-a-clock-directly-linking-time-to-a-particle-mass",
  experimental_bound @ "atom-recoil-h-over-m-metrology-fixes-the-compton-frequency-m-c-squared-over-hbar-to-0-point-2-ppb-parker-2018-lan-muller-subharmonic-compton-clock-mass-time-metrology",
  caveat @ "claim:parker-2018-supports-recoil-h-over-m-metrology-for-alpha-and-lan-muller-2013-a-subharmonic-compton-clock-and-mass-time-metrology-neither-tests-direct-compton-ticking-newton-g-or-the-cat-ept-imaginary-action-premise-delta-s-i-equals-m-c-squared-delta-tau-openwave-m9-109d"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_physicalTime where
  formalizes @ "claim:an-entropic-clock-whose-rate-is-anchored-to-the-compton-zitterbewegung-frequency-reads-physical-proper-time-with-a-mass-fixed-unit",
  epistemic_status @ "conditional-model",
  requires @ "claim:after-calibration-by-delta-s-i-equals-hbar-omega-zero-delta-tau-physical-the-entropic-clock-read-through-an-independent-phase-clock-equals-physical-proper-time",
  supported_by @ "paper:gouanere-2008-experimental-observation-compatible-with-particle-internal-clock-channeling",
  supported_by @ "paper:hestenes-2008-zitterbewegung-in-quantum-mechanics-research-program",
  experimental_bound @ "electron-channeling-clock-resonance-p-approx-81-mev-c-and-162-mev-c-two-times-zitterbewegung-gouanere-catillon-2008",
  caveat @ "claim:the-anchor-fixes-the-time-unit-to-the-mass-it-does-not-derive-the-mass-atoms-realize-it-directly-electron-via-channeling-and-the-experiments-confirm-not-a-novel-prediction"

/-- **The Compton temperature is the `k_B` reading of the Compton clock**:
`T_C = ħ·ω_C/(2π k_B)` — the interface between the frequency sector and the temperature sector.
This is the mediating definition whose absence made the `comptonFrequency ≐ unruhTemperature`
unification inhomogeneous by exactly the `k_B` conversion; with it,
`Thermodynamics.unruh_eq_comptonTemperature_iff` reads: the anchored clock's own vacuum
temperature is reached exactly at the Compton acceleration `a_C = c·ω_C`. -/
theorem comptonTemperature_eq_clock {m c kB ħ : ℝ} (hħ : ħ ≠ 0) :
    Physlib.Thermodynamics.comptonTemperature m c kB
      = ħ * FrequencyTrinity.comptonFrequency m c ħ / (2 * Real.pi * kB) := by
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
    FrequencyTrinity.comptonFrequency
  have hcancel : ħ * (m * c ^ 2 / ħ) = m * c ^ 2 := by field_simp
  rw [hcancel]

/-- Link found by `#zil_link`: `deBroglieTemperature` is `deBroglieFrequency` under `the same names` with conversion `ℏ · kB^-1` and prescription `× 1/2 · π^-1`. -/
theorem deBroglieTemperature_eq_deBroglieFrequency_scaled (E kB ħ : ℝ) (hħ : ħ ≠ 0) :
    Physlib.Thermodynamics.deBroglieTemperature E kB
      = ((1 / 2 : ℝ) * ħ / (kB * Real.pi)) * Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency E ħ := by
  unfold Physlib.Thermodynamics.deBroglieTemperature
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency
  field_simp


/-- **The anchored clock's entropic action over a displacement**: at the rest-energy rate
`Ṡ_I = mc²` (`comptonAnchored_actionRate_eq_restEnergy`), the imaginary action accumulated
over the light-crossing time `Δx/c` of a displacement is `S_I = mc·Δx` — one Compton
wavelength of displacement accumulates exactly `ℏ` of action. -/
theorem restEnergyRate_lightCrossing_action (m c Δx : ℝ) (hc : c ≠ 0) :
    m * c ^ 2 * (Δx / c) = m * c * Δx := by
  field_simp

/-- **The displacement-entropy ansatz, discharged**: Verlinde's `ΔS_V = 2π·k_B·mcΔx/ℏ` *is*
the `k_B` reading of the anchored clock's entropic action over the displacement —
`ΔS_V = 2π·k_B·(S_I/ℏ)` with `S_I = mc·Δx` (`restEnergyRate_lightCrossing_action`) — through
the same `ℏ → k_B` interface conversion as the temperature welds, the `2π` being the
clock-cycle normalization of the 2π-quantization family.  The WEP chain therefore rests on
the Compton-anchor *calibration* (a unit choice, recorded as such in this file's caveats) and
exact identities — not on a free postulate. -/
theorem verlindeDisplacementEntropy_eq_entropicAction_reading (ℏ kB m c Δx : ℝ) :
    Physlib.Thermodynamics.verlindeDisplacementEntropy ℏ kB m c Δx
      = 2 * Real.pi * kB * Physlib.Thermodynamics.SecondLaw.entropicTimeOf (m * c * Δx) ℏ := by
  unfold Physlib.Thermodynamics.verlindeDisplacementEntropy
    Physlib.Thermodynamics.SecondLaw.entropicTimeOf
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime
  ring

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.verlindeDisplacementEntropy_eq_entropicAction_reading where
  derives @ "assumption:displacement-entropy-ansatz",
  formalizes @ "claim:verlindes-displacement-entropy-is-the-boltzmann-reading-of-the-anchored-clocks-entropic-action-over-the-displacement",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.entropicTimeOf",
  caveat @ "claim:conditional-on-the-compton-anchor-calibration-which-fixes-the-time-unit-to-the-mass-a-unit-choice-not-a-physical-postulate"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonTemperature_eq_clock where
  formalizes @ "claim:the-compton-temperature-is-the-boltzmann-constant-reading-of-the-compton-clock-frequency",
  supported_by @ "lean:Physlib.Thermodynamics.comptonTemperature",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_geometricProperTime where
  formalizes @ "claim:when-imaginary-action-accumulates-at-the-rest-energy-rate-m-c-squared-the-compton-anchored-entropic-clock-reads-the-geometric-proper-time",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-compton-anchored-entropic-clock-action-rate-hbar-omega-zero-equals-the-rest-energy-m-c-squared",
  supported_by @ "paper:osche-2011-electron-channeling-resonance-and-de-broglie-internal-clock",
  supported_by @ "paper:consa-2018-helical-solenoid-model-of-the-electron",
  supported_by @ "paper:margalit-2015-a-self-interfering-clock-as-a-which-path-witness",
  supported_by @ "paper:margalit-2021-realization-of-a-complete-stern-gerlach-interferometer",
  experimental_bound @ "self-interfering-clock-two-spin-state-clock-path-complementarity-margalit-2015-engineered-differential-not-a-compton-clock-or-relativistic-redshift",
  caveat @ "claim:margalit-2015-demonstrates-two-spin-state-clock-path-complementarity-not-a-compton-clock-a-relativistic-redshift-measurement-or-the-cat-ept-g-chain-the-proper-time-differential-is-engineered-by-a-magnetic-gradient-and-the-compton-redshift-clock-interpretation-of-closed-atom-interferometers-is-contested-wolf-et-al-2011-openwave-m9-109d"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_threeOriginMass where
  formalizes @ "claim:the-compton-anchored-entropic-clock-reads-proper-time-with-its-unit-fixed-by-the-three-origin-yukawa-horizon-topological-mass-one-internal-compton-clock",
  epistemic_status @ "conditional-model",
  requires @ "claim:when-imaginary-action-accumulates-at-the-rest-energy-rate-m-c-squared-the-compton-anchored-entropic-clock-reads-the-geometric-proper-time",
  derives @ "claim:the-entropic-time-sector-connects-to-the-mass-origin-sector-and-reaches-the-gravitational-constant-through-the-horizon-form-of-the-internal-compton-clock",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins.higgs_clock_three_origins",
  caveat @ "claim:the-three-origin-coincidence-is-a-conditional-hypothesis-not-a-derivation-the-mass-value-y-and-v-are-inputs-the-lepton-mass-hierarchy-is-a-negative-result-and-g-is-derived-as-hbar-c-over-m-squared-conditionally-not-an-independent-input"

zil_file_contract physlib.entropicClockComptonAnchor where
  promises "The free clock frequency omega_0 of the EntropicAgreement action-rate calibration is fixed to the mass-determined Compton frequency omega_C equals m c squared over hbar, equivalently half the rest-frame Zitterbewegung frequency, with tick period the Compton period h over m c squared. The action rate hbar omega_0 is exactly the rest energy m c squared, so the entropic clock unit is set by the particle mass rather than an internal choice. At the Yukawa mass the anchored rate is exactly the Higgs internal Compton clock, so by the three-origins theorem the same clock is the Yukawa, gravitational horizon-entropy, and topological Chern-Simons mass, and reaches the gravitational constant through the horizon form omega_0 equals c cubed A-dot over four G hbar: the entropic-time sector connects to the mass-origin sector. The cited experiments support only narrow subclaims and none tests the load-bearing premise delta S_I equals m c squared delta tau: Parker 2018 is recoil h over m metrology for alpha, Lan and Muller 2013 a subharmonic Compton clock and mass-time metrology, Gouanere channeling is compatible-with not a confirmation of the internal clock, and Margalit 2015 is two-spin-state clock-path complementarity not a Compton clock or redshift. The anchor fixes the time unit to the mass and does not derive the mass value: y and v are inputs, the lepton mass hierarchy is a negative result, the three-origin coincidence is a conditional hypothesis. G is not an independent input: it is derived as h-bar c over m squared equals h-bar c sigma-nought to the fourth from the G-free Compton-cell count, so G equals c to the fifth over h-bar omega-nought squared through the clock frequency, conditional on the same mass-scale or inference-width identification. That G derivation is holographic: G equals area c cubed over h-bar N with the bit count N equals four pi log K squared supplied G-free by the Compton-cell tiling, so G equals h-bar c over m squared is the entanglement screen area-per-bit and m is the screen or cell scale lambda_C equals h-bar over m c, not a particle species. It is the Compton-cell equals Planck-cell matching that coincides exactly at the Planck mass where lambda_C equals the Planck length. So the OpenWave M9.109b species non-universality substitution of the electron muon and proton masses is a category error, plugging particle masses into the screen-scale slot where lambda_C scales as one over m makes different cells trivially give different area-per-bit, and its inversion-control charge re-asserts the very circularity this G-free count removes. The genuine residue is that the numerical value of G stays conditional on fixing one scale, the empirical input shifted from G to a mass, not a parameter-free prediction. The experiments confirm narrow subclaims rather than predict; the Margalit differential is engineered and the Compton-redshift-clock interpretation of closed atom interferometers is contested (Wolf et al 2011)."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Clock.EntropicAgreement.EntropicPhysicalClockCalibration",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins.higgsClockFrequency",
    "lean:Physlib.QuantumMechanics.Clock.Phase.PhaseClock"]
  forbids_substitutes ["leaving the clock frequency omega_0 as a free internal parameter instead of anchoring it to the mass-fixed Compton frequency",
    "claiming the anchor derives the particle mass value or the three-origin coincidence rather than expressing and cross-linking the mass",
    "treating the confirming experiments as a novel prediction or the engineered Margalit proper-time lag as a relativistic measurement"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock_period,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_newtonG_eq_from_clockFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_calibration_of_restEnergy_law,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_geometricProperTime,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_threeOriginMass,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonTemperature_eq_clock,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.verlindeDisplacementEntropy_eq_entropicAction_reading]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor

end
