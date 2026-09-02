/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
meta import Zil

/-!
# The inverse-square law uniquely determines the holographic stack

Each theorem here is an **inverse/rigidity result**: given exact inverse-square
phenomenology as the hypothesis, the microscopic structure is uniquely reconstructed.
The input: a screen with an **arbitrary** bit-count profile `N : ℝ → ℝ` whose entropic
force satisfies `F(R)·R² = C` at every radius.  No power law and no holographic postulate
are supplied — but the inverse-square response itself *is* the hypothesis, and these
theorems reconstruct from it; they are not an independent microscopic origin of it.  The
entropic-force relation (with `verlindeDisplacementEntropy`) is likewise part of the
interface, and the standing caveat applies: tiling and entropic force remain physical
inputs.

* **The count profile is forced** (`inverseSquare_forces_holographicProfile`): there is
  **exactly one** coupling `G` — necessarily `C/(Mm)` — such that
  `N R = holographicBits (sphereArea R) G ℏ c` at *every* radius.  Verlinde's holographic
  area postulate, constant included, is the unique solution of inverse-square
  phenomenology.  (`newtonG_isolated` was the fixed-radius iff; this is the functional,
  `∃!`-quantified version with the count unconstrained a priori.)
* **Power laws collapse to the area law** (`powerLaw_bitScaling_inverseSquare_iff`): for
  `N(R) = σ·R^p` with *any real* `p`, inverse-square behaviour at two distinct radii
  already forces `p = 2` — full exponent rigidity, upgrading the library's `p ∈ {2, 3}`
  certificates.
* **The Compton–Fisher tiling pins the constant**
  (`comptonFisher_inverseSquare_unique_coupling`): the tiled screen realizes the
  phenomenology with `C = ħcσ₀⁴·Mm`, and any coupling whose holographic profile matches
  the tiling equals `ħcσ₀⁴`; `existsUnique_calibration` then pins the width uniquely at
  the Planck width.
* **The complex-EFE normalization is forced** (`einsteinCoupling_unique_from_poisson`):
  any `κ` whose dust source reproduces the Poisson limit at the derived `G` — at a single
  nonzero density — equals `8πG/c⁴`.  The `κ` at which
  `CompleteComplexEinsteinFieldEquation` runs (with the BCJ entropic split
  `m_I c² = S₁ + S₂` of `SuperoperatorComplexEinsteinBCJSector`) is the only value
  compatible with the screen's Newtonian limit, not a choice.
* **The AdS/CFT modulus is forced** (`existsUnique_d3CompactificationVolume`): exactly
  one compactification volume makes the D3-brane reduced Einstein coupling land on
  `8π(ħcσ₀⁴)/c⁴`.  The dictionary's modulus is *determined* by the Compton clock, not
  merely consistent with it.

`stack_from_inverseSquare` composes the chain: on the Compton–Fisher screen, the
inverse-square constant is `ħcσ₀⁴Mm`; the profile coupling, the calibration width, the
EFE normalization and the compactification volume are then each unique.  One assumed
law, four `∃!`/uniqueness statements downstream, no free parameter in between — rigidity
of the interface, with inertia, inverse-square phenomenology, screen-cell identification
and (in the Gaussian–Fisher branch) the inference mass as the explicit physical inputs.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling

/-! ## §A — the functional rigidity theorem -/

/-- **The inverse-square law forces the holographic count profile, with a unique
coupling.**  For an arbitrary nowhere-zero profile `N` with `F(R)·R² = C ≠ 0` at every
positive radius, there is exactly one coupling `G` — necessarily `C/(Mm)` — for which `N`
is the holographic count at every radius. -/
theorem inverseSquare_forces_holographicProfile
    (M c kB m ħ Δx C : ℝ) (N : ℝ → ℝ)
    (hM : M ≠ 0) (hm : m ≠ 0) (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hC : C ≠ 0) (hNz : ∀ R : ℝ, 0 < R → N R ≠ 0)
    (hIS : ∀ R : ℝ, 0 < R →
      verlindeEntropicForce (bitScreenTemperature M c (N R) kB)
          (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R ^ 2 = C) :
    ∃! G : ℝ, G ≠ 0 ∧ C = G * (M * m)
      ∧ ∀ R : ℝ, 0 < R → N R = holographicBits (sphereArea R) G ħ c := by
  have hMm : M * m ≠ 0 := mul_ne_zero hM hm
  have hG0 : C / (M * m) ≠ 0 := div_ne_zero hC hMm
  refine ⟨C / (M * m), ⟨hG0, by field_simp, fun R hR => ?_⟩, ?_⟩
  · -- the profile is the holographic count at G₀ = C/(Mm)
    have h := hIS R hR
    rw [entropicForce_bitForm M c (N R) kB m ħ Δx (hNz R hR) hkB hΔx] at h
    have hNR := hNz R hR
    -- h : 4πmMc³/(ħ·N R)·R² = C  ⇒  N R = 4πmMc³R²/(ħC)
    have hmain : 4 * Real.pi * m * M * c ^ 3 * R ^ 2 = C * (ħ * N R) := by
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hħ.ne' hNR)] at h
      linear_combination h
    have hprofile : N R = 4 * Real.pi * m * M * c ^ 3 * R ^ 2 / (ħ * C) := by
      rw [eq_div_iff (mul_ne_zero hħ.ne' hC)]
      linear_combination -hmain
    rw [hprofile]
    unfold holographicBits sphereArea
    rw [div_eq_div_iff (mul_ne_zero hħ.ne' hC)
      (mul_ne_zero (div_ne_zero hC hMm) hħ.ne')]
    field_simp
  · -- uniqueness: the Newton reading C = G·Mm pins G
    rintro G' ⟨hG', hCG, -⟩
    rw [hCG, mul_div_cancel_right₀ _ hMm]

/-- **The equivalence form of §A — a single biconditional.**  Given the entropic-force
interface, screen thermality, and a nowhere-zero profile, the response is exactly
inverse-square with strength `C` at every positive radius if and only if the profile is
the holographic area count at the single coupling `G = C/(M·m)`.  Neither side is
established by the equivalence: the inverse-square phenomenology and the interface
remain the premises. -/
lemma holographicProfile_iff_inverseSquare
    (M c kB m ħ Δx C : ℝ) (N : ℝ → ℝ)
    (hM : M ≠ 0) (hm : m ≠ 0) (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hC : C ≠ 0) (hNz : ∀ R : ℝ, 0 < R → N R ≠ 0) :
    (∀ R : ℝ, 0 < R →
        verlindeEntropicForce (bitScreenTemperature M c (N R) kB)
            (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R ^ 2 = C) ↔
      ∀ R : ℝ, 0 < R → N R = holographicBits (sphereArea R) (C / (M * m)) ħ c := by
  have hMm : M * m ≠ 0 := mul_ne_zero hM hm
  constructor
  · intro hIS
    obtain ⟨G, ⟨-, hCG, hprof⟩, -⟩ :=
      inverseSquare_forces_holographicProfile M c kB m ħ Δx C N
        hM hm hc hħ hkB hΔx hC hNz hIS
    have hGval : G = C / (M * m) := by
      rw [hCG, mul_div_cancel_right₀ _ hMm]
    exact fun R hR => hGval ▸ hprof R hR
  · intro hprof R hR
    have hR0 : R ≠ 0 := hR.ne'
    have hG0 : C / (M * m) ≠ 0 := div_ne_zero hC hMm
    have hc0 : c ≠ 0 := hc.ne'
    have hħ0 : ħ ≠ 0 := hħ.ne'
    rw [entropicForce_bitForm M c (N R) kB m ħ Δx (hNz R hR) hkB hΔx, hprof R hR]
    unfold holographicBits sphereArea
    field_simp

/-! ## §B — exponent rigidity: power laws collapse to the area law -/

private lemma force_powerLaw_form (M c kB m ħ Δx σ p R : ℝ)
    (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hσ : 0 < σ) (hR : 0 < R) :
    verlindeEntropicForce (bitScreenTemperature M c (σ * R ^ p) kB)
        (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R ^ 2
      = (4 * Real.pi * m * M * c ^ 3 / (ħ * σ)) * R ^ ((2 : ℝ) - p) := by
  have hN : σ * R ^ p ≠ 0 := (mul_pos hσ (Real.rpow_pos_of_pos hR p)).ne'
  rw [entropicForce_bitForm M c _ kB m ħ Δx hN hkB hΔx, Real.rpow_sub hR]
  have h2 : R ^ ((2 : ℝ)) = R ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast R 2]
    norm_num
  rw [h2]
  have hRp : R ^ p ≠ 0 := (Real.rpow_pos_of_pos hR p).ne'
  field_simp

/-- **Exponent rigidity**: a power-law bit scaling `N(R) = σ·R^p` (any real `p`) gives
inverse-square behaviour at two distinct radii iff `p = 2`. -/
theorem powerLaw_bitScaling_inverseSquare_iff
    (M c kB m ħ Δx σ p R₁ R₂ : ℝ)
    (hM : M ≠ 0) (hm : m ≠ 0) (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hσ : 0 < σ) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂) :
    (verlindeEntropicForce (bitScreenTemperature M c (σ * R₁ ^ p) kB)
        (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R₁ ^ 2
      = verlindeEntropicForce (bitScreenTemperature M c (σ * R₂ ^ p) kB)
        (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R₂ ^ 2)
      ↔ p = 2 := by
  rw [force_powerLaw_form M c kB m ħ Δx σ p R₁ hc hħ hkB hΔx hσ hR₁,
    force_powerLaw_form M c kB m ħ Δx σ p R₂ hc hħ hkB hΔx hσ hR₂]
  have hK : 4 * Real.pi * m * M * c ^ 3 / (ħ * σ) ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hm) hM) (pow_ne_zero 3 hc.ne'))
      (mul_ne_zero hħ.ne' hσ.ne')
  constructor
  · intro h
    have hpow : R₁ ^ ((2 : ℝ) - p) = R₂ ^ ((2 : ℝ) - p) := mul_left_cancel₀ hK h
    have hlog := congrArg Real.log hpow
    rw [Real.log_rpow hR₁, Real.log_rpow hR₂] at hlog
    have hlogne : Real.log R₁ ≠ Real.log R₂ := fun hEq =>
      hne (Real.log_injOn_pos (Set.mem_Ioi.mpr hR₁) (Set.mem_Ioi.mpr hR₂) hEq)
    by_contra hp
    have hq : (2 : ℝ) - p ≠ 0 := fun h0 => hp (by linarith)
    exact hlogne (mul_left_cancel₀ hq hlog)
  · rintro rfl
    simp [Real.rpow_zero]

/-! ## §C — the Compton–Fisher screen realizes the phenomenology and pins the constant -/

/-- **The tiled screen's inverse-square constant is `ħcσ₀⁴·Mm`, and the coupling is
unique**: any `G'` whose holographic profile matches the Compton–Fisher tiling at one
radius equals `ħcσ₀⁴`. -/
theorem comptonFisher_inverseSquare_unique_coupling
    (σ₀ M c kB m ħ Δx : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hm : m ≠ 0) (hM : M ≠ 0) :
    (∀ R : ℝ, 0 < R →
      verlindeEntropicForce
          (bitScreenTemperature M c (comptonBitDensity σ₀ c ħ * sphereArea R) kB)
          (verlindeDisplacementEntropy ħ kB m c Δx) Δx * R ^ 2
        = (ħ * c * σ₀ ^ 4) * (M * m))
    ∧ (∀ G' R : ℝ, G' ≠ 0 → R ≠ 0 →
        comptonBitDensity σ₀ c ħ * sphereArea R = holographicBits (sphereArea R) G' ħ c
        → G' = ħ * c * σ₀ ^ 4) := by
  constructor
  · intro R hR
    rw [tiledScreen_gravitationalResponse σ₀ M c kB m ħ Δx R
      hσ.ne' hc.ne' hħ.ne' hkB hΔx hm hM hR.ne',
      div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')]
    ring
  · intro G' R hG' hR h
    exact ((identification_iff_tilings_agree hσ.ne' hħ.ne' hc.ne' hG' hR).mpr h).symm

/-- **The triangle closes: counted micro-data predict the laboratory response.**  The
same independently counted screen data `(A, N)` that force the unique coupling
(`GFreeComptonCellCalibration.existsUnique_countedNewtonG`) predict the tiled screen's
Newton-form force law *with that counted coupling* — the microscopic count, the
constructed `ħcσ₀⁴`, and the operational response are one constant measured three ways. -/
theorem countedData_forces_response
    (C : Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration)
    (M kB m Δx R : ℝ)
    (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) :
    verlindeEntropicForce
        (bitScreenTemperature M C.lightSpeed
          (comptonBitDensity C.inferenceWidth C.lightSpeed C.hbar * sphereArea R) kB)
        (verlindeDisplacementEntropy C.hbar kB m C.lightSpeed Δx) Δx
      = C.countedNewtonG * M * m / R ^ 2 := by
  rw [tiledScreen_gravitationalResponse C.inferenceWidth M C.lightSpeed kB m C.hbar Δx R
      C.inferenceWidth_pos.ne' C.lightSpeed_pos.ne' C.hbar_pos.ne' hkB hΔx hm hM hR,
    ← C.countedNewtonG_eq_hbar_c_mul_inferenceWidth_four]

/-! ## §D — the EFE normalization is forced by the Poisson limit -/

/-- **Uniqueness of the Einstein coupling from the Newtonian limit**: any `κ` whose dust
source `κ·(ρc²/2)` reproduces the Poisson source `4πGρ/c²` at a single nonzero density
equals `8πG/c⁴`.  The complex EFE's normalization is the only one compatible with the
screen-derived `G`. -/
theorem einsteinCoupling_unique_from_poisson {κ G c ρ : ℝ} (hρ : ρ ≠ 0) (hc : c ≠ 0)
    (h : κ * (ρ * c ^ 2 / 2) = 4 * Real.pi * G * ρ / c ^ 2) :
    κ = 8 * Real.pi * G / c ^ 4 := by
  rw [eq_div_iff (pow_ne_zero 4 hc)]
  have h2 : κ * (ρ * c ^ 2 / 2) * c ^ 2 = 4 * Real.pi * G * ρ := by
    rw [h, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]
  have h3 : ρ * (κ * c ^ 4) = ρ * (8 * Real.pi * G) := by linear_combination 2 * h2
  exact mul_left_cancel₀ hρ h3

/-! ## §E — the AdS/CFT modulus is forced -/

/-- **Uniqueness of the compactification volume**: exactly one `V` makes the D3-brane
reduced Einstein coupling equal the tiled screen's `8π(ħcσ₀⁴)/c⁴`.  The AdS/CFT
dictionary's modulus is determined by the Compton clock. -/
theorem existsUnique_d3CompactificationVolume
    (σ₀ c ħ R N : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hR : R ≠ 0) (hN : N ≠ 0) :
    ∃! V : ℝ, V ≠ 0
      ∧ d3ReducedEinsteinCoupling R N V c = 8 * Real.pi * (ħ * c * σ₀ ^ 4) / c ^ 4 := by
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hV0den : 2 * ħ * σ₀ ^ 4 * N ^ 2 * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hħ.ne')
      (pow_ne_zero 4 hσ.ne')) (pow_ne_zero 2 hN)) hc.ne'
  have hV0 : Real.pi * R ^ 3 / (2 * ħ * σ₀ ^ 4 * N ^ 2 * c) ≠ 0 :=
    div_ne_zero (mul_ne_zero hπ (pow_ne_zero 3 hR)) hV0den
  refine ⟨Real.pi * R ^ 3 / (2 * ħ * σ₀ ^ 4 * N ^ 2 * c), ⟨hV0, ?_⟩, ?_⟩
  · unfold d3ReducedEinsteinCoupling
    rw [div_eq_div_iff
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hN) hV0) (pow_ne_zero 4 hc.ne'))
      (pow_ne_zero 4 hc.ne')]
    field_simp
    ring
  · rintro V ⟨hV, hmatch⟩
    unfold d3ReducedEinsteinCoupling at hmatch
    have hVden : N ^ 2 * V * c ^ 4 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hN) hV) (pow_ne_zero 4 hc.ne')
    rw [div_eq_div_iff hVden (pow_ne_zero 4 hc.ne')] at hmatch
    rw [eq_div_iff hV0den]
    have hcancel : (4 * Real.pi * c ^ 4) * (V * (2 * ħ * σ₀ ^ 4 * N ^ 2 * c))
        = (4 * Real.pi * c ^ 4) * (Real.pi * R ^ 3) := by
      linear_combination -hmatch
    exact mul_left_cancel₀
      (mul_ne_zero (mul_ne_zero (by norm_num) hπ) (pow_ne_zero 4 hc.ne')) hcancel

/-! ## §F — the composed stack -/

/-- **From one law to four unique structures.**  On the Compton–Fisher screen: the
inverse-square constant is `ħcσ₀⁴Mm`; the holographic profile's coupling is unique
(`∃!`, equal to `ħcσ₀⁴`); the calibration width is unique; any Poisson-compatible EFE
normalization equals `8π(ħcσ₀⁴)/c⁴`; and the D3 compactification volume matching it is
unique. -/
theorem stack_from_inverseSquare
    (σ₀ M c kB m ħ Δx Rd Nd : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0)
    (hm : m ≠ 0) (hM : M ≠ 0) (hRd : Rd ≠ 0) (hNd : Nd ≠ 0) :
    (∃! G : ℝ, G ≠ 0 ∧ (ħ * c * σ₀ ^ 4) * (M * m) = G * (M * m)
      ∧ ∀ R : ℝ, 0 < R →
          comptonBitDensity σ₀ c ħ * sphereArea R = holographicBits (sphereArea R) G ħ c)
    ∧ (∃! σ : ℝ, 0 < σ ∧ ħ * c * σ ^ 4 = ħ * c * σ₀ ^ 4)
    ∧ (∀ κ ρ : ℝ, ρ ≠ 0 →
        κ * (ρ * c ^ 2 / 2) = 4 * Real.pi * (ħ * c * σ₀ ^ 4) * ρ / c ^ 2
        → κ = 8 * Real.pi * (ħ * c * σ₀ ^ 4) / c ^ 4)
    ∧ (∃! V : ℝ, V ≠ 0
        ∧ d3ReducedEinsteinCoupling Rd Nd V c = 8 * Real.pi * (ħ * c * σ₀ ^ 4) / c ^ 4) := by
  have hC : (ħ * c * σ₀ ^ 4) * (M * m) ≠ 0 :=
    mul_ne_zero (by positivity) (mul_ne_zero hM hm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hIS := (comptonFisher_inverseSquare_unique_coupling σ₀ M c kB m ħ Δx
      hσ hc hħ hkB hΔx hm hM).1
    have hNz : ∀ R : ℝ, 0 < R → comptonBitDensity σ₀ c ħ * sphereArea R ≠ 0 := fun R hR =>
      mul_ne_zero (comptonBitDensity_ne_zero hσ.ne' hc.ne' hħ.ne') (sphereArea_ne_zero hR.ne')
    exact inverseSquare_forces_holographicProfile M c kB m ħ Δx
      ((ħ * c * σ₀ ^ 4) * (M * m)) (fun R => comptonBitDensity σ₀ c ħ * sphereArea R)
      hM hm hc hħ hkB hΔx hC hNz hIS
  · exact existsUnique_calibration (by positivity) hħ hc
  · exact fun κ ρ hρ h => einsteinCoupling_unique_from_poisson hρ hc.ne' h
  · exact existsUnique_d3CompactificationVolume σ₀ c ħ Rd Nd hσ hc hħ hRd hNd

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling

zil attach inverseSquare_forces_holographicProfile where
  formalizes @ "claim:the-inverse-square-law-on-an-arbitrary-bit-count-profile-forces-the-\
full-holographic-area-count-with-exactly-one-coupling-c-over-m-m-verlinde-holography-is-\
the-unique-solution-of-inverse-square-phenomenology",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.entropicForce_bitForm",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated",
  caveat @ "claim:this-is-an-inverse-rigidity-theorem-conditional-on-the-exact-raw-\
inverse-square-response-at-every-positive-radius-not-an-independent-microscopic-origin-\
of-that-response"

zil attach holographicProfile_iff_inverseSquare where
  formalizes @ "claim:given-the-entropic-force-interface-and-screen-thermality-a-nowhere-\
zero-bit-profile-yields-the-exact-inverse-square-response-of-strength-c-if-and-only-if-\
it-is-the-holographic-area-count-at-the-single-coupling-c-over-m-m-neither-side-is-\
established-by-the-equivalence",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.entropicForce_bitForm",
  caveat @ "claim:this-is-an-inverse-rigidity-theorem-conditional-on-the-exact-raw-\
inverse-square-response-at-every-positive-radius-not-an-independent-microscopic-origin-\
of-that-response"

zil attach powerLaw_bitScaling_inverseSquare_iff where
  formalizes @ "claim:area-scaling-is-the-unique-real-power-law-bit-scaling-compatible-\
with-the-inverse-square-law-the-holographic-exponent-is-forced-not-chosen",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.volumeScaling_not_inverseSquare"

zil attach countedData_forces_response where
  formalizes @ "claim:the-same-independently-counted-screen-data-that-force-the-unique-\
coupling-predict-the-tiled-screens-newton-form-response-at-that-counted-coupling-one-\
constant-measured-three-ways",
  epistemic_status @ "consistency-identity",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.existsUnique_countedNewtonG"

zil attach einsteinCoupling_unique_from_poisson where
  formalizes @ "claim:any-einstein-coupling-whose-dust-source-reproduces-the-poisson-\
limit-at-one-nonzero-density-equals-eight-pi-g-over-c-fourth-the-complex-efe-\
normalization-is-forced-by-the-newtonian-limit",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.newtonG_establishes_gravitationalSystem"

zil attach existsUnique_d3CompactificationVolume where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  formalizes @ "claim:exactly-one-compactification-volume-makes-the-d3-brane-reduced-\
einstein-coupling-equal-the-tiled-screens-eight-pi-hbar-c-sigma-zero-fourth-over-c-\
fourth-the-ads-cft-modulus-is-determined-by-the-compton-clock",
  epistemic_status @ "consistency-identity",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary"

zil attach stack_from_inverseSquare where
  formalizes @ "claim:on-the-compton-fisher-screen-one-inverse-square-law-uniquely-\
determines-the-holographic-profile-coupling-the-planck-calibration-width-the-complex-efe-\
normalization-with-the-bcj-entropic-split-and-the-d3-compactification-volume",
  epistemic_status @ "consistency-identity",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_calibration",
  caveat @ "claim:the-uniqueness-chain-is-internal-to-the-tiled-screen-formalism-the-\
tiling-and-entropic-force-premises-remain-the-physical-input"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling
