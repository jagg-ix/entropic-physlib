/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant
public import Mathlib.Tactic.FieldSimp
meta import Zil

/-!
# Breaking the holographic-`G` circularity: the `G`-free Compton-cell bit count

The entropic-dynamics thesis identifies `G = 𝒜c³/(ℏN)` (thesis pillar IV,
`EntropicTime.EntropicMassGravitationalConstant.entropic_gravity_system`) only *conditional* on
`N = holographicBits(𝒜, G, ℏ, c) = 𝒜c³/(Gℏ)` — the Verlinde count, which measures the screen area in
**Planck cells** `ℓ_P² = Gℏ/c³` and therefore already contains `G`. Solving for `G` is then circular:
`N` was built from the very `G` it returns.

This file supplies the bit count from a **`G`-free** source instead. The entanglement screen has area
`𝒜 = 4π λ_C²(log K)²` (`EntanglementScreenArea.entanglementScreenArea`), which is manifestly free of `G`.
Tiling it by **Compton cells** `λ_C²` rather than Planck cells gives

  `comptonCellBits = 𝒜 / λ_C² = 4π (log K)²`   (`comptonCellBits_eq`, no `G`),

and feeding *that* into the area-per-bit formula returns

  `G = 𝒜c³/(ℏ · comptonCellBits) = ℏc/m²`   (`newtonG_from_comptonCellBits`).

The Gaussian-Fisher capstone `gaussianFisherScreenCoupling_eq` removes two
mathematical abbreviations from this chain. It uses the proved score integral
`I = ∫(∂μ log p)²p = 1/σ₀²` rather than assuming `m = 1/σ₀²`, and it
characterizes the effective cell count by the unique area balance `N λ² = A`.
Consequently the coupling constructed from the Gaussian experiment and the
normalized screen area is exactly `ℏcσ₀⁴`.

So Newton's constant comes out as `ℏc/m²` — a function of the **mass scale `m`** alone, with no `G` on the
right — rather than being read back off a count that already contained it. Equivalently the Planck-cell
(holographic) count equals the Compton-cell count **exactly when** `G = ℏc/m²`
(`holographicBits_eq_comptonCellBits_iff`): the two tilings coincide precisely at the Planck-mass
identification, which is now the *content* of the statement, not an input.

**Honest layering.** This does not conjure the numerical value of measured `G`
from nothing. The direct branch replaces the circular premise `N = 𝒜c³/(Gℏ)` by
an independent mass scale `m` represented by the inference layer's
inverse-square-root-mass coordinate
`EntropicMassGravitationalConstant.inferenceMass`. Once `N` is supplied `G`-free as the
Compton tiling, `G = ℏc/m²` follows as an exact identity. The inverse calibration branch instead takes an
independently measured area and cell count and fixes `m` by the physical identification
`√(A/N) = λ_C(m)`. Thus the definitional `G`-circularity is removed, but empirical input remains: either the
mass, or independent `A/N` plus the Compton-cell identification.

The exact theorem therefore separates two statements that must not be
conflated: construction of the information-theoretic screen coupling uses only
the supplied positive Gaussian and conversion coordinates, while identifying that
constructed coupling with the Newton constant measured in gravitational
experiments remains a physical claim about the model.

The same non-circular count also closes the Bekenstein–Caticha clock chain:
`comptonCell_bekensteinCaticha_clock_from_entropicAction` instantiates the Bekenstein screen entropy,
area-per-cell coupling, Caticha inference mass, and the entropic-action clock without taking
`N = holographicBits(..., G, ...)` as an independent premise.

## References

* T. Padmanabhan; E. Verlinde — entropic gravity / area per bit. A. Caticha, C. Cafaro — information → mass → `G`.
* J. D. Bekenstein, *Black-hole thermodynamics*, Physics Today **33** (1980) 24–31.
  Companions: `ComptonClock.EntanglementScreenArea` (the `G`-free screen area `4π λ_C²(log K)²` and the
  Planck-cell count), `Thermodynamics.VerlindeNewtonGravity` (`sphereArea`, `holographicBits`),
  `EntropicTime.EntropicMassGravitationalConstant` (thesis pillar IV — the circular `entropic_gravity_system`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.Relativity.SemiClassical
open Dimension.LTMCTI
open Physlib.Units.GravitationalCouplingDimensions
open Physlib.Units.InformationDimensionCollision
open Physlib.Units.PlanckUnitsInformation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

/-- The **`G`-free Compton-cell bit count** of the entanglement screen: its area `𝒜 = 4π λ_C²(log K)²`
divided by the Compton cell `λ_C²`, not the `G`-dependent Planck cell `ℓ_P² = Gℏ/c³`. -/
noncomputable def comptonCellBits (m c ħ η : ℝ) : ℝ :=
  sphereArea (entropicProperDistance m c ħ η) / comptonWavelength m c ħ ^ 2

/-- **[The Compton-cell bit count is `G`-free]** `comptonCellBits = 4π (log K)²` — the squared entanglement
nats, with no appearance of Newton's constant. -/
theorem comptonCellBits_eq (m c ħ η : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonCellBits m c ħ η = 4 * Real.pi * Real.log (schmidtNumber η) ^ 2 := by
  have hcw : comptonWavelength m c ħ ≠ 0 := by
    unfold comptonWavelength; exact div_ne_zero hħ (mul_ne_zero hm hc)
  unfold comptonCellBits
  rw [entanglementScreenArea,
      show (4 : ℝ) * Real.pi * comptonWavelength m c ħ ^ 2 * Real.log (schmidtNumber η) ^ 2
        = (4 * Real.pi * Real.log (schmidtNumber η) ^ 2) * comptonWavelength m c ħ ^ 2 by ring,
      mul_div_assoc, div_self (pow_ne_zero 2 hcw), mul_one]

/-- The `G`-free Compton-cell count is positive for positive mass, conversion constants, and
Schmidt rapidity. -/
lemma comptonCellBits_pos (m c ħ η : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    0 < comptonCellBits m c ħ η := by
  rw [comptonCellBits_eq m c ħ η hm.ne' hc.ne' hħ.ne']
  have hlog : 0 < Real.log (schmidtNumber η) :=
    Real.log_pos (schmidtNumber_gt_one η hη)
  positivity

/-- **[The coupling induced by reduced-Compton-area normalization]**
`A c^3/(hbar * comptonCellBits) = hbar c/m^2`. Since `comptonCellBits = A/lambda_C^2`,
the whole area, including its entanglement and radius dependence, cancels. This is a `G`-free
normalized-area identity; identifying its output with measured Newton `G` is separate. -/
theorem newtonG_from_comptonCellBits (m c ħ η : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    sphereArea (entropicProperDistance m c ħ η) * c ^ 3 / (ħ * comptonCellBits m c ħ η)
      = ħ * c / m ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [entanglementScreenArea, comptonCellBits_eq m c ħ η hm hc hħ]
  unfold comptonWavelength
  field_simp
  try ring

/-- **[The screen coupling from the Gaussian inference width]** grounding the
scale in the inference layer
`m = inferenceMass σ₀ = 1/σ₀²`, the `G`-free effective Compton-cell construction becomes
`ℏc·σ₀⁴`. Here `σ₀` is the inference coordinate with inverse-square-root-mass dimension,
not an SI spatial standard deviation; the spatial conversion is formalized below. -/
theorem newtonG_from_positionVariance (σ₀ c ħ η : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
        / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)
      = ħ * c * σ₀ ^ 4 := by
  have hm : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]; exact inv_ne_zero (pow_ne_zero 2 hσ)
  rw [newtonG_from_comptonCellBits (inferenceMass σ₀) c ħ η hm hc hħ hK, inferenceMass]
  field_simp
  try ring

/-! ## The constructed Gaussian-Fisher screen coupling -/

/-- The inference mass is not merely the reciprocal-variance definition: for a
nondegenerate Gaussian location family it is the integral of the squared
log-density score. -/
lemma inferenceMass_eq_gaussianMeanFisherInformation (σ₀ : ℝ) (hσ : σ₀ ≠ 0) :
    inferenceMass σ₀ =
      gaussianMeanFisherInformation 0 (σ₀ ^ 2).toNNReal := by
  rw [mass_is_fisherRao_metric,
    gMuMu_eq_gaussianMeanFisherInformation σ₀ hσ]

/-- The effective Compton-cell count satisfies the exact area balance: count
times cell area equals screen area. This characterizes the count as a
normalized area, without supplying a global bit-density certificate. -/
lemma comptonCellBits_mul_cellArea (m c ħ η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonCellBits m c ħ η * comptonWavelength m c ħ ^ 2 =
      sphereArea (entropicProperDistance m c ħ η) := by
  have hcell : comptonWavelength m c ħ ^ 2 ≠ 0 := by
    unfold comptonWavelength
    exact pow_ne_zero 2 (div_ne_zero hħ (mul_ne_zero hm hc))
  unfold comptonCellBits
  exact div_mul_cancel₀ _ hcell

/-- The area balance uniquely determines the effective Compton-cell count.
Thus `comptonCellBits` is the constructed normalized screen area, rather than
an independently supplied count. -/
lemma eq_comptonCellBits_of_mul_cellArea_eq {N m c ħ η : ℝ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (harea : N * comptonWavelength m c ħ ^ 2 =
      sphereArea (entropicProperDistance m c ħ η)) :
    N = comptonCellBits m c ħ η := by
  have hcell : comptonWavelength m c ħ ^ 2 ≠ 0 := by
    unfold comptonWavelength
    exact pow_ne_zero 2 (div_ne_zero hħ (mul_ne_zero hm hc))
  rw [← comptonCellBits_mul_cellArea m c ħ η hm hc hħ] at harea
  exact mul_right_cancel₀ hcell harea

/-! # A. Finite operational Compton tilings -/

/-- A finite screen tiling by reduced-Compton-area cells.

Unlike `comptonCellBits`, whose value is an effective real area ratio, this carrier contains
an actual natural-number count. Its area equation is the explicit physical/discretization
premise needed to identify that count with the normalized screen area. -/
structure FiniteComptonScreenTiling (m c ħ A : ℝ) where
  /-- The number of resolved cells in the finite screen partition. -/
  cellCount : ℕ
  /-- The finite partition contains at least one cell. -/
  cellCount_pos : 0 < cellCount
  /-- The measured screen area is the finite count times one reduced-Compton cell area. -/
  area_eq_count_mul_cellArea :
    A = (cellCount : ℝ) * comptonWavelength m c ħ ^ 2

namespace FiniteComptonScreenTiling

/-- The finite type labelling the cells of an operational Compton tiling. -/
abbrev Cell {m c ħ A : ℝ} (T : FiniteComptonScreenTiling m c ħ A) : Type := Fin T.cellCount

/-- Boolean occupation data for every resolved cell in a finite Compton tiling. -/
abbrev CellRegister {m c ħ A : ℝ} (T : FiniteComptonScreenTiling m c ħ A) : Type :=
  T.Cell → Bool

/-- The label type has exactly the independently supplied natural-number cell count. -/
lemma cell_card {m c ħ A : ℝ} (T : FiniteComptonScreenTiling m c ħ A) :
    Fintype.card T.Cell = T.cellCount := by
  simp [Cell]

/-- A tiling with `n` Boolean cells has exactly `2^n` microscopic register states. -/
lemma cellRegister_card {m c ħ A : ℝ} (T : FiniteComptonScreenTiling m c ħ A) :
    Fintype.card T.CellRegister = 2 ^ T.cellCount := by
  rw [Fintype.card_fun, Fintype.card_bool, T.cell_card]

/-- Exact finite tiling turns the effective real normalized area into the cast of the
natural-number operational count. -/
lemma normalizedArea_eq_count {m c ħ A : ℝ} (T : FiniteComptonScreenTiling m c ħ A)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    A / comptonWavelength m c ħ ^ 2 = (T.cellCount : ℝ) := by
  have hcell : comptonWavelength m c ħ ^ 2 ≠ 0 := by
    unfold comptonWavelength
    exact pow_ne_zero 2 (div_ne_zero hħ (mul_ne_zero hm hc))
  calc
    A / comptonWavelength m c ħ ^ 2 =
        ((T.cellCount : ℝ) * comptonWavelength m c ħ ^ 2) /
          comptonWavelength m c ħ ^ 2 :=
      congrArg (fun area => area / comptonWavelength m c ħ ^ 2)
        T.area_eq_count_mul_cellArea
    _ = (T.cellCount : ℝ) := mul_div_cancel_right₀ (T.cellCount : ℝ) hcell

/-- For an exactly tiled entanglement screen, `comptonCellBits` is an actual finite
cardinality rather than only an effective real area ratio. -/
lemma comptonCellBits_eq_count {m c ħ η : ℝ}
    (T : FiniteComptonScreenTiling m c ħ
      (sphereArea (entropicProperDistance m c ħ η)))
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonCellBits m c ħ η = (T.cellCount : ℝ) := by
  unfold comptonCellBits
  exact T.normalizedArea_eq_count hm hc hħ

/-- Existence of an exact finite tiling imposes the missing quantization condition:
`4π(log K)^2` must be the cast of a natural number. -/
lemma entropicArea_quantized {m c ħ η : ℝ}
    (T : FiniteComptonScreenTiling m c ħ
      (sphereArea (entropicProperDistance m c ħ η)))
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    (T.cellCount : ℝ) = 4 * Real.pi * Real.log (schmidtNumber η) ^ 2 := by
  rw [← T.comptonCellBits_eq_count hm hc hħ,
    comptonCellBits_eq m c ħ η hm hc hħ]

end FiniteComptonScreenTiling

/-- The coupling constructed directly from the genuine Gaussian Fisher
information and its normalized screen area. No Newton constant, physical mass,
or independently supplied cell count occurs in the definition. -/
noncomputable def gaussianFisherScreenCoupling (σ₀ c ħ η : ℝ) : ℝ :=
  let I := gaussianMeanFisherInformation 0 (σ₀ ^ 2).toNNReal
  sphereArea (entropicProperDistance I c ħ η) * c ^ 3 /
    (ħ * comptonCellBits I c ħ η)

/-- **Gaussian-Fisher construction of the quartic coupling.** For positive
Gaussian width, light speed, action scale, and Schmidt rapidity, the actual
score integral constructs the precision `I = 1/σ₀²`; the unique normalized
Compton-cell count obeys `N λ² = A`; and the resulting screen coupling is
exactly `ħ c σ₀⁴`.

This theorem removes the two mathematical placeholders from the chain. It
constructs an information-theoretic coupling; identifying that constructed
quantity with the empirically measured Newton constant is a separate physical
claim. -/
@[zil_level physical_theorem]
lemma gaussianFisherScreenCoupling_eq (σ₀ c ħ η : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    let I := gaussianMeanFisherInformation 0 (σ₀ ^ 2).toNNReal
    gaussianFisherScreenCoupling σ₀ c ħ η = ħ * c * σ₀ ^ 4
      ∧ I = 1 / σ₀ ^ 2
      ∧ comptonCellBits I c ħ η * comptonWavelength I c ħ ^ 2 =
          sphereArea (entropicProperDistance I c ħ η) := by
  dsimp only [gaussianFisherScreenCoupling]
  have hI : inferenceMass σ₀ =
      gaussianMeanFisherInformation 0 (σ₀ ^ 2).toNNReal :=
    inferenceMass_eq_gaussianMeanFisherInformation σ₀ hσ.ne'
  have hm : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]
    exact inv_ne_zero (pow_ne_zero 2 hσ.ne')
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  rw [← hI]
  exact ⟨newtonG_from_positionVariance σ₀ c ħ η hσ.ne' hc.ne' hħ.ne' hlog,
    inferenceMass_eq σ₀,
    comptonCellBits_mul_cellArea (inferenceMass σ₀) c ħ η
      hm hc.ne' hħ.ne'⟩

/-! ## Fixing the mass and inference width from an independent cell count -/

/-- Positive data for a screen whose area and Compton-cell count are supplied
without using Newton's constant.

The physical premise is that `cellCount` is an independently counted number of
equal Compton cells covering `screenArea`.  All four scale inputs are positive;
there is deliberately no `G` field. -/
structure GFreeComptonCellCalibration where
  /-- Independently supplied screen area. -/
  screenArea : ℝ
  /-- Independently supplied number of Compton cells. -/
  cellCount : ℝ
  /-- Speed of light used in the Compton relation. -/
  lightSpeed : ℝ
  /-- Reduced Planck constant used in the Compton relation. -/
  hbar : ℝ
  /-- Positivity of screen area. -/
  screenArea_pos : 0 < screenArea
  /-- Positivity of cell count. -/
  cellCount_pos : 0 < cellCount
  /-- Positivity of light speed. -/
  lightSpeed_pos : 0 < lightSpeed
  /-- Positivity of the reduced Planck constant. -/
  hbar_pos : 0 < hbar

namespace GFreeComptonCellCalibration

/-- The measured area of one counted cell, `A/N`, with no `G` input. -/
noncomputable def cellArea (C : GFreeComptonCellCalibration) : ℝ :=
  C.screenArea / C.cellCount

/-- The independently counted cell area is positive. -/
theorem cellArea_pos (C : GFreeComptonCellCalibration) : 0 < C.cellArea :=
  div_pos C.screenArea_pos C.cellCount_pos

/-- The screen mass fixed by treating `√(A/N)` as its Compton wavelength:
`m_scr = ℏ/(c √(A/N))`.

Unlike `√(ℏc/G)`, this definition contains no Newton constant. -/
noncomputable def screenMass (C : GFreeComptonCellCalibration) : ℝ :=
  C.hbar / (C.lightSpeed * Real.sqrt C.cellArea)

/-- The mass fixed by the positive G-free calibration is positive. -/
theorem screenMass_pos (C : GFreeComptonCellCalibration) : 0 < C.screenMass := by
  exact div_pos C.hbar_pos
    (mul_pos C.lightSpeed_pos (Real.sqrt_pos.2 C.cellArea_pos))

/-- The Caticha inference width fixed by the counted screen mass:
`σ₀ = 1/√m_scr`, so that `m_scr = 1/σ₀²`. -/
noncomputable def inferenceWidth (C : GFreeComptonCellCalibration) : ℝ :=
  1 / Real.sqrt C.screenMass

/-- The calibrated inference width is positive. -/
theorem inferenceWidth_pos (C : GFreeComptonCellCalibration) :
    0 < C.inferenceWidth := by
  exact one_div_pos.2 (Real.sqrt_pos.2 C.screenMass_pos)

/-- Newton's coupling obtained from the independently counted area per cell. -/
noncomputable def countedNewtonG (C : GFreeComptonCellCalibration) : ℝ :=
  C.screenArea * C.lightSpeed ^ 3 / (C.hbar * C.cellCount)

/-- The positive length selected by the counted cell area.  The Planck closure
below proves that it is simultaneously the calibrated reduced Compton
wavelength and the Planck length associated with `countedNewtonG`. -/
noncomputable def countedPlanckLength (C : GFreeComptonCellCalibration) : ℝ :=
  Real.sqrt C.cellArea

/-- The time light needs to cross one calibrated cell length. -/
noncomputable def countedPlanckTime (C : GFreeComptonCellCalibration) : ℝ :=
  C.countedPlanckLength / C.lightSpeed

/-- The independently counted cell area is exactly the Planck-area
combination `G_count ℏ/c³` of the derived coupling. -/
theorem cellArea_eq_countedPlanckArea (C : GFreeComptonCellCalibration) :
    C.cellArea = C.countedNewtonG * C.hbar / C.lightSpeed ^ 3 := by
  unfold cellArea countedNewtonG
  field_simp [C.cellCount_pos.ne', C.hbar_pos.ne', C.lightSpeed_pos.ne']

/-- The calibrated length satisfies the standard Planck-length equation
`ℓ_P² = G_count ℏ/c³`. -/
theorem countedPlanckLength_sq_eq (C : GFreeComptonCellCalibration) :
    C.countedPlanckLength ^ 2 =
      C.countedNewtonG * C.hbar / C.lightSpeed ^ 3 := by
  unfold countedPlanckLength
  rw [Real.sq_sqrt C.cellArea_pos.le, C.cellArea_eq_countedPlanckArea]

/-- The calibrated crossing time satisfies the standard Planck-time equation
`t_P² = G_count ℏ/c⁵`. -/
theorem countedPlanckTime_sq_eq (C : GFreeComptonCellCalibration) :
    C.countedPlanckTime ^ 2 =
      C.countedNewtonG * C.hbar / C.lightSpeed ^ 5 := by
  unfold countedPlanckTime
  rw [div_pow, C.countedPlanckLength_sq_eq]
  field_simp [C.lightSpeed_pos.ne']

/-- The reduced Compton wavelength of the calibrated screen mass is the
positive square root of the independently counted cell area. -/
theorem comptonWavelength_screenMass_eq_countedPlanckLength
    (C : GFreeComptonCellCalibration) :
    comptonWavelength C.screenMass C.lightSpeed C.hbar =
      C.countedPlanckLength := by
  unfold comptonWavelength screenMass countedPlanckLength
  field_simp [C.hbar_pos.ne', C.lightSpeed_pos.ne',
    (Real.sqrt_pos.2 C.cellArea_pos).ne']

/-- The calibrated Caticha inference mass is exactly the calibrated screen
mass; the inference-width choice therefore fixes rather than merely labels the
mass scale. -/
theorem inferenceMass_inferenceWidth (C : GFreeComptonCellCalibration) :
    inferenceMass C.inferenceWidth = C.screenMass := by
  unfold inferenceMass inferenceWidth
  rw [one_div, inv_pow, inv_inv, Real.sq_sqrt C.screenMass_pos.le]

/-- **The non-circular counted-cell coupling.**  Independent `A` and `N` fix
`m_scr = ℏ/(c√(A/N))`, and their area-per-cell coupling consequently satisfies
`G_count = ℏc/m_scr²`.

No occurrence of `G` appears among the calibration inputs. -/
theorem countedNewtonG_eq_hbar_c_div_screenMass_sq
    (C : GFreeComptonCellCalibration) :
    C.countedNewtonG = C.hbar * C.lightSpeed / C.screenMass ^ 2 := by
  unfold countedNewtonG screenMass cellArea
  have hsqrt : (Real.sqrt (C.screenArea / C.cellCount)) ^ 2 =
      C.screenArea / C.cellCount :=
    Real.sq_sqrt (div_nonneg C.screenArea_pos.le C.cellCount_pos.le)
  have hcross :
      C.cellCount * (Real.sqrt (C.screenArea / C.cellCount)) ^ 2 =
        C.screenArea := by
    rw [hsqrt]
    field_simp [C.cellCount_pos.ne']
  field_simp [C.screenArea_pos.ne', C.cellCount_pos.ne',
    C.lightSpeed_pos.ne', C.hbar_pos.ne',
    (Real.sqrt_pos.2 (div_pos C.screenArea_pos C.cellCount_pos)).ne']
  nlinarith [hcross]

/-- **The same non-circular coupling in Caticha variables.**  With
`σ₀ = 1/√m_scr`, the independently counted coupling is
`G_count = ℏc σ₀⁴`. -/
theorem countedNewtonG_eq_hbar_c_mul_inferenceWidth_four
    (C : GFreeComptonCellCalibration) :
    C.countedNewtonG =
      C.hbar * C.lightSpeed * C.inferenceWidth ^ 4 := by
  rw [C.countedNewtonG_eq_hbar_c_div_screenMass_sq]
  unfold inferenceWidth
  rw [one_div, inv_pow]
  have hsqrt : (Real.sqrt C.screenMass) ^ 2 = C.screenMass :=
    Real.sq_sqrt C.screenMass_pos.le
  have hsqrt4 : (Real.sqrt C.screenMass) ^ 4 = C.screenMass ^ 2 := by
    nlinarith [hsqrt]
  field_simp [C.screenMass_pos.ne',
    (Real.sqrt_pos.2 C.screenMass_pos).ne']
  rw [hsqrt4]

/-- **Uniqueness of the counted coupling.**  If a candidate `G` makes the independently
counted cell area `A/N` equal to its Planck-area combination `Għ/c³`, then that candidate
is the `G`-free area-per-cell coupling `countedNewtonG`.  No measured Newton constant is an
input to the calibration data. -/
lemma candidateNewtonG_eq_countedNewtonG (C : GFreeComptonCellCalibration) {G : ℝ}
    (hplanck : C.cellArea = G * C.hbar / C.lightSpeed ^ 3) :
    G = C.countedNewtonG := by
  have hscale : C.hbar / C.lightSpeed ^ 3 ≠ 0 :=
    div_ne_zero C.hbar_pos.ne' (pow_ne_zero 3 C.lightSpeed_pos.ne')
  have hscaled : G * (C.hbar / C.lightSpeed ^ 3) =
      C.countedNewtonG * (C.hbar / C.lightSpeed ^ 3) := by
    calc
      G * (C.hbar / C.lightSpeed ^ 3) = C.cellArea := by
        rw [hplanck]
        ring
      _ = C.countedNewtonG * (C.hbar / C.lightSpeed ^ 3) := by
        rw [C.cellArea_eq_countedPlanckArea]
        ring
  exact mul_right_cancel₀ hscale hscaled

/-- Any coupling compatible with the independently counted Planck-area relation is forced
to be `ħcσ₀⁴`, where `σ₀` is itself fixed from the same `G`-free cell data. -/
lemma candidateNewtonG_eq_hbar_c_mul_inferenceWidth_four
    (C : GFreeComptonCellCalibration) {G : ℝ}
    (hplanck : C.cellArea = G * C.hbar / C.lightSpeed ^ 3) :
    G = C.hbar * C.lightSpeed * C.inferenceWidth ^ 4 :=
  (C.candidateNewtonG_eq_countedNewtonG hplanck).trans
    C.countedNewtonG_eq_hbar_c_mul_inferenceWidth_four

/-- The independently counted cell data admit exactly one coupling satisfying the
Planck-area relation.  Its witness is the constructed `countedNewtonG`, subsequently
identified with `ħcσ₀⁴` by `countedNewtonG_eq_hbar_c_mul_inferenceWidth_four`. -/
lemma existsUnique_countedNewtonG (C : GFreeComptonCellCalibration) :
    ∃! G : ℝ, C.cellArea = G * C.hbar / C.lightSpeed ^ 3 :=
  ⟨C.countedNewtonG, C.cellArea_eq_countedPlanckArea,
    fun _ hplanck => C.candidateNewtonG_eq_countedNewtonG hplanck⟩

/-- The squared Planck mass of the counted coupling is exactly the squared
screen mass.  Positivity of `screenMass` therefore selects `screenMass` itself
as the positive Planck mass. -/
theorem planckMassSq_countedNewtonG (C : GFreeComptonCellCalibration) :
    planckMassSq C.countedNewtonG C.hbar C.lightSpeed = C.screenMass ^ 2 := by
  rw [C.countedNewtonG_eq_hbar_c_div_screenMass_sq]
  unfold planckMassSq
  field_simp [C.hbar_pos.ne', C.lightSpeed_pos.ne', C.screenMass_pos.ne']

/-- The counted Planck crossing time is the inverse Compton angular frequency
of the calibrated screen mass. -/
theorem countedPlanckTime_eq_inv_comptonFrequency
    (C : GFreeComptonCellCalibration) :
    C.countedPlanckTime =
      1 / comptonFrequency C.screenMass C.lightSpeed C.hbar := by
  unfold countedPlanckTime comptonFrequency
  rw [← C.comptonWavelength_screenMass_eq_countedPlanckLength]
  unfold comptonWavelength
  field_simp [C.hbar_pos.ne', C.lightSpeed_pos.ne', C.screenMass_pos.ne']

/-- The Planck energy selected by the counted mass is the quantum of its
Compton/Planck clock, `m_scr c² = ℏω_C`. -/
theorem screenMass_energy_eq_hbar_mul_comptonFrequency
    (C : GFreeComptonCellCalibration) :
    C.screenMass * C.lightSpeed ^ 2 =
      C.hbar * comptonFrequency C.screenMass C.lightSpeed C.hbar := by
  unfold comptonFrequency
  field_simp [C.hbar_pos.ne']

/-- The complete calibrated identity requested by the G-free construction:
the count fixes `m_scr` and `σ₀`, these obey `m_scr = 1/σ₀²`, and both give the
same counted Newton coupling. -/
theorem fixes_screenMass_inferenceWidth_and_newtonG
    (C : GFreeComptonCellCalibration) :
    inferenceMass C.inferenceWidth = C.screenMass
      ∧ C.countedNewtonG = C.hbar * C.lightSpeed / C.screenMass ^ 2
      ∧ C.countedNewtonG =
          C.hbar * C.lightSpeed * C.inferenceWidth ^ 4 :=
  ⟨C.inferenceMass_inferenceWidth,
    C.countedNewtonG_eq_hbar_c_div_screenMass_sq,
    C.countedNewtonG_eq_hbar_c_mul_inferenceWidth_four⟩

/-- **The complete Planck/Compton closure of the G-free calibration.**  The
same independently counted cell is the derived Planck area, its positive
square root is the reduced Compton/Planck length, the screen mass is the
positive Planck mass, and its Compton clock is the Planck clock.

This is a conditional identification, not an independent prediction of a new
mass scale: the physical premise is that the independently observed cells are
Compton cells. -/
theorem countedCell_planckComptonClosure (C : GFreeComptonCellCalibration) :
    C.cellArea = C.countedNewtonG * C.hbar / C.lightSpeed ^ 3
      ∧ C.countedPlanckLength ^ 2 =
          C.countedNewtonG * C.hbar / C.lightSpeed ^ 3
      ∧ C.countedPlanckTime ^ 2 =
          C.countedNewtonG * C.hbar / C.lightSpeed ^ 5
      ∧ comptonWavelength C.screenMass C.lightSpeed C.hbar =
          C.countedPlanckLength
      ∧ planckMassSq C.countedNewtonG C.hbar C.lightSpeed = C.screenMass ^ 2
      ∧ C.countedPlanckTime =
          1 / comptonFrequency C.screenMass C.lightSpeed C.hbar
      ∧ C.screenMass * C.lightSpeed ^ 2 =
          C.hbar * comptonFrequency C.screenMass C.lightSpeed C.hbar :=
  ⟨C.cellArea_eq_countedPlanckArea,
    C.countedPlanckLength_sq_eq,
    C.countedPlanckTime_sq_eq,
    C.comptonWavelength_screenMass_eq_countedPlanckLength,
    C.planckMassSq_countedNewtonG,
    C.countedPlanckTime_eq_inv_comptonFrequency,
    C.screenMass_energy_eq_hbar_mul_comptonFrequency⟩

/-! ### Constructing the exact finite tiling from counted data -/

/-- The exact finite Compton tiling constructed by the inverse calibration.
If the positive real count of a `GFreeComptonCellCalibration` is the cast of a
positive natural number `n`, the calibrated screen mass makes one reduced
Compton cell have area `screenArea / n`; hence `n` such cells cover the screen
exactly. -/
noncomputable def finiteTilingOfNatCount
    (C : GFreeComptonCellCalibration) (n : ℕ) (hn : 0 < n)
    (hcount : (n : ℝ) = C.cellCount) :
    FiniteComptonScreenTiling C.screenMass C.lightSpeed C.hbar C.screenArea where
  cellCount := n
  cellCount_pos := hn
  area_eq_count_mul_cellArea := by
    have harea : C.screenArea = C.cellCount * C.cellArea := by
      unfold cellArea
      field_simp [C.cellCount_pos.ne']
    have hcell :
        comptonWavelength C.screenMass C.lightSpeed C.hbar ^ 2 = C.cellArea := by
      rw [C.comptonWavelength_screenMass_eq_countedPlanckLength]
      unfold countedPlanckLength
      exact Real.sq_sqrt C.cellArea_pos.le
    rw [harea, ← hcount, hcell]

/-- An inverse calibration whose positive real count is an integer always
admits an exact finite Compton-screen tiling with that cardinality. -/
@[zil_level bridge_theorem]
lemma exists_finiteTiling_of_natCount
    (C : GFreeComptonCellCalibration) (n : ℕ) (hn : 0 < n)
    (hcount : (n : ℝ) = C.cellCount) :
    ∃ T : FiniteComptonScreenTiling C.screenMass C.lightSpeed C.hbar C.screenArea,
      T.cellCount = n :=
  ⟨C.finiteTilingOfNatCount n hn hcount, rfl⟩

/-! ### Dimensional boundary for the Caticha inference width -/

/-- In the ordinary SI projection, a parameter satisfying `m = 1/σ₀²` has
inverse-square-root-mass dimension.  It is not a length dimension. -/
def inferenceWidthSI_dim : Dimension LTMCTIDimensionBase := M𝓭 ^ (-(1 : ℚ) / 2)

/-- Squaring and inverting the calibrated inference-width dimension produces
the SI mass dimension, exactly as required by `m = 1/σ₀²`. -/
theorem inferenceWidthSI_invSq_eq_mass :
    inferenceWidthSI_dim ^ (-2 : ℚ) = M𝓭 := by
  ext b <;> cases b <;> norm_num [inferenceWidthSI_dim]

/-- The inference width used in `m = 1/σ₀²` cannot be silently substituted for
an SI spatial standard deviation.  A conversion scale is required to relate
the two notions. -/
theorem inferenceWidthSI_dim_ne_length : inferenceWidthSI_dim ≠ L𝓭 := by
  intro h
  have hm := congrArg (fun d => d.exponent .mass) h
  norm_num [inferenceWidthSI_dim] at hm

/-- With the repository's information grading, the corresponding inference
width carries `M⁻¹/² I⁻¹/⁴`, whose inverse square is the informed Planck-mass
dimension `M I¹/²`. -/
def informedInferenceWidth_dim : Dimension LTMCTIDimensionBase :=
  M𝓭 ^ (-(1 : ℚ) / 2) * I𝓭 ^ (-(1 : ℚ) / 4)

theorem informedInferenceWidth_invSq_eq_planckMass :
    informedInferenceWidth_dim ^ (-2 : ℚ) = informedPlanckMass_dim := by
  ext b <;> cases b <;> norm_num [informedInferenceWidth_dim, informedPlanckMass_dim,
    informedNewton_dim, newtonConstant_dim, action_dim, velocity_dim]

/-! ### Explicit conversion to a spatial standard deviation -/

/-- A positive conversion scale between a literal spatial standard deviation
`σx` and the inverse-square-root-mass inference width.  Its physical dimension
is `M L²`; setting it silently to one is exactly the unit convention that the
dimension audit above forbids in SI. -/
structure SpatialInferenceConversion where
  /-- The explicit mass-times-length-squared conversion scale. -/
  massLengthSqScale : ℝ
  /-- The conversion scale is positive. -/
  scale_pos : 0 < massLengthSqScale

namespace SpatialInferenceConversion

/-- The normalized Caticha width associated with a literal spatial width:
`σ₀ = σx/√μ`. -/
noncomputable def normalizedWidth
    (K : SpatialInferenceConversion) (σx : ℝ) : ℝ :=
  σx / Real.sqrt K.massLengthSqScale

/-- The dimensionally restored inference mass `m = μ/σx²`. -/
noncomputable def spatialInferenceMass
    (K : SpatialInferenceConversion) (σx : ℝ) : ℝ :=
  K.massLengthSqScale / σx ^ 2

/-- Restoring the conversion scale makes the original Caticha mass exactly
the dimensionally correct spatial-width mass. -/
theorem inferenceMass_normalizedWidth
    (K : SpatialInferenceConversion) (σx : ℝ) :
    inferenceMass (K.normalizedWidth σx) = K.spatialInferenceMass σx := by
  unfold inferenceMass normalizedWidth spatialInferenceMass
  rw [div_pow, inv_div]
  rw [Real.sq_sqrt K.scale_pos.le]

/-- The literal spatial width corresponding to the G-free calibrated
inference width: `σx = √μ σ₀`. -/
noncomputable def spatialWidth
    (K : SpatialInferenceConversion) (C : GFreeComptonCellCalibration) : ℝ :=
  Real.sqrt K.massLengthSqScale * C.inferenceWidth

theorem spatialWidth_pos
    (K : SpatialInferenceConversion) (C : GFreeComptonCellCalibration) :
    0 < K.spatialWidth C :=
  mul_pos (Real.sqrt_pos.2 K.scale_pos) C.inferenceWidth_pos

/-- Normalizing the restored spatial width returns the calibrated Caticha
width exactly. -/
theorem normalizedWidth_spatialWidth
    (K : SpatialInferenceConversion) (C : GFreeComptonCellCalibration) :
    K.normalizedWidth (K.spatialWidth C) = C.inferenceWidth := by
  unfold normalizedWidth spatialWidth
  exact mul_div_cancel_left₀ C.inferenceWidth
    (Real.sqrt_pos.2 K.scale_pos).ne'

/-- The restored spatial-width mass is the same calibrated screen/Planck mass;
the conversion changes units, not the physical mass. -/
theorem spatialInferenceMass_spatialWidth
    (K : SpatialInferenceConversion) (C : GFreeComptonCellCalibration) :
    K.spatialInferenceMass (K.spatialWidth C) = C.screenMass := by
  rw [← K.inferenceMass_normalizedWidth (K.spatialWidth C),
    K.normalizedWidth_spatialWidth]
  exact C.inferenceMass_inferenceWidth

/-- **Dimensionally restored spatial-width form of the counted coupling.**
For `σx = √μ σ₀`, the calibrated result is
`G_count = ℏc σx⁴/μ²`.  The conversion scale is explicit and cannot be
silently discarded. -/
theorem countedNewtonG_eq_spatialWidth
    (K : SpatialInferenceConversion) (C : GFreeComptonCellCalibration) :
    C.countedNewtonG =
      C.hbar * C.lightSpeed * (K.spatialWidth C) ^ 4 /
        K.massLengthSqScale ^ 2 := by
  rw [C.countedNewtonG_eq_hbar_c_mul_inferenceWidth_four]
  unfold spatialWidth
  have hsqrt : (Real.sqrt K.massLengthSqScale) ^ 2 = K.massLengthSqScale :=
    Real.sq_sqrt K.scale_pos.le
  have hsqrt4 : (Real.sqrt K.massLengthSqScale) ^ 4 =
      K.massLengthSqScale ^ 2 := by
    nlinarith [hsqrt]
  rw [mul_pow, hsqrt4]
  field_simp [K.scale_pos.ne']

/-- SI dimension of the required conversion scale, `M L²`. -/
def spatialInferenceScaleSI_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭 ^ (2 : ℚ)

/-- Dividing the conversion scale by a spatial variance produces mass. -/
theorem spatialInferenceScale_div_area_eq_mass :
    spatialInferenceScaleSI_dim / L𝓭 ^ (2 : ℚ) = M𝓭 := by
  ext b <;> cases b <;> norm_num [spatialInferenceScaleSI_dim]

/-- Dividing a spatial width by the square root of the conversion scale gives
the inverse-square-root-mass inference-width dimension. -/
theorem spatialWidth_div_sqrtScale_eq_inferenceWidth :
    L𝓭 / spatialInferenceScaleSI_dim ^ ((1 : ℚ) / 2) =
      inferenceWidthSI_dim := by
  ext b <;> cases b <;> norm_num [spatialInferenceScaleSI_dim, inferenceWidthSI_dim]

end SpatialInferenceConversion

end GFreeComptonCellCalibration

/-- **[The Planck-cell count equals the Compton-cell count exactly at `G = ℏc/m²`]** substituting the
Planck-mass identification `G = ℏc/m²` into the holographic (Planck-cell) bit count reproduces the `G`-free
Compton-cell count of the same entanglement screen — the two tilings coincide precisely at that value of
`G`, which is therefore the content of the equality rather than an input. -/
theorem holographicBits_eq_comptonCellBits_of_massScale (m c ħ η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    holographicBits (sphereArea (entropicProperDistance m c ħ η)) (ħ * c / m ^ 2) ħ c
      = comptonCellBits m c ħ η := by
  have hG : ħ * c / m ^ 2 ≠ 0 := div_ne_zero (mul_ne_zero hħ hc) (pow_ne_zero 2 hm)
  rw [entanglementScreen_holographicBits m c ħ (ħ * c / m ^ 2) η hm hc hħ hG,
      comptonCellBits_eq m c ħ η hm hc hħ]
  field_simp
  try ring

/-! ## The inference-variance realization and the full entropic-gravity hierarchy -/

/-- At the inference-mass realization, the Planck-cell count evaluated with
`G = ℏc σ₀⁴` equals the independently defined Compton-cell count.  Thus the
variance coupling is compatible with the older holographic hierarchy without using
that hierarchy's `G`-dependent count to obtain `G`. -/
theorem holographicBits_eq_comptonCellBits_of_inferenceVariance (c ħ σ₀ η : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    holographicBits
        (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η))
        (ħ * c * σ₀ ^ 4) ħ c =
      comptonCellBits (inferenceMass σ₀) c ħ η := by
  have hm : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]
    exact inv_ne_zero (pow_ne_zero 2 hσ)
  have hG : ħ * c / inferenceMass σ₀ ^ 2 = ħ * c * σ₀ ^ 4 := by
    rw [inferenceMass]
    field_simp
  rw [← hG]
  exact holographicBits_eq_comptonCellBits_of_massScale
    (inferenceMass σ₀) c ħ η hm hc hħ

/-! ## The non-circular Bekenstein–Caticha entropic-action clock -/

/-- **[The Bekenstein–Caticha clock with a `G`-free count].** Set

* `m = inferenceMass σ₀ = 1/σ₀²`,
* `A = sphereArea (entropicProperDistance m c ℏ η)`,
* `N = comptonCellBits m c ℏ η = 4π(log K)²`, and
* `G = ℏcσ₀⁴`.

Then the independently supplied Compton-cell count agrees with the Planck-cell count at this `G`;
therefore the screen carries Bekenstein–Hawking entropy, `G` has the area-per-cell form, and the
entangled inference-mass Compton clock is

`ω_ent = √((1 − exp(−2S_I/ℏ))⁻¹) · G N/(A c σ₀²)`.

Unlike `bekensteinCaticha_clock_from_entropicAction`, this result does not assume
`N = holographicBits(A, G, ℏ, c)`: it proves that equality from the `G`-free Compton tiling. The
physical identification of that tiling and the inference scale remain explicit model inputs. -/
@[zil_level physical_theorem]
theorem comptonCell_bekensteinCaticha_clock_from_entropicAction
    (c ħ σ₀ η : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let A := sphereArea (entropicProperDistance m c ħ η)
    let N := comptonCellBits m c ħ η
    let G := ħ * c * σ₀ ^ 4
    microstateEntropy N = A * c ^ 3 / (4 * (G * ħ))
      ∧ G = A * c ^ 3 / (ħ * N)
      ∧ m = 1 / σ₀ ^ 2
      ∧ deBroglieFrequency (Real.cosh η * (m * c ^ 2)) ħ =
        Real.sqrt ((1 - Real.exp (-2 * (entropicAction ħ η / ħ)))⁻¹) *
          (G * N / (A * c * σ₀ ^ 2)) := by
  dsimp only
  have hm : 0 < inferenceMass σ₀ := by
    rw [inferenceMass]
    positivity
  have hR : 0 < entropicProperDistance (inferenceMass σ₀) c ħ η :=
    entropicProperDistance_pos (inferenceMass σ₀) c ħ η hm hc hħ hη
  have hA : 0 < sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) :=
    sphereArea_pos hR
  have hN : 0 < comptonCellBits (inferenceMass σ₀) c ħ η :=
    comptonCellBits_pos (inferenceMass σ₀) c ħ η hm hc hħ hη
  have hG : 0 < ħ * c * σ₀ ^ 4 := by positivity
  have hbits :
      comptonCellBits (inferenceMass σ₀) c ħ η =
        holographicBits
          (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η))
          (ħ * c * σ₀ ^ 4) ħ c :=
    (holographicBits_eq_comptonCellBits_of_inferenceVariance
      c ħ σ₀ η hσ.ne' hc.ne' hħ.ne').symm
  exact bekensteinCaticha_clock_from_entropicAction
    η σ₀ (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η))
    (ħ * c * σ₀ ^ 4) (comptonCellBits (inferenceMass σ₀) c ħ η) c ħ
    hσ.ne' hA.ne' hG.ne' hN.ne' hc.ne' hħ.ne' hη hbits

/-- **[The `G`-free variance coupling enters the complete entropic-gravity
hierarchy].**  With positive physical data, set

* `m = inferenceMass σ₀ = 1/σ₀²`,
* `N = comptonCellBits m c ħ η` (independent of `G`),
* `G = ħc σ₀⁴`, and
* `R = entropicProperDistance m c ħ η`.

The independently obtained count first reproduces the Planck-cell count at this
coupling; the existing `entropic_gravity_system` then supplies, without duplicated
algebra, the inference-mass entropic force, area-per-bit identity, Einstein coupling,
dust source, and Schwarzschild radius. -/
theorem comptonCell_inference_entropic_gravity_system
    (M c kB σ₀ ħ Δx η ρ : ℝ)
    (hM : 0 < M) (hc : 0 < c) (hkB : 0 < kB) (hσ : 0 < σ₀)
    (hħ : 0 < ħ) (hΔx : 0 < Δx) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ħ η
    let N := comptonCellBits m c ħ η
    let G := ħ * c * σ₀ ^ 4
    N = holographicBits (sphereArea R) G ħ c
      ∧ verlindeEntropicForce (bitScreenTemperature M c N kB)
          (verlindeDisplacementEntropy ħ kB (inferenceMass σ₀) c Δx) Δx
          = 4 * Real.pi * M * c ^ 3 / (ħ * N * σ₀ ^ 2)
      ∧ G = sphereArea R * c ^ 3 / (ħ * N)
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ħ * c)
      ∧ (8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 / 2) =
          4 * Real.pi * G * ρ / c ^ 2
      ∧ schwarzschildRadius M G c = 2 * M * c * sphereArea R / (ħ * N) := by
  dsimp only
  have hσ0 : σ₀ ≠ 0 := hσ.ne'
  have hm : 0 < inferenceMass σ₀ := by
    rw [inferenceMass]
    positivity
  have hN : 0 < comptonCellBits (inferenceMass σ₀) c ħ η :=
    comptonCellBits_pos (inferenceMass σ₀) c ħ η hm hc hħ hη
  have hG : 0 < ħ * c * σ₀ ^ 4 := by positivity
  have hR : 0 < entropicProperDistance (inferenceMass σ₀) c ħ η :=
    entropicProperDistance_pos (inferenceMass σ₀) c ħ η hm hc hħ hη
  have hbits :
      comptonCellBits (inferenceMass σ₀) c ħ η =
        holographicBits
          (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η))
          (ħ * c * σ₀ ^ 4) ħ c :=
    (holographicBits_eq_comptonCellBits_of_inferenceVariance
      c ħ σ₀ η hσ0 hc.ne' hħ.ne').symm
  exact ⟨hbits,
    entropic_gravity_system M c (comptonCellBits (inferenceMass σ₀) c ħ η)
      kB σ₀ ħ Δx (ħ * c * σ₀ ^ 4)
      (entropicProperDistance (inferenceMass σ₀) c ħ η) ρ
      hN.ne' hkB.ne' hΔx.ne' hσ0 hM.ne' hc.ne' hħ.ne' hG.ne' hR.ne' hbits⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

end

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant in
#physlib_axiom_clean_all [
  inferenceMass_eq_gaussianMeanFisherInformation,
  comptonCellBits_mul_cellArea,
  eq_comptonCellBits_of_mul_cellArea_eq,
  gaussianFisherScreenCoupling_eq,
  GFreeComptonCellCalibration.exists_finiteTiling_of_natCount ]

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant in
#physlib_non_vacuous_all [
  inferenceMass_eq_gaussianMeanFisherInformation,
  comptonCellBits_mul_cellArea,
  eq_comptonCellBits_of_mul_cellArea_eq,
  gaussianFisherScreenCoupling_eq,
  GFreeComptonCellCalibration.exists_finiteTiling_of_natCount ]

/- ZIL-BEGIN -/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits where
  formalizes @ "claim:supplying-the-holographic-bit-count-from-the-g-free-compton-cell-tiling-of-the-entanglement-screen-returns-newtons-constant-as-hbar-c-over-mass-squared-a-prediction-from-the-mass-scale-not-a-circular-inversion",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.entanglementScreenArea",
  caveat @ "claim:this-shifts-the-empirical-input-from-newtons-constant-to-a-mass-scale-and-does-not-derive-the-numerical-value-of-g-from-no-physical-input"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits",
  supported_by @ "lean:contrContrContractField.nondegenerate",
  formalizes @ "claim:grounding-the-screen-scale-in-the-inference-mass-one-over-\
gaussian-inference-width-squared-the-g-free-effective-compton-cell-screen-coupling-\
becomes-hbar-c-times-inference-width-to-the-fourth",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:supplying-the-holographic-bit-count-from-the-g-free-compton-cell-tiling-of-the-entanglement-screen-returns-newtons-constant-as-hbar-c-over-mass-squared-a-prediction-from-the-mass-scale-not-a-circular-inversion",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass",
  caveat @ "epistemic:the-inference-width-has-inverse-square-root-mass-dimension-\
and-the-exact-screen-coupling-does-not-become-measured-newton-g-without-a-separate-\
physical-identification-and-numerical-selection-of-sigma0"

zil attach gaussianFisherScreenCoupling_eq where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:SpatialInferenceConversion.comptonCellBits_mul_cellArea",
  formalizes @ "claim:the-genuine-gaussian-score-integral-and-the-unique-normalized-\
screen-area-count-construct-an-information-screen-coupling-equal-to-hbar-c-times-\
sigma0-to-the-fourth",
  epistemic_status @ "mathematical-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.\
GaussianMeanFisherInformationIntegral.gaussianMeanFisherInformation_eq_inv_variance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
EntanglementScreenArea.entanglementScreenArea",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.comptonCellBits_mul_cellArea",
  caveat @ "epistemic:the-constructed-information-screen-coupling-is-exact-but-\
equating-it-with-the-newton-constant-measured-by-gravitational-experiments-is-a-\
separate-physical-identification",
  caveat @ "scope:sigma0-is-a-gaussian-inference-width-with-inverse-square-root-mass-\
dimension-not-an-si-spatial-length"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.fixes_screenMass_inferenceWidth_and_newtonG where
  formalizes @ "claim:an-independent-g-free-screen-area-and-compton-cell-count-fix-the-screen-mass-and-caticha-inference-width-and-yield-g-equal-to-hbar-c-over-screen-mass-squared-equal-to-hbar-c-times-sigma0-to-the-fourth",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass",
  caveat @ "epistemic:conditional-non-circular-calibration-the-independent-screen-area-and-cell-count-are-physical-inputs-and-are-not-derived-from-g"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.existsUnique_countedNewtonG where
  formalizes @ "claim:g-free-screen-area-and-cell-count-admit-exactly-one-coupling-whose-\
planck-area-equals-the-counted-cell-area-and-that-coupling-is-hbar-c-sigma0-to-the-fourth",
  epistemic_status @ "mathematical-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.candidateNewtonG_eq_countedNewtonG",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.\
countedNewtonG_eq_hbar_c_mul_inferenceWidth_four",
  caveat @ "epistemic:forward-uniqueness-does-not-assume-a-measured-G-but-its-physical-\
newtonian-interpretation-requires-that-screen-area-and-compton-cell-count-are-independent-\
physical-data"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.countedCell_planckComptonClosure where
  formalizes @ "claim:the-independently-counted-compton-cell-area-is-the-derived-planck-area-the-screen-mass-is-the-positive-planck-mass-and-the-compton-clock-is-the-planck-clock",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:screen-area-and-cell-count-are-measured-without-using-newtons-constant-or-the-screen-mass",
  requires @ "assumption:the-independently-counted-cells-are-reduced-compton-wavelength-cells",
  supported_by @ "lean:Physlib.Units.PlanckUnitsInformation.informedPlanck_halfBit_grading",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency",
  caveat @ "epistemic:conditional-planck-scale-calibration-not-an-independent-prediction-of-a-distinct-particle-mass-if-the-cell-count-was-itself-computed-from-an-already-supplied-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.SpatialInferenceConversion.countedNewtonG_eq_spatialWidth where
  formalizes @ "claim:with-an-explicit-mass-times-length-squared-conversion-scale-mu-the-g-free-calibration-has-the-dimensionally-correct-spatial-width-form-g-equals-hbar-c-times-sigma-x-to-the-fourth-over-mu-squared",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-positive-conversion-scale-mu-between-caticha-inference-width-and-si-spatial-width-is-independently-supplied",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.SpatialInferenceConversion.spatialWidth_div_sqrtScale_eq_inferenceWidth",
  caveat @ "epistemic:the-theorem-restores-si-dimensional-consistency-but-does-not-predict-the-conversion-scale-mu-or-license-setting-it-to-one"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_massScale where
  supported_by @ "lean:SpatialInferenceConversion.comptonCellBits_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.entanglementScreen_holographicBits",
  formalizes @ "claim:the-planck-cell-holographic-bit-count-and-the-g-free-compton-cell-count-of-the-entanglement-screen-coincide-exactly-when-newtons-constant-equals-hbar-c-over-mass-squared",
  requires @ "claim:supplying-the-holographic-bit-count-from-the-g-free-compton-cell-tiling-of-the-entanglement-screen-returns-newtons-constant-as-hbar-c-over-mass-squared-a-prediction-from-the-mass-scale-not-a-circular-inversion"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_bekensteinCaticha_clock_from_entropicAction where
  formalizes @ "claim:the-g-free-compton-cell-count-closes-the-bekenstein-caticha-entropic-action-clock-chain-with-g-equal-to-hbar-c-times-sigma0-to-the-fourth",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:bekenstein-black-hole-thermodynamics-1980",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_inferenceVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions.bekensteinCaticha_clock_from_entropicAction",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:schmidt-rapidity-reparametrizes-the-physical-compton-clock",
  caveat @ "epistemic:the-old-circular-holographic-count-premise-is-discharged-but-the-compton-cell-tiling-and-position-variance-remain-model-inputs",
  caveat @ "epistemic:the-theorem-does-not-fix-sigma0-eta-or-the-measured-value-of-newtons-constant"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system where
  formalizes @ "claim:g-equals-hbar-c-sigma0-to-the-fourth-from-the-independent-compton-cell-count-feeds-the-existing-entropic-gravity-hierarchy-through-area-per-bit-einstein-coupling-dust-source-and-schwarzschild-radius",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant.entropic_gravity_system",
  caveat @ "epistemic:the-compton-cell-count-removes-the-old-g-in-the-bit-count-circularity-but-the-screen-tiling-and-position-variance-remain-explicit-model-inputs"

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

zil attach GFreeComptonCellCalibration.exists_finiteTiling_of_natCount where
  formalizes @ "claim:a-positive-g-free-inverse-calibration-whose-real-cell-count-\
is-the-cast-of-a-positive-natural-number-constructs-an-exact-finite-compton-\
screen-tiling-with-that-cardinality",
  epistemic_status @ "mathematical-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.GFreeComptonCellCalibration.\
comptonWavelength_screenMass_eq_countedPlanckLength",
  caveat @ "epistemic:this-is-an-inverse-calibration-existence-theorem-the-\
positive-screen-area-and-natural-number-count-remain-supplied-data"

zil attach FiniteComptonScreenTiling.comptonCellBits_eq_count where
  formalizes @ "claim:an-exact-finite-partition-by-reduced-compton-area-cells-turns-\
the-effective-real-area-ratio-into-the-cast-of-an-actual-natural-number-cell-cardinality",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-screen-admits-an-exact-finite-partition-by-reduced-\
compton-area-cells",
  caveat @ "epistemic:the-partition-is-additional-microscopic-data-and-does-not-exist-\
for-an-arbitrary-real-screen-area"

zil attach FiniteComptonScreenTiling.entropicArea_quantized where
  formalizes @ "claim:if-the-entanglement-screen-has-an-exact-finite-compton-cell-\
partition-then-four-pi-log-k-squared-is-the-cast-of-its-natural-number-cell-count",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonCellNewtonConstant.FiniteComptonScreenTiling.comptonCellBits_eq_count",
  caveat @ "epistemic:this-is-a-necessary-quantization-condition-not-an-unconditional-\
existence-proof-for-the-partition"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant

zil_file_contract physlib.comptonCellNewtonConstant where
  promises "The G-free direct branch defines an effective real count N = A/lambda_C^2. \
Consequently the complete area, including every radius and entanglement factor, cancels \
from A c^3/(hbar N), leaving the normalized-area identity hbar c/m^2; identifying this \
constructed coupling with measured Newton G remains separate. An additional \
FiniteComptonScreenTiling carrier supplies the missing operational interpretation: it \
contains a natural-number count, a finite label type, a Boolean register with 2^N states, \
and an exact area-partition equation. Only under that explicit partition does the \
effective real ratio equal an actual cardinality, and for the entanglement screen its \
existence forces 4 pi log(K)^2 to be integral. Conversely, when the positive G-free \
count is already the cast of a natural number, the inverse-calibrated screen mass \
constructs the exact finite tiling rather than requiring it as another witness. The \
Gaussian-Fisher and inverse-calibration \
branches retain their stated conditional Planck/Compton closures and dimensional audit."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.entanglementScreenArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.entanglementScreen_holographicBits",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.\
GaussianMeanFisherInformationIntegral.gaussianMeanFisherInformation_eq_inv_variance",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant.entropic_gravity_system",
    "lean:Physlib.Thermodynamics.VerlindeNewtonGravity.holographicBits"]
  forbids_substitutes ["the circular Planck-cell count N = A c^3/(G hbar), which already contains the G it returns",
    "a numerical prediction of G from no physical input: the direct branch requires a mass while the inverse branch requires independent A/N and the Compton-cell identification",
    "calling the real-valued effective area ratio a literal finite cell cardinality \
without a FiniteComptonScreenTiling witness",
    "identifying the constructed Gaussian-Fisher screen coupling with measured \
Newton G without a separate physical or empirical selection theorem",
    "interpreting the Caticha inference width sigma0 as an SI spatial length without an explicit dimensionful conversion scale"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits_eq,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.inferenceMass_eq_gaussianMeanFisherInformation,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits_mul_cellArea,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.eq_comptonCellBits_of_mul_cellArea_eq,
    FiniteComptonScreenTiling.cellRegister_card,
    FiniteComptonScreenTiling.comptonCellBits_eq_count,
    FiniteComptonScreenTiling.entropicArea_quantized,
    GFreeComptonCellCalibration.exists_finiteTiling_of_natCount,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.gaussianFisherScreenCoupling_eq,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.fixes_screenMass_inferenceWidth_and_newtonG,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.countedCell_planckComptonClosure,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.inferenceWidthSI_dim_ne_length,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.SpatialInferenceConversion.countedNewtonG_eq_spatialWidth,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.SpatialInferenceConversion.spatialWidth_div_sqrtScale_eq_inferenceWidth,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_massScale,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_inferenceVariance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_bekensteinCaticha_clock_from_entropicAction,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system]

/- ZIL-END -/
