/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.PhysicalDualityNavierStokesFiberLift
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierAgmonInterpolation

/-!
# The confinement criterion at field level: two hypotheses become theorems

`PhysicalDualityNavierStokesFiberLift.pointwise_threshold_confinement` is stated over **bare reals**
`VS, ν, P, C, λ₁, Ω`, with the enstrophy non-negativity, the spectral gap `λ₁Ω ≤ P`, and the interpolation all
carried as hypotheses.  That is scalar bookkeeping: nothing tied `Ω` and `P` to a field.

This module instantiates the criterion on the repository's actual spectral fields — `NSFieldFourier`, with
`enstrophy v = ∑ |k_i|²|â_i|²` and `palinstrophy v = ∑ |k_i|⁴|â_i|²` — and thereby **discharges three of its
hypotheses from theorems rather than assumptions**:

* `0 ≤ Ω` and `0 ≤ P` are `enstrophy_nonneg` / `palinstrophy_nonneg` — properties of the spectral sums;
* the **spectral gap at `λ₁ = 1`** is `NSFourierAgmonInterpolation.enstrophy_le_palinstrophy`: for a field
  whose modes all satisfy `|k| ≥ 1` (the `T³` Poincaré condition — no zero mode), `Ω ≤ P` is *proved*
  (`fieldLevel_spectral_gap`), not posited.  This is the assumption the small-domain story previously took on
  faith: on the torus it is a theorem about the Fourier support.

What remains genuinely assumed is the interpolation `VS ≤ C√(Ω³P)` — and honestly so: the repository has no
vortex-stretching functional on `NSFieldFourier`, so `VS` stays an abstract real constrained by the
interpolation inequality.  Making `VS` a spectral functional (a mode-sum for `∫(ω·∇)u·ω`) and *deriving* the
interpolation from the Fourier data is the remaining step to a fully field-level criterion.

* `fieldLevel_twoDim_rate_nonpos` — the 2D corner needs no hypothesis at all: `VS = 0` gives
  `dΩ/dt = −2ν·palinstrophy v ≤ 0` for any field and any `ν ≥ 0`.
* `fieldLevel_confinement` — the criterion on a genuine field, with only the interpolation and the threshold
  `C²·(enstrophy v)² ≤ ν²` assumed.
* `fieldLevel_confinement_synthesis` — the gap and both non-negativities exhibited as theorems alongside the
  conclusion, so the reduction in assumed content is visible in one statement.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.FieldLevelConfinementBridge

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.PhysicalDualityNavierStokesFiberLift
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/-- **The spectral gap is a theorem, not a hypothesis.**  For a spectral field whose modes all satisfy
`|k| ≥ 1` (no zero mode — the `T³` Poincaré condition), the unit-gap inequality `1·Ω ≤ P` holds by
`enstrophy_le_palinstrophy`: on the torus the confinement criterion's spectral-gap assumption is a fact about
the Fourier support. -/
theorem fieldLevel_spectral_gap (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i) :
    1 * enstrophy v ≤ palinstrophy v := by
  rw [one_mul]
  exact enstrophy_le_palinstrophy v hfreq

/-- **The 2D corner is unconditional at field level.**  With no vortex stretching the enstrophy rate of any
spectral field is `−2ν·palinstrophy v ≤ 0` — no interpolation, no gap, no threshold: the palinstrophy of a
Fourier field is a sum of squares. -/
theorem fieldLevel_twoDim_rate_nonpos (v : NSFieldFourier) (ν : ℝ) (hν : 0 ≤ ν) :
    enstrophyRate 0 ν (palinstrophy v) ≤ 0 := by
  unfold enstrophyRate
  nlinarith [mul_nonneg hν (palinstrophy_nonneg v)]

/-- **The confinement criterion on a genuine spectral field.**  Instantiating
`pointwise_threshold_confinement` at `Ω := enstrophy v`, `P := palinstrophy v`, `λ₁ := 1`: the two
non-negativities and the spectral gap are supplied by *theorems* about the Fourier sums, leaving only the
interpolation and the threshold `C²(enstrophy v)² ≤ ν²` as hypotheses.  Below that threshold the enstrophy of
the field is non-increasing. -/
theorem fieldLevel_confinement (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i)
    (VS ν C : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hVS : VS ≤ C * Real.sqrt (enstrophy v ^ 3 * palinstrophy v))
    (hthresh : C ^ 2 * enstrophy v ^ 2 ≤ ν ^ 2) :
    enstrophyRate VS ν (palinstrophy v) ≤ 0 := by
  refine pointwise_threshold_confinement VS ν (palinstrophy v) C 1 (enstrophy v)
    hC hν (enstrophy_nonneg v) (palinstrophy_nonneg v) hVS
    (fieldLevel_spectral_gap v hfreq) ?_
  rw [mul_one]
  exact hthresh

/-- **The reduction in assumed content, in one statement.**  For a zero-mode-free spectral field: the two
non-negativities and the spectral gap hold as theorems, and the confinement conclusion follows from the
interpolation and threshold alone — the criterion is no longer scalar bookkeeping but a statement about an
actual Fourier field, with three of its five structural hypotheses discharged. -/
theorem fieldLevel_confinement_synthesis (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i)
    (VS ν C : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hVS : VS ≤ C * Real.sqrt (enstrophy v ^ 3 * palinstrophy v))
    (hthresh : C ^ 2 * enstrophy v ^ 2 ≤ ν ^ 2) :
    0 ≤ enstrophy v
      ∧ 0 ≤ palinstrophy v
      ∧ 1 * enstrophy v ≤ palinstrophy v
      ∧ enstrophyRate VS ν (palinstrophy v) ≤ 0 :=
  ⟨enstrophy_nonneg v, palinstrophy_nonneg v, fieldLevel_spectral_gap v hfreq,
    fieldLevel_confinement v hfreq VS ν C hC hν hVS hthresh⟩

/-! ### The stretching as a spectral functional: the interpolation derived, not assumed

The remaining assumed hypothesis was the interpolation `VS ≤ C√(Ω³P)`, carried because `VS` was an abstract
real.  For the **mode-diagonal (shell) stretching** — the one stretching functional definable on this carrier,
`vortexStretchingDiagonal v = ∑ |k_i|³ â_i³` — no interpolation need be assumed at all: Cauchy–Schwarz on the
Fourier data *derives* the bound `VS_diag ≤ √Ω · Ω` (`vortexStretchingDiagonal_le`), because each mode obeys
`(|k_i| â_i)² ≤ Ω`.  Feeding that in, `diagonal_confinement` closes the criterion with **no assumed
inequality whatsoever**: enstrophy below `ν²` is non-increasing, everything from the spectral sums.

**Why only the diagonal one.**  The true vortex stretching `∫(ω·∇)u·ω` is irreducibly *triadic* — it needs
vector amplitudes and the resonance convolution `k = j + l`.  The repository has that structure
(`TorusFourier.TriadicKernel.triadicKernelCoeff`, with `TorusWaveVec3` and the resonance condition), but it is
not joined to `NSFieldFourier`, which stores only wavenumber *magnitudes* `freq : Fin N → ℕ` and *scalar*
amplitudes.  So the shell functional is what this carrier supports, and it is honestly weaker: its derived
bound scales as `Ω^{3/2}`, below the triadic estimate's critical `Ω^{3/2}P^{1/2}` — the diagonal model's
stretching is easier to dominate than the real one.  `diagonal_confinement` is therefore a fully-derived
confinement **for the shell model**, not the 3D theorem; joining `NSFieldFourier` to the triadic kernel is the
step that would make it one. -/

/-- **The mode-diagonal (shell) vortex stretching** `∑ |k_i|³ â_i³` — the stretching functional definable on a
scalar spectral carrier, with one factor of `|k|` per field factor. -/
noncomputable def vortexStretchingDiagonal (v : NSFieldFourier) : ℝ :=
  ∑ i, (v.freq i : ℝ) ^ 3 * v.amp i ^ 3

/-- Each mode's squared contribution is bounded by the enstrophy — a single term of a sum of
non-negatives. -/
lemma mode_sq_le_enstrophy (v : NSFieldFourier) (i : Fin v.N) :
    ((v.freq i : ℝ) * v.amp i) ^ 2 ≤ enstrophy v := by
  unfold enstrophy
  have hrw : ((v.freq i : ℝ) * v.amp i) ^ 2 = (v.freq i : ℝ) ^ 2 * v.amp i ^ 2 := by ring
  rw [hrw]
  exact Finset.single_le_sum (f := fun j => (v.freq j : ℝ) ^ 2 * v.amp j ^ 2)
    (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)

/-- Hence each mode amplitude-times-wavenumber is bounded by `√Ω`. -/
lemma mode_le_sqrt_enstrophy (v : NSFieldFourier) (i : Fin v.N) :
    (v.freq i : ℝ) * v.amp i ≤ Real.sqrt (enstrophy v) :=
  calc (v.freq i : ℝ) * v.amp i ≤ |(v.freq i : ℝ) * v.amp i| := le_abs_self _
    _ = Real.sqrt (((v.freq i : ℝ) * v.amp i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (enstrophy v) := Real.sqrt_le_sqrt (mode_sq_le_enstrophy v i)

/-- **The interpolation, derived.**  Cauchy–Schwarz on the Fourier data gives `VS_diag ≤ √Ω · Ω` — the
shell stretching is bounded by the spectral sums with **no assumed inequality**, factoring each term as
`(|k_i| â_i)·(|k_i|² â_i²)` and bounding the first factor by `√Ω`. -/
theorem vortexStretchingDiagonal_le (v : NSFieldFourier) :
    vortexStretchingDiagonal v ≤ Real.sqrt (enstrophy v) * enstrophy v := by
  have key : ∀ i ∈ (Finset.univ : Finset (Fin v.N)),
      (v.freq i : ℝ) ^ 3 * v.amp i ^ 3
        ≤ Real.sqrt (enstrophy v) * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := by
    intro i _
    have hrw : (v.freq i : ℝ) ^ 3 * v.amp i ^ 3
        = ((v.freq i : ℝ) * v.amp i) * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (mode_le_sqrt_enstrophy v i) (by positivity)
  calc vortexStretchingDiagonal v
      ≤ ∑ i, Real.sqrt (enstrophy v) * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := Finset.sum_le_sum key
    _ = Real.sqrt (enstrophy v) * enstrophy v := by rw [← Finset.mul_sum]; rfl

/-- **Confinement with nothing assumed.**  For a zero-mode-free spectral field with enstrophy below `ν²`, the
shell-model enstrophy rate is non-increasing — the interpolation is *derived* (`vortexStretchingDiagonal_le`),
the spectral gap is *derived* (`enstrophy_le_palinstrophy`), the non-negativities are *derived*: no inequality
is posited anywhere in the chain `VS_diag ≤ √Ω·Ω ≤ ν·Ω ≤ ν·P`. -/
theorem diagonal_confinement (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i) (ν : ℝ) (hν : 0 ≤ ν)
    (hthresh : enstrophy v ≤ ν ^ 2) :
    enstrophyRate (vortexStretchingDiagonal v) ν (palinstrophy v) ≤ 0 := by
  refine (enstrophyRate_nonpos_iff _ _ _).mpr ?_
  have hsq : Real.sqrt (enstrophy v) ≤ ν := by
    have h := Real.sqrt_le_sqrt hthresh
    rwa [Real.sqrt_sq hν] at h
  calc vortexStretchingDiagonal v ≤ Real.sqrt (enstrophy v) * enstrophy v :=
        vortexStretchingDiagonal_le v
    _ ≤ ν * enstrophy v := mul_le_mul_of_nonneg_right hsq (enstrophy_nonneg v)
    _ ≤ ν * palinstrophy v := mul_le_mul_of_nonneg_left (enstrophy_le_palinstrophy v hfreq) hν

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.FieldLevelConfinementBridge

end
