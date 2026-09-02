/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
meta import Zil

/-!
# Entanglement-entropy dynamics from the linearized AdS Einstein equation

This module formalizes the analytic core of Nozaki, Numasawa, Prudenziati, and
Takayanagi, *Dynamics of Entanglement Entropy from Einstein Equation*,
arXiv:1304.7100v2.

* The Fefferman--Graham normalizable coefficient is converted to the boundary
  stress tensor with the paper's exact normalization.
* The radius convention of the general round-ball first law is reconciled with
  the interval-width convention used in the AdS3 section.  The leading
  homogeneous entropy shift then satisfies the first law exactly.
* The paper's nonlocal AdS3 Fourier kernel is differentiated twice and proved
  to satisfy its radial equation.
* A boundary metric mode satisfying the massless wave equation produces an
  entropy mode satisfying both the boundary-time and radial equations.

## Honest direction and scope

The paper solves the linearized Einstein equations in Fefferman--Graham gauge
and derives constraints on the first-order RT entropy shift.  Accordingly, the
results below prove `Einstein/FG mode -> entropy equations`; they do not reverse
this implication or derive the nonlinear Einstein equation from entanglement.
The homogeneous entropy formula is the leading small-interval term of the
paper's Eq. (3.24), not the full finite-width entropy.  The Fourier result is
the pure-gravity AdS3/CFT2 sector.  Einstein--scalar source terms, higher
dimensions, boosted regions, and nonlinear backreaction remain separate.

## Reference

* M. Nozaki, T. Numasawa, A. Prudenziati, T. Takayanagi,
  arXiv:1304.7100v2.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra

/-! ## A. Fefferman--Graham stress normalization and the first law -/

/-- The first-order induced-area variation represented by the integrated
metric contraction in Nozaki et al. Eq. (2.4).  Extremality removes the
first-order embedding variation, leaving one half of that contraction. -/
noncomputable def firstOrderInducedAreaVariation (metricContractionIntegral : ℝ) : ℝ :=
  metricContractionIntegral / 2

/-- **[Nozaki et al. Eq. (2.4) through the existing RT carrier]** Applying the
repository's `rtAreaEntropy` to the first-order induced-area variation gives
exactly the paper's `1/(8G_N)` metric-contraction formula. -/
@[zil_level bridge_theorem]
lemma rtAreaEntropy_firstOrderVariation (G metricContractionIntegral : ℝ) :
    rtAreaEntropy (firstOrderInducedAreaVariation metricContractionIntegral) G =
      metricContractionIntegral / (8 * G) := by
  unfold rtAreaEntropy firstOrderInducedAreaVariation
  ring

/-- **[Nozaki et al. Eq. (2.9)]** The coefficient converting the normalizable
Fefferman--Graham mode `h_{μν} = z^d H_{μν} + ...` into the boundary
stress tensor: `d R^(d-1)/(16 π G_N)`. -/
noncomputable def fgBoundaryStressCoefficient (d : ℕ) (R G : ℝ) : ℝ :=
  d * R ^ (d - 1) / (16 * Real.pi * G)

/-- **[Nozaki et al. Eq. (2.6)]** The universal effective temperature of a
round CFT region of radius `r`: `(d+1)/(2πr)`. -/
noncomputable def roundBallEntanglingTemperature (d : ℕ) (r : ℝ) : ℝ :=
  (d + 1) / (2 * Real.pi * r)

/-- In CFT2 the Fefferman--Graham stress coefficient is `R/(8πG_N)`. -/
@[zil_level bridge_theorem]
lemma fgBoundaryStressCoefficient_two (R G : ℝ) :
    fgBoundaryStressCoefficient 2 R G = R / (8 * Real.pi * G) := by
  unfold fgBoundaryStressCoefficient
  norm_num
  ring

/-- The CFT2 boundary energy density associated with the normalizable metric
coefficient `H`: `T_tt = R H/(8πG_N)`. -/
noncomputable def ads3BoundaryEnergyDensity (R G H : ℝ) : ℝ :=
  R / (8 * Real.pi * G) * H

/-- **[Nozaki et al. Eq. (3.24)]** The leading small-interval RT entropy shift
for interval width `ell`: `R ell² H/(24G_N)`.  This definition deliberately
names the leading term rather than identifying it with the full entropy. -/
noncomputable def ads3LeadingEntropyShift (R G H ell : ℝ) : ℝ :=
  R * ell ^ 2 / (24 * G) * H

/-- The energy shift of a spatially homogeneous CFT2 density on an interval of
width `ell`. -/
noncomputable def ads3HomogeneousEnergyShift (R G H ell : ℝ) : ℝ :=
  ell * ads3BoundaryEnergyDensity R G H

/-- The paper's AdS3 interval coordinate uses the width `ell`, whereas its
general round-ball formula uses radius `r = ell/2`.  Consequently the CFT2
effective temperature is exactly `3/(π ell)`. -/
@[zil_level bridge_theorem]
lemma roundBallEntanglingTemperature_two_half_width (ell : ℝ) :
    roundBallEntanglingTemperature 2 (ell / 2) = 3 / (Real.pi * ell) := by
  unfold roundBallEntanglingTemperature
  norm_num
  ring

/-- **[Nozaki et al. Eqs. (2.5)--(2.9), (3.24)]** With the radius/width
conversion made explicit, the leading homogeneous AdS3 entropy shift obeys
`T_eff ΔS_A = ΔE_A` exactly. -/
@[zil_level physical_theorem]
lemma ads3LeadingEntropy_firstLaw (R G H ell : ℝ)
    (hG : G ≠ 0) (hell : ell ≠ 0) :
    roundBallEntanglingTemperature 2 (ell / 2) *
        ads3LeadingEntropyShift R G H ell =
      ads3HomogeneousEnergyShift R G H ell := by
  rw [roundBallEntanglingTemperature_two_half_width]
  unfold ads3LeadingEntropyShift ads3HomogeneousEnergyShift ads3BoundaryEnergyDensity
  field_simp [hG, hell, Real.pi_ne_zero]
  ring

/-! ## B. The pure-gravity AdS3 Fourier kernel -/

/-- The numerator `2 sin(k ell/2) - ell k cos(k ell/2)` in the nonlocal
entropy kernel of Nozaki et al. Eq. (3.8). -/
noncomputable def ads3EntropyKernelNumerator (k ell : ℝ) : ℝ :=
  2 * Real.sin (k * ell / 2) - ell * k * Real.cos (k * ell / 2)

/-- The first derivative of `ads3EntropyKernelNumerator` with respect to the
interval width. -/
noncomputable def ads3EntropyKernelNumeratorDeriv (k ell : ℝ) : ℝ :=
  ell * k ^ 2 / 2 * Real.sin (k * ell / 2)

/-- The second derivative of `ads3EntropyKernelNumerator` with respect to the
interval width. -/
noncomputable def ads3EntropyKernelNumeratorSecondDeriv (k ell : ℝ) : ℝ :=
  k ^ 2 / 2 * Real.sin (k * ell / 2) +
    ell * k ^ 3 / 4 * Real.cos (k * ell / 2)

/-- The numerator has the displayed first derivative. -/
@[zil_level bridge_theorem]
lemma ads3EntropyKernelNumerator_hasDerivAt (k ell : ℝ) :
    HasDerivAt (ads3EntropyKernelNumerator k)
      (ads3EntropyKernelNumeratorDeriv k ell) ell := by
  have hu : HasDerivAt (fun x : ℝ => k * x / 2) (k / 2) ell := by
    simpa using ((hasDerivAt_id ell).const_mul k).div_const 2
  have hsin := (Real.hasDerivAt_sin (k * ell / 2)).comp ell hu
  have hcos := (Real.hasDerivAt_cos (k * ell / 2)).comp ell hu
  unfold ads3EntropyKernelNumerator ads3EntropyKernelNumeratorDeriv
  convert hsin.const_mul 2 |>.sub
    (((hasDerivAt_id ell).const_mul k).mul hcos) using 1 <;>
    first
      | rfl
      | (ext x; simp only [Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply,
          Pi.add_apply]; ring)
      | (simp only [Function.comp_apply, id_eq]; ring)

/-- The numerator has the displayed second derivative. -/
@[zil_level bridge_theorem]
lemma ads3EntropyKernelNumeratorDeriv_hasDerivAt (k ell : ℝ) :
    HasDerivAt (ads3EntropyKernelNumeratorDeriv k)
      (ads3EntropyKernelNumeratorSecondDeriv k ell) ell := by
  have hu : HasDerivAt (fun x : ℝ => k * x / 2) (k / 2) ell := by
    simpa using ((hasDerivAt_id ell).const_mul k).div_const 2
  have hsin := (Real.hasDerivAt_sin (k * ell / 2)).comp ell hu
  unfold ads3EntropyKernelNumeratorDeriv ads3EntropyKernelNumeratorSecondDeriv
  convert (((hasDerivAt_id ell).const_mul (k ^ 2 / 2)).mul hsin) using 1 <;>
    first
      | rfl
      | (ext x; simp only [Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply,
          Pi.add_apply]; ring)
      | (simp only [Function.comp_apply, id_eq]; ring)

/-- **[Nozaki et al. Eq. (3.8)]** The Fourier multiplier taking a normalizable
AdS3 boundary metric mode `H(k,t)` to the first-order entropy mode. -/
noncomputable def ads3EntropyFourierKernel (R G k ell : ℝ) : ℝ :=
  R / (2 * G * k ^ 3) * (ads3EntropyKernelNumerator k ell / ell)

/-- The first width derivative of the AdS3 entropy kernel. -/
noncomputable def ads3EntropyFourierKernelDeriv (R G k ell : ℝ) : ℝ :=
  R / (2 * G * k ^ 3) *
    (ads3EntropyKernelNumeratorDeriv k ell / ell -
      ads3EntropyKernelNumerator k ell / ell ^ 2)

/-- The second width derivative of the AdS3 entropy kernel. -/
noncomputable def ads3EntropyFourierKernelSecondDeriv (R G k ell : ℝ) : ℝ :=
  R / (2 * G * k ^ 3) *
    (ads3EntropyKernelNumeratorSecondDeriv k ell / ell -
      2 * ads3EntropyKernelNumeratorDeriv k ell / ell ^ 2 +
      2 * ads3EntropyKernelNumerator k ell / ell ^ 3)

/-- The paper's Fourier kernel has its displayed first derivative away from
zero interval width. -/
@[zil_level bridge_theorem]
lemma ads3EntropyFourierKernel_hasDerivAt (R G k ell : ℝ) (hell : ell ≠ 0) :
    HasDerivAt (ads3EntropyFourierKernel R G k)
      (ads3EntropyFourierKernelDeriv R G k ell) ell := by
  have hquot := (ads3EntropyKernelNumerator_hasDerivAt k ell).div
    (hasDerivAt_id ell) hell
  unfold ads3EntropyFourierKernel ads3EntropyFourierKernelDeriv
  convert hquot.const_mul (R / (2 * G * k ^ 3)) using 1 <;>
    first
      | rfl
      | (ext x; simp only [Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply,
          Pi.add_apply, Pi.div_apply]; ring)
      | (simp only [id_eq]; field_simp [hell] <;> ring)

/-- The first-derivative expression has the displayed second derivative away
from zero interval width. -/
@[zil_level bridge_theorem]
lemma ads3EntropyFourierKernelDeriv_hasDerivAt (R G k ell : ℝ) (hell : ell ≠ 0) :
    HasDerivAt (ads3EntropyFourierKernelDeriv R G k)
      (ads3EntropyFourierKernelSecondDeriv R G k ell) ell := by
  have hfirst := (ads3EntropyKernelNumeratorDeriv_hasDerivAt k ell).div
    (hasDerivAt_id ell) hell
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ell) ell := by
    simpa using hasDerivAt_pow 2 ell
  have hsecond := (ads3EntropyKernelNumerator_hasDerivAt k ell).div hsq
    (pow_ne_zero 2 hell)
  unfold ads3EntropyFourierKernelDeriv ads3EntropyFourierKernelSecondDeriv
  convert (hfirst.sub hsecond).const_mul (R / (2 * G * k ^ 3)) using 1 <;>
    first
      | rfl
      | (ext x; simp only [Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply,
          Pi.add_apply, Pi.div_apply]; ring)
      | (simp only [id_eq]; field_simp [hell] <;> ring)

/-- **[Nozaki et al. Eq. (3.9)]** The exact second derivative of the
nonlocal Fourier kernel satisfies the AdS radial entropy equation
`K'' + (k²/4 - 2/ell²)K = 0`. -/
@[zil_level physical_theorem]
lemma ads3EntropyFourierKernel_radialEquation (R G k ell : ℝ) (hell : ell ≠ 0) :
    ads3EntropyFourierKernelSecondDeriv R G k ell +
      (k ^ 2 / 4 - 2 / ell ^ 2) * ads3EntropyFourierKernel R G k ell = 0 := by
  unfold ads3EntropyFourierKernelSecondDeriv ads3EntropyFourierKernel
    ads3EntropyKernelNumeratorSecondDeriv ads3EntropyKernelNumeratorDeriv
    ads3EntropyKernelNumerator
  field_simp [hell]
  ring

/-! ## C. Einstein boundary modes induce both entropy evolution equations -/

/-- The Fourier entropy mode obtained by multiplying the paper's nonlocal
kernel by a normalizable boundary metric mode `H(k,t)`. -/
noncomputable def ads3EntropyFourierMode
    (R G k ell : ℝ) (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  ads3EntropyFourierKernel R G k ell * H t

/-- A boundary mode with `H'' + k²H = 0` induces the same massless time-mode
equation for the entropy Fourier mode, with both differentiations witnessed by
`HasDerivAt`. -/
@[zil_level bridge_theorem]
lemma ads3EntropyFourierMode_timeEquation
    (R G k ell : ℝ) (H dH : ℝ → ℝ) (t ddH : ℝ)
    (hH : HasDerivAt H (dH t) t) (hdH : HasDerivAt dH ddH t)
    (hwave : ddH + k ^ 2 * H t = 0) :
    HasDerivAt (ads3EntropyFourierMode R G k ell H)
        (ads3EntropyFourierKernel R G k ell * dH t) t ∧
      HasDerivAt (fun s => ads3EntropyFourierKernel R G k ell * dH s)
        (ads3EntropyFourierKernel R G k ell * ddH) t ∧
      ads3EntropyFourierKernel R G k ell * ddH +
        k ^ 2 * ads3EntropyFourierMode R G k ell H t = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact hH.const_mul (ads3EntropyFourierKernel R G k ell)
  · exact hdH.const_mul (ads3EntropyFourierKernel R G k ell)
  · unfold ads3EntropyFourierMode
    linear_combination ads3EntropyFourierKernel R G k ell * hwave

/-- **[Nozaki et al. Eqs. (3.9)--(3.11)]** A normalizable pure-gravity AdS3
boundary mode obeying its Einstein-derived wave equation produces an entropy
mode with both the boundary-time wave equation and the independent radial
equation.  The statement includes the actual first and second derivative
witnesses in both variables. -/
@[zil_level physical_theorem]
lemma ads3EinsteinMode_induces_entropyDynamics
    (R G k ell : ℝ) (H dH : ℝ → ℝ) (t ddH : ℝ)
    (hell : ell ≠ 0) (hH : HasDerivAt H (dH t) t)
    (hdH : HasDerivAt dH ddH t) (hwave : ddH + k ^ 2 * H t = 0) :
    (ads3EntropyFourierKernel R G k ell * ddH +
        k ^ 2 * ads3EntropyFourierMode R G k ell H t = 0) ∧
      (ads3EntropyFourierKernelSecondDeriv R G k ell * H t +
        (k ^ 2 / 4 - 2 / ell ^ 2) *
          ads3EntropyFourierMode R G k ell H t = 0) ∧
      HasDerivAt (ads3EntropyFourierMode R G k ell H)
        (ads3EntropyFourierKernel R G k ell * dH t) t ∧
      HasDerivAt (fun s => ads3EntropyFourierKernel R G k ell * dH s)
        (ads3EntropyFourierKernel R G k ell * ddH) t ∧
      HasDerivAt (fun width => ads3EntropyFourierMode R G k width H t)
        (ads3EntropyFourierKernelDeriv R G k ell * H t) ell ∧
      HasDerivAt
        (fun width => ads3EntropyFourierKernelDeriv R G k width * H t)
        (ads3EntropyFourierKernelSecondDeriv R G k ell * H t) ell := by
  have htime := ads3EntropyFourierMode_timeEquation R G k ell H dH t ddH hH hdH hwave
  have hradial := ads3EntropyFourierKernel_radialEquation R G k ell hell
  refine ⟨htime.2.2, ?_, htime.1, htime.2.1, ?_, ?_⟩
  · unfold ads3EntropyFourierMode
    linear_combination H t * hradial
  · simpa [ads3EntropyFourierMode] using
      (ads3EntropyFourierKernel_hasDerivAt R G k ell hell).mul_const (H t)
  · exact (ads3EntropyFourierKernelDeriv_hasDerivAt R G k ell hell).mul_const (H t)

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics

end

/- ZIL-BEGIN entanglement-dynamics-from-einstein -/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics

zil attach ads3LeadingEntropy_firstLaw where
  formalizes @ "claim:the-fefferman-graham-boundary-stress-normalization-and-the\
    -radius-to-width-conversion-close-the-leading-ads-three-entanglement-first-law",
  supported_by @ "paper:nozaki-numasawa-prudenziati-takayanagi-arxiv-1304-7100v2\
    -equations-2-5-2-9-3-24",
  caveat @ "claim:leading-small-interval-homogeneous-term-not-the-full-finite-width-entropy"

zil attach rtAreaEntropy_firstOrderVariation where
  formalizes @ "claim:the-first-order-induced-area-contraction-enters-through-the\
    -existing-ryu-takayanagi-area-over-four-G-carrier-with-the-paper-one-over\
    -eight-G-normalization",
  supported_by @ "paper:nozaki-numasawa-prudenziati-takayanagi-arxiv-1304-7100v2\
    -equation-2-4",
  caveat @ "claim:first-order-extremal-surface-variation-not-a-nonlinear-or\
    -quantum-corrected-entropy-functional"

zil attach ads3EntropyFourierKernel_radialEquation where
  formalizes @ "claim:the-pure-gravity-ads-three-entanglement-fourier-kernel\
    -satisfies-the-paper-radial-evolution-equation-with-actual-width-derivatives",
  supported_by @ "paper:nozaki-numasawa-prudenziati-takayanagi-arxiv-1304-7100v2\
    -equations-3-8-3-9",
  caveat @ "claim:pure-gravity-ads-three-sector-away-from-zero-interval-width"

zil attach ads3EinsteinMode_induces_entropyDynamics where
  formalizes @ "claim:a-normalizable-boundary-mode-obeying-the-pure-ads-three\
    -linearized-einstein-wave-equation-induces-entanglement-entropy-modes\
    -obeying-both-time-and-radial-equations",
  supported_by @ "paper:nozaki-numasawa-prudenziati-takayanagi-arxiv-1304-7100v2\
    -equations-3-5-3-8-3-11",
  caveat @ "claim:forward-linearized-einstein-to-entanglement-direction-not-a\
    -converse-or-nonlinear-einstein-derivation"

zil_file_contract physlib.einsteinEntanglementDynamics where
  promises "The Fefferman--Graham boundary-stress normalization, the radius-to\
    -width-correct leading AdS3 entanglement first law, and the actual time/radial\
    differential equations induced by a pure-gravity normalizable linearized\
    -Einstein boundary mode."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.\
      RyuTakayanagiFormulaAlgebra.rtAreaEntropy"
  ]
  forbids_substitutes [
    "reversing the paper's Einstein-implies-entropy-equations direction",
    "promoting the leading small-interval term to the full finite-width entropy",
    "claiming the pure-gravity AdS3 equations include Einstein--scalar sources\
      or nonlinear backreaction"
  ]
  witnessed_by [
    rtAreaEntropy_firstOrderVariation,
    fgBoundaryStressCoefficient_two,
    roundBallEntanglingTemperature_two_half_width,
    ads3LeadingEntropy_firstLaw,
    ads3EntropyKernelNumerator_hasDerivAt,
    ads3EntropyKernelNumeratorDeriv_hasDerivAt,
    ads3EntropyFourierKernel_hasDerivAt,
    ads3EntropyFourierKernelDeriv_hasDerivAt,
    ads3EntropyFourierKernel_radialEquation,
    ads3EntropyFourierMode_timeEquation,
    ads3EinsteinMode_induces_entropyDynamics
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.einsteinEntanglementDynamics
