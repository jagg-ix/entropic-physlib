/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronWaveFunctionLink
public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Mathlib.Topology.MetricSpace.Thickening
meta import Zil

/-!
# Certified self-bound three-dimensional Schrödinger--Newton PDE carrier

This file assembles, without reimplementing the analytic components, one common
carrier for a real three-dimensional Schrödinger--Newton profile.  A
`CertifiedSelfBoundProfile3` contains a normalized compactly supported Schwartz
profile and an explicit certificate that it solves the stationary nonlinear
Hartree equation at the inferred coupling `G = ħ c σ₀⁴`.  From that certificate
the file derives:

* the full pointwise time-dependent Schrödinger--Newton equation for the standing wave;
* time-independent Born and spinor densities;
* total charge quantized by the existing winding law `Q = n / 3`;
* the internal spectral clock `ħ ω = E`;
* the exact Pauli spin-`1/2` Casimir;
* Newtonian self-interaction and a state-independent energy floor for every
  normalized compactly supported Schwartz perturbation;
* the distributional weak-field Einstein `00` equation and uniqueness of its
  homogeneous `Ḣ¹` Poisson solution.

## Honest scope

The nonlinear stationary profile is certificate data.  This file does not
claim a concentration-compactness construction of a nonzero ground state.
The perturbation theorem is energetic no-collapse/coercivity on the normalized
Schwartz core, not orbital or asymptotic stability.  The geometry theorem is
the static scalar weak-field Einstein `00` sector, not nonlinear dynamical
Einstein backreaction.  These distinctions are recorded in the ZIL contract.
-/

set_option autoImplicit false

open Filter MeasureTheory SchwartzMap Topology
open scoped ENNReal Space Matrix
open Space

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

/-- The complex Schwartz Born density `ψ²`, assembled with the existing
continuous-linear-map operations rather than a duplicate Schwartz proof. -/
noncomputable def bornDensitySchwartz (ψ : 𝓢(Space 3, ℝ)) :
    𝓢(Space 3, ℂ) :=
  (SchwartzMap.smulLeftCLM ℝ (ψ : Space 3 → ℝ) ψ).postcompCLM Complex.ofRealCLM

@[simp, zil_level bridge_theorem]
lemma bornDensitySchwartz_apply (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    bornDensitySchwartz ψ x = ((ψ x ^ 2 : ℝ) : ℂ) := by
  rw [bornDensitySchwartz, SchwartzMap.postcompCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]
  simp [pow_two]

/-- The real Born density used by the Hartree/Newton energy carriers. -/
noncomputable def bornDensity (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) : ℝ :=
  ψ x ^ 2

/-! ## A.1. The complete `H¹` Born density on the Newtonian `Space 3` carrier -/

/-- Canonical measurable representative of a complete `H¹(ℝ³)` Born
density, transported through the repository's existing linear chart from
Mathlib's Euclidean space to Physlib's `Space 3`.

The `AEMeasurable.mk` operation changes the physical density only on a null
set.  Naming the representative is necessary because the general-density HLS
theorem is stated for everywhere-measurable functions, while an `Lp` field
naturally supplies only an almost-everywhere measurable representative. -/
noncomputable def hOneBornDensityOnSpace
    (u : EuclideanHOneThree) : Space 3 → ℝ :=
  fun x =>
    (integrable_hOneBornDensityReal u).aestronglyMeasurable.mk
      (hOneBornDensityReal u) (euclideanToSpaceThree.symm x)

lemma measurable_hOneBornDensityOnSpace
    (u : EuclideanHOneThree) :
    Measurable (hOneBornDensityOnSpace u) :=
  (integrable_hOneBornDensityReal u).aestronglyMeasurable.measurable_mk.comp
    euclideanToSpaceThree.symm.continuous.measurable

/-- The actual real Newtonian self-energy of the complete `H¹` Born density
on the shared `Space 3` carrier. -/
noncomputable def hOneNewtonianSelfEnergy
    (u : EuclideanHOneThree) : ℝ :=
  newtonianSelfEnergy (hOneBornDensityOnSpace u)

/-- The explicit model-specific compactness input left after the abstract
energy-split direct method: along the selected subsequence, the transported
Born densities converge strongly in `L^(6/5)` and their `L^(6/5)` masses
converge to the limiting density's mass.  Finiteness fields make every
singular Newton kernel Bochner-integrable.

This predicate deliberately does not claim that unlocalized weak `H¹`
convergence implies the condition.  In applications it is supplied by the
local Rellich/concentration-compactness step. -/
def HOneBornLSixFifthsConverges
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree) : Prop :=
  (∀ n,
    ∫⁻ x, ENNReal.ofReal
      |hOneBornDensityOnSpace (u n) x| ^ ((6 : ℝ) / 5) ≠ ∞) ∧
  (∫⁻ x, ENNReal.ofReal
    |hOneBornDensityOnSpace v x| ^ ((6 : ℝ) / 5) ≠ ∞) ∧
  (∀ n,
    ∫⁻ x, ENNReal.ofReal
      |hOneBornDensityOnSpace (u n) x -
        hOneBornDensityOnSpace v x| ^ ((6 : ℝ) / 5) ≠ ∞) ∧
  Tendsto
    (fun n =>
      ∫⁻ x, ENNReal.ofReal
        |hOneBornDensityOnSpace (u n) x -
          hOneBornDensityOnSpace v x| ^ ((6 : ℝ) / 5))
    atTop (𝓝 0) ∧
  Tendsto
    (fun n =>
      ∫⁻ x, ENNReal.ofReal
        |hOneBornDensityOnSpace (u n) x| ^ ((6 : ℝ) / 5))
    atTop
    (𝓝 (∫⁻ x, ENNReal.ofReal
      |hOneBornDensityOnSpace v x| ^ ((6 : ℝ) / 5)))

/-! ## A.2. Localized Rellich plus recentering closes the Hartree topology -/

/-- The exact `L¹`--`L³` interpolation inequality for the exponent used by
the Newton kernel:

`∫ f^(6/5) ≤ (∫ f)^(9/10) (∫ f³)^(1/10)`.

The proof is Hölder with conjugate exponents `10/9` and `10`.  It is stated
for the genuine continuum measure and is used below with the absolute
difference of two Born densities. -/
@[zil_level physical_theorem]
theorem lintegral_one_three_interpolation
    (f : Space 3 → ℝ≥0∞) (hf : AEMeasurable f volume) :
    ∫⁻ x, f x ^ ((6 : ℝ) / 5) ≤
      (∫⁻ x, f x) ^ ((9 : ℝ) / 10) *
        (∫⁻ x, f x ^ (3 : ℝ)) ^ ((1 : ℝ) / 10) := by
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume : Measure (Space 3))
    (p := (10 : ℝ) / 9) (q := (10 : ℝ))
    (Real.holderConjugate_iff.mpr (by constructor <;> norm_num))
    (hf.pow_const ((9 : ℝ) / 10)) (hf.pow_const ((3 : ℝ) / 10))
  have hmul (x : Space 3) :
      f x ^ ((9 : ℝ) / 10) * f x ^ ((3 : ℝ) / 10) =
        f x ^ ((6 : ℝ) / 5) := by
    rw [← ENNReal.rpow_add_of_nonneg ((9 : ℝ) / 10) ((3 : ℝ) / 10)
      (by norm_num) (by norm_num)]
    norm_num
  have hpone (x : Space 3) :
      (f x ^ ((9 : ℝ) / 10)) ^ ((10 : ℝ) / 9) = f x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hpthree (x : Space 3) :
      (f x ^ ((3 : ℝ) / 10)) ^ (10 : ℝ) = f x ^ (3 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp_rw [Pi.mul_apply, hmul, hpone, hpthree] at hholder
  norm_num at hholder ⊢
  exact hholder

/-- Strong `L¹` convergence together with one finite uniform `L³` bound
upgrades to strong `L^(6/5)` convergence.  This is the interpolation step
between localized Rellich compactness and Newton/Hartree continuity. -/
@[zil_level physical_theorem]
theorem lintegral_lsixFifths_tendsto_zero_of_lone_of_lthree_bound
    (f : ℕ → Space 3 → ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) volume)
    (hL1 : Tendsto (fun n => ∫⁻ x, f n x) atTop (𝓝 0))
    (M : ℝ≥0∞) (hMtop : M ≠ ∞)
    (hL3 : ∀ n, ∫⁻ x, f n x ^ (3 : ℝ) ≤ M) :
    Tendsto (fun n => ∫⁻ x, f n x ^ ((6 : ℝ) / 5))
      atTop (𝓝 0) := by
  have hsmall :
      Tendsto (fun n => (∫⁻ x, f n x) ^ ((9 : ℝ) / 10))
        atTop (𝓝 0) := by
    simpa using hL1.ennrpow_const ((9 : ℝ) / 10)
  have hMpow : M ^ ((1 : ℝ) / 10) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMtop
  have hupper :
      Tendsto
        (fun n =>
          (∫⁻ x, f n x) ^ ((9 : ℝ) / 10) *
            M ^ ((1 : ℝ) / 10))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hsmall (Or.inr hMpow)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have heventually :=
    (ENNReal.tendsto_nhds_zero.mp hupper) ε hε
  filter_upwards [heventually] with n hn
  exact
    (lintegral_one_three_interpolation (f n) (hf n)).trans
      ((mul_le_mul_of_nonneg_left
        (ENNReal.rpow_le_rpow (hL3 n) (by norm_num)) zero_le).trans hn)

/-- Localized Rellich convergence for a sequence of nonnegative density
differences: on every fixed closed ball the `L¹` error tends to zero. -/
def LocalizedRellichLOne
    (f : ℕ → Space 3 → ℝ≥0∞) : Prop :=
  ∀ R : ℕ,
    Tendsto
      (fun n => ∫⁻ x in Metric.closedBall (0 : Space 3) R, f n x)
      atTop (𝓝 0)

/-- Recentered concentration compactness in its exact tail form.  After the
translation centers have been chosen, the `L¹` mass outside growing balls
vanishes uniformly in the sequence. -/
def RecenteredLOneTight
    (f : ℕ → Space 3 → ℝ≥0∞) : Prop :=
  Tendsto
    (fun R : ℕ =>
      ⨆ n : ℕ,
        ∫⁻ x in (Metric.closedBall (0 : Space 3) R)ᶜ, f n x)
    atTop (𝓝 0)

/-- **Local-to-global Rellich gluing.** Local `L¹` convergence and uniform
recentered tails imply global `L¹` convergence.  The proof splits the
Lebesgue integral into a closed ball and its complement and chooses the
same radius for every member of the sequence. -/
@[zil_level physical_theorem]
theorem lintegral_tendsto_zero_of_localizedRellich_of_recenteredTight
    (f : ℕ → Space 3 → ℝ≥0∞)
    (hlocal : LocalizedRellichLOne f)
    (htight : RecenteredLOneTight f) :
    Tendsto (fun n => ∫⁻ x, f n x) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · filter_upwards [] with n
    simpa [hεtop] using
      (show (∫⁻ x, f n x) ≤ (∞ : ℝ≥0∞) from le_top)
  have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨R, hR⟩ :=
    (ENNReal.tendsto_atTop_zero.mp htight) (ε / 2) hhalf
  have htail :
      (⨆ n : ℕ,
        ∫⁻ x in (Metric.closedBall (0 : Space 3) R)ᶜ, f n x) ≤ ε / 2 :=
    hR R le_rfl
  have hlocEventually :=
    (ENNReal.tendsto_nhds_zero.mp (hlocal R)) (ε / 2) hhalf
  filter_upwards [hlocEventually] with n hn
  rw [← lintegral_add_compl (f n) measurableSet_closedBall]
  calc
    (∫⁻ x in Metric.closedBall (0 : Space 3) R, f n x) +
          ∫⁻ x in (Metric.closedBall (0 : Space 3) R)ᶜ, f n x
        ≤ ε / 2 + ε / 2 := add_le_add hn ((le_iSup (fun k : ℕ =>
          ∫⁻ x in (Metric.closedBall (0 : Space 3) R)ᶜ, f k x) n).trans htail)
    _ = ε := ENNReal.add_halves ε

/-- Strong `L^(6/5)` convergence implies convergence of the corresponding
`L^(6/5)` masses.  This fact is derived through Mathlib's complete `Lp`
carrier and continuity of its extended norm; it is not an extra
concentration-compactness assumption. -/
theorem lsixFifths_mass_tendsto_of_diff
    (ρ : ℕ → Space 3 → ℝ) (σ : Space 3 → ℝ)
    (hρ : ∀ n, Measurable (ρ n)) (hσ : Measurable σ)
    (hρtop : ∀ n,
      ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop :
      ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hdiff :
      Tendsto
        (fun n =>
          ∫⁻ x, ENNReal.ofReal |ρ n x - σ x| ^ ((6 : ℝ) / 5))
        atTop (𝓝 0)) :
    Tendsto
        (fun n =>
          ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5))
        atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5))) := by
  let p : ℝ≥0∞ := ENNReal.ofReal ((6 : ℝ) / 5)
  have hp0 : p ≠ 0 := by simp [p]
  have hptop : p ≠ ∞ := by simp [p]
  have hpto : p.toReal = (6 : ℝ) / 5 := by norm_num [p]
  letI : Fact (1 ≤ p) := ⟨by norm_num [p]⟩
  have hρmem : ∀ n, MemLp (ρ n) p volume := by
    intro n
    refine ⟨(hρ n).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpto]
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
    simpa only [← ofReal_norm, Real.norm_eq_abs] using hρtop n
  have hσmem : MemLp σ p volume := by
    refine ⟨hσ.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpto]
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
    simpa only [← ofReal_norm, Real.norm_eq_abs] using hσtop
  have heLpDiff :
      Tendsto (fun n => eLpNorm (ρ n - σ) p volume) atTop (𝓝 0) := by
    have hrpow := hdiff.ennrpow_const ((5 : ℝ) / 6)
    have heq (n : ℕ) :
        eLpNorm (ρ n - σ) p volume =
          (∫⁻ x, ENNReal.ofReal |ρ n x - σ x| ^ ((6 : ℝ) / 5)) ^
            ((5 : ℝ) / 6) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpto]
      rw [show (1 : ℝ) / ((6 : ℝ) / 5) = (5 : ℝ) / 6 by norm_num]
      congr 1
      apply lintegral_congr
      intro x
      simp only [Pi.sub_apply, ← ofReal_norm, Real.norm_eq_abs]
    have hz : (0 : ℝ≥0∞) ^ ((5 : ℝ) / 6) = 0 :=
      ENNReal.zero_rpow_of_pos (by norm_num)
    rw [hz] at hrpow
    simpa only [heq] using hrpow
  have hLp :
      Tendsto (fun n => (hρmem n).toLp (ρ n)) atTop
        (𝓝 (hσmem.toLp σ)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    exact heLpDiff
  have henorm :=
    (continuous_enorm.tendsto (hσmem.toLp σ)).comp hLp
  change Tendsto (fun n => ‖(hρmem n).toLp (ρ n)‖ₑ) atTop
      (𝓝 ‖hσmem.toLp σ‖ₑ) at henorm
  have hnorms :
      Tendsto (fun n => eLpNorm (ρ n) p volume) atTop
        (𝓝 (eLpNorm σ p volume)) := by
    convert henorm using 1
    · funext n
      exact (Lp.enorm_toLp (hρmem n)).symm
    · exact congrArg 𝓝 (Lp.enorm_toLp hσmem).symm
  have hpowers :
      Tendsto (fun n => eLpNorm (ρ n) p volume ^ ((6 : ℝ) / 5))
        atTop (𝓝 (eLpNorm σ p volume ^ ((6 : ℝ) / 5))) :=
    (ENNReal.continuous_rpow_const.tendsto (eLpNorm σ p volume)).comp hnorms
  let pnn : NNReal := ⟨(6 : ℝ) / 5, by norm_num⟩
  have hpnn0 : pnn ≠ 0 := by
    intro h
    have h' := congrArg (fun q : NNReal => (q : ℝ)) h
    change (6 : ℝ) / 5 = 0 at h'
    norm_num at h'
  have hpnn : (pnn : ENNReal) = p := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hpnnReal : (pnn : ℝ) = (6 : ℝ) / 5 := by
    rfl
  have hmassρ (n : ℕ) :
      ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5) =
        eLpNorm (ρ n) p volume ^ ((6 : ℝ) / 5) := by
    simpa only [hpnn, hpnnReal, ← ofReal_norm, Real.norm_eq_abs] using
      (eLpNorm_nnreal_pow_eq_lintegral
        (μ := volume) (f := ρ n) (p := pnn) hpnn0).symm
  have hmassσ :
      ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5) =
        eLpNorm σ p volume ^ ((6 : ℝ) / 5) := by
    simpa only [hpnn, hpnnReal, ← ofReal_norm, Real.norm_eq_abs] using
      (eLpNorm_nnreal_pow_eq_lintegral
        (μ := volume) (f := σ) (p := pnn) hpnn0).symm
  simpa only [hmassρ, hmassσ] using hpowers

/-- Absolute difference of the transported complete-`H¹` Born densities. -/
noncomputable def hOneBornDifference
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (n : ℕ) (x : Space 3) : ℝ≥0∞ :=
  ENNReal.ofReal
    |hOneBornDensityOnSpace (u n) x - hOneBornDensityOnSpace v x|

/-- The concrete output data of the localized Rellich and recentering
stage.  Its fields are analytic estimates rather than theorem certificates:

* local `L¹` convergence on every closed ball;
* uniform `L¹` tail decay after recentering;
* the finite uniform `L³` density-difference bound supplied by the
  three-dimensional `H¹ → L⁶` Sobolev estimate; and
* finite `L^(6/5)` masses for the sequence and limit.

The theorem below derives all remaining fields of
`HOneBornLSixFifthsConverges`, including global convergence and convergence
of the masses. -/
structure HOneRecenteredLocalizedRellichData
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree) where
  localRellich :
    LocalizedRellichLOne (hOneBornDifference u v)
  recenteredTight :
    RecenteredLOneTight (hOneBornDifference u v)
  differenceLOneFinite : ∀ n,
    ∫⁻ x, hOneBornDifference u v n x ≠ ∞
  cubicBound : ℝ≥0∞
  cubicBound_ne_top : cubicBound ≠ ∞
  differenceLThreeBound : ∀ n,
    ∫⁻ x, (hOneBornDifference u v n x) ^ (3 : ℝ) ≤ cubicBound
  sequenceLSixFifthsFinite : ∀ n,
    ∫⁻ x, ENNReal.ofReal
      |hOneBornDensityOnSpace (u n) x| ^ ((6 : ℝ) / 5) ≠ ∞
  limitLSixFifthsFinite :
    ∫⁻ x, ENNReal.ofReal
      |hOneBornDensityOnSpace v x| ^ ((6 : ℝ) / 5) ≠ ∞

/-- **Localized Rellich/concentration compactness closes the Newton
interaction topology.**  Once the sequence has been recentered, local
Rellich `L¹` convergence and uniform tail control give global `L¹`
convergence of the Born densities.  The uniform cubic bound interpolates
that convergence to strong `L^(6/5)`, and `Lp` completeness proves
convergence of the `L^(6/5)` masses.  Therefore the exact predicate consumed
by the Hartree-continuity theorem follows rather than being supplied. -/
@[zil_level physical_theorem]
theorem hOneBornLSixFifthsConverges_of_recentered_localizedRellich
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : HOneRecenteredLocalizedRellichData u v) :
    HOneBornLSixFifthsConverges u v := by
  have hmeas : ∀ n,
      AEMeasurable (hOneBornDifference u v n) volume := by
    intro n
    exact ENNReal.measurable_ofReal.comp
      ((measurable_hOneBornDensityOnSpace (u n)).sub
        (measurable_hOneBornDensityOnSpace v)).abs |>.aemeasurable
  have hL1 :
      Tendsto (fun n => ∫⁻ x, hOneBornDifference u v n x)
        atTop (𝓝 0) :=
    lintegral_tendsto_zero_of_localizedRellich_of_recenteredTight
      (hOneBornDifference u v) h.localRellich h.recenteredTight
  have hdiff :
      Tendsto
        (fun n =>
          ∫⁻ x, hOneBornDifference u v n x ^ ((6 : ℝ) / 5))
        atTop (𝓝 0) :=
    lintegral_lsixFifths_tendsto_zero_of_lone_of_lthree_bound
      (hOneBornDifference u v) hmeas hL1 h.cubicBound
      h.cubicBound_ne_top h.differenceLThreeBound
  have hdifftop : ∀ n,
      ∫⁻ x, hOneBornDifference u v n x ^ ((6 : ℝ) / 5) ≠ ∞ := by
    intro n
    apply ne_of_lt
    refine lt_of_le_of_lt
      (lintegral_one_three_interpolation
        (hOneBornDifference u v n) (hmeas n)) ?_
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (h.differenceLOneFinite n))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ne_of_lt
          ((h.differenceLThreeBound n).trans_lt h.cubicBound_ne_top.lt_top)))
  have hmass :=
    lsixFifths_mass_tendsto_of_diff
      (fun n => hOneBornDensityOnSpace (u n))
      (hOneBornDensityOnSpace v)
      (fun n => measurable_hOneBornDensityOnSpace (u n))
      (measurable_hOneBornDensityOnSpace v)
      h.sequenceLSixFifthsFinite h.limitLSixFifthsFinite
      (by
        simpa [hOneBornDifference] using hdiff)
  exact ⟨h.sequenceLSixFifthsFinite, h.limitLSixFifthsFinite,
    (by
      intro n
      simpa [hOneBornDifference] using hdifftop n),
    (by simpa [hOneBornDifference] using hdiff), hmass⟩

/-- **The missing Hartree closure on the complete `H¹` carrier.**
Strong `L^(6/5)` convergence of the transported canonical Born densities
implies convergence of their actual real Newtonian self-energies.  This is
the concrete theorem that discharges the nonlinear interaction-convergence
premise in the energy-split direct method once the model's localized
Rellich/concentration-compactness estimate has produced
`HOneBornLSixFifthsConverges`. -/
@[zil_level physical_theorem]
theorem hOneNewtonianSelfEnergy_tendsto_of_lsixFifths
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : HOneBornLSixFifthsConverges u v) :
    Tendsto (fun n => hOneNewtonianSelfEnergy (u n)) atTop
      (𝓝 (hOneNewtonianSelfEnergy v)) := by
  exact newtonianSelfEnergy_tendsto_of_lsixFifths
    (fun n => hOneBornDensityOnSpace (u n))
    (hOneBornDensityOnSpace v)
    (fun n => measurable_hOneBornDensityOnSpace (u n))
    (measurable_hOneBornDensityOnSpace v)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- The attractive Newton/Hartree interaction appearing in the energy
split, with coupling `G`. -/
noncomputable def hOneAttractiveNewtonInteraction
    (G : ℝ) (u : EuclideanHOneThree) : ℝ :=
  -G * hOneNewtonianSelfEnergy u

/-- The same `L^(6/5)` density convergence supplies exactly the attractive
interaction convergence expected by
`hOne_tendsto_of_minimizing_energySplit`. -/
@[zil_level physical_theorem]
theorem hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths
    (G : ℝ) (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : HOneBornLSixFifthsConverges u v) :
    Tendsto (fun n => hOneAttractiveNewtonInteraction G (u n))
      atTop (𝓝 (hOneAttractiveNewtonInteraction G v)) := by
  exact tendsto_const_nhds.mul
    (hOneNewtonianSelfEnergy_tendsto_of_lsixFifths u v h)

/-- Localized Rellich and recentered concentration compactness now discharge
the complete Newtonian self-energy convergence premise directly. -/
@[zil_level physical_theorem]
theorem hOneNewtonianSelfEnergy_tendsto_of_recentered_localizedRellich
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : HOneRecenteredLocalizedRellichData u v) :
    Tendsto (fun n => hOneNewtonianSelfEnergy (u n)) atTop
      (𝓝 (hOneNewtonianSelfEnergy v)) :=
  hOneNewtonianSelfEnergy_tendsto_of_lsixFifths u v
    (hOneBornLSixFifthsConverges_of_recentered_localizedRellich u v h)

/-- The direct minimizing-sequence interaction conclusion: after
recentring, localized Rellich and the uniform Sobolev-density bound imply
convergence of the attractive Newton/Hartree term for every coupling. -/
@[zil_level physical_theorem]
theorem hOneAttractiveNewtonInteraction_tendsto_of_recentered_localizedRellich
    (G : ℝ) (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (h : HOneRecenteredLocalizedRellichData u v) :
    Tendsto (fun n => hOneAttractiveNewtonInteraction G (u n))
      atTop (𝓝 (hOneAttractiveNewtonInteraction G v)) :=
  hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths G u v
    (hOneBornLSixFifthsConverges_of_recentered_localizedRellich u v h)

/-- The pointwise stationary three-dimensional Schrödinger--Newton
Hamiltonian with the repository's continuum Laplacian and Newton convolution. -/
noncomputable def stationaryHamiltonian
    (G m hbar : ℝ) (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) : ℝ :=
  -(hbar ^ 2 / (2 * m)) * laplacianSchwartz ψ x -
    G * m ^ 2 * newtonianConvolutionPotential (bornDensity ψ) x * ψ x

/-- Certificate that `ψ` solves the nonlinear stationary
Schrödinger--Newton equation `H_G[ψ] = E ψ`. -/
def IsStationaryProfile (G m hbar E : ℝ) (ψ : 𝓢(Space 3, ℝ)) : Prop :=
  ∀ x, stationaryHamiltonian G m hbar ψ x = E * ψ x

/-- The standing-wave lift of a stationary spatial profile. -/
noncomputable def standingWave (E hbar : ℝ) (ψ : 𝓢(Space 3, ℝ))
    (t : ℝ) (x : Space 3) : ℂ :=
  spectralPhase E hbar t * (ψ x : ℂ)

@[zil_level bridge_theorem]
lemma standingWave_hasDerivAt (E hbar : ℝ) (ψ : 𝓢(Space 3, ℝ))
    (t : ℝ) (x : Space 3) :
    HasDerivAt (fun s => standingWave E hbar ψ s x)
      ((E : ℂ) / (Complex.I * hbar) * standingWave E hbar ψ t x) t := by
  simpa [standingWave, mul_assoc] using
    (hasDerivAt_spectralPhase E hbar t).mul_const (ψ x : ℂ)

/-- A stationary Schrödinger--Newton certificate lifts to the full pointwise
time-dependent nonlinear PDE. -/
@[zil_level physical_theorem]
lemma standingWave_solves_full_schrodingerNewton
    (G m hbar E : ℝ) (hhbar : hbar ≠ 0)
    (ψ : 𝓢(Space 3, ℝ)) (hprofile : IsStationaryProfile G m hbar E ψ)
    (t : ℝ) (x : Space 3) :
    (Complex.I * (hbar : ℂ)) *
        deriv (fun s => standingWave E hbar ψ s x) t =
      spectralPhase E hbar t * (stationaryHamiltonian G m hbar ψ x : ℂ) := by
  rw [(standingWave_hasDerivAt E hbar ψ t x).deriv, hprofile x]
  unfold standingWave
  push_cast
  have hhbarC : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hhbar
  field_simp [hhbarC]

/-! ## B. Local well-posedness on the complete continuum `H¹` carrier -/

/-- **Local existence for a nonlinear continuum `H¹(ℝ³)` evolution.**
Every continuously Fréchet differentiable autonomous generator on the
complete Bessel-energy carrier has a local classical trajectory through each
initial datum.

For the Schrödinger--Newton equation, this theorem discharges the ODE/Picard
part once the Hartree generator has been proved to map `H¹` to `H¹` and to be
`C¹`.  Those mapping estimates are analytic statements and are not hidden in
this theorem. -/
@[zil_level bridge_theorem]
theorem exists_local_hOnePDE_solution
    (V : EuclideanHOneThree → EuclideanHOneThree)
    (hV : ContDiff ℝ 1 V) (u₀ : EuclideanHOneThree) (t₀ : ℝ) :
    ∃ u : ℝ → EuclideanHOneThree, u t₀ = u₀ ∧ ∃ ε > 0,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt u (V (u t)) t := by
  exact hV.contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- **Local uniqueness on continuum `H¹(ℝ³)`.** Two trajectories of the
same `C¹` autonomous generator through the same state agree in a
neighborhood of the initial time.  The proof extracts the local Lipschitz
estimate from `C¹` regularity and applies Mathlib's ODE uniqueness theorem. -/
@[zil_level bridge_theorem]
theorem hOnePDE_solution_eventuallyEq
    (V : EuclideanHOneThree → EuclideanHOneThree)
    (hV : ContDiff ℝ 1 V) (u₀ : EuclideanHOneThree) (t₀ : ℝ)
    (u v : ℝ → EuclideanHOneThree)
    (hu₀ : u t₀ = u₀) (hv₀ : v t₀ = u₀)
    (hu : ∀ᶠ t in 𝓝 t₀, HasDerivAt u (V (u t)) t)
    (hv : ∀ᶠ t in 𝓝 t₀, HasDerivAt v (V (v t)) t) :
    u =ᶠ[𝓝 t₀] v := by
  obtain ⟨K, s, hs, hlip⟩ :=
    hV.contDiffAt.exists_lipschitzOnWith
  have huAt := hu.self_of_nhds
  have hvAt := hv.self_of_nhds
  have hus : ∀ᶠ t in 𝓝 t₀, u t ∈ s :=
    huAt.continuousAt.eventually (hu₀.symm ▸ hs)
  have hvs : ∀ᶠ t in 𝓝 t₀, v t ∈ s :=
    hvAt.continuousAt.eventually (hv₀.symm ▸ hs)
  apply ODE_solution_unique_of_eventually
    (v := fun _ => V) (s := fun _ => s) (K := K)
    (Filter.Eventually.of_forall fun _ => hlip)
    (hu.and hus) (hv.and hvs)
  exact hu₀.trans hv₀.symm

/-! ## C. Compact-sublevel orbital stability -/

/-- Uniform orbital stability relative to a conserved constraint set.  The
distance is the genuine `H¹(ℝ³)` metric distance to the full minimizing
orbit, so phase or translation symmetries can be represented by placing all
equivalent minimizers in `orbit`. -/
def IsUniformlyOrbitallyStableOn
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible orbit : Set EuclideanHOneThree) : Prop :=
  ∀ ε > 0, ∃ d > 0, ∀ u ∈ admissible,
    Metric.infDist u orbit < d →
      ∀ t, Metric.infDist (flow t u) orbit < ε

/-- **Cazenave--Lions compactness mechanism on continuum `H¹(ℝ³)`.**
The minimizing orbit is uniformly orbitally stable when

1. it is a nonempty compact set of exactly the constrained energy minimizers;
2. the energy is continuous and bounded below by the ground level;
3. the constrained unit low-energy sublevel is compact; and
4. the flow preserves both the constraint and the energy.

The proof derives, rather than assumes, a positive energy gap on every closed
set a fixed positive distance from the orbit.  Compactness gives a uniform
lower energy there, while compactness of the orbit gives a uniform
neighborhood on which the energy stays below that gap.  Conservation then
prevents the trajectory from crossing the separating shell.

For the unregularized Schrödinger--Newton flow the remaining model-specific
work is to derive the compact-sublevel premise modulo its phase/translation
symmetries from the joint `H¹`/Prokhorov theorem and to construct the
energy-preserving global flow. -/
@[zil_level bridge_theorem]
theorem uniform_orbitalStability_of_compact_energySublevel
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible orbit : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ) (groundEnergy : ℝ)
    (horbit : IsCompact orbit) (horbit_ne : orbit.Nonempty)
    (henergy : Continuous energy)
    (hminimizers : ∀ u,
      u ∈ orbit ↔ u ∈ admissible ∧ energy u = groundEnergy)
    (hground_le : ∀ u ∈ admissible, groundEnergy ≤ energy u)
    (hcompactSublevel :
      IsCompact {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1})
    (hflow_admissible : ∀ t u,
      u ∈ admissible → flow t u ∈ admissible)
    (hflow_energy : ∀ t u, energy (flow t u) = energy u) :
    IsUniformlyOrbitallyStableOn flow admissible orbit := by
  intro ε hε
  let K : Set EuclideanHOneThree :=
    {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} ∩
      {u | ε ≤ Metric.infDist u orbit}
  have hK : IsCompact K := by
    apply hcompactSublevel.inter_right
    exact isClosed_le continuous_const (Metric.continuous_infDist_pt orbit)
  have hstrict : ∀ u ∈ K, groundEnergy < energy u := by
    intro u hu
    have hle := hground_le u hu.1.1
    exact lt_of_le_of_ne hle fun heq => by
      have huorbit : u ∈ orbit :=
        (hminimizers u).2 ⟨hu.1.1, heq.symm⟩
      have hzero := Metric.infDist_zero_of_mem huorbit
      have : ε ≤ 0 := by simpa [hzero] using hu.2
      linarith
  obtain ⟨a, ha, haK⟩ :=
    hK.exists_forall_le' henergy.continuousOn hstrict
  let η : ℝ := min (a - groundEnergy) 1 / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hη_one : η ≤ 1 := by
    dsimp [η]
    linarith [min_le_right (a - groundEnergy) 1]
  have hη_a : groundEnergy + η < a := by
    dsimp [η]
    have hmin : min (a - groundEnergy) 1 ≤ a - groundEnergy :=
      min_le_left _ _
    linarith
  have horbit_open :
      orbit ⊆ {u | energy u < groundEnergy + η} := by
    intro u hu
    have heq := (hminimizers u).1 hu |>.2
    simp only [Set.mem_setOf_eq]
    linarith
  obtain ⟨d, hd, hthick⟩ :=
    horbit.exists_thickening_subset_open
      (isOpen_lt henergy continuous_const) horbit_open
  refine ⟨d, hd, ?_⟩
  intro u hu hnear t
  have huThick : u ∈ Metric.thickening d orbit :=
    (Metric.mem_thickening_iff_infDist_lt horbit_ne).2 hnear
  have henergy_u : energy u < groundEnergy + η :=
    hthick huThick
  have henergy_flow : energy (flow t u) < groundEnergy + η := by
    rw [hflow_energy]
    exact henergy_u
  by_contra hfar
  have hfar' : ε ≤ Metric.infDist (flow t u) orbit :=
    le_of_not_gt hfar
  have hflow_sublevel :
      energy (flow t u) ≤ groundEnergy + 1 := by
    linarith
  have hflowK : flow t u ∈ K :=
    ⟨⟨hflow_admissible t u hu, hflow_sublevel⟩, hfar'⟩
  have := haK _ hflowK
  linarith

/-- **Moment/norm-closure instantiation of the Cazenave--Lions mechanism.**
This theorem replaces the previously supplied compact low-energy sublevel by
quantitative continuum hypotheses:

* the sublevel is closed and bounded in the complete `H¹(ℝ³)` norm;
* its associated probability measures have a uniform finite first radial
  moment (after any model-specific recentering); and
* every selected joint weak-field/probability subsequence preserves the
  `H¹` norm.

The Euclidean concentration-compactness bridge derives strong compactness of
the sublevel, after which
`uniform_orbitalStability_of_compact_energySublevel` derives the positive
energy separation and uniform orbital stability.  The last norm-closure
premise is the explicit place where a concrete Hartree model must exclude
loss of kinetic/interaction energy; it is not a hidden compactness
certificate. -/
@[zil_level bridge_theorem]
theorem uniform_orbitalStability_of_firstMoment_normClosure
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible orbit : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ) (groundEnergy : ℝ)
    (bornMeasure :
      EuclideanHOneThree →
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (horbit : IsCompact orbit) (horbit_ne : orbit.Nonempty)
    (henergy : Continuous energy)
    (hminimizers : ∀ u,
      u ∈ orbit ↔ u ∈ admissible ∧ energy u = groundEnergy)
    (hground_le : ∀ u ∈ admissible, groundEnergy ≤ energy u)
    (hclosedSublevel :
      IsClosed {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1})
    (B : ℝ)
    (hboundedSublevel : ∀ u,
      u ∈ {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} →
      ‖u‖ ≤ B)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u,
      u ∈ {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} →
      ∫⁻ x, ENNReal.ofReal ‖x‖
        ∂((bornMeasure u :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n,
          u n ∈ {u | u ∈ admissible ∧
            energy u ≤ groundEnergy + 1}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖))
    (hflow_admissible : ∀ t u,
      u ∈ admissible → flow t u ∈ admissible)
    (hflow_energy : ∀ t u, energy (flow t u) = energy u) :
    IsUniformlyOrbitallyStableOn flow admissible orbit := by
  apply uniform_orbitalStability_of_compact_energySublevel
    flow admissible orbit energy groundEnergy horbit horbit_ne henergy
    hminimizers hground_le
  · exact
      isCompact_of_closed_bounded_firstMoment_and_normClosure
        {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1}
        bornMeasure hclosedSublevel B hboundedSublevel C hC hmoment
        hnormClosure
  · exact hflow_admissible
  · exact hflow_energy

/-- **Born-specialized continuum orbital stability.**  This removes the
arbitrary measure-valued adapter from
`uniform_orbitalStability_of_firstMoment_normClosure`: every low-energy
state is physically `L²` normalized, localization is the first moment of
its actual reconstructed `H¹` Born density, and strong compactness retains
that same Born law at the limiting field. -/
@[zil_level bridge_theorem]
theorem uniform_orbitalStability_of_hOneBornMoment_normClosure
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible orbit : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ) (groundEnergy : ℝ)
    (horbit : IsCompact orbit) (horbit_ne : orbit.Nonempty)
    (henergy : Continuous energy)
    (hminimizers : ∀ u,
      u ∈ orbit ↔ u ∈ admissible ∧ energy u = groundEnergy)
    (hground_le : ∀ u ∈ admissible, groundEnergy ≤ energy u)
    (hclosedSublevel :
      IsClosed {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1})
    (B : ℝ)
    (hboundedSublevel : ∀ u,
      u ∈ {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} →
      ‖u‖ ≤ B)
    (hnormalizedSublevel : ∀ u,
      u ∈ {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} →
      HOneLTwoNormalized u)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u,
      u ∈ {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} →
      ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n,
          u n ∈ {u | u ∈ admissible ∧
            energy u ≤ groundEnergy + 1}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖))
    (hflow_admissible : ∀ t u,
      u ∈ admissible → flow t u ∈ admissible)
    (hflow_energy : ∀ t u, energy (flow t u) = energy u) :
    IsUniformlyOrbitallyStableOn flow admissible orbit := by
  apply uniform_orbitalStability_of_compact_energySublevel
    flow admissible orbit energy groundEnergy horbit horbit_ne henergy
    hminimizers hground_le
  · exact
      isCompact_of_closed_bounded_hOneBornMoment_and_normClosure
        {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1}
        hclosedSublevel B hboundedSublevel hnormalizedSublevel C hC
        hmoment hnormClosure
  · exact hflow_admissible
  · exact hflow_energy

/-! ## D. Derived ground-state orbit and stability

The preceding theorem still accepted a compact nonempty minimizing orbit as
data.  The next layer removes that logical redundancy.  Once the admissible
family itself has been proved compact by the actual Born moment/no-loss
criterion, the extreme-value theorem constructs a ground state, its full
equal-energy minimizing orbit is a compact level set, and Cazenave--Lions
stability follows from conservation.
-/

/-- The full set of constrained energy minimizers.  It contains every
phase/translation representative that remains inside `admissible`; no
distinguished minimizer is chosen in this definition. -/
def HOneConstrainedEnergyMinimizers
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ) :
    Set EuclideanHOneThree :=
  {u | u ∈ admissible ∧ ∀ v ∈ admissible, energy u ≤ energy v}

/-- Once one constrained ground state is known, the order-defined minimizing
set is exactly its equal-energy level inside the constraint set. -/
lemma hOneConstrainedEnergyMinimizers_iff_eq_ground
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ)
    (groundState : EuclideanHOneThree)
    (hgroundState : groundState ∈ admissible)
    (hminimum : ∀ v ∈ admissible, energy groundState ≤ energy v)
    (u : EuclideanHOneThree) :
    u ∈ HOneConstrainedEnergyMinimizers admissible energy ↔
      u ∈ admissible ∧ energy u = energy groundState := by
  constructor
  · intro hu
    exact ⟨hu.1, le_antisymm (hu.2 groundState hgroundState)
      (hminimum u hu.1)⟩
  · rintro ⟨hu, heq⟩
    refine ⟨hu, ?_⟩
    intro v hv
    rw [heq]
    exact hminimum v hv

/-- A continuous energy on a nonempty compact constraint set attains its
minimum, and the complete minimizing orbit is itself compact. -/
@[zil_level bridge_theorem]
theorem hOneConstrainedEnergyMinimizers_nonempty_isCompact
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ)
    (hcompact : IsCompact admissible)
    (hne : admissible.Nonempty)
    (henergy : Continuous energy) :
    (HOneConstrainedEnergyMinimizers admissible energy).Nonempty ∧
      IsCompact (HOneConstrainedEnergyMinimizers admissible energy) := by
  obtain ⟨groundState, hgroundState, hminimum⟩ :=
    hcompact.exists_isMinOn hne henergy.continuousOn
  have hchar :
      HOneConstrainedEnergyMinimizers admissible energy =
        admissible ∩ {u | energy u = energy groundState} := by
    ext u
    rw [hOneConstrainedEnergyMinimizers_iff_eq_ground admissible energy
      groundState hgroundState hminimum]
    rfl
  constructor
  · exact ⟨groundState,
      (hOneConstrainedEnergyMinimizers_iff_eq_ground admissible energy
        groundState hgroundState hminimum groundState).2
        ⟨hgroundState, rfl⟩⟩
  · rw [hchar]
    exact hcompact.inter_right
      (isClosed_eq henergy continuous_const)

/-- **Ground-state attainment from the actual continuum Born law.**
Closedness, an `H¹` bound, physical `L²` normalization, a finite first
moment of `|ψ|²`, and no loss of the `H¹` norm make the admissible family
compact.  A continuous energy therefore has an attained global constrained
minimum.  The theorem does not accept a ground-state certificate. -/
@[zil_level bridge_theorem]
theorem exists_hOneBorn_energyMinimizer
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ)
    (hclosed : IsClosed admissible)
    (hne : admissible.Nonempty)
    (B : ℝ)
    (hbounded : ∀ u ∈ admissible, ‖u‖ ≤ B)
    (hnormalized : ∀ u ∈ admissible, HOneLTwoNormalized u)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u ∈ admissible,
      ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ admissible) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖))
    (henergy : Continuous energy) :
    ∃ groundState ∈ admissible,
      ∀ v ∈ admissible, energy groundState ≤ energy v := by
  have hcompact :
      IsCompact admissible :=
    isCompact_of_closed_bounded_hOneBornMoment_and_normClosure
      admissible hclosed B hbounded hnormalized C hC hmoment hnormClosure
  exact hcompact.exists_isMinOn hne henergy.continuousOn

/-- Compact admissibility and conservation derive, rather than assume, the
ground energy, the nonempty compact minimizing orbit, and its uniform
orbital stability. -/
@[zil_level bridge_theorem]
theorem exists_compact_hOne_minimizingOrbit_uniformlyStable
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ)
    (hcompact : IsCompact admissible)
    (hne : admissible.Nonempty)
    (henergy : Continuous energy)
    (hflow_admissible : ∀ t u,
      u ∈ admissible → flow t u ∈ admissible)
    (hflow_energy : ∀ t u, energy (flow t u) = energy u) :
    ∃ groundEnergy : ℝ,
      (HOneConstrainedEnergyMinimizers admissible energy).Nonempty ∧
      IsCompact (HOneConstrainedEnergyMinimizers admissible energy) ∧
      (∀ u, u ∈ HOneConstrainedEnergyMinimizers admissible energy ↔
        u ∈ admissible ∧ energy u = groundEnergy) ∧
      (∀ u ∈ admissible, groundEnergy ≤ energy u) ∧
      IsUniformlyOrbitallyStableOn flow admissible
        (HOneConstrainedEnergyMinimizers admissible energy) := by
  obtain ⟨groundState, hgroundState, hminimum⟩ :=
    hcompact.exists_isMinOn hne henergy.continuousOn
  let groundEnergy := energy groundState
  have hcharacterization :
      ∀ u, u ∈ HOneConstrainedEnergyMinimizers admissible energy ↔
        u ∈ admissible ∧ energy u = groundEnergy := by
    intro u
    exact hOneConstrainedEnergyMinimizers_iff_eq_ground admissible energy
      groundState hgroundState hminimum u
  have horbit :=
    hOneConstrainedEnergyMinimizers_nonempty_isCompact admissible energy
      hcompact hne henergy
  have hcompactSublevel :
      IsCompact
        {u | u ∈ admissible ∧ energy u ≤ groundEnergy + 1} := by
    exact hcompact.inter_right
      (isClosed_le henergy continuous_const)
  have hstable :
      IsUniformlyOrbitallyStableOn flow admissible
        (HOneConstrainedEnergyMinimizers admissible energy) := by
    exact uniform_orbitalStability_of_compact_energySublevel
      flow admissible (HOneConstrainedEnergyMinimizers admissible energy)
      energy groundEnergy horbit.2 horbit.1 henergy hcharacterization
      hminimum hcompactSublevel hflow_admissible hflow_energy
  exact ⟨groundEnergy, horbit.1, horbit.2, hcharacterization,
    hminimum, hstable⟩

/-- **Born-law direct method plus Cazenave--Lions stability.**  The actual
normalized `H¹` Born density supplies compactness, the extreme-value theorem
constructs the ground state and its entire compact minimizing orbit, and
constraint/energy conservation proves that orbit uniformly stable.  Thus
neither a ground state nor a minimizing orbit is an input.

The finite-moment/no-loss hypotheses remain the honest model-specific
concentration-compactness obligations; constructing the unregularized
Schrödinger--Newton flow and proving its conservation laws are separate. -/
@[zil_level physical_theorem]
theorem exists_hOneBorn_minimizingOrbit_uniformlyStable
    (flow : ℝ → EuclideanHOneThree → EuclideanHOneThree)
    (admissible : Set EuclideanHOneThree)
    (energy : EuclideanHOneThree → ℝ)
    (hclosed : IsClosed admissible)
    (hne : admissible.Nonempty)
    (B : ℝ)
    (hbounded : ∀ u ∈ admissible, ‖u‖ ≤ B)
    (hnormalized : ∀ u ∈ admissible, HOneLTwoNormalized u)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u ∈ admissible,
      ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ admissible) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖))
    (henergy : Continuous energy)
    (hflow_admissible : ∀ t u,
      u ∈ admissible → flow t u ∈ admissible)
    (hflow_energy : ∀ t u, energy (flow t u) = energy u) :
    ∃ groundEnergy : ℝ,
      (HOneConstrainedEnergyMinimizers admissible energy).Nonempty ∧
      IsCompact (HOneConstrainedEnergyMinimizers admissible energy) ∧
      (∀ u, u ∈ HOneConstrainedEnergyMinimizers admissible energy ↔
        u ∈ admissible ∧ energy u = groundEnergy) ∧
      (∀ u ∈ admissible, groundEnergy ≤ energy u) ∧
      IsUniformlyOrbitallyStableOn flow admissible
        (HOneConstrainedEnergyMinimizers admissible energy) := by
  have hcompact :
      IsCompact admissible :=
    isCompact_of_closed_bounded_hOneBornMoment_and_normClosure
      admissible hclosed B hbounded hnormalized C hC hmoment hnormClosure
  exact exists_compact_hOne_minimizingOrbit_uniformlyStable
    flow admissible energy hcompact hne henergy
    hflow_admissible hflow_energy

/-- A single carrier for the profile and the physical certificates needed by
the downstream charge, clock, spin, interaction, stability, and geometry
theorems.  In particular, `stationary` is an explicit analytic premise. -/
structure CertifiedSelfBoundProfile3 where
  hbar : ℝ
  c : ℝ
  sigma0 : ℝ
  mass : ℝ
  winding : ℤ
  energy : ℝ
  psi : 𝓢(Space 3, ℝ)
  spinor : Fin 2 → ℂ
  hbar_pos : 0 < hbar
  c_pos : 0 < c
  mass_pos : 0 < mass
  normalized : ∫⁻ x, ‖psi x‖ₑ ^ (2 : ℝ) = 1
  compactSupport : HasCompactSupport (psi : Space 3 → ℝ)
  spinor_normalized :
    Complex.normSq (spinor 0) + Complex.normSq (spinor 1) = 1
  stationary :
    IsStationaryProfile (hbar * c * sigma0 ^ 4) mass hbar energy psi

namespace CertifiedSelfBoundProfile3

/-- Newton's coupling inferred from the repository's screen scale. -/
noncomputable def inferredG (S : CertifiedSelfBoundProfile3) : ℝ :=
  S.hbar * S.c * S.sigma0 ^ 4

/-- The total Born probability mass. -/
noncomputable def probabilityMass (S : CertifiedSelfBoundProfile3) : ℝ :=
  (∫⁻ x, ‖S.psi x‖ₑ ^ (2 : ℝ)).toReal

/-- Electric charge in units of the elementary charge, generated by the
integer winding sector through `Q = n / 3`. -/
def topologicalCharge (S : CertifiedSelfBoundProfile3) : ℝ :=
  ((windingCharge S.winding : ℚ) : ℝ)

/-- The integrated charge density. -/
noncomputable def totalCharge (S : CertifiedSelfBoundProfile3) : ℝ :=
  S.topologicalCharge * S.probabilityMass

/-- The internal spectral-clock angular frequency. -/
noncomputable def internalClockFrequency (S : CertifiedSelfBoundProfile3) : ℝ :=
  S.energy / S.hbar

/-- The profile's total matter energy, generated by the continuum
Schrödinger--Newton functional rather than supplied as a second observable. -/
noncomputable def generatedEnergy (S : CertifiedSelfBoundProfile3) : ℝ :=
  schrodingerNewtonEnergy S.inferredG S.psi

@[zil_level derived_prediction]
lemma inferredG_nonneg (S : CertifiedSelfBoundProfile3) : 0 ≤ S.inferredG := by
  exact mul_nonneg (mul_nonneg S.hbar_pos.le S.c_pos.le) (by positivity)

/-- Normalization makes integrated charge equal to the winding charge. -/
@[zil_level physical_theorem]
lemma totalCharge_eq (S : CertifiedSelfBoundProfile3) :
    S.totalCharge = S.topologicalCharge := by
  rw [totalCharge, probabilityMass, S.normalized]
  simp

/-- The winding `n = -3` sector has electron charge `-1`. -/
@[zil_level physical_theorem]
lemma electron_totalCharge (S : CertifiedSelfBoundProfile3) (h : S.winding = -3) :
    S.totalCharge = -1 := by
  rw [S.totalCharge_eq, topologicalCharge, h]
  norm_num [windingCharge]

/-- The eigenphase clock carries precisely the certified energy:
`ħ ω = E`. -/
@[zil_level physical_theorem]
lemma internalClock_energy (S : CertifiedSelfBoundProfile3) :
    S.hbar * S.internalClockFrequency = S.energy := by
  rw [internalClockFrequency]
  exact mul_div_cancel₀ S.energy S.hbar_pos.ne'

/-- The time-dependent scalar wave. -/
noncomputable def wave (S : CertifiedSelfBoundProfile3)
    (t : ℝ) (x : Space 3) : ℂ :=
  standingWave S.energy S.hbar S.psi t x

/-- The scalar spatial wave tensored with the certified two-component spinor. -/
noncomputable def spinorWave (S : CertifiedSelfBoundProfile3)
    (t : ℝ) (x : Space 3) (a : Fin 2) : ℂ :=
  S.wave t x * S.spinor a

@[zil_level physical_theorem]
lemma wave_normSq (S : CertifiedSelfBoundProfile3) (t : ℝ) (x : Space 3) :
    Complex.normSq (S.wave t x) = S.psi x ^ 2 := by
  rw [wave, standingWave, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq, spectralPhase_norm, one_pow,
    one_mul, Complex.normSq_ofReal]
  ring

/-- The normalized spinor adds no multiplicity to the Born density. -/
@[zil_level physical_theorem]
lemma spinorWave_density (S : CertifiedSelfBoundProfile3) (t : ℝ) (x : Space 3) :
    ∑ a, Complex.normSq (S.spinorWave t x a) = S.psi x ^ 2 := by
  rw [Fin.sum_univ_two]
  simp only [spinorWave, Complex.normSq_mul, S.wave_normSq]
  rw [← mul_add, S.spinor_normalized, mul_one]

/-- The certified profile solves the full pointwise time-dependent
Schrödinger--Newton matter equation at inferred `G`. -/
@[zil_level physical_theorem]
lemma solves_matterPDE (S : CertifiedSelfBoundProfile3) (t : ℝ) (x : Space 3) :
    (Complex.I * (S.hbar : ℂ)) *
        deriv (fun s => S.wave s x) t =
      spectralPhase S.energy S.hbar t *
        (stationaryHamiltonian S.inferredG S.mass S.hbar S.psi x : ℂ) := by
  exact standingWave_solves_full_schrodingerNewton
    S.inferredG S.mass S.hbar S.energy S.hbar_pos.ne'
    S.psi S.stationary t x

/-- The internal Pauli degree of freedom has the exact spin-`1/2` Casimir
`S² = 3 ħ² / 4`. -/
@[zil_level physical_theorem]
lemma spin_half (S : CertifiedSelfBoundProfile3) :
    (Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinX S.hbar *
          Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinX S.hbar +
        Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinY S.hbar *
          Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinY S.hbar +
        Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinZ S.hbar *
          Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinZ S.hbar) *ᵥ S.spinor =
      ((3 / 4) * (S.hbar : ℂ) ^ 2) • S.spinor := by
  rw [Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spin_sq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The profile interacts with itself through the shared Newton/Hartree
carrier, and that interaction functional is nonnegative before the attractive
minus sign in the total energy. -/
@[zil_level physical_theorem]
lemma selfInteraction (S : CertifiedSelfBoundProfile3) :
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy
        (bornDensity S.psi) (bornDensity S.psi) =
        newtonianSelfEnergy (bornDensity S.psi) ∧
      0 ≤ newtonianSelfEnergy (bornDensity S.psi) := by
  exact ⟨
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_self
      (bornDensity S.psi),
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianSelfEnergy_nonneg
      (bornDensity S.psi) (fun _ => sq_nonneg _)⟩

/-- The certified state cannot lower its energy below the universal
HLS--Sobolev completing-the-square floor. -/
@[zil_level physical_theorem]
lemma energy_noCollapse (S : CertifiedSelfBoundProfile3) :
    -(S.inferredG * schrodingerNewtonStabilityConstant) ^ 2 / 8 ≤
      S.generatedEnergy := by
  exact schrodingerNewtonEnergy_normalized_stability
    S.inferredG S.inferredG_nonneg S.psi S.normalized S.compactSupport

/-- The normalized compactly supported Schwartz perturbation class on which
the coercive energy floor is uniform. -/
def IsNormalizedCorePerturbation (φ : 𝓢(Space 3, ℝ)) : Prop :=
  (∫⁻ x, ‖φ x‖ₑ ^ (2 : ℝ) = 1) ∧
    HasCompactSupport (φ : Space 3 → ℝ)

/-- Every admissible perturbation obeys the same state-independent energy
floor.  This is energetic no-collapse, not orbital stability. -/
@[zil_level physical_theorem]
lemma admissiblePerturbation_noCollapse (S : CertifiedSelfBoundProfile3)
    (φ : 𝓢(Space 3, ℝ)) (hφ : IsNormalizedCorePerturbation φ) :
    -(S.inferredG * schrodingerNewtonStabilityConstant) ^ 2 / 8 ≤
      schrodingerNewtonEnergy S.inferredG φ := by
  exact schrodingerNewtonEnergy_normalized_stability
    S.inferredG S.inferredG_nonneg φ hφ.1 hφ.2

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence

/-- The geometry generated by the Born density: distributional weak-field
Einstein `00` plus the unique homogeneous `Ḣ¹` weak Poisson solution. -/
def HasGeneratedWeakGeometry (S : CertifiedSelfBoundProfile3) : Prop :=
  TemperedWeakFieldEinstein00Equation3
      S.inferredG S.c
      (inferenceNewtonTemperedPotential S.hbar S.c S.sigma0
        (bornDensitySchwartz S.psi))
      (temperedConvolutionSchwartz (TemperedDistribution.delta 0)
        (bornDensitySchwartz S.psi)) ∧
    ∃! energyDerivative : FourierDotHOneThree,
      IsFourierDotHOneWeakSolution
        (inferenceNewtonSchwartzDotHMinusOneThree S.hbar S.c S.sigma0
          (bornDensitySchwartz S.psi))
        energyDerivative

@[zil_level physical_theorem]
lemma generatedGeometry (S : CertifiedSelfBoundProfile3) :
    S.HasGeneratedWeakGeometry := by
  exact inferenceNewtonTemperedPotential_einstein00_and_energy_unique
    S.hbar S.c S.sigma0 (bornDensitySchwartz S.psi) S.c_pos.ne'

/-- The capstone: one certified profile carries the nonlinear matter PDE,
Born/spinor density, winding charge, internal clock, interaction, perturbative
energy floor, spin-`1/2`, and generated weak geometry. -/
@[zil_level physical_theorem]
theorem fullPDE_observables_and_stability (S : CertifiedSelfBoundProfile3) :
    (∀ t x, (Complex.I * (S.hbar : ℂ)) *
          deriv (fun s => S.wave s x) t =
        spectralPhase S.energy S.hbar t *
          (stationaryHamiltonian S.inferredG S.mass S.hbar S.psi x : ℂ))
      ∧ (∀ t x, ∑ a, Complex.normSq (S.spinorWave t x a) = S.psi x ^ 2)
      ∧ S.totalCharge = S.topologicalCharge
      ∧ S.hbar * S.internalClockFrequency = S.energy
      ∧ -(S.inferredG * schrodingerNewtonStabilityConstant) ^ 2 / 8 ≤
          S.generatedEnergy
      ∧ 0 ≤ newtonianSelfEnergy (bornDensity S.psi)
      ∧ (Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinX S.hbar *
              Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinX S.hbar +
            Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinY S.hbar *
              Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinY S.hbar +
            Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinZ S.hbar *
              Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spinZ S.hbar) *ᵥ S.spinor =
          ((3 / 4) * (S.hbar : ℂ) ^ 2) • S.spinor
      ∧ S.HasGeneratedWeakGeometry := by
  exact ⟨fun t x => S.solves_matterPDE t x,
    fun t x => S.spinorWave_density t x, S.totalCharge_eq,
    S.internalClock_energy, S.energy_noCollapse, S.selfInteraction.2,
    S.spin_half, S.generatedGeometry⟩

end CertifiedSelfBoundProfile3

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lintegral_tendsto_zero_of_localizedRellich_of_recenteredTight where
  formalizes @ "claim:localized-rellich-l-one-convergence-on-every-fixed-ball-and-uniform-recentered-tail-decay-imply-global-l-one-convergence-on-the-continuum",
  supported_by @ "lean:MeasureTheory.lintegral_add_compl",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-the-local-to-global-concentration-compactness-gluing-step-the-model-must-still-produce-the-recentering-centers-and-prove-the-two-visible-estimates"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lintegral_lsixFifths_tendsto_zero_of_lone_of_lthree_bound where
  formalizes @ "claim:strong-l-one-convergence-and-a-finite-uniform-l-three-bound-imply-strong-l-six-fifths-convergence-by-the-proved-continuum-holder-interpolation-inequality",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lintegral_one_three_interpolation",
  epistemic_status @ "risky",
  caveat @ "claim:for-born-density-differences-the-uniform-cubic-bound-is-the-explicit-output-required-from-the-three-dimensional-h-one-to-l-six-sobolev-estimate"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneBornLSixFifthsConverges_of_recentered_localizedRellich where
  formalizes @ "claim:localized-rellich-convergence-uniform-recentered-tightness-and-the-h-one-sobolev-cubic-density-bound-derive-the-complete-strong-l-six-fifths-born-density-predicate-consumed-by-newton-hartree-continuity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lintegral_tendsto_zero_of_localizedRellich_of_recenteredTight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lintegral_lsixFifths_tendsto_zero_of_lone_of_lthree_bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.lsixFifths_mass_tendsto_of_diff",
  epistemic_status @ "risky",
  caveat @ "claim:the-global-gluing-and-interpolation-are-proved-the-visible-data-fields-remain-the-model-specific-local-rellich-recentering-tail-and-sobolev-finiteness-estimates"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneNewtonianSelfEnergy_tendsto_of_lsixFifths where
  formalizes @ "claim:strong-l-six-fifths-convergence-of-the-complete-h-one-born-densities-transported-through-the-existing-euclidean-to-space-three-chart-implies-convergence-of-their-actual-real-newtonian-self-energies",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianSelfEnergy_tendsto_of_lsixFifths",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.euclideanToSpaceThree",
  epistemic_status @ "risky",
  caveat @ "claim:the-new-localized-rellich-theorem-derives-this-predicate-from-explicit-local-convergence-recentered-tail-and-sobolev-cubic-estimates-weak-h-one-convergence-alone-is-not-relabeled-as-strong-density-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths where
  formalizes @ "claim:the-same-strong-l-six-fifths-born-density-convergence-supplies-exactly-the-attractive-newton-hartree-interaction-convergence-premise-used-by-the-positive-energy-split-direct-method",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneNewtonianSelfEnergy_tendsto_of_lsixFifths",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit",
  epistemic_status @ "risky",
  caveat @ "claim:this-closes-the-kernel-continuity-implication-and-the-new-recentered-local-rellich-theorem-closes-its-global-interpolation-step-the-model-specific-local-estimates-and-global-conservative-flow-remain-explicit"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.standingWave_solves_full_schrodingerNewton where
  derives @ "claim:a-certified-stationary-three-dimensional-schrodinger-newton-profile-lifts-to-a-pointwise-time-dependent-standing-wave-solution",
  requires @ "claim:the-spatial-profile-satisfies-the-stationary-nonlinear-schrodinger-newton-equation",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-theorem-lifts-an-explicit-stationary-profile-certificate-it-does-not-construct-a-nonlinear-ground-state-by-concentration-compactness"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_local_hOnePDE_solution where
  formalizes @ "claim:every-continuously-frechet-differentiable-autonomous-generator-on-the-complete-continuum-h-one-r-three-carrier-has-a-local-classical-solution-through-every-initial-state",
  supported_by @ "lean:ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀",
  epistemic_status @ "risky",
  caveat @ "claim:applying-this-to-the-unregularized-schrodinger-newton-generator-requires-the-separate-hartree-h-one-to-h-one-c-one-mapping-estimate"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOnePDE_solution_eventuallyEq where
  formalizes @ "claim:two-local-continuum-h-one-trajectories-of-the-same-c-one-autonomous-generator-through-the-same-initial-state-agree-near-the-initial-time",
  supported_by @ "lean:ODE_solution_unique_of_eventually",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-local-uniqueness-for-a-c-one-h-one-generator-not-a-global-no-blowup-result-for-the-unregularized-hartree-pde"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel where
  formalizes @ "claim:a-nonempty-compact-continuum-h-one-ground-state-orbit-is-uniformly-orbitally-stable-under-an-energy-and-constraint-preserving-flow-when-the-constrained-low-energy-sublevel-is-compact",
  derives @ "claim:the-positive-energy-separation-away-from-the-orbit-is-derived-by-the-extreme-value-theorem-rather-than-supplied-as-a-stability-certificate",
  supported_by @ "lean:IsCompact.exists_forall_le'",
  supported_by @ "lean:IsCompact.exists_thickening_subset_open",
  epistemic_status @ "risky",
  caveat @ "claim:for-the-unregularized-schrodinger-newton-model-global-energy-preserving-flow-and-compactness-modulo-phase-and-translation-must-still-be-instantiated-from-hartree-mapping-tightness-mass-closure-and-lower-semicontinuity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_firstMoment_normClosure where
  formalizes @ "claim:closedness-h-one-boundedness-a-finite-recentered-first-moment-and-no-loss-of-h-one-norm-derive-the-compact-low-energy-sublevel-needed-for-uniform-orbital-stability",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_firstMoment_and_normClosure",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel",
  epistemic_status @ "risky",
  caveat @ "claim:the-model-specific-recentering-uniform-moment-bound-hartree-no-loss-of-norm-estimate-and-global-energy-preserving-flow-remain-explicit-premises-for-the-unregularized-schrodinger-newton-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_hOneBornMoment_normClosure where
  formalizes @ "claim:physical-l-two-normalization-the-first-moment-of-the-actual-reconstructed-h-one-born-density-and-no-loss-of-h-one-norm-derive-the-compact-low-energy-sublevel-and-uniform-orbital-stability-without-an-arbitrary-measure-adapter",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel",
  epistemic_status @ "risky",
  caveat @ "claim:recentering-the-born-moment-deriving-no-loss-of-the-h-one-norm-and-constructing-the-global-energy-preserving-unregularized-hartree-flow-remain-explicit-model-specific-premises"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneConstrainedEnergyMinimizers_nonempty_isCompact where
  formalizes @ "claim:a-continuous-energy-on-a-nonempty-compact-continuum-h-one-constraint-set-attains-its-minimum-and-its-complete-equal-energy-minimizing-orbit-is-compact",
  supported_by @ "lean:IsCompact.exists_isMinOn",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneConstrainedEnergyMinimizers_iff_eq_ground",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-the-direct-method-after-compactness-it-does-not-assert-that-the-unregularized-hartree-admissible-family-is-compact-without-the-separate-analytic-estimates"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_energyMinimizer where
  formalizes @ "claim:closedness-h-one-boundedness-physical-l-two-normalization-a-finite-first-born-moment-and-no-loss-of-h-one-norm-derive-an-attained-continuum-ground-state-for-every-continuous-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure",
  supported_by @ "lean:IsCompact.exists_isMinOn",
  epistemic_status @ "risky",
  caveat @ "claim:the-ground-state-is-derived-under-explicit-concentration-compactness-hypotheses-the-model-specific-recentering-moment-bound-and-no-loss-estimate-are-not-hidden"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_compact_hOne_minimizingOrbit_uniformlyStable where
  formalizes @ "claim:compact-admissibility-continuous-energy-and-conservation-derive-the-ground-energy-the-nonempty-compact-full-minimizing-orbit-and-its-uniform-cazenave-lions-stability",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneConstrainedEnergyMinimizers_nonempty_isCompact",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel",
  epistemic_status @ "risky",
  caveat @ "claim:the-global-constraint-and-energy-preserving-flow-remains-an-explicit-premise"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_minimizingOrbit_uniformlyStable where
  formalizes @ "claim:the-actual-normalized-h-one-born-law-and-no-loss-concentration-compactness-derive-ground-state-attainment-the-complete-compact-minimizing-orbit-and-uniform-orbital-stability-without-supplying-a-ground-state-or-orbit",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_compact_hOne_minimizingOrbit_uniformlyStable",
  epistemic_status @ "risky",
  caveat @ "claim:the-hls-continuity-and-recentered-local-rellich-interpolation-bridges-now-derive-hartree-convergence-the-remaining-obligations-are-the-model-specific-local-rellich-tail-and-sobolev-estimates-and-the-global-conservative-hartree-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.totalCharge_eq where
  derives @ "claim:the-integrated-charge-of-a-normalized-profile-equals-its-winding-generated-charge-n-over-three",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.windingCharge",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:charge-quantization-follows-from-the-winding-carrier-while-the-assignment-of-a-particle-sector-to-a-specific-winding-is-model-input"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.internalClock_energy where
  derives @ "claim:the-standing-wave-internal-spectral-clock-obeys-hbar-times-omega-equals-the-certified-energy",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-energy-eigenphase-clock-it-is-not-identified-with-the-rest-compton-clock-unless-energy-equals-mass-times-c-squared-is-separately-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.spin_half where
  derives @ "claim:the-two-component-internal-degree-of-freedom-obeys-the-exact-pauli-spin-one-half-casimir",
  supported_by @ "lean:Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spin_sq",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.admissiblePerturbation_noCollapse where
  derives @ "claim:every-normalized-compactly-supported-schwartz-perturbation-obeys-the-same-state-independent-schrodinger-newton-energy-floor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_stability",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-coercive-energetic-no-collapse-on-the-schwartz-core-not-orbital-asymptotic-or-spectral-stability"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.energy_noCollapse where
  derives @ "claim:the-profile-generates-its-total-matter-energy-through-the-continuum-schrodinger-newton-functional-and-that-energy-obeys-the-universal-hls-sobolev-floor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_stability",
  epistemic_status @ "risky",
  caveat @ "claim:the-generated-total-functional-energy-is-distinct-from-the-stationary-equation-eigenvalue-and-the-lower-bound-is-not-an-orbital-stability-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.generatedGeometry where
  derives @ "claim:the-profile-born-density-generates-the-distributional-weak-field-einstein-zero-zero-equation-and-a-unique-homogeneous-h-one-poisson-solution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-is-the-static-scalar-linearized-einstein-zero-zero-sector-not-the-full-nonlinear-dynamical-einstein-system"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.fullPDE_observables_and_stability where
  derives @ "claim:one-certified-three-dimensional-continuum-profile-carries-the-time-dependent-schrodinger-newton-pde-born-density-winding-charge-spectral-clock-spin-self-interaction-uniform-perturbation-energy-floor-and-generated-weak-geometry",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:the-stationary-nonlinear-profile-is-explicit-certificate-data-the-perturbation-result-is-an-energy-floor-rather-than-orbital-stability-and-the-geometry-is-the-static-weak-field-einstein-zero-zero-sector"

zil_file_contract physlib.selfBoundSchrodingerNewtonPDE where
  promises "A common three-dimensional continuum carrier assembles the existing Schrödinger-Newton, winding-charge, spectral-clock, Pauli-spin, HLS-Sobolev stability, tempered-Poisson, and weak-Einstein infrastructure. The complete continuum H1 carrier now has Picard local existence and uniqueness for every C1 autonomous generator. A Cazenave-Lions theorem derives uniform orbital stability and its positive separating energy gap from a nonempty compact minimizing orbit, continuous energy, and constraint/energy conservation. Its quantitative refinement derives the required compact low-energy sublevel from closedness, H1 boundedness, a finite recentered first radial moment, and explicit no-loss of the H1 norm along the common weak-field/Prokhorov subsequence. The Born-specialized refinement removes the arbitrary probability-measure adapter: physical L2 normalization and the first moment of the reconstructed squared-amplitude density produce a limit probability measure that is proved to be the Born law of the strong H1 limit. The minimizing-sequence energy-split refinement derives the formerly opaque no-loss premise from weak closure, convergence of the nonlinear interaction and the positive kinetic-plus-interaction decomposition; it attains the variational level and proves strong H1 and Born-law convergence. The complete H1 Born density is transported through the existing Euclidean-to-Space-three chart to a canonical measurable density, and the general-density bilinear HLS theorem proves that strong L^(6/5) convergence implies convergence of the actual attractive Newton-Hartree interaction. The formerly abstract HOneBornLSixFifthsConverges premise is now derived by a continuum local-to-global theorem: localized Rellich L1 convergence plus uniform recentered tails gives global L1, the proved L1-L3 Holder interpolation gives strong L^(6/5), and the complete Lp carrier gives convergence of the L^(6/5) masses. The direct-method refinement no longer accepts a ground state or minimizing orbit: under the explicit Born compactness hypotheses the energy attains its minimum, the full equal-energy minimizing orbit is nonempty and compact, and a conservative flow makes it uniformly orbitally stable. From an explicit stationary-profile certificate the file proves the pointwise time-dependent nonlinear matter PDE, invariant Born and spinor density, integrated winding charge, hbar omega equals energy, spin one half, self-interaction, a uniform energy floor for all normalized compactly supported Schwartz perturbations, and generated distributional weak geometry with a unique homogeneous H1 Poisson solution. Honest: applying the H1 well-posedness and orbital theorems to the unregularized Hartree generator still requires a mild Duhamel-Strichartz well-posedness proof, global conserved continuation, model-specific recentering centers, localized Rellich/tail estimates, and the H1-to-L6 Sobolev bound supplying the visible cubic-density field; the global gluing and interpolation themselves are proved. The Laplacian is unbounded on H1 so the full generator is not relabeled as a C1 H1-to-H1 ODE, ground-state existence and stability are conditional on the now-visible concentration-compactness and conservation hypotheses, the certified-profile energy floor alone is not orbital stability, and the geometry is the static scalar weak-field Einstein 00 sector rather than full nonlinear backreaction."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_stability",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_local_hOnePDE_solution",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOnePDE_solution_eventuallyEq",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_firstMoment_normClosure",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_hOneBornMoment_normClosure",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_energyMinimizer",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_minimizingOrbit_uniformlyStable",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneNewtonianSelfEnergy_tendsto_of_lsixFifths",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.windingCharge",
    "lean:Physlib.QuantumMechanics.SpinDensityFunctionalOperators.spin_sq",
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.hasDerivAt_spectralPhase"]
  forbids_substitutes ["an arbitrary real charge parameter in place of winding quantization",
    "a finite lattice in place of the continuum Space 3 Schwartz and tempered-distribution carriers",
    "an energy lower bound mislabeled as orbital stability",
    "a supplied gravitational potential in place of the proved tempered Poisson and weak Einstein solution",
    "claiming that generic C1 Picard well-posedness already proves the unregularized Hartree generator maps H1 to H1",
    "claiming that a finite first moment alone proves strong H1 compactness without the separate no-loss-of-norm estimate",
    "claiming weak H1 convergence alone proves convergence of the singular Hartree interaction",
    "an unconditional nonlinear ground-state existence claim without concentration compactness"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.standingWave_solves_full_schrodingerNewton,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_local_hOnePDE_solution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOnePDE_solution_eventuallyEq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_compact_energySublevel,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_firstMoment_normClosure,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.uniform_orbitalStability_of_hOneBornMoment_normClosure,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneConstrainedEnergyMinimizers_nonempty_isCompact,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_energyMinimizer,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_compact_hOne_minimizingOrbit_uniformlyStable,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.exists_hOneBorn_minimizingOrbit_uniformlyStable,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneNewtonianSelfEnergy_tendsto_of_lsixFifths,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.totalCharge_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.internalClock_energy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.spin_half,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.energy_noCollapse,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.admissiblePerturbation_noCollapse,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.generatedGeometry,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE.CertifiedSelfBoundProfile3.fullPDE_observables_and_stability]

/- ZIL-END -/
