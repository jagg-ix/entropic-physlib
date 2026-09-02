/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
public import Mathlib.MeasureTheory.Integral.Prod
meta import Zil

/-!
# The sharp Hardy–Littlewood–Sobolev bound on the Newtonian self-energy

The gravitational self-energy of a mass density `ρ` is `∬ ρ(x)·ρ(y)/‖x−y‖` — the `λ = 1`, `n = 3`
diagonal of the Riesz–Newton bilinear form. For a **uniform density on a set `A`** (`ρ = 𝟙_A`), this is
the near-diagonal integral `∬_{A×A} ‖x−y‖⁻¹`, and the sharp Hardy–Littlewood–Sobolev inequality
(`bilinearRieszForm_le_sharp`, specialized to `B = A`, `λ = 1`, with `3/(3−1) = 3/2`, `1 − 1/3 = 2/3`,
`μ(A)^{2/3}·μ(A) = μ(A)^{5/3}`) gives the sharp bound

  `∬_{A×A} ‖x−y‖⁻¹ ≤ (3/2)·μ(ball(0,1))^{1/3}·μ(A)^{5/3}`   (`uniformSelfEnergy_le`).

This is the concrete self-energy estimate the Schrödinger–Poisson / entropic-gravity arc needs: the
Coulomb/Newton self-interaction of a bounded uniform source is controlled by a power `5/3` of its volume,
with the sharp geometric constant.

The module now also lands the general-density HLS theorem on the repository's real-valued Bochner
functional:

  `newtonianSelfEnergy ρ ≤ (C · (∫ ρ^(6/5))^(5/3)).toReal`.

This second theorem assumes only measurability, pointwise nonnegativity, and finite `L^(6/5)` mass.
It uses the repository's maximal-function/Marcinkiewicz development, including the genuine weak-`Lᵖ`
distribution estimate that removes the earlier auxiliary `L¹` premise.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal Space

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential

/-- The explicit dimension-three maximal-function HLS coefficient. Naming it
separately prevents downstream Schrödinger–Newton interpolation and stability
theorems from duplicating the analytic constant. -/
noncomputable def newtonianHLSConstant : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
      * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
      * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1)
          / ((6 : ℝ) / 5 - 1))) ^ ((1 : ℝ) / 6)

/-- The explicit maximal-function HLS upper bound for a real density `ρ`. This
names the analytic right-hand side so downstream Schrödinger–Poisson and
entropic-gravity theorems do not duplicate its constant. -/
noncomputable def newtonianHLSBound (ρ : Space 3 → ℝ) : ℝ :=
  (newtonianHLSConstant
    * (∫⁻ x, ENNReal.ofReal (ρ x) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3)).toReal

/-- **[The sharp Hardy–Littlewood–Sobolev bound on the uniform-density self-energy]** for a measurable
set `A` of finite measure, the Newtonian self-energy of the uniform density `𝟙_A`,

  `∬_{A×A} ‖x−y‖⁻¹ = ∬ 𝟙_A(x)·𝟙_A(y)/‖x−y‖`,

is bounded by `(3/2)·μ(ball(0,1))^{1/3}·μ(A)^{5/3}`. This is the `λ = 1`, `n = 3` diagonal of the sharp
HLS inequality (`bilinearRieszForm_le_sharp` at `B = A`): the self-interaction of a bounded uniform mass
source scales as the `5/3` power of its volume, with the sharp geometric constant. -/
@[zil_level physical_theorem]
theorem uniformSelfEnergy_le (A : Set (Space 3)) (hA : MeasurableSet A) (hAfin : volume A ≠ ∞) :
    ∫⁻ p in A ×ˢ A, ENNReal.ofReal (‖p.1 - p.2‖⁻¹) ∂(volume.prod volume) ≤
      ENNReal.ofReal (3 / 2 * (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (1 / 3 : ℝ)
        * (volume A).toReal ^ (5 / 3 : ℝ)) := by
  have hsharp := bilinearRieszForm_le_sharp A A hA hA hAfin hAfin 1 (by norm_num) (by norm_num)
  simp only [Real.rpow_neg_one] at hsharp
  refine hsharp.trans (le_of_eq ?_)
  set c := (volume (Metric.ball (0 : Space 3) 1)).toReal with hc
  set v := (volume A).toReal with hv
  have hv0 : (0 : ℝ) ≤ v := ENNReal.toReal_nonneg
  have hvpow : v ^ (2 / 3 : ℝ) * v = v ^ (5 / 3 : ℝ) := by
    rcases eq_or_ne v 0 with h | h
    · rw [h, mul_zero, Real.zero_rpow (by norm_num)]
    · rw [show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
        Real.rpow_add (hv0.lt_of_ne (Ne.symm h)), Real.rpow_one]
  rw [show volume A = ENNReal.ofReal v from (ENNReal.ofReal_toReal hAfin).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    ← hvpow]
  ring

/-- **[The sharp bound on the repo's Newtonian self-energy functional for a uniform density]** the
gravitational self-energy `newtonianSelfEnergy (𝟙_A) = ∬ 𝟙_A(x)·𝟙_A(y)/‖x−y‖` of the uniform density on
a finite-measure set `A` obeys the sharp Hardy–Littlewood–Sobolev estimate

  `newtonianSelfEnergy (𝟙_A) ≤ (3/2)·μ(ball(0,1))^{1/3}·μ(A)^{5/3}`.

This packages `uniformSelfEnergy_le` onto the repo's Bochner self-energy functional: the double integral
is bridged to the `ℝ≥0∞` near-diagonal integral through Fubini (`integral_integral`), the nonnegativity
bridge (`integral_eq_lintegral_of_nonneg_ae`), and integrability from the finite HLS bound. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_indicator_le (A : Set (Space 3)) (hA : MeasurableSet A)
    (hAfin : volume A ≠ ∞) :
    newtonianSelfEnergy (A.indicator (fun _ => 1)) ≤
      3 / 2 * (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (1 / 3 : ℝ)
        * (volume A).toReal ^ (5 / 3 : ℝ) := by
  have hρ_meas : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hg_nn : 0 ≤ᵐ[volume.prod volume] fun p : Space 3 × Space 3 =>
      A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖ :=
    Filter.Eventually.of_forall fun p => div_nonneg
      (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (norm_nonneg _)
  have hg_meas : AEStronglyMeasurable (fun p : Space 3 × Space 3 =>
      A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖)
      (volume.prod volume) :=
    (((hρ_meas.comp measurable_fst).mul (hρ_meas.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
  have hofReal : (fun p : Space 3 × Space 3 => ENNReal.ofReal
        (A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖))
      = (A ×ˢ A).indicator (fun p => ENNReal.ofReal ‖p.1 - p.2‖⁻¹) := by
    funext p
    by_cases hp : p ∈ A ×ˢ A
    · simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2,
        one_mul, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hp]
      rcases not_and_or.mp (Set.mem_prod.not.mp hp) with h | h
      · simp only [Set.indicator_of_notMem h, zero_mul, zero_div, ENNReal.ofReal_zero]
      · simp only [Set.indicator_of_notMem h, mul_zero, zero_div, ENNReal.ofReal_zero]
  have hlint_eq : ∫⁻ p, ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) p.1 *
        A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖) ∂(volume.prod volume)
      = ∫⁻ p in A ×ˢ A, ENNReal.ofReal ‖p.1 - p.2‖⁻¹ ∂(volume.prod volume) := by
    rw [hofReal, lintegral_indicator (hA.prod hA)]
  have hfin : ∫⁻ p, ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) p.1 *
      A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖) ∂(volume.prod volume) < ∞ := by
    rw [hlint_eq]; exact lt_of_le_of_lt (uniformSelfEnergy_le A hA hAfin) ENNReal.ofReal_lt_top
  have hg_int : Integrable (fun p : Space 3 × Space 3 =>
      A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2 / ‖p.1 - p.2‖)
      (volume.prod volume) := ⟨hg_meas, (hasFiniteIntegral_iff_ofReal hg_nn).mpr hfin⟩
  rw [newtonianSelfEnergy_eq_doubleIntegral, integral_integral hg_int,
    integral_eq_lintegral_of_nonneg_ae hg_nn hg_meas, hlint_eq,
    ← ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 2 *
      (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (1 / 3 : ℝ) *
      (volume A).toReal ^ (5 / 3 : ℝ) by positivity)]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (uniformSelfEnergy_le A hA hAfin)

/-- **[General-density HLS bound on the real Bochner Newtonian self-energy]**.
For every measurable nonnegative density `ρ ∈ L^(6/5)(ℝ³)`, the repository's
real-valued functional

`newtonianSelfEnergy ρ = ∫ x, ∫ y, ρ x * ρ y / ‖x-y‖`

is finite and bounded by the explicit maximal-function HLS constant times
`(∫ ρ^(6/5))^(5/3) = ‖ρ‖_(6/5)^2`. The proof is the bridge from the
`ℝ≥0∞` theorem `lintegral_selfInteraction_le` to the Bochner integral: Tonelli
identifies the two nonnegative double integrals, the HLS bound proves
integrability, Fubini recovers the iterated real integral, and `toReal_mono`
transfers the inequality. No separate `L¹` hypothesis is present. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_le_hls
    (ρ : Space 3 → ℝ) (hρ : Measurable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hNtop : ∫⁻ x, ENNReal.ofReal (ρ x) ^ ((6 : ℝ) / 5) ≠ ∞) :
    newtonianSelfEnergy ρ ≤ newtonianHLSBound ρ := by
  change newtonianSelfEnergy ρ ≤
    (newtonianHLSConstant
        * (∫⁻ x, ENNReal.ofReal (ρ x) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3)).toReal
  let ρe : Space 3 → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x)
  have hρe : Measurable ρe := ENNReal.measurable_ofReal.comp hρ
  have hbound := lintegral_selfInteraction_le ρe hρe hNtop
  let g : Space 3 × Space 3 → ℝ := fun p => ρ p.1 * ρ p.2 / ‖p.1 - p.2‖
  have hg_nn : 0 ≤ᵐ[volume.prod volume] g :=
    Filter.Eventually.of_forall fun p =>
      div_nonneg (mul_nonneg (hρnn p.1) (hρnn p.2)) (norm_nonneg _)
  have hg_meas : AEStronglyMeasurable g (volume.prod volume) :=
    (((hρ.comp measurable_fst).mul (hρ.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
  have hofReal : ∀ p : Space 3 × Space 3,
      ENNReal.ofReal (g p) =
        ρe p.1 * (ρe p.2 * ENNReal.ofReal ‖p.1 - p.2‖⁻¹) := by
    intro p
    simp only [g, ρe]
    by_cases hd : ‖p.1 - p.2‖ = 0
    · simp [hd]
    · have hdpos : 0 < ‖p.1 - p.2‖ := (norm_nonneg _).lt_of_ne (Ne.symm hd)
      rw [div_eq_mul_inv,
        ENNReal.ofReal_mul (mul_nonneg (hρnn p.1) (hρnn p.2)),
        ENNReal.ofReal_mul (hρnn p.1), ENNReal.ofReal_inv_of_pos hdpos]
      ring
  have hlint_eq :
      ∫⁻ p, ENNReal.ofReal (g p) ∂(volume.prod volume) =
        ∫⁻ x, ρe x * ∫⁻ y, ρe y * ENNReal.ofReal ‖x - y‖⁻¹ := by
    rw [lintegral_prod _ hg_meas.aemeasurable.ennreal_ofReal]
    apply lintegral_congr
    intro x
    calc
      ∫⁻ y, ENNReal.ofReal (g (x, y))
          = ∫⁻ y, ρe x * (ρe y * ENNReal.ofReal ‖x - y‖⁻¹) :=
        lintegral_congr fun y => hofReal (x, y)
      _ = ρe x * ∫⁻ y, ρe y * ENNReal.ofReal ‖x - y‖⁻¹ := by
        apply lintegral_const_mul
        exact hρe.mul (by fun_prop)
  have hRtop :
      newtonianHLSConstant
        * (∫⁻ x, ENNReal.ofReal (ρ x) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · unfold newtonianHLSConstant
      apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
          · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNtop
  have hfin : ∫⁻ p, ENNReal.ofReal (g p) ∂(volume.prod volume) < ∞ := by
    rw [hlint_eq]
    exact lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hRtop)
  have hg_int : Integrable g (volume.prod volume) :=
    ⟨hg_meas, (hasFiniteIntegral_iff_ofReal hg_nn).mpr hfin⟩
  rw [newtonianSelfEnergy_eq_doubleIntegral, integral_integral hg_int,
    integral_eq_lintegral_of_nonneg_ae hg_nn hg_meas, hlint_eq]
  exact ENNReal.toReal_mono hRtop hbound

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.uniformSelfEnergy_le where
  formalizes @ "claim:the-sharp-hardy-littlewood-sobolev-bound-on-the-uniform-density-newtonian-self-energy-the-double-integral-over-a-cross-a-of-one-over-norm-x-minus-y-the-self-energy-of-the-indicator-density-of-a-is-at-most-three-halves-times-the-measure-of-the-unit-ball-to-the-one-third-times-the-measure-of-a-to-the-five-thirds",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le_sharp",
  caveat @ "claim:this-is-the-sharp-indicator-density-bound-the-separate-general-density-theorem-newtonian-self-energy-le-hls-has-an-explicit-maximal-function-constant-and-does-not-claim-that-constant-is-sharp"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_indicator_le where
  formalizes @ "claim:the-repos-newtonian-self-energy-functional-of-the-uniform-indicator-density-on-a-finite-measure-set-a-the-double-integral-of-the-indicator-of-a-at-x-times-the-indicator-of-a-at-y-over-norm-x-minus-y-is-at-most-three-halves-times-the-measure-of-the-unit-ball-to-the-one-third-times-the-measure-of-a-to-the-five-thirds",
  supported_by @ "lean:MeasureTheory.integral_integral",
  supported_by @ "lean:MeasureTheory.integral_eq_lintegral_of_nonneg_ae"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_le_hls where
  formalizes @ "claim:for-every-measurable-nonnegative-real-density-rho-on-r-three-with-finite-l-six-fifths-mass-the-repositorys-bochner-newtonian-self-energy-is-finite-and-at-most-the-explicit-hls-constant-times-the-l-six-fifths-norm-squared-with-no-separate-l-one-hypothesis",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_selfInteraction_le",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.weak_p_p",
  supported_by @ "lean:MeasureTheory.integral_integral",
  caveat @ "claim:the-density-is-real-measurable-and-pointwise-nonnegative-the-explicit-maximal-function-constant-is-not-asserted-to-be-the-sharp-lieb-hls-constant"

zil_file_contract physlib.newtonianSelfEnergySharpBound where
  promises "Hardy-Littlewood-Sobolev bounds on the repository's real Newtonian self-energy. uniformSelfEnergy_le and newtonianSelfEnergy_indicator_le retain the sharp indicator-density estimate. newtonianSelfEnergy_le_hls supplies the general measurable nonnegative density theorem: finite L^(6/5) mass alone bounds the real Bochner newtonianSelfEnergy by an explicit constant times (integral rho^(6/5))^(5/3), equivalently the squared L^(6/5) norm. The bridge identifies the ENNReal and real double integrals by Tonelli, obtains Bochner integrability from the finite HLS upper bound, and returns to the iterated real integral by Fubini. The former auxiliary L1 premise is removed by the genuine weak-(p,p) distribution estimate weak_p_p derived from truncated weak-(1,1) and the Lp tail inequality."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le_sharp",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_selfInteraction_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.weak_p_p",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral",
    "lean:MeasureTheory.integral_integral"]
  forbids_substitutes ["an L1 premise hidden inside the general L^(6/5) theorem",
    "an unconstrained volume power, whereas the indicator self-energy scales sharply as the 5/3 power of the source volume",
    "an abstract lintegral only, whereas newtonianSelfEnergy_indicator_le lands the bound on the repo's Bochner newtonianSelfEnergy functional"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.uniformSelfEnergy_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_indicator_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_le_hls]

/- ZIL-END -/
