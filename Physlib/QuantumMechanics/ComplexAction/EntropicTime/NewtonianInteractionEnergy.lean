/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction
meta import Zil

/-!
# The mutual Newtonian interaction energy and Newton's third law

The gravitational interaction energy of two mass densities `ρ` and `σ` is the pairwise integral

  `W(ρ,σ) = ∬ ρ(x)·σ(y)/‖x−y‖ dx dy`   (`newtonianInteractionEnergy`).

It reduces to the self-energy on the diagonal (`newtonianInteractionEnergy_self`) and is symmetric —
`W(ρ,σ) = W(σ,ρ)` (`newtonianInteractionEnergy_symm`), the energetic form of Newton's third law: the
mutual gravitational energy is the same whichever source is regarded as acting on the other. Symmetry
follows from Fubini and the symmetry `‖x−y‖ = ‖y−x‖` of the Newton kernel.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal Space
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy

/-- The **mutual Newtonian interaction energy** of two mass densities:
`W(ρ,σ) = ∬ ρ(x)·σ(y)/‖x−y‖`. -/
noncomputable def newtonianInteractionEnergy (ρ σ : Space 3 → ℝ) : ℝ :=
  ∫ x, ∫ y, ρ x * σ y / ‖x - y‖

/-- The extended-real bilinear HLS bound shared by the integrability,
modulus-of-continuity, and convergence theorems below. -/
noncomputable def newtonianMutualHLSBoundENNReal
    (ρ σ : Space 3 → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
    * (newtonianRieszSixthConstant
        * (∫⁻ y, ENNReal.ofReal |σ y| ^ ((6 : ℝ) / 5)) ^ (5 : ℝ))
      ^ ((1 : ℝ) / 6)

/-- The real-valued bilinear HLS bound for the mutual Newtonian energy. -/
noncomputable def newtonianMutualHLSBound
    (ρ σ : Space 3 → ℝ) : ℝ :=
  (newtonianMutualHLSBoundENNReal ρ σ).toReal

/-- **Bilinear HLS integrability and real-energy bound.**  Measurable real
densities with finite `L^(6/5)` mass define an integrable Newton kernel on
the product space, and the absolute value of the repository's actual
Bochner mutual energy is controlled by `newtonianMutualHLSBound`.

The proof applies the positive bilinear HLS theorem to `|ρ|` and `|σ|`,
uses Tonelli to identify the product lintegral, obtains Bochner
integrability from finiteness of the bound, and then applies
`|∫g| ≤ ∫|g|`. -/
@[zil_level physical_theorem]
theorem newtonianInteractionEnergy_hls
    (ρ σ : Space 3 → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρtop : ∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop : ∫⁻ y, ENNReal.ofReal |σ y| ^ ((6 : ℝ) / 5) ≠ ∞) :
    Integrable
        (Function.uncurry fun x y : Space 3 =>
          ρ x * σ y / ‖x - y‖) (volume.prod volume) ∧
      |newtonianInteractionEnergy ρ σ| ≤
        newtonianMutualHLSBound ρ σ := by
  let ρe : Space 3 → ℝ≥0∞ := fun x => ENNReal.ofReal |ρ x|
  let σe : Space 3 → ℝ≥0∞ := fun x => ENNReal.ofReal |σ x|
  have hρe : Measurable ρe :=
    ENNReal.measurable_ofReal.comp hρ.abs
  have hσe : Measurable σe :=
    ENNReal.measurable_ofReal.comp hσ.abs
  have hbound :=
    lintegral_mutualInteraction_le ρe σe hρe hσe hσtop
  let g : Space 3 × Space 3 → ℝ :=
    fun p => ρ p.1 * σ p.2 / ‖p.1 - p.2‖
  have hg_meas : Measurable g :=
    (((hρ.comp measurable_fst).mul (hσ.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm))
  have hofReal : ∀ p : Space 3 × Space 3,
      ENNReal.ofReal |g p| =
        ρe p.1 * (σe p.2 * ENNReal.ofReal ‖p.1 - p.2‖⁻¹) := by
    intro p
    simp only [g, ρe, σe, abs_div, abs_mul, abs_norm]
    by_cases hd : ‖p.1 - p.2‖ = 0
    · simp [hd]
    · have hdpos : 0 < ‖p.1 - p.2‖ :=
        (norm_nonneg _).lt_of_ne (Ne.symm hd)
      rw [div_eq_mul_inv,
        ENNReal.ofReal_mul
          (mul_nonneg (abs_nonneg (ρ p.1)) (abs_nonneg (σ p.2))),
        ENNReal.ofReal_mul (abs_nonneg (ρ p.1)),
        ENNReal.ofReal_inv_of_pos hdpos]
      ring
  have hlint_eq :
      ∫⁻ p, ENNReal.ofReal |g p| ∂(volume.prod volume) =
        ∫⁻ x, ρe x * ∫⁻ y, σe y * ENNReal.ofReal ‖x - y‖⁻¹ := by
    calc
      ∫⁻ p, ENNReal.ofReal |g p| ∂(volume.prod volume)
          = ∫⁻ x, ∫⁻ y, ENNReal.ofReal |g (x, y)| := by
              exact lintegral_prod _
                (ENNReal.measurable_ofReal.comp hg_meas.abs).aemeasurable
      _ = ∫⁻ x, ρe x * ∫⁻ y, σe y * ENNReal.ofReal ‖x - y‖⁻¹ := by
        apply lintegral_congr
        intro x
        calc
          ∫⁻ y, ENNReal.ofReal |g (x, y)|
              = ∫⁻ y, ρe x * (σe y * ENNReal.ofReal ‖x - y‖⁻¹) :=
            lintegral_congr fun y => hofReal (x, y)
          _ = ρe x * ∫⁻ y, σe y * ENNReal.ofReal ‖x - y‖⁻¹ := by
            apply lintegral_const_mul
            exact hσe.mul (by fun_prop)
  have hRtop :
      newtonianMutualHLSBoundENNReal ρ σ ≠ ∞ := by
    unfold newtonianMutualHLSBoundENNReal
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hρtop
    · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      exact ENNReal.mul_ne_top
        newtonianRieszSixthConstant_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hσtop)
  have hfin :
      ∫⁻ p, ENNReal.ofReal |g p| ∂(volume.prod volume) < ∞ := by
    rw [hlint_eq]
    exact lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hRtop)
  have hg_int : Integrable g (volume.prod volume) :=
    ⟨hg_meas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_norm]
      simpa [Real.norm_eq_abs] using hfin⟩
  refine ⟨?_, ?_⟩
  · change Integrable g (volume.prod volume)
    exact hg_int
  change |∫ x, ∫ y, ρ x * σ y / ‖x - y‖| ≤ _
  rw [integral_integral hg_int]
  calc
    |∫ p, g p ∂(volume.prod volume)|
        ≤ ∫ p, |g p| ∂(volume.prod volume) :=
      abs_integral_le_integral_abs
    _ = (∫⁻ p, ENNReal.ofReal |g p| ∂(volume.prod volume)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hg_meas.norm.aestronglyMeasurable]
    _ ≤ newtonianMutualHLSBound ρ σ := by
      unfold newtonianMutualHLSBound
      apply ENNReal.toReal_mono hRtop
      rw [hlint_eq]
      simpa [newtonianMutualHLSBoundENNReal, ρe, σe] using hbound

/-- The product Newton kernel is Bochner-integrable under the exact
`L^(6/5)` hypotheses used by the bilinear HLS theorem. -/
theorem integrable_newtonianInteractionKernel_of_lsixFifths
    (ρ σ : Space 3 → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρtop : ∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop : ∫⁻ y, ENNReal.ofReal |σ y| ^ ((6 : ℝ) / 5) ≠ ∞) :
    Integrable
      (Function.uncurry fun x y : Space 3 =>
        ρ x * σ y / ‖x - y‖) (volume.prod volume) :=
  (newtonianInteractionEnergy_hls ρ σ hρ hσ hρtop hσtop).1

/-- Absolute-value form of the real bilinear HLS estimate. -/
theorem abs_newtonianInteractionEnergy_le_hls
    (ρ σ : Space 3 → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρtop : ∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop : ∫⁻ y, ENNReal.ofReal |σ y| ^ ((6 : ℝ) / 5) ≠ ∞) :
    |newtonianInteractionEnergy ρ σ| ≤
      newtonianMutualHLSBound ρ σ :=
  (newtonianInteractionEnergy_hls ρ σ hρ hσ hρtop hσtop).2

/-- **[The interaction energy on the diagonal is the self-energy]** `W(ρ,ρ) = ∫ φ_ρ·ρ`. -/
@[zil_level physical_theorem]
theorem newtonianInteractionEnergy_self (ρ : Space 3 → ℝ) :
    newtonianInteractionEnergy ρ ρ = newtonianSelfEnergy ρ :=
  (newtonianSelfEnergy_eq_doubleIntegral ρ).symm

/-- **[Newton's third law for the mutual gravitational energy]** `W(ρ,σ) = W(σ,ρ)`: the interaction
energy is symmetric in the two sources, by Fubini and the symmetry of the Newton kernel
`‖x−y‖ = ‖y−x‖`. The product-integrability hypothesis licenses the Fubini swap. -/
@[zil_level physical_theorem]
theorem newtonianInteractionEnergy_symm (ρ σ : Space 3 → ℝ)
    (hInt : Integrable (Function.uncurry fun x y : Space 3 => ρ x * σ y / ‖x - y‖)
      (volume.prod volume)) :
    newtonianInteractionEnergy ρ σ = newtonianInteractionEnergy σ ρ := by
  rw [newtonianInteractionEnergy, integral_integral_swap hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [norm_sub_rev]
  ring

/-- Polarized difference identity for the actual mutual-energy integral.
All four Fubini and linearity steps are licensed by the bilinear HLS
integrability theorem. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_sub_eq_mutual
    (ρ σ : Space 3 → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρtop : ∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop : ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hdifftop :
      ∫⁻ x, ENNReal.ofReal |ρ x - σ x| ^ ((6 : ℝ) / 5) ≠ ∞) :
    newtonianInteractionEnergy ρ ρ -
        newtonianInteractionEnergy σ σ =
      newtonianInteractionEnergy (ρ - σ) ρ +
        newtonianInteractionEnergy σ (ρ - σ) := by
  have hdiff : Measurable (ρ - σ) := hρ.sub hσ
  have hρρ :=
    integrable_newtonianInteractionKernel_of_lsixFifths
      ρ ρ hρ hρ hρtop hρtop
  have hσσ :=
    integrable_newtonianInteractionKernel_of_lsixFifths
      σ σ hσ hσ hσtop hσtop
  have hdρ :=
    integrable_newtonianInteractionKernel_of_lsixFifths
      (ρ - σ) ρ hdiff hρ hdifftop hρtop
  have hσd :=
    integrable_newtonianInteractionKernel_of_lsixFifths
      σ (ρ - σ) hσ hdiff hσtop hdifftop
  have hρρ' : Integrable
      (fun p : Space 3 × Space 3 =>
        ρ p.1 * ρ p.2 / ‖p.1 - p.2‖) (volume.prod volume) := by
    exact hρρ
  have hσσ' : Integrable
      (fun p : Space 3 × Space 3 =>
        σ p.1 * σ p.2 / ‖p.1 - p.2‖) (volume.prod volume) := by
    exact hσσ
  have hdρ' : Integrable
      (fun p : Space 3 × Space 3 =>
        (ρ - σ) p.1 * ρ p.2 / ‖p.1 - p.2‖) (volume.prod volume) := by
    exact hdρ
  have hσd' : Integrable
      (fun p : Space 3 × Space 3 =>
        σ p.1 * (ρ - σ) p.2 / ‖p.1 - p.2‖) (volume.prod volume) := by
    exact hσd
  unfold newtonianInteractionEnergy
  rw [integral_integral hρρ, integral_integral hσσ,
    integral_integral hdρ, integral_integral hσd,
    ← integral_sub hρρ' hσσ', ← integral_add hdρ' hσd']
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp [Function.uncurry]
  ring

/-- **Quantitative HLS modulus for Newtonian self-energy.**
The difference of two real self-energies is controlled by two bilinear
forms involving the `L^(6/5)` density difference. -/
@[zil_level physical_theorem]
theorem abs_newtonianSelfEnergy_sub_le_hls
    (ρ σ : Space 3 → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρtop : ∫⁻ x, ENNReal.ofReal |ρ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop : ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hdifftop :
      ∫⁻ x, ENNReal.ofReal |ρ x - σ x| ^ ((6 : ℝ) / 5) ≠ ∞) :
    |newtonianSelfEnergy ρ - newtonianSelfEnergy σ| ≤
      newtonianMutualHLSBound (ρ - σ) ρ +
        newtonianMutualHLSBound σ (ρ - σ) := by
  rw [← newtonianInteractionEnergy_self,
    ← newtonianInteractionEnergy_self,
    newtonianSelfEnergy_sub_eq_mutual
      ρ σ hρ hσ hρtop hσtop hdifftop]
  calc
    |newtonianInteractionEnergy (ρ - σ) ρ +
        newtonianInteractionEnergy σ (ρ - σ)|
        ≤ |newtonianInteractionEnergy (ρ - σ) ρ| +
            |newtonianInteractionEnergy σ (ρ - σ)| :=
      abs_add_le _ _
    _ ≤ newtonianMutualHLSBound (ρ - σ) ρ +
          newtonianMutualHLSBound σ (ρ - σ) :=
      add_le_add
        (abs_newtonianInteractionEnergy_le_hls
          (ρ - σ) ρ (hρ.sub hσ) hρ hdifftop hρtop)
        (abs_newtonianInteractionEnergy_le_hls
          σ (ρ - σ) hσ (hρ.sub hσ) hσtop hdifftop)

/-- **Continuity of the real Newtonian self-energy in `L^(6/5)`.**
Strong `L^(6/5)` convergence of measurable densities, expressed through
the defining lintegrals, implies convergence of the repository's actual
Bochner Newtonian self-energy.  The accompanying mass convergence records
the bounded and identified `L^(6/5)` scale of the sequence. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_tendsto_of_lsixFifths
    (ρ : ℕ → Space 3 → ℝ) (σ : Space 3 → ℝ)
    (hρ : ∀ n, Measurable (ρ n)) (hσ : Measurable σ)
    (hρtop : ∀ n,
      ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hσtop :
      ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hdifftop : ∀ n,
      ∫⁻ x, ENNReal.ofReal |ρ n x - σ x| ^ ((6 : ℝ) / 5) ≠ ∞)
    (hdiff :
      Tendsto
        (fun n =>
          ∫⁻ x, ENNReal.ofReal |ρ n x - σ x| ^ ((6 : ℝ) / 5))
        atTop (𝓝 0))
    (hmass :
      Tendsto
        (fun n =>
          ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5))
        atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5)))) :
    Tendsto (fun n => newtonianSelfEnergy (ρ n)) atTop
      (𝓝 (newtonianSelfEnergy σ)) := by
  let d : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal |ρ n x - σ x| ^ ((6 : ℝ) / 5)
  let m : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal |ρ n x| ^ ((6 : ℝ) / 5)
  let mσ : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal |σ x| ^ ((6 : ℝ) / 5)
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa [d] using hdiff
  have hm : Tendsto m atTop (𝓝 mσ) := by
    simpa [m, mσ] using hmass
  have hd56 :
      Tendsto (fun n => d n ^ ((5 : ℝ) / 6)) atTop (𝓝 0) := by
    simpa using hd.ennrpow_const ((5 : ℝ) / 6)
  have hm5 :
      Tendsto (fun n => m n ^ (5 : ℝ)) atTop
        (𝓝 (mσ ^ (5 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto mσ).comp hm
  have hCm5 :
      Tendsto
        (fun n => newtonianRieszSixthConstant * m n ^ (5 : ℝ))
        atTop
        (𝓝 (newtonianRieszSixthConstant * mσ ^ (5 : ℝ))) :=
    ENNReal.Tendsto.const_mul hm5
      (Or.inr newtonianRieszSixthConstant_ne_top)
  have hsecond :
      Tendsto
        (fun n =>
          (newtonianRieszSixthConstant * m n ^ (5 : ℝ))
            ^ ((1 : ℝ) / 6))
        atTop
        (𝓝 ((newtonianRieszSixthConstant * mσ ^ (5 : ℝ))
          ^ ((1 : ℝ) / 6))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp hCm5
  have hmσtop : mσ ≠ ∞ := by
    simpa [mσ] using hσtop
  have hsecondTop :
      (newtonianRieszSixthConstant * mσ ^ (5 : ℝ))
          ^ ((1 : ℝ) / 6) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top
      newtonianRieszSixthConstant_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmσtop)
  have hrawLeft :
      Tendsto
        (fun n =>
          newtonianMutualHLSBoundENNReal (ρ n - σ) (ρ n))
        atTop (𝓝 0) := by
    have hmul :=
      ENNReal.Tendsto.mul hd56 (Or.inr hsecondTop) hsecond
        (Or.inr ENNReal.zero_ne_top)
    simpa [newtonianMutualHLSBoundENNReal, d, m] using hmul
  have hd5 :
      Tendsto (fun n => d n ^ (5 : ℝ)) atTop (𝓝 0) := by
    simpa using hd.ennrpow_const (5 : ℝ)
  have hCd5 :
      Tendsto
        (fun n => newtonianRieszSixthConstant * d n ^ (5 : ℝ))
        atTop (𝓝 0) := by
    simpa using
      ENNReal.Tendsto.const_mul hd5
        (Or.inr newtonianRieszSixthConstant_ne_top)
  have hsecondDiff :
      Tendsto
        (fun n =>
          (newtonianRieszSixthConstant * d n ^ (5 : ℝ))
            ^ ((1 : ℝ) / 6))
        atTop (𝓝 0) := by
    simpa using hCd5.ennrpow_const ((1 : ℝ) / 6)
  have hmσ56top : mσ ^ ((5 : ℝ) / 6) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmσtop
  have hrawRight :
      Tendsto
        (fun n =>
          newtonianMutualHLSBoundENNReal σ (ρ n - σ))
        atTop (𝓝 0) := by
    have hmul :=
      ENNReal.Tendsto.mul tendsto_const_nhds
        (Or.inr ENNReal.zero_ne_top) hsecondDiff
        (Or.inr hmσ56top)
    simpa [newtonianMutualHLSBoundENNReal, d, mσ] using hmul
  have hleft :
      Tendsto
        (fun n => newtonianMutualHLSBound (ρ n - σ) (ρ n))
        atTop (𝓝 0) := by
    unfold newtonianMutualHLSBound
    change Tendsto
      (ENNReal.toReal ∘
        fun n => newtonianMutualHLSBoundENNReal (ρ n - σ) (ρ n))
      atTop (𝓝 (ENNReal.toReal 0))
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrawLeft
  have hright :
      Tendsto
        (fun n => newtonianMutualHLSBound σ (ρ n - σ))
        atTop (𝓝 0) := by
    unfold newtonianMutualHLSBound
    change Tendsto
      (ENNReal.toReal ∘
        fun n => newtonianMutualHLSBoundENNReal σ (ρ n - σ))
      atTop (𝓝 (ENNReal.toReal 0))
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrawRight
  have hupper :
      Tendsto
        (fun n =>
          newtonianMutualHLSBound (ρ n - σ) (ρ n) +
            newtonianMutualHLSBound σ (ρ n - σ))
        atTop (𝓝 0) := by
    simpa using hleft.add hright
  have habs :
      Tendsto
        (fun n =>
          |newtonianSelfEnergy (ρ n) - newtonianSelfEnergy σ|)
        atTop (𝓝 0) :=
    squeeze_zero
      (fun _ => abs_nonneg _)
      (fun n =>
        abs_newtonianSelfEnergy_sub_le_hls
          (ρ n) σ (hρ n) hσ (hρtop n) hσtop (hdifftop n))
      hupper
  have hsub :
      Tendsto
        (fun n => newtonianSelfEnergy (ρ n) - newtonianSelfEnergy σ)
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  simpa using hsub.add_const (newtonianSelfEnergy σ)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_mutualInteraction_le where
  formalizes @ "claim:the-bilinear-general-density-hardy-littlewood-sobolev-estimate-for-two-measurable-l-six-fifths-densities-the-mutual-newton-kernel-form-is-controlled-by-holder-six-fifths-six-and-the-existing-sixth-power-riesz-potential-bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_riesz_sixth_power_le",
  supported_by @ "lean:ENNReal.lintegral_mul_le_Lp_mul_Lq",
  caveat @ "claim:this-is-a-positive-extended-real-bilinear-kernel-bound-not-a-polarization-assumption-for-signed-real-densities"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_hls where
  formalizes @ "claim:finite-l-six-fifths-mass-makes-the-signed-real-mutual-newton-kernel-bochner-integrable-and-bounds-the-absolute-value-of-the-repositorys-actual-mutual-energy-by-the-shared-bilinear-hls-bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_mutualInteraction_le",
  supported_by @ "lean:MeasureTheory.lintegral_prod",
  caveat @ "claim:the-theorem-is-an-analytic-continuity-bound-for-measurable-densities-it-does-not-assert-that-weak-h-one-convergence-alone-implies-strong-l-six-fifths-density-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_symm where
  formalizes @ "claim:newtons-third-law-for-the-mutual-gravitational-energy-the-newtonian-interaction-energy-of-two-mass-densities-the-double-integral-of-rho-x-sigma-y-over-norm-x-minus-y-is-symmetric-in-the-two-sources-by-fubini-and-the-symmetry-of-the-newton-kernel"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_self where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral",
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-mutual-newtonian-interaction-energy-on-the-diagonal-equals-the-gravitational-self-interaction-energy-of-a-single-density"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.abs_newtonianSelfEnergy_sub_le_hls where
  formalizes @ "claim:the-difference-of-two-real-newtonian-self-energies-is-quantitatively-controlled-by-two-bilinear-hls-bounds-containing-the-l-six-fifths-density-difference",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianSelfEnergy_sub_eq_mutual",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.abs_newtonianInteractionEnergy_le_hls",
  caveat @ "claim:the-modulus-requires-finite-l-six-fifths-mass-of-both-densities-and-their-difference"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianSelfEnergy_tendsto_of_lsixFifths where
  formalizes @ "claim:strong-l-six-fifths-convergence-of-measurable-densities-and-convergence-of-their-l-six-fifths-mass-imply-convergence-of-the-actual-real-bochner-newtonian-self-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.abs_newtonianSelfEnergy_sub_le_hls",
  caveat @ "claim:this-discharges-hartree-interaction-convergence-once-the-model-proves-strong-l-six-fifths-density-convergence-it-does-not-derive-that-convergence-from-an-unlocalized-weak-h-one-sequence"

zil_file_contract physlib.newtonianInteractionEnergy where
  promises "The mutual Newtonian gravitational interaction energy of two mass densities, W(rho,sigma) = double integral of rho(x) sigma(y)/norm(x-y) (newtonianInteractionEnergy). The imported sixth-power Riesz estimate and Holder now yield a genuine bilinear general-density HLS theorem. On signed real measurable densities, finite L^(6/5) mass proves product-kernel Bochner integrability and an explicit absolute mutual-energy bound. The polarized difference identity consequently gives a quantitative modulus for self-energy differences, and strong L^(6/5) density convergence plus convergence of the L^(6/5) mass proves convergence of the actual real newtonianSelfEnergy functional. newtonianInteractionEnergy_self identifies the diagonal with self-energy, while newtonianInteractionEnergy_symm proves Newton's third law under its explicit Fubini integrability premise. Honest: the convergence theorem converts strong L^(6/5) density convergence into Hartree convergence; it does not claim generic weak H1 convergence supplies that strong density convergence without localization/compactness."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_riesz_sixth_power_le",
    "lean:ENNReal.lintegral_mul_le_Lp_mul_Lq"]
  forbids_substitutes ["a self-energy of a single density, whereas this is the mutual energy of two distinct sources",
    "an unconditional Fubini swap, whereas the product-integrability hypothesis is carried explicitly",
    "weak H1 convergence relabeled as Hartree convergence without the model-specific strong L^(6/5) density estimate"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_self,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_symm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction.lintegral_mutualInteraction_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianInteractionEnergy_hls,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.abs_newtonianSelfEnergy_sub_le_hls,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy.newtonianSelfEnergy_tendsto_of_lsixFifths]

/- ZIL-END -/
