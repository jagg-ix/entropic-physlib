/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid

/-!
# The Cameron–Martin complex Feynman–Kac path integral converges to the QED path integral

Completes `PathIntegral.QEDPathIntegralMeasureValid`: the measure-valid Cameron–Martin complex-action path integral
not only is a rigorous Bochner integral, it **converges to the (oscillatory) QED path integral** as the
entropic regulator is removed. This is the `iε → 0` / regulator-removal limit: the damped weight
`e^{iS_R/ℏ − S_I/ℏ}` is a well-defined Bochner integrand for every `S_I ≥ 0`, and as `S_I → 0` the
expectation converges to the formal oscillatory Feynman/QED amplitude `∫ obs · e^{iS_R/ℏ}`.

The convergence is genuine (dominated convergence): the damping `‖weight‖ = e^{−S_I/ℏ} ≤ 1` is uniformly
bounded by `1`, so on the finite reference measure the integrals converge. So the entropic-damping
regularization of the QED path integral is *consistent* — removing the regulator recovers the QED
oscillatory amplitude.

* **§A — the QED oscillatory amplitude** (`qedOscillatoryAmplitude`): the undamped pure-phase integral
 `∫ obs · e^{iS_R/ℏ} dμ`, the formal Feynman/QED path-integral amplitude (which exists as a Bochner
 integral on the finite reference measure).
* **§B — convergence** (`qed_FK_tendsto_QED`): along any `λ_n → 0⁺`, the damped Feynman–Kac integral
 `∫ obs · e^{iS_R/ℏ − λ_n/ℏ} dμ → ∫ obs · e^{iS_R/ℏ} dμ` — the measure-valid regularization converges to
 the QED amplitude.
* **§C — at the model level** (`qed_model_FK_tendsto_QED`): the QED-exchange model's complex FK
 expectation `⟨obs⟩_{λ_n} → ⟨obs⟩_{QED}` as the fermion entropic damping vanishes.

**Scope.** This is the regulator-removal limit on the finite-measure single-mode model: the damped
expectations converge to the oscillatory amplitude `∫ obs · e^{iS_R/ℏ}`, which is the QED path integral *of
this model*, not the full interacting gauge-field functional integral. The point proved is *consistency*:
the entropically-damped (measure-valid) integral has the oscillatory QED integral as its `S_I → 0` limit.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralConvergence

open Physlib.QFT.PathIntegral MeasureTheory Filter Topology

/-! ## §A — the QED oscillatory amplitude (the undamped limit) -/

/-- **The oscillatory QED path-integral amplitude** `∫ obs · e^{iS_R/ℏ} dμ` — the undamped, pure-phase
Feynman integral, the limit of the entropically-damped path integral as `S_I → 0`. -/
noncomputable def qedOscillatoryAmplitude (ℏ : ℝ) (obs : ℝ → ℂ) (SR : ℝ → ℝ) : ℂ :=
  ∫ x, obs x * Complex.exp (((SR x / ℏ : ℝ) : ℂ) * Complex.I) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))

/-! ## §B — convergence of the damped Feynman–Kac integral to the QED amplitude -/

/-- **[Convergence] The Cameron–Martin damped path integral converges to the QED oscillatory amplitude.**
For a measurable, essentially-bounded observable `obs` and any sequence of entropic regulators `λ_n → 0⁺`,
the damped Feynman–Kac integral converges:
`∫ obs · e^{iS_R/ℏ − λ_n/ℏ} dμ ⟶ ∫ obs · e^{iS_R/ℏ} dμ = qedOscillatoryAmplitude`.
Proof by dominated convergence — the damping `e^{−λ_n/ℏ} ≤ 1` is uniformly bounded by `1`, dominating the
integrand by `‖obs‖ ≤ C` on the finite reference measure. Removing the entropic regulator recovers the QED
path integral. -/
theorem qed_FK_tendsto_QED
    (ℏ : ℝ) (hℏ : 0 < ℏ) (obs : ℝ → ℂ) (hobs : Measurable obs) (C : ℝ)
    (hbound : ∀ x, ‖obs x‖ ≤ C) (SR : ℝ → ℝ) (hSR : Measurable SR)
    (lam : ℕ → ℝ) (hlam0 : ∀ n, 0 ≤ lam n) (hlam : Tendsto lam atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ x, obs x * Complex.exp (((SR x / ℏ : ℝ) : ℂ) * Complex.I - ((lam n / ℏ : ℝ) : ℂ))
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      atTop (𝓝 (qedOscillatoryAmplitude ℏ obs SR)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    refine (hobs.mul (Complex.measurable_exp.comp ?_)).aestronglyMeasurable
    exact ((Complex.measurable_ofReal.comp (hSR.div_const ℏ)).mul measurable_const).sub measurable_const
  · exact integrable_const C
  · intro n
    filter_upwards with x
    rw [norm_mul, Complex.norm_exp]
    have hre : (((SR x / ℏ : ℝ) : ℂ) * Complex.I - ((lam n / ℏ : ℝ) : ℂ)).re = -(lam n / ℏ) := by
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have h1 : Real.exp (-(lam n / ℏ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have : 0 ≤ lam n / ℏ := div_nonneg (hlam0 n) hℏ.le; linarith)
    calc ‖obs x‖ * Real.exp (-(lam n / ℏ)) ≤ C * 1 :=
            mul_le_mul (hbound x) h1 (Real.exp_pos _).le (le_trans (norm_nonneg _) (hbound x))
      _ = C := mul_one C
  · filter_upwards with x
    have hd : Tendsto (fun n => lam n / ℏ) atTop (𝓝 0) := by simpa using hlam.div_const ℏ
    have hc : Tendsto (fun n => ((lam n / ℏ : ℝ) : ℂ)) atTop (𝓝 0) := by
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num]
      exact (Complex.continuous_ofReal.tendsto 0).comp hd
    have harg : Tendsto (fun n => (((SR x / ℏ : ℝ) : ℂ) * Complex.I - ((lam n / ℏ : ℝ) : ℂ)))
        atTop (𝓝 (((SR x / ℏ : ℝ) : ℂ) * Complex.I)) := by
      simpa using (tendsto_const_nhds (x := ((SR x / ℏ : ℝ) : ℂ) * Complex.I)).sub hc
    exact ((Complex.continuous_exp.tendsto _).comp harg).const_mul (obs x)

/-! ## §C — convergence at the QED-exchange model level -/

/-- The QED-exchange model's complex FK expectation is the damped integral with `S_R(x) = x`. -/
theorem qed_model_FK_eq_integral (ℏ lam : ℝ) (hℏ : 0 < ℏ) (hl : 0 ≤ lam) (obs : ℝ → ℂ) :
    (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ lam 0 hℏ hl le_rfl).complexFKExpectation obs
      = ∫ x, obs x * Complex.exp (((x / ℏ : ℝ) : ℂ) * Complex.I - ((lam / ℏ : ℝ) : ℂ))
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  unfold MeasurePathIntegralModel.complexFKExpectation MeasurePathIntegralModel.weight
    MeasurePathIntegralModel.actionReScaled MeasurePathIntegralModel.actionImScaled
    PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel
  congr 1; ext x; congr 2; push_cast; ring

/-- **[Convergence — model level] The QED-exchange complex Feynman–Kac expectation converges to the QED
oscillatory amplitude** as the fermion entropic damping `λ_n → 0⁺`:
`⟨obs⟩_{λ_n} = (qedExchangeModel ℏ λ_n 0).complexFKExpectation obs ⟶ qedOscillatoryAmplitude ℏ obs id`.
The measure-valid Cameron–Martin path integral of the QED single-photon exchange converges to its
oscillatory (undamped) QED amplitude when the regulator is removed. -/
theorem qed_model_FK_tendsto_QED
    (ℏ : ℝ) (hℏ : 0 < ℏ) (obs : ℝ → ℂ) (hobs : Measurable obs) (C : ℝ) (hbound : ∀ x, ‖obs x‖ ≤ C)
    (lam : ℕ → ℝ) (hlam0 : ∀ n, 0 ≤ lam n) (hlam : Tendsto lam atTop (𝓝 0)) :
    Tendsto
      (fun n => (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ (lam n) 0 hℏ (hlam0 n) le_rfl).complexFKExpectation obs)
      atTop (𝓝 (qedOscillatoryAmplitude ℏ obs id)) := by
  have heq : (fun n => (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ (lam n) 0 hℏ (hlam0 n) le_rfl).complexFKExpectation obs)
      = fun n => ∫ x, obs x * Complex.exp (((id x / ℏ : ℝ) : ℂ) * Complex.I - ((lam n / ℏ : ℝ) : ℂ))
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    funext n; exact qed_model_FK_eq_integral ℏ (lam n) hℏ (hlam0 n) obs
  rw [heq]
  exact qed_FK_tendsto_QED ℏ hℏ obs hobs C hbound id measurable_id lam hlam0 hlam

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralConvergence

end
