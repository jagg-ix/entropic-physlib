/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Euclidean free Schrödinger evolution on `L²`

This module implements the genuine infinite-dimensional `L²(ℝⁿ)` layer
described in the introduction of Jonathan Hickman's exposition of the
Du--Zhang theorem (arXiv:2304.02507).

For the paper-normalized frequency phase

`mₜ(ξ) = exp(i t ‖ξ‖²)`,

the free evolution is defined through Mathlib's Plancherel isometry by

`U(t)f = 𝓕⁻(mₜ · 𝓕f)`.

We prove that:

* the frequency multiplier and physical-space evolution are isometries;
* they satisfy the additive one-parameter composition law;
* `U(0)f = f`;
* `U(t)f → f` strongly in `L²(ℝⁿ)` as `t → 0`.

The strong-continuity proof is the direct Plancherel/dominated-convergence
argument indicated around equations (4)--(6) of the paper.

## Scope boundary

Strong `L²` convergence is not pointwise or almost-everywhere convergence.
This file does not formalize a Schrödinger maximal operator, a Sobolev
regularity threshold, the Bourgain counterexample, or the Du--Zhang theorem.
The phase convention follows the paper's Fourier normalization; relating it to
another normalization of the Laplacian requires the corresponding `2π`
conversion.

## Reference

Jonathan Hickman, *Pointwise convergence for the Schrödinger equation (after
Xiumin Du and Ruixiang Zhang)*, arXiv:2304.02507, 2023.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory
open scoped FourierTransform ENNReal NNReal

namespace Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution

/-- Complex-valued `L²(ℝⁿ)`, represented using Mathlib's Euclidean-space
Fourier transform and Plancherel isometry. -/
abbrev EuclideanL2 (n : ℕ) :=
  Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2

/-- The paper-normalized free Schrödinger frequency phase
`exp(i t ‖ξ‖²)`. -/
def freeSchrodingerPhase {n : ℕ}
    (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (Complex.I * Complex.ofReal (t * ‖ξ‖ ^ 2))

@[simp] lemma freeSchrodingerPhase_zero {n : ℕ}
    (ξ : EuclideanSpace ℝ (Fin n)) :
    freeSchrodingerPhase 0 ξ = 1 := by
  simp [freeSchrodingerPhase]

lemma freeSchrodingerPhase_add {n : ℕ}
    (s t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    freeSchrodingerPhase (s + t) ξ =
      freeSchrodingerPhase s ξ * freeSchrodingerPhase t ξ := by
  unfold freeSchrodingerPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma norm_freeSchrodingerPhase {n : ℕ}
    (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖freeSchrodingerPhase t ξ‖ = 1 := by
  have hre :
      (Complex.I * Complex.ofReal (t * ‖ξ‖ ^ 2)).re = 0 := by
    let r : ℝ := t * ‖ξ‖ ^ 2
    change (Complex.I * Complex.ofReal r).re = 0
    simp
  rw [freeSchrodingerPhase, Complex.norm_exp, hre, Real.exp_zero]

lemma continuous_freeSchrodingerPhase {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      freeSchrodingerPhase p.1 p.2) := by
  unfold freeSchrodingerPhase
  fun_prop

lemma aestronglyMeasurable_freeSchrodingerPhase_mul {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    AEStronglyMeasurable
      (fun ξ => freeSchrodingerPhase t ξ * f ξ) := by
  exact
    ((continuous_freeSchrodingerPhase.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)

/-- Multiplication by the free Schrödinger phase preserves membership in
frequency-space `L²`. -/
lemma memLp_freeSchrodingerPhase_mul {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    MemLp (fun ξ => freeSchrodingerPhase t ξ * f ξ) 2 := by
  exact (Lp.memLp f).congr_norm
    (aestronglyMeasurable_freeSchrodingerPhase_mul t f)
    (Filter.Eventually.of_forall fun ξ => by
      rw [norm_mul, norm_freeSchrodingerPhase, one_mul])

/-- The free Schrödinger multiplier on frequency-space `L²`. -/
def freeSchrodingerMultiplier {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) : EuclideanL2 n :=
  (memLp_freeSchrodingerPhase_mul t f).toLp
    (fun ξ => freeSchrodingerPhase t ξ * f ξ)

lemma freeSchrodingerMultiplier_coeFn {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    freeSchrodingerMultiplier t f =ᵐ[volume]
      fun ξ => freeSchrodingerPhase t ξ * f ξ :=
  MemLp.coeFn_toLp _

@[simp] lemma freeSchrodingerMultiplier_zero_time {n : ℕ}
    (f : EuclideanL2 n) :
    freeSchrodingerMultiplier 0 f = f := by
  apply Lp.ext (μ := volume)
  filter_upwards [freeSchrodingerMultiplier_coeFn 0 f] with ξ hξ
  simpa using hξ

lemma freeSchrodingerMultiplier_add {n : ℕ}
    (s t : ℝ) (f : EuclideanL2 n) :
    freeSchrodingerMultiplier (s + t) f =
      freeSchrodingerMultiplier s (freeSchrodingerMultiplier t f) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    freeSchrodingerMultiplier_coeFn (s + t) f,
    freeSchrodingerMultiplier_coeFn t f,
    freeSchrodingerMultiplier_coeFn s (freeSchrodingerMultiplier t f)
  ] with ξ hst ht hs
  rw [hst, hs, ht, freeSchrodingerPhase_add]
  ring

lemma freeSchrodingerMultiplier_map_add {n : ℕ}
    (t : ℝ) (f g : EuclideanL2 n) :
    freeSchrodingerMultiplier t (f + g) =
      freeSchrodingerMultiplier t f + freeSchrodingerMultiplier t g := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    freeSchrodingerMultiplier_coeFn t (f + g),
    freeSchrodingerMultiplier_coeFn t f,
    freeSchrodingerMultiplier_coeFn t g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (freeSchrodingerMultiplier t f)
      (freeSchrodingerMultiplier t g)
  ] with ξ hsum hf hg hfg hout
  rw [hsum, hfg, hout]
  change
    freeSchrodingerPhase t ξ * (f ξ + g ξ) =
      freeSchrodingerMultiplier t f ξ +
        freeSchrodingerMultiplier t g ξ
  rw [hf, hg]
  ring

lemma freeSchrodingerMultiplier_map_smul {n : ℕ}
    (t : ℝ) (a : ℂ) (f : EuclideanL2 n) :
    freeSchrodingerMultiplier t (a • f) =
      a • freeSchrodingerMultiplier t f := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    freeSchrodingerMultiplier_coeFn t (a • f),
    freeSchrodingerMultiplier_coeFn t f,
    Lp.coeFn_smul a f,
    Lp.coeFn_smul a (freeSchrodingerMultiplier t f)
  ] with ξ hmul hf haf hout
  rw [hmul, haf, hout]
  change
    freeSchrodingerPhase t ξ * (a * f ξ) =
      a * freeSchrodingerMultiplier t f ξ
  rw [hf]
  ring

/-- Exact frequency-space `L²` norm conservation. -/
@[simp] lemma norm_freeSchrodingerMultiplier {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    ‖freeSchrodingerMultiplier t f‖ = ‖f‖ := by
  rw [freeSchrodingerMultiplier, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul, norm_freeSchrodingerPhase, one_mul]

/-- The phase multiplier as a bundled complex-linear isometric automorphism of
frequency-space `L²`.  Its inverse is the multiplier at time `-t`. -/
def freeSchrodingerMultiplierₗᵢ {n : ℕ}
    (t : ℝ) : EuclideanL2 n ≃ₗᵢ[ℂ] EuclideanL2 n where
  toFun := freeSchrodingerMultiplier t
  invFun := freeSchrodingerMultiplier (-t)
  left_inv f := by
    calc
      freeSchrodingerMultiplier (-t) (freeSchrodingerMultiplier t f) =
          freeSchrodingerMultiplier (-t + t) f :=
        (freeSchrodingerMultiplier_add (-t) t f).symm
      _ = f := by simp
  right_inv f := by
    calc
      freeSchrodingerMultiplier t (freeSchrodingerMultiplier (-t) f) =
          freeSchrodingerMultiplier (t + -t) f :=
        (freeSchrodingerMultiplier_add t (-t) f).symm
      _ = f := by simp
  map_add' := freeSchrodingerMultiplier_map_add t
  map_smul' := freeSchrodingerMultiplier_map_smul t
  norm_map' := norm_freeSchrodingerMultiplier t

@[simp] lemma freeSchrodingerMultiplierₗᵢ_apply {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    freeSchrodingerMultiplierₗᵢ t f =
      freeSchrodingerMultiplier t f :=
  rfl

/-! ## Strong continuity of the frequency multiplier -/

private lemma multiplier_error_sq_integral_tendsto_zero {n : ℕ}
    (f : EuclideanL2 n) :
    Tendsto
      (fun t : ℝ =>
        ∫ ξ, ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
  let F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun t ξ => ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ^ 2
  have hF_meas :
      ∀ᶠ t : ℝ in 𝓝 0, AEStronglyMeasurable (F t) := by
    filter_upwards [] with t
    exact
      (((aestronglyMeasurable_freeSchrodingerPhase_mul t f).sub
        (Lp.aestronglyMeasurable f)).norm.pow 2)
  have hbound :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ ξ ∂volume,
        ‖F t ξ‖ ≤ 4 * ‖f ξ‖ ^ 2 := by
    filter_upwards [] with t
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _)]
      have hnorm :
          ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ≤ 2 * ‖f ξ‖ := by
        calc
          ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖
              ≤ ‖freeSchrodingerPhase t ξ * f ξ‖ + ‖f ξ‖ := norm_sub_le _ _
          _ = 2 * ‖f ξ‖ := by
            rw [norm_mul, norm_freeSchrodingerPhase]
            ring
      calc
        ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ^ 2
            ≤ (2 * ‖f ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = 4 * ‖f ξ‖ ^ 2 := by ring
  have hbound_integrable :
      Integrable (fun ξ : EuclideanSpace ℝ (Fin n) =>
        4 * ‖f ξ‖ ^ 2) :=
    ((Lp.memLp f).integrable_norm_pow two_ne_zero).const_mul 4
  have hlim :
      ∀ᵐ ξ ∂volume, Tendsto (fun t : ℝ => F t ξ) (𝓝 0) (𝓝 0) := by
    filter_upwards [] with ξ
    have hphase :
        Tendsto (fun t : ℝ => freeSchrodingerPhase t ξ)
          (𝓝 0) (𝓝 1) := by
      have hcontinuous :
          Continuous (fun t : ℝ => freeSchrodingerPhase t ξ) :=
        continuous_freeSchrodingerPhase.comp
          (continuous_id.prodMk continuous_const)
      rw [← freeSchrodingerPhase_zero ξ]
      exact hcontinuous.continuousAt
    dsimp [F]
    convert (((hphase.mul_const (f ξ)).sub tendsto_const_nhds).norm.pow 2) using 1
    simp
  simpa [F] using
    tendsto_integral_filter_of_dominated_convergence
      (fun ξ : EuclideanSpace ℝ (Fin n) => 4 * ‖f ξ‖ ^ 2)
      hF_meas hbound hbound_integrable hlim

private lemma norm_sq_multiplier_sub_eq_integral {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    ‖freeSchrodingerMultiplier t f - f‖ ^ 2 =
      ∫ ξ, ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re
      (MeasureTheory.L2.integrable_inner
        (freeSchrodingerMultiplier t f - f)
        (freeSchrodingerMultiplier t f - f))]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub (freeSchrodingerMultiplier t f) f,
    freeSchrodingerMultiplier_coeFn t f
  ] with ξ hsub hmul
  rw [hsub]
  change
    RCLike.re
        (inner ℂ
          (freeSchrodingerMultiplier t f ξ - f ξ)
          (freeSchrodingerMultiplier t f ξ - f ξ)) =
      ‖freeSchrodingerPhase t ξ * f ξ - f ξ‖ ^ 2
  rw [hmul, inner_self_eq_norm_sq]

/-- Strong `L²` recovery in frequency space:
`mₜ · f → f` as `t → 0`. -/
lemma freeSchrodingerMultiplier_tendsto_zero {n : ℕ}
    (f : EuclideanL2 n) :
    Tendsto (fun t : ℝ => freeSchrodingerMultiplier t f)
      (𝓝 0) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsq :
      Tendsto
        (fun t : ℝ => ‖freeSchrodingerMultiplier t f - f‖ ^ 2)
        (𝓝 0) (𝓝 0) := by
    simpa only [norm_sq_multiplier_sub_eq_integral] using
      multiplier_error_sq_integral_tendsto_zero f
  have heventually :=
    hsq.eventually (Iio_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [heventually] with t ht
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (freeSchrodingerMultiplier t f - f)]

/-! ## Physical-space free Schrödinger evolution -/

/-- The free Schrödinger evolution on `L²(ℝⁿ)`, defined as the inverse Fourier
transform of the unit-modulus frequency multiplier. -/
def freeSchrodingerEvolution {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) : EuclideanL2 n :=
  𝓕⁻ (freeSchrodingerMultiplier t (𝓕 f))

/-- The physical-space free Schrödinger evolution as a bundled complex-linear
isometric automorphism. -/
def freeSchrodingerEvolutionₗᵢ {n : ℕ}
    (t : ℝ) : EuclideanL2 n ≃ₗᵢ[ℂ] EuclideanL2 n :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
      (EuclideanSpace ℝ (Fin n)) ℂ).trans
    ((freeSchrodingerMultiplierₗᵢ t).trans
      (MeasureTheory.Lp.fourierTransformₗᵢ
        (EuclideanSpace ℝ (Fin n)) ℂ).symm)

@[simp] lemma freeSchrodingerEvolutionₗᵢ_apply {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    freeSchrodingerEvolutionₗᵢ t f =
      freeSchrodingerEvolution t f :=
  rfl

@[simp] lemma freeSchrodingerEvolution_zero {n : ℕ}
    (f : EuclideanL2 n) :
    freeSchrodingerEvolution 0 f = f := by
  simp [freeSchrodingerEvolution]

lemma freeSchrodingerEvolution_add {n : ℕ}
    (s t : ℝ) (f : EuclideanL2 n) :
    freeSchrodingerEvolution (s + t) f =
      freeSchrodingerEvolution s (freeSchrodingerEvolution t f) := by
  simp [freeSchrodingerEvolution, freeSchrodingerMultiplier_add]

/-- Conservation of `L²` energy for the Euclidean free Schrödinger flow. -/
@[simp] lemma norm_freeSchrodingerEvolution {n : ℕ}
    (t : ℝ) (f : EuclideanL2 n) :
    ‖freeSchrodingerEvolution t f‖ = ‖f‖ := by
  have hinv :
      ‖𝓕⁻ (freeSchrodingerMultiplier t (𝓕 f))‖ =
        ‖freeSchrodingerMultiplier t (𝓕 f)‖ := by
    have h :=
      MeasureTheory.Lp.norm_fourier_eq
        (𝓕⁻ (freeSchrodingerMultiplier t (𝓕 f)))
    simpa using h.symm
  rw [freeSchrodingerEvolution, hinv,
    norm_freeSchrodingerMultiplier, MeasureTheory.Lp.norm_fourier_eq]

/-- Strong `L²(ℝⁿ)` initial-data recovery:
`e^{itΔ}f → f` as `t → 0`. -/
lemma freeSchrodingerEvolution_tendsto_zero {n : ℕ}
    (f : EuclideanL2 n) :
    Tendsto (fun t : ℝ => freeSchrodingerEvolution t f)
      (𝓝 0) (𝓝 f) := by
  have hinv :
      Tendsto (𝓕⁻ : EuclideanL2 n → EuclideanL2 n)
        (𝓝 (𝓕 f)) (𝓝 f) := by
    have h :
        Tendsto (𝓕⁻ : EuclideanL2 n → EuclideanL2 n)
          (𝓝 (𝓕 f)) (𝓝 (𝓕⁻ (𝓕 f))) :=
      (ContinuousFourierInv.continuous_fourierInv :
        Continuous (𝓕⁻ : EuclideanL2 n → EuclideanL2 n)).continuousAt
    simpa only [FourierTransform.fourierInv_fourier_eq] using h
  exact hinv.comp (freeSchrodingerMultiplier_tendsto_zero (𝓕 f))

/-- Capstone certificate for the Euclidean `L²` free Schrödinger layer:
identity, composition, energy conservation, and strong initial-data recovery. -/
lemma euclideanL2_freeSchrodinger_unitaryStronglyContinuous {n : ℕ}
    (f : EuclideanL2 n) :
    (∀ t : ℝ,
      freeSchrodingerEvolutionₗᵢ t f =
        freeSchrodingerEvolution t f) ∧
    freeSchrodingerEvolution 0 f = f ∧
    (∀ s t : ℝ,
      freeSchrodingerEvolution (s + t) f =
        freeSchrodingerEvolution s (freeSchrodingerEvolution t f)) ∧
    (∀ t : ℝ, ‖freeSchrodingerEvolution t f‖ = ‖f‖) ∧
    Tendsto (fun t : ℝ => freeSchrodingerEvolution t f)
      (𝓝 0) (𝓝 f) := by
  exact ⟨fun t => freeSchrodingerEvolutionₗᵢ_apply t f,
    freeSchrodingerEvolution_zero f,
    fun s t => freeSchrodingerEvolution_add s t f,
    fun t => norm_freeSchrodingerEvolution t f,
    freeSchrodingerEvolution_tendsto_zero f⟩

end Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
