/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Properties of coherent states: overlap, norm, and Poissonian statistics

Building on `SciamaFockCoherentState` (`|α⟩` with `⟨n|α⟩ = αⁿ/√(n!)`, `a|α⟩ = α|α⟩`):

* `coherentState_inner` — the **overlap** `⟨α|β⟩ = e^{ᾱβ}`: distinct coherent states are never orthogonal
  (the coherent states form an *overcomplete* system).
* `coherentState_norm_sq` — `‖|α⟩‖² = e^{|α|²}`: the (unnormalized) coherent state's norm.
* `coherentState_photon_amp_sq` — `|⟨n|α⟩|² = |α|^{2n}/n!`, and `coherentState_photon_poisson` —
  `|⟨n|α⟩|²/‖|α⟩‖² = e^{-|α|²}|α|^{2n}/n!`: the photon-number statistics of a coherent state are **Poissonian**.

Honest scope: the exact overlap/norm/statistics of the (unnormalized) coherent states, via the exponential
series `∑ zⁿ/n! = e^z`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **[Coherent-state overlap] `⟨α|β⟩ = e^{ᾱβ}`.**  Distinct coherent states are non-orthogonal — the
coherent states are overcomplete. -/
theorem coherentState_inner (α β : ℂ) :
    ⟪coherentState α, coherentState β⟫ = Complex.exp ((starRingEnd ℂ) α * β) := by
  rw [lp.inner_eq_tsum, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  refine tsum_congr (fun n => ?_)
  have hpos : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
  have hne : (Real.sqrt (n.factorial) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsq : (Real.sqrt (n.factorial) : ℂ) * (Real.sqrt (n.factorial) : ℂ) = (n.factorial : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos, Complex.ofReal_natCast]
  rw [coherentState_apply, coherentState_apply, coherentCoeff, coherentCoeff, RCLike.inner_apply,
    map_div₀, map_pow, Complex.conj_ofReal, smul_eq_mul, div_mul_div_comm, hsq, ← mul_pow]
  rw [mul_comm ((starRingEnd ℂ) α) β, mul_comm ((n.factorial : ℂ)⁻¹) ((β * (starRingEnd ℂ) α) ^ n),
    mul_comm β ((starRingEnd ℂ) α)]
  rw [div_eq_mul_inv]

/-- **[Coherent-state norm] `‖|α⟩‖² = e^{|α|²}`.** -/
theorem coherentState_norm_sq (α : ℂ) : ‖coherentState α‖ ^ 2 = Real.exp (‖α‖ ^ 2) := by
  have h := coherentState_inner α α
  have hca : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, RCLike.mul_conj]; norm_cast
  rw [hca, ← Complex.ofReal_exp] at h
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (coherentState α), h]
  exact Complex.ofReal_re _

/-- **[Photon amplitude] `|⟨n|α⟩|² = |α|^{2n}/n!`.** -/
theorem coherentState_photon_amp_sq (α : ℂ) (n : ℕ) :
    ‖⟪fockKet n, coherentState α⟫‖ ^ 2 = ‖α‖ ^ (2 * n) / n.factorial := by
  rw [fockKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, coherentState_apply,
    coherentCoeff, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, ← pow_mul, Real.sq_sqrt (by positivity),
    mul_comm n 2]

/-- **[Poissonian statistics] `|⟨n|α⟩|²/‖|α⟩‖² = e^{-|α|²}|α|^{2n}/n!`.**  The photon-number distribution of a
coherent state is a Poisson distribution with mean `|α|²`. -/
theorem coherentState_photon_poisson (α : ℂ) (n : ℕ) :
    ‖⟪fockKet n, coherentState α⟫‖ ^ 2 / ‖coherentState α‖ ^ 2
      = Real.exp (-(‖α‖ ^ 2)) * (‖α‖ ^ (2 * n) / n.factorial) := by
  rw [coherentState_photon_amp_sq, coherentState_norm_sq, Real.exp_neg]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties

end