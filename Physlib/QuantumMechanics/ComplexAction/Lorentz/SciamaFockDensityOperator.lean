/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The Hartle–Hawking density matrix as a bounded operator on `ℓ²`

`SciamaThermalDensityMatrix` had the thermal state as a c-number Gibbs distribution `p_n`;
`SciamaFockThermalTrace` computed its (diagonal) trace.  Here the density matrix is a genuine **bounded
operator** on the ℓ² completion: the diagonal multiplier by the Gibbs weights, built from Mathlib's Hölder
multiplier `lp.holderL` (`ℓ^∞ · ℓ² → ℓ²`).

* `thermalDiag` — the Gibbs weights as a bounded `ℓ^∞` diagonal (`0 ≤ p_n ≤ 1`).
* `densityOp` — the density matrix `ρ : ℓ² →L[ℂ] ℓ²`, a genuine **continuous** (bounded) operator.
* `densityOp_apply_fockKet` — `ρ|n⟩ = p_n |n⟩`: the number states are eigenstates with the Gibbs eigenvalues.
* `densityOp_norm_le` — `‖ρ‖ ≤ 1`: the density matrix is a **contraction** (as any state must be).

Honest scope: `ρ` as a bounded diagonal operator with its Gibbs spectrum and contraction bound.  Its
self-adjointness/positivity and the trace-class property `Tr ρ = 1` as an operator trace (beyond the diagonal
`SciamaFockThermalTrace.thermalTrace_normalized`) are the further trace-class theory.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator

open scoped ENNReal NNReal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

/-- **[Gibbs weights are non-negative] `0 ≤ p_n`.** -/
theorem thermalProbability_nonneg (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    0 ≤ thermalProbability β E n := by
  unfold thermalProbability
  have h1 : (0 : ℝ) ≤ 1 - Real.exp (-(β * E)) := by linarith [exp_neg_lt_one β E h]
  exact mul_nonneg (pow_nonneg (Real.exp_pos _).le n) h1

/-- **[Gibbs weights are ≤ 1] `p_n ≤ 1`.** -/
theorem thermalProbability_le_one (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    thermalProbability β E n ≤ 1 := by
  unfold thermalProbability
  have hlt := exp_neg_lt_one β E h
  have hpow : Real.exp (-(β * E)) ^ n ≤ 1 := pow_le_one₀ (Real.exp_pos _).le hlt.le
  have h1 : 1 - Real.exp (-(β * E)) ≤ 1 := by linarith [(Real.exp_pos (-(β * E)))]
  calc Real.exp (-(β * E)) ^ n * (1 - Real.exp (-(β * E)))
      ≤ 1 * 1 := mul_le_mul hpow h1 (by linarith) (by norm_num)
    _ = 1 := one_mul 1

/-- **The Gibbs weights as a bounded `ℓ^∞` diagonal.** -/
def thermalDiag (β E : ℝ) (h : 0 < β * E) : lp (fun _ : ℕ => ℂ) ∞ :=
  ⟨fun n => (thermalProbability β E n : ℂ), by
    show Memℓp (fun n => (thermalProbability β E n : ℂ)) ∞
    rw [memℓp_infty_iff]
    refine ⟨1, ?_⟩
    rintro x ⟨n, rfl⟩
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (thermalProbability_nonneg β E h n)]
    exact thermalProbability_le_one β E h n⟩

@[simp] theorem thermalDiag_coe (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    (thermalDiag β E h : ∀ _ : ℕ, ℂ) n = (thermalProbability β E n : ℂ) := rfl

/-- **[Gibbs diagonal is a contraction] `‖diag(p)‖_∞ ≤ 1`.** -/
theorem thermalDiag_norm_le (β E : ℝ) (h : 0 < β * E) : ‖thermalDiag β E h‖ ≤ 1 := by
  refine lp.norm_le_of_forall_le (by norm_num) (fun n => ?_)
  rw [thermalDiag_coe]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (thermalProbability_nonneg β E h n)]
  exact thermalProbability_le_one β E h n

/-- The multiplier bound `‖·×·‖ ≤ 1`. -/
theorem mul_norm_le : ∀ _ : ℕ, ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ≥0) :=
  fun _ => by simpa using ContinuousLinearMap.opNorm_mul_le ℂ ℂ

/-- **The Hartle–Hawking density matrix** `ρ` as a bounded operator on `ℓ²`: the diagonal multiplier by the
Gibbs weights, built from the Hölder multiplier `ℓ^∞ · ℓ² → ℓ²`. -/
def densityOp (β E : ℝ) (h : 0 < β * E) : FockHilbert →L[ℂ] FockHilbert :=
  lp.holderL 2 (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le (thermalDiag β E h)

/-- **[Gibbs eigenstates] `ρ|n⟩ = p_n|n⟩`.**  The number states are eigenstates of the density operator with
the Gibbs weights as eigenvalues. -/
theorem densityOp_apply_fockKet (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    densityOp β E h (fockKet n) = (thermalProbability β E n : ℂ) • fockKet n := by
  apply lp.ext
  funext i
  simp only [densityOp, lp.holderL, LinearMap.mkContinuous₂_apply, lp.holderₗ_apply_apply_coe,
    ContinuousLinearMap.mul_apply', fockKet, lp.coeFn_single, lp.coeFn_smul, Pi.smul_apply,
    thermalDiag_coe, smul_eq_mul]
  rcases eq_or_ne i n with hi | hi
  · subst hi; simp
  · rw [Pi.single_eq_of_ne hi]; ring

/-- **[Density matrix is a contraction] `‖ρ‖ ≤ 1`.**  As any density matrix, `ρ` has operator norm at most
one. -/
theorem densityOp_norm_le (β E : ℝ) (h : 0 < β * E) : ‖densityOp β E h‖ ≤ 1 := by
  have hL : ‖lp.holderL (p := ∞) (q := 2) 2
      (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le‖ ≤ 1 := by
    simpa using lp.norm_holderL_le (p := ∞) (q := 2) 2
      (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le
  show ‖lp.holderL (p := ∞) (q := 2) 2 (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le
      (thermalDiag β E h)‖ ≤ 1
  refine (ContinuousLinearMap.le_opNorm _ (thermalDiag β E h)).trans ?_
  calc ‖lp.holderL (p := ∞) (q := 2) 2 (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le‖
        * ‖thermalDiag β E h‖
      ≤ 1 * 1 := mul_le_mul hL (thermalDiag_norm_le β E h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator

end
