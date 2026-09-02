/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The density matrix is self-adjoint and positive

`SciamaFockDensityOperator` built the Hartle–Hawking density matrix `ρ` as a bounded contraction with the
Gibbs spectrum.  This completes the **density-matrix axioms**: `ρ` is self-adjoint and positive.  Together
with the (diagonal) unit trace `SciamaFockThermalTrace.thermalTrace_normalized`, `ρ` satisfies all the defining
properties of a density operator — self-adjoint, positive, unit trace, contraction.

* `densityOp_apply_coe` — the diagonal action `(ρx)_i = p_i x_i` on a general vector.
* `densityOp_isSymmetric`, `densityOp_isSelfAdjoint` — `ρ = ρ†` (the Gibbs weights are real).
* `densityOp_re_inner_self_nonneg` — `0 ≤ ⟨x, ρx⟩` (the Gibbs weights are non-negative): `ρ ≥ 0`.
* `densityOp_isPositive` — `ρ` is a positive operator.

Honest scope: self-adjointness and positivity of the bounded diagonal operator via the ℓ² inner product.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **[Diagonal action] `(ρx)_i = p_i x_i`.** -/
theorem densityOp_apply_coe (β E : ℝ) (h : 0 < β * E) (x : FockHilbert) (i : ℕ) :
    (densityOp β E h x) i = (thermalProbability β E i : ℂ) * x i := by
  simp only [densityOp, lp.holderL, LinearMap.mkContinuous₂_apply, lp.holderₗ_apply_apply_coe,
    ContinuousLinearMap.mul_apply', thermalDiag_coe]

/-- **[Hermitian] `ρ = ρ†` (weak form).**  `⟨ρx, y⟩ = ⟨x, ρy⟩` — the Gibbs weights are real. -/
theorem densityOp_isSymmetric (β E : ℝ) (h : 0 < β * E) :
    (↑(densityOp β E h) : FockHilbert →ₗ[ℂ] FockHilbert).IsSymmetric := by
  intro x y
  rw [ContinuousLinearMap.coe_coe, lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun i => ?_)
  rw [densityOp_apply_coe, densityOp_apply_coe, RCLike.inner_apply, RCLike.inner_apply, map_mul,
    Complex.conj_ofReal]
  ring

/-- **[Self-adjoint] `ρ = ρ†`.** -/
theorem densityOp_isSelfAdjoint (β E : ℝ) (h : 0 < β * E) : IsSelfAdjoint (densityOp β E h) :=
  (densityOp_isSymmetric β E h).isSelfAdjoint

/-- **[Positive] `0 ≤ ⟨x, ρx⟩`.**  The Gibbs weights are non-negative, so `ρ` is a positive operator. -/
theorem densityOp_re_inner_self_nonneg (β E : ℝ) (h : 0 < β * E) (x : FockHilbert) :
    0 ≤ (⟪densityOp β E h x, x⟫ : ℂ).re := by
  refine (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) (densityOp β E h x) x)).nonneg (fun i => ?_)
  rw [densityOp_apply_coe, RCLike.inner_apply]
  have key : x i * (starRingEnd ℂ) ((thermalProbability β E i : ℂ) * x i)
      = ((thermalProbability β E i * Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal,
      show x i * ((thermalProbability β E i : ℂ) * (starRingEnd ℂ) (x i))
        = (thermalProbability β E i : ℂ) * (x i * (starRingEnd ℂ) (x i)) from by ring,
      Complex.mul_conj]
    push_cast; ring
  rw [key, Complex.ofReal_re]
  exact mul_nonneg (thermalProbability_nonneg β E h i) (Complex.normSq_nonneg _)

/-- **[Positive operator]** `ρ` is a positive operator (self-adjoint with non-negative diagonal form). -/
theorem densityOp_isPositive (β E : ℝ) (h : 0 < β * E) : (densityOp β E h).IsPositive :=
  ⟨densityOp_isSymmetric β E h, densityOp_re_inner_self_nonneg β E h⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive

end
