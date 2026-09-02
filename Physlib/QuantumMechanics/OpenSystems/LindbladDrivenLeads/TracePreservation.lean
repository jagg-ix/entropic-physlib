/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace preservation of the finite LDDL generator

This file proves directly that the Hamiltonian and dissipative parts of the
finite-dimensional Hilbert--Schmidt LDDL generator have zero operator trace.
The proof uses cyclicity of the existing `LinearMap.trace`; no trace-preserving
property is introduced as an assumption.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open HilbertSchmidtOperatorSpace
open LownerHeinzTheorem

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ]

/-- Operator trace as a linear functional on the existing Hilbert--Schmidt
operator space. -/
noncomputable def hsTrace : HSOp ℋ →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ ℋ).comp (hsLinearMapEquiv (ℋ := ℋ)).toLinearMap

@[simp]
theorem hsTrace_apply (rho : HSOp ℋ) :
    hsTrace (ℋ := ℋ) rho = LinearMap.trace ℂ ℋ (toOp rho).toLinearMap :=
  rfl

/-- The Hamiltonian commutator has zero trace. -/
theorem hsTrace_hamiltonianPartHS (H : L ℋ) (rho : HSOp ℋ) :
    hsTrace (ℋ := ℋ) (hamiltonianPartHS H rho) = 0 := by
  rw [hsTrace_apply, hamiltonianPartHS_apply]
  simp only [ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul,
    map_smul, map_sub, smul_eq_mul]
  rw [LinearMap.trace_mul_comm]
  ring

/-- Every individual GKSL dissipator has zero trace. -/
theorem hsTrace_lindbladDissipatorHS (J : L ℋ) (rho : HSOp ℋ) :
    hsTrace (ℋ := ℋ) (lindbladDissipatorHS J rho) = 0 := by
  rw [hsTrace_apply, lindbladDissipatorHS_apply]
  simp only [ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul,
    map_smul, map_sub, smul_eq_mul]
  let j : ℋ →ₗ[ℂ] ℋ := J.toLinearMap
  let x : ℋ →ₗ[ℂ] ℋ := (toOp rho).toLinearMap
  let js : ℋ →ₗ[ℂ] ℋ := (star J).toLinearMap
  change 2 * LinearMap.trace ℂ ℋ (j * x * js) -
      LinearMap.trace ℂ ℋ (js * j * x) -
      LinearMap.trace ℂ ℋ (x * (js * j)) = 0
  rw [LinearMap.trace_mul_cycle]
  rw [LinearMap.trace_mul_comm ℂ x (js * j)]
  ring

/-- Multiplying a dissipator by a physical rate preserves its zero-trace
property. -/
theorem hsTrace_weightedDissipatorHS (lambda : ℝ) (J : L ℋ) (rho : HSOp ℋ) :
    hsTrace (ℋ := ℋ) (weightedDissipatorHS lambda J rho) = 0 := by
  change hsTrace (ℋ := ℋ) ((lambda : ℂ) • lindbladDissipatorHS J rho) = 0
  rw [map_smul, hsTrace_lindbladDissipatorHS, smul_zero]

/-- The complete finite-dimensional LDDL generator is trace preserving at the
infinitesimal level: its output has zero trace for every input operator. -/
theorem hsTrace_lddlGeneratorHS (H Jloss Jgain : L ℋ) (r : RateData)
    (rho : HSOp ℋ) :
    hsTrace (ℋ := ℋ) (lddlGeneratorHS H Jloss Jgain r rho) = 0 := by
  change hsTrace (ℋ := ℋ)
    (hamiltonianPartHS H rho + weightedDissipatorHS (lossRate r) Jloss rho +
      weightedDissipatorHS (gainRate r) Jgain rho) = 0
  rw [map_add, map_add, hsTrace_hamiltonianPartHS,
    hsTrace_weightedDissipatorHS, hsTrace_weightedDissipatorHS, add_zero, zero_add]

/-- The trace functional composed with the finite LDDL generator is the zero
linear map. -/
theorem hsTrace_comp_lddlGeneratorHS (H Jloss Jgain : L ℋ) (r : RateData) :
    (hsTrace (ℋ := ℋ)).comp (lddlGeneratorHS H Jloss Jgain r).toLinearMap = 0 := by
  ext rho
  exact hsTrace_lddlGeneratorHS H Jloss Jgain r rho

end LindbladDrivenLeads
end QuantumMechanics
