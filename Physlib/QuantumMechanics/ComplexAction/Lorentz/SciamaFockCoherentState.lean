/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Coherent states: eigenstates of the annihilation operator

The **coherent state** `|α⟩` is the unnormalized `ℓ²` vector with number-basis coefficients
`⟨n|α⟩ = αⁿ/√(n!)`.  It lives in `ℓ²` because `∑ₙ ‖αⁿ/√(n!)‖² = ∑ₙ (‖α‖²)ⁿ/n! = e^{‖α‖²} < ∞` (the exponential
series).  Its defining property is that it is an **eigenstate of the annihilation operator** with eigenvalue
`α`: `a|α⟩ = α|α⟩`.

The annihilation operator acts on `ℓ²` coordinates by the shift `(aψ)ₙ = √(n+1) ψₙ₊₁` (the transpose of
`a†|n⟩ = √(n+1)|n+1⟩`).  On the coherent state this gives
`(a|α⟩)ₙ = √(n+1)·α^{n+1}/√((n+1)!) = α·αⁿ/√(n!) = α⟨n|α⟩`, i.e. `a|α⟩ = α|α⟩`.

* `coherentState α` — `|α⟩` as an `ℓ²` vector; `coherentState_apply` — its coefficients `αⁿ/√(n!)`.
* `coherentCoeff_shift` — the eigenvalue identity coordinate-wise: `√(n+1)⟨n+1|α⟩ = α⟨n|α⟩`.
* `coherentState_isEigenstate` — `a|α⟩ = α|α⟩` at the `ℓ²` level (the annihilation shift equals `α•|α⟩`).

Honest scope: the coherent state as an `ℓ²` vector and its annihilation eigen-equation.  A full unbounded
annihilation `LinearPMap` on all of its natural domain is not built; the shift action is used directly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

open scoped ENNReal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion

/-- **The coherent-state coefficient** `⟨n|α⟩ = αⁿ/√(n!)`. -/
def coherentCoeff (α : ℂ) (n : ℕ) : ℂ := α ^ n / (Real.sqrt (n.factorial) : ℂ)

/-- **[Annihilation eigen-identity, coordinate form] `√(n+1)⟨n+1|α⟩ = α⟨n|α⟩`.**  This is `a|α⟩ = α|α⟩` read
off coordinate-by-coordinate. -/
theorem coherentCoeff_shift (α : ℂ) (n : ℕ) :
    (Real.sqrt (n + 1) : ℂ) * coherentCoeff α (n + 1) = α * coherentCoeff α n := by
  have hs1 : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs2 : (Real.sqrt (n.factorial) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsucc : (Real.sqrt ((n + 1).factorial) : ℂ)
      = (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt (n.factorial) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    congr 2
    push_cast [Nat.factorial_succ]
    ring
  rw [coherentCoeff, coherentCoeff, hsucc, pow_succ]
  field_simp

/-- **The coherent-state coefficients are square-summable** (`∑ (‖α‖²)ⁿ/n! = e^{‖α‖²}`). -/
theorem coherentCoeff_memℓp (α : ℂ) : Memℓp (coherentCoeff α) 2 := by
  refine memℓp_gen ?_
  have key : (fun n => ‖coherentCoeff α n‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun n => (‖α‖ ^ 2) ^ n / (n.factorial : ℝ)) := by
    funext n
    rw [coherentCoeff, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      div_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity)]
  rw [key]
  exact Real.summable_pow_div_factorial (‖α‖ ^ 2)

/-- **The coherent state** `|α⟩` as an `ℓ²` vector. -/
def coherentState (α : ℂ) : FockHilbert := ⟨coherentCoeff α, coherentCoeff_memℓp α⟩

@[simp] theorem coherentState_apply (α : ℂ) (n : ℕ) :
    (coherentState α) n = coherentCoeff α n := rfl

/-- The annihilation shift of the coherent state is square-summable (it equals `α•|α⟩`). -/
theorem coherentState_shift_memℓp (α : ℂ) :
    Memℓp (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1) : ℂ) * (coherentState α) (n + 1)) 2 := by
  have h : (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1) : ℂ) * (coherentState α) (n + 1))
      = ⇑(α • coherentState α) := by
    funext n
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coherentState_apply, coherentState_apply]
    exact coherentCoeff_shift α n
  rw [h]
  exact lp.memℓp _

/-- **[Coherent state is an annihilation eigenstate] `a|α⟩ = α|α⟩`.**  Applying the annihilation shift
`(aψ)ₙ = √(n+1)ψₙ₊₁` to `|α⟩` reproduces `α|α⟩`. -/
theorem coherentState_isEigenstate (α : ℂ) :
    (⟨fun n : ℕ => (Real.sqrt ((n : ℝ) + 1) : ℂ) * (coherentState α) (n + 1),
      coherentState_shift_memℓp α⟩ : FockHilbert) = α • coherentState α := by
  apply lp.ext
  funext n
  show (Real.sqrt ((n : ℝ) + 1) : ℂ) * (coherentState α) (n + 1) = (α • coherentState α) n
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [coherentState_apply]
  exact coherentCoeff_shift α n

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

end
