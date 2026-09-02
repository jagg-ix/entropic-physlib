/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

/-!
# The displacement operator on the vacuum: `D(α)|0⟩ = |α⟩`

The displacement operator `D(α) = e^{αa† − ᾱa}` generates the coherent state from the vacuum,
`D(α)|0⟩ = |α⟩`.  In normal-ordered form (Baker–Campbell–Hausdorff),

`D(α) = e^{−|α|²/2} e^{αa†} e^{−ᾱa}`,

and on the vacuum the annihilation exponential is trivial, `e^{−ᾱa}|0⟩ = |0⟩` (since `a|0⟩ = 0`), so the whole
content is the **creation exponential** `e^{αa†}|0⟩`.  That is a genuinely convergent `ℓ²` series — it does
not require exponentiating an unbounded operator — because `(a†)ⁿ|0⟩ = √(n!)|n⟩`, hence

`e^{αa†}|0⟩ = Σₙ (αⁿ/n!)(a†)ⁿ|0⟩ = Σₙ (αⁿ/n!)√(n!)|n⟩ = Σₙ (αⁿ/√(n!))|n⟩ = |α⟩`,

the coherent state of `SciamaFockCoherentState`.

* `creationOp_iterate_numberKet_zero` — `(a†)ⁿ|0⟩ = √(n!)|n⟩` (the iterated creation ladder).
* `coherentState_hasSum_fockKet` — `|α⟩ = Σₙ ⟨n|α⟩ |n⟩` (the number-basis expansion of the coherent state).
* `creationExp_vacuum_hasSum` — **`e^{αa†}|0⟩ = |α⟩`**: the creation-exponential series converges to `|α⟩`.
* `displacedVacuum`, `displacedVacuum_norm` — the normalized displaced vacuum `D(α)|0⟩ = e^{−|α|²/2}|α⟩` is a
  **unit vector**.
* `displacedVacuum_annihilation_coord` — `D(α)|0⟩` is an annihilation eigenstate with eigenvalue `α`
  (a minimum-uncertainty coherent state).

Honest scope: the creation-exponential series on the vacuum and the normalized displaced vacuum as a unit
annihilation-eigenstate.  The full displacement operator `D(α)` as a unitary on all of `ℓ²` (an exponential of
the unbounded generator `αa† − ᾱa`) is not built; its action on the vacuum is captured directly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDisplacement

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties

/-- **[Iterated creation ladder] `(a†)ⁿ|0⟩ = √(n!)|n⟩`.**  Applying the creation operator `n` times to the
vacuum reaches the `n`-quantum state, weighted by `√(n!)`. -/
theorem creationOp_iterate_numberKet_zero (n : ℕ) :
    (⇑creationOp)^[n] (numberKet 0) = (Real.sqrt (n.factorial) : ℂ) • numberKet n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, creationOp_numberKet, creationKet, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ))]
    congr 1
    push_cast [Nat.factorial_succ]
    ring

/-- **[Number-basis expansion] `|α⟩ = Σₙ ⟨n|α⟩ |n⟩`.**  The coherent state is the `ℓ²` sum of its number
components. -/
theorem coherentState_hasSum_fockKet (α : ℂ) :
    HasSum (fun n : ℕ => coherentCoeff α n • fockKet n) (coherentState α) := by
  have key : (fun n : ℕ => lp.single 2 n ((coherentState α) n))
      = (fun n : ℕ => coherentCoeff α n • fockKet n) := by
    funext n
    rw [coherentState_apply, fockKet, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [← key]
  exact lp.hasSum_single (by norm_num) (coherentState α)

/-- **[Creation exponential on the vacuum] `e^{αa†}|0⟩ = |α⟩`.**  The series `Σₙ (αⁿ/n!)(a†)ⁿ|0⟩` converges in
`ℓ²` to the coherent state — the displacement operator's action on the vacuum (its annihilation part
`e^{−ᾱa}|0⟩ = |0⟩` is trivial). -/
theorem creationExp_vacuum_hasSum (α : ℂ) :
    HasSum (fun n : ℕ => incl ((α ^ n / (n.factorial : ℂ)) • (⇑creationOp)^[n] (numberKet 0)))
      (coherentState α) := by
  have hnf : ∀ n : ℕ, (n.factorial : ℂ) ≠ 0 := fun n => by
    simp only [ne_eq, Nat.cast_eq_zero]; exact (Nat.factorial_pos n).ne'
  have hne : ∀ n : ℕ, (Real.sqrt (n.factorial) : ℂ) ≠ 0 := fun n => by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsq : ∀ n : ℕ, (Real.sqrt (n.factorial) : ℂ) * (Real.sqrt (n.factorial) : ℂ)
      = (n.factorial : ℂ) := fun n => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  have key : (fun n : ℕ => incl ((α ^ n / (n.factorial : ℂ)) • (⇑creationOp)^[n] (numberKet 0)))
      = (fun n : ℕ => coherentCoeff α n • fockKet n) := by
    funext n
    rw [creationOp_iterate_numberKet_zero, smul_smul, map_smul, incl_numberKet]
    congr 1
    rw [coherentCoeff, div_mul_eq_mul_div, div_eq_div_iff (hnf n) (hne n), mul_assoc, hsq n]
  rw [key]
  exact coherentState_hasSum_fockKet α

/-- **The normalized displaced vacuum** `D(α)|0⟩ = e^{−|α|²/2}|α⟩`. -/
def displacedVacuum (α : ℂ) : FockHilbert := (Real.exp (-(‖α‖ ^ 2 / 2)) : ℂ) • coherentState α

/-- **[Displaced vacuum is a unit vector] `‖D(α)|0⟩‖ = 1`.**  The coherent state normalized by the
displacement's `e^{−|α|²/2}` is a state. -/
theorem displacedVacuum_norm (α : ℂ) : ‖displacedVacuum α‖ = 1 := by
  have hcs : ‖coherentState α‖ = Real.exp (‖α‖ ^ 2 / 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (coherentState α)), coherentState_norm_sq,
      show Real.exp (‖α‖ ^ 2) = Real.exp (‖α‖ ^ 2 / 2) ^ 2 from by
        rw [pow_two (Real.exp (‖α‖ ^ 2 / 2)), ← Real.exp_add]; congr 1; ring,
      Real.sqrt_sq (Real.exp_pos _).le]
  rw [displacedVacuum, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hcs, ← Real.exp_add,
    show -(‖α‖ ^ 2 / 2) + ‖α‖ ^ 2 / 2 = 0 from by ring, Real.exp_zero]

/-- **[Displaced vacuum is an annihilation eigenstate] `a·D(α)|0⟩ = α·D(α)|0⟩`.**  `D(α)|0⟩` is a coherent
state — a minimum-uncertainty annihilation eigenstate with eigenvalue `α`. -/
theorem displacedVacuum_annihilation_coord (α : ℂ) (n : ℕ) :
    (Real.sqrt (n + 1) : ℂ) * displacedVacuum α (n + 1) = α * displacedVacuum α n := by
  rw [displacedVacuum, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    coherentState_apply, coherentState_apply,
    show (Real.sqrt ((n : ℝ) + 1) : ℂ) * ((Real.exp (-(‖α‖ ^ 2 / 2)) : ℂ) * coherentCoeff α (n + 1))
      = (Real.exp (-(‖α‖ ^ 2 / 2)) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℂ) * coherentCoeff α (n + 1))
      from by ring, coherentCoeff_shift]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDisplacement

end
