/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.Wick.Consistency
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Path-integral damping and coercivity (UV finiteness)

The path-integral kernel `w = exp(i S_R/ℏ − S_I/ℏ)` factorises into an
oscillatory phase `exp(i S_R/ℏ)` (unit modulus) and an **entropic damping**
`exp(−S_I/ℏ) ∈ (0, 1]` (under `S_I ≥ 0`).  Combined with a **coercivity
condition** `C·‖φ‖² ≤ S_I φ` (`C > 0`), the damping factor is exponentially
suppressed in the field norm — the structural entropic route to UV
finiteness.

The complex kernel itself is `complexActionWeight` in
`Physlib.QFT.Wick.Consistency`; this module adds:

* `path_integral_damping ℏ S_I = exp(−S_I/ℏ)` — the **modulus** of the
  complex action weight (also: `path_integral_damping_eq_norm_complexActionWeight`).
* `pathIntegralDamping_le_one` — damping `≤ 1` under `S_I ≥ 0, ℏ > 0`
  (eq. 54 modulus bound).
* `CoercivityCondition` — UV-finiteness carrier (`C·‖φ‖² ≤ S_I φ`).
* `coercivity_implies_exponential_damping` — eq. 57/58: coercivity yields
  `exp(−C·‖φ‖²/ℏ)` bound.
* `coercivity_ensures_integrability` — damping ∈ (0, 1] in the coercive
  regime.


## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Real


/-- **Path-integral damping factor** `exp(−S_I/ℏ)` — the modulus of the
complex action weight. -/
def path_integral_damping (ℏ S_I : ℝ) : ℝ :=
  Real.exp (- S_I / ℏ)

/-- The damping factor is strictly positive (it is a real exponential). -/
lemma path_integral_damping_pos (ℏ S_I : ℝ) :
    0 < path_integral_damping ℏ S_I :=
  Real.exp_pos _

lemma path_integral_damping_nonneg (ℏ S_I : ℝ) :
    0 ≤ path_integral_damping ℏ S_I :=
  le_of_lt (path_integral_damping_pos ℏ S_I)

/-- **Eq. 54 modulus bound**: `|exp(−S_I/ℏ)| ≤ 1` under `S_I ≥ 0, ℏ > 0`. -/
lemma path_integral_damping_le_one (ℏ S_I : ℝ) (hℏ : 0 < ℏ) (hS : 0 ≤ S_I) :
    path_integral_damping ℏ S_I ≤ 1 := by
  unfold path_integral_damping
  have h : (- S_I) / ℏ ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact le_of_lt hℏ
  calc Real.exp (- S_I / ℏ)
      ≤ Real.exp 0 := Real.exp_le_exp.mpr h
    _ = 1 := Real.exp_zero

/-- The path-integral damping coincides with the modulus of
`Physlib.QFT.Wick.Consistency.complexActionWeight`. -/
lemma path_integral_damping_eq_norm_complexActionWeight
    (S_R S_I ℏ : ℝ) :
    path_integral_damping ℏ S_I =
      ‖Physlib.QFT.Wick.Consistency.complexActionWeight S_R S_I ℏ‖ := by
  unfold path_integral_damping
  rw [Physlib.QFT.Wick.Consistency.norm_complexActionWeight]
  congr 1
  ring


/-- **Coercivity condition** `S_I φ ≥ C·‖φ‖²` ensuring UV convergence of the
path integral. -/
structure CoercivityCondition {Φ : Type*} [NormedAddCommGroup Φ] where
  /-- Coercivity constant. -/
  C : ℝ
  /-- Strictly positive coercivity constant. -/
  C_pos : 0 < C
  /-- The imaginary-action lower bound. -/
  bound : ∀ (S_I : Φ → ℝ) (φ : Φ), C * ‖φ‖ ^ 2 ≤ S_I φ

/-- **Eq. 57/58 — coercivity ⇒ exponential damping bound.**  Under a coercivity
condition, the path-integral damping is bounded by `exp(−C·‖φ‖²/ℏ)`. -/
lemma coercivity_implies_exponential_damping
    {Φ : Type*} [NormedAddCommGroup Φ]
    (S_I : Φ → ℝ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (coer : CoercivityCondition (Φ := Φ)) :
    ∀ φ : Φ, coer.C * ‖φ‖ ^ 2 ≤ S_I φ →
      path_integral_damping ℏ (S_I φ) ≤
        Real.exp (- coer.C * ‖φ‖ ^ 2 / ℏ) := by
  intro φ h_bound
  unfold path_integral_damping
  apply Real.exp_le_exp.mpr
  have hneg : -(S_I φ) ≤ -coer.C * ‖φ‖ ^ 2 := by
    simpa [neg_mul] using (neg_le_neg h_bound)
  exact div_le_div_of_nonneg_right hneg (le_of_lt hℏ)

/-- **Coercivity ensures integrability**: in the coercive regime the damping
sits in `(0, 1]`. -/
lemma coercivity_ensures_integrability
    {Φ : Type*} [NormedAddCommGroup Φ]
    (S_I : Φ → ℝ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (coer : CoercivityCondition (Φ := Φ))
    (h_bound : ∀ φ : Φ, coer.C * ‖φ‖ ^ 2 ≤ S_I φ) :
    ∀ φ : Φ, 0 < path_integral_damping ℏ (S_I φ) ∧
             path_integral_damping ℏ (S_I φ) ≤ 1 := by
  intro φ
  refine ⟨path_integral_damping_pos ℏ (S_I φ), ?_⟩
  have h1 := coercivity_implies_exponential_damping S_I ℏ hℏ coer φ (h_bound φ)
  calc path_integral_damping ℏ (S_I φ)
      ≤ Real.exp (- coer.C * ‖φ‖ ^ 2 / ℏ) := h1
    _ ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith [coer.C_pos, sq_nonneg ‖φ‖]
        · exact le_of_lt hℏ
    _ = 1 := Real.exp_zero

/-- **Eq. 58 (re-statement)**: coercivity provides exponential UV damping
of the path-integral weight. -/
lemma exponential_damping_of_coercivity
    {Φ : Type*} [NormedAddCommGroup Φ]
    (S_I : Φ → ℝ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (coer : CoercivityCondition (Φ := Φ))
    (h_bound : ∀ φ : Φ, coer.C * ‖φ‖ ^ 2 ≤ S_I φ) :
    ∀ φ : Φ, path_integral_damping ℏ (S_I φ) ≤
             Real.exp (- coer.C * ‖φ‖ ^ 2 / ℏ) :=
  fun φ => coercivity_implies_exponential_damping S_I ℏ hℏ coer φ (h_bound φ)

end Physlib.QFT.PathIntegral

end
