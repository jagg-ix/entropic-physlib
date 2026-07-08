/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.MeasureModel
public import Physlib.QFT.Wick.Consistency
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lorentzian path-integral kernel, propagator, and Trotter splitting

**Lorentzian** path-integral content at the scalar level:

* `ComplexHamiltonian` — the scalar complex-Hamiltonian model
  `Ĥ = H_R − i·H_I` with `H_I ≥ 0`.  This is the **scalar** layer
  (real-valued `H_R`, `H_I`); the operator-level
  `complexHamiltonian : (H →L[ℂ] H) → (H →L[ℂ] H) → (H →L[ℂ] H)` lives
  in `Physlib.QuantumMechanics.FiniteTarget`.
* `lorentzianKernel S_R S_I ℏ = exp(i·S_R/ℏ − S_I/ℏ)` — the path-integral
  kernel as a Lorentzian (real-time) factor, identified with the
  existing `complexActionWeight` (`lorentzianKernel_eq_complexActionWeight`).
* `lorentzianKernel_factorizes` — phase × damping factorisation.
* `lorentzianKernel_norm_is_damping` — modulus is the entropic damping.
* `lorentzianPropagator H t ℏ = lorentzianKernel(−t·H_R, t·H_I, ℏ)` —
  the scalar Lorentzian propagator for the complex Hamiltonian `H`
  over time `t`, with `lorentzianPropagator_norm_is_damping` and
  `lorentzianPropagator_norm_le_one` (forward-time damping).
* `lorentzianTrotterStep H dt ℏ` — one-step Trotter factorisation of
  the Lorentzian propagator: `exp(−i·dt·H_R/ℏ) · exp(−dt·H_I/ℏ)`.
* `lorentzianTrotterProduct H t ℏ n` — discrete `n + 1`-step Trotter
  product (avoiding division by zero).


## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
- **Grosche 1988** — *Path integration via summation of perturbation expansions*
- **Trotter 1959** — *On the product of semi-groups of operators*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Real Complex

/-! ## §1 — Scalar complex Hamiltonian -/

/-- **Scalar complex Hamiltonian** `Ĥ = H_R − i·H_I`, with `H_I ≥ 0`.
This is the eigen-level / single-mode scalar form used in the
Lorentzian path-integral kernel; the operator-level analog is
`QuantumMechanics.FiniteTarget.complexHamiltonian`. -/
structure ComplexHamiltonian where
  /-- Real (reversible) part. -/
  H_R : ℝ
  /-- Imaginary (dissipative) part, `H_I ≥ 0`. -/
  H_I : ℝ
  /-- Non-negativity of the dissipative part. -/
  H_I_nonneg : 0 ≤ H_I

/-! ## §2 — Lorentzian path-integral kernel -/

/-- **Lorentzian path-integral kernel** `exp(i·S_R/ℏ − S_I/ℏ)`. -/
def lorentzianKernel (S_R S_I ℏ : ℝ) : ℂ :=
  Complex.exp (((S_R / ℏ : ℂ) * Complex.I) - (S_I / ℏ : ℂ))

/-- The Lorentzian kernel is exactly the existing `complexActionWeight`. -/
theorem lorentzianKernel_eq_complexActionWeight (S_R S_I ℏ : ℝ) :
    lorentzianKernel S_R S_I ℏ =
      Physlib.QFT.Wick.Consistency.complexActionWeight S_R S_I ℏ := by
  unfold lorentzianKernel Physlib.QFT.Wick.Consistency.complexActionWeight
  congr 1
  push_cast
  ring

/-- **Kernel factorisation** into oscillatory phase times entropic damping. -/
theorem lorentzianKernel_factorizes (S_R S_I ℏ : ℝ) :
    lorentzianKernel S_R S_I ℏ =
      Complex.exp ((S_R / ℏ : ℂ) * Complex.I) *
        (Real.exp (-(S_I / ℏ)) : ℂ) := by
  unfold lorentzianKernel
  have hreal : (Real.exp (-(S_I / ℏ)) : ℂ) =
      Complex.exp (-(S_I / ℏ : ℂ)) := by
    simp [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [hreal, sub_eq_add_neg, Complex.exp_add]

/-- **Norm of the Lorentzian kernel = entropic damping**:
`‖exp(i·S_R/ℏ − S_I/ℏ)‖ = exp(−S_I/ℏ)`. -/
theorem lorentzianKernel_norm_is_damping (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = Real.exp (-(S_I / ℏ)) := by
  rw [lorentzianKernel_factorizes, norm_mul]
  have hphase : ‖Complex.exp ((S_R / ℏ : ℂ) * Complex.I)‖ = 1 := by
    have : (S_R / ℏ : ℂ) = ((S_R / ℏ : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hphase, one_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **Norm of the Lorentzian kernel = path-integral damping**:
identifies `‖lorentzianKernel‖` with `path_integral_damping`. -/
theorem lorentzianKernel_norm_eq_path_integral_damping (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = path_integral_damping ℏ S_I := by
  rw [lorentzianKernel_norm_is_damping]
  unfold path_integral_damping
  congr 1; ring

/-- The Lorentzian kernel is never zero (it is a complex exponential). -/
theorem lorentzianKernel_ne_zero (S_R S_I ℏ : ℝ) :
    lorentzianKernel S_R S_I ℏ ≠ 0 := by
  rw [lorentzianKernel_eq_complexActionWeight]
  exact Physlib.QFT.Wick.Consistency.complexActionWeight_ne_zero _ _ _

/-! ## §3 — Lorentzian weight on a measure path-integral model -/

/-- **Lorentzian weight** of a measurable path-integral model — same as
its complex weight, named to match Lorentzian conventions. -/
def lorentzianWeight {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) : α → ℂ :=
  m.weight

/-- `‖lorentzianWeight m x‖ = exp(−actionImScaled x)` — modulus is the
damping along each path. -/
theorem lorentzianWeight_norm_is_damping
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (x : α) :
    ‖lorentzianWeight m x‖ = Real.exp (-(m.actionImScaled x)) :=
  m.weight_norm_is_damping x

/-- Lorentzian weight has uniform modulus bound `≤ 1`. -/
theorem lorentzianWeight_bochner_bounded
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (x : α) :
    ‖lorentzianWeight m x‖ ≤ 1 :=
  m.weight_bochner_bounded x

/-! ## §4 — Lorentzian scalar propagator -/

/-- **Lorentzian scalar propagator** for the complex Hamiltonian `Ĥ`:
the kernel with `S_R = −t·H_R` and `S_I = t·H_I`. -/
def lorentzianPropagator (H : ComplexHamiltonian) (t ℏ : ℝ) : ℂ :=
  lorentzianKernel (-(t * H.H_R)) (t * H.H_I) ℏ

/-- **Modulus of the Lorentzian propagator** equals the entropic damping
`exp(−t·H_I/ℏ)`. -/
theorem lorentzianPropagator_norm_is_damping
    (H : ComplexHamiltonian) (t ℏ : ℝ) :
    ‖lorentzianPropagator H t ℏ‖ = Real.exp (-(t * H.H_I / ℏ)) := by
  unfold lorentzianPropagator
  simpa [lorentzianKernel_norm_is_damping, mul_div_assoc] using
    (lorentzianKernel_norm_is_damping (S_R := -(t * H.H_R))
      (S_I := t * H.H_I) (ℏ := ℏ))

/-- **Forward-time damping bound**: for `t ≥ 0, ℏ > 0`,
`‖lorentzianPropagator H t ℏ‖ ≤ 1`. -/
theorem lorentzianPropagator_norm_le_one
    (H : ComplexHamiltonian) (t ℏ : ℝ)
    (ht : 0 ≤ t) (hℏ : 0 < ℏ) :
    ‖lorentzianPropagator H t ℏ‖ ≤ 1 := by
  rw [lorentzianPropagator_norm_is_damping]
  have hnonpos : -(t * H.H_I / ℏ) ≤ 0 := by
    have hnum : 0 ≤ t * H.H_I := mul_nonneg ht H.H_I_nonneg
    have hdiv : 0 ≤ t * H.H_I / ℏ := div_nonneg hnum (le_of_lt hℏ)
    linarith
  simp [Real.exp_le_one_iff, hnonpos]

/-- The Lorentzian propagator is never zero. -/
theorem lorentzianPropagator_ne_zero (H : ComplexHamiltonian) (t ℏ : ℝ) :
    lorentzianPropagator H t ℏ ≠ 0 :=
  lorentzianKernel_ne_zero _ _ _

/-! ## §5 — Trotter splitting (scalar form) -/

/-- **One-step Trotter factorisation** of the Lorentzian propagator at
step `dt`:
`U_step = exp(−i·dt·H_R/ℏ) · exp(−dt·H_I/ℏ)`
— phase from the reversible generator times damping from the
irreversible generator. -/
def lorentzianTrotterStep (H : ComplexHamiltonian) (dt ℏ : ℝ) : ℂ :=
  Complex.exp ((-(dt * H.H_R) / ℏ : ℂ) * Complex.I) *
    (Real.exp (-(dt * H.H_I / ℏ)) : ℂ)

/-- **Discrete Trotter product** with `n + 1` substeps over total time
`t`.  Defined as `(lorentzianTrotterStep H (t / (n + 1)) ℏ) ^ (n + 1)`
to avoid division-by-zero. -/
def lorentzianTrotterProduct (H : ComplexHamiltonian) (t ℏ : ℝ) (n : ℕ) : ℂ :=
  let steps : ℝ := (n + 1)
  let dt : ℝ := t / steps
  (lorentzianTrotterStep H dt ℏ) ^ (n + 1)

/-- The one-step Trotter factor has modulus equal to the entropic damping
of the substep. -/
theorem lorentzianTrotterStep_norm_is_damping
    (H : ComplexHamiltonian) (dt ℏ : ℝ) :
    ‖lorentzianTrotterStep H dt ℏ‖ = Real.exp (-(dt * H.H_I / ℏ)) := by
  unfold lorentzianTrotterStep
  rw [norm_mul]
  have hphase :
      ‖Complex.exp ((-(dt * H.H_R) / ℏ : ℂ) * Complex.I)‖ = 1 := by
    have : (-(dt * H.H_R) / ℏ : ℂ) = (((-(dt * H.H_R) / ℏ : ℝ)) : ℂ) := by
      push_cast; ring
    rw [this]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hphase, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The Trotter factor is never zero (product of non-zero exponentials). -/
theorem lorentzianTrotterStep_ne_zero (H : ComplexHamiltonian) (dt ℏ : ℝ) :
    lorentzianTrotterStep H dt ℏ ≠ 0 := by
  unfold lorentzianTrotterStep
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  exact_mod_cast (ne_of_gt (Real.exp_pos (-(dt * H.H_I / ℏ))))

end Physlib.QFT.PathIntegral

end
