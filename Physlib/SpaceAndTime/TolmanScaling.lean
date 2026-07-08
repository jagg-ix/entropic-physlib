/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Lapse

/-!
# Tolman scaling

A `TolmanScaling` packages an asymptotic value `O_∞`, a position-dependent local
value `O_loc : SpaceTime → ℝ`, and a lapse `N`, subject to the Tolman invariant
`O_loc(x) · N(x) = O_∞`. This is the generic structure behind gravitational
redshift laws (temperature, decoherence rate, clock rate, …): any quantity that
redshifts by the lapse satisfies the same law.

(The field is named `localValue` because `local` is a reserved keyword.)

## Source and equation map

* R. C. Tolman, *On the Weight of Heat and Thermal Equilibrium in General Relativity*,
  Physical Review 35 (1930), 904-924, doi:10.1103/PhysRev.35.904.
* R. C. Tolman and P. Ehrenfest, *Temperature Equilibrium in a Static Gravitational
  Field*, Physical Review 36 (1930), 1791-1798, doi:10.1103/PhysRev.36.1791.
* C. Rovelli and M. Smerlak, *Thermal time and Tolman-Ehrenfest effect: temperature as
  the speed of time*, Classical and Quantum Gravity 28 (2011), 075007,
  doi:10.1088/0264-9381/28/7/075007.

The physical Tolman-Ehrenfest temperature law is `T(x) N(x) = T_∞` in lapse notation
(for a static metric, `N = sqrt(-g_00)` in common sign conventions). This file abstracts
that equation to any scalar observable `O` satisfying `O_loc(x) * N(x) = O_∞`.
-/

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

variable {sd : ℕ}

/-- A quantity that redshifts by the lapse: `O_loc(x) · N(x) = O_∞`. -/
structure TolmanScaling (sd : ℕ) where
  /-- The lapse field. -/
  L : Lapse sd
  /-- Asymptotic (infinity-frame) value. -/
  asymptotic : ℝ
  /-- Locally measured value at each event. -/
  localValue : SpaceTime sd → ℝ
  /-- Tolman invariant. -/
  law : ∀ x, localValue x * L.N x = asymptotic

namespace TolmanScaling

/-- The local value is the asymptotic value divided by the lapse. -/
theorem localValue_eq_asymptotic_div_lapse
    (T : TolmanScaling sd) (x : SpaceTime sd) :
    T.localValue x = T.asymptotic / T.L.N x := by
  have hN : T.L.N x ≠ 0 := (T.L.N_pos x).ne'
  exact (eq_div_iff hN).mpr (T.law x)

/-- The Tolman invariant as a `@[simp]` rewrite. -/
@[simp] theorem localValue_mul_lapse
    (T : TolmanScaling sd) (x : SpaceTime sd) :
    T.localValue x * T.L.N x = T.asymptotic :=
  T.law x

/-- The local/asymptotic ratio is the inverse lapse `1/N(x)`. -/
theorem localValue_div_asymptotic_eq_inv_lapse
    (T : TolmanScaling sd) (x : SpaceTime sd) (hA : T.asymptotic ≠ 0) :
    T.localValue x / T.asymptotic = 1 / T.L.N x := by
  rw [T.localValue_eq_asymptotic_div_lapse x]
  field_simp

/-- **Monotonicity under lapse ordering**: for a positive asymptotic value,
a smaller lapse gives a larger local value (deeper gravity well ⇒ larger local
quantity). The single reusable monotonicity fact for all Tolman-scaled
observables. -/
theorem localValue_monotone_of_positive_asymptotic
    (T : TolmanScaling sd) (hA : 0 < T.asymptotic)
    {x₁ x₂ : SpaceTime sd} (hN : T.L.N x₂ ≤ T.L.N x₁) :
    T.localValue x₁ ≤ T.localValue x₂ := by
  rw [T.localValue_eq_asymptotic_div_lapse x₁, T.localValue_eq_asymptotic_div_lapse x₂]
  exact div_le_div_of_nonneg_left hA.le (T.L.N_pos x₂) hN

end TolmanScaling

end Physlib.SpaceTime

end
