/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Vacuum

/-!
# Characterization of the Gaussian vacuum center

For a positive quadratic kernel and positive `hbar`, the complex-action vacuum
weight has unit modulus exactly at the source-induced classical field.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

/-- Unit modulus occurs exactly at the unique source-induced classical field. -/
lemma norm_vacuumComplexWeight_eq_one_iff
    (k j A hbar : ℝ) (hk : 0 < k) (hhbar : 0 < hbar) :
    ‖vacuumComplexWeight k j A hbar‖ = 1 ↔
      A = classicalSourceField k j := by
  rw [norm_vacuumComplexWeight]
  constructor
  · intro h
    have hexp :
        Real.exp (-(vacuumEntropicTime k j A hbar)) = Real.exp 0 := by
      simpa using h
    have harg : -(vacuumEntropicTime k j A hbar) = 0 :=
      Real.exp_injective hexp
    have ht : vacuumEntropicTime k j A hbar = 0 := by
      linarith
    have hrel : vacuumRelativeAction k j A = 0 := by
      unfold vacuumEntropicTime at ht
      exact (div_eq_zero_iff).mp ht |>.resolve_right hhbar.ne'
    exact (vacuumRelativeAction_eq_zero_iff k j A hk).mp hrel
  · rintro rfl
    rw [← norm_vacuumComplexWeight]
    exact norm_vacuumComplexWeight_at_center k j hbar hk.ne'

end Physlib.QFT.ScalarGreenFunctions

end
