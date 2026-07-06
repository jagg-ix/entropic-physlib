/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The quantum Boltzmann H-theorem: monotonic relaxation to equilibrium

The second-law arrow for a quantum Boltzmann (GKLS) relaxation. A dissipative rate `Γ ≥ 0` drives the system to
equilibrium along the **relaxed fraction**

`f(Γ,t) = 1 − e^{−Γt}`,

which starts at `0`, is bounded by `1`, and is **monotonically increasing** in time — the H-theorem: the system
approaches equilibrium irreversibly and never returns. This is the coarse macroscopic content of the GKLS
entropy-production law `Σⱼ Tr(Lⱼ†Lⱼ ρ) ≥ 0`.

References: L. Boltzmann (H-theorem); G. Lindblad 1976 (GKLS). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics.QuantumBoltzmannHTheorem

/-- **The relaxed fraction** `f(Γ,t) = 1 − e^{−Γt}` — the fraction of the system that has relaxed to equilibrium by
time `t` at dissipative rate `Γ`. -/
noncomputable def relaxedFraction (Γ t : ℝ) : ℝ := 1 - Real.exp (-(Γ * t))

/-- **No relaxation at the start** `f(Γ,0) = 0`. -/
theorem relaxedFraction_at_zero (Γ : ℝ) : relaxedFraction Γ 0 = 0 := by
  simp [relaxedFraction]

/-- **The relaxed fraction is bounded above by `1`** `f ≤ 1`. -/
theorem relaxedFraction_le_one (Γ t : ℝ) : relaxedFraction Γ t ≤ 1 := by
  unfold relaxedFraction
  have := (Real.exp_pos (-(Γ * t))).le
  linarith

/-- **The relaxed fraction is non-negative** `f ≥ 0` for `Γ, t ≥ 0`. -/
theorem relaxedFraction_nonneg (Γ t : ℝ) (hΓ : 0 ≤ Γ) (ht : 0 ≤ t) : 0 ≤ relaxedFraction Γ t := by
  unfold relaxedFraction
  have h1 : Real.exp (-(Γ * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hΓ ht])
  rw [Real.exp_zero] at h1
  linarith

/-- **The H-theorem: relaxation is monotonic** `t₁ ≤ t₂ ⟹ f(Γ,t₁) ≤ f(Γ,t₂)`. For a non-negative dissipative rate
the relaxed fraction never decreases: the system approaches equilibrium irreversibly (the second-law arrow of the
quantum Boltzmann flow). -/
theorem relaxedFraction_monotone (Γ : ℝ) (hΓ : 0 ≤ Γ) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    relaxedFraction Γ t₁ ≤ relaxedFraction Γ t₂ := by
  unfold relaxedFraction
  have h1 : Real.exp (-(Γ * t₂)) ≤ Real.exp (-(Γ * t₁)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h hΓ])
  linarith

end Physlib.Thermodynamics.QuantumBoltzmannHTheorem

end
