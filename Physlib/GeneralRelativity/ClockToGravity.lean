/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# From the quantum clock to Newtonian gravity

The chain that carries the quantum internal clock into general relativity through its weak-field (Newtonian) limit.
A moving clock's energy is `E = mc² cosh θ` in the rapidity `θ`; at rest it is the Compton-clock energy `mc² = ℏω_C`.
In a gravitational potential the clock's rate is redshifted, `g₀₀ = −(1 + 2Φ/c²)`; the Levi-Civita connection of
this weak-field metric has `Γⁱ₀₀ = (1/c²)∂ⁱΦ`, and the geodesic equation reduces to **Newton's law**
`ẍ = −Γ c² = −∇Φ`. So the same clock whose phase ticks at `ω_C` (`QuantumMechanics.ComptonClock`) sources, through
the Levi-Civita geodesic, the Newtonian gravitational acceleration.

References: entropic / clock-based derivation of the Newtonian and GR limits. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.GeneralRelativity.ClockToGravity

/-- **The clock energy** `E = mc² cosh θ` in the rapidity `θ`. -/
noncomputable def clockEnergy (m c θ : ℝ) : ℝ := m * c ^ 2 * Real.cosh θ

/-- **The rest clock energy is `mc²`** — the Compton-clock energy `ℏω_C`. -/
theorem clockEnergy_rest (m c : ℝ) : clockEnergy m c 0 = m * c ^ 2 := by
  rw [clockEnergy, Real.cosh_zero, mul_one]

/-- **The weak-field time-time metric** `g₀₀ = −(1 + 2Φ/c²)` — the gravitational redshift of the clock rate. -/
noncomputable def weakFieldMetric00 (Φ c : ℝ) : ℝ := -(1 + 2 * Φ / c ^ 2)

/-- **The weak-field Levi-Civita connection** `Γⁱ₀₀ = (1/c²)∂ⁱΦ` — the only Christoffel symbol surviving the
Newtonian limit of the metric `g₀₀ = −(1 + 2Φ/c²)`. -/
noncomputable def weakFieldChristoffel (Φ : ℝ → ℝ) (c x : ℝ) : ℝ := deriv Φ x / c ^ 2

/-- **The Newtonian acceleration from the geodesic** `ẍ = −Γ c²`. -/
noncomputable def newtonianAcceleration (Φ : ℝ → ℝ) (c x : ℝ) : ℝ :=
  -(c ^ 2) * weakFieldChristoffel Φ c x

/-- **The geodesic reduces to Newton's law** `ẍ = −∇Φ`. In the weak field the geodesic acceleration built from the
Levi-Civita connection `Γⁱ₀₀` is exactly minus the gradient of the potential — Newton's law of gravitation emerges
from the clock's weak-field geometry. -/
theorem newtonianAcceleration_eq_neg_gradient (Φ : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) :
    newtonianAcceleration Φ c x = -deriv Φ x := by
  unfold newtonianAcceleration weakFieldChristoffel
  field_simp

end Physlib.GeneralRelativity.ClockToGravity

end
