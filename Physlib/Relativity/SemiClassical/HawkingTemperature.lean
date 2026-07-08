/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hawking temperature

For a horizon with surface gravity `κ`, semi-classical gravity assigns the
temperature

  `hawkingTemperature ℏ κ c kB  =  ℏ · κ / (2π · c · kB)`

(Hawking, 1975, *Comm. Math. Phys.* 43, 199-220).  Here `ℏ` is the reduced
Planck constant, `c` the speed of light, and `kB` the Boltzmann constant;
all four arguments are taken as positive real parameters so the formula is
agnostic to the unit system.

This module provides the bare formula plus the positivity theorem.  The
identification with a specific horizon (Schwarzschild, de Sitter, Rindler,
Kerr, …) belongs to the consumers.

-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Relativity.SemiClassical

/-- **Hawking temperature.** For a horizon with surface gravity `κ`, the
temperature is `ℏ · κ / (2π · c · kB)`. -/
noncomputable def hawkingTemperature (ℏ κ c kB : ℝ) : ℝ :=
  ℏ * κ / (2 * Real.pi * c * kB)

@[simp] theorem hawkingTemperature_def (ℏ κ c kB : ℝ) :
    hawkingTemperature ℏ κ c kB = ℏ * κ / (2 * Real.pi * c * kB) := rfl

/-- **Positivity of the Hawking temperature.** When `ℏ, κ, c, kB > 0`, the
Hawking temperature is strictly positive. -/
theorem hawkingTemperature_pos
    (ℏ κ c kB : ℝ) (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c) (hkB : 0 < kB) :
    0 < hawkingTemperature ℏ κ c kB := by
  have h2π : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h2πc : 0 < 2 * Real.pi * c := mul_pos h2π hc
  have hden : 0 < 2 * Real.pi * c * kB := mul_pos h2πc hkB
  have hnum : 0 < ℏ * κ := mul_pos hℏ hκ
  simpa [hawkingTemperature] using div_pos hnum hden

/-- **Non-negativity of the Hawking temperature.** When all four arguments
are non-negative, the Hawking temperature is non-negative. -/
theorem hawkingTemperature_nonneg
    (ℏ κ c kB : ℝ) (hℏ : 0 ≤ ℏ) (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hkB : 0 ≤ kB) :
    0 ≤ hawkingTemperature ℏ κ c kB := by
  have h2π : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h2πc : 0 ≤ 2 * Real.pi * c := mul_nonneg (le_of_lt h2π) hc
  have hden : 0 ≤ 2 * Real.pi * c * kB := mul_nonneg h2πc hkB
  have hnum : 0 ≤ ℏ * κ := mul_nonneg hℏ hκ
  simpa [hawkingTemperature] using div_nonneg hnum hden

end Physlib.Relativity.SemiClassical
