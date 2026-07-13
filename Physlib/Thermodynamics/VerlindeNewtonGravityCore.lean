/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Holographic screen area and bit count — the light core

`sphereArea = 4πR²` and the Verlinde holographic bit count `holographicBits = A·c³/(Gℏ)`, depending
only on `Real.pi`.

## References

* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029 — the
  number of bits on a holographic screen, `N = A·c³/(Gℏ)`. -/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics

/-- **Sphere area**: `A = 4π · R²` — the area of a spherical holographic screen of radius `R`. -/
noncomputable def sphereArea (R : ℝ) : ℝ := 4 * Real.pi * R ^ 2

/-- **Holographic bit count** on a screen of area `A`: `N := A · c³ / (G · ℏ)` (Verlinde, JHEP 04
(2011) 029) — the number of bits on a holographic screen of area `A`, with `G` to be identified with
Newton's constant. -/
noncomputable def holographicBits (A G ℏ c : ℝ) : ℝ := A * c ^ 3 / (G * ℏ)

end Physlib.Thermodynamics

end
