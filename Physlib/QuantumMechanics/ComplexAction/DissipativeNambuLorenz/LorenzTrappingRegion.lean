/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu
public import Mathlib.Tactic.Linarith

/-!
# The Lorenz attracting ellipsoid: the bounded region the orbit occupies (Axenides–Floratos §3.1)

The Lorenz flow (`DissipativeNambuLorenz.LorenzNambu.lorenzField`) is **orbit-localizable**: every trajectory is
eventually trapped inside a bounded ellipsoid set by the parameters `σ, r, b` (Axenides, Floratos,
JHEP 04 (2010) 036, Eqs. 3.5–3.8). With the Lyapunov function

  `S₁ = r x² + σ y² + σ(z − 2r)²`   (Eq. 3.5),

its rate along the flow is (Eq. 3.6)

  `dS₁/dt = ṙ · ∇S₁ = −2σ [r x² + y² + b(z − r)² − b r²]`,

which is **negative outside** the fixed ellipsoid

  `S₂ : r x² + y² + b(z − r)² = b r²`   (Eq. 3.7),

so all orbits crossing `S₂` are ingoing (Eq. 3.8) — the attractor lives in a bounded spatial region.

This file works at the vector-algebra layer (gradients as vectors, as in `DissipativeNambuLorenz.LorenzNambu`):

* **§A — the Lyapunov rate** (Eq. 3.6). `lorenz_S1_lyapunov_rate`: `lorenzField ⬝ᵥ ∇S₁ = −2σ·(trappingForm − b r²)`,
  a pure vector-algebra identity.
* **§B — the bounded trapping region** (Eqs. 3.7–3.8). `trappingForm_nonneg` (the form is positive
  semidefinite for `0 ≤ r, b`, so the ellipsoid is well-defined); `lorenz_S1_decreasing_outside`: for `σ > 0`,
  outside `S₂` (`b r² < trappingForm`) the Lyapunov function strictly decreases — orbits are ingoing.
* **§C — the reversible node sits on the boundary.** `lorenz_origin_on_trapping_boundary`: at the origin
  `P₁` (the unique reversible fixed point, `∇D = 0`, contour weight `1` —
  `DissipativeNambuLorenz.NambuEntropicContour`) the trapping form equals `b r²`, i.e. `P₁ ∈ S₂`: the entropy-free
  node lies exactly on the attracting-ellipsoid boundary.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §3.1, Eqs. 3.5–3.8. `Physlib`
  (`DissipativeNambuLorenz.LorenzNambu`).

No additional assumptions.
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzTrappingRegion

variable (σ r b : ℝ) (p : Fin 3 → ℝ)

/-- **`∇S₁ = (2rx, 2σy, 2σ(z−2r))`** — gradient of the Lyapunov function `S₁ = rx² + σy² + σ(z−2r)²`
(Eq. 3.5). -/
def lorenzGradS1 : Fin 3 → ℝ := ![2 * r * p 0, 2 * σ * p 1, 2 * σ * (p 2 - 2 * r)]

/-- **The trapping quadratic form** `r x² + y² + b(z − r)²` — the left-hand side of the fixed ellipsoid
`S₂` (Eq. 3.7); the orbit is ingoing where this exceeds `b r²`. -/
def trappingForm : ℝ := r * p 0 ^ 2 + p 1 ^ 2 + b * (p 2 - r) ^ 2

/-! ## §A — the Lyapunov rate along the Lorenz flow (Eq. 3.6) -/

/-- **[`dS₁/dt = −2σ(trappingForm − b r²)`]** the rate of the Lyapunov function `S₁` along the Lorenz flow
(Eq. 3.6): `ṙ · ∇S₁ = −2σ[r x² + y² + b(z − r)² − b r²]`. A pure vector-algebra identity on
`lorenzField`. -/
theorem lorenz_S1_lyapunov_rate :
    lorenzField σ r b p ⬝ᵥ lorenzGradS1 σ r p
      = -2 * σ * (trappingForm r b p - b * r ^ 2) := by
  simp only [lorenzField, lorenzGradS1, trappingForm, vec3_dotProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## §B — the bounded trapping region (Eqs. 3.7–3.8) -/

/-- **[The trapping form is positive semidefinite]** for `0 ≤ r, b` the form `r x² + y² + b(z − r)² ≥ 0` —
the level sets `S₂` are genuine ellipsoids, so the trapping region is bounded. -/
theorem trappingForm_nonneg (hr : 0 ≤ r) (hb : 0 ≤ b) : 0 ≤ trappingForm r b p := by
  unfold trappingForm
  have h1 : 0 ≤ r * p 0 ^ 2 := mul_nonneg hr (sq_nonneg _)
  have h2 : 0 ≤ b * (p 2 - r) ^ 2 := mul_nonneg hb (sq_nonneg _)
  nlinarith [sq_nonneg (p 1), h1, h2]

/-- **[Orbits are ingoing outside `S₂`]** for `σ > 0`, wherever the trapping form exceeds `b r²` (i.e. outside
the fixed ellipsoid `S₂`, Eq. 3.7) the Lyapunov function strictly decreases, `dS₁/dt < 0` (Eq. 3.8): every
orbit crossing `S₂` heads inward, so the attractor is confined to a bounded region fixed by `σ, r, b`. -/
theorem lorenz_S1_decreasing_outside (hσ : 0 < σ) (hout : b * r ^ 2 < trappingForm r b p) :
    lorenzField σ r b p ⬝ᵥ lorenzGradS1 σ r p < 0 := by
  rw [lorenz_S1_lyapunov_rate]
  nlinarith [mul_pos hσ (show (0:ℝ) < trappingForm r b p - b * r ^ 2 by linarith)]

/-! ## §C — the reversible node lies on the trapping boundary -/

/-- **[`P₁ ∈ S₂`]** at the origin `P₁ = (0,0,0)` — the unique reversible fixed point (`∇D = 0`, contour weight
`1`, `DissipativeNambuLorenz.NambuEntropicContour`) — the trapping form equals `b r²`, so the entropy-free node sits
exactly on the attracting-ellipsoid boundary `S₂` (Eq. 3.7). -/
theorem lorenz_origin_on_trapping_boundary : trappingForm r b 0 = b * r ^ 2 := by
  simp [trappingForm]

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzTrappingRegion

end
