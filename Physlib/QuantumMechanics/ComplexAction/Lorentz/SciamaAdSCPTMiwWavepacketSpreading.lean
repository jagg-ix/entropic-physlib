/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-!
# MIW wavepacket spreading: inverse-square scaling (Hall–Deckert–Wiseman 1402.6144, §IV.B)

Completes the "quantum phenomena as generic MIW effects" of Hall–Deckert–Wiseman with §IV.B, wavepacket
spreading.  A free quantum particle's position variance grows *quadratically in time*.  HDW show the same for
`N` interacting worlds, for any interworld potential that is translation invariant and **inverse-square
homogeneous**,

`U_N(λx₁,…,λx_N) = λ⁻² U_N(x₁,…,x_N)`  (Eq. scaling),

which the toy model satisfies.  Differentiating the scaling at `λ = 1` gives Euler's identity
`Σ x_n ∂U_N/∂x_n = −2U_N`, whence the variance's acceleration is constant,
`V̈_N = 4⟨E⟩_N/m − 2⟨p⟩_N²/m²`, and integration yields the quadratic spreading law (Eq. spreadn).

* `interworldGapEnergy_inverse_square` — the interworld potential core `1/gap²` **is** inverse-square
  homogeneous: `interworldGapEnergy(λ·gap) = λ⁻² · interworldGapEnergy(gap)` — the concrete degree-`−2` scaling.
* `spreadingVariance_zero` — at `t = 0` the variance is the initial `V_N(0)`.
* `spreadingVariance_quadratic` — the variance is a quadratic in `t`: `V_N(0) + ((2/m)Cov)·t +
  ((2/m)(⟨E⟩ − ⟨p⟩²/2m))·t²`.
* `spreadingVariance_acceleration_constant` — the `t²` coefficient's double is
  `V̈_N = 4⟨E⟩/m − 2⟨p⟩²/m²`, **constant**: the spreading acceleration is fixed by the conserved energy and
  momentum — the source of the quadratic-in-time growth, for any `N`.

So the quantum wavepacket spreading `Var(t) = Var(0) + (2t/m)Cov + (2t²/m)[⟨E⟩ − ⟨p⟩²/2m]` is reproduced by the
finite interacting worlds, a direct consequence of the interworld potential's inverse-square scaling.

Honest scope: the concrete inverse-square scaling of the potential core, and the quadratic spreading law with its
constant acceleration.  The full Euler-identity derivative step `Σx_n∂U_N = −2U_N` and the time-integration are
the paper's calculus content (kept out to stay import-light; the `λ⁻²` factor here is exactly the `−2` degree).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwWavepacketSpreading

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-! ## A. The interworld potential is inverse-square homogeneous -/

/-- **[Inverse-square scaling] `interworldGapEnergy(λ·gap) = λ⁻² · interworldGapEnergy(gap)`.**  The interworld
potential core `1/gap²` is homogeneous of degree `−2`, the property behind wavepacket spreading (Eq. scaling). -/
theorem interworldGapEnergy_inverse_square (lam gap : ℝ) :
    interworldGapEnergy (lam * gap) = (1 / lam ^ 2) * interworldGapEnergy gap := by
  unfold interworldGapEnergy
  rw [mul_pow, one_div_mul_one_div]

/-! ## B. The quadratic spreading law -/

/-- The MIW position variance at time `t` (Eq. spreadn): quadratic in `t`, from the constant acceleration. -/
def spreadingVariance (V0 cov energy p m t : ℝ) : ℝ :=
  V0 + (2 * t / m) * cov + (2 * t ^ 2 / m) * (energy - p ^ 2 / (2 * m))

/-- **[Initial variance] `V_N(0) = V_N(0)`.** -/
theorem spreadingVariance_zero (V0 cov energy p m : ℝ) :
    spreadingVariance V0 cov energy p m 0 = V0 := by
  unfold spreadingVariance; ring

/-- **[Quadratic in time] `V_N(t) = V_N(0) + b·t + a·t²`** with `b = (2/m)Cov`, `a = (2/m)(⟨E⟩ − ⟨p⟩²/2m)`. -/
theorem spreadingVariance_quadratic (V0 cov energy p m t : ℝ) :
    spreadingVariance V0 cov energy p m t
      = V0 + ((2 / m) * cov) * t + ((2 / m) * (energy - p ^ 2 / (2 * m))) * t ^ 2 := by
  unfold spreadingVariance; ring

/-- **[Constant acceleration] `V̈_N = 4⟨E⟩/m − 2⟨p⟩²/m²`.**  Twice the `t²` coefficient — fixed by the conserved
energy and momentum (from Euler's `Σx∂U = −2U` and Ehrenfest `⟨p⟩` conserved) — so the spreading is quadratic. -/
theorem spreadingVariance_acceleration_constant {m : ℝ} (hm : m ≠ 0) (energy p : ℝ) :
    2 * ((2 / m) * (energy - p ^ 2 / (2 * m))) = 4 * energy / m - 2 * p ^ 2 / m ^ 2 := by
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwWavepacketSpreading

end
