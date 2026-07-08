/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.Lorentzian

/-!
# Lorentz-invariant proper-time kernel

The proper-time / Schwinger representation of a propagator uses a
**Lorentz-invariant** denominator `p² + m²` (Euclidean) or `p² − m²`
(Lorentzian), where `p² = ⟪p, p⟫ₘ` is the Minkowski inner product (a Lorentz
scalar).  This module provides the kernel content as a scalar API: a model that
produces the Lorentz-invariant scalar `pSq : ℝ` plugs straight into

* `lorentzInvariantDenominator pSq m  =  pSq + m²` — Euclidean propagator
  denominator;
* `lorentzInvariantProperTimeKernel pSq m σ  =  exp(−(pSq + m²)·σ)` — the
  Schwinger-parameter kernel `exp(−(p² + m²) σ)` of the propagator;
* `lorentzInvariantProperTimePhase pSq m σ  =
   exp(i·σ·(pSq − m²))` — the Lorentzian (real-time) kernel factor with
  `S_R = σ·(p² − m²)` and `S_I = 0` (no dissipation).

Both kernels compose with the just-shipped `Physlib/QFT/PathIntegral/`
infrastructure: the Euclidean kernel is a `path_integral_damping` instance
(Lorentz-invariant `S_I`) and the Lorentzian phase is a `lorentzianKernel`
with imaginary action `S_I = 0`.

## Lemmas

* `lorentzInvariantProperTimeKernel_pos` — positivity.
* `lorentzInvariantProperTimeKernel_eq_path_integral_damping` — bridge to
  `path_integral_damping ℏ (pSq + m²) σ` (at `ℏ = 1`).
* `lorentzInvariantProperTimePhase_norm_one` — phase is unitary
  (`S_I = 0` ⇒ no damping).
* `lorentzInvariantProperTimePhase_eq_lorentzianKernel` — identification
  with the existing scalar `lorentzianKernel`.


## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Real Complex

/-! ## §1 — Euclidean Lorentz-invariant kernel -/

/-- **Lorentz-invariant denominator** `p² + m²`, where `pSq = ⟪p, p⟫ₘ` is
the Minkowski inner product (a Lorentz scalar). -/
def lorentzInvariantDenominator (pSq m : ℝ) : ℝ := pSq + m ^ 2

/-- **Schwinger / Lorentz-invariant proper-time kernel**
`K(σ) = exp(−(p² + m²)·σ)`.  Phase-1 scalar form: the consumer supplies
the Lorentz scalar `pSq = ⟪p, p⟫ₘ`. -/
def lorentzInvariantProperTimeKernel (pSq m σ : ℝ) : ℝ :=
  Real.exp (-(lorentzInvariantDenominator pSq m) * σ)

/-- The Schwinger kernel is strictly positive. -/
theorem lorentzInvariantProperTimeKernel_pos (pSq m σ : ℝ) :
    0 < lorentzInvariantProperTimeKernel pSq m σ :=
  Real.exp_pos _

/-- The Schwinger kernel coincides with `path_integral_damping 1
((p² + m²)·σ)`. -/
theorem lorentzInvariantProperTimeKernel_eq_path_integral_damping
    (pSq m σ : ℝ) :
    lorentzInvariantProperTimeKernel pSq m σ =
      path_integral_damping 1 ((lorentzInvariantDenominator pSq m) * σ) := by
  unfold lorentzInvariantProperTimeKernel path_integral_damping
  congr 1; ring

/-! ## §2 — Lorentzian (real-time) Lorentz-invariant phase -/

/-- **Lorentzian Lorentz-invariant phase**
`exp(i·σ·(p² − m²))` — the real-time Schwinger phase with real action
`S_R = σ·(p² − m²)` and zero imaginary action. -/
def lorentzInvariantProperTimePhase (pSq m σ : ℝ) : ℂ :=
  Complex.exp ((σ * (pSq - m ^ 2) : ℂ) * Complex.I)

/-- **Phase is unitary**: `S_I = 0` ⇒ no entropic damping. -/
theorem lorentzInvariantProperTimePhase_norm_one (pSq m σ : ℝ) :
    ‖lorentzInvariantProperTimePhase pSq m σ‖ = 1 := by
  unfold lorentzInvariantProperTimePhase
  have : (σ * (pSq - m ^ 2) : ℂ) = ((σ * (pSq - m ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Lorentzian phase is exactly `lorentzianKernel (σ·(p² − m²)) 0 1` —
the existing Lorentzian kernel at `S_I = 0, ℏ = 1`. -/
theorem lorentzInvariantProperTimePhase_eq_lorentzianKernel
    (pSq m σ : ℝ) :
    lorentzInvariantProperTimePhase pSq m σ =
      lorentzianKernel (σ * (pSq - m ^ 2)) 0 1 := by
  unfold lorentzInvariantProperTimePhase lorentzianKernel
  congr 1
  push_cast
  ring

/-- The Lorentzian phase is never zero. -/
theorem lorentzInvariantProperTimePhase_ne_zero (pSq m σ : ℝ) :
    lorentzInvariantProperTimePhase pSq m σ ≠ 0 :=
  Complex.exp_ne_zero _

end Physlib.QFT.PathIntegral

end
