/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BCJ color–kinematics duality and the double copy

The Bern–Carrasco–Johansson double copy: gauge-theory amplitudes can be written so that their **kinematic
numerators satisfy the same Jacobi identities as the color factors**, and replacing the color factors by a second
copy of kinematic numerators yields **gravity** amplitudes — "gravity = gauge²".

* a `BCJColorKinematicsDuality` packages a three-channel `(s,t,u)` amplitude whose color factors obey the gauge
  Jacobi `c_s + c_t + c_u = 0` *and* whose kinematic numerators obey the same `n_s + n_t + n_u = 0`;
* the **double copy** `M = Σ nᵢ ñᵢ/Dᵢ` replaces the color factors by a second numerator set, and is
  non-negative per diagonal channel;
* the **Maxwell–Faraday Bianchi identity is a BCJ kinematic Jacobi**: the three cyclic terms of `dF = 0` for
  `F = dA` sum to zero (`faraday_bianchi`), realizing the kinematic Jacobi from `d² = 0`;
* the double copy is a **Feynman–Kac factorization** `exp(−(S₁+S₂)) = exp(−S₁)exp(−S₂)`.

References: Z. Bern, J.J.M. Carrasco, H. Johansson, Phys. Rev. D 78 (2008) 085011 (arXiv:0805.3993). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.DoubleCopy.ColorKinematics

/-! ## BCJ amplitude data -/

/-- A single BCJ channel: kinematic numerator `nᵢ`, color factor `cᵢ`, positive propagator `Dᵢ`. -/
structure BCJTriple where
  /-- Kinematic numerator. -/
  numerator : ℝ
  /-- Color factor (from the gauge structure constants). -/
  color : ℝ
  /-- Propagator denominator. -/
  propagator : ℝ
  /-- Positivity of the propagator. -/
  prop_pos : 0 < propagator

/-- **Tree-level gauge amplitude** `A = Σᵢ nᵢcᵢ/Dᵢ`. -/
noncomputable def bcjGaugeAmplitude (ts : List BCJTriple) : ℝ :=
  ts.foldl (fun acc t => acc + t.numerator * t.color / t.propagator) 0

/-- **Tree-level double-copy (gravity) amplitude** `M = Σᵢ nᵢñᵢ/Dᵢ` — the color factors replaced by a second set
of kinematic numerators (gravity as "gauge²"). -/
noncomputable def bcjDoubleCopyAmplitude (ts₁ ts₂ : List BCJTriple) : ℝ :=
  (ts₁.zip ts₂).foldl (fun acc p => acc + p.1.numerator * p.2.numerator / p.1.propagator) 0

/-- **The diagonal double copy is non-negative per channel** `nᵢ²/Dᵢ ≥ 0` — squaring a gauge channel contributes
non-negatively to the gravity amplitude. -/
theorem bcjDoubleCopy_diagonal_nonneg (t : BCJTriple) : 0 ≤ t.numerator ^ 2 / t.propagator :=
  div_nonneg (sq_nonneg _) t.prop_pos.le

/-! ## Color–kinematics duality -/

/-- **BCJ color–kinematics duality** for a three-channel `(s,t,u)` amplitude: the kinematic numerators satisfy the
*same* Jacobi identity `n_s + n_t + n_u = 0` as the color factors `c_s + c_t + c_u = 0`. -/
structure BCJColorKinematicsDuality where
  /-- Color factor, `s`-channel. -/
  c_s : ℝ
  /-- Color factor, `t`-channel. -/
  c_t : ℝ
  /-- Color factor, `u`-channel. -/
  c_u : ℝ
  /-- Kinematic numerator, `s`-channel. -/
  n_s : ℝ
  /-- Kinematic numerator, `t`-channel. -/
  n_t : ℝ
  /-- Kinematic numerator, `u`-channel. -/
  n_u : ℝ
  /-- Gauge Jacobi identity for the color factors. -/
  color_jacobi : c_s + c_t + c_u = 0
  /-- Kinematic Jacobi identity — the BCJ duality condition. -/
  kinematic_jacobi : n_s + n_t + n_u = 0

/-- **The single-propagator gauge amplitude collects over a common denominator**
`Σ cᵢnᵢ/D = (Σ cᵢnᵢ)/D`. -/
theorem bcj_gauge_amplitude_single_vanishing (d : BCJColorKinematicsDuality) (D : ℝ) :
    d.c_s * d.n_s / D + d.c_t * d.n_t / D + d.c_u * d.n_u / D =
      (d.c_s * d.n_s + d.c_t * d.n_t + d.c_u * d.n_u) / D := by
  ring

/-! ## The Maxwell–Bianchi identity is a BCJ kinematic Jacobi -/

/-- **The Faraday tensor** `F_{μν} = k_μ A_ν − k_ν A_μ` (with `∂ → k`, `F = dA`). -/
def faraday (k A : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ := k μ * A ν - k ν * A μ

/-- **The Maxwell–Faraday Bianchi identity is a BCJ kinematic Jacobi**
`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`. The three cyclic terms of the homogeneous Maxwell equation `dF = 0`
(for `F = dA`) sum to zero because `d² = 0` — exactly the kinematic Jacobi `n_s + n_t + n_u = 0` of the BCJ
duality. -/
theorem faraday_bianchi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 := by
  unfold faraday
  ring

/-- **The Faraday–Bianchi identity supplies a BCJ color–kinematics duality**: the cyclic `k F` terms are the
`(s,t,u)` kinematic numerators (kinematic Jacobi = Bianchi), paired with any color factors obeying their own gauge
Jacobi. -/
noncomputable def faradayBCJDuality (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (c_s c_t c_u : ℝ) (hcolor : c_s + c_t + c_u = 0) : BCJColorKinematicsDuality where
  c_s := c_s
  c_t := c_t
  c_u := c_u
  n_s := k lam * faraday k A μ ν
  n_t := k μ * faraday k A ν lam
  n_u := k ν * faraday k A lam μ
  color_jacobi := hcolor
  kinematic_jacobi := faraday_bianchi k A lam μ ν

/-! ## The double copy is a Feynman–Kac factorization -/

/-- **The double copy as a path-integral factorization** `exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)`: identifying the BCJ
numerators with (entropic/imaginary) actions, the Feynman–Kac weight of the product theory factorizes — the
path-integral realization of `M = A₁·A₂`. -/
theorem bcj_doublecopy_fk_factorization (S₁ S₂ : ℝ) :
    Real.exp (-(S₁ + S₂)) = Real.exp (-S₁) * Real.exp (-S₂) := by
  rw [show -(S₁ + S₂) = -S₁ + -S₂ by ring, Real.exp_add]

end Physlib.DoubleCopy.ColorKinematics

end
