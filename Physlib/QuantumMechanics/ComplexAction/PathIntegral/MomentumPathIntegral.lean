/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The complex-action momentum relation `p = m·q̇` via the Feynman path integral (Nagao–Nielsen §3)

Nagao–Nielsen derive the momentum relation `p = ∂L/∂q̇ = m·q̇` for the complex action
theory by a Feynman path-integral / saddle-point argument (*Momentum relation and
classical limit in the future-not-included complex action theory*, Prog. Theor. Phys.,
arXiv:1304.4017, §3). With `L = ½ m q̇² − V(q)` and the phase-space Lagrangian
`L(p,q,q̇) = p q̇ − H(p,q)`, `H = p²/2m + V`, the momentum integral in the discretized FPI

  `∫ dp/2πℏ · exp[(i/ℏ)Δt(p q̇ − H)]`   (Eq. 3.14, 3.17)

is a Gaussian whose **saddle point is `p = m q̇`** (Eq. 3.10). This file formalizes that
derivation as it reduces to algebra + one complex Gaussian integral.

* `phaseLagrangian_complete_square` — **Eq. 3.15**: `p q̇ − (p²/2m + V) =
  −(1/2m)(p − m q̇)² + (½ m q̇² − V)`. Completing the square in `p` exhibits the unique
  saddle `p = m q̇` and the configuration Lagrangian as its value.
* `saddle_iff` / `phaseLagrangian_at_saddle` — the Gaussian's stationary point is exactly
  `p = m q̇`, where `L_phase` equals the configuration Lagrangian.
* `momentum_relation` — **Eq. 3.10**: `∂/∂q̇ (½ m q̇² − V) = m q̇`, i.e. `p = m q̇`.
* `momentum_integral_converges_iff` — the momentum Gaussian converges iff the imaginary
  mass is positive, `m_I = Im m > 0` (Eq. 3.1's `m_I ≥ 0` condition). This is the
  **Feynman–Kac / Euclidean damping** condition: `Im m > 0` is exactly `Re b > 0` for the
  Gaussian coefficient `b`, so the imaginary part of the action contributes a real damping
  `e^{−S_I/ℏ}` (the modulus of `e^{iS/ℏ}`, cf. `NonHermitianComplexAction.EntropicDampingEquivalence`).
* `momentum_gaussian_integral` — **Eq. 3.17**: the saddle-point integral
  `∫ e^{−b(u)²} du = (π/b)^{1/2}`, evaluated by Mathlib's `integral_gaussian_complex` —
  the *same* complex-Gaussian tool that powers the contour/delta machinery
  (`ComplexDelta.Contour`), tying the momentum derivation to that proof.

## §5 — Future-not-included theory: effective mass and real action (Eqs. 3.4–3.5, 5.10–5.14)

In the *future-not-included* theory (`⟨Ô⟩^{AA}`) the momentum relation `p = m q̇` (complex
`m`) is replaced by `p = m_eff q̇` with a **real** effective mass, because `⟨q̂⟩` and `⟨p̂⟩`
are real while `m q̇` would be complex (the contradiction Nagao–Nielsen resolve in §5). The
anti-Hermitian part of `Ĥ` is suppressed in the classical limit (their Eqs. 5.6–5.7), so the
classical theory is governed by a real action `S_eff = ∫ L_eff dt`.

* `configLagrangian_eq_real_add_imag` — **Eqs. 3.1–3.5**: the complex Lagrangian splits as
  `L = L_R + i L_I` with `L_R = ½ m_R q̇² − V_R`, `L_I = ½ m_I q̇² − V_I` (real `q̇`).
* `effectiveMass`, `effectiveMass_ge`, `effectiveMass_eq_self_iff` — **Eq. 5.10**:
  `m_eff = m_R + m_I²/m_R`; it is real, satisfies `m_R ≤ m_eff` (`m_R > 0`), and
  **`m_eff = m_R ⟺ m_I = 0`** — the reversible / no-imaginary-mass point.
* `effectiveLagrangian`, `effective_momentum_relation` — **Eqs. 5.11, 5.14**:
  `L_eff = ½ m_eff q̇² − V_R` and `p = ∂L_eff/∂q̇ = m_eff q̇`.
* `effectiveLagrangian_eq_lagRealPart_of_reversible` — at the reversible point `m_I = 0` the
  effective real action collapses to `L_R`: the future-not-included and ordinary theories
  coincide exactly when the imaginary mass (hence the imaginary action) vanishes — the
  `S_I = 0` / no-information point linked in `PathIntegral.QFTPathIntegralComplexAction`.

Reference: K. Nagao, H. B. Nielsen, *Momentum relation and classical limit in the
future-not-included complex action theory*, Prog. Theor. Phys., arXiv:1304.4017v3, §3, §5,
Eqs. (3.1), (3.4), (3.5), (3.10), (3.15), (3.17), (5.10), (5.11), (5.14).
-/

set_option autoImplicit false

open Real Complex MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-- **The phase-space Lagrangian** `L(p,q,q̇) = p q̇ − H(p,q)` with `H = p²/2m + V`
(Nagao–Nielsen Eq. 3.15, first line). All quantities complex (`m = m_R + i m_I`). -/
noncomputable def phaseLagrangian (m p qdot V : ℂ) : ℂ := p * qdot - (p ^ 2 / (2 * m) + V)

/-- **The configuration-space Lagrangian** `L = ½ m q̇² − V` (Nagao–Nielsen Eq. 3.1). -/
noncomputable def configLagrangian (m qdot V : ℂ) : ℂ := (1 / 2) * m * qdot ^ 2 - V

/-- **Completing the square — Eq. 3.15**: `p q̇ − (p²/2m + V) = −(1/2m)(p − m q̇)² +
(½ m q̇² − V)`. The Legendre transform exhibits the unique Gaussian saddle at `p = m q̇`
and the configuration Lagrangian as the saddle value. -/
theorem phaseLagrangian_complete_square (m p qdot V : ℂ) (hm : m ≠ 0) :
    phaseLagrangian m p qdot V
      = -(1 / (2 * m)) * (p - m * qdot) ^ 2 + configLagrangian m qdot V := by
  unfold phaseLagrangian configLagrangian
  field_simp
  ring

/-- At the saddle `p = m q̇`, the phase-space Lagrangian equals the configuration
Lagrangian (the quadratic term vanishes). -/
theorem phaseLagrangian_at_saddle (m qdot V : ℂ) (hm : m ≠ 0) :
    phaseLagrangian m (m * qdot) qdot V = configLagrangian m qdot V := by
  rw [phaseLagrangian_complete_square m (m * qdot) qdot V hm]; simp

/-- **The saddle is exactly `p = m q̇`**: the stationarity `q̇ − p/m = 0` of the phase-space
Lagrangian in `p` is equivalent to the momentum relation `p = m q̇`. -/
theorem saddle_iff (m p qdot : ℂ) (hm : m ≠ 0) : qdot - p / m = 0 ↔ p = m * qdot := by
  rw [sub_eq_zero, eq_comm, div_eq_iff hm, mul_comm qdot m]

/-- **The momentum relation — Eq. 3.10**: `p = ∂L/∂q̇ = m q̇`. The derivative of the
configuration Lagrangian `½ m q̇² − V` with respect to `q̇` is `m q̇`. -/
theorem momentum_relation (m qdot V : ℂ) :
    HasDerivAt (fun q' : ℂ => configLagrangian m q' V) (m * qdot) qdot := by
  unfold configLagrangian
  have h := (((hasDerivAt_pow 2 qdot).const_mul ((1 : ℂ) / 2 * m)).sub_const V)
  exact h.congr_deriv (by push_cast; ring)

/-! ## The momentum Gaussian integral and its convergence (Feynman–Kac damping) -/

/-- The coefficient `b = i Δt / (2ℏ m)` of the momentum Gaussian
`exp[−b (p − m q̇)²]` from `(i/ℏ)Δt·(−1/2m)` in Eq. 3.17. -/
noncomputable def momentumGaussianCoeff (m : ℂ) (ℏ dt : ℝ) : ℂ :=
  (↑(dt / (2 * ℏ)) : ℂ) * (Complex.I / m)

theorem momentumGaussianCoeff_re (m : ℂ) (ℏ dt : ℝ) :
    (momentumGaussianCoeff m ℏ dt).re = dt / (2 * ℏ) * (m.im / Complex.normSq m) := by
  rw [momentumGaussianCoeff, Complex.re_ofReal_mul, Complex.div_re]
  simp

/-- **The momentum integral converges iff `Im m > 0`** (Nagao–Nielsen Eq. 3.1's `m_I ≥ 0`).
For `ℏ, Δt > 0`, the Gaussian coefficient has positive real part — the condition
`integral_gaussian_complex` needs — exactly when the imaginary mass is positive. This is
the Feynman–Kac/Euclidean damping condition: `Im m > 0` makes the imaginary action
contribute a *real, decaying* weight rather than a divergent one. -/
theorem momentum_integral_converges_iff (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) : 0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im := by
  rw [momentumGaussianCoeff_re]
  have hc : 0 < dt / (2 * ℏ) := by positivity
  have hn : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm
  rw [mul_pos_iff_of_pos_left hc, div_pos_iff_of_pos_right hn]

/-- **The saddle-point momentum integral — Eq. 3.17**: `∫ e^{−b u²} du = (π/b)^{1/2}`,
evaluated by Mathlib's `integral_gaussian_complex` (the same complex-Gaussian tool that
powers `ComplexDelta.Contour`), valid under the Feynman–Kac convergence `Im m > 0`. With the
saddle substitution `u = p − m q̇` this is the momentum integral of the discretized FPI. -/
theorem momentum_gaussian_integral (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm_I : 0 < m.im) :
    ∫ u : ℝ, Complex.exp (-(momentumGaussianCoeff m ℏ dt) * (u : ℂ) ^ 2)
      = (↑π / momentumGaussianCoeff m ℏ dt) ^ (1 / 2 : ℂ) := by
  have hm : m ≠ 0 := fun h => by rw [h] at hm_I; simp at hm_I
  exact integral_gaussian_complex ((momentum_integral_converges_iff m hℏ hdt hm).mpr hm_I)

/-! ## §5 — Effective mass and real action of the future-not-included theory -/

/-- **Real part of the Lagrangian** `L_R = ½ m_R q̇² − V_R` (Nagao–Nielsen Eq. 3.4). -/
noncomputable def lagRealPart (m_R V_R qdot : ℝ) : ℝ := (1 / 2) * m_R * qdot ^ 2 - V_R

/-- **Imaginary part of the Lagrangian** `L_I = ½ m_I q̇² − V_I` (Nagao–Nielsen Eq. 3.5). -/
noncomputable def lagImagPart (m_I V_I qdot : ℝ) : ℝ := (1 / 2) * m_I * qdot ^ 2 - V_I

/-- **The complex Lagrangian decomposes as `L = L_R + i L_I`** (Eqs. 3.1–3.5): with
`m = m_R + i m_I`, `V = V_R + i V_I` and real `q̇`, the configuration Lagrangian
`½ m q̇² − V` splits into the real and imaginary Lagrangians. -/
theorem configLagrangian_eq_real_add_imag (m_R m_I V_R V_I qdot : ℝ) :
    configLagrangian ((m_R : ℂ) + (m_I : ℂ) * Complex.I) (qdot : ℂ)
        ((V_R : ℂ) + (V_I : ℂ) * Complex.I)
      = ((lagRealPart m_R V_R qdot : ℝ) : ℂ)
        + ((lagImagPart m_I V_I qdot : ℝ) : ℂ) * Complex.I := by
  unfold configLagrangian lagRealPart lagImagPart
  push_cast
  ring

/-- **The effective (real) mass** `m_eff = m_R + m_I²/m_R` (Nagao–Nielsen Eq. 5.10) — the
real mass of the future-not-included momentum relation `p = m_eff q̇`. -/
noncomputable def effectiveMass (m_R m_I : ℝ) : ℝ := m_R + m_I ^ 2 / m_R

/-- **The effective mass increases the inertia**: `m_R ≤ m_eff` for `m_R > 0` — the imaginary
mass only *adds* to the effective real mass. -/
theorem effectiveMass_ge (m_R m_I : ℝ) (hm_R : 0 < m_R) : m_R ≤ effectiveMass m_R m_I := by
  unfold effectiveMass
  have : 0 ≤ m_I ^ 2 / m_R := by positivity
  linarith

/-- **Reversibility ⟺ no effective-mass correction**: `m_eff = m_R ⟺ m_I = 0`. The effective
mass collapses to the bare real mass exactly when the imaginary mass vanishes — the
reversible / no-dissipation (`S_I = 0`) point where the future-not-included and ordinary
theories agree. -/
theorem effectiveMass_eq_self_iff (m_R m_I : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = m_R ↔ m_I = 0 := by
  unfold effectiveMass
  constructor
  · intro h
    have h2 : m_I ^ 2 / m_R = 0 := by linarith
    rcases div_eq_zero_iff.mp h2 with h' | h'
    · exact (pow_eq_zero_iff (by norm_num)).mp h'
    · exact absurd h' hm_R
  · intro h; rw [h]; simp

/-- **The effective real Lagrangian** `L_eff = ½ m_eff q̇² − V_R` (Nagao–Nielsen Eq. 5.14):
the future-not-included classical theory is governed by a *real* action `S_eff = ∫ L_eff dt`
(Eq. 5.13) with effective mass `m_eff` and the real potential `V_R`. -/
noncomputable def effectiveLagrangian (m_R m_I V_R qdot : ℝ) : ℝ :=
  (1 / 2) * effectiveMass m_R m_I * qdot ^ 2 - V_R

/-- **The future-not-included momentum relation — Eq. 5.11**: `p = ∂L_eff/∂q̇ = m_eff q̇`,
with the *real* effective mass `m_eff` (contrast Eq. 3.10's `p = m q̇` with complex `m`). -/
theorem effective_momentum_relation (m_R m_I V_R qdot : ℝ) :
    HasDerivAt (fun q' : ℝ => effectiveLagrangian m_R m_I V_R q')
      (effectiveMass m_R m_I * qdot) qdot := by
  unfold effectiveLagrangian
  have h := (((hasDerivAt_pow 2 qdot).const_mul ((1 : ℝ) / 2 * effectiveMass m_R m_I)).sub_const V_R)
  exact h.congr_deriv (by push_cast; ring)

/-- **Reversible collapse `L_eff = L_R`**: at the no-information point `m_I = 0` (hence
`m_eff = m_R`) the effective real action equals the real-part Lagrangian — the
future-not-included theory reduces to the ordinary real theory exactly when the imaginary
action vanishes (cf. `PathIntegral.QFTPathIntegralComplexAction`). -/
theorem effectiveLagrangian_eq_lagRealPart_of_reversible (m_R V_R qdot : ℝ) :
    effectiveLagrangian m_R 0 V_R qdot = lagRealPart m_R V_R qdot := by
  unfold effectiveLagrangian lagRealPart effectiveMass
  norm_num

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

end
