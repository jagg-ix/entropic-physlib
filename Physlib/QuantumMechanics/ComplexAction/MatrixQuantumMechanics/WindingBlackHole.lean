/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Winding perturbations of MQM: Sine–Liouville, the black hole, and Toda (Alexandrov §IV)

Winding (vortex) perturbations of compactified MQM describe 2D string theory in a **curved (black hole)
background** (Alexandrov, hep-th/0311273, Ch. IV). The simplest case `λ_{±1} ≠ 0` is the **Sine–Liouville
CFT** (Eq. IV.19), conjectured dual to the `2D` Euclidean black hole; the winding partition function is a
**τ-function of the Toda hierarchy** (Eq. IV.15), so it obeys the Toda equation (Eq. IV.23).

* **§A — Sine–Liouville marginality** (Eq. IV.20). The Liouville/winding dressings `γ = −Q + √(Q²−4)` and
  `ρ = −Q + √(R²+Q²−4)` are the marginal roots `γ² + 2Qγ + 4 = 0`, `ρ² + 2Qρ + (4−R²) = 0`
  (`sineLiouville_marginal_gamma`, `sineLiouville_marginal_rho`).
* **§B — central charge and the black-hole point** (Eqs. IV.19, IV.21–IV.22). `centralCharge Q = 2 + 6Q²`;
  `centralCharge_eq_26_iff`: criticality `c = 26 ⟺ Q² = 4`. At the black-hole point `R = 3/2`
  (so `k = R² = 9/4`), the level expression `Q = 1/√(k−2)` equals `2` and `c = 26` (`blackHole_point`).
* **§C — the winding free energy as a Toda τ-function** (Eqs. IV.15, IV.23). `winding_toda_nonlinearity`:
  the free-energy nonlinearity `exp[F(μ+i) + F(μ−i) − 2F(μ)]` equals the τ-function ratio
  `τ_{l+1}τ_{l-1}/τ_l²`, so the winding Toda equation (Eq. IV.23) is the τ-form Toda equation
  (Eq. II.136) — connecting Ch. IV to `[[project_alexandrov_mqm_thesis]]` (the `MatrixQuantumMechanics.TodaLaxHirotaString`
  Hirota ⟺ Toda result).

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. IV, Eqs. (IV.15), (IV.19)–(IV.23).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.WindingBlackHole

/-! ## §A — Sine–Liouville marginality conditions (Eq. IV.20) -/

/-- **[Marginal Liouville dressing, Eq. IV.20]** `γ = −Q + √(Q²−4)` is the marginal root
`γ² + 2Qγ + 4 = 0` — the condition that the Liouville operator `e^{γφ}` of the Sine–Liouville CFT is
marginal (dimension 1). -/
theorem sineLiouville_marginal_gamma (Q : ℝ) (hQ : 4 ≤ Q ^ 2) :
    (-Q + Real.sqrt (Q ^ 2 - 4)) ^ 2 + 2 * Q * (-Q + Real.sqrt (Q ^ 2 - 4)) + 4 = 0 := by
  have h : Real.sqrt (Q ^ 2 - 4) ^ 2 = Q ^ 2 - 4 := Real.sq_sqrt (by linarith)
  linear_combination h

/-- **[Marginal winding dressing, Eq. IV.20]** `ρ = −Q + √(R²+Q²−4)` is the marginal root
`ρ² + 2Qρ + (4−R²) = 0` — the condition that the winding operator `e^{ρφ} cos(RX̃)` is marginal at
compactification radius `R`. -/
theorem sineLiouville_marginal_rho (Q R : ℝ) (hQR : 4 ≤ R ^ 2 + Q ^ 2) :
    (-Q + Real.sqrt (R ^ 2 + Q ^ 2 - 4)) ^ 2 + 2 * Q * (-Q + Real.sqrt (R ^ 2 + Q ^ 2 - 4))
      + (4 - R ^ 2) = 0 := by
  have h : Real.sqrt (R ^ 2 + Q ^ 2 - 4) ^ 2 = R ^ 2 + Q ^ 2 - 4 := Real.sq_sqrt (by linarith)
  linear_combination h

/-! ## §B — central charge and the black-hole point (Eqs. IV.19, IV.21–IV.22) -/

/-- **The Sine–Liouville central charge** `c = 2 + 6Q²` (Eq. IV.19). -/
def centralCharge (Q : ℝ) : ℝ := 2 + 6 * Q ^ 2

/-- **[Criticality, Eq. IV.22]** `c = 26 ⟺ Q² = 4` — the `c = 26` matrix-model (critical-string) condition
fixes `Q = 2`. -/
theorem centralCharge_eq_26_iff (Q : ℝ) : centralCharge Q = 26 ↔ Q ^ 2 = 4 := by
  unfold centralCharge
  constructor <;> intro h <;> linarith

/-- **[The black-hole point is consistent, Eqs. IV.21–IV.22]** At `R = 3/2` (so the level is `k = R² = 9/4`)
the level expression `Q = 1/√(k−2)` equals `2`, matching the central-charge value `Q = 2`, and `c = 26`. The
two parameter conditions of the Sine–Liouville / black-hole duality intersect at `Q = 2, R = 3/2`. -/
theorem blackHole_point :
    1 / Real.sqrt ((3 / 2 : ℝ) ^ 2 - 2) = 2 ∧ centralCharge 2 = 26 := by
  refine ⟨?_, by unfold centralCharge; norm_num⟩
  rw [show ((3 / 2 : ℝ) ^ 2 - 2) = (1 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## §C — the winding free energy as a Toda τ-function (Eqs. IV.15, IV.23) -/

/-- **[Winding Toda nonlinearity, Eq. IV.23 ↔ II.136]** `exp[F(μ+i) + F(μ−i) − 2F(μ)] = τ_{l+1}τ_{l-1}/τ_l²`
where `F = log τ`. The free-energy form of the Toda nonlinearity (Eq. IV.23) is exactly the τ-function ratio
of the Toda equation (Eq. II.136): the winding partition function is a τ-function of the Toda hierarchy. -/
theorem winding_toda_nonlinearity (τ τp τm : ℝ) (hτ : 0 < τ) (hp : 0 < τp) (hm : 0 < τm) :
    Real.exp (Real.log τp + Real.log τm - 2 * Real.log τ) = τp * τm / τ ^ 2 := by
  have h2 : Real.exp (2 * Real.log τ) = τ ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hτ]; ring
  rw [Real.exp_sub, Real.exp_add, Real.exp_log hp, Real.exp_log hm, h2]

/-- **[Winding Toda equation, Eq. IV.23]** with `D = ∂_{t₁}∂_{t₋₁}F` the free-energy Toda equation
`D + exp[F(μ+i) + F(μ−i) − 2F(μ)] = 0` is equivalent to the τ-form Toda equation
`D + τ_{l+1}τ_{l-1}/τ_l² = 0` (Eq. II.136). -/
theorem winding_toda_equation_iff (D τ τp τm : ℝ) (hτ : 0 < τ) (hp : 0 < τp) (hm : 0 < τm) :
    D + Real.exp (Real.log τp + Real.log τm - 2 * Real.log τ) = 0 ↔ D + τp * τm / τ ^ 2 = 0 := by
  rw [winding_toda_nonlinearity τ τp τm hτ hp hm]

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.WindingBlackHole

end
