/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Generalized-trigonometric solution, `arcsin_{m,n}` inversion, and the generating function (Ghosh–Bhamidipati 1905.08062)

The special-function layer of `PurelyNonlinearActionAngle`: the exact generalized-trigonometric solution
(Eqs. 2.12–2.13), the incomplete-beta `arcsin_{m,n}` inversion defining the generalized sine (Eqs. 3.4, B.20), and
the canonical generating function `F = ∮ p dq'` (Eqs. 3.8–3.9). These are formalized at the level of their exact
**defining relations** — the linear angle flow, the integral definitions and their fundamental-theorem-of-calculus
derivatives (the inversion `sin_{m,n}' = cos_{m,n}` and the canonical `p = ∂F/∂q`) — not the closed-form
`₂F₁`/Beta *evaluations*, which are the paper's special-function content.

* **§A — the generalized-trigonometric solution (Eqs. 2.12–2.13).** `angleEvolution`;
 **`angleEvolution_hasDerivAt`** (`θ̇ = Ω`), `pnlSolution`; **`pnlSolution_initial`** (`q(0) = q₀` fixes
 `θ₀ = π_{2,α+1}/2`).
* **§B — the canonical generating function (Eqs. 3.8–3.9).** `generatingF`; **`momentum_eq_generatingF_deriv`**
 (`p = ∂F/∂q`), `reducedMomentum`; **`reducedMomentum_sq`**.
* **§C — the `arcsin_{m,n}` incomplete-beta inversion (Eqs. 3.4, B.20).** `genSineIntegrand`, `arcsinMN`
 (the `B.20` integral), `incompleteBeta`; **`arcsinMN_zero`**, **`arcsinMN_hasDerivAt`** (the inversion
 `d/dy arcsin_{m,n} = (1 − y^n)^{−1/m}`, so its inverse `sin_{m,n}` satisfies `sin' = (1 − sin^n)^{1/m} =
 cos_{m,n}`).

Exact `HasDerivAt`/`intervalIntegral`/`Real.sqrt` identities for the angle flow, the
generating-function and `arcsin_{m,n}` derivatives, and the momentum. The closed-form evaluations
`arcsin_{m,n} x = (1/n)B_x(1/n,(m−1)/m)` (Eq. 3.4, by the substitution `t = s^n`) and the `₂F₁` generating function
(Eqs. 3.9–3.10) — and the construction of `sin_{m,n}` as the inverse of `arcsinMN` — are the paper's
special-function analysis, recorded not re-derived; `incompleteBeta` is defined so the `B_x` form of Eq. 3.4 can be
stated.

## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062, Eqs. 2.12–2.13, 3.4, 3.8–3.9, B.20. Special-function layer of
 `PurelyNonlinearActionAngle`.

No new axioms.
-/

set_option autoImplicit false

open scoped Real
open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig

/-! ## §A — the generalized-trigonometric solution (Eqs. 2.12–2.13) -/

/-- The **angle variable's linear flow** `θ(t) = Ω t + θ₀` (Eq. 2.12) — the solution of the trivial action-angle
Hamilton equation `θ̇ = Ω(J)` (the action `J` being a first integral, `J̇ = 0`). -/
noncomputable def angleEvolution (Ω θ₀ t : ℝ) : ℝ := Ω * t + θ₀

/-- **The angle flows linearly `θ̇ = Ω`** (Eq. 2.12) — the angular frequency is constant on a level set. -/
theorem angleEvolution_hasDerivAt (Ω θ₀ t : ℝ) : HasDerivAt (angleEvolution Ω θ₀) Ω t := by
  have h : HasDerivAt (fun t => Ω * t + θ₀) (Ω * 1) t :=
    ((hasDerivAt_id t).const_mul Ω).add_const θ₀
  rw [mul_one] at h
  exact h

@[simp] theorem angleEvolution_zero (Ω θ₀ : ℝ) : angleEvolution Ω θ₀ 0 = θ₀ := by
  simp [angleEvolution]

/-- The **generalized-trigonometric solution** `q(t) = q₀ · sin_{2,α+1}(Ω t + π_{2,α+1}/2)` (Eq. 2.13) — the exact
solution of the purely nonlinear oscillator, with `S` the generalized sine `sin_{2,α+1}` and the initial phase
`θ₀ = π_{2,α+1}/2` (`genPi2 α / 2`). -/
noncomputable def pnlSolution (q₀ : ℝ) (S : ℝ → ℝ) (α Ω t : ℝ) : ℝ :=
  q₀ * S (angleEvolution Ω (genPi2 α / 2) t)

/-- **The initial condition `q(0) = q₀` fixes `θ₀ = π_{2,α+1}/2`** (Eq. 2.13) — since `sin_{m,n}(π_{m,n}/2) = 1`,
the amplitude phase is `π_{2,α+1}/2` and the solution starts at the turning point `q₀`. -/
theorem pnlSolution_initial (q₀ : ℝ) (S : ℝ → ℝ) (α Ω : ℝ) (hS : S (genPi2 α / 2) = 1) :
    pnlSolution q₀ S α Ω 0 = q₀ := by
  simp [pnlSolution, hS]

/-! ## §B — the canonical generating function (Eqs. 3.8–3.9) -/

/-- The **canonical generating function** `F(q) = ∫₀^q p dq'` (Eq. 3.8) — the type-2 generating function of the
canonical transformation to action-angle variables. -/
noncomputable def generatingF (pFun : ℝ → ℝ) (a q : ℝ) : ℝ := ∫ q' in a..q, pFun q'

/-- **The momentum is the `q`-gradient of the generating function** `p = ∂F/∂q` (Eq. 3.8) — the defining relation
of the type-2 generating function, from the fundamental theorem of calculus (for a continuous momentum `p`). -/
theorem momentum_eq_generatingF_deriv (pFun : ℝ → ℝ) (hp : Continuous pFun) (a q : ℝ) :
    HasDerivAt (generatingF pFun a) (pFun q) q := by
  show HasDerivAt (fun x => ∫ q' in a..x, pFun q') (pFun q) q
  exact intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable a q)
    hp.stronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt

/-- The **reduced momentum in action variables** `p = √(2I/τ − q^{α+1}/τ²)` (Eq. 3.9 integrand) — the momentum
expressed through the adiabatic action `I` and the length scale `τ`; `F = ∫₀^q p dq'` is the `₂F₁` generating
function of Eq. 3.9. -/
noncomputable def reducedMomentum (I α τ q : ℝ) : ℝ := Real.sqrt (2 * I / τ - q ^ (α + 1) / τ ^ 2)

/-- **The reduced momentum squares to the on-shell relation** `p² = 2I/τ − q^{α+1}/τ²` — the algebraic content of
the `₂F₁` integrand (where the radicand is non-negative). -/
theorem reducedMomentum_sq (I α τ q : ℝ) (h : 0 ≤ 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    reducedMomentum I α τ q ^ 2 = 2 * I / τ - q ^ (α + 1) / τ ^ 2 :=
  Real.sq_sqrt h

/-! ## §C — the `arcsin_{m,n}` incomplete-beta inversion (Eqs. 3.4, B.20) -/

/-- The **generalized-sine integrand** `(1 − t^n)^{−1/m}` — the integrand whose primitive is `arcsin_{m,n}`. -/
noncomputable def genSineIntegrand (m n t : ℝ) : ℝ := (1 - t ^ n) ^ (-(1 / m))

/-- The **generalized arcsine** `arcsin_{m,n}(y) = ∫₀^y (1 − t^n)^{−1/m} dt` (Eq. B.20) — the integral whose
inverse is the generalized sine `sin_{m,n}`. -/
noncomputable def arcsinMN (m n y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, genSineIntegrand m n t

/-- The **incomplete beta function** `B_x(a,b) = ∫₀^x t^{a−1}(1−t)^{b−1} dt` — so that `arcsin_{m,n}` has the
closed-form `(1/n)B_{y^n}(1/n,(m−1)/m)` (Eq. 3.4, by the substitution `t = s^n`). -/
noncomputable def incompleteBeta (x a b : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ (b - 1)

@[simp] theorem arcsinMN_zero (m n : ℝ) : arcsinMN m n 0 = 0 := by
  simp [arcsinMN]

@[simp] theorem incompleteBeta_zero (a b : ℝ) : incompleteBeta 0 a b = 0 := by
  simp [incompleteBeta]

/-- **`arcsin_{m,n}` inverts the generalized sine** `d/dy arcsin_{m,n}(y) = (1 − y^n)^{−1/m}` (Eqs. 3.4, B.20) —
the fundamental theorem of calculus for the defining integral. Hence its inverse `sin_{m,n}` satisfies the
generalized-trigonometric ODE `sin_{m,n}' = (1 − sin_{m,n}^n)^{1/m} = cos_{m,n}` (whose `m = 2`, `n = α+1` case is
the purely nonlinear oscillator, `sa² + ca^{α+1} = 1`). Valid where the integrand is continuous and integrable
(the branch `|y| < 1`). -/
theorem arcsinMN_hasDerivAt (m n y : ℝ)
    (hi : IntervalIntegrable (genSineIntegrand m n) volume 0 y)
    (hmeas : StronglyMeasurableAtFilter (genSineIntegrand m n) (nhds y))
    (hc : ContinuousAt (genSineIntegrand m n) y) :
    HasDerivAt (arcsinMN m n) (genSineIntegrand m n y) y := by
  show HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, genSineIntegrand m n t) _ y
  exact intervalIntegral.integral_hasDerivAt_right hi hmeas hc

end Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
