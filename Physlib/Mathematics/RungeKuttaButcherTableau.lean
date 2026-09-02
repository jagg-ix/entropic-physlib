/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Runge–Kutta Butcher tableaux and their algebraic order conditions

Ports `NavierStokes/ButcherTableauFormalization.lean` of the reference tree — the algebraic
core of Butcher's B-series theory of Runge–Kutta methods, over `ℚ`.  A method is a tableau
`(A, b, c)` of stage coefficients, quadrature weights, and quadrature nodes; its order is
decided by polynomial conditions on the tableau:

* `IsConsistent` — **B(1)**, `∑ bᵢ = 1`: constants are integrated exactly (order ≥ 1);
* `IsStageConsistent` — **C(1)**, `cᵢ = ∑ⱼ aᵢⱼ`: each stage sits at its node;
* `HasOrderTwo` — **B(2)**, `∑ bᵢcᵢ = 1/2`: linear functions are integrated exactly;
* `HasOrderThreeQuadrature` — **B(3)**, `∑ bᵢcᵢ² = 1/3`: the quadrature layer of order three
  (added here beyond the source, completing the `B(k)` ladder through the classical methods);
* `IsStifflyAccurate` — the last stage is the update, `a_{s,j} = bⱼ` (the L-stability
  mechanism for stiff problems).

Concrete tableaux with their order conditions decided by `norm_num` — genuinely, including the
negative results:

* `gaussLegendre1` (implicit midpoint): consistent, stage-consistent, order two — and **not**
  order-three quadrature (`gaussLegendre1_not_order3`);
* `radauIIA1` (backward Euler): consistent, stiffly accurate — and **not** order two
  (`radauIIA1_not_order2`);
* `classicalRK4` (the classical four-stage method): consistent, stage-consistent, order two,
  and order-three quadrature — the extension of the source file to a multi-stage tableau.

**Honest layering.**  These are the algebraic order conditions on tableaux; the analytic
statement that they imply the corresponding convergence order of the integrator (B-series /
rooted-tree expansion, Hairer–Nørsett–Wanner §II.2) is the numerical-analysis layer, recorded
not re-derived.

## References

* J. C. Butcher, *Numerical Methods for Ordinary Differential Equations* (2016);
  E. Hairer, S. P. Nørsett, G. Wanner, *Solving Ordinary Differential Equations I* (1987),
  §II.1–II.2.  Source: `NavierStokes/ButcherTableauFormalization.lean` (reference tree, own
  authorship), re-authored with the `B(3)` layer and the classical four-stage tableau added.
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.Mathematics.RungeKuttaButcherTableau

/-- **A Butcher tableau** with `s` stages over `ℚ`: stage coefficients `A`, quadrature weights
`b`, quadrature nodes `c`. -/
structure ButcherTableau (s : ℕ) where
  /-- Stage coefficient matrix `a_{ij}` — the weight of stage `j` inside stage `i`. -/
  A : Fin s → Fin s → ℚ
  /-- Quadrature weights `bᵢ` for the final update. -/
  b : Fin s → ℚ
  /-- Quadrature nodes `cᵢ` — the position of stage `i` inside the step. -/
  c : Fin s → ℚ

namespace ButcherTableau

variable {s : ℕ}

/-- **B(1), consistency**: `∑ bᵢ = 1` — constants are integrated exactly. -/
def IsConsistent (bt : ButcherTableau s) : Prop :=
  ∑ i, bt.b i = 1

/-- **C(1), stage consistency**: `cᵢ = ∑ⱼ aᵢⱼ` — each stage sits at its quadrature node. -/
def IsStageConsistent (bt : ButcherTableau s) : Prop :=
  ∀ i, bt.c i = ∑ j, bt.A i j

/-- **B(2), order two**: `∑ bᵢcᵢ = 1/2` — linear functions are integrated exactly. -/
def HasOrderTwo (bt : ButcherTableau s) : Prop :=
  ∑ i, bt.b i * bt.c i = 1/2

/-- **B(3), order-three quadrature**: `∑ bᵢcᵢ² = 1/3` — quadratics are integrated exactly. -/
def HasOrderThreeQuadrature (bt : ButcherTableau s) : Prop :=
  ∑ i, bt.b i * bt.c i ^ 2 = 1/3

/-- **Stiff accuracy**: the last stage coincides with the update, `a_{s,j} = bⱼ` — the
mechanism behind L-stability. -/
def IsStifflyAccurate (bt : ButcherTableau s) : Prop :=
  ∀ (hs : 0 < s) (j : Fin s), bt.A ⟨s - 1, Nat.sub_lt hs Nat.one_pos⟩ j = bt.b j

end ButcherTableau

/-! ## Gauss–Legendre with one stage: the implicit midpoint rule -/

/-- **Gauss–Legendre, one stage** — the implicit midpoint rule: `c = [1/2]`, `A = [[1/2]]`,
`b = [1]`.  Order two, symplectic, A-stable. -/
def gaussLegendre1 : ButcherTableau 1 where
  A := fun _ _ => 1/2
  b := fun _ => 1
  c := fun _ => 1/2

theorem gaussLegendre1_consistent : gaussLegendre1.IsConsistent := by
  simp [ButcherTableau.IsConsistent, gaussLegendre1]

theorem gaussLegendre1_stageConsistent : gaussLegendre1.IsStageConsistent := by
  intro i
  simp [gaussLegendre1]

theorem gaussLegendre1_orderTwo : gaussLegendre1.HasOrderTwo := by
  simp [ButcherTableau.HasOrderTwo, gaussLegendre1]

/-- The midpoint rule does **not** integrate quadratics exactly: `1·(1/2)² = 1/4 ≠ 1/3`. -/
theorem gaussLegendre1_not_order3 : ¬ gaussLegendre1.HasOrderThreeQuadrature := by
  simp [ButcherTableau.HasOrderThreeQuadrature, gaussLegendre1]
  norm_num

/-! ## Radau IIA with one stage: backward Euler -/

/-- **Radau IIA, one stage** — backward Euler: `c = [1]`, `A = [[1]]`, `b = [1]`.  Order one,
L-stable, stiffly accurate. -/
def radauIIA1 : ButcherTableau 1 where
  A := fun _ _ => 1
  b := fun _ => 1
  c := fun _ => 1

theorem radauIIA1_consistent : radauIIA1.IsConsistent := by
  simp [ButcherTableau.IsConsistent, radauIIA1]

/-- Backward Euler is **not** order two: `1·1 = 1 ≠ 1/2`. -/
theorem radauIIA1_not_order2 : ¬ radauIIA1.HasOrderTwo := by
  simp [ButcherTableau.HasOrderTwo, radauIIA1]

theorem radauIIA1_stifflyAccurate : radauIIA1.IsStifflyAccurate := by
  intro _ j
  simp [radauIIA1]

/-! ## The classical four-stage Runge–Kutta method -/

/-- **The classical Runge–Kutta method** (four stages):
`c = (0, 1/2, 1/2, 1)`, `b = (1/6, 1/3, 1/3, 1/6)`, with the strictly lower-triangular
`A` of the explicit scheme (`a₁₀ = a₂₁ = 1/2`, `a₃₂ = 1`). -/
def classicalRK4 : ButcherTableau 4 where
  A := fun i j =>
    if i = 1 ∧ j = 0 then 1/2
    else if i = 2 ∧ j = 1 then 1/2
    else if i = 3 ∧ j = 2 then 1
    else 0
  b := fun i => if i = 0 ∨ i = 3 then 1/6 else 1/3
  c := fun i => if i = 0 then 0 else if i = 3 then 1 else 1/2

theorem classicalRK4_consistent : classicalRK4.IsConsistent := by
  show ∑ i, classicalRK4.b i = 1
  rw [Fin.sum_univ_four]
  simp +decide [classicalRK4]
  norm_num

theorem classicalRK4_stageConsistent : classicalRK4.IsStageConsistent := by
  intro i
  rw [Fin.sum_univ_four]
  fin_cases i <;> simp +decide [classicalRK4]

theorem classicalRK4_orderTwo : classicalRK4.HasOrderTwo := by
  show ∑ i, classicalRK4.b i * classicalRK4.c i = 1/2
  rw [Fin.sum_univ_four]
  simp +decide [classicalRK4]
  norm_num

/-- The classical method's quadrature layer reaches order three: Simpson's rule,
`∑ bᵢcᵢ² = 1/3·1/4 + 1/3·1/4 + 1/6 = 1/3`. -/
theorem classicalRK4_orderThreeQuadrature : classicalRK4.HasOrderThreeQuadrature := by
  show ∑ i, classicalRK4.b i * classicalRK4.c i ^ 2 = 1/3
  rw [Fin.sum_univ_four]
  simp +decide [classicalRK4]
  norm_num

end Physlib.Mathematics.RungeKuttaButcherTableau

end
