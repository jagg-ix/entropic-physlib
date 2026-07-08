/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# The Gegenbauer (ultraspherical) ODE and its low-order polynomial solutions

Formalizes the **Gegenbauer differential equation** (the Eq. 17 ODE of the Cutkosky Bethe–Salpeter
problem, the angular `O(4)` / hydrogen part) and its polynomial eigenfunctions — the piece the
`BetheSalpeter.CutkoskyCompleteSolution` scope note left open ("the Gegenbauer eigenfunctions ... are not
formalized"). The Gegenbauer equation is

 `(1 − x²) y'' − (2α+1) x y' + n(n+2α) y = 0`,

with eigenvalue `λ_n = n(n+2α)` (`gegenbauerEigenvalue`). At `α = 1/2` (the Legendre case) the eigenvalue is
`n(n+1) = cutkoskyEigenvalue n = reggeCasimir n`, the hydrogen `O(4)` Casimir.

* **§A — the eigenvalue** (`gegenbauerEigenvalue`, `gegenbauerEigenvalue_half_eq_cutkosky`). `λ_n = n(n+2α)`;
 at `α = 1/2` it is the Cutkosky/hydrogen `N(N+1)`.
* **§B — the ODE predicate** (`IsGegenbauerSolution`). `y` solves the Gegenbauer ODE with derivative `dy`
 (and second derivative `ddy`): `HasDerivAt y (dy x) x`, `HasDerivAt dy (ddy x) x`, and the ODE holds.
* **§C — the low-order polynomial solutions** (`gegenbauer0_solves`, `gegenbauer1_solves`,
 `gegenbauer2_solves`). `C₀ = 1` (λ₀ = 0), `C₁ = 2αx` (λ₁ = 1+2α), `C₂ = 2α(α+1)x² − α` (λ₂ = 2(2+2α)) each
 solve the Gegenbauer ODE — the eigenvalue derivation is the calculus exercise the note anticipated.
* **§D — the Legendre / hydrogen specialization** (`legendre2_solves`, `legendre2_eigenvalue`). At `α = 1/2`
 the solutions are the Legendre polynomials (`C₂^{1/2} = (3x²−1)/2 = P₂`) solving the Legendre ODE with
 eigenvalue `n(n+1) = reggeCasimir n` — the hydrogen bound-state angular eigenfunctions.
* **§E — the general-`n` solution at `α = 1`** (`gegenbauerOne`, `gegenbauerOne_solves`). `C_n^{(1)} = U_n`
 (Mathlib's Chebyshev polynomial of the second kind) solves the Gegenbauer ODE for **every** `n`
 (eigenvalue `n(n+2)`, the `S³`/`O(4)` Laplacian), by using Mathlib's Chebyshev second-derivative
 identity — the all-`n` Cutkosky angular eigenfunction.

**Scope.** The general-`n` eigenfunction is now proven at `α = 1` (via Mathlib's Chebyshev `U`, §E).
For general `α` only `n ≤ 2` eigenfunctions are proven (the general-`α` general-`n` proof needs the
Gegenbauer recurrence and a derivative-of-recurrence induction, or a Mathlib Legendre/Gegenbauer family —
a bounded follow-up). The eigenvalue `n(n+2α)` and its hydrogen identification hold for all `n`, all `α`.

## References

* L. Gegenbauer (1874); ultraspherical polynomials. DLMF §18.3 (Gegenbauer / ultraspherical), §14
 (Legendre).
* R. E. Cutkosky, Phys. Rev. 96 (1954) 1135 — the Bethe–Salpeter Eq. 17 ODE and `O(4)` spectrum.
* Repo structure: `BetheSalpeter.CutkoskyBetheSalpeterSolution` (`cutkoskyEigenvalue = N(N+1) = reggeCasimir`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-! ## §A — the Gegenbauer eigenvalue `λ_n = n(n+2α)` -/

/-- **The Gegenbauer (ultraspherical) ODE eigenvalue** `λ_n = n(n+2α)`. -/
noncomputable def gegenbauerEigenvalue (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 2 * α)

/-- **[Link — hydrogen `O(4)` Casimir] At `α = 1/2` the Gegenbauer eigenvalue is the Cutkosky eigenvalue.**
`gegenbauerEigenvalue (1/2) n = n(n+1) = cutkoskyEigenvalue n = reggeCasimir n`: the Legendre/Gegenbauer ODE
eigenvalue is the hydrogen bound-state `O(4)` Casimir. -/
theorem gegenbauerEigenvalue_half_eq_cutkosky (n : ℕ) :
    gegenbauerEigenvalue (1 / 2) n = cutkoskyEigenvalue n := by
  unfold gegenbauerEigenvalue cutkoskyEigenvalue; ring

/-! ## §B — the Gegenbauer ODE predicate -/

/-- **`y` solves the Gegenbauer ODE** with first derivative `dy` and a second derivative: for every `x`,
`HasDerivAt y (dy x) x`, there is `ddy` with `HasDerivAt dy ddy x`, and
`(1 − x²)·ddy − (2α+1)x·dy(x) + λ_n·y(x) = 0`. -/
def IsGegenbauerSolution (α : ℝ) (n : ℕ) (y dy : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, HasDerivAt y (dy x) x ∧
    ∃ ddy : ℝ, HasDerivAt dy ddy x ∧
      (1 - x ^ 2) * ddy - (2 * α + 1) * x * dy x + gegenbauerEigenvalue α n * y x = 0

/-! ## §C — the low-order polynomial solutions -/

/-- **`C₀^{(α)}(x) = 1` solves the Gegenbauer ODE** (eigenvalue `λ₀ = 0`). -/
theorem gegenbauer0_solves (α : ℝ) :
    IsGegenbauerSolution α 0 (fun _ => 1) (fun _ => 0) := by
  intro x
  refine ⟨hasDerivAt_const x 1, 0, hasDerivAt_const x 0, ?_⟩
  unfold gegenbauerEigenvalue; push_cast; ring

/-- **`C₁^{(α)}(x) = 2αx` solves the Gegenbauer ODE** (eigenvalue `λ₁ = 1+2α`). -/
theorem gegenbauer1_solves (α : ℝ) :
    IsGegenbauerSolution α 1 (fun x => 2 * α * x) (fun _ => 2 * α) := by
  intro x
  refine ⟨by simpa using (hasDerivAt_id x).const_mul (2 * α), 0, hasDerivAt_const x (2 * α), ?_⟩
  unfold gegenbauerEigenvalue; push_cast; ring

/-- **`C₂^{(α)}(x) = 2α(α+1)x² − α` solves the Gegenbauer ODE** (eigenvalue `λ₂ = 2(2+2α)`). -/
theorem gegenbauer2_solves (α : ℝ) :
    IsGegenbauerSolution α 2
      (fun x => 2 * α * (α + 1) * x ^ 2 - α) (fun x => 4 * α * (α + 1) * x) := by
  intro x
  refine ⟨?_, 4 * α * (α + 1), by exact ((hasDerivAt_id x).const_mul (4 * α * (α + 1))).congr_deriv (by ring), ?_⟩
  · have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h := (hp.const_mul (2 * α * (α + 1))).sub_const α
    exact h.congr_deriv (by ring)
  · unfold gegenbauerEigenvalue; push_cast; ring

/-! ## §D — the Legendre (`α = 1/2`) / hydrogen specialization -/

/-- **[Legendre] `C₂^{(1/2)}(x) = (3x² − 1)/2 = P₂(x)` solves the Legendre ODE.** At `α = 1/2` the Gegenbauer
ODE is the Legendre equation `(1 − x²)y'' − 2xy' + n(n+1)y = 0`, and `C₂^{(1/2)}` is the Legendre polynomial
`P₂`. -/
theorem legendre2_solves :
    IsGegenbauerSolution (1 / 2) 2
      (fun x => 2 * (1 / 2) * ((1 / 2) + 1) * x ^ 2 - (1 / 2)) (fun x => 4 * (1 / 2) * ((1 / 2) + 1) * x) :=
  gegenbauer2_solves (1 / 2)

/-- **[Link — hydrogen eigenvalue] The `α = 1/2` Gegenbauer/Legendre eigenvalue is the hydrogen `O(4)`
Casimir `N(N+1)`.** For the bound state `N`, `gegenbauerEigenvalue (1/2) N = cutkoskyEigenvalue N =
reggeCasimir N`: the Gegenbauer eigenfunction's eigenvalue is exactly the Cutkosky Bethe–Salpeter / hydrogen
spectrum. -/
theorem legendre2_eigenvalue (N : ℕ) :
    gegenbauerEigenvalue (1 / 2) N = cutkoskyEigenvalue N :=
  gegenbauerEigenvalue_half_eq_cutkosky N

/-! ## §E — general `n` at `α = 1` via Mathlib's Chebyshev `U` (Gegenbauer `C_n^{(1)}`) -/

open Polynomial Polynomial.Chebyshev in
/-- The Gegenbauer polynomial `C_n^{(1)}` is Mathlib's Chebyshev polynomial of the second kind `U_n`
(`Polynomial.Chebyshev.U`). -/
noncomputable def gegenbauerOne (n : ℕ) : ℝ → ℝ := fun x => (U ℝ (n : ℤ)).eval x

/-- **The `α = 1` Gegenbauer eigenvalue is `n(n+2)`** — the `S³` Laplacian / `O(4)` eigenvalue. -/
theorem gegenbauerEigenvalue_one (n : ℕ) : gegenbauerEigenvalue 1 n = (n : ℝ) * ((n : ℝ) + 2) := by
  unfold gegenbauerEigenvalue; ring

open Polynomial Polynomial.Chebyshev in
/-- **[General `n` — the all-`n` solution at `α = 1`] `C_n^{(1)} = U_n` solves the Gegenbauer ODE for every
`n`**, with eigenvalue `λ_n = n(n+2)`. Proven by using Mathlib's Chebyshev second-derivative identity
`one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U` (`(1−X²)U'' = 3X·U' − n(n+2)·U`) together with
`Polynomial.hasDerivAt`. This is the `O(4)`/`S³` ultraspherical harmonic — the Cutkosky angular
eigenfunction — for all `n`, closing the general-`n` case at `α = 1` left open in the low-order section. -/
theorem gegenbauerOne_solves (n : ℕ) :
    IsGegenbauerSolution 1 n (gegenbauerOne n) (fun x => (derivative (U ℝ (n : ℤ))).eval x) := by
  intro x
  refine ⟨(U ℝ (n : ℤ)).hasDerivAt x, (derivative (derivative (U ℝ (n : ℤ)))).eval x,
    (derivative (U ℝ (n : ℤ))).hasDerivAt x, ?_⟩
  have key := one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := ℝ) (n : ℤ)
  rw [Function.iterate_succ_apply', Function.iterate_one] at key
  have keyEval := congr_arg (eval x) key
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_ofNat, eval_intCast,
    eval_add] at keyEval
  push_cast at keyEval
  unfold gegenbauerEigenvalue gegenbauerOne
  linear_combination keyEval

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

end
