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
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

meta import Zil

/-!
# The Gegenbauer (ultraspherical) ODE and its low-order polynomial solutions

Formalizes the **Gegenbauer differential equation** (the Eq. 17 ODE of the Cutkosky Bethe–Salpeter
problem, the angular `O(4)` / hydrogen part) and its polynomial eigenfunctions — the piece the
`BetheSalpeter.CutkoskyCompleteSolution` honest-scope note left open ("the Gegenbauer eigenfunctions ... are not
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

**Honest scope.** The general-`n` eigenfunction is now proven at `α = 1` (via Mathlib's Chebyshev `U`, §E).
For general `α` only `n ≤ 2` eigenfunctions are proven (the general-`α` general-`n` proof needs the
Gegenbauer recurrence and a derivative-of-recurrence induction, or a Mathlib Legendre/Gegenbauer family —
a bounded follow-up). The eigenvalue `n(n+2α)` and its hydrogen identification hold for all `n`, all `α`.

## References

* L. Gegenbauer (1874); ultraspherical polynomials. DLMF §18.3 (Gegenbauer / ultraspherical), §14
  (Legendre).
* R. E. Cutkosky, Phys. Rev. 96 (1954) 1135 — the Bethe–Salpeter Eq. 17 ODE and `O(4)` spectrum.
* Repo carrier: `BetheSalpeter.CutkoskyBetheSalpeterSolution` (`cutkoskyEigenvalue = N(N+1) = reggeCasimir`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution


/-- **The Gegenbauer (ultraspherical) ODE eigenvalue** `λ_n = n(n+2α)`. -/
noncomputable def gegenbauerEigenvalue (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 2 * α)

/-- **[Link — hydrogen `O(4)` Casimir] At `α = 1/2` the Gegenbauer eigenvalue is the Cutkosky eigenvalue.**
`gegenbauerEigenvalue (1/2) n = n(n+1) = cutkoskyEigenvalue n = reggeCasimir n`: the Legendre/Gegenbauer ODE
eigenvalue is the hydrogen bound-state `O(4)` Casimir. -/
lemma gegenbauerEigenvalue_half_eq_cutkosky (n : ℕ) :
    gegenbauerEigenvalue (1 / 2) n = cutkoskyEigenvalue n := by
  unfold gegenbauerEigenvalue cutkoskyEigenvalue; ring


/-- **`y` solves the Gegenbauer ODE** with first derivative `dy` and a second derivative: for every `x`,
`HasDerivAt y (dy x) x`, there is `ddy` with `HasDerivAt dy ddy x`, and
`(1 − x²)·ddy − (2α+1)x·dy(x) + λ_n·y(x) = 0`. -/
def IsGegenbauerSolution (α : ℝ) (n : ℕ) (y dy : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, HasDerivAt y (dy x) x ∧
    ∃ ddy : ℝ, HasDerivAt dy ddy x ∧
      (1 - x ^ 2) * ddy - (2 * α + 1) * x * dy x + gegenbauerEigenvalue α n * y x = 0


/-- **`C₀^{(α)}(x) = 1` solves the Gegenbauer ODE** (eigenvalue `λ₀ = 0`). -/
lemma gegenbauer0_solves (α : ℝ) :
    IsGegenbauerSolution α 0 (fun _ => 1) (fun _ => 0) := by
  intro x
  refine ⟨hasDerivAt_const x 1, 0, hasDerivAt_const x 0, ?_⟩
  unfold gegenbauerEigenvalue; push_cast; ring

/-- **`C₁^{(α)}(x) = 2αx` solves the Gegenbauer ODE** (eigenvalue `λ₁ = 1+2α`). -/
lemma gegenbauer1_solves (α : ℝ) :
    IsGegenbauerSolution α 1 (fun x => 2 * α * x) (fun _ => 2 * α) := by
  intro x
  refine ⟨by simpa using (hasDerivAt_id x).const_mul (2 * α), 0, hasDerivAt_const x (2 * α), ?_⟩
  unfold gegenbauerEigenvalue; push_cast; ring

/-- **`C₂^{(α)}(x) = 2α(α+1)x² − α` solves the Gegenbauer ODE** (eigenvalue `λ₂ = 2(2+2α)`). -/
lemma gegenbauer2_solves (α : ℝ) :
    IsGegenbauerSolution α 2
      (fun x => 2 * α * (α + 1) * x ^ 2 - α) (fun x => 4 * α * (α + 1) * x) := by
  intro x
  refine ⟨?_, 4 * α * (α + 1), by exact ((hasDerivAt_id x).const_mul (4 * α * (α + 1))).congr_deriv (by ring), ?_⟩
  · have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h := (hp.const_mul (2 * α * (α + 1))).sub_const α
    exact h.congr_deriv (by ring)
  · unfold gegenbauerEigenvalue; push_cast; ring


/-- **[Legendre] `C₂^{(1/2)}(x) = (3x² − 1)/2 = P₂(x)` solves the Legendre ODE.** At `α = 1/2` the Gegenbauer
ODE is the Legendre equation `(1 − x²)y'' − 2xy' + n(n+1)y = 0`, and `C₂^{(1/2)}` is the Legendre polynomial
`P₂`. -/
lemma legendre2_solves :
    IsGegenbauerSolution (1 / 2) 2
      (fun x => 2 * (1 / 2) * ((1 / 2) + 1) * x ^ 2 - (1 / 2)) (fun x => 4 * (1 / 2) * ((1 / 2) + 1) * x) :=
  gegenbauer2_solves (1 / 2)

/-- **[Link — hydrogen eigenvalue] The `α = 1/2` Gegenbauer/Legendre eigenvalue is the hydrogen `O(4)`
Casimir `N(N+1)`.** For the bound state `N`, `gegenbauerEigenvalue (1/2) N = cutkoskyEigenvalue N =
reggeCasimir N`: the Gegenbauer eigenfunction's eigenvalue is exactly the Cutkosky Bethe–Salpeter / hydrogen
spectrum. -/
lemma legendre2_eigenvalue (N : ℕ) :
    gegenbauerEigenvalue (1 / 2) N = cutkoskyEigenvalue N :=
  gegenbauerEigenvalue_half_eq_cutkosky N


open Polynomial Polynomial.Chebyshev in
/-- The Gegenbauer polynomial `C_n^{(1)}` is Mathlib's Chebyshev polynomial of the second kind `U_n`
(`Polynomial.Chebyshev.U`). -/
noncomputable def gegenbauerOne (n : ℕ) : ℝ → ℝ := fun x => (U ℝ (n : ℤ)).eval x

/-- **The `α = 1` Gegenbauer eigenvalue is `n(n+2)`** — the `S³` Laplacian / `O(4)` eigenvalue. -/
lemma gegenbauerEigenvalue_one (n : ℕ) : gegenbauerEigenvalue 1 n = (n : ℝ) * ((n : ℝ) + 2) := by
  unfold gegenbauerEigenvalue; ring

open Polynomial Polynomial.Chebyshev in
/-- **[General `n` — the all-`n` solution at `α = 1`] `C_n^{(1)} = U_n` solves the Gegenbauer ODE for every
`n`**, with eigenvalue `λ_n = n(n+2)`. Proven by using Mathlib's Chebyshev second-derivative identity
`one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U` (`(1−X²)U'' = 3X·U' − n(n+2)·U`) together with
`Polynomial.hasDerivAt`. This is the `O(4)`/`S³` ultraspherical harmonic — the Cutkosky angular
eigenfunction — for all `n`, closing the general-`n` case at `α = 1` left open in the low-order section. -/
lemma gegenbauerOne_solves (n : ℕ) :
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

/-! ### `P₄` — the `n = 4` Legendre member

The fourth Legendre polynomial `P₄(x) = (35x⁴ − 30x² + 3)/8` is the `α = 1/2`, `n = 4`
member of the family above, solving the Legendre ODE with eigenvalue `4·5 = 20`
(`legendre4_solves`).  Its exact algebra: both range bounds come from factorisations —
`1 − P₄ = 5(7x²+1)(1−x²)/8` and `P₄ + 3/7 = 5(7x²−3)²/56` — so on `[−1, 1]` the range
is `[−3/7, 1]` with both ends attained, and `∫₋₁¹ P₄ = 0` by orthogonality to `P₀`.

Citation: these proofs were prompted by the cubatic order parameter of Asencio,
Acevedo, Zuriguel and Maza, Phys. Rev. Lett. **119** (2017) 228002, whose summand is
`8·P₄` (`cubatic_summand_eq_legendre4`); `P₄(1/√2) = −13/32` is the value on a
cube-diagonal direction cosine. -/

/-- **The fourth Legendre polynomial** `P₄(x) = (35x⁴ − 30x² + 3)/8`. -/
noncomputable def legendre4 (x : ℝ) : ℝ := (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8

/-- **`P₄` solves the Legendre ODE** — the `α = 1/2`, `n = 4` member of the Gegenbauer
family, with eigenvalue `gegenbauerEigenvalue (1/2) 4 = 20`. -/
lemma legendre4_solves :
    IsGegenbauerSolution (1 / 2) 4 legendre4 (fun x => (35 * x ^ 3 - 15 * x) / 2) := by
  intro x
  refine ⟨?_, (105 * x ^ 2 - 15) / 2, ?_, ?_⟩
  · have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h := (((h4.const_mul 35).sub (h2.const_mul 30)).add_const 3).div_const 8
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [Pi.sub_apply]
    unfold legendre4; ring
  · have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
    have h := ((h3.const_mul 35).sub ((hasDerivAt_id x).const_mul 15)).div_const 2
    exact h.congr_deriv (by ring)
  · unfold gegenbauerEigenvalue legendre4
    push_cast
    ring

/-- **The eigenvalue is `20`** — `n(n+1)` at `n = 4`. -/
lemma legendre4_eigenvalue : gegenbauerEigenvalue (1 / 2) 4 = 20 := by
  unfold gegenbauerEigenvalue; norm_num

/-- `P₄(1) = 1`. -/
lemma legendre4_aligned : legendre4 1 = 1 := by
  unfold legendre4; norm_num

/-- The cubatic-order-parameter summand `(35c⁴ − 30c² + 3)/8` is `P₄`. -/
lemma cubatic_summand_eq_legendre4 (c : ℝ) :
    (35 * c ^ 4 - 30 * c ^ 2 + 3) / 8 = legendre4 c := rfl

/-- **The upper bound, with its equality case**: `P₄(x) ≤ 1` for `|x| ≤ 1`, because

  `1 − P₄(x) = 5(7x² + 1)(1 − x²)/8`,

an exact factorisation; equality holds precisely at `|x| = 1`. -/
lemma legendre4_le_one {x : ℝ} (hx : x ^ 2 ≤ 1) : legendre4 x ≤ 1 := by
  have hfac : 1 - legendre4 x = 5 * (7 * x ^ 2 + 1) * (1 - x ^ 2) / 8 := by
    unfold legendre4; ring
  nlinarith [sq_nonneg x, hfac]

/-- **The lower bound, with its equality case**: `P₄(x) ≥ −3/7` for every real `x`,
because

  `P₄(x) + 3/7 = 5(7x² − 3)²/56`,

again exact; the minimum `−3/7` is attained at `7x² = 3`. -/
lemma legendre4_ge (x : ℝ) : -(3 / 7 : ℝ) ≤ legendre4 x := by
  have hfac : legendre4 x + 3 / 7 = 5 * (7 * x ^ 2 - 3) ^ 2 / 56 := by
    unfold legendre4; ring
  nlinarith [sq_nonneg (7 * x ^ 2 - 3), hfac]

/-- `P₄(1/√2) = −13/32` — the value on a cube-diagonal direction cosine is
negative. -/
lemma legendre4_diagonal : legendre4 (1 / Real.sqrt 2) = -(13 / 32) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  unfold legendre4
  field_simp
  nlinarith [h2, sq_nonneg (Real.sqrt 2)]

/-- `∫₋₁¹ P₄ = 0` — orthogonality to `P₀`. -/
lemma legendre4_interval_integral_zero :
    ∫ x in (-1 : ℝ)..1, legendre4 x = 0 := by
  have h : ∀ x : ℝ, legendre4 x = (35 / 8) * x ^ 4 - (30 / 8) * x ^ 2 + 3 / 8 := by
    intro x; unfold legendre4; ring
  simp only [h]
  have i4 : IntervalIntegrable (fun x : ℝ => (35 / 8) * x ^ 4) MeasureTheory.volume (-1) 1 :=
    ((intervalIntegral.intervalIntegrable_pow 4).const_mul _)
  have i2 : IntervalIntegrable (fun x : ℝ => (30 / 8) * x ^ 2) MeasureTheory.volume (-1) 1 :=
    ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)
  have i0 : IntervalIntegrable (fun _ : ℝ => (3 / 8 : ℝ)) MeasureTheory.volume (-1) 1 :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add (i4.sub i2) i0,
    intervalIntegral.integral_sub i4 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/-! ### A bounded observable cannot advance logarithmically forever

If `φ(N) = φ₀ + a·log N` with `a > 0` stays below a ceiling, then
`N ≤ exp((φmax − φ₀)/a)`: a logarithmic advance in a bounded quantity holds only on a
finite window.  (The prompting instance is the same experiment's compaction law; where
that system saturates remains a geometric input, recorded as the graph caveat.) -/

/-- If `φ₀ + a·log N ≤ φmax` with `0 < a` and `0 < N`, then
`N ≤ exp((φmax − φ₀)/a)`. -/
theorem log_growth_range_bounded {φ₀ a φmax N : ℝ} (ha : 0 < a) (hN : 0 < N)
    (hbound : φ₀ + a * Real.log N ≤ φmax) :
    N ≤ Real.exp ((φmax - φ₀) / a) := by
  have hlog : Real.log N ≤ (φmax - φ₀) / a := by
    rw [le_div_iff₀ ha]
    linarith [hbound]
  calc N = Real.exp (Real.log N) := (Real.exp_log hN).symm
    _ ≤ Real.exp ((φmax - φ₀) / a) := Real.exp_le_exp.mpr hlog

/-- No positive-rate logarithmic advance stays below a ceiling for all `N`. -/
theorem log_growth_not_global {φ₀ a φmax : ℝ} (ha : 0 < a) :
    ¬ (∀ N : ℝ, 0 < N → φ₀ + a * Real.log N ≤ φmax) := by
  intro hall
  have hbig := log_growth_range_bounded (φ₀ := φ₀) (a := a) (φmax := φmax)
    (N := Real.exp ((φmax - φ₀) / a) + 1) ha (by positivity)
    (hall _ (by positivity))
  linarith [hbig]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre4_solves where
  formalizes @ "claim:the-cubatic-order-parameter-of-sheared-hard-cubes-is-the-fourth-legendre-member-of-the-gegenbauer-family-sharing-its-ode-and-eigenvalue",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre2_solves"

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre4_le_one where
  derives @ "claim:the-cubatic-order-parameter-reaches-one-exactly-under-perfect-alignment-by-the-factorisation-one-minus-p4-equals-five-times-seven-x-squared-plus-one-times-one-minus-x-squared-over-eight",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002"

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre4_ge where
  derives @ "claim:the-cubatic-order-parameter-is-bounded-below-by-minus-three-sevenths-attained-where-seven-x-squared-equals-three-so-no-configuration-drives-it-lower",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002"

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre4_diagonal where
  derives @ "claim:the-diagonally-aligned-cube-population-contributes-minus-thirteen-thirty-seconds-to-the-cubatic-order-parameter-so-competing-orientations-cancel-rather-than-add",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002"

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.legendre4_interval_integral_zero where
  derives @ "claim:the-disordered-value-of-the-cubatic-order-parameter-is-zero-by-orthogonality-of-the-legendre-family-not-by-a-subtracted-baseline",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002",
  caveat @ "claim:the-logarithmic-compaction-law-the-shear-versus-load-phase-boundary-and-the-spatial-correlation-decay-are-experimental-fits-and-are-not-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.log_growth_not_global where
  derives @ "claim:a-logarithmic-compaction-law-in-a-bounded-packing-fraction-holds-only-on-a-finite-window-of-drive-counts-ending-by-a-computable-bound",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:asencio-acevedo-zuriguel-maza-2017-experimental-study-of-ordering-of-hard-cubes-by-shearing-prl-119-228002",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.log_growth_range_bounded",
  caveat @ "claim:the-saturation-value-the-densest-boundary-compatible-packing-remains-a-geometric-input-and-the-shear-versus-load-boundary-as-a-contact-coefficient-is-a-similarity-of-form-only-neither-is-derived"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

end
