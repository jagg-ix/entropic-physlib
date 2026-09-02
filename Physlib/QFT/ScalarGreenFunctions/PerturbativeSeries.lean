/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.DysonSchwinger
public import Mathlib.Analysis.Complex.Exponential

/-!
# Perturbative solutions of scalar Dyson--Schwinger equations

Rivers emphasizes that an underdetermined exact Dyson--Schwinger equation can
nevertheless determine a unique *formal perturbation series*.  This file makes
that distinction explicit.

Given the rearranged equation

`G = L⁻¹ e - g L⁻¹ U G`,

the coefficient sequence is fixed recursively by

`G⁽⁰⁾ = L⁻¹ e`, `G⁽ⁿ⁺¹⁾ = -L⁻¹ U G⁽ⁿ⁾`.

The construction and uniqueness theorem below require no convergence or
summability hypothesis.  Finite partial sums are separately defined, matching
the chapter's use of the Dyson--Wick series as a formal/asymptotic expansion.

The second part gives the zero-dimensional/static-ultralocal scalar hierarchy,
where the functional Dyson--Schwinger equation becomes a recurrence for a
sequence of moments.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators

section LinearRecursion

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Coefficients of the formal perturbative solution of
`G = L⁻¹e - g L⁻¹UG`. -/
def perturbativeCoefficient
    (Linv U : V →ₗ[𝕜] V) (e : V) : ℕ → V
  | 0 => Linv e
  | n + 1 => -Linv (U (perturbativeCoefficient Linv U e n))

@[simp] lemma perturbativeCoefficient_zero
    (Linv U : V →ₗ[𝕜] V) (e : V) :
    perturbativeCoefficient Linv U e 0 = Linv e := rfl

@[simp] lemma perturbativeCoefficient_succ
    (Linv U : V →ₗ[𝕜] V) (e : V) (n : ℕ) :
    perturbativeCoefficient Linv U e (n + 1) =
      -Linv (U (perturbativeCoefficient Linv U e n)) := rfl

/-- The coefficient recursion has a unique solution.  This is Rivers' point
that perturbative uniqueness is independent of convergence of the resulting
series. -/
theorem perturbativeCoefficient_unique
    (Linv U : V →ₗ[𝕜] V) (e : V) (c : ℕ → V)
    (h0 : c 0 = Linv e)
    (hs : ∀ n, c (n + 1) = -Linv (U (c n))) :
    c = perturbativeCoefficient Linv U e := by
  funext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      rw [hs n, perturbativeCoefficient_succ, ih]

/-- Existence and uniqueness of the formal coefficient sequence. -/
theorem exists_unique_perturbativeCoefficient
    (Linv U : V →ₗ[𝕜] V) (e : V) :
    ∃! c : ℕ → V,
      c 0 = Linv e ∧ ∀ n, c (n + 1) = -Linv (U (c n)) := by
  refine ⟨perturbativeCoefficient Linv U e, ?_, ?_⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · intro c hc
    exact perturbativeCoefficient_unique Linv U e c hc.1 hc.2

/-- Finite truncation `Σ_{n=0}^N gⁿ G⁽ⁿ⁾` of the formal perturbation series. -/
def perturbativePartialSum
    (Linv U : V →ₗ[𝕜] V) (e : V) (g : 𝕜) (N : ℕ) : V :=
  ∑ n ∈ Finset.range (N + 1),
    g ^ n • perturbativeCoefficient Linv U e n

lemma perturbativePartialSum_succ
    (Linv U : V →ₗ[𝕜] V) (e : V) (g : 𝕜) (N : ℕ) :
    perturbativePartialSum Linv U e g (N + 1) =
      perturbativePartialSum Linv U e g N +
        g ^ (N + 1) • perturbativeCoefficient Linv U e (N + 1) := by
  unfold perturbativePartialSum
  rw [Finset.sum_range_succ]

/-- At zero coupling every finite truncation reduces to the free coefficient. -/
@[simp] lemma perturbativePartialSum_zero_coupling
    (Linv U : V →ₗ[𝕜] V) (e : V) (N : ℕ) :
    perturbativePartialSum Linv U e 0 N = Linv e := by
  unfold perturbativePartialSum
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

end LinearRecursion

/-! ## Static-ultralocal and zero-dimensional scalar models -/

/-- Product of independent local generating functions, the finite-site form of
the static-ultralocal factorization in Eq. (1.45). -/
def ultralocalGeneratingFunctional
    {X : Type*} [Fintype X] (z : ℂ → ℂ) (J : X → ℂ) : ℂ :=
  ∏ x, z (J x)

@[simp] lemma ultralocalGeneratingFunctional_zero
    {X : Type*} [Fintype X] (z : ℂ → ℂ) :
    ultralocalGeneratingFunctional z (fun (_ : X) => (0 : ℂ)) = z 0 ^ Fintype.card X := by
  show (∏ _x : X, z 0) = z 0 ^ Fintype.card X
  rw [Finset.prod_const, Finset.card_univ]

/-- Zero-dimensional free scalar generating function, Eq. (1.92), in the
chapter's dimensionless convention. -/
def zeroDimensionalFreeGenerating (j : ℂ) : ℂ :=
  Complex.exp (-(j ^ 2) / 2)

@[simp] lemma zeroDimensionalFreeGenerating_zero :
    zeroDimensionalFreeGenerating 0 = 1 := by
  simp [zeroDimensionalFreeGenerating]

/-- Moment hierarchy for the zero-dimensional quartic scalar model.  The
recurrence is the coefficient form of the ordinary Dyson--Schwinger equation
obtained after functional truncation. -/
structure ZeroDimensionalQuarticDS where
  /-- Mass-square coefficient. -/
  massSq : ℂ
  /-- Quartic coupling. -/
  coupling : ℂ
  /-- Planck constant. -/
  hbar : ℂ
  /-- Moment sequence `Gₙ`. -/
  moment : ℕ → ℂ
  /-- The zero-dimensional Dyson--Schwinger recurrence. -/
  recurrence : ∀ n : ℕ,
    massSq * moment (n + 1) + (coupling / 6) * moment (n + 3) =
      if n = 0 then 0
      else -(Complex.I * hbar) * (n : ℂ) * moment (n - 1)

namespace ZeroDimensionalQuarticDS

/-- Zeroth moment equation. -/
lemma recurrence_zero (D : ZeroDimensionalQuarticDS) :
    D.massSq * D.moment 1 + (D.coupling / 6) * D.moment 3 = 0 := by
  simpa using D.recurrence 0

/-- First differentiated moment equation. -/
lemma recurrence_one (D : ZeroDimensionalQuarticDS) :
    D.massSq * D.moment 2 + (D.coupling / 6) * D.moment 4 =
      -(Complex.I * D.hbar) * D.moment 0 := by
  simpa using D.recurrence 1

/-- Second differentiated moment equation. -/
lemma recurrence_two (D : ZeroDimensionalQuarticDS) :
    D.massSq * D.moment 3 + (D.coupling / 6) * D.moment 5 =
      -(Complex.I * D.hbar) * 2 * D.moment 1 := by
  simpa using D.recurrence 2

/-- A `Z₂`-symmetric zero-dimensional hierarchy has vanishing odd moments. -/
def IsZ2Symmetric (D : ZeroDimensionalQuarticDS) : Prop :=
  ∀ n, D.moment (2 * n + 1) = 0

lemma IsZ2Symmetric.moment_one
    {D : ZeroDimensionalQuarticDS} (h : D.IsZ2Symmetric) :
    D.moment 1 = 0 := by
  simpa using h 0

lemma IsZ2Symmetric.moment_three
    {D : ZeroDimensionalQuarticDS} (h : D.IsZ2Symmetric) :
    D.moment 3 = 0 := by
  simpa using h 1

/-- In the `Z₂`-symmetric sector, the zeroth Dyson--Schwinger equation is
satisfied identically. -/
lemma recurrence_zero_of_z2
    (D : ZeroDimensionalQuarticDS) (h : D.IsZ2Symmetric) :
    D.massSq * D.moment 1 + (D.coupling / 6) * D.moment 3 = 0 := by
  rw [h.moment_one, h.moment_three]
  ring

end ZeroDimensionalQuarticDS

end Physlib.QFT.ScalarGreenFunctions

end
