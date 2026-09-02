/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Fourier binding formulas for periodic Schrödinger operators

The load-bearing algebraic identity in Veliev's paper is obtained by projecting

`(-Δ + q) Ψ = Λ Ψ`

onto a free Bloch mode. In Fourier coefficients it has the form

`(Λ - E₀(γ+t)) b(γ) = ∑_η q(η) b(γ-η)`.

This file formalizes the exact finite-support convolution equation and the
coefficient recovery formula used in the nonresonant iterations. The
reciprocal-mode type is an arbitrary additive commutative group and may be
infinite; only the potential truncation is finite.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open scoped BigOperators

variable {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]

/-- Finite Fourier convolution of a potential coefficient family `q` with a
Bloch coefficient family `b`. -/
def potentialConvolution
    (support : Finset Γ) (q b : Γ → ℂ) (γ : Γ) : ℂ :=
  ∑ η ∈ support, q η * b (γ - η)

@[simp] theorem potentialConvolution_empty
    (q b : Γ → ℂ) (γ : Γ) :
    potentialConvolution ∅ q b γ = 0 := by
  simp [potentialConvolution]

/-- Linearity of potential convolution in the Bloch coefficients. -/
theorem potentialConvolution_add
    (support : Finset Γ) (q b₁ b₂ : Γ → ℂ) (γ : Γ) :
    potentialConvolution support q (b₁ + b₂) γ =
      potentialConvolution support q b₁ γ +
        potentialConvolution support q b₂ γ := by
  simp [potentialConvolution, mul_add, Finset.sum_add_distrib]

/-- Scalar linearity of potential convolution. -/
theorem potentialConvolution_smul
    (support : Finset Γ) (q b : Γ → ℂ) (c : ℂ) (γ : Γ) :
    potentialConvolution support q (c • b) γ =
      c * potentialConvolution support q b γ := by
  unfold potentialConvolution
  calc
    (∑ η ∈ support, q η * (c • b) (γ - η)) =
        ∑ η ∈ support, c * (q η * b (γ - η)) := by
      apply Finset.sum_congr rfl
      intro η hη
      simp [Pi.smul_apply]
      ring
    _ = c * ∑ η ∈ support, q η * b (γ - η) := by
      simp only [Finset.mul_sum]

/-- Fourier-space potential as a linear operator on coefficient families. -/
def potentialConvolutionLinear
    (support : Finset Γ) (q : Γ → ℂ) :
    (Γ → ℂ) →ₗ[ℂ] (Γ → ℂ) where
  toFun b := fun γ => potentialConvolution support q b γ
  map_add' b₁ b₂ := by
    funext γ
    exact potentialConvolution_add support q b₁ b₂ γ
  map_smul' c b := by
    funext γ
    simpa [Pi.smul_apply] using
      potentialConvolution_smul support q b c γ

/-- Abstract free energy assigned to each reciprocal mode. -/
abbrev ModeEnergy (Γ : Type*) := Γ → ℝ

/-- Exact binding equation at one reciprocal mode. -/
def BindingEquation
    (support : Finset Γ) (q b : Γ → ℂ)
    (energy : ModeEnergy Γ) (Λ : ℂ) (γ : Γ) : Prop :=
  (Λ - energy γ) * b γ = potentialConvolution support q b γ

/-- Binding equation for every reciprocal mode. -/
def SatisfiesBindingSystem
    (support : Finset Γ) (q b : Γ → ℂ)
    (energy : ModeEnergy Γ) (Λ : ℂ) : Prop :=
  ∀ γ, BindingEquation support q b energy Λ γ

/-- Away from a zero denominator, the binding equation determines the mode
coefficient exactly. -/
theorem coefficient_eq_convolution_div
    (support : Finset Γ) (q b : Γ → ℂ)
    (energy : ModeEnergy Γ) (Λ : ℂ) (γ : Γ)
    (hbind : BindingEquation support q b energy Λ γ)
    (hgap : Λ - energy γ ≠ 0) :
    b γ = potentialConvolution support q b γ /
      (Λ - energy γ) := by
  rw [eq_div_iff hgap]
  simpa [BindingEquation, mul_comm] using hbind

/-- The same coefficient formula at a shifted mode. This is the exact form
iterated in the paper. -/
theorem shifted_coefficient_eq
    (support : Finset Γ) (q b : Γ → ℂ)
    (energy : ModeEnergy Γ) (Λ : ℂ) (γ η : Γ)
    (hbind : SatisfiesBindingSystem support q b energy Λ)
    (hgap : Λ - energy (γ - η) ≠ 0) :
    b (γ - η) =
      potentialConvolution support q b (γ - η) /
        (Λ - energy (γ - η)) :=
  coefficient_eq_convolution_div support q b energy Λ (γ - η)
    (hbind (γ - η)) hgap

/-- Nonresonant denominator condition on a family of modes. -/
def HasDenominatorGap
    (energy : ModeEnergy Γ) (Λ : ℂ)
    (modes : Set Γ) (gap : ℝ) : Prop :=
  ∀ γ ∈ modes, gap ≤ ‖Λ - energy γ‖

/-- A strictly positive denominator gap excludes zero denominators. -/
theorem denominator_ne_zero_of_gap
    (energy : ModeEnergy Γ) (Λ : ℂ)
    (modes : Set Γ) {gap : ℝ} (hgap : 0 < gap)
    (hden : HasDenominatorGap energy Λ modes gap)
    {γ : Γ} (hγ : γ ∈ modes) :
    Λ - energy γ ≠ 0 := by
  intro hz
  have h := hden γ hγ
  rw [hz, norm_zero] at h
  linarith

/-- Norm estimate obtained directly from the binding equation and a positive
spectral denominator. -/
theorem norm_coefficient_le
    (support : Finset Γ) (q b : Γ → ℂ)
    (energy : ModeEnergy Γ) (Λ : ℂ) (γ : Γ)
    (hbind : BindingEquation support q b energy Λ γ)
    {gap : ℝ} (hgap : 0 < gap)
    (hden : gap ≤ ‖Λ - energy γ‖) :
    ‖b γ‖ ≤ ‖potentialConvolution support q b γ‖ / gap := by
  have hne : Λ - energy γ ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hden
    linarith
  rw [coefficient_eq_convolution_div support q b energy Λ γ hbind hne,
    norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    hgap hden

/-! ## Generic finite perturbation iteration -/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Iteration of a linear perturbation operator, defined without depending on
an endomorphism-power simplification theorem. -/
def linearIterate (T : M →ₗ[ℂ] M) : ℕ → M → M
  | 0, x => x
  | n + 1, x => T (linearIterate T n x)

@[simp] theorem linearIterate_zero
    (T : M →ₗ[ℂ] M) (x : M) :
    linearIterate T 0 x = x :=
  rfl

@[simp] theorem linearIterate_succ
    (T : M →ₗ[ℂ] M) (n : ℕ) (x : M) :
    linearIterate T (n + 1) x = T (linearIterate T n x) :=
  rfl

/-- Iteration preserves addition. -/
theorem linearIterate_add
    (T : M →ₗ[ℂ] M) (n : ℕ) (x y : M) :
    linearIterate T n (x + y) =
      linearIterate T n x + linearIterate T n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp [linearIterate, ih, map_add]

/-- Iterating after one application of `T` advances the iterate count. -/
theorem linearIterate_map
    (T : M →ₗ[ℂ] M) (n : ℕ) (x : M) :
    linearIterate T n (T x) = linearIterate T (n + 1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [linearIterate, ih]

/-- Finite geometric perturbation sum
`r + T r + ... + T^(n-1) r`. -/
def perturbationPartialSum
    (T : M →ₗ[ℂ] M) (r : M) : ℕ → M
  | 0 => 0
  | n + 1 => perturbationPartialSum T r n + linearIterate T n r

@[simp] theorem perturbationPartialSum_zero
    (T : M →ₗ[ℂ] M) (r : M) :
    perturbationPartialSum T r 0 = 0 :=
  rfl

@[simp] theorem perturbationPartialSum_succ
    (T : M →ₗ[ℂ] M) (r : M) (n : ℕ) :
    perturbationPartialSum T r (n + 1) =
      perturbationPartialSum T r n + linearIterate T n r :=
  rfl

/-- If `x = r + T x`, then after `n` substitutions it is the finite
perturbation sum plus the exact iterated remainder. -/
theorem fixedPoint_eq_partialSum_add_remainder
    (T : M →ₗ[ℂ] M) (r x : M)
    (hfixed : x = r + T x) :
    ∀ n, x = perturbationPartialSum T r n + linearIterate T n x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        x = perturbationPartialSum T r n + linearIterate T n x := ih
        _ = perturbationPartialSum T r n +
            linearIterate T n (r + T x) := by rw [← hfixed]
        _ = perturbationPartialSum T r n +
            (linearIterate T n r + linearIterate T n (T x)) := by
              rw [linearIterate_add]
        _ = perturbationPartialSum T r n +
            (linearIterate T n r + linearIterate T (n + 1) x) := by
              rw [linearIterate_map]
        _ = perturbationPartialSum T r (n + 1) +
            linearIterate T (n + 1) x := by
              simp [add_assoc]

/-- When the exact remainder vanishes, the finite perturbation expansion is
exact. -/
theorem fixedPoint_eq_partialSum_of_remainder_zero
    (T : M →ₗ[ℂ] M) (r x : M)
    (hfixed : x = r + T x) (n : ℕ)
    (hremainder : linearIterate T n x = 0) :
    x = perturbationPartialSum T r n := by
  rw [fixedPoint_eq_partialSum_add_remainder T r x hfixed n,
    hremainder, add_zero]

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
