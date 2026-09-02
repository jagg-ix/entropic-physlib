/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.EuclideanPropagator
public import Physlib.QFT.PathIntegral.FeynmanKac
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Entropically damped heat and Stokes semigroups

This module upgrades the scalar kernels in `EuclideanPropagator` from pointwise
exponential identities to a genuine real `C₀` contraction-semigroup statement.
For the decay rate `a = m² + λ`, the operators

`T(t)x = exp(-a t) x`

form a strongly continuous contraction semigroup on `ℝ` when `m², λ ≥ 0`.
Their infinitesimal generator is multiplication by `-a`, and their Laplace
resolvent is

`∫₀∞ exp(-βt) T(t) dt = (β + m² + λ)⁻¹`.

At the unit scalar this is exactly the existing
`euclidean_propagator β m² λ`.  Specializing `m² = ν k²` supplies the same
result for each Fourier mode of the entropically damped Stokes flow.

The formalization is deliberately modewise.  It does not assert construction
of the full heat or Navier--Stokes PDE semigroup on a function space.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Filter Set

/-! ## A. A minimal real `C₀` contraction-semigroup carrier -/

/-- A strongly continuous contraction semigroup of bounded real-linear
operators on a real normed space. -/
structure RealC0ContractionSemigroup
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] where
  /-- The bounded linear evolution operator at time `t`. -/
  operator : ℝ → X →L[ℝ] X
  /-- The time-zero operator is the identity. -/
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ X
  /-- Evolution composes for non-negative times. -/
  operator_add : ∀ s t, 0 ≤ s → 0 ≤ t →
    operator (s + t) = (operator s).comp (operator t)
  /-- Every orbit is continuous on non-negative time. -/
  strong_continuous : ∀ x, ContinuousOn (fun t => operator t x) (Ici 0)
  /-- Every non-negative-time operator is contractive in operator norm. -/
  contraction : ∀ t, 0 ≤ t → ‖operator t‖ ≤ 1

namespace RealC0ContractionSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A bounded operator is the infinitesimal generator of `S` when every
right-hand difference quotient converges to its action. -/
def HasInfinitesimalGenerator (S : RealC0ContractionSemigroup X)
    (A : X →L[ℝ] X) : Prop :=
  ∀ x, Tendsto
    (fun t => t⁻¹ • (S.operator t x - x))
    (nhdsWithin 0 (Ioi 0)) (nhds (A x))

end RealC0ContractionSemigroup

/-! ## B. The entropically damped heat semigroup -/

/-- The scalar damped-heat evolution operator
`T(t)x = exp(-(m² + λ)t) x`. -/
def dampedHeatOperator (m_sq lam t : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ (damped_heat_propagator t m_sq lam)

@[simp]
lemma dampedHeatOperator_apply (m_sq lam t x : ℝ) :
    dampedHeatOperator m_sq lam t x =
      damped_heat_propagator t m_sq lam * x := by
  rfl

@[simp]
lemma dampedHeatOperator_zero (m_sq lam : ℝ) :
    dampedHeatOperator m_sq lam 0 = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  simp [dampedHeatOperator, damped_heat_propagator]

/-- The damped-heat operators compose according to addition of
non-negative times. -/
lemma dampedHeatOperator_add (m_sq lam s t : ℝ) :
    dampedHeatOperator m_sq lam (s + t) =
      (dampedHeatOperator m_sq lam s).comp
        (dampedHeatOperator m_sq lam t) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [dampedHeatOperator_apply, ContinuousLinearMap.comp_apply]
  unfold damped_heat_propagator
  rw [show -(m_sq + lam) * (s + t) =
      (-(m_sq + lam) * s) + (-(m_sq + lam) * t) by ring, Real.exp_add]
  ring

/-- Every scalar orbit of the damped-heat operators is continuous. -/
lemma dampedHeatOperator_continuous (m_sq lam x : ℝ) :
    Continuous (fun t => dampedHeatOperator m_sq lam t x) := by
  unfold dampedHeatOperator damped_heat_propagator
  fun_prop

/-- Under non-negative mass-square and damping, each non-negative-time
damped-heat operator has norm at most one. -/
lemma dampedHeatOperator_norm_le_one
    (m_sq lam t : ℝ) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    ‖dampedHeatOperator m_sq lam t‖ ≤ 1 := by
  rw [dampedHeatOperator, ContinuousLinearMap.opNorm_lsmul_apply]
  simpa [Real.norm_eq_abs, abs_of_pos (damped_heat_propagator_pos t m_sq lam)] using
    damped_heat_propagator_le_one t m_sq lam ht hm hl

/-- The entropically damped scalar heat flow is a real `C₀` contraction
semigroup when `m², λ ≥ 0`. -/
def dampedHeatC0ContractionSemigroup
    (m_sq lam : ℝ) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    RealC0ContractionSemigroup ℝ where
  operator := dampedHeatOperator m_sq lam
  operator_zero := dampedHeatOperator_zero m_sq lam
  operator_add := fun s t _ _ => dampedHeatOperator_add m_sq lam s t
  strong_continuous := fun x =>
    (dampedHeatOperator_continuous m_sq lam x).continuousOn
  contraction := fun t ht => dampedHeatOperator_norm_le_one m_sq lam t hm hl ht

/-! ## C. Infinitesimal generator -/

/-- The bounded scalar generator `A x = -(m² + λ)x` of the damped heat
semigroup. -/
def dampedHeatGenerator (m_sq lam : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ (-(m_sq + lam))

@[simp]
lemma dampedHeatGenerator_apply (m_sq lam x : ℝ) :
    dampedHeatGenerator m_sq lam x = -(m_sq + lam) * x := by
  rfl

/-- The generator of the damped-heat `C₀` semigroup is multiplication by
`-(m² + λ)`, obtained as the right derivative at time zero. -/
lemma dampedHeat_hasInfinitesimalGenerator
    (m_sq lam : ℝ) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    (dampedHeatC0ContractionSemigroup m_sq lam hm hl).HasInfinitesimalGenerator
      (dampedHeatGenerator m_sq lam) := by
  intro x
  have hderiv :
      HasDerivAt
        (fun t => dampedHeatOperator m_sq lam t x)
        (-(m_sq + lam) * x) 0 := by
    simpa [dampedHeatOperator, damped_heat_propagator] using
      ((damping_satisfies_decay_ODE (m_sq + lam) 0).mul_const x)
  change Tendsto
    (fun t => t⁻¹ * (damped_heat_propagator t m_sq lam * x - x))
    (nhdsWithin 0 (Ioi 0)) (nhds (-(m_sq + lam) * x))
  simpa [dampedHeatOperator, damped_heat_propagator] using
    hderiv.tendsto_slope_zero_right

/-! ## D. Laplace resolvent and Euclidean propagator -/

/-- The scalar Laplace resolvent of the damped-heat semigroup, defined by
the Hille--Yosida integral formula
`R(β)x = ∫₀∞ exp(-βt) T(t)x dt`. -/
noncomputable def dampedHeatLaplaceResolvent
    (beta m_sq lam : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.lsmul ℝ ℝ
    (∫ t in Ioi 0,
      Real.exp (-beta * t) * damped_heat_propagator t m_sq lam)

/-- The scalar coefficient in the damped-heat Laplace resolvent is
`1 / (β + m² + λ)`. -/
lemma dampedHeat_laplaceIntegral
    (beta m_sq lam : ℝ) (hbeta : 0 < beta)
    (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    (∫ t in Ioi 0,
      Real.exp (-beta * t) * damped_heat_propagator t m_sq lam) =
      1 / (beta + m_sq + lam) := by
  have hsum : 0 < beta + m_sq + lam := by linarith
  calc
    (∫ t in Ioi 0,
        Real.exp (-beta * t) * damped_heat_propagator t m_sq lam)
        = ∫ t in Ioi 0, Real.exp (-(beta + m_sq + lam) * t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            unfold damped_heat_propagator
            rw [← Real.exp_add]
            congr 1
            ring
    _ = -Real.exp (-(beta + m_sq + lam) * 0) / (-(beta + m_sq + lam)) :=
      integral_exp_mul_Ioi (by linarith) 0
    _ = 1 / (beta + m_sq + lam) := by
      rw [mul_zero, Real.exp_zero]
      field_simp

/-- The Laplace resolvent of the damped-heat semigroup is exactly scalar
multiplication by the existing Euclidean propagator. -/
lemma dampedHeatLaplaceResolvent_eq_euclideanPropagator
    (beta m_sq lam : ℝ) (hbeta : 0 < beta)
    (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    dampedHeatLaplaceResolvent beta m_sq lam =
      ContinuousLinearMap.lsmul ℝ ℝ
        (euclidean_propagator beta m_sq lam) := by
  apply ContinuousLinearMap.ext
  intro x
  change
    (∫ t in Ioi 0,
      Real.exp (-beta * t) * damped_heat_propagator t m_sq lam) * x =
      euclidean_propagator beta m_sq lam * x
  rw [dampedHeat_laplaceIntegral beta m_sq lam hbeta hm hl]
  rfl

/-- Evaluating the Hille--Yosida Laplace resolvent at `1` recovers the
Euclidean propagator denominator exactly. -/
lemma dampedHeatLaplaceResolvent_one_eq_euclideanPropagator
    (beta m_sq lam : ℝ) (hbeta : 0 < beta)
    (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    dampedHeatLaplaceResolvent beta m_sq lam 1 =
      euclidean_propagator beta m_sq lam := by
  rw [dampedHeatLaplaceResolvent_eq_euclideanPropagator
    beta m_sq lam hbeta hm hl]
  simp

/-! ## E. Entropically damped Stokes modes -/

/-- The `C₀` contraction semigroup of one Stokes Fourier mode with rate
`ν k² + λ`. -/
def stokesModeC0ContractionSemigroup
    (nu k_sq lam : ℝ) (hnu : 0 ≤ nu) (hk : 0 ≤ k_sq) (hl : 0 ≤ lam) :
    RealC0ContractionSemigroup ℝ :=
  dampedHeatC0ContractionSemigroup (nu * k_sq) lam (mul_nonneg hnu hk) hl

/-- The infinitesimal generator of one entropically damped Stokes mode is
multiplication by `-(ν k² + λ)`. -/
lemma stokesMode_hasInfinitesimalGenerator
    (nu k_sq lam : ℝ) (hnu : 0 ≤ nu) (hk : 0 ≤ k_sq) (hl : 0 ≤ lam) :
    (stokesModeC0ContractionSemigroup nu k_sq lam hnu hk hl).HasInfinitesimalGenerator
      (dampedHeatGenerator (nu * k_sq) lam) :=
  dampedHeat_hasInfinitesimalGenerator
    (nu * k_sq) lam (mul_nonneg hnu hk) hl

/-- The Hille--Yosida Laplace resolvent of one entropically damped Stokes
mode is the Euclidean propagator with `m² = ν k²`. -/
lemma stokesModeLaplaceResolvent_one_eq_euclideanPropagator
    (beta nu k_sq lam : ℝ) (hbeta : 0 < beta)
    (hnu : 0 ≤ nu) (hk : 0 ≤ k_sq) (hl : 0 ≤ lam) :
    dampedHeatLaplaceResolvent beta (nu * k_sq) lam 1 =
      euclidean_propagator beta (nu * k_sq) lam :=
  dampedHeatLaplaceResolvent_one_eq_euclideanPropagator
    beta (nu * k_sq) lam hbeta (mul_nonneg hnu hk) hl

end Physlib.QFT.PathIntegral

end
