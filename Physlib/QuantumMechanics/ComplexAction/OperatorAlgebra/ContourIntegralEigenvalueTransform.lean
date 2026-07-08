/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.IsEigenvector
public import Mathlib.Tactic

/-!
# Contour-integral quantum eigenvalue transformation

This file formalizes Lean-checkable kernels from Shan Jiang and Dong An,
*Contour-integral based quantum eigenvalue transformation: analysis and
applications*, arXiv:2601.11959v2 (2026).

The paper represents an eigenvalue transformation by Cauchy's integral formula
and then discretizes the contour into a finite linear combination of resolvents.
The analytic Cauchy theorem, quadrature error estimates, QSVT construction, and
big-O complexity accounting are not asserted here.  The formalized content is the
finite algebraic spine that those algorithms use:

* a shifted operator `zI - A` acts on an eigenvector by the scalar `z - λ`;
* a left inverse of `zI - A` therefore acts as the scalar resolvent
  `(z - λ)⁻¹` on that eigenvector;
* a finite LCU/quadrature sum of sampled resolvents acts as the corresponding
  finite scalar contour transform;
* the appendix-A scalar resolvent distance bound;
* the appendix-B dissipativity implication, in quadratic-form form;
* the appendix-C deterministic triangle step combining sampling and operator
  approximation errors.

The file is proof-complete and introduces no declaration-level assumptions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ContourIntegralEigenvalueTransform

/-! ## Finite sampled contour rules -/

/-- A finite discretized contour rule: nodes `z_k` and complex weights `c_k`. -/
structure FiniteContourRule (κ : Type*) where
  node : κ → ℂ
  weight : κ → ℂ

variable {κ H : Type*} [Fintype κ]

/--
The scalar finite contour transform associated to the sampled rule:
`Σ_k c_k (z_k - λ)⁻¹`.
-/
def FiniteContourRule.scalarTransform (q : FiniteContourRule κ) (lam : ℂ) : ℂ :=
  ∑ k : κ, q.weight k * (q.node k - lam)⁻¹

/--
The finite LCU operator assembled from sampled resolvents `R k`:
`Σ_k c_k • R_k`.
-/
def FiniteContourRule.sampledResolventLCU [AddCommMonoid H] [Module ℂ H]
    (q : FiniteContourRule κ) (R : κ → H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ∑ k : κ, q.weight k • R k

/--
If each sampled resolvent acts on `ψ` by the scalar `(z_k - λ)⁻¹`, then the
finite LCU acts by the finite scalar contour transform on `ψ`.
-/
theorem sampledResolventLCU_apply_eigenvector [AddCommMonoid H] [Module ℂ H]
    (q : FiniteContourRule κ) (R : κ → H →ₗ[ℂ] H) (ψ : H) (lam : ℂ)
    (hR : ∀ k : κ, R k ψ = (q.node k - lam)⁻¹ • ψ) :
    q.sampledResolventLCU R ψ = q.scalarTransform lam • ψ := by
  classical
  unfold FiniteContourRule.sampledResolventLCU FiniteContourRule.scalarTransform
  simp [hR, smul_smul, Finset.sum_smul]

/-! ## Resolvents from shifted eigenvalue equations -/

/-- The shifted operator `zI - A`. -/
def shiftedOperator [AddCommGroup H] [Module ℂ H] (A : H →ₗ[ℂ] H) (z : ℂ) : H →ₗ[ℂ] H :=
  z • LinearMap.id - A

/-- On an eigenvector of `A` with eigenvalue `λ`, `zI - A` acts by `z - λ`. -/
theorem shiftedOperator_apply_eigenvector [AddCommGroup H] [Module ℂ H]
    (A : H →ₗ[ℂ] H) (z : ℂ) {ψ : H} {lam : ℂ}
    (hEig : A ψ = lam • ψ) :
    shiftedOperator A z ψ = (z - lam) • ψ := by
  simp [shiftedOperator, hEig, sub_smul]

/--
If `R` is a left inverse of `zI - A`, then on an eigenvector it is the scalar
resolvent `(z - λ)⁻¹`.
-/
theorem leftInverseResolvent_apply_eigenvector [AddCommGroup H] [Module ℂ H]
    (A R : H →ₗ[ℂ] H) (z : ℂ) {ψ : H} {lam : ℂ}
    (hEig : A ψ = lam • ψ)
    (hLeft : R.comp (shiftedOperator A z) = LinearMap.id)
    (hz : z ≠ lam) :
    R ψ = (z - lam)⁻¹ • ψ := by
  have hleft_apply : R (shiftedOperator A z ψ) = ψ := by
    calc
      R (shiftedOperator A z ψ) = (R.comp (shiftedOperator A z)) ψ := rfl
      _ = (LinearMap.id : H →ₗ[ℂ] H) ψ := by rw [hLeft]
      _ = ψ := rfl
  rw [shiftedOperator_apply_eigenvector A z hEig] at hleft_apply
  have hscalar : (z - lam) • R ψ = ψ := by
    simpa using hleft_apply
  have hnonzero : z - lam ≠ 0 := sub_ne_zero.mpr hz
  calc
    R ψ = (1 : ℂ) • R ψ := by simp
    _ = ((z - lam)⁻¹ * (z - lam)) • R ψ := by
      rw [inv_mul_cancel₀ hnonzero]
    _ = (z - lam)⁻¹ • ((z - lam) • R ψ) := by
      rw [smul_smul]
    _ = (z - lam)⁻¹ • ψ := by
      rw [hscalar]

/--
The finite contour LCU acts diagonally on every eigenvector when every sampled
resolvent is a left inverse of its shifted operator.
-/
theorem finite_contour_lcu_eigenvector [AddCommGroup H] [Module ℂ H]
    (q : FiniteContourRule κ) (A : H →ₗ[ℂ] H) (R : κ → H →ₗ[ℂ] H)
    {ψ : H} {lam : ℂ}
    (hEig : A ψ = lam • ψ)
    (hLeft : ∀ k : κ, (R k).comp (shiftedOperator A (q.node k)) = LinearMap.id)
    (hAvoid : ∀ k : κ, q.node k ≠ lam) :
    q.sampledResolventLCU R ψ = q.scalarTransform lam • ψ := by
  exact sampledResolventLCU_apply_eigenvector q R ψ lam fun k =>
    leftInverseResolvent_apply_eigenvector A (R k) (q.node k) hEig (hLeft k) (hAvoid k)

/--
If the scalar finite contour rule realizes a target eigenvalue function at `λ`,
then the sampled LCU realizes the corresponding eigenvector transformation.
-/
theorem finite_contour_lcu_exact_eigenvalue_transform [AddCommGroup H] [Module ℂ H]
    (q : FiniteContourRule κ) (A : H →ₗ[ℂ] H) (R : κ → H →ₗ[ℂ] H)
    (f : ℂ → ℂ) {ψ : H} {lam : ℂ}
    (hEig : A ψ = lam • ψ)
    (hLeft : ∀ k : κ, (R k).comp (shiftedOperator A (q.node k)) = LinearMap.id)
    (hAvoid : ∀ k : κ, q.node k ≠ lam)
    (hScalar : q.scalarTransform lam = f lam) :
    q.sampledResolventLCU R ψ = f lam • ψ := by
  rw [finite_contour_lcu_eigenvector q A R hEig hLeft hAvoid, hScalar]

/-! ## Appendix A scalar resolvent bound -/

/--
If the contour node is at distance at least `a > 0` from an eigenvalue `λ`, then
the scalar resolvent has norm at most `a⁻¹`.
-/
theorem scalar_resolvent_norm_le_inv_distance {z lam : ℂ} {a : ℝ}
    (ha : 0 < a) (hdist : a ≤ ‖z - lam‖) :
    ‖(z - lam)⁻¹‖ ≤ a⁻¹ := by
  rw [norm_inv]
  have hnorm : 0 < ‖z - lam‖ := lt_of_lt_of_le ha hdist
  exact (inv_le_inv₀ hnorm ha).2 hdist

/--
The appendix-A diagonalizable estimate, reduced to its scalar distance input:
if `κS` bounds the condition number and `a` is the contour/eigenvalue distance,
then `κS * ‖(z - λ)⁻¹‖ ≤ κS / a`.
-/
theorem condition_number_scalar_resolvent_bound {z lam : ℂ} {a κS : ℝ}
    (ha : 0 < a) (hκ : 0 ≤ κS) (hdist : a ≤ ‖z - lam‖) :
    κS * ‖(z - lam)⁻¹‖ ≤ κS / a := by
  calc
    κS * ‖(z - lam)⁻¹‖ ≤ κS * a⁻¹ :=
      mul_le_mul_of_nonneg_left (scalar_resolvent_norm_le_inv_distance ha hdist) hκ
    _ = κS / a := by rw [div_eq_mul_inv]

/-! ## Appendix B dissipativity kernel -/

/--
Quadratic-form dissipativity implies every eigenvalue visible through an
eigenvector has nonpositive real part.  This is the Lean-checkable core of
Appendix B, Lemma 11 (`A + A† ⪯ 0 ⇒ Re λ ≤ 0`).
-/
theorem dissipative_eigenvalue_re_nonpos
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) {ψ : H} {lam : ℂ}
    (hψ : ψ ≠ 0)
    (hEig : A ψ = lam • ψ)
    (hDiss : ∀ v : H, (inner ℂ v (A v)).re ≤ 0) :
    lam.re ≤ 0 := by
  have hq := hDiss ψ
  rw [hEig, inner_smul_right] at hq
  have hquad : lam.re * ‖ψ‖ ^ 2 ≤ 0 := by
    have hinner : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      exact (Complex.ofReal_pow ‖ψ‖ 2).symm
    have hreal : (lam * inner ℂ ψ ψ).re = lam.re * ‖ψ‖ ^ 2 := by
      calc
        (lam * inner ℂ ψ ψ).re = (lam * ((‖ψ‖ ^ 2 : ℝ) : ℂ)).re := by
          rw [hinner]
        _ = lam.re * ‖ψ‖ ^ 2 := Complex.re_mul_ofReal lam (‖ψ‖ ^ 2)
    exact hreal ▸ hq
  have hnorm : 0 < ‖ψ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hψ)
  nlinarith

/-! ## Appendix C deterministic single-ancilla LCU error steps -/

/--
The deterministic triangle step used after sampling and block-encoding
approximation: if the sampling error and approximation error are each at most
`ε/2`, then the final observable estimate is within `ε`.
-/
theorem single_ancilla_error_composition {μ sampled exact ε : ℝ}
    (hsample : |μ - sampled| ≤ ε / 2)
    (happrox : |sampled - exact| ≤ ε / 2) :
    |μ - exact| ≤ ε := by
  calc
    |μ - exact| = |(μ - sampled) + (sampled - exact)| := by ring_nf
    _ ≤ |μ - sampled| + |sampled - exact| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hsample happrox
    _ = ε := by ring

/--
The algebraic half-error budget from Appendix C: the paper's bound
`3‖O‖‖P‖ξ ≤ ε/2` follows from
`ξ ≤ ε / (6‖O‖‖P‖)` when the norm factors are positive.
-/
theorem lcu_operator_approx_error_half {O P ξ ε : ℝ}
    (hO : 0 < O) (hP : 0 < P)
    (hbudget : ξ ≤ ε / (6 * O * P)) :
    3 * O * P * ξ ≤ ε / 2 := by
  have hden : 0 < 6 * O * P := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 3 * O * P by positivity)
  calc
    3 * O * P * ξ ≤ 3 * O * P * (ε / (6 * O * P)) := by
      simpa [mul_assoc] using hmul
    _ = ε / 2 := by
      field_simp [ne_of_gt hO, ne_of_gt hP]
      ring

/-! ## Existing contour bridge compatibility -/

/--
On the real contour of the existing Nagao-Kozak bridge, the sampled contour
picture is compatible with the reversible real-axis fiber.
-/
theorem real_contour_reversible_with_finite_rule
    (q : FiniteContourRule κ) (ξ : ℝ) (hξ : 0 < ξ) (ω : ℝ) (lam : ℂ) :
    0 ≤ EntropicTime.NagaoKozakContourEntropicTime.lorentzianDispersion 0 ω
      ∧ EntropicTime.NagaoKozakContourEntropicTime.lorentzianDispersion 0 (-ω)
          = EntropicTime.NagaoKozakContourEntropicTime.lorentzianDispersion 0 ω
      ∧ Bogoliubov.EntropicTime.bogoliubovEntropicTime ξ 0 = 0
      ∧ q.scalarTransform lam = ∑ k : κ, q.weight k * (q.node k - lam)⁻¹ := by
  exact
    ⟨EntropicTime.NagaoKozakContourEntropicTime.lorentzianDispersion_real_nonneg ω,
      EntropicTime.NagaoKozakContourEntropicTime.lorentzianDispersion_fnEven 0 ω,
      Bogoliubov.EntropicTime.bogoliubov_entropicTime_normal_zero ξ hξ,
      rfl⟩

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ContourIntegralEigenvalueTransform

end
