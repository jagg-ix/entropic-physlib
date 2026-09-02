/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# The continuum circle Dirac spectrum and its heat/zeta asymptotics

This file replaces the finite spectral-action analogy by an actual infinite-dimensional Fourier
model.  `circleFourierL2` is the Haar `L²` space of the additive circle, unitarily represented by
`ℓ²(ℤ,ℂ)`.  On the maximal weighted domain, `circleDirac` multiplies Fourier coefficient `n`
by the real eigenvalue `n`.  Its self-adjointness is proved by computing the adjoint domain, rather
than assumed as a certificate.

The heat trace is the convergent integer Gaussian theta series.  Poisson summation gives its exact
modular identity and Jacobi-theta decay supplies the continuum Seeley--DeWitt leading coefficient.
The dimension zeta function is the meromorphic continuation `2 ζ(s)` and has residue `2` at its
dimension-spectrum pole `s = 1`.

## Honest boundary

This module does **not** call a finite signed eigenvalue count the APS theorem.  It supplies a
continuum Fredholm computation and the closed nonnegative spectral boundary space for the circle
operator.  The arbitrary-manifold APS formula still requires the geometric Sobolev trace theorem,
elliptic boundary regularity, and characteristic-form transgression; these are subsequent global
steps, not substitutes for the continuum results proved here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry

open scoped ENNReal lp
open Complex Filter Topology LinearPMap

/-- Square-summable coefficient space used by a Hilbert basis. -/
abbrev L2Sequence (index : Type*) := ℓ²(index, ℂ)

/-- The maximal domain of multiplication by a real eigenvalue family. -/
def diagonalDomain {index : Type*} (eigenvalue : index → ℝ) :
    Submodule ℂ (L2Sequence index) where
  carrier := {x | Memℓp (fun i => (eigenvalue i : ℂ) * x i) 2}
  zero_mem' := by
    change Memℓp (fun i => (eigenvalue i : ℂ) * (0 : L2Sequence index) i) 2
    rw [show (fun i => (eigenvalue i : ℂ) * (0 : L2Sequence index) i) =
        (fun _ : index => (0 : ℂ)) by funext i; simp]
    exact zero_mem_ℓp'
  add_mem' := by
    intro x y hx hy
    have h := hx.add hy
    change Memℓp (fun i => (eigenvalue i : ℂ) * (x + y : L2Sequence index) i) 2
    rw [show (fun i => (eigenvalue i : ℂ) * (x + y : L2Sequence index) i) =
        (fun i => (eigenvalue i : ℂ) * x i) +
          (fun i => (eigenvalue i : ℂ) * y i) by
      funext i
      simp [mul_add]]
    exact h
  smul_mem' := by
    intro c x hx
    have h := hx.const_smul c
    change Memℓp (fun i => (eigenvalue i : ℂ) * (c • x : L2Sequence index) i) 2
    rw [show (fun i => (eigenvalue i : ℂ) * (c • x : L2Sequence index) i) =
        c • (fun i => (eigenvalue i : ℂ) * x i) by
      funext i
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring]
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- Maximal real diagonal operator on a genuine infinite Hilbert sequence space. -/
def diagonalOperator {index : Type*} (eigenvalue : index → ℝ) :
    L2Sequence index →ₗ.[ℂ] L2Sequence index where
  domain := diagonalDomain eigenvalue
  toFun :=
    { toFun := fun x => ⟨fun i => (eigenvalue i : ℂ) * x.1 i, x.prop⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change (eigenvalue i : ℂ) * (x.1 + y.1) i = _
        simp [mul_add]
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change (eigenvalue i : ℂ) * (c • x.1) i = _
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        change (eigenvalue i : ℂ) * (c * x.1 i) =
          c * ((eigenvalue i : ℂ) * x.1 i)
        ring }

@[simp] theorem diagonalOperator_apply {index : Type*} (eigenvalue : index → ℝ)
    (x : (diagonalOperator eigenvalue).domain) (i : index) :
    diagonalOperator eigenvalue x i = (eigenvalue i : ℂ) * x.1 i := rfl

/-- The canonical Hilbert basis of `ℓ²(index,ℂ)`. -/
def sequenceHilbertBasis (index : Type*) : HilbertBasis index ℂ (L2Sequence index) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem sequenceHilbertBasis_apply {index : Type*} [DecidableEq index] (i : index) :
    sequenceHilbertBasis index i = lp.single 2 i (1 : ℂ) := by
  apply (sequenceHilbertBasis index).repr.injective
  rw [(sequenceHilbertBasis index).repr_self]
  rfl

theorem sequenceHilbertBasis_mem_domain {index : Type*} [DecidableEq index]
    (eigenvalue : index → ℝ) (i : index) :
    sequenceHilbertBasis index i ∈ (diagonalOperator eigenvalue).domain := by
  change Memℓp (fun j => (eigenvalue j : ℂ) * sequenceHilbertBasis index i j) 2
  have h : (fun j => (eigenvalue j : ℂ) * sequenceHilbertBasis index i j) =
      (lp.single 2 i (eigenvalue i : ℂ) : L2Sequence index) := by
    funext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [lp.single_apply, hij]
  rw [h]
  exact lp.memℓp _

/-- Finite Fourier combinations make the maximal diagonal domain dense. -/
theorem diagonalOperator_hasDenseDomain {index : Type*} [DecidableEq index]
    (eigenvalue : index → ℝ) : (diagonalOperator eigenvalue).HasDenseDomain := by
  change Dense ((diagonalOperator eigenvalue).domain : Set (L2Sequence index))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply le_antisymm le_top
  rw [← (sequenceHilbertBasis index).dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact sequenceHilbertBasis_mem_domain eigenvalue i

theorem diagonalOperator_isSymmetric {index : Type*} (eigenvalue : index → ℝ) :
    (diagonalOperator eigenvalue).IsSymmetric := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  change inner ℂ ((eigenvalue i : ℂ) * x.1 i) (y.1 i) =
    inner ℂ (x.1 i) ((eigenvalue i : ℂ) * y.1 i)
  simp [mul_assoc, mul_left_comm]

/-- Each standard basis vector is an eigenvector of the maximal diagonal operator. -/
theorem diagonalOperator_basis {index : Type*} [DecidableEq index]
    (eigenvalue : index → ℝ) (i : index) :
    diagonalOperator eigenvalue
        ⟨sequenceHilbertBasis index i, sequenceHilbertBasis_mem_domain eigenvalue i⟩ =
      (eigenvalue i : ℂ) • sequenceHilbertBasis index i := by
  apply lp.ext
  funext j
  rw [diagonalOperator_apply]
  change (eigenvalue j : ℂ) * (sequenceHilbertBasis index i) j =
    ((eigenvalue i : ℂ) • sequenceHilbertBasis index i) j
  rw [sequenceHilbertBasis_apply]
  by_cases hij : i = j
  · subst j
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
      Pi.single_eq_same, mul_one]
  · have hji : j ≠ i := Ne.symm hij
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
      Pi.single_eq_of_ne hji, mul_zero]

/-- A maximal real diagonal operator is self-adjoint.  The reverse adjoint-domain inclusion is
proved by testing the formal-adjoint identity on every Hilbert basis vector. -/
theorem diagonalOperator_isSelfAdjoint {index : Type*} [DecidableEq index]
    (eigenvalue : index → ℝ) : IsSelfAdjoint (diagonalOperator eigenvalue) := by
  let D := diagonalOperator eigenvalue
  have hDense : D.HasDenseDomain := diagonalOperator_hasDenseDomain eigenvalue
  have hSymm : D.IsSymmetric := diagonalOperator_isSymmetric eigenvalue
  apply (hSymm.isSelfAdjoint_iff hDense).2
  apply le_antisymm
  · intro y hy
    let ya : D.adjoint.domain := ⟨y, hy⟩
    let w : L2Sequence index := D.adjoint ya
    have hcoord : ∀ i, w i = (eigenvalue i : ℂ) * y i := by
      intro i
      let ei : D.domain :=
        ⟨sequenceHilbertBasis index i, sequenceHilbertBasis_mem_domain eigenvalue i⟩
      have hei : diagonalOperator eigenvalue ei =
          (eigenvalue i : ℂ) • sequenceHilbertBasis index i := by
        apply lp.ext
        funext j
        rw [diagonalOperator_apply]
        change (eigenvalue j : ℂ) * (sequenceHilbertBasis index i) j =
          ((eigenvalue i : ℂ) • sequenceHilbertBasis index i) j
        rw [sequenceHilbertBasis_apply]
        by_cases hij : i = j
        · subst j
          simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
            Pi.single_eq_same, mul_one]
        · have hji : j ≠ i := Ne.symm hij
          simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
            Pi.single_eq_of_ne hji, mul_zero]
      have h := adjoint_isFormalAdjoint hDense ya ei
      change inner ℂ w (sequenceHilbertBasis index i) =
        inner ℂ y (diagonalOperator eigenvalue ei) at h
      rw [hei, inner_smul_right, sequenceHilbertBasis_apply,
        lp.inner_single_right, lp.inner_single_right] at h
      have hc := congrArg star h
      simpa [w, mul_assoc, mul_comm] using hc
    change Memℓp (fun i => (eigenvalue i : ℂ) * y i) 2
    rw [← funext hcoord]
    exact lp.memℓp w
  · exact (hSymm.le_adjoint hDense).1

/-! ## The geometric circle model -/

/-- The genuine Haar `L²` Hilbert space of the additive circle. -/
abbrev CircleFourierL2 :=
  MeasureTheory.Lp ℂ 2 (@AddCircle.haarAddCircle 1 (by infer_instance))

/-- Fourier transform identifying Haar `L²(S¹)` with `ℓ²(ℤ,ℂ)`. -/
def circleFourierTransform : CircleFourierL2 ≃ₗᵢ[ℂ] L2Sequence ℤ :=
  (@fourierBasis 1 (by infer_instance)).repr

/-- The circle Dirac operator in its Fourier representation, with maximal domain
`{a ∈ ℓ² | (n a_n) ∈ ℓ²}`. -/
def circleDirac : L2Sequence ℤ →ₗ.[ℂ] L2Sequence ℤ :=
  diagonalOperator fun n : ℤ => n

theorem circleDirac_isSelfAdjoint : IsSelfAdjoint circleDirac :=
  diagonalOperator_isSelfAdjoint fun n : ℤ => n

theorem circleDirac_mode (n : ℤ) :
    circleDirac ⟨sequenceHilbertBasis ℤ n,
      sequenceHilbertBasis_mem_domain (fun k : ℤ => (k : ℝ)) n⟩ =
      (n : ℂ) • sequenceHilbertBasis ℤ n :=
  diagonalOperator_basis (fun k : ℤ => (k : ℝ)) n

/-! ## The closed-unbounded Fredholm realization -/

/-- A closed Fredholm partial linear operator has closed range and finite-dimensional kernel and
cokernel.  Its index is the existing algebraic `LinearMap.index` of its domain map. -/
def ClosedFredholm {H H' : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (T : H →ₗ.[ℂ] H') : Prop :=
  T.IsClosed ∧ IsClosed (T.toFun.range : Set H') ∧
    Module.Finite ℂ T.toFun.ker ∧ Module.Finite ℂ (H' ⧸ T.toFun.range)

/-- Continuous extraction of the zero Fourier coefficient. -/
def circleZeroMode : L2Sequence ℤ →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0

lemma norm_inverse_integer_le_one (n : ℤ) (hn : n ≠ 0) :
    ‖((n : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_intCast, inv_le_one₀]
  exact_mod_cast abs_pos.mpr hn
  exact_mod_cast Int.one_le_abs hn

/-- Division by the Fourier index away from the zero mode. -/
def divideCircleFourierByIndex (y : L2Sequence ℤ) : L2Sequence ℤ := by
  refine ⟨fun n => if n = 0 then 0 else (n : ℂ)⁻¹ * y n, ?_⟩
  apply Memℓp.mono' (lp.memℓp y)
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_inverse_integer_le_one n hn) (norm_nonneg _)).trans_eq
      (one_mul _)

lemma divideCircleFourierByIndex_mem_domain (y : L2Sequence ℤ) :
    divideCircleFourierByIndex y ∈ circleDirac.domain := by
  change Memℓp (fun n : ℤ => (n : ℂ) * divideCircleFourierByIndex y n) 2
  apply Memℓp.mono' (lp.memℓp y)
  intro n
  by_cases hn : n = 0
  · simp [divideCircleFourierByIndex, hn]
  · simp [divideCircleFourierByIndex, hn]

lemma circleDirac_divideCircleFourierByIndex (y : L2Sequence ℤ) (hy : y 0 = 0) :
    circleDirac ⟨divideCircleFourierByIndex y, divideCircleFourierByIndex_mem_domain y⟩ = y := by
  apply lp.ext
  funext n
  change (n : ℂ) * divideCircleFourierByIndex y n = y n
  by_cases hn : n = 0
  · subst n
    simpa [divideCircleFourierByIndex] using hy.symm
  · simp [divideCircleFourierByIndex, hn]

set_option backward.isDefEq.respectTransparency false in
/-- The range of the circle Dirac operator is exactly the closed hyperplane of sequences whose
zero Fourier coefficient vanishes. -/
theorem circleDirac_range_eq_circleZeroMode_ker :
    circleDirac.toFun.range = circleZeroMode.ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change circleZeroMode (circleDirac.toFun x) = 0
    rw [show circleZeroMode (circleDirac.toFun x) = (circleDirac.toFun x) 0 from rfl]
    change ((diagonalOperator fun n : ℤ => (n : ℝ)).toFun x) 0 = 0
    rw [show (diagonalOperator fun n : ℤ => (n : ℝ)).toFun x =
      diagonalOperator (fun n : ℤ => (n : ℝ)) x from rfl]
    rw [diagonalOperator_apply]
    simp
  · intro hy
    change y 0 = 0 at hy
    refine ⟨⟨divideCircleFourierByIndex y, divideCircleFourierByIndex_mem_domain y⟩, ?_⟩
    simpa [circleZeroMode] using circleDirac_divideCircleFourierByIndex y hy

/-- The zero Fourier mode, regarded as an element of the maximal circle-Dirac domain. -/
def circleZeroModeInDomain : circleDirac.domain :=
  ⟨sequenceHilbertBasis ℤ 0,
    sequenceHilbertBasis_mem_domain (fun n : ℤ => (n : ℝ)) 0⟩

lemma circleZeroModeInDomain_ne_zero : circleZeroModeInDomain ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : circleDirac.domain => x.1 0) h
  simpa [circleZeroModeInDomain] using h0

/-- The circle Dirac kernel is precisely the span of its zero Fourier mode. -/
theorem circleDirac_ker_eq_span_zeroMode :
    circleDirac.toFun.ker = ℂ ∙ circleZeroModeInDomain := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.1 0, ?_⟩
    apply Subtype.ext
    apply lp.ext
    funext n
    by_cases hn : n = 0
    · subst n
      simp [circleZeroModeInDomain]
    · have hcoord := congrArg (fun y : L2Sequence ℤ => y n) hx
      change (n : ℂ) * x.1 n = 0 at hcoord
      have hxzero : x.1 n = 0 := by
        apply (mul_eq_zero.mp hcoord).resolve_left
        exact_mod_cast hn
      simp [circleZeroModeInDomain, hn, hxzero]
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [LinearMap.mem_ker]
    have hzero : circleDirac.toFun circleZeroModeInDomain = 0 := by
      simpa [circleZeroModeInDomain] using circleDirac_mode 0
    simpa [hzero] using circleDirac.toFun.map_smul c circleZeroModeInDomain

lemma circleZeroMode_surjective : Function.Surjective circleZeroMode := by
  intro z
  refine ⟨lp.single 2 0 z, ?_⟩
  change (lp.single 2 0 z : L2Sequence ℤ) 0 = z
  simp

theorem circleDirac_ker_finrank : Module.finrank ℂ circleDirac.toFun.ker = 1 := by
  rw [circleDirac_ker_eq_span_zeroMode,
    finrank_span_singleton circleZeroModeInDomain_ne_zero]

theorem circleDirac_coker_finrank :
    Module.finrank ℂ (L2Sequence ℤ ⧸ circleDirac.toFun.range) = 1 := by
  rw [circleDirac_range_eq_circleZeroMode_ker]
  let e := circleZeroMode.toLinearMap.quotKerEquivOfSurjective circleZeroMode_surjective
  letI : FiniteDimensional ℂ (L2Sequence ℤ ⧸ circleZeroMode.ker) :=
    e.symm.finiteDimensional
  exact
    e.finrank_eq.trans (Module.finrank_self ℂ)

/-- The continuum circle Dirac operator is a closed Fredholm operator. -/
theorem circleDirac_closedFredholm : ClosedFredholm circleDirac := by
  refine ⟨circleDirac_isSelfAdjoint.isClosed, ?_, ?_, ?_⟩
  · rw [circleDirac_range_eq_circleZeroMode_ker]
    exact circleZeroMode.isClosed_ker
  · rw [circleDirac_ker_eq_span_zeroMode]
    infer_instance
  · rw [circleDirac_range_eq_circleZeroMode_ker]
    exact Module.Finite.equiv
      (circleZeroMode.toLinearMap.quotKerEquivOfSurjective
        circleZeroMode_surjective).symm

/-- The analytic Fredholm index of the continuum circle Dirac operator is zero. -/
theorem circleDirac_index_eq_zero : circleDirac.toFun.index = 0 := by
  rw [LinearMap.index_eq_finrank_sub, circleDirac_ker_finrank, circleDirac_coker_finrank]
  norm_num

/-! ## The APS spectral boundary space -/

/-! ### A genuine infinite-dimensional Sobolev trace carrier

The following carrier is the Fourier realization of the anisotropic cylinder space
`L²(S¹; H¹([0,1]))`.  A bulk coefficient is stored after multiplication by the normal
Sobolev weight `k + 1`; restriction to the boundary therefore sums the physical coefficients,
which is the inner product against `(k + 1)⁻¹`.  The inverse-weight vector is square summable,
so Cauchy--Schwarz gives a bounded trace into `L²(S¹)`.

This is an actual infinite Hilbert-space trace theorem.  It is the local cylinder model used by
the later manifold/collar globalization; it is not a finite-mode trace certificate.
-/

/-- Normal inverse fractional-Sobolev weights `(k+1)⁻ˢ`.  The sharp trace threshold
`s > 1/2` is exactly the shifted `p`-series convergence condition `2s > 1`. -/
def normalSobolevTraceVectorAt (s : ℝ) (hs : (1 / 2 : ℝ) < s) : L2Sequence ℕ := by
  refine ⟨fun k => ((((k : ℝ) + 1) ^ (-s) : ℝ) : ℂ), ?_⟩
  apply memℓp_gen
  have hsum : Summable (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ (2 * s)) :=
    (Real.summable_one_div_nat_add_rpow 1 (2 * s)).2 (by linarith)
  convert hsum using 1
  funext k
  have hk : 0 ≤ (k : ℝ) + 1 := by positivity
  rw [show |(k : ℝ) + 1| = (k : ℝ) + 1 by rw [abs_of_pos] <;> positivity]
  simp only [Complex.norm_real, Real.norm_eq_abs, ENNReal.toReal_ofNat, one_div]
  rw [Real.abs_rpow_of_nonneg hk, abs_of_nonneg hk]
  calc
    ((((k : ℝ) + 1) ^ (-s)) ^ (2 : ℝ)) =
        ((k : ℝ) + 1) ^ (-s * (2 : ℝ)) :=
      (Real.rpow_mul hk (-s) 2).symm
    _ = (((k : ℝ) + 1) ^ (2 * s))⁻¹ := by
      rw [show -s * (2 : ℝ) = -(2 * s) by ring, Real.rpow_neg hk]

/-- Normal inverse `H¹` Sobolev weights, the `s = 1` specialization of the sharp family. -/
def normalSobolevTraceVector : L2Sequence ℕ :=
  normalSobolevTraceVectorAt 1 (by norm_num)

/-- Fourier carrier for `L²(S¹;H¹_normal)`.  The outer index is tangential and the inner
`ℕ` index is a normal Fourier/eigenfunction mode carrying one Sobolev derivative. -/
abbrev CircleCylinderH1 := lp (fun _ : ℤ => L2Sequence ℕ) 2

set_option backward.isDefEq.respectTransparency false in
/-- The unbundled fractional boundary restriction map.  In physical coefficients it sums the
normal modes; the normalized carrier stores `x(n,k) = (k+1)^s a(n,k)`. -/
def circleCylinderTraceLinearAt (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    CircleCylinderH1 →ₗ[ℂ] L2Sequence ℤ where
  toFun x := by
    refine ⟨fun n => inner ℂ (normalSobolevTraceVectorAt s hs) (x n), ?_⟩
    have hx : Memℓp
        (fun n => (‖normalSobolevTraceVectorAt s hs‖ : ℂ) • x n) 2 :=
      (lp.memℓp x).const_smul (‖normalSobolevTraceVectorAt s hs‖ : ℂ)
    apply Memℓp.mono' hx
    intro n
    calc
      ‖inner ℂ (normalSobolevTraceVectorAt s hs) (x n)‖
          ≤ ‖normalSobolevTraceVectorAt s hs‖ * ‖x n‖ := norm_inner_le_norm _ _
      _ = ‖(‖normalSobolevTraceVectorAt s hs‖ : ℂ) • x n‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
  map_add' := by
    intro x y
    apply lp.ext
    funext n
    simp [inner_add_right]
  map_smul' := by
    intro c x
    apply lp.ext
    funext n
    simp [inner_smul_right]

/-- The unbundled `H¹` boundary restriction map. -/
def circleCylinderTraceLinear : CircleCylinderH1 →ₗ[ℂ] L2Sequence ℤ :=
  circleCylinderTraceLinearAt 1 (by norm_num)

/-- **Sharp local Sobolev trace theorem on the cylinder.** For every `s > 1/2`, boundary
restriction is bounded from the normalized `L²(S¹;Hˢ_normal)` Fourier carrier to `L²(S¹)`. -/
def circleCylinderSobolevTraceAt (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    CircleCylinderH1 →L[ℂ] L2Sequence ℤ :=
  (circleCylinderTraceLinearAt s hs).mkContinuous ‖normalSobolevTraceVectorAt s hs‖ fun x => by
    calc
      ‖circleCylinderTraceLinearAt s hs x‖
          ≤ ‖(‖normalSobolevTraceVectorAt s hs‖ : ℂ) • x‖ :=
        lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun n => by
          change ‖inner ℂ (normalSobolevTraceVectorAt s hs) (x n)‖ ≤
            ‖(‖normalSobolevTraceVectorAt s hs‖ : ℂ) • x n‖
          calc
            _ ≤ ‖normalSobolevTraceVectorAt s hs‖ * ‖x n‖ :=
              norm_inner_le_norm (𝕜 := ℂ) _ _
            _ = _ := by
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (norm_nonneg _)])
      _ = ‖normalSobolevTraceVectorAt s hs‖ * ‖x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]

/-- The `H¹` specialization of the sharp local Sobolev trace theorem. -/
def circleCylinderSobolevTrace : CircleCylinderH1 →L[ℂ] L2Sequence ℤ :=
  circleCylinderSobolevTraceAt 1 (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- Constant-normal extension of boundary Fourier data into the cylinder Sobolev carrier. -/
def circleCylinderConstantExtensionLinear : L2Sequence ℤ →ₗ[ℂ] CircleCylinderH1 where
  toFun y := by
    refine ⟨fun n => lp.single 2 0 (y n), ?_⟩
    apply Memℓp.mono' (lp.memℓp y)
    intro n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  map_add' := by
    intro x y
    apply lp.ext
    funext n
    apply lp.ext
    funext k
    simp [lp.single_apply]
  map_smul' := by
    intro c x
    apply lp.ext
    funext n
    apply lp.ext
    funext k
    by_cases hk : k = 0 <;> simp [lp.single_apply, hk]

set_option maxHeartbeats 800000 in
/-- The constant-normal extension is bounded (in fact isometric). -/
def circleCylinderConstantExtension : L2Sequence ℤ →L[ℂ] CircleCylinderH1 :=
  circleCylinderConstantExtensionLinear.mkContinuous 1 fun y => by
    simpa only [one_mul] using
      lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (x := circleCylinderConstantExtensionLinear y) (y := y) (fun n => by
          change ‖(lp.single 2 0 (y n) : L2Sequence ℕ)‖ ≤ ‖y n‖
          rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)])

/-- At every sharp exponent `s > 1/2`, restriction after constant-normal extension is the
identity on the boundary. -/
theorem circleCylinderSobolevTraceAt_comp_extension (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    (circleCylinderSobolevTraceAt s hs).comp circleCylinderConstantExtension =
      ContinuousLinearMap.id ℂ (L2Sequence ℤ) := by
  ext y n
  simp [circleCylinderSobolevTraceAt, circleCylinderTraceLinearAt,
    circleCylinderConstantExtension, circleCylinderConstantExtensionLinear,
    lp.inner_single_right, normalSobolevTraceVectorAt]

/-- Restriction after constant-normal extension is the identity at `s = 1`. -/
theorem circleCylinderSobolevTrace_comp_extension :
    circleCylinderSobolevTrace.comp circleCylinderConstantExtension =
      ContinuousLinearMap.id ℂ (L2Sequence ℤ) :=
  circleCylinderSobolevTraceAt_comp_extension 1 (by norm_num)

/-- The sharp fractional cylinder trace is onto for every `s > 1/2`. -/
theorem circleCylinderSobolevTraceAt_surjective (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    Function.Surjective (circleCylinderSobolevTraceAt s hs) := by
  intro y
  refine ⟨circleCylinderConstantExtension y, ?_⟩
  have h := congrArg (fun f : L2Sequence ℤ →L[ℂ] L2Sequence ℤ => f y)
    (circleCylinderSobolevTraceAt_comp_extension s hs)
  simpa using h

/-- The local cylinder Sobolev trace is onto `L²(S¹)`. -/
theorem circleCylinderSobolevTrace_surjective :
    Function.Surjective circleCylinderSobolevTrace := by
  exact circleCylinderSobolevTraceAt_surjective 1 (by norm_num)


/-- The nonnegative Fourier part of a circle boundary field. -/
def nonnegativeCircleFourierPart (x : L2Sequence ℤ) : L2Sequence ℤ := by
  refine ⟨fun n => if 0 ≤ n then x n else 0, ?_⟩
  apply Memℓp.mono' (lp.memℓp x)
  intro n
  split <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Linear nonnegative-mode projection on the circle boundary Hilbert space. -/
def circleAPSProjectionLinear : L2Sequence ℤ →ₗ[ℂ] L2Sequence ℤ where
  toFun := nonnegativeCircleFourierPart
  map_add' := by
    intro x y
    apply lp.ext
    funext n
    by_cases hn : 0 ≤ n <;> simp [nonnegativeCircleFourierPart, hn]
  map_smul' := by
    intro c x
    apply lp.ext
    funext n
    by_cases hn : 0 ≤ n <;> simp [nonnegativeCircleFourierPart, hn]

/-- The bounded APS projection onto the nonnegative spectrum of the circle Dirac operator. -/
def circleAPSProjection : L2Sequence ℤ →L[ℂ] L2Sequence ℤ :=
  circleAPSProjectionLinear.mkContinuous 1 fun x => by
    change ‖nonnegativeCircleFourierPart x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (x := nonnegativeCircleFourierPart x) (y := x) (fun n => by
        by_cases hn : 0 ≤ n <;> simp [nonnegativeCircleFourierPart, hn])

@[simp] lemma circleAPSProjection_apply (x : L2Sequence ℤ) (n : ℤ) :
    circleAPSProjection x n = if 0 ≤ n then x n else 0 := rfl

lemma circleAPSProjection_idempotent :
    circleAPSProjection.comp circleAPSProjection = circleAPSProjection := by
  ext x n
  by_cases hn : 0 ≤ n
  · change circleAPSProjection (circleAPSProjection x) n = circleAPSProjection x n
    simp only [circleAPSProjection_apply, if_pos hn]
  · change circleAPSProjection (circleAPSProjection x) n = circleAPSProjection x n
    simp only [circleAPSProjection_apply, if_neg hn]

/-- The nonnegative circle spectral subspace used by the APS boundary condition. -/
def circleAPSBoundarySpace : Submodule ℂ (L2Sequence ℤ) := circleAPSProjection.range

/-- The continuum APS spectral boundary space is topologically closed. -/
theorem circleAPSBoundarySpace_isClosed :
    IsClosed (circleAPSBoundarySpace : Set (L2Sequence ℤ)) := by
  have hIdem : IsIdempotentElem circleAPSProjection := circleAPSProjection_idempotent
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hIdem

/-- Given a continuous Sobolev trace operator into the circle boundary Hilbert space, the APS
boundary realization consists of bulk fields whose nonnegative spectral trace vanishes. -/
def circleAPSBoundaryCondition {Bulk : Type*} [NormedAddCommGroup Bulk] [NormedSpace ℂ Bulk]
    (trace : Bulk →L[ℂ] L2Sequence ℤ) : Submodule ℂ Bulk :=
  (circleAPSProjection.comp trace).ker

/-- Every continuous Sobolev trace operator induces a closed APS boundary condition. -/
theorem circleAPSBoundaryCondition_isClosed {Bulk : Type*}
    [NormedAddCommGroup Bulk] [NormedSpace ℂ Bulk]
    (trace : Bulk →L[ℂ] L2Sequence ℤ) :
    IsClosed (circleAPSBoundaryCondition trace : Set Bulk) :=
  (circleAPSProjection.comp trace).isClosed_ker

/-- The concrete APS domain on the Fourier cylinder, using the proved Sobolev trace operator. -/
def circleCylinderAPSBoundaryCondition : Submodule ℂ CircleCylinderH1 :=
  circleAPSBoundaryCondition circleCylinderSobolevTrace

/-- The APS domain at any fractional normal Sobolev exponent above the sharp trace threshold. -/
def circleCylinderAPSBoundaryConditionAt (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    Submodule ℂ CircleCylinderH1 :=
  circleAPSBoundaryCondition (circleCylinderSobolevTraceAt s hs)

/-- Every fractional cylinder APS domain above the trace threshold is closed. -/
theorem circleCylinderAPSBoundaryConditionAt_isClosed (s : ℝ) (hs : (1 / 2 : ℝ) < s) :
    IsClosed (circleCylinderAPSBoundaryConditionAt s hs : Set CircleCylinderH1) :=
  circleAPSBoundaryCondition_isClosed (circleCylinderSobolevTraceAt s hs)

/-- The concrete APS Sobolev domain on the infinite Fourier cylinder is closed. -/
theorem circleCylinderAPSBoundaryCondition_isClosed :
    IsClosed (circleCylinderAPSBoundaryCondition : Set CircleCylinderH1) :=
  circleCylinderAPSBoundaryConditionAt_isClosed 1 (by norm_num)

/-! ## Exact heat kernel and Seeley--DeWitt leading asymptotic -/

/-- The continuum circle heat trace `Tr(exp(-t D²))`, expressed in the Fourier eigenbasis. -/
def circleHeatTrace (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-t * (n : ℝ) ^ 2)

/-- Exact Poisson/Jacobi transformation of the circle heat trace. -/
theorem circleHeatTrace_poisson (t : ℝ) (ht : 0 < t) :
    circleHeatTrace t = Real.sqrt (Real.pi / t) *
      circleHeatTrace (Real.pi ^ 2 / t) := by
  have h := Real.tsum_exp_neg_mul_int_sq (a := t / Real.pi) (div_pos ht Real.pi_pos)
  have hleft : ∀ n : ℤ,
      -Real.pi * (t / Real.pi) * (n : ℝ) ^ 2 = -t * (n : ℝ) ^ 2 := by
    intro n
    field_simp
  have hright : ∀ n : ℤ,
      -Real.pi / (t / Real.pi) * (n : ℝ) ^ 2 =
        -(Real.pi ^ 2 / t) * (n : ℝ) ^ 2 := by
    intro n
    field_simp
  rw [show (1 : ℝ) / (t / Real.pi) ^ (1 / 2 : ℝ) =
      Real.sqrt (Real.pi / t) by
    rw [Real.sqrt_eq_rpow, one_div,
      ← Real.inv_rpow (le_of_lt (div_pos ht Real.pi_pos))]
    congr 2
    field_simp] at h
  simp_rw [hleft, hright] at h
  simpa only [circleHeatTrace, div_div, div_pow, Int.cast_ofNat] using h

theorem circleHeatTrace_ofReal_eq_jacobiTheta (u : ℝ) :
    (circleHeatTrace u : ℂ) = jacobiTheta (Complex.I * (u / Real.pi : ℝ)) := by
  unfold circleHeatTrace jacobiTheta
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The theta remainder tends to zero.  Combined with `circleHeatTrace_poisson`, this is the
flat-circle Seeley--DeWitt leading coefficient
`Tr(exp(-tD²)) ~ sqrt(pi/t)` (all higher flat local coefficients vanish). -/
theorem circleHeatTrace_tendsto_one_atTop :
    Tendsto circleHeatTrace atTop (nhds 1) := by
  let tau : ℝ → ℂ := fun u => Complex.I * (u / Real.pi : ℝ)
  have htau : Tendsto tau atTop (Filter.comap Complex.im atTop) := by
    rw [Filter.tendsto_comap_iff]
    simpa [tau, Function.comp_def] using
      (Tendsto.atTop_div_const Real.pi_pos tendsto_id)
  have hO := isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto htau
  have hexp : Tendsto
      ((fun z : ℂ => Real.exp (-Real.pi * z.im)) ∘ tau) atTop (nhds 0) := by
    have hneg : Tendsto (fun u : ℝ => -u) atTop atBot := tendsto_neg_atTop_atBot
    have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (nhds 0) :=
      (Real.tendsto_exp_atBot).comp hneg
    convert he using 1
    funext u
    simp only [tau, Function.comp_apply, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, neg_mul]
    field_simp [Real.pi_ne_zero]
    simp
  have htheta : Tendsto
      ((fun z : ℂ => jacobiTheta z - 1) ∘ tau) atTop (nhds 0) :=
    hO.trans_tendsto hexp
  have htheta' : Tendsto (fun u => jacobiTheta (tau u)) atTop (nhds 1) := by
    simpa [Function.comp_def] using htheta.add_const 1
  have hofReal : Tendsto (fun u => (circleHeatTrace u : ℂ)) atTop (nhds (1 : ℂ)) := by
    simpa [tau, circleHeatTrace_ofReal_eq_jacobiTheta] using htheta'
  exact (Complex.continuous_re.tendsto (1 : ℂ)).comp hofReal

/-! ## Meromorphic dimension spectrum -/

/-- The nonzero absolute Dirac spectrum, meromorphically continued from its Dirichlet series. -/
def circleDimensionZeta (s : ℂ) : ℂ := 2 * riemannZeta s

/-- The actual dimension-spectrum pole is `s = 1`, with residue `2`. -/
theorem circleDimensionZeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * circleDimensionZeta s)
      (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) (nhds (2 : ℂ)) := by
  have h := riemannZeta_residue_one.const_mul 2
  convert h using 1
  · funext s
    simp [circleDimensionZeta]
    ring
  · norm_num

/-- At every even integer `k ≥ 2`, the continued zeta agrees with the literal two-sided
nonzero Fourier spectrum. -/
theorem circleDimensionZeta_eq_spectralSeries_of_even
    (k : ℕ) (hk : 2 ≤ k) (hkEven : Even k) :
    circleDimensionZeta k = ∑' n : ℤ, ((n : ℂ) ^ k)⁻¹ := by
  exact two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even hk hkEven

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry
