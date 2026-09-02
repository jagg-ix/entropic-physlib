/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.DynamicalSystems.HolderConjugacy
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic
meta import Zil

/-!
# Derivative cocycles and continuous hyperbolic splittings

This module supplies the differential-geometric infrastructure deliberately left open by
`HolderConjugacy`.  It uses Mathlib's genuine `Diffeomorph`, `mfderiv`, tangent spaces, tangent
bundle topology, complementary submodules, and Riemannian fiber norms.

The three principal targets are:

1. `derivativeCocycle_add`: the chain-rule cocycle law for the differential of every iterate;
2. `InvariantSplitting.derivative_components`: a complementary stable/unstable tangent splitting
   whose canonical projections commute with the differential;
3. `HyperbolicSplitting.stable_tendsto_zero` and
   `HyperbolicSplitting.unstable_backward_tendsto_zero`: exponential estimates imply genuine
   asymptotic contraction in the Riemannian tangent norms.

The final section adds the finite algebraic Lyapunov--entropy layer isolated in Brown's survey
*Entropy, Lyapunov Exponents, and Rigidity of Group Actions* (arXiv:1809.09192v4): positive
proportionality defines coarse Lyapunov classes with a common sign, weighted entropy is bounded by
the Margulis--Ruelle capacity, equality forces componentwise saturation, and the entropy sum is
linear on every closed Weyl cone on which all exponent signs agree.

`ContinuousInvariantSplitting` records continuity of the two projections on the actual tangent
bundle.  `HyperbolicSplitting` adds the standard uniform constants `C > 0` and `0 ≤ λ < 1`.

## Honest scope

The module does not assert that an arbitrary diffeomorphism is Anosov.  A hyperbolic splitting is
explicit data: complementary invariant subspaces, continuous bundle projections, and forward /
backward contraction estimates.  Existence for a concrete system must be proved by constructing
that data.  Likewise, the entropy section proves consequences of supplied finite Lyapunov
functionals and transverse dimensions.  It does not construct an Oseledets splitting, identify the
weighted sum with Kolmogorov--Sinai entropy, construct conditional measures or SRB states, or claim
the full measure/classification rigidity theorems of the survey.
-/

set_option autoImplicit false

noncomputable section

open scoped Bundle Manifold ContDiff
open Bundle Manifold Filter
open BigOperators

@[expose] public section

namespace Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity

universe u v

variable {E : Type u} {H M : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)

/-! ## A. The intrinsic derivative cocycle -/

/-- The derivative cocycle `D(Φⁿ)_x`, represented as a continuous linear map between the genuine
tangent fibers over `x` and `Φⁿx`. -/
def derivativeCocycle (Φ : Diffeomorph I I M M 1) (n : ℕ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I ((Φ^[n]) x) :=
  mfderiv I I (Φ^[n]) x

/-- The manifold chain rule gives the cocycle identity
`D(Φ^(m+n))_x = D(Φ^m)_(Φ^n x) ∘ D(Φ^n)_x`. -/
lemma derivativeCocycle_add (Φ : Diffeomorph I I M M 1) (m n : ℕ) (x : M) :
    derivativeCocycle I Φ (m + n) x =
      (derivativeCocycle I Φ m ((Φ^[n]) x)).comp (derivativeCocycle I Φ n x) := by
  unfold derivativeCocycle
  rw [Function.iterate_add]
  exact mfderiv_comp x
    ((Φ.contMDiff.iterate m).mdifferentiable one_ne_zero ((Φ^[n]) x))
    ((Φ.contMDiff.iterate n).mdifferentiable one_ne_zero x)

set_option backward.isDefEq.respectTransparency false in
/-- The time-zero derivative cocycle is the identity on the tangent fiber. -/
lemma derivativeCocycle_zero (Φ : Diffeomorph I I M M 1) (x : M) :
    derivativeCocycle I Φ 0 x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  simp [derivativeCocycle, mfderiv_id]

set_option backward.isDefEq.respectTransparency false in
/-- The one-step derivative cocycle is Mathlib's manifold derivative of the diffeomorphism. -/
lemma derivativeCocycle_one (Φ : Diffeomorph I I M M 1) (x : M) :
    derivativeCocycle I Φ 1 x = mfderiv I I Φ x := by
  simp [derivativeCocycle]

/-- The one-step cocycle is bijective because the derivative of a diffeomorphism is a continuous
linear equivalence. -/
lemma derivativeCocycle_one_bijective (Φ : Diffeomorph I I M M 1) (x : M) :
    Function.Bijective (derivativeCocycle I Φ 1 x) := by
  rw [derivativeCocycle_one]
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
    (x := x) Φ one_ne_zero]
  exact (Φ.mfderivToContinuousLinearEquiv one_ne_zero x).bijective

/-- A smooth additive group action packaged directly by genuine manifold diffeomorphisms.  Taking
`G = Fin d → ℤ` gives the smooth `ℤ^d` actions used throughout Brown's survey.  The composition
order states that `A (g + h)` first applies `A h` and then `A g`. -/
structure SmoothAdditiveDiffeomorphismAction (G : Type*) [AddGroup G] where
  /-- Diffeomorphism assigned to each action element. -/
  toDiffeomorph : G → Diffeomorph I I M M 1
  /-- The zero action element acts identically. -/
  map_zero : toDiffeomorph 0 = Diffeomorph.refl I M 1
  /-- Addition is represented by composition. -/
  map_add : ∀ g h, toDiffeomorph (g + h) =
    (toDiffeomorph h).trans (toDiffeomorph g)

/-- The derivative cocycle of a smooth additive action. -/
def higherRankDerivativeCocycle {G : Type*} [AddGroup G]
    (A : SmoothAdditiveDiffeomorphismAction I G) (g : G) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I (A.toDiffeomorph g x) :=
  mfderiv I I (A.toDiffeomorph g) x

/-- The genuine manifold chain rule realizes the higher-rank derivative-cocycle identity. -/
@[zil_level bridge_theorem]
lemma higherRankDerivativeCocycle_add {G : Type*} [AddGroup G]
    (A : SmoothAdditiveDiffeomorphismAction I G) (g h : G) (x : M) :
    higherRankDerivativeCocycle I A (g + h) x =
      (higherRankDerivativeCocycle I A g (A.toDiffeomorph h x)).comp
        (higherRankDerivativeCocycle I A h x) := by
  unfold higherRankDerivativeCocycle
  rw [A.map_add]
  exact mfderiv_comp x
    ((A.toDiffeomorph g).contMDiff.mdifferentiable one_ne_zero (A.toDiffeomorph h x))
    ((A.toDiffeomorph h).contMDiff.mdifferentiable one_ne_zero x)

set_option backward.isDefEq.respectTransparency false in
/-- The derivative cocycle at the zero action element is the identity on the tangent fiber. -/
lemma higherRankDerivativeCocycle_zero {G : Type*} [AddGroup G]
    (A : SmoothAdditiveDiffeomorphismAction I G) (x : M) :
    higherRankDerivativeCocycle I A 0 x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  unfold higherRankDerivativeCocycle
  rw [A.map_zero]
  simp [mfderiv_id]

/-- An invariant tangent splitting into complementary stable and unstable subspaces.  Invariance
is exact equality of the submodule image under the genuine manifold differential. -/
structure InvariantSplitting (Φ : Diffeomorph I I M M 1) where
  /-- Stable tangent subspace at each base point. -/
  stable : (x : M) → Submodule ℝ (TangentSpace I x)
  /-- Unstable tangent subspace at each base point. -/
  unstable : (x : M) → Submodule ℝ (TangentSpace I x)
  /-- Every tangent vector decomposes uniquely into stable and unstable components. -/
  complementary : ∀ x, IsCompl (stable x) (unstable x)
  /-- The differential maps the stable subspace exactly onto the next stable subspace. -/
  stable_image : ∀ x,
    Submodule.map (mfderiv I I Φ x).toLinearMap (stable x) = stable (Φ x)
  /-- The differential maps the unstable subspace exactly onto the next unstable subspace. -/
  unstable_image : ∀ x,
    Submodule.map (mfderiv I I Φ x).toLinearMap (unstable x) = unstable (Φ x)

namespace InvariantSplitting

variable {I}
variable {Φ : Diffeomorph I I M M 1}

/-- Stable vectors remain stable under the differential. -/
lemma stable_invariant (S : InvariantSplitting I Φ) (x : M)
    (v : TangentSpace I x) (hv : v ∈ S.stable x) :
    mfderiv I I Φ x v ∈ S.stable (Φ x) := by
  rw [← S.stable_image x]
  exact ⟨v, hv, rfl⟩

/-- Unstable vectors remain unstable under the differential. -/
lemma unstable_invariant (S : InvariantSplitting I Φ) (x : M)
    (v : TangentSpace I x) (hv : v ∈ S.unstable x) :
    mfderiv I I Φ x v ∈ S.unstable (Φ x) := by
  rw [← S.unstable_image x]
  exact ⟨v, hv, rfl⟩

/-- Stable and unstable tangent directions have trivial intersection. -/
lemma stable_inf_unstable (S : InvariantSplitting I Φ) (x : M) :
    S.stable x ⊓ S.unstable x = ⊥ :=
  (S.complementary x).inf_eq_bot

/-- Stable and unstable tangent directions span the full tangent space. -/
lemma stable_sup_unstable (S : InvariantSplitting I Φ) (x : M) :
    S.stable x ⊔ S.unstable x = ⊤ :=
  (S.complementary x).sup_eq_top

/-- The canonical linear equivalence from a tangent fiber to its stable/unstable components. -/
def decompositionEquiv (S : InvariantSplitting I Φ) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] S.stable x × S.unstable x :=
  (Submodule.prodEquivOfIsCompl _ _ (S.complementary x)).symm

/-- Stable component of a tangent vector. -/
def stableComponent (S : InvariantSplitting I Φ) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  S.decompositionEquiv x v |>.1

/-- Unstable component of a tangent vector. -/
def unstableComponent (S : InvariantSplitting I Φ) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  S.decompositionEquiv x v |>.2

/-- The stable component lies in the stable tangent subspace. -/
lemma stableComponent_mem (S : InvariantSplitting I Φ) (x : M) (v : TangentSpace I x) :
    S.stableComponent x v ∈ S.stable x :=
  (S.decompositionEquiv x v).1.property

/-- The unstable component lies in the unstable tangent subspace. -/
lemma unstableComponent_mem (S : InvariantSplitting I Φ) (x : M) (v : TangentSpace I x) :
    S.unstableComponent x v ∈ S.unstable x :=
  (S.decompositionEquiv x v).2.property

/-- The two canonical components reconstruct the original tangent vector. -/
lemma decomposition_sum (S : InvariantSplitting I Φ) (x : M) (v : TangentSpace I x) :
    S.stableComponent x v + S.unstableComponent x v = v := by
  change (Submodule.prodEquivOfIsCompl _ _ (S.complementary x))
    ((Submodule.prodEquivOfIsCompl _ _ (S.complementary x)).symm v) = v
  exact LinearEquiv.apply_symm_apply _ v

/-- A stable-plus-unstable decomposition of a tangent vector is unique. -/
lemma decomposition_unique (S : InvariantSplitting I Φ) (x : M)
    (v vStable vUnstable : TangentSpace I x)
    (hStable : vStable ∈ S.stable x) (hUnstable : vUnstable ∈ S.unstable x)
    (hsum : vStable + vUnstable = v) :
    S.stableComponent x v = vStable ∧ S.unstableComponent x v = vUnstable := by
  let e := Submodule.prodEquivOfIsCompl _ _ (S.complementary x)
  have hpairs :
      S.decompositionEquiv x v =
        (⟨vStable, hStable⟩, ⟨vUnstable, hUnstable⟩) := by
    apply e.injective
    change e (e.symm v) = vStable + vUnstable
    rw [e.apply_symm_apply]
    exact hsum.symm
  exact ⟨congrArg (fun p => (p.1 : TangentSpace I x)) hpairs,
    congrArg (fun p => (p.2 : TangentSpace I x)) hpairs⟩

/-- The differential commutes with both canonical bundle components.  This is the intrinsic
stable-bundle compatibility equation, obtained from exact invariance and uniqueness. -/
lemma derivative_components (S : InvariantSplitting I Φ) (x : M)
    (v : TangentSpace I x) :
    mfderiv I I Φ x (S.stableComponent x v) =
        S.stableComponent (Φ x) (mfderiv I I Φ x v) ∧
      mfderiv I I Φ x (S.unstableComponent x v) =
        S.unstableComponent (Φ x) (mfderiv I I Φ x v) := by
  have hsum :
      mfderiv I I Φ x (S.stableComponent x v) +
          mfderiv I I Φ x (S.unstableComponent x v) =
        mfderiv I I Φ x v := by
    rw [← map_add, S.decomposition_sum]
  have h := S.decomposition_unique (Φ x) (mfderiv I I Φ x v)
    (mfderiv I I Φ x (S.stableComponent x v))
    (mfderiv I I Φ x (S.unstableComponent x v))
    (S.stable_invariant x _ (S.stableComponent_mem x v))
    (S.unstable_invariant x _ (S.unstableComponent_mem x v)) hsum
  exact ⟨h.1.symm, h.2.symm⟩

/-- The stable projection as a base-preserving self-map of the genuine tangent bundle. -/
def stableBundleProjection (S : InvariantSplitting I Φ) :
    TangentBundle I M → TangentBundle I M :=
  fun p => ⟨p.1, S.stableComponent p.1 p.2⟩

/-- The unstable projection as a base-preserving self-map of the genuine tangent bundle. -/
def unstableBundleProjection (S : InvariantSplitting I Φ) :
    TangentBundle I M → TangentBundle I M :=
  fun p => ⟨p.1, S.unstableComponent p.1 p.2⟩

end InvariantSplitting

variable [IsManifold I 1 M]

/-- An invariant splitting whose stable and unstable projections vary continuously on the tangent
bundle.  This is the bundle-regularity datum missing from a merely pointwise family of subspaces. -/
structure ContinuousInvariantSplitting (Φ : Diffeomorph I I M M 1)
    extends InvariantSplitting I Φ where
  /-- Continuity of the stable tangent-bundle projection. -/
  stableProjection_continuous :
    Continuous toInvariantSplitting.stableBundleProjection
  /-- Continuity of the unstable tangent-bundle projection. -/
  unstableProjection_continuous :
    Continuous toInvariantSplitting.unstableBundleProjection

variable [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- A continuous invariant splitting with uniform forward stable and backward unstable exponential
contraction in the Riemannian tangent norms. -/
structure HyperbolicSplitting (Φ : Diffeomorph I I M M 1)
    extends ContinuousInvariantSplitting I Φ where
  /-- Uniform multiplicative constant in both hyperbolic estimates. -/
  C : ℝ
  /-- Positivity of the uniform constant. -/
  C_pos : 0 < C
  /-- Uniform geometric contraction factor. -/
  contraction : ℝ
  /-- Nonnegativity of the contraction factor. -/
  contraction_nonneg : 0 ≤ contraction
  /-- Strict contraction. -/
  contraction_lt_one : contraction < 1
  /-- Forward exponential contraction on stable tangent vectors. -/
  stable_contracts : ∀ n x v, v ∈ stable x →
    ‖derivativeCocycle I Φ n x v‖ ≤ (C * ‖v‖) * contraction ^ n
  /-- Backward exponential contraction on unstable tangent vectors. -/
  unstable_contracts_backward : ∀ n x v, v ∈ unstable x →
    ‖derivativeCocycle I Φ.symm n x v‖ ≤ (C * ‖v‖) * contraction ^ n

namespace HyperbolicSplitting

variable {I}
variable {Φ : Diffeomorph I I M M 1}

/-- Every stable tangent vector converges to zero under the forward derivative cocycle. -/
lemma stable_tendsto_zero (S : HyperbolicSplitting I Φ) (x : M)
    (v : TangentSpace I x) (hv : v ∈ S.stable x) :
    Tendsto (fun n => ‖derivativeCocycle I Φ n x v‖) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => S.stable_contracts n x v hv)
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one S.contraction_nonneg
      S.contraction_lt_one).const_mul (S.C * ‖v‖)

/-- Every unstable tangent vector converges to zero under the backward derivative cocycle. -/
lemma unstable_backward_tendsto_zero (S : HyperbolicSplitting I Φ) (x : M)
    (v : TangentSpace I x) (hv : v ∈ S.unstable x) :
    Tendsto (fun n => ‖derivativeCocycle I Φ.symm n x v‖) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => S.unstable_contracts_backward n x v hv)
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one S.contraction_nonneg
      S.contraction_lt_one).const_mul (S.C * ‖v‖)

end HyperbolicSplitting

/-- Intrinsic Anosov data for a `C¹` diffeomorphism: existence of a continuous complementary
stable/unstable tangent splitting with uniform exponential contraction. -/
def IsAnosovDiffeomorph (Φ : Diffeomorph I I M M 1) : Prop :=
  Nonempty (HyperbolicSplitting I Φ)

/-! ## B. Coarse Lyapunov classes and the finite entropy--rigidity mechanism -/

section LyapunovEntropy

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two Lyapunov functionals lie in the same coarse class when they differ by a strictly positive
scalar.  Positivity, rather than mere nonzero proportionality, is what makes the expanding,
neutral, and contracting signs independent of the representative. -/
def CoarseLyapunovEquivalent (lambdaExp muExp : V →ₗ[ℝ] ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ lambdaExp = c • muExp

lemma coarseLyapunovEquivalent_refl (lambdaExp : V →ₗ[ℝ] ℝ) :
    CoarseLyapunovEquivalent lambdaExp lambdaExp := by
  exact ⟨1, zero_lt_one, by simp⟩

lemma coarseLyapunovEquivalent_symm {lambdaExp muExp : V →ₗ[ℝ] ℝ}
    (h : CoarseLyapunovEquivalent lambdaExp muExp) :
    CoarseLyapunovEquivalent muExp lambdaExp := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

lemma coarseLyapunovEquivalent_trans {lambdaExp muExp nuExp : V →ₗ[ℝ] ℝ}
    (hFirst : CoarseLyapunovEquivalent lambdaExp muExp)
    (hSecond : CoarseLyapunovEquivalent muExp nuExp) :
    CoarseLyapunovEquivalent lambdaExp nuExp := by
  rcases hFirst with ⟨c, hc, rfl⟩
  rcases hSecond with ⟨d, hd, rfl⟩
  refine ⟨c * d, mul_pos hc hd, ?_⟩
  rw [smul_smul]

/-- Every representative of a coarse Lyapunov class has the same expanding, neutral, or
contracting sign on every action direction.  This is the algebraic fact used to assign a sign to a
coarse exponent in Brown §7.4.2. -/
@[zil_level bridge_theorem]
lemma coarseLyapunovEquivalent_sign {lambdaExp muExp : V →ₗ[ℝ] ℝ}
    (h : CoarseLyapunovEquivalent lambdaExp muExp) (n : V) :
    (0 < lambdaExp n ↔ 0 < muExp n) ∧
      (lambdaExp n = 0 ↔ muExp n = 0) ∧
      (lambdaExp n < 0 ↔ muExp n < 0) := by
  rcases h with ⟨c, hc, rfl⟩
  simp only [LinearMap.smul_apply, smul_eq_mul]
  constructor
  · exact mul_pos_iff_of_pos_left hc
  constructor
  · simp [hc.ne']
  · calc
      c * muExp n < 0 ↔ 0 < -(c * muExp n) := neg_pos.symm
      _ ↔ 0 < c * (-muExp n) := by ring_nf
      _ ↔ 0 < -muExp n := mul_pos_iff_of_pos_left hc
      _ ↔ muExp n < 0 := neg_pos

/-- Coarse-equivalent Lyapunov functionals define the same Lyapunov hyperplane. -/
@[zil_level bridge_theorem]
lemma coarseLyapunovEquivalent_ker_eq {lambdaExp muExp : V →ₗ[ℝ] ℝ}
    (h : CoarseLyapunovEquivalent lambdaExp muExp) :
    LinearMap.ker lambdaExp = LinearMap.ker muExp := by
  rcases h with ⟨c, hc, rfl⟩
  ext n
  simp [LinearMap.mem_ker, hc.ne']

/-- An action direction is regular for a finite exponent family when it lies on none of its
Lyapunov hyperplanes. -/
def IsRegularLyapunovDirection [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (n : V) : Prop :=
  ∀ i, exponent i n ≠ 0

/-- Regularity depends only on coarse Lyapunov classes, not on their representatives. -/
@[zil_level bridge_theorem]
lemma isRegularLyapunovDirection_iff_of_pointwise_coarse [Fintype ι]
    {exponent exponent' : ι → V →ₗ[ℝ] ℝ}
    (hcoarse : ∀ i, CoarseLyapunovEquivalent (exponent i) (exponent' i))
    (n : V) :
    IsRegularLyapunovDirection exponent n ↔ IsRegularLyapunovDirection exponent' n := by
  constructor
  · intro hreg i hzero
    apply hreg i
    exact ((coarseLyapunovEquivalent_sign (hcoarse i) n).2.1).mpr hzero
  · intro hreg i hzero
    apply hreg i
    exact ((coarseLyapunovEquivalent_sign (hcoarse i) n).2.1).mp hzero

/-- The finite Ledrappier--Young weighted exponent sum.  This is deliberately an algebraic
quantity: identifying it with metric entropy requires the analytic hypotheses and conditional
measure theory of the Ledrappier--Young theorem. -/
noncomputable def weightedLyapunovEntropy [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ) (n : V) : ℝ :=
  ∑ i, transverseDimension i * max (exponent i n) 0

/-- The finite Margulis--Ruelle capacity: positive Lyapunov growth counted with its full integer
multiplicity. -/
noncomputable def margulisRuelleCapacity [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (multiplicity : ι → ℕ) (n : V) : ℝ :=
  ∑ i, (multiplicity i : ℝ) * max (exponent i n) 0

lemma weightedLyapunovEntropy_nonneg [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ) (n : V)
    (hdim : ∀ i, 0 ≤ transverseDimension i) :
    0 ≤ weightedLyapunovEntropy exponent transverseDimension n := by
  unfold weightedLyapunovEntropy
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hdim i) (le_max_right _ _)

/-- Finite algebraic core of the Margulis--Ruelle/Ledrappier--Young comparison: conditional
dimensions bounded by full multiplicities give an entropy sum bounded by the positive-exponent
capacity. -/
@[zil_level bridge_theorem]
lemma weightedLyapunovEntropy_le_margulisRuelleCapacity [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ)
    (multiplicity : ι → ℕ) (n : V)
    (hdim : ∀ i, transverseDimension i ≤ multiplicity i) :
    weightedLyapunovEntropy exponent transverseDimension n ≤
      margulisRuelleCapacity exponent multiplicity n := by
  unfold weightedLyapunovEntropy margulisRuelleCapacity
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hdim i) (le_max_right _ _)

/-- If every displayed exponent is strictly positive, the weighted entropy reaches the full
Margulis--Ruelle capacity exactly when every transverse dimension reaches its multiplicity.  This
is the finite saturation mechanism behind the SRB criterion, without claiming the analytic SRB
characterization itself. -/
@[zil_level bridge_theorem]
lemma weightedLyapunovEntropy_eq_capacity_iff_fullDimension [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ)
    (multiplicity : ι → ℕ) (n : V)
    (hdim : ∀ i, transverseDimension i ≤ multiplicity i)
    (hpos : ∀ i, 0 < exponent i n) :
    weightedLyapunovEntropy exponent transverseDimension n =
        margulisRuelleCapacity exponent multiplicity n ↔
      ∀ i, transverseDimension i = multiplicity i := by
  unfold weightedLyapunovEntropy margulisRuelleCapacity
  constructor
  · intro hsum i
    have hterm : ∀ j ∈ Finset.univ,
        transverseDimension j * max (exponent j n) 0 ≤
          (multiplicity j : ℝ) * max (exponent j n) 0 :=
      fun j _ => mul_le_mul_of_nonneg_right (hdim j) (le_max_right _ _)
    have hi := (Finset.sum_eq_sum_iff_of_le hterm).mp hsum i (Finset.mem_univ i)
    rw [max_eq_left (hpos i).le] at hi
    exact mul_right_cancel₀ (ne_of_gt (hpos i)) hi
  · intro hfull
    apply Finset.sum_congr rfl
    intro i _
    rw [hfull i]

/-- Two action directions lie in one closed Weyl cone when every exponent is nonnegative on both
or nonpositive on both. -/
def SameClosedWeylCone [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (n m : V) : Prop :=
  ∀ i, (0 ≤ exponent i n ∧ 0 ≤ exponent i m) ∨
    (exponent i n ≤ 0 ∧ exponent i m ≤ 0)

/-- The weighted positive-exponent sum is positively homogeneous. -/
@[zil_level bridge_theorem]
lemma weightedLyapunovEntropy_smul_of_nonneg [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ) (n : V)
    (c : ℝ) (hc : 0 ≤ c) :
    weightedLyapunovEntropy exponent transverseDimension (c • n) =
      c * weightedLyapunovEntropy exponent transverseDimension n := by
  unfold weightedLyapunovEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  by_cases hexp : 0 ≤ exponent i n
  · rw [max_eq_left hexp, max_eq_left (mul_nonneg hc hexp)]
    ring
  · have hexp' : exponent i n ≤ 0 := le_of_not_ge hexp
    rw [max_eq_right hexp', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hexp')]
    ring

/-- On a common closed Weyl cone, the weighted positive-exponent sum is additive.  Together with
homogeneity this is the exact finite piecewise-linear entropy geometry described after Brown's
Theorem 8.8. -/
@[zil_level bridge_theorem]
lemma weightedLyapunovEntropy_add_of_sameClosedWeylCone [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ) (n m : V)
    (hcone : SameClosedWeylCone exponent n m) :
    weightedLyapunovEntropy exponent transverseDimension (n + m) =
      weightedLyapunovEntropy exponent transverseDimension n +
        weightedLyapunovEntropy exponent transverseDimension m := by
  unfold weightedLyapunovEntropy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add]
  rcases hcone i with hnonneg | hnonpos
  · rw [max_eq_left hnonneg.1, max_eq_left hnonneg.2,
      max_eq_left (add_nonneg hnonneg.1 hnonneg.2)]
    ring
  · rw [max_eq_right hnonpos.1, max_eq_right hnonpos.2,
      max_eq_right (add_nonpos hnonpos.1 hnonpos.2)]
    ring

/-- For nonnegative transverse dimensions, the weighted Lyapunov entropy is globally
subadditive.  Exact additivity is recovered by
`weightedLyapunovEntropy_add_of_sameClosedWeylCone`. -/
@[zil_level bridge_theorem]
lemma weightedLyapunovEntropy_subadd [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (transverseDimension : ι → ℝ) (n m : V)
    (hdim : ∀ i, 0 ≤ transverseDimension i) :
    weightedLyapunovEntropy exponent transverseDimension (n + m) ≤
      weightedLyapunovEntropy exponent transverseDimension n +
        weightedLyapunovEntropy exponent transverseDimension m := by
  unfold weightedLyapunovEntropy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [map_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (hdim i)
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- The signed multiplicity-weighted Lyapunov sum.  For a volume-preserving derivative cocycle
this vanishes; the theorem below takes that analytic/geometric fact as a visible premise. -/
noncomputable def signedLyapunovSum [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (multiplicity : ι → ℕ) (n : V) : ℝ :=
  ∑ i, (multiplicity i : ℝ) * exponent i n

private lemma max_eq_self_add_max_neg (a : ℝ) :
    max a 0 = a + max (-a) 0 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    ring
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
    ring

/-- A zero signed Lyapunov sum makes the positive-exponent capacity symmetric under reversal of
the action direction.  This is the finite algebraic stable/unstable balance used for
volume-preserving higher-rank actions. -/
@[zil_level bridge_theorem]
lemma margulisRuelleCapacity_neg_eq_of_signedSum_eq_zero [Fintype ι]
    (exponent : ι → V →ₗ[ℝ] ℝ) (multiplicity : ι → ℕ) (n : V)
    (hbalance : signedLyapunovSum exponent multiplicity n = 0) :
    margulisRuelleCapacity exponent multiplicity (-n) =
      margulisRuelleCapacity exponent multiplicity n := by
  unfold margulisRuelleCapacity
  have hrewrite : ∀ i,
      max (exponent i n) 0 = exponent i n + max (-(exponent i n)) 0 :=
    fun i => max_eq_self_add_max_neg (exponent i n)
  calc
    ∑ i, (multiplicity i : ℝ) * max (exponent i (-n)) 0 =
        ∑ i, (multiplicity i : ℝ) * max (-(exponent i n)) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [map_neg]
    _ = 0 + ∑ i, (multiplicity i : ℝ) * max (-(exponent i n)) 0 := by ring
    _ = signedLyapunovSum exponent multiplicity n +
          ∑ i, (multiplicity i : ℝ) * max (-(exponent i n)) 0 := by rw [hbalance]
    _ = ∑ i, ((multiplicity i : ℝ) * exponent i n +
          (multiplicity i : ℝ) * max (-(exponent i n)) 0) := by
            unfold signedLyapunovSum
            rw [Finset.sum_add_distrib]
    _ = ∑ i, (multiplicity i : ℝ) * max (exponent i n) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hrewrite i]
          ring

/-- A finite rigidity principle used repeatedly in entropy arguments: if each leafwise entropy is
bounded by its capacity and the total bound is saturated, every component is saturated. -/
@[zil_level bridge_theorem]
lemma coarseEntropy_saturation_rigidity [Fintype ι]
    (leafEntropy capacity : ι → ℝ)
    (hle : ∀ i, leafEntropy i ≤ capacity i)
    (hsum : ∑ i, leafEntropy i = ∑ i, capacity i) :
    ∀ i, leafEntropy i = capacity i := by
  intro i
  exact (Finset.sum_eq_sum_iff_of_le fun j _ => hle j).mp hsum i (Finset.mem_univ i)

/-- A root is resonant with a finite fiberwise exponent family when it belongs to the same coarse
Lyapunov class as at least one fiberwise exponent. -/
def IsResonantWith {Fiber : Type*} (root : V →ₗ[ℝ] ℝ)
    (fiberExponent : Fiber → V →ₗ[ℝ] ℝ) : Prop :=
  ∃ j, CoarseLyapunovEquivalent root (fiberExponent j)

/-- Brown's finite resonance-counting mechanism (Remark 15.6): if distinct roots belong to
distinct coarse Lyapunov classes, the number of roots resonant with a fiberwise exponent is at
most the number of fiberwise exponent slots. -/
@[zil_level bridge_theorem]
lemma resonantRoot_card_le {Root Fiber : Type*} [Fintype Root] [Fintype Fiber]
    (root : Root → V →ₗ[ℝ] ℝ) (fiberExponent : Fiber → V →ₗ[ℝ] ℝ)
    (hseparated : ∀ r s,
      CoarseLyapunovEquivalent (root r) (root s) → r = s) :
    Nat.card {r : Root // IsResonantWith (root r) fiberExponent} ≤
      Nat.card Fiber := by
  classical
  let witness : {r : Root // IsResonantWith (root r) fiberExponent} → Fiber :=
    fun r => Classical.choose r.property
  have hwitness : ∀ r,
      CoarseLyapunovEquivalent (root r.1) (fiberExponent (witness r)) :=
    fun r => Classical.choose_spec r.property
  apply Nat.card_le_card_of_injective witness
  intro r s hrs
  apply Subtype.ext
  apply hseparated r.1 s.1
  apply coarseLyapunovEquivalent_trans (hwitness r)
  apply coarseLyapunovEquivalent_symm
  simpa [hrs] using hwitness s

end LyapunovEntropy

end Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.derivativeCocycle_add where
  formalizes @ "claim:the-manifold-derivative-of-iterates-satisfies-the-cocycle-chain-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:Mathlib.Geometry.Manifold.ContMDiff.MFDeriv",
  caveat @ "claim:this-is-an-exact-chain-rule-identity-and-does-not-assert-hyperbolicity"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.higherRankDerivativeCocycle_add where
  formalizes @ "claim:the-manifold-derivative-of-a-smooth-additive-group-action-satisfies-the-higher-rank-cocycle-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-section-7.4",
  caveat @ "claim:the-smooth-action-is-explicit-data-and-the-theorem-does-not-construct-an-oseledets-splitting-or-invariant-measure"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.InvariantSplitting.derivative_components where
  formalizes @ "claim:canonical-stable-and-unstable-tangent-components-commute-with-the-diffeomorphism-derivative",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms",
  caveat @ "claim:the-result-is-derived-from-explicit-complementarity-and-exact-invariance-data"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.HyperbolicSplitting.stable_tendsto_zero where
  formalizes @ "claim:uniform-exponential-stable-cocycle-contraction-implies-forward-tangent-convergence-to-zero",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:tendsto_pow_atTop_nhds_zero_of_lt_one",
  caveat @ "claim:existence-of-the-hyperbolic-splitting-remains-a-system-specific-proof-obligation"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.HyperbolicSplitting.unstable_backward_tendsto_zero where
  formalizes @ "claim:uniform-exponential-unstable-cocycle-contraction-implies-backward-tangent-convergence-to-zero",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:tendsto_pow_atTop_nhds_zero_of_lt_one",
  caveat @ "claim:existence-of-the-hyperbolic-splitting-remains-a-system-specific-proof-obligation"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseLyapunovEquivalent_sign where
  formalizes @ "claim:positive-proportional-coarse-lyapunov-exponents-have-the-same-sign-in-every-action-direction",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-section-7.4.2",
  caveat @ "claim:the-result-proves-representative-independent-sign-for-supplied-linear-functionals-and-does-not-construct-oseledets-exponents"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseLyapunovEquivalent_ker_eq where
  formalizes @ "claim:positive-proportional-coarse-lyapunov-exponents-determine-the-same-lyapunov-hyperplane",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-section-7.4.2",
  caveat @ "claim:the-hyperplane-identity-is-for-supplied-linear-functionals-and-does-not-construct-weyl-chambers-for-an-action"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.isRegularLyapunovDirection_iff_of_pointwise_coarse where
  formalizes @ "claim:regular-action-directions-are-independent-of-the-chosen-coarse-lyapunov-representatives",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-section-7.4",
  caveat @ "claim:regularity-is-proved-relative-to-a-supplied-finite-exponent-family"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_le_margulisRuelleCapacity where
  formalizes @ "claim:a-finite-ledrappier-young-weighted-exponent-sum-is-bounded-by-the-margulis-ruelle-capacity",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorems-8.6-8.7",
  caveat @ "claim:this-is-the-algebraic-inequality-for-supplied-exponents-and-dimensions-not-a-proof-that-the-sum-is-kolmogorov-sinai-entropy"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_eq_capacity_iff_fullDimension where
  formalizes @ "claim:strictly-positive-finite-lyapunov-entropy-capacity-saturates-exactly-when-every-transverse-dimension-is-full",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorem-9.3",
  caveat @ "claim:this-proves-the-finite-saturation-mechanism-but-not-the-analytic-srb-characterization-or-absolute-continuity-of-leafwise-measures"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_add_of_sameClosedWeylCone where
  formalizes @ "claim:the-finite-weighted-positive-lyapunov-sum-is-linear-within-each-common-closed-weyl-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorem-8.8",
  caveat @ "claim:the-theorem-is-exact-for-the-defined-finite-sum-and-does-not-identify-it-with-action-entropy-without-the-surveys-analytic-hypotheses"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_smul_of_nonneg where
  formalizes @ "claim:the-finite-weighted-positive-lyapunov-sum-is-positively-homogeneous-on-action-directions",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorem-8.8",
  caveat @ "claim:together-with-same-cone-additivity-this-proves-piecewise-linearity-only-for-the-defined-finite-sum"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_subadd where
  formalizes @ "claim:nonnegative-finite-weighted-lyapunov-entropy-is-globally-subadditive-and-exactly-additive-inside-a-common-weyl-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorem-8.8",
  caveat @ "claim:this-is-a-convexity-property-of-the-defined-exponent-sum-not-a-standalone-metric-entropy-theorem"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.margulisRuelleCapacity_neg_eq_of_signedSum_eq_zero where
  formalizes @ "claim:zero-signed-lyapunov-sum-makes-positive-exponent-capacity-symmetric-under-action-reversal",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-section-15.1",
  caveat @ "claim:the-zero-signed-sum-is-visible-input-and-must-be-derived-separately-from-volume-preservation-of-a-concrete-cocycle"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseEntropy_saturation_rigidity where
  formalizes @ "claim:finite-componentwise-entropy-bounds-plus-total-saturation-force-every-coarse-component-to-saturate",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-theorem-9.5",
  caveat @ "claim:this-is-the-finite-order-rigidity-step-and-does-not-by-itself-prove-invariance-under-a-foliation-subgroup"

zil attach Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.resonantRoot_card_le where
  formalizes @ "claim:pairwise-coarse-distinct-roots-resonant-with-fiberwise-exponents-are-bounded-in-number-by-the-fiberwise-exponent-slots",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:Brown-Entropy-Lyapunov-Exponents-Rigidity-arXiv-1809.09192v4-remark-15.6",
  caveat @ "claim:this-proves-the-finite-resonance-counting-step-not-the-nonresonance-implies-subgroup-invariance-principle"

zil_file_contract physlib.derivativeCocycleHyperbolicity where
  promises "Intrinsic derivative cocycles for iterates and smooth additive group actions with continuous stable-bundle geometry, extended by the finite algebraic entropy-Lyapunov layer: coarse-class hyperplanes and signs, regular directions, Margulis-Ruelle capacity, convex Weyl-cone geometry, stable/unstable balance, saturation rigidity, and fiber-resonance counting."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Diffeomorph", "lean:SmoothAdditiveDiffeomorphismAction",
    "lean:mfderiv", "lean:TangentBundle",
    "lean:RiemannianBundle", "lean:Submodule.prodEquivOfIsCompl"]
  forbids_substitutes ["an abstract label presented as an Anosov diffeomorphism",
    "a pointwise splitting presented as continuous without tangent-bundle projection continuity",
    "existence of stable bundles for an arbitrary diffeomorphism",
    "a supplied exponent family presented as a constructed Oseledets splitting",
    "an algebraic weighted exponent sum presented as Kolmogorov-Sinai entropy without analytic hypotheses",
    "finite sum saturation presented as SRB or subgroup-invariance rigidity",
    "volume-preserving capacity symmetry without a proved zero signed Lyapunov sum",
    "finite nonresonance counting presented as a subgroup-invariance theorem"]
  witnessed_by [
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.derivativeCocycle_add,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.higherRankDerivativeCocycle_add,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.InvariantSplitting.derivative_components,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.HyperbolicSplitting.stable_tendsto_zero,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.HyperbolicSplitting.unstable_backward_tendsto_zero,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseLyapunovEquivalent_sign,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseLyapunovEquivalent_ker_eq,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.isRegularLyapunovDirection_iff_of_pointwise_coarse,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_le_margulisRuelleCapacity,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_eq_capacity_iff_fullDimension,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_smul_of_nonneg,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_add_of_sameClosedWeylCone,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.weightedLyapunovEntropy_subadd,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.margulisRuelleCapacity_neg_eq_of_signedSum_eq_zero,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.coarseEntropy_saturation_rigidity,
    Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.resonantRoot_card_le]

/- ZIL-END -/
