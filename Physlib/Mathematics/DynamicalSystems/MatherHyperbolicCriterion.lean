/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.DynamicalSystems.MatherSpectrum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Tactic
meta import Zil

/-!
# The forward Mather hyperbolicity criterion

This module proves the analytic implication that was left open by `MatherSpectrum`.
For an invertible complex bounded operator `T` with commuting stable and unstable projections,
assume uniform geometric bounds

`‖Tⁿ Pₛ‖ ≤ C λⁿ`,  `‖T⁻⁽ⁿ⁺¹⁾ Pᵤ‖ ≤ C λⁿ⁺¹`,  with `0 ≤ λ < 1`.

The two operator-norm Green series

`Gₛ = ∑ n, Tⁿ Pₛ`,  `Gᵤ = ∑ n, T⁻⁽ⁿ⁺¹⁾ Pᵤ`

then converge in the genuine Banach algebra of continuous linear endomorphisms, and
`Gₛ - Gᵤ` is a two-sided inverse of `1 - T`.  Consequently `1 ∉ spectrum ℂ T`.
Specializing `T` to the complex bounded weighted-composition operator from `MatherSpectrum`
gives the forward, spectral half of Mather's criterion.

## Honest scope

`HyperbolicOperatorSplitting` contains the global operator-norm estimates that make the Green
series converge.  The preceding geometric module constructs intrinsic continuous invariant
stable/unstable tangent bundles and their fiberwise estimates.  Passing from those data to the
operator bounds below additionally requires uniform control of the chosen global frame and its
coordinate projections.  That system-specific comparison is not hidden here.

This module proves the forward implication from the explicit operator splitting.  It does not
prove Mather's converse, the annular structure of spectral components, or density hypotheses on
nonperiodic points.
-/

set_option autoImplicit false

noncomputable section

@[expose] public section

namespace Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion

universe u v w

/-! ## A. Uniform hyperbolicity in a complex Banach operator algebra -/

variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A genuine stable/unstable splitting for an invertible bounded complex operator, together
with the uniform geometric estimates needed by the Green-series resolvent construction.

The algebraic projection fields record that this really is a complementary splitting; the
analytic proof uses their sum, commutation with `T`, and the two power bounds. -/
structure HyperbolicOperatorSplitting (T : X →L[ℂ] X) where
  /-- The bounded two-sided inverse of `T`. -/
  inverse : X →L[ℂ] X
  /-- The inverse cancels `T` on the left. -/
  inverse_mul : inverse * T = 1
  /-- The inverse cancels `T` on the right. -/
  mul_inverse : T * inverse = 1
  /-- Stable projection. -/
  stableProjection : X →L[ℂ] X
  /-- Unstable projection. -/
  unstableProjection : X →L[ℂ] X
  /-- The stable projection is idempotent. -/
  stable_idempotent : stableProjection * stableProjection = stableProjection
  /-- The unstable projection is idempotent. -/
  unstable_idempotent : unstableProjection * unstableProjection = unstableProjection
  /-- Stable then unstable projection vanishes. -/
  stable_unstable_zero : stableProjection * unstableProjection = 0
  /-- Unstable then stable projection vanishes. -/
  unstable_stable_zero : unstableProjection * stableProjection = 0
  /-- The two complementary projections sum to the identity. -/
  projection_sum : stableProjection + unstableProjection = 1
  /-- The stable projection commutes with the evolution. -/
  stable_commutes : Commute stableProjection T
  /-- The unstable projection commutes with the evolution. -/
  unstable_commutes : Commute unstableProjection T
  /-- Common multiplicative constant for the geometric estimates. -/
  C : ℝ
  /-- Nonnegativity of the common constant. -/
  C_nonneg : 0 ≤ C
  /-- Common contraction factor. -/
  contraction : ℝ
  /-- Nonnegativity of the contraction factor. -/
  contraction_nonneg : 0 ≤ contraction
  /-- Strict contraction. -/
  contraction_lt_one : contraction < 1
  /-- Uniform forward contraction on the stable projection. -/
  stable_power_bound : ∀ n,
    ‖T ^ n * stableProjection‖ ≤ C * contraction ^ n
  /-- Uniform backward contraction on the unstable projection. -/
  unstable_inverse_power_bound : ∀ n,
    ‖inverse ^ (n + 1) * unstableProjection‖ ≤ C * contraction ^ (n + 1)

namespace HyperbolicOperatorSplitting

variable {T : X →L[ℂ] X}

/-- The `n`th stable Green-series term. -/
def stableTerm (S : HyperbolicOperatorSplitting T) (n : ℕ) : X →L[ℂ] X :=
  T ^ n * S.stableProjection

/-- The `n`th unstable Green-series term, starting at inverse power one. -/
def unstableTerm (S : HyperbolicOperatorSplitting T) (n : ℕ) : X →L[ℂ] X :=
  S.inverse ^ (n + 1) * S.unstableProjection

/-- The stable Green series converges in operator norm. -/
lemma stableTerm_summable (S : HyperbolicOperatorSplitting T) :
    Summable S.stableTerm := by
  apply Summable.of_norm_bounded
    (Summable.mul_left S.C
      (summable_geometric_of_lt_one S.contraction_nonneg S.contraction_lt_one))
  exact S.stable_power_bound

/-- The unstable Green series converges in operator norm. -/
lemma unstableTerm_summable (S : HyperbolicOperatorSplitting T) :
    Summable S.unstableTerm := by
  have hgeometric :
      Summable (fun n => S.C * S.contraction ^ n) :=
    Summable.mul_left S.C
      (summable_geometric_of_lt_one S.contraction_nonneg S.contraction_lt_one)
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hgeometric)
  intro n
  simpa [unstableTerm, add_assoc] using S.unstable_inverse_power_bound n

/-- The stable Green operator `∑ n, Tⁿ Pₛ`. -/
def stableGreen (S : HyperbolicOperatorSplitting T) : X →L[ℂ] X :=
  ∑' n, S.stableTerm n

/-- The unstable Green operator `∑ n, T⁻⁽ⁿ⁺¹⁾ Pᵤ`. -/
def unstableGreen (S : HyperbolicOperatorSplitting T) : X →L[ℂ] X :=
  ∑' n, S.unstableTerm n

/-- The candidate inverse of `1 - T`: stable forward Green series minus unstable backward
Green series. -/
def greenInverse (S : HyperbolicOperatorSplitting T) : X →L[ℂ] X :=
  S.stableGreen - S.unstableGreen

/-- The stable Green series is a left inverse of `1 - T` on the stable subspace. -/
lemma one_sub_mul_stableGreen (S : HyperbolicOperatorSplitting T) :
    (1 - T) * S.stableGreen = S.stableProjection := by
  have hs := S.stableTerm_summable
  have hshift :
      T * S.stableGreen = ∑' n, S.stableTerm (n + 1) := by
    rw [stableGreen, ← hs.tsum_mul_left T]
    apply tsum_congr
    intro n
    simp [stableTerm, pow_succ', mul_assoc]
  rw [sub_mul, one_mul, hshift]
  calc
    S.stableGreen - (∑' n, S.stableTerm (n + 1)) =
        (S.stableTerm 0 + ∑' n, S.stableTerm (n + 1)) -
          ∑' n, S.stableTerm (n + 1) := by
            rw [stableGreen, hs.tsum_eq_zero_add]
    _ = S.stableProjection := by simp [stableTerm]

/-- The stable Green series is a right inverse of `1 - T` on the stable subspace. -/
lemma stableGreen_mul_one_sub (S : HyperbolicOperatorSplitting T) :
    S.stableGreen * (1 - T) = S.stableProjection := by
  have hs := S.stableTerm_summable
  have hshift :
      S.stableGreen * T = ∑' n, S.stableTerm (n + 1) := by
    rw [stableGreen, ← hs.tsum_mul_right T]
    apply tsum_congr
    intro n
    simp only [stableTerm]
    calc
      (T ^ n * S.stableProjection) * T =
          T ^ n * (S.stableProjection * T) := by ac_rfl
      _ = T ^ n * (T * S.stableProjection) := by rw [S.stable_commutes.eq]
      _ = T ^ (n + 1) * S.stableProjection := by
        rw [pow_succ]
        ac_rfl
  rw [mul_sub, mul_one, hshift]
  calc
    S.stableGreen - (∑' n, S.stableTerm (n + 1)) =
        (S.stableTerm 0 + ∑' n, S.stableTerm (n + 1)) -
          ∑' n, S.stableTerm (n + 1) := by
            rw [stableGreen, hs.tsum_eq_zero_add]
    _ = S.stableProjection := by simp [stableTerm]

/-- Adding the missing zeroth inverse-power term preserves summability. -/
lemma inverse_pow_summable (S : HyperbolicOperatorSplitting T) :
    Summable (fun n => S.inverse ^ n * S.unstableProjection) := by
  apply (summable_nat_add_iff 1).mp
  change Summable S.unstableTerm
  exact S.unstableTerm_summable

/-- Multiplication by `T` shifts the unstable Green series backward by one term. -/
lemma mul_unstableGreen (S : HyperbolicOperatorSplitting T) :
    T * S.unstableGreen = S.unstableProjection + S.unstableGreen := by
  have hu := S.unstableTerm_summable
  have hall := S.inverse_pow_summable
  rw [unstableGreen, ← hu.tsum_mul_left T]
  calc
    (∑' n, T * S.unstableTerm n) =
        ∑' n, S.inverse ^ n * S.unstableProjection := by
      apply tsum_congr
      intro n
      simp only [unstableTerm]
      rw [pow_succ']
      calc
        T * (S.inverse * S.inverse ^ n) * S.unstableProjection =
            (T * S.inverse) * S.inverse ^ n * S.unstableProjection := by ac_rfl
        _ = S.inverse ^ n * S.unstableProjection := by
          rw [S.mul_inverse, one_mul]
    _ = S.unstableProjection + S.unstableGreen := by
      rw [hall.tsum_eq_zero_add]
      simp [unstableGreen, unstableTerm]

/-- Right multiplication by `T` gives the same unstable Green shift. -/
lemma unstableGreen_mul (S : HyperbolicOperatorSplitting T) :
    S.unstableGreen * T = S.unstableProjection + S.unstableGreen := by
  have hu := S.unstableTerm_summable
  have hall := S.inverse_pow_summable
  rw [unstableGreen, ← hu.tsum_mul_right T]
  calc
    (∑' n, S.unstableTerm n * T) =
        ∑' n, S.inverse ^ n * S.unstableProjection := by
      apply tsum_congr
      intro n
      simp only [unstableTerm]
      calc
        (S.inverse ^ (n + 1) * S.unstableProjection) * T =
            S.inverse ^ (n + 1) * (S.unstableProjection * T) := by ac_rfl
        _ = S.inverse ^ (n + 1) * (T * S.unstableProjection) := by
          rw [S.unstable_commutes.eq]
        _ = S.inverse ^ n * S.unstableProjection := by
          rw [pow_succ]
          calc
            S.inverse ^ n * S.inverse * T * S.unstableProjection =
                S.inverse ^ n * (S.inverse * T) * S.unstableProjection := by
                  ac_rfl
            _ = S.inverse ^ n * S.unstableProjection := by
              rw [S.inverse_mul, mul_one]
    _ = S.unstableProjection + S.unstableGreen := by
      rw [hall.tsum_eq_zero_add]
      simp [unstableGreen, unstableTerm]

/-- The negative unstable Green series is a left inverse on the unstable subspace. -/
lemma one_sub_mul_neg_unstableGreen (S : HyperbolicOperatorSplitting T) :
    (1 - T) * (-S.unstableGreen) = S.unstableProjection := by
  rw [mul_neg, sub_mul, one_mul, S.mul_unstableGreen]
  abel

/-- The negative unstable Green series is a right inverse on the unstable subspace. -/
lemma neg_unstableGreen_mul_one_sub (S : HyperbolicOperatorSplitting T) :
    (-S.unstableGreen) * (1 - T) = S.unstableProjection := by
  rw [neg_mul, mul_sub, mul_one, S.unstableGreen_mul]
  abel

/-- The Green operator is a left inverse of `1 - T`. -/
theorem one_sub_mul_greenInverse (S : HyperbolicOperatorSplitting T) :
    (1 - T) * S.greenInverse = 1 := by
  rw [greenInverse, mul_sub, S.one_sub_mul_stableGreen]
  have hu := S.one_sub_mul_neg_unstableGreen
  rw [mul_neg] at hu
  calc
    S.stableProjection - (1 - T) * S.unstableGreen =
        S.stableProjection + S.unstableProjection := by
          rw [sub_eq_add_neg, hu]
    _ = 1 := S.projection_sum

/-- The Green operator is a right inverse of `1 - T`. -/
theorem greenInverse_mul_one_sub (S : HyperbolicOperatorSplitting T) :
    S.greenInverse * (1 - T) = 1 := by
  rw [greenInverse, sub_mul, S.stableGreen_mul_one_sub]
  have hu := S.neg_unstableGreen_mul_one_sub
  rw [neg_mul] at hu
  calc
    S.stableProjection - S.unstableGreen * (1 - T) =
        S.stableProjection + S.unstableProjection := by
          rw [sub_eq_add_neg, hu]
    _ = 1 := S.projection_sum

/-- **Green-series inverse theorem.**  Uniform stable/unstable hyperbolicity makes `1 - T`
a unit of the complex Banach operator algebra. -/
theorem one_sub_isUnit (S : HyperbolicOperatorSplitting T) :
    IsUnit (1 - T) := by
  apply isUnit_iff_exists.mpr
  exact ⟨S.greenInverse, S.one_sub_mul_greenInverse,
    S.greenInverse_mul_one_sub⟩

/-- **Forward hyperbolic spectral criterion.**  The spectral value one is excluded. -/
theorem one_not_mem_spectrum (S : HyperbolicOperatorSplitting T) :
    (1 : ℂ) ∉ spectrum ℂ T := by
  rw [spectrum.notMem_iff]
  simpa using S.one_sub_isUnit

end HyperbolicOperatorSplitting

/-! ## B. Specialization to the genuine complex Mather spectrum -/

open Physlib.Mathematics.DynamicalSystems.MatherSpectrum

variable {M : Type v} {Y : Type w}
variable [TopologicalSpace M] [CompactSpace M]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- **Forward Mather criterion on the compact continuum section carrier.**
An explicit uniform hyperbolic splitting of the bounded Mather weighted-composition operator
excludes one from its genuine complex Banach spectrum. -/
theorem one_not_mem_matherSpectrum
    (g : M ≃ₜ M) (A : C(M, Y →L[ℂ] Y))
    (S : HyperbolicOperatorSplitting (weightedComposition g A)) :
    (1 : ℂ) ∉ matherSpectrum g A :=
  S.one_not_mem_spectrum

variable {E₀ : Type*}
variable [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

/-- The same forward Mather criterion for a cocycle carrying an explicit real-to-complex
intertwining witness.  Thus the excluded spectral value belongs to the complexification of the
real derivative cocycle rather than to an unrelated complex operator. -/
theorem ComplexCocycleExtension.one_not_mem_spectrum
    {A : C(M, E₀ →L[ℝ] E₀)}
    (J : ComplexCocycleExtension (X := Y) A)
    (g : M ≃ₜ M)
    (S : HyperbolicOperatorSplitting (weightedComposition g J.cocycle)) :
    (1 : ℂ) ∉ J.spectrum g :=
  S.one_not_mem_spectrum

/-! ## C. Intrinsic derivative geometry, coordinates, and spectrum in one carrier -/

open scoped Bundle Manifold ContDiff Topology BoundedContinuousFunction
open Bundle Manifold
open Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity

variable {E : Type u} {H : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [TopologicalSpace H] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 1 M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- A single honest carrier tying together:

1. the intrinsic continuous hyperbolic tangent splitting of `Φ`;
2. a global linear frame and the exact real coordinate derivative cocycle;
3. an explicit complexification of that same real cocycle; and
4. the uniform operator estimates used by the Green inverse.

The final field is deliberately explicit: a system-specific proof must transport the intrinsic
fiber estimates through its chosen frame with uniform constants. -/
structure FramedComplexHyperbolicMatherData
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ]
    (Φ : Diffeomorph I I M M 1)
    (hcont : Continuous (realMatherCocycleAt I e Φ))
    (J : ComplexCocycleExtension (X := Y)
      (realMatherCocycle I e Φ hcont)) where
  /-- The chosen linear tangent frame covers the whole manifold. -/
  frame_global : e.baseSet = Set.univ
  /-- Intrinsic continuous stable/unstable tangent geometry. -/
  geometric : HyperbolicSplitting I Φ
  /-- Uniform complex operator estimates for the coordinate Mather operator. -/
  operator : HyperbolicOperatorSplitting
    (weightedComposition Φ.toHomeomorph J.cocycle)

/-- **Intrinsic-to-spectral capstone.**  The bundled data simultaneously gives:

1. intrinsic Anosov data on the genuine tangent bundle;
2. exact conjugacy of intrinsic Mather evolution with the real coordinate
   weighted-composition operator; and
3. exclusion of one from the genuine spectrum of the explicit complexification.

Thus the geometric and spectral statements cannot refer to unrelated dynamics. -/
theorem FramedComplexHyperbolicMatherData.intrinsic_conjugacy_and_spectral
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [e.IsLinear ℝ]
    (Φ : Diffeomorph I I M M 1)
    (hcont : Continuous (realMatherCocycleAt I e Φ))
    (J : ComplexCocycleExtension (X := Y)
      (realMatherCocycle I e Φ hcont))
    (D : FramedComplexHyperbolicMatherData I e Φ hcont J) :
    IsAnosovDiffeomorph I Φ ∧
      (∀ V,
        tangentSectionCoordinates I e D.frame_global
            (MatherVectorFieldOperator.matherOperator I Φ V) =
          weightedComposition Φ.toHomeomorph (realMatherCocycle I e Φ hcont)
            (tangentSectionCoordinates I e D.frame_global V)) ∧
      (1 : ℂ) ∉ J.spectrum Φ.toHomeomorph :=
  ⟨⟨D.geometric⟩,
    fun V => tangentSectionCoordinates_matherOperator
      I e D.frame_global Φ hcont V,
    ComplexCocycleExtension.one_not_mem_spectrum
      J Φ.toHomeomorph D.operator⟩

end Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.stableTerm_summable where
  formalizes @ "claim:uniform-stable-hyperbolicity-makes-the-forward-operator-green-series-converge-in-operator-norm",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:summable_geometric_of_lt_one",
  caveat @ "claim:the-uniform-operator-power-bound-is-explicit-input-and-is-not-inferred-from-an-uncontrolled-frame"

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.unstableTerm_summable where
  formalizes @ "claim:uniform-unstable-backward-hyperbolicity-makes-the-inverse-operator-green-series-converge-in-operator-norm",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:summable_geometric_of_lt_one",
  caveat @ "claim:the-bounded-two-sided-inverse-and-backward-power-bound-are-explicit-data"

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.one_sub_isUnit where
  formalizes @ "claim:the-stable-minus-unstable-green-series-is-a-two-sided-inverse-of-one-minus-the-hyperbolic-operator",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.one_sub_mul_greenInverse",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.greenInverse_mul_one_sub",
  caveat @ "claim:this-is-a-banach-operator-green-series-result-under-explicit-uniform-hyperbolicity"

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.one_not_mem_matherSpectrum where
  formalizes @ "claim:uniform-complex-mather-hyperbolicity-excludes-one-from-the-genuine-complex-banach-spectrum",
  epistemic_status @ "conditional-model",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms",
  supported_by @ "lean:spectrum.notMem_iff",
  caveat @ "claim:this-proves-the-forward-spectral-implication-only-the-converse-and-annular-spectrum-components-remain-unproved"

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.ComplexCocycleExtension.one_not_mem_spectrum where
  formalizes @ "claim:the-forward-mather-spectral-exclusion-applies-to-an-explicit-complexification-of-the-real-derivative-cocycle",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherSpectrum.ComplexCocycleExtension.weightedComposition_intertwines",
  caveat @ "claim:construction-of-the-uniform-coordinate-operator-bounds-from-a-specific-geometric-frame-remains-system-specific"

zil attach Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.FramedComplexHyperbolicMatherData.intrinsic_conjugacy_and_spectral where
  formalizes @ "claim:one-carrier-links-intrinsic-anosov-tangent-geometry-exact-real-mather-coordinate-conjugacy-and-complex-spectral-exclusion",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity.HyperbolicSplitting",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherSpectrum.tangentSectionCoordinates_matherOperator",
  supported_by @ "lean:Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.ComplexCocycleExtension.one_not_mem_spectrum",
  caveat @ "claim:uniform-comparison-of-fiberwise-hyperbolicity-with-the-global-frame-operator-norm-is-an-explicit-system-specific-field"

zil_file_contract physlib.matherHyperbolicCriterion where
  promises "The forward Mather spectral criterion on the genuine compact continuum section carrier: convergent stable and unstable Banach-operator Green series, an explicit two-sided inverse of one minus the Mather operator, and exclusion of one from the explicitly complexified Mather spectrum."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.DynamicalSystems.MatherSpectrum.weightedComposition",
    "lean:Physlib.Mathematics.DynamicalSystems.MatherSpectrum.matherSpectrum",
    "lean:summable_geometric_of_lt_one",
    "lean:spectrum.notMem_iff"]
  forbids_substitutes [
    "a finite matrix relabelled as the continuum Mather operator",
    "formal operator series without operator-norm summability",
    "claiming fiberwise hyperbolicity automatically supplies frame-uniform operator bounds",
    "claiming the converse Mather theorem or the annular-component theorem"]
  witnessed_by [
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.stableTerm_summable,
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.unstableTerm_summable,
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.HyperbolicOperatorSplitting.one_sub_isUnit,
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.one_not_mem_matherSpectrum,
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.ComplexCocycleExtension.one_not_mem_spectrum,
    Physlib.Mathematics.DynamicalSystems.MatherHyperbolicCriterion.FramedComplexHyperbolicMatherData.intrinsic_conjugacy_and_spectral]

/- ZIL-END -/
