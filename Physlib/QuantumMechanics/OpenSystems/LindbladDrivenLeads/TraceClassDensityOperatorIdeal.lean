/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumSemigroupClosure
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.TraceClassDensityOperatorIdeal -/

/-!
# Infinite trace-class ideal and density operators

This file supplies the operator ideal missing from the continuum Hilbert--Schmidt semigroup layer.
For a complex Hilbert space `H`, `IsTraceClass T` means that `T` has a nuclear rank-one
decomposition

`T = ∑' n, |left n><right n|`

whose cost `∑ n, ‖left n‖ * ‖right n‖` is finite.  This is the standard nuclear definition of
trace class on Hilbert spaces.  The construction is genuinely infinite-dimensional and proves
closure under addition, scalar multiplication, adjoint, and arbitrary bounded left and right
composition.  It also proves that every such operator is compact.

`TraceClassDensityOperator` bundles a countable spectral resolution with nonnegative summable
weights of total mass one.  Its operator is proved positive, trace class, compact, and normalized;
finite spectral truncations converge in operator norm, weak-operator topology, and spectral trace.

Honest boundary: the density carrier asks for the spectral resolution explicitly.  This file does
not claim a new enumeration form of the infinite-dimensional spectral theorem, nor a
representation-independent trace for arbitrary nonnormal nuclear decompositions.  Operator-norm
limits alone do not preserve trace class; every limit below is controlled by an explicit
summable nuclear series.
-/

set_option autoImplicit false

open Filter NormedSpace
open scoped Topology InnerProductSpace ComplexOrder

@[expose] public section

namespace QuantumMechanics.LindbladDrivenLeads

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def interleave {α : Type*} (f g : ℕ → α) (n : ℕ) : α :=
  Sum.elim f g (Equiv.natSumNatEquivNat.symm n)

@[simp] lemma interleave_even {α : Type*} (f g : ℕ → α) (n : ℕ) :
    interleave f g (2 * n) = f n := by
  unfold interleave
  have h := Equiv.natSumNatEquivNat.symm_apply_apply (Sum.inl n)
  rw [Equiv.natSumNatEquivNat_apply] at h
  simpa using congrArg (Sum.elim f g) h

@[simp] lemma interleave_odd {α : Type*} (f g : ℕ → α) (n : ℕ) :
    interleave f g (2 * n + 1) = g n := by
  unfold interleave
  have h := Equiv.natSumNatEquivNat.symm_apply_apply (Sum.inr n)
  rw [Equiv.natSumNatEquivNat_apply] at h
  simpa using congrArg (Sum.elim f g) h

structure TraceClassDecomposition (T : H →L[ℂ] H) where
  left : ℕ → H
  right : ℕ → H
  summable_cost : Summable (fun n => ‖left n‖ * ‖right n‖)
  hasSum_operator :
    HasSum (fun n => InnerProductSpace.rankOne ℂ (left n) (right n)) T

def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  Nonempty (TraceClassDecomposition T)

namespace TraceClassDecomposition

def zero : TraceClassDecomposition (0 : H →L[ℂ] H) where
  left := 0
  right := 0
  summable_cost := by simp
  hasSum_operator := by simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : H →L[ℂ] H)) 0)

def add {S T : H →L[ℂ] H}
    (P : TraceClassDecomposition S) (Q : TraceClassDecomposition T) :
    TraceClassDecomposition (S + T) where
  left := interleave P.left Q.left
  right := interleave P.right Q.right
  summable_cost := by
    apply Summable.even_add_odd
    · simpa using P.summable_cost
    · simpa using Q.summable_cost
  hasSum_operator := by
    apply HasSum.even_add_odd
    · simpa using P.hasSum_operator
    · simpa using Q.hasSum_operator

def smul (c : ℂ) {T : H →L[ℂ] H}
    (P : TraceClassDecomposition T) :
    TraceClassDecomposition (c • T) where
  left := fun n => c • P.left n
  right := P.right
  summable_cost := by
    simpa [norm_smul, mul_assoc] using P.summable_cost.mul_left ‖c‖
  hasSum_operator := by
    have h := P.hasSum_operator.const_smul c
    simpa [InnerProductSpace.rankOne_apply, inner_smul_left,
      mul_comm, mul_left_comm, mul_assoc] using h

def comp_left (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (P : TraceClassDecomposition T) :
    TraceClassDecomposition (A * T) where
  left := fun n => A (P.left n)
  right := P.right
  summable_cost := by
    apply Summable.of_nonneg_of_le
    · intro n; positivity
    · intro n
      calc
        ‖A (P.left n)‖ * ‖P.right n‖
            ≤ (‖A‖ * ‖P.left n‖) * ‖P.right n‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = ‖A‖ * (‖P.left n‖ * ‖P.right n‖) := by ring
    · exact P.summable_cost.mul_left ‖A‖
  hasSum_operator := by
    have h := P.hasSum_operator.mul_left A
    rw [show
      (fun n => InnerProductSpace.rankOne ℂ (A (P.left n)) (P.right n)) =
        (fun n => A * InnerProductSpace.rankOne ℂ (P.left n) (P.right n)) by
      funext n
      exact (InnerProductSpace.comp_rankOne _ _ _).symm]
    exact h

def comp_right (A : H →L[ℂ] H) {T : H →L[ℂ] H}
    (P : TraceClassDecomposition T) :
    TraceClassDecomposition (T * A) where
  left := P.left
  right := fun n => A.adjoint (P.right n)
  summable_cost := by
    apply Summable.of_nonneg_of_le
    · intro n; positivity
    · intro n
      calc
        ‖P.left n‖ * ‖A.adjoint (P.right n)‖
            ≤ ‖P.left n‖ * (‖A.adjoint‖ * ‖P.right n‖) :=
          mul_le_mul_of_nonneg_left (A.adjoint.le_opNorm _) (norm_nonneg _)
        _ = ‖A‖ * (‖P.left n‖ * ‖P.right n‖) := by
          rw [ContinuousLinearMap.adjoint.norm_map]
          ring
    · exact P.summable_cost.mul_left ‖A‖
  hasSum_operator := by
    have h := P.hasSum_operator.mul_right A
    rw [show
      (fun n => InnerProductSpace.rankOne ℂ (P.left n) (A.adjoint (P.right n))) =
        (fun n => InnerProductSpace.rankOne ℂ (P.left n) (P.right n) * A) by
      funext n
      exact (InnerProductSpace.rankOne_comp _ _ _).symm]
    exact h

def adjoint {T : H →L[ℂ] H}
    (P : TraceClassDecomposition T) :
    TraceClassDecomposition T.adjoint where
  left := P.right
  right := P.left
  summable_cost := by
    simpa [mul_comm] using P.summable_cost
  hasSum_operator := by
    have h := P.hasSum_operator.map ContinuousLinearMap.adjoint
      ContinuousLinearMap.adjoint.continuous
    rw [show
      (fun n => InnerProductSpace.rankOne ℂ (P.right n) (P.left n)) =
        (ContinuousLinearMap.adjoint ∘
          fun n => InnerProductSpace.rankOne ℂ (P.left n) (P.right n)) by
      funext n
      exact (InnerProductSpace.adjoint_rankOne _ _).symm]
    exact h

end TraceClassDecomposition

lemma isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) :=
  ⟨TraceClassDecomposition.zero⟩

lemma IsTraceClass.add {S T : H →L[ℂ] H}
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  rcases hS with ⟨P⟩
  rcases hT with ⟨Q⟩
  exact ⟨P.add Q⟩

lemma IsTraceClass.smul {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (c : ℂ) : IsTraceClass (c • T) := by
  rcases hT with ⟨P⟩
  exact ⟨P.smul c⟩

lemma IsTraceClass.neg {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsTraceClass (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1)

lemma IsTraceClass.sub {S T : H →L[ℂ] H}
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S - T) := by
  rw [sub_eq_add_neg]
  exact hS.add hT.neg

lemma IsTraceClass.comp_left {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (A : H →L[ℂ] H) : IsTraceClass (A * T) := by
  rcases hT with ⟨P⟩
  exact ⟨P.comp_left A⟩

lemma IsTraceClass.comp_right {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (A : H →L[ℂ] H) : IsTraceClass (T * A) := by
  rcases hT with ⟨P⟩
  exact ⟨P.comp_right A⟩

lemma IsTraceClass.adjoint {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsTraceClass T.adjoint := by
  rcases hT with ⟨P⟩
  exact ⟨P.adjoint⟩

lemma isTraceClass_rankOne (x y : H) :
    IsTraceClass (InnerProductSpace.rankOne ℂ x y) := by
  let P : TraceClassDecomposition (InnerProductSpace.rankOne ℂ x y) := {
    left := fun n => if n = 0 then x else 0
    right := fun n => if n = 0 then y else 0
    summable_cost := by
      rw [show
        (fun n : ℕ => ‖if n = 0 then x else 0‖ * ‖if n = 0 then y else 0‖) =
          (fun n => if n = 0 then ‖x‖ * ‖y‖ else 0) by
        funext n
        split <;> simp_all]
      exact (hasSum_ite_eq 0 (‖x‖ * ‖y‖)).summable
    hasSum_operator := by
      rw [show
        (fun n : ℕ =>
          InnerProductSpace.rankOne ℂ (if n = 0 then x else 0)
            (if n = 0 then y else 0)) =
          (fun n => if n = 0 then InnerProductSpace.rankOne ℂ x y else 0) by
        funext n
        split <;> simp_all]
      exact hasSum_ite_eq 0 (InnerProductSpace.rankOne ℂ x y)
  }
  exact ⟨P⟩

lemma rankOne_isCompact (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (innerSL ℂ y)).clm_comp (ContinuousLinearMap.toSpanSingleton ℂ x)

lemma IsTraceClass.isCompact {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsCompactOperator T := by
  rcases hT with ⟨P⟩
  apply isCompactOperator_of_tendsto P.hasSum_operator.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro N
  induction N with
  | zero =>
      simp
      exact isCompactOperator_zero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (rankOne_isCompact _ _)

/-- The trace-class operators as a complex linear subspace of bounded operators. -/
def traceClassSubmodule : Submodule ℂ (H →L[ℂ] H) where
  carrier := IsTraceClass
  zero_mem' := isTraceClass_zero
  add_mem' := IsTraceClass.add
  smul_mem' := fun c _ hT => hT.smul c

/-- The nuclear trace-class subspace is a two-sided operator ideal. -/
theorem traceClass_isTwoSidedIdeal :
    (∀ (A : H →L[ℂ] H) {T}, T ∈ traceClassSubmodule (H := H) →
      A * T ∈ traceClassSubmodule (H := H)) ∧
    (∀ (A : H →L[ℂ] H) {T}, T ∈ traceClassSubmodule (H := H) →
      T * A ∈ traceClassSubmodule (H := H)) := by
  constructor
  · intro A T hT
    exact hT.comp_left A
  · intro A T hT
    exact hT.comp_right A

/-! Spectral density operators. -/

lemma isSymmetric_of_norm_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : Tendsto A l (nhds T))
    (hSymm : ∀ i, (A i).IsSymmetric) :
    T.IsSymmetric := by
  intro x y
  have hx : Tendsto (fun i => A i x) l (nhds (T x)) :=
    ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp hA
  have hy : Tendsto (fun i => A i y) l (nhds (T y)) :=
    ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp hA
  have hleft : Tendsto (fun i => ⟪A i x, y⟫_ℂ) l
      (nhds ⟪T x, y⟫_ℂ) :=
    hx.inner tendsto_const_nhds
  have hright : Tendsto (fun i => ⟪x, A i y⟫_ℂ) l
      (nhds ⟪x, T y⟫_ℂ) :=
    tendsto_const_nhds.inner hy
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun i => (hSymm i x y).symm))

lemma isPositive_of_norm_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : Tendsto A l (nhds T))
    (hPos : ∀ i, (A i).IsPositive) :
    T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨isSymmetric_of_norm_tendsto hA (fun i => (hPos i).isSymmetric), ?_⟩
  intro x
  have hx : Tendsto (fun i => A i x) l (nhds (T x)) :=
    ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp hA
  have hinner : Tendsto (fun i => ⟪A i x, x⟫_ℂ) l
      (nhds ⟪T x, x⟫_ℂ) :=
    hx.inner tendsto_const_nhds
  exact ge_of_tendsto hinner
    (Filter.Eventually.of_forall fun i => (hPos i).inner_nonneg_left x)

/-- A positive trace-one operator supplied by a countable spectral resolution.

The spectral data are explicit because Mathlib does not currently expose the infinite-dimensional
spectral theorem in a form that enumerates every positive compact operator's eigenvectors. -/
structure TraceClassDensityOperator where
  basis : HilbertBasis ℕ ℂ H
  weight : ℕ → ℝ
  weight_nonneg : ∀ n, 0 ≤ weight n
  summable_weight : Summable weight
  trace_one : ∑' n, weight n = 1

namespace TraceClassDensityOperator

/-- The pure density state concentrated at one vector of a supplied Hilbert basis. -/
noncomputable def pure (b : HilbertBasis ℕ ℂ H) (k : ℕ) :
    TraceClassDensityOperator (H := H) where
  basis := b
  weight := fun n => if n = k then 1 else 0
  weight_nonneg := by
    intro n
    split <;> positivity
  summable_weight := (hasSum_ite_eq k (1 : ℝ)).summable
  trace_one := by
    exact tsum_ite_eq k (fun _ => (1 : ℝ))

/-- The `n`th positive rank-one spectral term. -/
noncomputable def term (ρ : TraceClassDensityOperator (H := H)) (n : ℕ) :
    H →L[ℂ] H :=
  (ρ.weight n : ℂ) • InnerProductSpace.rankOne ℂ (ρ.basis n) (ρ.basis n)

/-- The density operator obtained by summing its spectral resolution in operator norm. -/
noncomputable def operator (ρ : TraceClassDensityOperator (H := H)) :
    H →L[ℂ] H :=
  ∑' n, ρ.term n

/-- Finite-rank positive approximation retaining the first `N` spectral modes. -/
noncomputable def partialOperator (ρ : TraceClassDensityOperator (H := H)) (N : ℕ) :
    H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, ρ.term n

@[simp] theorem pure_operator
    (b : HilbertBasis ℕ ℂ H) (k : ℕ) :
    (pure b k).operator = InnerProductSpace.rankOne ℂ (b k) (b k) := by
  unfold operator
  rw [show
    (fun n => (pure b k).term n) =
      (fun n => if n = k then InnerProductSpace.rankOne ℂ (b k) (b k) else 0) by
    funext n
    split <;> simp_all [term, pure]]
  exact tsum_ite_eq k (fun _ => InnerProductSpace.rankOne ℂ (b k) (b k))

lemma norm_term (ρ : TraceClassDensityOperator (H := H)) (n : ℕ) :
    ‖ρ.term n‖ = ρ.weight n := by
  simp [term, norm_smul, InnerProductSpace.norm_rankOne,
    ρ.basis.orthonormal.norm_eq_one, abs_of_nonneg (ρ.weight_nonneg n)]

lemma summable_term (ρ : TraceClassDensityOperator (H := H)) :
    Summable ρ.term := by
  apply Summable.of_norm
  simpa only [ρ.norm_term] using ρ.summable_weight

lemma hasSum_operator (ρ : TraceClassDensityOperator (H := H)) :
    HasSum ρ.term ρ.operator :=
  ρ.summable_term.hasSum

lemma partialOperator_tendsto (ρ : TraceClassDensityOperator (H := H)) :
    Tendsto ρ.partialOperator atTop (nhds ρ.operator) := by
  exact ρ.hasSum_operator.tendsto_sum_nat

lemma term_isPositive (ρ : TraceClassDensityOperator (H := H)) (n : ℕ) :
    (ρ.term n).IsPositive := by
  exact (InnerProductSpace.isPositive_rankOne_self (ρ.basis n)).smul_of_nonneg
    (by exact_mod_cast ρ.weight_nonneg n)

lemma partialOperator_isPositive (ρ : TraceClassDensityOperator (H := H)) (N : ℕ) :
    (ρ.partialOperator N).IsPositive := by
  unfold partialOperator
  exact ContinuousLinearMap.isPositive_sum _ fun n _ => ρ.term_isPositive n

lemma operator_isPositive (ρ : TraceClassDensityOperator (H := H)) :
    ρ.operator.IsPositive :=
  isPositive_of_norm_tendsto ρ.partialOperator_tendsto ρ.partialOperator_isPositive

lemma operator_isTraceClass (ρ : TraceClassDensityOperator (H := H)) :
    IsTraceClass ρ.operator := by
  let P : TraceClassDecomposition ρ.operator := {
    left := fun n => (ρ.weight n : ℂ) • ρ.basis n
    right := fun n => ρ.basis n
    summable_cost := by
      rw [show
        (fun n => ‖(ρ.weight n : ℂ) • ρ.basis n‖ * ‖ρ.basis n‖) =
          ρ.weight by
        funext n
        simp [norm_smul, ρ.basis.orthonormal.norm_eq_one,
          abs_of_nonneg (ρ.weight_nonneg n)]]
      exact ρ.summable_weight
    hasSum_operator := by
      rw [show
        (fun n => InnerProductSpace.rankOne ℂ
          ((ρ.weight n : ℂ) • ρ.basis n) (ρ.basis n)) = ρ.term by
        funext n
        simp [term, InnerProductSpace.rankOne_apply]]
      exact ρ.hasSum_operator
  }
  exact ⟨P⟩

/-- The spectral trace of the bundled positive operator. -/
noncomputable def trace (ρ : TraceClassDensityOperator (H := H)) : ℝ :=
  ∑' n, ρ.weight n

@[simp] theorem trace_eq_one (ρ : TraceClassDensityOperator (H := H)) :
    ρ.trace = 1 :=
  ρ.trace_one

/-- Finite spectral traces converge to the normalized trace. -/
theorem partialTrace_tendsto_one (ρ : TraceClassDensityOperator (H := H)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ρ.weight n) atTop (nhds 1) := by
  simpa [ρ.trace_one] using ρ.summable_weight.hasSum.tendsto_sum_nat

/-- The finite-rank approximants converge in the genuine weak-operator topology. -/
theorem partialOperator_WOT_tendsto (ρ : TraceClassDensityOperator (H := H)) :
    Tendsto (fun N =>
      QuantumMechanics.LindbladDrivenLeads.toWOT (ρ.partialOperator N)) atTop
      (nhds (QuantumMechanics.LindbladDrivenLeads.toWOT ρ.operator)) :=
  QuantumMechanics.LindbladDrivenLeads.norm_tendsto_implies_WOT
    ρ.partialOperator_tendsto

/-- A bounded reservoir sandwich preserves the trace-class ideal. -/
theorem reservoirSandwich_isTraceClass
    (ρ : TraceClassDensityOperator (H := H)) (L R : H →L[ℂ] H) :
    IsTraceClass (L * ρ.operator * R) :=
  (ρ.operator_isTraceClass.comp_left L).comp_right R

/-- A physical adjoint sandwich preserves positivity as well as trace class.

Normalization is not claimed without a separate trace-preserving/isometry hypothesis. -/
theorem adjointSandwich_isPositive_and_traceClass
    (ρ : TraceClassDensityOperator (H := H)) (A : H →L[ℂ] H) :
    (A * ρ.operator * A.adjoint).IsPositive ∧
      IsTraceClass (A * ρ.operator * A.adjoint) := by
  constructor
  · exact ρ.operator_isPositive.conj_adjoint A
  · exact (ρ.operator_isTraceClass.comp_left A).comp_right A.adjoint

/-- Capstone certificate for a normalized continuum density operator and its finite-mode
approximation. -/
theorem continuum_density_operator_certificate
    (ρ : TraceClassDensityOperator (H := H)) :
    ρ.operator.IsPositive
      ∧ IsTraceClass ρ.operator
      ∧ IsCompactOperator ρ.operator
      ∧ ρ.trace = 1
      ∧ Tendsto ρ.partialOperator atTop (nhds ρ.operator)
      ∧ Tendsto (fun N =>
          QuantumMechanics.LindbladDrivenLeads.toWOT (ρ.partialOperator N)) atTop
          (nhds (QuantumMechanics.LindbladDrivenLeads.toWOT ρ.operator))
      ∧ Tendsto (fun N => ∑ n ∈ Finset.range N, ρ.weight n) atTop (nhds 1) := by
  exact ⟨ρ.operator_isPositive, ρ.operator_isTraceClass,
    ρ.operator_isTraceClass.isCompact, ρ.trace_eq_one,
    ρ.partialOperator_tendsto, ρ.partialOperator_WOT_tendsto,
    ρ.partialTrace_tendsto_one⟩

end TraceClassDensityOperator

end

end QuantumMechanics.LindbladDrivenLeads

end

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.traceClass_isTwoSidedIdeal where
  formalizes @ "claim:the-nuclear-rank-one-summable-operators-on-an-arbitrary-complex-hilbert-space-form-a-two-sided-bounded-operator-ideal",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:InnerProductSpace.comp_rankOne",
  supported_by @ "lean:InnerProductSpace.rankOne_comp",
  caveat @ "claim:trace-class-is-defined-by-the-standard-nuclear-decomposition-on-a-hilbert-space-no-Schatten-singular-value-equivalence-is-reproved-here"

zil attach QuantumMechanics.LindbladDrivenLeads.TraceClassDensityOperator.adjointSandwich_isPositive_and_traceClass where
  formalizes @ "claim:bounded-adjoint-sandwiches-preserve-positivity-and-the-infinite-trace-class-ideal",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ContinuousLinearMap.IsPositive.conj_adjoint",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.traceClass_isTwoSidedIdeal",
  caveat @ "claim:normalization-is-not-preserved-without-a-separate-trace-preserving-or-isometry-hypothesis"

zil attach QuantumMechanics.LindbladDrivenLeads.TraceClassDensityOperator.continuum_density_operator_certificate where
  formalizes @ "claim:a-countable-nonnegative-spectral-resolution-of-total-weight-one-constructs-a-positive-compact-trace-class-density-operator-with-norm-WOT-and-trace-convergent-finite-rank-approximants",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:InnerProductSpace.isPositive_rankOne_self",
  supported_by @ "lean:ContinuousLinearMapWOT.continuous_ofCLM",
  supported_by @ "lean:isCompactOperator_of_tendsto",
  caveat @ "claim:the-spectral-resolution-is-supplied-data-this-does-not-reprove-the-general-infinite-dimensional-spectral-theorem-or-a-basis-independent-trace-on-arbitrary-nonnormal-nuclear-operators"

zil_file_contract physlib.lindbladDrivenLeads.traceClassDensityOperatorIdeal where
  promises "On every complex Hilbert space, summable nuclear rank-one decompositions form an adjoint-stable two-sided ideal of compact operators. A supplied countable positive spectral resolution with weights summing to one constructs a normalized positive trace-class density operator whose finite-rank truncations converge in operator norm, WOT, and spectral trace; bounded adjoint sandwiches preserve positivity and trace class."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:InnerProductSpace.rankOne",
    "lean:InnerProductSpace.comp_rankOne",
    "lean:ContinuousLinearMap.IsPositive.conj_adjoint",
    "lean:ContinuousLinearMapWOT.continuous_ofCLM"]
  forbids_substitutes ["a finite matrix carrier relabeled as trace class",
    "claiming operator-norm closure of the trace-class ideal",
    "claiming arbitrary sandwiches preserve trace one",
    "claiming a representation-independent trace without a nuclear trace theorem"]
  witnessed_by [QuantumMechanics.LindbladDrivenLeads.traceClass_isTwoSidedIdeal,
    QuantumMechanics.LindbladDrivenLeads.TraceClassDensityOperator.adjointSandwich_isPositive_and_traceClass,
    QuantumMechanics.LindbladDrivenLeads.TraceClassDensityOperator.continuum_density_operator_certificate]

/- ZIL-END -/

/- Consolidated from Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.NuclearDensityEvolution -/

/-!
# Non-diagonal nuclear density ensembles and isometric evolution

This file removes the diagonal-basis restriction from the preceding spectral density carrier.
A `NuclearDensityOperator` is an arbitrary countable family of amplitudes `a n` with

`∑ n, ‖a n‖² = 1`.

It represents the positive operator `∑' n, |a n><a n|`.  The series converges in operator norm
and is proved positive, trace class, compact, and trace one.  Its finite truncations converge in
operator norm, weak-operator topology, and trace.

The carrier is closed under genuine convex mixtures by interleaving the square-root-weighted
ensembles.  Complex linear isometries act by `ρ ↦ U ρ U†`; this action preserves positivity,
trace class, and normalization and obeys identity and composition exactly.

The scope remains explicit: the ensemble is supplied constructive data, not a reproof that every
abstract positive trace-class operator has an enumerated decomposition.  Isometric evolution is
trace preserving, but a general non-isometric open-system map still requires a Kraus completeness
or trace-preservation certificate.
-/

set_option autoImplicit false

open Filter NormedSpace
open scoped Topology InnerProductSpace ComplexOrder

@[expose] public section

namespace QuantumMechanics.LindbladDrivenLeads

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure NuclearDensityOperator where
  amplitude : ℕ → H
  summable_normSq : Summable (fun n => ‖amplitude n‖ ^ 2)
  trace_one : ∑' n, ‖amplitude n‖ ^ 2 = 1

namespace NuclearDensityOperator

noncomputable def term (ρ : NuclearDensityOperator (H := H)) (n : ℕ) :
    H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ (ρ.amplitude n) (ρ.amplitude n)

noncomputable def operator (ρ : NuclearDensityOperator (H := H)) :
    H →L[ℂ] H :=
  ∑' n, ρ.term n

noncomputable def partialOperator (ρ : NuclearDensityOperator (H := H)) (N : ℕ) :
    H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, ρ.term n

lemma norm_term (ρ : NuclearDensityOperator (H := H)) (n : ℕ) :
    ‖ρ.term n‖ = ‖ρ.amplitude n‖ ^ 2 := by
  simp [term, InnerProductSpace.norm_rankOne, pow_two]

lemma summable_term (ρ : NuclearDensityOperator (H := H)) :
    Summable ρ.term := by
  apply Summable.of_norm
  simpa only [ρ.norm_term] using ρ.summable_normSq

lemma hasSum_operator (ρ : NuclearDensityOperator (H := H)) :
    HasSum ρ.term ρ.operator :=
  ρ.summable_term.hasSum

lemma partialOperator_tendsto (ρ : NuclearDensityOperator (H := H)) :
    Tendsto ρ.partialOperator atTop (nhds ρ.operator) :=
  ρ.hasSum_operator.tendsto_sum_nat

lemma partialOperator_isPositive (ρ : NuclearDensityOperator (H := H)) (N : ℕ) :
    (ρ.partialOperator N).IsPositive := by
  unfold partialOperator term
  exact ContinuousLinearMap.isPositive_sum _ fun n _ =>
    InnerProductSpace.isPositive_rankOne_self (ρ.amplitude n)

lemma operator_isPositive (ρ : NuclearDensityOperator (H := H)) :
    ρ.operator.IsPositive :=
  isPositive_of_norm_tendsto ρ.partialOperator_tendsto ρ.partialOperator_isPositive

lemma operator_isTraceClass (ρ : NuclearDensityOperator (H := H)) :
    IsTraceClass ρ.operator := by
  exact ⟨{
    left := ρ.amplitude
    right := ρ.amplitude
    summable_cost := by simpa only [pow_two] using ρ.summable_normSq
    hasSum_operator := ρ.hasSum_operator
  }⟩

noncomputable def trace (ρ : NuclearDensityOperator (H := H)) : ℝ :=
  ∑' n, ‖ρ.amplitude n‖ ^ 2

@[simp] theorem trace_eq_one (ρ : NuclearDensityOperator (H := H)) :
    ρ.trace = 1 := ρ.trace_one

theorem partialTrace_tendsto_one (ρ : NuclearDensityOperator (H := H)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ‖ρ.amplitude n‖ ^ 2)
      atTop (nhds 1) := by
  simpa [ρ.trace_one] using ρ.summable_normSq.hasSum.tendsto_sum_nat

theorem partialOperator_WOT_tendsto (ρ : NuclearDensityOperator (H := H)) :
    Tendsto (fun N => toWOT (ρ.partialOperator N)) atTop
      (nhds (toWOT ρ.operator)) :=
  norm_tendsto_implies_WOT ρ.partialOperator_tendsto

theorem continuum_nuclear_density_certificate
    (ρ : NuclearDensityOperator (H := H)) :
    ρ.operator.IsPositive
      ∧ IsTraceClass ρ.operator
      ∧ IsCompactOperator ρ.operator
      ∧ ρ.trace = 1
      ∧ Tendsto ρ.partialOperator atTop (nhds ρ.operator)
      ∧ Tendsto (fun N => toWOT (ρ.partialOperator N)) atTop
          (nhds (toWOT ρ.operator))
      ∧ Tendsto (fun N => ∑ n ∈ Finset.range N, ‖ρ.amplitude n‖ ^ 2)
          atTop (nhds 1) := by
  exact ⟨ρ.operator_isPositive, ρ.operator_isTraceClass,
    ρ.operator_isTraceClass.isCompact, ρ.trace_eq_one,
    ρ.partialOperator_tendsto, ρ.partialOperator_WOT_tendsto,
    ρ.partialTrace_tendsto_one⟩

noncomputable def pure (ψ : H) (hψ : ‖ψ‖ = 1) :
    NuclearDensityOperator (H := H) where
  amplitude := fun n => if n = 0 then ψ else 0
  summable_normSq := by
    rw [show
      (fun n : ℕ => ‖if n = 0 then ψ else 0‖ ^ 2) =
        (fun n => if n = 0 then ‖ψ‖ ^ 2 else 0) by
      funext n
      split <;> simp_all]
    exact (hasSum_ite_eq 0 (‖ψ‖ ^ 2)).summable
  trace_one := by
    rw [show
      (fun n : ℕ => ‖if n = 0 then ψ else 0‖ ^ 2) =
        (fun n => if n = 0 then ‖ψ‖ ^ 2 else 0) by
      funext n
      split <;> simp_all]
    simp [hψ]

@[simp] theorem pure_operator (ψ : H) (hψ : ‖ψ‖ = 1) :
    (pure ψ hψ).operator = InnerProductSpace.rankOne ℂ ψ ψ := by
  unfold operator
  rw [show
    (fun n => (pure ψ hψ).term n) =
      (fun n => if n = 0 then InnerProductSpace.rankOne ℂ ψ ψ else 0) by
    funext n
    split <;> simp_all [term, pure]]
  exact tsum_ite_eq 0 (fun _ => InnerProductSpace.rankOne ℂ ψ ψ)

lemma norm_sqrt_smul_sq {p : ℝ} (hp : 0 ≤ p) (x : H) :
    ‖(Real.sqrt p : ℂ) • x‖ ^ 2 = p * ‖x‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg p)]
  nlinarith [Real.sq_sqrt hp]

lemma rankOne_sqrt_smul_self {p : ℝ} (hp : 0 ≤ p) (x : H) :
    InnerProductSpace.rankOne ℂ ((Real.sqrt p : ℂ) • x)
        ((Real.sqrt p : ℂ) • x) =
      (p : ℂ) • InnerProductSpace.rankOne ℂ x x := by
  ext y
  simp only [InnerProductSpace.rankOne_apply, smul_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  congr 1
  have hsqrt : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp
  calc
    (Real.sqrt p : ℂ) * ⟪x, y⟫_ℂ * (Real.sqrt p : ℂ) =
        ((Real.sqrt p : ℂ) ^ 2) * ⟪x, y⟫_ℂ := by ring
    _ = (p : ℂ) * ⟪x, y⟫_ℂ := by rw [hsqrt]

noncomputable def mixedAmplitude (p : ℝ)
    (ρ σ : NuclearDensityOperator (H := H)) : ℕ → H :=
  interleave
    (fun n => (Real.sqrt p : ℂ) • ρ.amplitude n)
    (fun n => (Real.sqrt (1 - p) : ℂ) • σ.amplitude n)

@[simp] lemma mixedAmplitude_even (p : ℝ)
    (ρ σ : NuclearDensityOperator (H := H)) (n : ℕ) :
    mixedAmplitude p ρ σ (2 * n) =
      (Real.sqrt p : ℂ) • ρ.amplitude n := by
  simp [mixedAmplitude]

@[simp] lemma mixedAmplitude_odd (p : ℝ)
    (ρ σ : NuclearDensityOperator (H := H)) (n : ℕ) :
    mixedAmplitude p ρ σ (2 * n + 1) =
      (Real.sqrt (1 - p) : ℂ) • σ.amplitude n := by
  simp [mixedAmplitude]

noncomputable def mixedCost (p : ℝ)
    (ρ σ : NuclearDensityOperator (H := H)) : ℕ → ℝ :=
  interleave
    (fun n => p * ‖ρ.amplitude n‖ ^ 2)
    (fun n => (1 - p) * ‖σ.amplitude n‖ ^ 2)

lemma mixedAmplitude_normSq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : NuclearDensityOperator (H := H)) (n : ℕ) :
    ‖mixedAmplitude p ρ σ n‖ ^ 2 = mixedCost p ρ σ n := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  unfold mixedAmplitude mixedCost interleave
  cases h : Equiv.natSumNatEquivNat.symm n with
  | inl k =>
      simp only [Sum.elim_inl]
      exact norm_sqrt_smul_sq hp0 (ρ.amplitude k)
  | inr k =>
      simp only [Sum.elim_inr]
      exact norm_sqrt_smul_sq hq (σ.amplitude k)

lemma mixedCost_hasSum (p : ℝ)
    (ρ σ : NuclearDensityOperator (H := H)) :
    HasSum (mixedCost p ρ σ) 1 := by
  have he0 := ρ.summable_normSq.hasSum.mul_left p
  rw [ρ.trace_one, mul_one] at he0
  have he : HasSum (fun n => mixedCost p ρ σ (2 * n)) p := by
    simpa only [mixedCost, interleave_even] using he0
  have ho0 := σ.summable_normSq.hasSum.mul_left (1 - p)
  rw [σ.trace_one, mul_one] at ho0
  have ho : HasSum (fun n => mixedCost p ρ σ (2 * n + 1)) (1 - p) := by
    simpa only [mixedCost, interleave_odd] using ho0
  simpa only [add_sub_cancel] using he.even_add_odd ho

lemma mixedAmplitude_hasSum_normSq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : NuclearDensityOperator (H := H)) :
    HasSum (fun n => ‖mixedAmplitude p ρ σ n‖ ^ 2) 1 := by
  exact (mixedCost_hasSum p ρ σ).congr_fun fun n =>
    mixedAmplitude_normSq p hp0 hp1 ρ σ n

noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : NuclearDensityOperator (H := H)) :
    NuclearDensityOperator (H := H) where
  amplitude := mixedAmplitude p ρ σ
  summable_normSq := (mixedAmplitude_hasSum_normSq p hp0 hp1 ρ σ).summable
  trace_one := (mixedAmplitude_hasSum_normSq p hp0 hp1 ρ σ).tsum_eq

theorem mix_operator (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : NuclearDensityOperator (H := H)) :
    (mix p hp0 hp1 ρ σ).operator =
      (p : ℂ) • ρ.operator + ((1 - p : ℝ) : ℂ) • σ.operator := by
  have he : HasSum (fun n => (mix p hp0 hp1 ρ σ).term (2 * n))
      ((p : ℂ) • ρ.operator) := by
    rw [show
      (fun n => (mix p hp0 hp1 ρ σ).term (2 * n)) =
        (fun n => (p : ℂ) • ρ.term n) by
      funext n
      simp only [term, mix, mixedAmplitude_even]
      exact rankOne_sqrt_smul_self hp0 (ρ.amplitude n)]
    exact ρ.hasSum_operator.const_smul (p : ℂ)
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have ho : HasSum (fun n => (mix p hp0 hp1 ρ σ).term (2 * n + 1))
      (((1 - p : ℝ) : ℂ) • σ.operator) := by
    rw [show
      (fun n => (mix p hp0 hp1 ρ σ).term (2 * n + 1)) =
        (fun n => ((1 - p : ℝ) : ℂ) • σ.term n) by
      funext n
      simp only [term, mix, mixedAmplitude_odd]
      exact rankOne_sqrt_smul_self hq (σ.amplitude n)]
    exact σ.hasSum_operator.const_smul ((1 - p : ℝ) : ℂ)
  exact (mix p hp0 hp1 ρ σ).hasSum_operator.unique (he.even_add_odd ho)

noncomputable def mapIsometry
    (U : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    NuclearDensityOperator (H := H) where
  amplitude := fun n => U (ρ.amplitude n)
  summable_normSq := by simpa only [U.norm_map] using ρ.summable_normSq
  trace_one := by simpa only [U.norm_map] using ρ.trace_one

@[simp] theorem mapIsometry_trace
    (U : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    (ρ.mapIsometry U).trace = ρ.trace := by
  simp only [trace, mapIsometry, U.norm_map]

@[simp] theorem mapIsometry_id (ρ : NuclearDensityOperator (H := H)) :
    ρ.mapIsometry (LinearIsometry.id) = ρ := by
  cases ρ
  rfl

@[simp] theorem mapIsometry_comp
    (U V : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    ρ.mapIsometry (V.comp U) = (ρ.mapIsometry U).mapIsometry V := by
  cases ρ
  rfl

theorem mapIsometry_operator
    (U : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    (ρ.mapIsometry U).operator =
      U.toContinuousLinearMap * ρ.operator * U.toContinuousLinearMap.adjoint := by
  have h := (ρ.hasSum_operator.mul_left U.toContinuousLinearMap).mul_right
    U.toContinuousLinearMap.adjoint
  apply HasSum.unique (ρ.mapIsometry U).hasSum_operator
  change HasSum (fun n => (ρ.mapIsometry U).term n)
    (U.toContinuousLinearMap * ρ.operator * U.toContinuousLinearMap.adjoint)
  rw [show
    (fun n => (ρ.mapIsometry U).term n) =
      (fun n => U.toContinuousLinearMap * ρ.term n *
        U.toContinuousLinearMap.adjoint) by
    funext n
    unfold term mapIsometry
    symm
    calc
      U.toContinuousLinearMap *
            InnerProductSpace.rankOne ℂ (ρ.amplitude n) (ρ.amplitude n) *
            U.toContinuousLinearMap.adjoint =
          InnerProductSpace.rankOne ℂ (U (ρ.amplitude n)) (ρ.amplitude n) *
            U.toContinuousLinearMap.adjoint := by
              change (U.toContinuousLinearMap.comp
                (InnerProductSpace.rankOne ℂ (ρ.amplitude n) (ρ.amplitude n))).comp
                  U.toContinuousLinearMap.adjoint =
                (InnerProductSpace.rankOne ℂ (U (ρ.amplitude n))
                  (ρ.amplitude n)).comp U.toContinuousLinearMap.adjoint
              rw [InnerProductSpace.comp_rankOne]
              rfl
      _ = InnerProductSpace.rankOne ℂ (U (ρ.amplitude n))
          (U.toContinuousLinearMap.adjoint.adjoint (ρ.amplitude n)) := by
            change (InnerProductSpace.rankOne ℂ (U (ρ.amplitude n))
              (ρ.amplitude n)).comp U.toContinuousLinearMap.adjoint =
              InnerProductSpace.rankOne ℂ (U (ρ.amplitude n))
                (U.toContinuousLinearMap.adjoint.adjoint (ρ.amplitude n))
            rw [InnerProductSpace.rankOne_comp]
      _ = InnerProductSpace.rankOne ℂ (U (ρ.amplitude n))
          (U (ρ.amplitude n)) := by
            rw [ContinuousLinearMap.adjoint_adjoint]
            rfl]
  exact h

theorem mapIsometry_preserves_density
    (U : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    (ρ.mapIsometry U).operator.IsPositive
      ∧ IsTraceClass (ρ.mapIsometry U).operator
      ∧ (ρ.mapIsometry U).trace = 1 :=
  ⟨(ρ.mapIsometry U).operator_isPositive,
    (ρ.mapIsometry U).operator_isTraceClass,
    (ρ.mapIsometry U).trace_eq_one⟩

theorem isometric_density_action_certificate
    (U V : H →ₗᵢ[ℂ] H) (ρ : NuclearDensityOperator (H := H)) :
    (ρ.mapIsometry U).operator =
        U.toContinuousLinearMap * ρ.operator * U.toContinuousLinearMap.adjoint
      ∧ (ρ.mapIsometry U).operator.IsPositive
      ∧ IsTraceClass (ρ.mapIsometry U).operator
      ∧ (ρ.mapIsometry U).trace = 1
      ∧ ρ.mapIsometry LinearIsometry.id = ρ
      ∧ ρ.mapIsometry (V.comp U) = (ρ.mapIsometry U).mapIsometry V := by
  exact ⟨ρ.mapIsometry_operator U,
    (ρ.mapIsometry U).operator_isPositive,
    (ρ.mapIsometry U).operator_isTraceClass,
    (ρ.mapIsometry U).trace_eq_one,
    ρ.mapIsometry_id,
    ρ.mapIsometry_comp U V⟩

end NuclearDensityOperator
end
end QuantumMechanics.LindbladDrivenLeads

end

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.continuum_nuclear_density_certificate where
  formalizes @ "claim:any-countable-square-summable-rank-one-ensemble-of-total-weight-one-constructs-a-positive-compact-trace-class-density-operator-with-norm-WOT-and-trace-convergent-finite-truncations",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.IsTraceClass.isCompact",
  supported_by @ "lean:InnerProductSpace.isPositive_rankOne_self",
  caveat @ "claim:the-positive-nuclear-ensemble-is-supplied-constructive-data-not-a-reproof-that-every-abstract-positive-trace-class-operator-has-an-enumerated-decomposition"

zil attach QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.mix_operator where
  formalizes @ "claim:positive-trace-one-nuclear-density-ensembles-are-closed-under-binary-convex-mixtures-and-the-associated-operator-is-the-same-convex-combination",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:HasSum.even_add_odd",
  caveat @ "claim:binary-convex-closure-on-explicit-countable-ensembles-not-a-general-barycentric-integral-over-an-uncountable-state-space"

zil attach QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.isometric_density_action_certificate where
  formalizes @ "claim:complex-linear-isometries-act-on-infinite-nuclear-density-operators-by-U-rho-U-adjoint-preserving-positivity-trace-class-and-trace-one-with-exact-identity-and-composition-laws",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:LinearIsometry.norm_map",
  supported_by @ "lean:InnerProductSpace.comp_rankOne",
  caveat @ "claim:isometric-closed-system-action-not-a-general-non-isometric-CPTP-or-unbounded-GKLS-semigroup-without-a-separate-Kraus-completeness-or-generation-certificate"

zil_file_contract physlib.lindbladDrivenLeads.nuclearDensityEvolution where
  promises "Arbitrary countable normalized positive nuclear ensembles construct genuine infinite positive compact trace-class density operators with norm, WOT, and trace convergent finite truncations. Binary convex mixtures stay in the carrier with the exact convex operator law, while complex linear isometries act by U rho U-adjoint, preserve the density conditions, and satisfy identity and composition."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:QuantumMechanics.LindbladDrivenLeads.TraceClassDecomposition",
    "lean:InnerProductSpace.isPositive_rankOne_self",
    "lean:HasSum.even_add_odd",
    "lean:LinearIsometry.norm_map"]
  forbids_substitutes ["a finite matrix carrier relabeled as a continuum density state",
    "assuming orthogonality of the non-diagonal ensemble",
    "claiming an arbitrary bounded sandwich preserves trace one",
    "claiming a general CPTP or unbounded GKLS evolution from isometry alone"]
  witnessed_by [QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.continuum_nuclear_density_certificate,
    QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.mix_operator,
    QuantumMechanics.LindbladDrivenLeads.NuclearDensityOperator.isometric_density_action_certificate]

/- ZIL-END -/

