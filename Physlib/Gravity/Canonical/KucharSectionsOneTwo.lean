/-
Copyright (c) 2026 Jorge Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge Garcia
-/
module

public import Physlib.Gravity.Canonical.ProblemOfTime
public import Zil

/-!
# Kuchař sections one and two

This module adds semantic contracts for the formulas and problem distinctions in
Sections 1 and 2 of Kuchař's `Time and interpretations of quantum gravity`.
It complements `ProblemOfTime`, which already records Eqs. (1.1)-(1.6),
(1.12)-(1.13), (2.4)-(2.6), and (2.8)-(2.9).

The declarations here cover the remaining equation-level interfaces used in
those sections:

* the embedding Hamilton-Jacobi equation (1.10);
* the absolute-time linear constraint (1.11);
* the functional Schrödinger equation (2.7);
* distinct predicates for functional evolution, multiple choice, and the
  Hilbert-space problem.

These are typed contracts, not claims that general relativity globally admits a
preferred time, embedding variables, or a preferred physical inner product.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Gravity.Canonical

/-! ## A. Absolute-time constraint -/

/-- Data entering Kuchař's absolute-time linear constraint, Eq. (1.11). -/
structure KucharAbsoluteTimeConstraint (Phase : Type*) where
  timeMomentum : Phase → ℝ
  trueHamiltonian : Phase → ℝ

/-- The left-hand side `P_T + h` of Kuchař Eq. (1.11). -/
def KucharAbsoluteTimeConstraint.residual {Phase : Type*}
    (C : KucharAbsoluteTimeConstraint Phase) (q : Phase) : ℝ :=
  C.timeMomentum q + C.trueHamiltonian q

/-- Exact satisfaction of the absolute-time constraint at a phase-space point. -/
def KucharAbsoluteTimeConstraint.Satisfies {Phase : Type*}
    (C : KucharAbsoluteTimeConstraint Phase) (q : Phase) : Prop :=
  C.residual q = 0

/-- Eq. (1.11) is equivalent to solving for the time momentum. -/
@[zil_claim Kuchar.absoluteTimeConstraint_eq_1_11]
lemma KucharAbsoluteTimeConstraint.satisfies_iff_momentum_eq_neg
    {Phase : Type*} (C : KucharAbsoluteTimeConstraint Phase) (q : Phase) :
    C.Satisfies q ↔ C.timeMomentum q = -C.trueHamiltonian q := by
  constructor
  · intro h
    dsimp [KucharAbsoluteTimeConstraint.Satisfies,
      KucharAbsoluteTimeConstraint.residual] at h
    linarith
  · intro h
    dsimp [KucharAbsoluteTimeConstraint.Satisfies,
      KucharAbsoluteTimeConstraint.residual]
    linarith

/-! ## B. Embedding Hamilton-Jacobi equation -/

/--
Data representing `δS/δX^A` and the energy flux after the Hamilton-Jacobi
substitution in Kuchař Eq. (1.10).
-/
structure KucharEmbeddingHamiltonJacobiData (Point Embedding : Type*) where
  embeddingActionDerivative : Embedding → Point → ℝ
  energyFluxAfterSubstitution : Embedding → Point → ℝ

/-- The left-hand side of the embedding Hamilton-Jacobi equation (1.10). -/
def KucharEmbeddingHamiltonJacobiData.residual {Point Embedding : Type*}
    (H : KucharEmbeddingHamiltonJacobiData Point Embedding)
    (A : Embedding) (x : Point) : ℝ :=
  H.embeddingActionDerivative A x + H.energyFluxAfterSubstitution A x

/-- Exact satisfaction of Kuchař Eq. (1.10) for every embedding component and point. -/
def KucharEmbeddingHamiltonJacobiData.Satisfies {Point Embedding : Type*}
    (H : KucharEmbeddingHamiltonJacobiData Point Embedding) : Prop :=
  ∀ A x, H.residual A x = 0

/-- Eq. (1.10) is equivalent to the action derivative being minus the substituted flux. -/
@[zil_claim Kuchar.embeddingHamiltonJacobi_eq_1_10]
lemma KucharEmbeddingHamiltonJacobiData.satisfies_iff_derivative_eq_neg_flux
    {Point Embedding : Type*} (H : KucharEmbeddingHamiltonJacobiData Point Embedding) :
    H.Satisfies ↔
      ∀ A x, H.embeddingActionDerivative A x = -H.energyFluxAfterSubstitution A x := by
  constructor
  · intro h A x
    have hz := h A x
    dsimp [KucharEmbeddingHamiltonJacobiData.residual] at hz
    linarith
  · intro h A x
    dsimp [KucharEmbeddingHamiltonJacobiData.residual]
    have heq := h A x
    linarith

/--
When the Hamilton-Jacobi terms are identified with the existing carrier fields,
the Eq. (1.10) residual is the Eq. (1.6) embedding constraint.
-/
@[zil_claim Kuchar.embeddingHamiltonJacobi_bridge_1_6_1_10]
lemma embeddingHamiltonJacobi_residual_eq_embeddingConstraint
    {Point Embedding State : Type*}
    (K : KucharPaperConstraintCarrier Point Embedding State)
    (H : KucharEmbeddingHamiltonJacobiData Point Embedding)
    (hMomentum : ∀ A x, H.embeddingActionDerivative A x = K.embeddingMomentum A x)
    (hFlux : ∀ A x, H.energyFluxAfterSubstitution A x = K.embeddingEnergyFlux A x) :
    ∀ A x, H.residual A x = kucharEmbeddingConstraint K A x := by
  intro A x
  simp only [KucharEmbeddingHamiltonJacobiData.residual, kucharEmbeddingConstraint,
    hMomentum A x, hFlux A x]

/-! ## C. Functional Schrödinger equation -/

/-- Complex data entering Kuchař's functional Schrödinger equation, Eq. (2.7). -/
structure KucharFunctionalSchrodingerData (Point Embedding State : Type*) where
  embeddingDerivative : Embedding → Point → State → ℂ
  energyFluxOperatorOn : Embedding → Point → State → ℂ

/-- The residual `i δΨ/δX^A - ĥ_A Ψ` of Eq. (2.7). -/
def KucharFunctionalSchrodingerData.residual {Point Embedding State : Type*}
    (D : KucharFunctionalSchrodingerData Point Embedding State)
    (A : Embedding) (x : Point) (Ψ : State) : ℂ :=
  Complex.I * D.embeddingDerivative A x Ψ - D.energyFluxOperatorOn A x Ψ

/-- Exact satisfaction of the functional Schrödinger equation for all arguments. -/
def KucharFunctionalSchrodingerData.Satisfies {Point Embedding State : Type*}
    (D : KucharFunctionalSchrodingerData Point Embedding State) : Prop :=
  ∀ A x Ψ, D.residual A x Ψ = 0

/-- Vanishing of the Eq. (2.7) residual is the displayed functional equation. -/
@[zil_claim Kuchar.functionalSchrodinger_eq_2_7]
lemma KucharFunctionalSchrodingerData.satisfies_iff_equation
    {Point Embedding State : Type*}
    (D : KucharFunctionalSchrodingerData Point Embedding State) :
    D.Satisfies ↔
      ∀ A x Ψ,
        Complex.I * D.embeddingDerivative A x Ψ = D.energyFluxOperatorOn A x Ψ := by
  constructor
  · intro h A x Ψ
    exact sub_eq_zero.mp (h A x Ψ)
  · intro h A x Ψ
    exact sub_eq_zero.mpr (h A x Ψ)

/-! ## D. Functional-evolution problem -/

/-- A nonzero Eq. (2.8) embedding-constraint commutator. -/
def KucharEmbeddingConstraintAnomaly {Point Embedding State : Type*}
    (K : KucharPaperConstraintCarrier Point Embedding State) : Prop :=
  ∃ A B x y Ψ, K.quantumEmbeddingCommutatorOn A B x y Ψ ≠ 0

/-- A nonzero commutator in one of the three Eq. (2.9) Dirac-algebra channels. -/
def KucharDiracConstraintAnomaly {Point Embedding State : Type*}
    (K : KucharPaperConstraintCarrier Point Embedding State) : Prop :=
  (∃ x y Ψ, K.quantumMomentumMomentumCommutatorOn x y Ψ ≠ 0) ∨
  (∃ x y Ψ, K.quantumMomentumHamiltonianCommutatorOn x y Ψ ≠ 0) ∨
  (∃ x y Ψ, K.quantumHamiltonianHamiltonianCommutatorOn x y Ψ ≠ 0)

/-- Kuchař's functional-evolution problem as an embedding or Dirac anomaly. -/
def KucharFunctionalEvolutionProblem {Point Embedding State : Type*}
    (K : KucharPaperConstraintCarrier Point Embedding State) : Prop :=
  KucharEmbeddingConstraintAnomaly K ∨ KucharDiracConstraintAnomaly K

/-- The existing Eq. (2.8) closure contract rules out an embedding anomaly. -/
@[zil_claim Kuchar.noEmbeddingConstraintAnomaly_eq_2_8]
lemma no_embeddingConstraintAnomaly_of_quantumFunctionalEvolution
    {Point Embedding State : Type*}
    {K : KucharPaperConstraintCarrier Point Embedding State}
    (h : KucharPaperQuantumFunctionalEvolution K) :
    ¬ KucharEmbeddingConstraintAnomaly K := by
  rintro ⟨A, B, x, y, Ψ, hne⟩
  exact hne (h.quantumEmbeddingCommutator_eq_zero_2_8 A B x y Ψ)

/-- The existing Eq. (2.9) closure contract rules out all three Dirac anomalies. -/
@[zil_claim Kuchar.noDiracConstraintAnomaly_eq_2_9]
lemma no_diracConstraintAnomaly_of_quantumFunctionalEvolution
    {Point Embedding State : Type*}
    {K : KucharPaperConstraintCarrier Point Embedding State}
    (h : KucharPaperQuantumFunctionalEvolution K) :
    ¬ KucharDiracConstraintAnomaly K := by
  rintro (hMM | hMH | hHH)
  · rcases hMM with ⟨x, y, Ψ, hne⟩
    exact hne (h.quantumMomentumMomentumCommutator_eq_zero_2_9 x y Ψ)
  · rcases hMH with ⟨x, y, Ψ, hne⟩
    exact hne (h.quantumMomentumHamiltonianCommutator_eq_zero_2_9 x y Ψ)
  · rcases hHH with ⟨x, y, Ψ, hne⟩
    exact hne (h.quantumHamiltonianHamiltonianCommutator_eq_zero_2_9 x y Ψ)

/-- Exact Eqs. (2.8)-(2.9) closure rules out the functional-evolution problem. -/
@[zil_claim Kuchar.noFunctionalEvolutionProblem]
lemma no_functionalEvolutionProblem_of_quantumFunctionalEvolution
    {Point Embedding State : Type*}
    {K : KucharPaperConstraintCarrier Point Embedding State}
    (h : KucharPaperQuantumFunctionalEvolution K) :
    ¬ KucharFunctionalEvolutionProblem K := by
  rintro (hEmbedding | hDirac)
  · exact no_embeddingConstraintAnomaly_of_quantumFunctionalEvolution h hEmbedding
  · exact no_diracConstraintAnomaly_of_quantumFunctionalEvolution h hDirac

/-! ## E. Multiple-choice problem -/

/-- A clock-indexed family of quantum theories and its chosen equivalence relation. -/
structure KucharClockTheoryFamily (Clock Theory : Type*) where
  quantization : Clock → Theory
  equivalent : Theory → Theory → Prop

/-- Two distinct clock choices produce inequivalent quantum theories. -/
def KucharMultipleChoiceProblem {Clock Theory : Type*}
    (F : KucharClockTheoryFamily Clock Theory) : Prop :=
  ∃ c d, c ≠ d ∧ ¬ F.equivalent (F.quantization c) (F.quantization d)

/-- Clock independence of the quantum theory rules out the multiple-choice problem. -/
@[zil_claim Kuchar.noMultipleChoiceProblem]
lemma no_multipleChoiceProblem_of_clock_independent
    {Clock Theory : Type*} {F : KucharClockTheoryFamily Clock Theory}
    (h : ∀ c d, F.equivalent (F.quantization c) (F.quantization d)) :
    ¬ KucharMultipleChoiceProblem F := by
  rintro ⟨c, d, _hcd, hne⟩
  exact hne (h c d)

/-! ## F. Hilbert-space problem -/

/-- An embedding-indexed candidate physical inner product. -/
structure KucharPhysicalInnerProductFamily (Embedding State : Type*) where
  physicalState : State → Prop
  innerProductAt : Embedding → State → State → ℂ

/-- The physical inner product is independent of the chosen embedding. -/
def KucharPhysicalInnerProductFamily.HasEmbeddingIndependentInnerProduct
    {Embedding State : Type*}
    (H : KucharPhysicalInnerProductFamily Embedding State) : Prop :=
  ∀ A B Ψ Φ, H.physicalState Ψ → H.physicalState Φ →
    H.innerProductAt A Ψ Φ = H.innerProductAt B Ψ Φ

/-- Kuchař's Hilbert-space problem as failure of embedding independence. -/
def KucharHilbertSpaceProblem {Embedding State : Type*}
    (H : KucharPhysicalInnerProductFamily Embedding State) : Prop :=
  ¬ H.HasEmbeddingIndependentInnerProduct

/-- An embedding-independent physical inner product rules out the Hilbert-space problem. -/
@[zil_claim Kuchar.noHilbertSpaceProblem]
lemma no_hilbertSpaceProblem_of_embedding_independent
    {Embedding State : Type*}
    {H : KucharPhysicalInnerProductFamily Embedding State}
    (h : H.HasEmbeddingIndependentInnerProduct) :
    ¬ KucharHilbertSpaceProblem H := by
  intro hProblem
  exact hProblem h

end Physlib.Gravity.Canonical
