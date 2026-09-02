/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDarwinismEverettDeutschRecords
meta import Zil

/-!
# Weinberg collapse and collapse-free Darwinism produce the same pointer Born weights

Weinberg's *Collapse of the state vector* (Phys. Rev. A **85** (2012) 062116,
`Foundations.WeinbergStateVectorCollapse`) is the **explicit-collapse** counterpoint to the collapse-free
Everett/Darwinism chain (`SciamaAdSCPTDarwinismEverettDeutschRecords`): a kernel `K` drives the state-vector
density onto the pointer basis, with the Born weights as conserved left zero modes.  The repo's measurement-step
inductive even carries Weinberg's step as its fifth alternative — `MeasurementStep.primitiveStateVectorCollapse`,
precisely the one step `everettHeisenberg_excludes_primitive_collapse` shows the Everett chain never uses.

This module proves the two routes **numerically agree** on the pointer weights, and makes the ontological
dichotomy explicit:

* `indicatorBasis_dual` / `expectation_indicatorBasis` — the pointer/weight *delta* basis is Weinberg-dual
  (`∑ ψ g_a f_b = δ_ab`), and its expectation reads off the density at the pointer outcome.
* `weinberg_collapse_recovers_record_weight` — instantiating Weinberg's collapse system on the **record-induced
  Born density** `P(m) = |Ψ_m|²`: **(i)** each Born coefficient is *conserved* under the collapse generator
  (left zero mode, Weinberg Eqs. 18–20); **(ii)** the collapsed distribution *recovers* it, `= |Ψ_m|²`
  (Weinberg Eqs. 14, 16); **(iii)** the collapse-free Everett record diagonal is the *same* `|Ψ_m|²`
  (`traceRight_correlatedKet_orthonormal`).  Collapse dynamics and record decoherence agree weight-by-weight.
* `collapse_dichotomy_same_weights` — the capstone: same pointer weights, opposite ontology — Weinberg's step
  *is* the primitive collapse (`IsPrimitiveCollapse .primitiveStateVectorCollapse`), while all four steps of the
  unitary/decoherent chain are not (`everettHeisenberg_excludes_primitive_collapse`).  At the level of pointer
  Born weights the primitive collapse is observationally redundant: the records already carry the same numbers.

Honest scope: the instantiation is the finite delta-basis pointer/weight pair on the record-induced density;
the agreement theorem is weight-level (pointer Born coefficients), not a full dynamical equivalence of the two
programs.  Weinberg's kernel dynamics and the open-system questions (nonlinearity, superluminal constraints)
are the paper's content.

Continuations: `SciamaAdSCPTCollapseDecoherenceResolution` resolves the competition the weight agreement
leaves open (strict coherence discriminator; collapse = the infinite-decoherence limit), and
`SciamaAdSCPTCollapseModularCompatibility` audits both sides against the AQFT layer (a nontrivial collapse is
non-injective, hence neither a vN symmetry over a separating state nor a member of any Tomita–Takesaki modular
flow; the decoherence visibility is itself the wedge-modular KMS eigenvalue).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence

open Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
open Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement
open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates
open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
open ComplexConjugate

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## §1. The delta pointer/weight basis is Weinberg-dual -/

/-- The indicator (delta) basis on the pointer outcomes: `f_a(ψ) = δ_{ψa}` — used as both the Weinberg pointer
distribution and the Born-weight functional. -/
def indicatorBasis (a ψ : Ω) : ℝ := if ψ = a then 1 else 0

/-- **[The delta basis is Weinberg-dual] `∑_ψ g_a f_b = δ_ab`** — the pointer/weight duality (Weinberg
Eqs. 14–16) holds exactly for the indicator pair. -/
theorem indicatorBasis_dual : dualPointerWeight (indicatorBasis (Ω := Ω)) indicatorBasis := by
  intro a b
  unfold indicatorBasis
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ a (fun ψ => if ψ = b then (1 : ℝ) else 0)]
  simp

/-- **[The delta expectation reads the density at the outcome] `⟨f_m, P⟩ = P(m)`.** -/
theorem expectation_indicatorBasis (m : Ω) (P : ProbabilityDensity Ω) :
    expectation (indicatorBasis m) P = P m := by
  unfold expectation indicatorBasis
  simp

/-! ## §2. Weinberg collapse recovers the Darwinism record weight -/

/-- **[Collapse and records agree weight-by-weight]** — on the record-induced Born density `P(m) = |Ψ_m|²`:
**(i)** the Born coefficient is *conserved* under the Weinberg collapse generator (left zero mode);
**(ii)** the collapsed distribution *recovers* it, `= |Ψ_m|²`; **(iii)** the collapse-free Everett record
diagonal (`SciamaAdSCPTDarwinismEverettDeutschRecords`) is the *same* `|Ψ_m|²`.  The explicit collapse dynamics
and the record decoherence produce identical pointer Born weights. -/
theorem weinberg_collapse_recovers_record_weight
    {dS dE : Type*} [Fintype dS] [Fintype dE] [DecidableEq dS] [DecidableEq dE]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (K : CollapseKernel dS)
    (hzero : ∀ a : dS, leftZeroMode K (indicatorBasis a)) (m : dS) :
    expectation (indicatorBasis m) (kernelAction K (fun ψ => Complex.normSq (Ψ ψ))) = 0
      ∧ expectation (indicatorBasis m)
          (collapsedDistribution indicatorBasis indicatorBasis (fun ψ => Complex.normSq (Ψ ψ)))
          = Complex.normSq (Ψ m)
      ∧ ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m = (Complex.normSq (Ψ m) : ℂ) := by
  obtain ⟨hcons, hrec⟩ := born_weights_conserved_and_recovered K indicatorBasis indicatorBasis
    (fun ψ => Complex.normSq (Ψ ψ)) hzero indicatorBasis_dual m
  refine ⟨hcons, ?_, ?_⟩
  · rw [hrec, expectation_indicatorBasis]
  · rw [traceRight_correlatedKet_orthonormal Ψ χ horth]
    simp

/-! ## §3. The dichotomy: same weights, opposite ontology -/

/-- **[Same pointer weights, opposite ontology]** — the weight agreement of §2, *and*: Weinberg's dynamics
models the fifth measurement step, which **is** the primitive collapse
(`IsPrimitiveCollapse .primitiveStateVectorCollapse`), while all four steps of the unitary/decoherent Everett
chain are **not** (`everettHeisenberg_excludes_primitive_collapse`).  At the pointer-weight level the primitive
collapse is observationally redundant — the records already carry the same numbers. -/
theorem collapse_dichotomy_same_weights
    {dS dE : Type*} [Fintype dS] [Fintype dE] [DecidableEq dS] [DecidableEq dE]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (K : CollapseKernel dS)
    (hzero : ∀ a : dS, leftZeroMode K (indicatorBasis a)) (m : dS) :
    (expectation (indicatorBasis m)
          (collapsedDistribution indicatorBasis indicatorBasis (fun ψ => Complex.normSq (Ψ ψ)))
          = Complex.normSq (Ψ m)
        ∧ ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m = (Complex.normSq (Ψ m) : ℂ))
      ∧ IsPrimitiveCollapse .primitiveStateVectorCollapse
      ∧ (¬ IsPrimitiveCollapse .unitaryInteraction
          ∧ ¬ IsPrimitiveCollapse .environmentalDecoherence
          ∧ ¬ IsPrimitiveCollapse .lindbladReducedDynamics
          ∧ ¬ IsPrimitiveCollapse .bornWeightedConditioning) :=
  ⟨⟨(weinberg_collapse_recovers_record_weight Ψ χ horth K hzero m).2.1,
      (weinberg_collapse_recovers_record_weight Ψ χ horth K hzero m).2.2⟩,
    rfl, everettHeisenberg_excludes_primitive_collapse⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence.weinberg_collapse_recovers_record_weight where
  formalizes @ "claim:weinberg-explicit-collapse-dynamics-and-collapse-free-everett-darwinism-records-produce-identical-pointer-born-weights",
  supported_by @ "paper:weinberg-2012-collapse-of-the-state-vector",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.born_weights_conserved_and_recovered",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics.traceRight_correlatedKet_orthonormal",
  caveat @ "epistemic:finite-delta-basis-instantiation-on-the-record-induced-density-weight-level-agreement-not-full-dynamical-equivalence"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence.collapse_dichotomy_same_weights where
  formalizes @ "claim:the-primitive-state-vector-collapse-is-observationally-redundant-at-the-pointer-weight-level-the-everett-records-carry-the-same-numbers",
  requires @ "claim:weinberg-explicit-collapse-dynamics-and-collapse-free-everett-darwinism-records-produce-identical-pointer-born-weights",
  supported_by @ "paper:weinberg-2012-collapse-of-the-state-vector",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates.everettHeisenberg_excludes_primitive_collapse",
  caveat @ "epistemic:redundancy-claim-scoped-to-pointer-born-weights-not-to-dynamical-or-interpretational-equivalence"

/- ZIL-END -/
