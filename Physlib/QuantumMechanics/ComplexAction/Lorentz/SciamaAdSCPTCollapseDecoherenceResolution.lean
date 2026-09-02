/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
meta import Zil

/-!
# Resolving the collapse/decoherence competition: collapse is the infinite-decoherence limit

`SciamaAdSCPTWeinbergCollapseBornEquivalence` showed Weinberg's explicit collapse and the collapse-free
Everett/Darwinism records **agree on every pointer Born weight** — but that leaves them as *competing dynamical
laws* claiming the same data.  This module resolves the competition on the repo's own derived grounds, in three
proved steps:

* **§1 — they differ, strictly, in the coherence sector.**  A *completed collapse* annihilates every coherence
  witness **exactly** (`collapsed_coherence_witness_vanishes`: any observable orthogonal to the pointer
  functions has expectation `0` in the collapsed distribution) — whereas the unitary/decoherent route leaves the
  interference fringe **strictly nonzero at every finite time** (`unitary_fringe_never_exactly_zero`: the
  visibility `exp(−Γt) > 0`, so the fringe `v·2Re D ≠ 0` whenever `Re D ≠ 0`).  Exactly-zero versus
  strictly-positive: the two are empirically **inequivalent in principle** (coherence-revival / echo
  experiments), so the competition is physical, not verbal.
* **§2 — collapse is the infinite-decoherence limit.**  The unitary route's visibility tends to `0` as
  `Γt → ∞` (`collapse_is_infinite_decoherence_limit`): the collapse description — exactly-zero coherence with
  the same pointer weights — is the **asymptotic effective limit** of the decoherent dynamics, not an
  independent rival law.
* **§3 — the resolution.**  `collapse_decoherence_resolution`: at any finite time the unitary route predicts
  everything collapse predicts (the same pointer weights, previous module) **plus** the strictly-nonzero
  residual coherence that collapse forbids; collapse is recovered as its `t → ∞` limit; and the unitary chain
  runs on the four non-collapse measurement steps alone — no fifth primitive.  The competition dissolves:
  **Weinberg-collapse is the infinite-decoherence effective description of Everett/Darwinism**, empirically
  distinguishable from it only through the finite-time coherence residue — which decoherence-limited revival
  experiments observe to be nonzero, and which the Born-derived unitary route predicts without any added
  postulate.

Honest scope: the discriminator and the limit are theorems in the finite models of the two programs (Weinberg's
finite kernel; the Sorkin-functional fringe at the golden-rule visibility); the empirical statement — that
observed revivals favour the nonzero-residue side — is experimental context, cited not formalized.  The
resolution is *subsumption* (same predictions + strictly more, fewer primitives, rival recovered as a limit),
not a refutation of collapse dynamics as mathematics.

**AQFT strengthening** (`SciamaAdSCPTCollapseModularCompatibility`): the resolution is independently confirmed
by the algebraic layer — a nontrivial collapse is a non-injective projection, so it cannot be a vN-algebraic
symmetry over a separating/faithful state (`faithful_state_standard`, Reeh–Schlieder `IsSeparating`) and is no
member of any Tomita–Takesaki modular flow (`modular_flow_injective`); the decoherence visibility, by contrast,
*is* the wedge-modular KMS eigenvalue (`visibility_is_wedgeModular`) and the collapse endpoint lies beyond
every finite entropic time.  Three independent selectors — the coherence residue, parsimony, and the AQFT
structure — all pick the same side.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution

open Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
open Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Filter

/-! ## §1. The strict discriminator: exactly zero (collapse) vs strictly nonzero (decoherence) -/

/-- **[A completed collapse annihilates every coherence witness — exactly]**: any observable `g` orthogonal to
all the pointer functions (`∑_ψ g·pointer_a = 0`) has expectation **exactly `0`** in the Weinberg collapsed
distribution.  The collapsed state carries no coherence whatsoever. -/
theorem collapsed_coherence_witness_vanishes {Ω A : Type*} [Fintype Ω] [Fintype A]
    (pointer weight : A → Ω → ℝ) (P : ProbabilityDensity Ω) (g : Ω → ℝ)
    (hwitness : ∀ a, ∑ ψ, g ψ * pointer a ψ = 0) :
    expectation g (collapsedDistribution pointer weight P) = 0 := by
  unfold expectation collapsedDistribution
  calc ∑ ψ, g ψ * ∑ a, pointer a ψ * expectation (weight a) P
      = ∑ ψ, ∑ a, g ψ * (pointer a ψ * expectation (weight a) P) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, ∑ ψ, g ψ * (pointer a ψ * expectation (weight a) P) := Finset.sum_comm
    _ = ∑ a, (∑ ψ, g ψ * pointer a ψ) * expectation (weight a) P := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ψ _ => by ring
    _ = 0 := by simp [hwitness]

/-- **[The unitary route's fringe is never exactly zero]** — at any finite time the decoherent visibility is
`exp(−Γt) > 0`, so for any interfering pair (`Re D(α,β) ≠ 0`) the decohered measure differs from the classical
sum: the coherence is suppressed but **strictly nonzero** — the exact opposite of the completed collapse. -/
theorem unitary_fringe_never_exactly_zero {ι : Type*} (D : ι → ι → ℂ) {α β : ι}
    (hD : (D α β).re ≠ 0) {prefactor : ℝ} (t : ℝ) (X : NobleMetal) :
    decoheredMeasure D (interferenceVisibility prefactor t X) α β
      ≠ quantalMeasure D α + quantalMeasure D β := by
  intro h
  have hterm : interferenceVisibility prefactor t X * (2 * (D α β).re) ≠ 0 :=
    mul_ne_zero (interferenceVisibility_pos prefactor t X).ne'
      (mul_ne_zero two_ne_zero hD)
  apply hterm
  unfold decoheredMeasure at h
  linarith

/-! ## §2. Collapse is the infinite-decoherence limit -/

/-- **[The collapse description is the `Γt → ∞` limit of the unitary route]** — the decoherent visibility tends
to `0`: `exp(−Γt) → 0` as `t → ∞`.  Exactly-zero coherence with the same pointer weights — i.e. the Weinberg
collapsed description — is the **asymptotic effective limit** of the unitary/decoherent dynamics, not an
independent law. -/
theorem collapse_is_infinite_decoherence_limit {prefactor : ℝ} (hp : 0 < prefactor) (X : NobleMetal) :
    Tendsto (fun t : ℝ => interferenceVisibility prefactor t X) atTop (nhds 0) := by
  unfold interferenceVisibility
  have hΓ : 0 < sdScatteringRate prefactor X := mul_pos hp (dBandDOS_pos X)
  have hlin : Tendsto (fun t : ℝ => sdScatteringRate prefactor X * t) atTop atTop :=
    Tendsto.const_mul_atTop hΓ tendsto_id
  simpa using hlin

/-! ## §3. The resolution: subsumption, not rivalry -/

/-- **[The collapse/decoherence competition, resolved]** — **(i)** the strict discriminator: the unitary route's
fringe is nonzero at every finite time, while the completed collapse annihilates every coherence witness
exactly — the two are empirically inequivalent in principle; **(ii)** the subsumption: the collapse description
is the `t → ∞` limit of the unitary visibility — a limit of the rival, not an independent law; **(iii)** the
economy: the unitary chain runs on the four non-collapse measurement steps alone
(`everettHeisenberg_excludes_primitive_collapse`) — no fifth primitive.  Same pointer weights
(`SciamaAdSCPTWeinbergCollapseBornEquivalence`), strictly more prediction (the finite-time coherence residue),
fewer primitives, rival recovered as a limit: the competition dissolves into **collapse = the
infinite-decoherence effective description of Everett/Darwinism**. -/
theorem collapse_decoherence_resolution {ι : Type*} (D : ι → ι → ℂ) {α β : ι}
    (hD : (D α β).re ≠ 0) {prefactor : ℝ} (hp : 0 < prefactor) (t : ℝ) (X : NobleMetal)
    {Ω A : Type*} [Fintype Ω] [Fintype A] (pointer weight : A → Ω → ℝ) (P : ProbabilityDensity Ω) :
    (decoheredMeasure D (interferenceVisibility prefactor t X) α β
        ≠ quantalMeasure D α + quantalMeasure D β
      ∧ ∀ g : Ω → ℝ, (∀ a, ∑ ψ, g ψ * pointer a ψ = 0) →
          expectation g (collapsedDistribution pointer weight P) = 0)
      ∧ Tendsto (fun s : ℝ => interferenceVisibility prefactor s X) atTop (nhds 0)
      ∧ (¬ IsPrimitiveCollapse .unitaryInteraction
          ∧ ¬ IsPrimitiveCollapse .environmentalDecoherence
          ∧ ¬ IsPrimitiveCollapse .lindbladReducedDynamics
          ∧ ¬ IsPrimitiveCollapse .bornWeightedConditioning) :=
  ⟨⟨unitary_fringe_never_exactly_zero D hD t X,
      fun g hg => collapsed_coherence_witness_vanishes pointer weight P g hg⟩,
    collapse_is_infinite_decoherence_limit hp X,
    Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates.everettHeisenberg_excludes_primitive_collapse⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution.collapsed_coherence_witness_vanishes where
  formalizes @ "claim:a-completed-weinberg-collapse-annihilates-every-pointer-orthogonal-coherence-witness-exactly",
  supported_by @ "paper:weinberg-2012-collapse-of-the-state-vector",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.collapsedDistribution_has_born_weights",
  caveat @ "epistemic:finite-weinberg-kernel-model"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution.collapse_decoherence_resolution where
  formalizes @ "claim:the-collapse-versus-decoherence-competition-dissolves-collapse-is-the-infinite-decoherence-limit-differing-only-by-the-strictly-nonzero-finite-time-coherence-residue",
  requires @ "claim:weinberg-explicit-collapse-dynamics-and-collapse-free-everett-darwinism-records-produce-identical-pointer-born-weights",
  requires @ "claim:a-completed-weinberg-collapse-annihilates-every-pointer-orthogonal-coherence-witness-exactly",
  supported_by @ "paper:weinberg-2012-collapse-of-the-state-vector",
  supported_by @ "paper:zurek-2021-emergence-of-the-classical-from-within-the-quantum-universe",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates.everettHeisenberg_excludes_primitive_collapse",
  caveat @ "epistemic:subsumption-in-the-finite-models-the-experimental-preference-for-nonzero-revivals-is-cited-context-not-formalized"

/- ZIL-END -/
