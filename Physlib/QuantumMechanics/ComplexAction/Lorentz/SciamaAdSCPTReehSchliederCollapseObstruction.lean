/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseModularCompatibility
meta import Zil

/-!
# The Type III Reeh–Schlieder collapse obstruction, derived on the local net

`SciamaAdSCPTCollapseModularCompatibility` proved the collapse obstruction in the Type I finite shadow
(`faithful_state_standard`) and *cited* the Type III statement.  This module **derives** the Type III form from
the repo's existing operator-algebraic dependencies — the Reeh–Schlieder machinery
(`AlgebraicQFT.ReehSchliederCyclicSeparating`: `IsSeparating`, `IsCyclic`, `reehSchlieder_net`;
`ReehSchliederStandardVector.reehSchlieder_standard`), the Verch local net with Haag duality
(`AlgebraicQFTQuasifree.HadamardLocalNet`: `LocalNet`, `HaagDuality R(O^⊥)' = R(O)`), and the von Neumann
commutant (`StarAlgebraGNSFormCommutant.commutant`).

* `separating_positive_residue` — the Type III **positive coherence residue**: over a separating vector, every
  nonzero algebra element leaves a strictly positive vacuum residue, `a ≠ 0 → 0 < ‖aΩ‖` — the operator-algebraic
  mirror of the finite-model discriminator (`unitary_fringe_never_exactly_zero`): nothing local annihilates
  exactly.
* `reehSchlieder_no_local_collapse` — **the derivation on the net**: Haag duality + cyclicity of the
  causal-complement algebra (the Reeh–Schlieder input) ⟹ `Ω` is separating for `R(O)` (`reehSchlieder_net`) ⟹
  **no nonzero local operator implements an exact collapse annihilation**, `0 < ‖aΩ‖` for every nonzero
  `a ∈ R(O)`.  This is the Type III statement the finite audit shadowed, now proved from the net axioms.
* `reehSchlieder_no_collapse_both_sides` — with cyclicity on both sides, the full Reeh–Schlieder property holds
  for `R(O)` (`reehSchlieder_standard` — the very cyclic-and-separating precondition that **licenses the
  Tomita–Takesaki modular flow** for the local algebra, `KazamaTomitaTakesakiModular`), and the collapse
  obstruction holds **on both sides of the Haag-dual split**: no nonzero element of `R(O)` *or* of its
  commutant `R(O)'` annihilates the vacuum.
* `typeIII_collapse_obstruction_with_finite_shadow` — the capstone: the derived Type III obstruction and its
  finite Type I shadow (`faithful_state_standard`) side by side — the audit's separating argument now holds at
  both levels.

So the audit's verdict is completed at the operator-algebra level: over a Reeh–Schlieder vacuum, the exact
collapse endpoint is not locally implementable (Type III), exactly as the finite shadow said — and the same
Reeh–Schlieder property that forbids the local collapse is what *grants* the local algebra its modular flow.

Honest scope: the derivation is from the repo's net axioms (isotony, locality, Haag duality) and the
Reeh–Schlieder cyclicity hypotheses — the standard AQFT inputs; the physical input (cyclicity of the vacuum for
the complement algebra, from the spectrum condition/analyticity) is the hypothesis `hcyc`, as in Reeh–Schlieder
1961.  No Type III factor classification is used or claimed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §1. The Type III positive coherence residue -/

omit [CompleteSpace H] in
/-- **[Positive residue over a separating vector]** `a ∈ M`, `a ≠ 0 ⟹ 0 < ‖aΩ‖` — every nonzero algebra
element leaves a strictly positive vacuum residue: over a separating vector nothing annihilates exactly.  The
operator-algebraic mirror of the finite discriminator (`unitary_fringe_never_exactly_zero`). -/
theorem separating_positive_residue {M : Set (H →L[ℂ] H)} {Ω : H}
    (hsep : IsSeparating M Ω) {a : H →L[ℂ] H} (haM : a ∈ M) (ha : a ≠ 0) :
    0 < ‖a Ω‖ := by
  rw [norm_pos_iff]
  intro h0
  exact ha (hsep a haM h0)

/-! ## §2. The derivation on the Verch local net -/

/-- **[The Type III Reeh–Schlieder collapse obstruction, derived]** — from Haag duality `R(O^⊥)' = R(O)` and
cyclicity of the causal-complement algebra (the Reeh–Schlieder input), the vacuum is separating for `R(O)`
(`reehSchlieder_net`), so **no nonzero local operator implements an exact collapse annihilation**:
`0 < ‖aΩ‖` for every nonzero `a ∈ R(O)`. -/
theorem reehSchlieder_no_local_collapse {ι : Type*} [Preorder ι]
    (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcyc : IsCyclic (N.alg (N.compl O)) Ω)
    {a : H →L[ℂ] H} (haM : a ∈ N.alg O) (ha : a ≠ 0) :
    0 < ‖a Ω‖ :=
  separating_positive_residue (reehSchlieder_net N O Ω hdual hcyc) haM ha

/-- **[Both sides of the Haag-dual split, and the modular licence]** — with vacuum cyclicity for the region and
its complement: the full Reeh–Schlieder property holds for `R(O)` (`reehSchlieder_standard` — the
cyclic-and-separating precondition that licenses the Tomita–Takesaki modular flow of the local algebra), and
the collapse obstruction holds on **both** sides: no nonzero element of `R(O)` or of its commutant `R(O)'`
annihilates the vacuum. -/
theorem reehSchlieder_no_collapse_both_sides {ι : Type*} [Preorder ι]
    (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcycO : IsCyclic (N.alg O) Ω)
    (hcycComp : IsCyclic (N.alg (N.compl O)) Ω) :
    ReehSchlieder (N.alg O) Ω
      ∧ (∀ a ∈ N.alg O, a ≠ 0 → 0 < ‖a Ω‖)
      ∧ (∀ a' ∈ commutant (N.alg O), a' ≠ 0 → 0 < ‖a' Ω‖) := by
  refine ⟨reehSchlieder_standard N O Ω hdual hcycO hcycComp, ?_, ?_⟩
  · intro a haM ha
    exact reehSchlieder_no_local_collapse N O Ω hdual hcycComp haM ha
  · intro a' ha'M ha'
    exact separating_positive_residue (separating_commutant_of_cyclic (N.alg O) Ω hcycO) ha'M ha'

/-! ## §3. The capstone: Type III obstruction with its finite shadow -/

/-- **[The Type III obstruction and its Type I shadow, side by side]** — the derived operator-algebraic
obstruction (no nonzero local operator annihilates a Reeh–Schlieder vacuum) together with the finite
faithful-state shadow the audit used (`faithful_state_standard`): the separating argument against a locally
implemented exact collapse holds at both levels. -/
theorem typeIII_collapse_obstruction_with_finite_shadow {ι : Type*} [Preorder ι]
    (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcyc : IsCyclic (N.alg (N.compl O)) Ω)
    {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (hρ : IsUnit ρ.M.mat) :
    (∀ a ∈ N.alg O, a ≠ 0 → 0 < ‖a Ω‖)
      ∧ (∀ B, B * ρ.M.mat = 0 → B = 0) :=
  ⟨fun _ haM ha => reehSchlieder_no_local_collapse N O Ω hdual hcyc haM ha,
    (faithful_state_standard ρ hρ).1⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction.reehSchlieder_no_local_collapse where
  formalizes @ "claim:over-a-reeh-schlieder-vacuum-no-nonzero-local-operator-implements-an-exact-collapse-annihilation",
  requires @ "claim:the-decoherence-side-embeds-in-von-neumann-modular-and-entropic-time-structure-while-a-nontrivial-collapse-conflicts-with-all-three-as-fundamental-dynamics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating.reehSchlieder_net",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.HaagDuality",
  caveat @ "epistemic:vacuum-cyclicity-for-the-complement-algebra-is-the-hypothesis-supplied-by-the-spectrum-condition-in-reeh-schlieder-1961"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction.reehSchlieder_no_collapse_both_sides where
  formalizes @ "claim:the-reeh-schlieder-property-that-forbids-local-collapse-on-both-sides-of-the-haag-dual-split-is-the-same-precondition-that-licenses-the-tomita-takesaki-modular-flow",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector.reehSchlieder_standard",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating.separating_commutant_of_cyclic",
  caveat @ "epistemic:no-type-three-factor-classification-used-or-claimed"

/- ZIL-END -/
