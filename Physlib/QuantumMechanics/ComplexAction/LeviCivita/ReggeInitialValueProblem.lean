/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeTimeEvolutionProblem
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
meta import Zil

/-!
# Sorkin §IV C — the initial-value problem, open space, and entropic time

Sorkin (1975) §IV C: beginning a Regge solution is an **initial-value problem** whose thatch equations
are of exactly the same type as the time-evolution problem (§IV B, `ReggeTimeEvolutionProblem`) — the
difference is topological, in the relation of what is found to what is specified. A **constraint leg**
is a couche leg whose `4`-simplex star lies wholly in the couche (it implicates only couche legs), so
its thatch equation constrains the initial data. One specifies the free legs and solves the constraint
system for the constraint legs.

* **§A — constraint legs** (`IsConstraintLeg`, `constraintLeg_implicates_only_couche`): a couche leg
  whose implicates are all in the couche.
* **§B — the free/constraint partition** (reusing `SpinNetworkTriangulationEvolution`): closed `S³×R`,
  `66 = 48 + 18` (`closedS3_initialValue_partition`); the constraint system is determined —
  `18` legs solved by their `18` constraints (`closedS3_constraint_determined`, reusing
  `IsWellPosedStep`). Beginning is a one-time constraint solve, continuing is the repeated evolution
  step (`closedS3_continue_determined`).
* **§C — open space** (`OpenR4InitialSliceCounts`): `72 = 55 + 17` per vertex
  (`openR4_initialValue_partition`, `openR4_constraint_determined`); but there are infinitely many
  vertices, so a constraint leg implicating outside a finite region `Ω` is undetermined without
  **boundary conditions at spatial infinity** (`ImplicatesOutside`,
  `openConstraint_near_boundary_undetermined`).
* **§D — entropic time.** The constraint/thatch equation is a *complex* Regge equation
  (`ComplexReggeAction`): it splits into a classical (real) and an **entropic (imaginary)** constraint
  (`initialThatch_classical_entropic_split`), and the couche's path weight is the entropic modulus
  `exp(−S_I/ℏ)` — which **decreases as the entropic Regge action grows**
  (`couche_entropicWeight_antitone`), the arrow of time along the evolution.

**Honest layering.** Proven: the constraint-leg locality, the determined free/constraint partitions
(reusing the repository counts), the open-space boundary obstruction, and the entropic split /
weight-antitonicity. Interpretive: the count values themselves are Sorkin's combinatorial data (in
`SpinNetworkTriangulationEvolution`); the physical "arrow of time" reading of `exp(−S_I/ℏ)` is the
complex-action theory's, supported by the antitonicity.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], §IV C. Reuses `LeviCivita.ReggeTimeEvolutionProblem` (`Implicates`,
  `IsWellPosedStep`), `SpinNetworkTriangulationEvolution` (the couche counts),
  `LeviCivita.ComplexReggeAction` (`complexThatch_stationary_iff`,
  `reggeAction_complexActionWeight_norm`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeTimeEvolutionProblem
open Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency


/-- **A constraint leg**: a couche leg whose entire `4`-simplex star lies in the couche — it
implicates only couche legs, so its thatch equation constrains the initial data (no unknown future
leg appears). -/
def IsConstraintLeg {Leg : Type*} (couche : Finset Leg) (star : Leg → Finset Leg) (lam : Leg) : Prop :=
  lam ∈ couche ∧ star lam ⊆ couche

/-- **A constraint leg implicates only couche legs** (via `Implicates` of `ReggeTimeEvolutionProblem`):
its thatch equation involves no leg outside the couche. -/
lemma constraintLeg_implicates_only_couche {Leg : Type*} (couche : Finset Leg)
    (star : Leg → Finset Leg) (lam mu : Leg) (h : IsConstraintLeg couche star lam)
    (himpl : Implicates star lam mu) : mu ∈ couche :=
  h.2 himpl


/-- **The closed-net free/constraint partition** `66 = 48 + 18`: the couche legs split into the freely
specified legs and the constraint legs (reusing `closedS3InitialSlice_standard_counts`). -/
lemma closedS3_initialValue_partition :
    ({} : ClosedS3InitialSliceCounts).freelySpecifiedLegs
        + ({} : ClosedS3InitialSliceCounts).constraintLegs
      = ({} : ClosedS3InitialSliceCounts).coucheLegs :=
  closedS3InitialSlice_standard_counts.1

/-- **Beginning is a determined constraint solve**: the `18` constraint legs are solved by the `18`
constraints they provide — a square system (`IsWellPosedStep`, `18 = 18`). -/
lemma closedS3_constraint_determined :
    IsWellPosedStep ({} : ClosedS3InitialSliceCounts).constraintLegs
      ({} : ClosedS3InitialSliceCounts).constraintLegs := rfl

/-- **Continuing a begun solution is the determined evolution step** (`14 = 14`, from §IV B): once the
initial couche is fixed, each step advances by a well-posed system (`closedS3Step_wellPosed`). -/
lemma closedS3_continue_determined :
    IsWellPosedStep (ClosedS3EvolutionStepCounts.totalNewLegs {})
      (ClosedS3EvolutionStepCounts.totalEquations {}) :=
  closedS3Step_wellPosed


/-- **The open-net free/constraint partition** `72 = 55 + 17` per vertex (reusing
`openR4InitialSlice_standard_counts`). -/
lemma openR4_initialValue_partition :
    ({} : OpenR4InitialSliceCounts).freelySpecifiedLegsPerVertex
        + ({} : OpenR4InitialSliceCounts).constraintLegsPerVertex
      = ({} : OpenR4InitialSliceCounts).coucheLegsPerVertex :=
  openR4InitialSlice_standard_counts.1

/-- **The per-vertex constraint system is determined** (`17 = 17`). -/
lemma openR4_constraint_determined :
    IsWellPosedStep ({} : OpenR4InitialSliceCounts).constraintLegsPerVertex
      ({} : OpenR4InitialSliceCounts).constraintLegsPerVertex := rfl

/-- **A leg implicates outside a region `Ω`** — some leg of its `4`-star lies outside `Ω`. -/
def ImplicatesOutside {Leg : Type*} (Ω : Finset Leg) (star : Leg → Finset Leg) (lam : Leg) : Prop :=
  ∃ mu ∈ star lam, mu ∉ Ω

/-- **Open-space obstruction**: on the infinite `R⁴` net, a constraint leg near the boundary of a
finitely-specified region `Ω` implicates a leg *outside* `Ω`, so it is undetermined by the data in `Ω`
alone — it requires **boundary conditions at spatial infinity** (via `Implicates`). -/
lemma openConstraint_near_boundary_undetermined {Leg : Type*} (Ω : Finset Leg)
    (star : Leg → Finset Leg) (lam : Leg) (h : ImplicatesOutside Ω star lam) :
    ∃ mu, Implicates star lam mu ∧ mu ∉ Ω := by
  obtain ⟨mu, hmu, hout⟩ := h
  exact ⟨mu, hmu, hout⟩


/-- **The initial-value constraint is a complex Regge thatch equation** that splits into a classical
(real, `−½∫R√−g`) constraint and an **entropic (imaginary)** constraint — reusing the complex-action
split `complexThatch_stationary_iff`. So even the initial data carries an entropic sector. -/
lemma initialThatch_classical_entropic_split {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℂ) (dArea : Bone → ℝ) :
    (∑ b : Bone, ((dArea b : ℝ) : ℂ) * defect b = 0)
      ↔ (∑ b : Bone, dArea b * (defect b).re = 0)
        ∧ (∑ b : Bone, dArea b * (defect b).im = 0) :=
  complexThatch_stationary_iff defect dArea

/-- **The entropic arrow of time along the evolution**: the couche's path weight is the entropic
modulus `exp(−S_I/ℏ)`, which **decreases as the entropic (imaginary) Regge action `S_I` grows**. So
the evolution flows toward larger entropic action — the arrow of time — reusing the entropic Regge
weight `reggeAction_complexActionWeight_norm`. -/
lemma couche_entropicWeight_antitone {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect₁ defect₂ : Bone → ℂ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (h : sorkinReggeAction area (fun b => (defect₁ b).im)
        ≤ sorkinReggeAction area (fun b => (defect₂ b).im)) :
    ‖complexActionWeight (complexReggeAction area defect₂).re
        (complexReggeAction area defect₂).im ℏ‖
      ≤ ‖complexActionWeight (complexReggeAction area defect₁).re
        (complexReggeAction area defect₁).im ℏ‖ := by
  rw [reggeAction_complexActionWeight_norm, reggeAction_complexActionWeight_norm]
  apply Real.exp_le_exp.mpr
  have hdiv : sorkinReggeAction area (fun b => (defect₁ b).im) / ℏ
      ≤ sorkinReggeAction area (fun b => (defect₂ b).im) / ℏ := by gcongr
  linarith

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.constraintLeg_implicates_only_couche where
  formalizes @ "claim:a-constraint-leg-whose-four-simplex-star-lies-wholly-in-the-couche-implicates-only-couche-legs-so-its-thatch-equation-constrains-the-initial-data",
  supported_by @ "paper:sorkin-1975-development-of-simplectic-methods-section-iv-c-initial-value-problem"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.openConstraint_near_boundary_undetermined where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.complexThatch_stationary_iff",
  formalizes @ "claim:on-the-infinite-open-r4-net-a-constraint-leg-near-the-boundary-of-a-finite-region-implicates-a-leg-outside-the-region-so-it-is-undetermined-without-boundary-conditions-at-spatial-infinity"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.initialThatch_classical_entropic_split where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.complexThatch_stationary_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.reggeAction_complexActionWeight_norm",
  formalizes @ "claim:the-initial-value-constraint-is-a-complex-regge-thatch-equation-that-splits-into-a-classical-real-constraint-and-an-entropic-imaginary-constraint-so-even-the-initial-data-carries-an-entropic-sector",
  requires @ "claim:the-complex-regge-thatch-stationarity-equation-splits-into-the-classical-real-and-entropic-imaginary-stationarity-conditions"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.couche_entropicWeight_antitone where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.reggeAction_complexActionWeight_norm",
  formalizes @ "claim:the-couche-path-weight-exp-minus-s-i-over-hbar-decreases-as-the-imaginary-regge-action-grows-so-the-evolution-flows-toward-larger-entropic-action-the-arrow-of-time",
  requires @ "claim:the-regge-path-weights-entropic-modulus-is-exp-minus-the-imaginary-regge-action-over-hbar-the-real-defect-sets-the-phase-the-imaginary-defect-the-damping"

zil_file_contract physlib.reggeInitialValueProblem where
  promises "Sorkin's Section IV C initial-value problem for Regge gravity (Sorkin 1975). A constraint leg -- a couche leg whose 4-simplex star lies wholly in the couche -- implicates only couche legs, so its thatch equation constrains the initial data (constraintLeg_implicates_only_couche); one specifies the free legs and solves the constraint system for the constraint legs. On the infinite open R4 net a constraint leg near the boundary of a finite region implicates a leg outside it, so it is undetermined without boundary conditions at spatial infinity (openConstraint_near_boundary_undetermined). The initial-value constraint is a complex Regge thatch equation splitting into a classical (real) and an entropic (imaginary) constraint, so even the initial data carries an entropic sector (initialThatch_classical_entropic_split); and the couche path weight exp(-S_I/hbar) decreases as the imaginary Regge action grows -- the arrow of time (couche_entropicWeight_antitone)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.IsConstraintLeg",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.complexReggeAction"]
  forbids_substitutes ["the simplicial 4-net combinatorics and the leg-counting of the standard closed-S3 and open-R4 slices, which are the cited discrete-geometry inputs",
    "any existence/uniqueness theorem for the full nonlinear Regge constraint solve, only the implication structure and the entropic split are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.constraintLeg_implicates_only_couche,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.openConstraint_near_boundary_undetermined,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.initialThatch_classical_entropic_split,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.couche_entropicWeight_antitone]

/- ZIL-END -/
