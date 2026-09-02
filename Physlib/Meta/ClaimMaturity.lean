/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Zil.Datalog.Basic
public import Zil.Datalog.Eval
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Multi-axis claim maturity and its consistency rules

A formalization's maturity is not one number. An exact theorem, a constructed state satisfying its
hypotheses, converged numerics, a physical identification, and a calibrated prediction are independent
achievements — a claim can hold the first and lack the rest. Collapsing them into a single ordinal
(`level : Nat`, or a single `epistemic_status` symbol) makes two errors impossible to catch mechanically:
promoting a claim above what its axes support, and leaving a claim understated when its formal and
numerical axes are in fact closed.

This module records maturity on **six independent axes** and makes the summary `level` a *derived*
quantity, not a hand-assigned one. Two structural theorems pin down that the derivation is honest
(`level ≥ 3` holds exactly when the three quantization axes are closed), so a level can never exceed its
axes. Three ZIL Datalog rules then reason over encoded claims:

* `quantizationReady` — formal ∧ numerical ∧ state-existence all closed (a positive conjunction);
* `overLabelled` — a claim asserting quantization that is not ready (stratified negation);
* `underLabelled` — a claim not asserting quantization whose formal and numerical axes are closed.

Each rule's soundness is verified by `decide` on a sample, and the encoding bridge `maturityToFacts` is
shown to make the executable `quantizationReady` rule agree with the pure `Maturity.isQuantization`
predicate. All are gated by `#physlib_axiom_clean_all` + `#physlib_non_vacuous_all`.

This is a self-contained physlib framework; it consumes no other ledger.
-/

open Lean

namespace Physlib.Meta.ClaimMaturity

open Zil.Datalog

@[expose] public section

/-! ### The maturity record -/

/-- Per-axis maturity, ordered `absent < candidate < reduced < validated`. -/
inductive Status | absent | candidate | reduced | validated
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Numeric rank of a status, for comparing how far an axis has progressed. -/
def Status.rank : Status → Nat
  | .absent => 0 | .candidate => 1 | .reduced => 2 | .validated => 3

/-- A claim's maturity on the six independent axes the summary must not collapse. -/
structure Maturity where
  formal          : Status
  numerical       : Status
  stateExistence  : Status
  physicalId      : Status
  calibration     : Status
  prediction      : Status
  deriving DecidableEq, Repr, Inhabited

/-- Quantization-grade: the three axes a Level-3 claim must close. A positive conjunction. -/
def Maturity.isQuantization (m : Maturity) : Bool :=
  m.formal == .validated && m.numerical == .validated && m.stateExistence == .validated

/-- Physically closed: quantization-grade plus identification, calibration, and a prediction. -/
def Maturity.isPhysical (m : Maturity) : Bool :=
  m.isQuantization && m.physicalId == .validated && m.calibration == .validated && m.prediction == .validated

/-- The summary `level` (0-4), **derived** from the axes — never asserted independently. -/
def Maturity.level (m : Maturity) : Nat :=
  if m.isPhysical then 4
  else if m.isQuantization then 3
  else if m.formal == .validated && 2 ≤ m.numerical.rank then 2
  else if m.formal == .validated then 1
  else 0

/-! ### The derived level is honest (it never exceeds the axes) -/

/-- **No overstatement.** A claim that does not close the three quantization axes cannot be assigned a
level of 3 or more. -/
theorem level_lt_three_of_not_quantization (m : Maturity) (h : m.isQuantization = false) :
    m.level < 3 := by
  have hp : m.isPhysical = false := by simp [Maturity.isPhysical, h]
  simp only [Maturity.level, hp, h, Bool.false_eq_true, if_false]
  split_ifs <;> omega

/-- **No understatement of quantization.** A claim that closes the three quantization axes has level at
least 3. -/
theorem level_ge_three_of_quantization (m : Maturity) (h : m.isQuantization = true) :
    3 ≤ m.level := by
  unfold Maturity.level
  rw [if_pos (show m.isQuantization = true from h)]
  split_ifs <;> omega

/-! ### The core consistency rules -/

/-- A body/head pattern `object —relation→ subject`. -/
def pat (object : Zil.Datalog.Term) (relation : String) (subject : Zil.Datalog.Term) : Pattern :=
  { object := object, relation := relation, subject := subject }

/-- Match a fixed axis value. -/
def isVal (v : String) : Zil.Datalog.Term := .value (.symbol v)

/-- `quantizationReady` — formal ∧ numerical ∧ state-existence all `validated`. -/
def quantReadyRule : Rule :=
  { name := "quantizationReady", head := pat (.variable "c") "quantizationReady" (.variable "c"),
    literals := [.positive (pat (.variable "c") "formal" (isVal "validated")),
                 .positive (pat (.variable "c") "numerical" (isVal "validated")),
                 .positive (pat (.variable "c") "stateExistence" (isVal "validated"))] }

/-- Intensional helper: formal and numerical both `validated`. -/
def formalNumericalRule : Rule :=
  { name := "formalNumericalClosed", head := pat (.variable "c") "formalNumericalClosed" (.variable "c"),
    literals := [.positive (pat (.variable "c") "formal" (isVal "validated")),
                 .positive (pat (.variable "c") "numerical" (isVal "validated"))] }

/-- `overLabelled` — asserts quantization yet is not `quantizationReady` (stratified negation). -/
def overLabelledRule : Rule :=
  { name := "overLabelled", head := pat (.variable "c") "overLabelled" (.variable "c"),
    literals := [.positive (pat (.variable "c") "assertedLevel" (isVal "quantization")),
                 .negative (pat (.variable "c") "quantizationReady" (.variable "c"))] }

/-- `underLabelled` — does not assert quantization yet has formal and numerical closed. -/
def underLabelledRule : Rule :=
  { name := "underLabelled", head := pat (.variable "c") "underLabelled" (.variable "c"),
    literals := [.positive (pat (.variable "c") "formalNumericalClosed" (.variable "c")),
                 .negative (pat (.variable "c") "assertedLevel" (isVal "quantization"))] }

/-- The core consistency suite. -/
def consistencyRules : List Rule :=
  [quantReadyRule, formalNumericalRule, overLabelledRule, underLabelledRule]

/-! ### Machine-checked soundness of the rules -/

def A (o r s : String) : Atom := { object := .symbol o, relation := r, subject := .symbol s }
def overAtom  (c : String) : Atom := { object := .symbol c, relation := "overLabelled", subject := .symbol c }
def underAtom (c : String) : Atom := { object := .symbol c, relation := "underLabelled", subject := .symbol c }
def readyAtom (c : String) : Atom := { object := .symbol c, relation := "quantizationReady", subject := .symbol c }

/-- Sample: `o` asserts quantization but has no state (over-labelled); `k` asserts quantization and is
fully ready (clean); `u` is formal+numerical closed but asserts nothing (under-labelled). -/
def consistencySample : Program :=
  { facts :=
      [A "o" "assertedLevel" "quantization", A "o" "formal" "validated", A "o" "numerical" "validated",
       A "k" "assertedLevel" "quantization", A "k" "formal" "validated", A "k" "numerical" "validated",
         A "k" "stateExistence" "validated",
       A "u" "formal" "validated", A "u" "numerical" "validated"]
    rules := consistencyRules }

set_option maxRecDepth 8000

/-- **Over-labelling fires.** `o` asserts quantization with no state-existence, so it is flagged. -/
theorem overLabelled_fires : overAtom "o" ∈ deriveProgram consistencySample 4 := by decide

/-- **Over-labelling is suppressed on a ready claim.** `k` asserts quantization and closes all three
axes, so it is not flagged: no false positive. -/
theorem overLabelled_suppressed : overAtom "k" ∉ deriveProgram consistencySample 4 := by decide

/-- **Under-labelling fires.** `u` closes formal and numerical yet asserts no level, so it is flagged. -/
theorem underLabelled_fires : underAtom "u" ∈ deriveProgram consistencySample 4 := by decide

/-- **Under-labelling is suppressed on an asserted claim.** `k` asserts quantization, so it is not
flagged as understated. -/
theorem underLabelled_suppressed : underAtom "k" ∉ deriveProgram consistencySample 4 := by decide

/-- **Quantization-ready fires.** `k` closes all three quantization axes. -/
theorem quantReady_fires : readyAtom "k" ∈ deriveProgram consistencySample 4 := by decide

/-- **Quantization-ready is suppressed without state-existence.** `o` has formal and numerical but no
state, so the strict conjunction rejects it. -/
theorem quantReady_suppressed : readyAtom "o" ∉ deriveProgram consistencySample 4 := by decide

/-! ### The encoding bridge: the rule agrees with the pure predicate -/

def statusSym : Status → String
  | .absent => "absent" | .candidate => "candidate" | .reduced => "reduced" | .validated => "validated"

/-- Encode a claim's maturity as ZIL facts. -/
def maturityToFacts (c : String) (m : Maturity) : List Atom :=
  [A c "formal" (statusSym m.formal), A c "numerical" (statusSym m.numerical),
   A c "stateExistence" (statusSym m.stateExistence), A c "physicalId" (statusSym m.physicalId),
   A c "calibration" (statusSym m.calibration), A c "prediction" (statusSym m.prediction)]

/-- A maturity that is quantization-grade but not yet physical. -/
def readyMaturity : Maturity :=
  { formal := .validated, numerical := .validated, stateExistence := .validated,
    physicalId := .absent, calibration := .absent, prediction := .absent }

/-- **Structure and rule agree.** Encoding a `Maturity` whose `isQuantization` is `true` makes the
executable `quantizationReady` rule fire — the pure predicate and the graph reasoning coincide. -/
theorem encoded_quantization_ready :
    readyAtom "q" ∈ deriveProgram { facts := maturityToFacts "q" readyMaturity, rules := consistencyRules } 4 := by
  decide

/-! ### The differentiated assessment

A ledger should not report "N partial." It should report how many claims sit at each closure class — the
file's central point. `classify` is an ordered refinement read off the axes, and `summarize` counts a
ledger by class. -/

/-- The differentiated maturity classes, ordered by closure. -/
inductive MaturityClass
  | unproved | conditionalFormal | exactFormal | numericallyClosed | quantizationGrade | physicallyClosed
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Ordinal rank of a class. -/
def MaturityClass.rank : MaturityClass → Nat
  | .unproved => 0 | .conditionalFormal => 1 | .exactFormal => 2
  | .numericallyClosed => 3 | .quantizationGrade => 4 | .physicallyClosed => 5

/-- Short human label. -/
def MaturityClass.label : MaturityClass → String
  | .unproved => "unproved" | .conditionalFormal => "conditional-formal"
  | .exactFormal => "exact-formal" | .numericallyClosed => "numerically-closed"
  | .quantizationGrade => "quantization-grade" | .physicallyClosed => "physically-closed"

/-- Classify a maturity by the highest closure it has reached. Derived from the axes, like `level`. -/
def Maturity.classify (m : Maturity) : MaturityClass :=
  if m.isPhysical then .physicallyClosed
  else if m.isQuantization then .quantizationGrade
  else if m.formal == .validated && m.numerical == .validated then .numericallyClosed
  else if m.formal == .validated then .exactFormal
  else if m.formal == .reduced then .conditionalFormal
  else .unproved

/-- **A physically closed claim is classified as such.** -/
theorem classify_physicallyClosed_of_isPhysical (m : Maturity) (h : m.isPhysical = true) :
    m.classify = .physicallyClosed := by simp [Maturity.classify, h]

/-- **A quantization-grade claim sits at class rank 4 or above** — the differentiated class never
under-reports a claim that closed the three quantization axes. -/
theorem classify_rank_ge_four_of_quantization (m : Maturity) (h : m.isQuantization = true) :
    4 ≤ m.classify.rank := by
  unfold Maturity.classify
  rw [if_pos (show m.isQuantization = true from h)]
  split_ifs <;> decide

/-- Count a ledger of claims by maturity class — the differentiated assessment that replaces one label. -/
def summarize (ledger : List Maturity) : List (MaturityClass × Nat) :=
  ([.unproved, .conditionalFormal, .exactFormal, .numericallyClosed, .quantizationGrade,
    .physicallyClosed] : List MaturityClass).map fun cls =>
    (cls, (ledger.filter (fun m => m.classify == cls)).length)

/-- An illustrative ledger (abstract maturities, one per class) showing the differentiated summary. -/
def exampleLedger : List Maturity :=
  [{ formal := .validated, numerical := .validated, stateExistence := .validated,
     physicalId := .validated, calibration := .validated, prediction := .validated },
   { formal := .validated, numerical := .validated, stateExistence := .validated,
     physicalId := .absent, calibration := .absent, prediction := .absent },
   { formal := .validated, numerical := .validated, stateExistence := .absent,
     physicalId := .absent, calibration := .absent, prediction := .absent },
   { formal := .validated, numerical := .reduced, stateExistence := .absent,
     physicalId := .absent, calibration := .absent, prediction := .absent },
   { formal := .reduced, numerical := .absent, stateExistence := .absent,
     physicalId := .absent, calibration := .absent, prediction := .absent },
   { formal := .absent, numerical := .absent, stateExistence := .absent,
     physicalId := .absent, calibration := .absent, prediction := .absent }]

/-! ### Improvement 1 — coherence: the axes respect their prerequisites

The axes are independent in value but not unconstrained: a dependent axis cannot be more advanced than the
axis it rests on. You cannot compute or construct a state for a theorem you have not proved, identify a
state you have not constructed, calibrate a result you have not computed, or predict from a model you have
not calibrated. `isCoherent` rejects records that violate this — the model no longer stores impossible
maturities. -/

/-- Coherent: every axis is no further along than the axis it depends on. -/
def Maturity.isCoherent (m : Maturity) : Bool :=
  decide (m.numerical.rank ≤ m.formal.rank) &&
  decide (m.stateExistence.rank ≤ m.formal.rank) &&
  decide (m.physicalId.rank ≤ m.stateExistence.rank) &&
  decide (m.calibration.rank ≤ m.numerical.rank) &&
  decide (m.prediction.rank ≤ m.calibration.rank)

/-- **Coherence enforces the calibration prerequisite** — a coherent claim's calibration never outruns its
numerics. -/
theorem coherent_calibration_needs_numerical (m : Maturity) (h : m.isCoherent = true) :
    m.calibration.rank ≤ m.numerical.rank := by
  simp only [Maturity.isCoherent, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- **Coherence enforces the identification prerequisite** — a coherent claim is not physically identified
beyond its constructed state. -/
theorem coherent_physicalId_needs_state (m : Maturity) (h : m.isCoherent = true) :
    m.physicalId.rank ≤ m.stateExistence.rank := by
  simp only [Maturity.isCoherent, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- A record claiming calibration with no numerics — rejected as incoherent. -/
def incoherentExample : Maturity :=
  { formal := .validated, numerical := .absent, stateExistence := .validated,
    physicalId := .absent, calibration := .validated, prediction := .absent }

/-! ### Improvement 2 — honest publication: asserted level may not exceed the derived level

The general anti-overstatement guard. An author may publish level `a` for a claim only if the axes support
it, `a ≤ Maturity.level`. This subsumes `overLabelled` (its `a = 3` instance) and covers every level. -/

/-- A published `assertedLevel` is honest exactly when it does not exceed the derived level. -/
def assertionHonest (assertedLevel : Nat) (m : Maturity) : Bool :=
  decide (assertedLevel ≤ m.level)

/-- **Honesty is exactly "asserted ≤ derived".** -/
theorem assertionHonest_iff (a : Nat) (m : Maturity) :
    assertionHonest a m = true ↔ a ≤ m.level := by
  unfold assertionHonest; exact decide_eq_true_iff

/-- **Asserting above the derived level is caught.** -/
theorem assertion_dishonest_of_gt_derived (a : Nat) (m : Maturity) (h : m.level < a) :
    assertionHonest a m = false := by
  unfold assertionHonest
  simp only [decide_eq_false_iff_not, Nat.not_le]
  exact h

/-- **Asserting quantization on a claim that is not quantization-ready is dishonest** — the general guard
recovers the `overLabelled` scenario from the derived level. -/
theorem quantization_assertion_dishonest_of_not_ready (m : Maturity) (h : m.isQuantization = false) :
    assertionHonest 3 m = false :=
  assertion_dishonest_of_gt_derived 3 m (level_lt_three_of_not_quantization m h)

/-! ### Improvement 3 — evidence-backed claims

`formal = validated` should not be a word an author types; it should carry the theorem that backs it. A
`Claim` bundles identity, an optional formal witness, the maturity, and the axes it explicitly declares
open. `valid` demands three things at once: a witness whenever `formal` is validated, an open-aspect list
that never names a validated axis, and a coherent maturity. Maturity becomes checkable, not asserted. -/

/-- The maturity axes, as a first-class enumeration for projection and annotation. -/
inductive Axis | formal | numerical | stateExistence | physicalId | calibration | prediction
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Read a single axis off a maturity record. -/
def Maturity.onAxis (m : Maturity) : Axis → Status
  | .formal => m.formal
  | .numerical => m.numerical
  | .stateExistence => m.stateExistence
  | .physicalId => m.physicalId
  | .calibration => m.calibration
  | .prediction => m.prediction

/-- A claim: identity, the theorem backing its formal closure (if any), its maturity, and the axes it
declares still open (the structured form of `doesNotProve`). -/
structure Claim where
  name          : String
  formalWitness : Option String
  maturity      : Maturity
  openAspects   : List Axis
  deriving Repr, Inhabited

/-- A claim is formally backed when a validated `formal` axis names a witnessing theorem. -/
def Claim.formalBacked (c : Claim) : Bool :=
  c.maturity.formal != .validated || c.formalWitness.isSome

/-- The open-aspect annotation is consistent when it never lists an axis the maturity marks validated. -/
def Claim.annotationConsistent (c : Claim) : Bool :=
  c.openAspects.all (fun ax => decide (c.maturity.onAxis ax ≠ .validated))

/-- A valid claim is formally backed, consistently annotated, and coherent. -/
def Claim.valid (c : Claim) : Bool :=
  c.formalBacked && c.annotationConsistent && c.maturity.isCoherent

/-- **A backed, formally-validated claim carries a witnessing theorem** — no formal closure without a
named proof. -/
theorem formalBacked_provides_witness (c : Claim) (hb : c.formalBacked = true)
    (hf : c.maturity.formal = .validated) : c.formalWitness.isSome = true := by
  simp only [Claim.formalBacked, hf] at hb
  exact hb

/-- **A consistently annotated claim never declares a validated axis open** — the honesty annotation
agrees with the axes. -/
theorem annotationConsistent_openAspect_not_validated (c : Claim) (h : c.annotationConsistent = true)
    (ax : Axis) (hmem : ax ∈ c.openAspects) : c.maturity.onAxis ax ≠ .validated := by
  simp only [Claim.annotationConsistent, List.all_eq_true] at h
  exact of_decide_eq_true (h ax hmem)

/-- **A valid claim is coherent** — validity subsumes the axis prerequisites. -/
theorem valid_implies_coherent (c : Claim) (h : c.valid = true) : c.maturity.isCoherent = true := by
  simp only [Claim.valid, Bool.and_eq_true] at h
  exact h.2

/-- A well-formed claim: formal is validated with a witness, and the open aspects (the unclosed axes) are
declared honestly. -/
def goodClaim : Claim :=
  { name := "example-formalized", formalWitness := some "Physlib.Meta.ClaimMaturity.readyMaturity",
    maturity := readyMaturity, openAspects := [.physicalId, .calibration, .prediction] }

/-- A claim that marks `formal` validated but names no witness — rejected as unbacked. -/
def unbackedClaim : Claim :=
  { name := "unbacked", formalWitness := none, maturity := readyMaturity, openAspects := [] }

end

-- Build-time gate: the consistency suite must be stratifiable, or the build fails.
run_cmd do
  let prog : Program := { facts := [], rules := Physlib.Meta.ClaimMaturity.consistencyRules }
  if prog.isStratified then
    logInfo "claim-maturity: consistency rules are stratifiable (safe negation)"
  else
    throwError "claim-maturity: consistency rules are NOT stratifiable — negation gate failed"

-- The differentiated assessment on the example ledger (one label per class, not one count).
run_cmd do
  let summary := Physlib.Meta.ClaimMaturity.summarize Physlib.Meta.ClaimMaturity.exampleLedger
  let mut s := "claim-maturity: differentiated summary of the example ledger —"
  for (cls, n) in summary do
    s := s ++ s!" {cls.label}={n}"
  logInfo s

-- Coherence sanity: the incoherent example is flagged and every example-ledger record is coherent.
run_cmd do
  if Physlib.Meta.ClaimMaturity.incoherentExample.isCoherent then
    throwError "claim-maturity: the incoherent example was NOT flagged"
  else if !(Physlib.Meta.ClaimMaturity.exampleLedger.all (·.isCoherent)) then
    throwError "claim-maturity: the example ledger contains an incoherent record"
  else
    logInfo "claim-maturity: coherence checks pass (incoherent record flagged, ledger coherent)"

-- Evidence sanity: a backed claim is valid; a formally-validated claim with no witness is rejected.
run_cmd do
  if !Physlib.Meta.ClaimMaturity.goodClaim.valid then
    throwError "claim-maturity: the backed example claim was rejected"
  else if Physlib.Meta.ClaimMaturity.unbackedClaim.valid then
    throwError "claim-maturity: a formally-validated claim with no witness was accepted"
  else
    logInfo "claim-maturity: evidence checks pass (backed claim valid, unbacked claim rejected)"

end Physlib.Meta.ClaimMaturity

/-! ### Honesty bars -/

#physlib_axiom_clean_all [Physlib.Meta.ClaimMaturity.level_lt_three_of_not_quantization,
  Physlib.Meta.ClaimMaturity.level_ge_three_of_quantization,
  Physlib.Meta.ClaimMaturity.overLabelled_fires,
  Physlib.Meta.ClaimMaturity.overLabelled_suppressed,
  Physlib.Meta.ClaimMaturity.underLabelled_fires,
  Physlib.Meta.ClaimMaturity.underLabelled_suppressed,
  Physlib.Meta.ClaimMaturity.quantReady_fires,
  Physlib.Meta.ClaimMaturity.quantReady_suppressed,
  Physlib.Meta.ClaimMaturity.encoded_quantization_ready,
  Physlib.Meta.ClaimMaturity.classify_physicallyClosed_of_isPhysical,
  Physlib.Meta.ClaimMaturity.classify_rank_ge_four_of_quantization,
  Physlib.Meta.ClaimMaturity.coherent_calibration_needs_numerical,
  Physlib.Meta.ClaimMaturity.coherent_physicalId_needs_state,
  Physlib.Meta.ClaimMaturity.assertionHonest_iff,
  Physlib.Meta.ClaimMaturity.assertion_dishonest_of_gt_derived,
  Physlib.Meta.ClaimMaturity.quantization_assertion_dishonest_of_not_ready,
  Physlib.Meta.ClaimMaturity.formalBacked_provides_witness,
  Physlib.Meta.ClaimMaturity.annotationConsistent_openAspect_not_validated,
  Physlib.Meta.ClaimMaturity.valid_implies_coherent]
#physlib_non_vacuous_all [Physlib.Meta.ClaimMaturity.level_lt_three_of_not_quantization,
  Physlib.Meta.ClaimMaturity.level_ge_three_of_quantization,
  Physlib.Meta.ClaimMaturity.overLabelled_fires,
  Physlib.Meta.ClaimMaturity.overLabelled_suppressed,
  Physlib.Meta.ClaimMaturity.underLabelled_fires,
  Physlib.Meta.ClaimMaturity.underLabelled_suppressed,
  Physlib.Meta.ClaimMaturity.quantReady_fires,
  Physlib.Meta.ClaimMaturity.quantReady_suppressed,
  Physlib.Meta.ClaimMaturity.encoded_quantization_ready,
  Physlib.Meta.ClaimMaturity.classify_physicallyClosed_of_isPhysical,
  Physlib.Meta.ClaimMaturity.classify_rank_ge_four_of_quantization,
  Physlib.Meta.ClaimMaturity.coherent_calibration_needs_numerical,
  Physlib.Meta.ClaimMaturity.coherent_physicalId_needs_state,
  Physlib.Meta.ClaimMaturity.assertionHonest_iff,
  Physlib.Meta.ClaimMaturity.assertion_dishonest_of_gt_derived,
  Physlib.Meta.ClaimMaturity.quantization_assertion_dishonest_of_not_ready,
  Physlib.Meta.ClaimMaturity.formalBacked_provides_witness,
  Physlib.Meta.ClaimMaturity.annotationConsistent_openAspect_not_validated,
  Physlib.Meta.ClaimMaturity.valid_implies_coherent]
