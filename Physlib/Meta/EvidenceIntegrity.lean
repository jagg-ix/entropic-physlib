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
# Evidence integrity: falsification, gates, and evidence class

Three checks a reproducibility audit needs but the current knowledge graph cannot express, each guided by
the OpenWave/CAT-EPT results audit:

* **Falsification and supersession.** A predicted value that was falsified (e.g. a clock frequency at 45%
  error) must not still be asserted, and a falsified claim must name a replacement or an open problem.
  These are stratified-negation rules over `derives` / `falsifiedBy` / `supersededBy` edges.
* **Structured gates.** A prediction is judged against explicit numeric gates (`residual ≤ 0.003`,
  `distance ≥ 0.05`, …). `Gate` makes each gate machine-readable and `gatesPass` composes them, so
  pass/fail is a checked predicate rather than a free string.
* **Evidence class.** Support that points only at internal lemmas is not the same as support from an
  external result. `internallySupportedOnly` flags a claim whose support is entirely internal.

The rule soundness is verified by `decide` on samples (the `Zil.Datalog` engine carries no soundness
proof), and the gate composition is proved universally on the pure side. All gated by
`#physlib_axiom_clean_all` + `#physlib_non_vacuous_all`; a build-time `run_cmd` fails unless the rule
suite is stratifiable.
-/

open Lean

namespace Physlib.Meta.EvidenceIntegrity

open Zil.Datalog

@[expose] public section

/-- A body/head pattern. -/
def pat (object : Zil.Datalog.Term) (relation : String) (subject : Zil.Datalog.Term) : Pattern :=
  { object := object, relation := relation, subject := subject }
/-- A ground fact atom. -/
def A (o r s : String) : Atom := { object := .symbol o, relation := r, subject := .symbol s }

/-! ### A — Falsification and supersession consistency -/

/-- A declaration still asserting (via `derives`) a prediction that has been `falsifiedBy` something. -/
def assertsFalsifiedRule : Rule :=
  { name := "assertsFalsified", head := pat (.variable "c") "assertsFalsified" (.variable "p"),
    literals := [.positive (pat (.variable "c") "derives" (.variable "p")),
                 .positive (pat (.variable "p") "falsifiedBy" (.variable "q"))] }

/-- Intensional helper: a claim `hasReplacement` if it is superseded or scoped as an open problem. -/
def hasReplacementBySupersededRule : Rule :=
  { name := "hasReplacement", head := pat (.variable "c") "hasReplacement" (.variable "c"),
    literals := [.positive (pat (.variable "c") "supersededBy" (.variable "r"))] }
def hasReplacementByOpenProblemRule : Rule :=
  { name := "hasReplacement", head := pat (.variable "c") "hasReplacement" (.variable "c"),
    literals := [.positive (pat (.variable "c") "open_problem_scope" (.variable "s"))] }

/-- **Consistency gap (stratified negation).** A falsified claim with no replacement and no open-problem
scope — a dangling dead end. -/
def danglingFalsifiedRule : Rule :=
  { name := "danglingFalsified", head := pat (.variable "c") "danglingFalsified" (.variable "c"),
    literals := [.positive (pat (.variable "c") "falsifiedBy" (.variable "q")),
                 .negative (pat (.variable "c") "hasReplacement" (.variable "c"))] }

/-- The falsification-consistency suite. -/
def falsificationRules : List Rule :=
  [assertsFalsifiedRule, hasReplacementBySupersededRule, hasReplacementByOpenProblemRule,
   danglingFalsifiedRule]

def assertsFalsifiedAtom (c p : String) : Atom :=
  { object := .symbol c, relation := "assertsFalsified", subject := .symbol p }
def danglingAtom (c : String) : Atom :=
  { object := .symbol c, relation := "danglingFalsified", subject := .symbol c }

/-- Sample: `c1` derives a falsified prediction; `c2` is falsified with no replacement; `c3` is falsified
but superseded. -/
def falsificationSample : Program :=
  { facts := [A "c1" "derives" "p1", A "p1" "falsifiedBy" "q1",
              A "c2" "falsifiedBy" "q2",
              A "c3" "falsifiedBy" "q3", A "c3" "supersededBy" "c4"]
    rules := falsificationRules }

set_option maxRecDepth 8000

/-- **A claim still deriving a falsified prediction is flagged.** -/
theorem asserts_falsified_fires :
    assertsFalsifiedAtom "c1" "p1" ∈ deriveProgram falsificationSample 4 := by decide

/-- **A falsified claim with no replacement is flagged as dangling.** -/
theorem dangling_fires : danglingAtom "c2" ∈ deriveProgram falsificationSample 4 := by decide

/-- **A falsified claim that was superseded is not dangling** — the stratified negation works. -/
theorem dangling_suppressed_when_replaced :
    danglingAtom "c3" ∉ deriveProgram falsificationSample 4 := by decide

/-! ### B — Structured prediction gates -/

/-- Whether a gate bounds its metric from above or below. -/
inductive GateDirection | atMost | atLeast
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A numeric acceptance gate: a metric bounded by a threshold, and the measured value. -/
structure Gate where
  metric    : String
  direction : GateDirection
  threshold : Float
  measured  : Float
  deriving Inhabited

/-- Did the measured value meet the threshold? (Runtime; `Float` comparison is not kernel-reducible.) -/
def Gate.satisfied (g : Gate) : Bool :=
  match g.direction with
  | .atMost  => g.measured ≤ g.threshold
  | .atLeast => g.threshold ≤ g.measured

/-- A prediction passes when every gate is satisfied. -/
def gatesPass (gates : List Gate) : Bool := gates.all Gate.satisfied

/-- The five acceptance gates for the M9.69 neutral non-Gaussian branch, transcribed from the audit. -/
def m9_69_gates : List Gate :=
  [{ metric := "stationary_residual", direction := .atMost,  threshold := 0.003,  measured := 0.001196453 },
   { metric := "seed_distance",       direction := .atMost,  threshold := 0.005,  measured := 0.0022446388 },
   { metric := "radius_spread",       direction := .atMost,  threshold := 0.02,   measured := 0.0127527297 },
   { metric := "gaussian_distance",   direction := .atLeast, threshold := 0.05,   measured := 0.0679012 },
   { metric := "boundary_fraction",   direction := .atMost,  threshold := 0.0001, measured := 7.18e-8 }]

/-- **A prediction passes exactly when every gate is satisfied** — pass/fail is the composition of the
individual gates, not a separate free-form verdict. -/
theorem gatesPass_iff (gates : List Gate) :
    gatesPass gates = true ↔ ∀ g ∈ gates, g.satisfied = true := by
  simp only [gatesPass, List.all_eq_true]

/-- **One unsatisfied gate fails the prediction** — no verdict can quietly outrun the gates. -/
theorem gates_fail_of_unsatisfied (gates : List Gate) (g : Gate) (hmem : g ∈ gates)
    (h : g.satisfied = false) : gatesPass gates = false := by
  rcases hb : gatesPass gates with _ | _
  · rfl
  · rw [gatesPass_iff] at hb
    exact absurd (hb g hmem) (by rw [h]; decide)

/-! ### C — Evidence class: internal support is not external evidence -/

/-- Intensional helper: a claim `hasExternal` support if any of its support is external. -/
def hasExternalRule : Rule :=
  { name := "hasExternal", head := pat (.variable "c") "hasExternal" (.variable "c"),
    literals := [.positive (pat (.variable "c") "externalSupport" (.variable "e"))] }

/-- **Evidence gap (stratified negation).** A claim whose support is entirely internal (only other
lemmas), with no external result behind it. -/
def internalOnlyRule : Rule :=
  { name := "internallySupportedOnly", head := pat (.variable "c") "internallySupportedOnly" (.variable "c"),
    literals := [.positive (pat (.variable "c") "internalSupport" (.variable "i")),
                 .negative (pat (.variable "c") "hasExternal" (.variable "c"))] }

/-- The evidence-class suite. -/
def evidenceRules : List Rule := [hasExternalRule, internalOnlyRule]

def internalOnlyAtom (c : String) : Atom :=
  { object := .symbol c, relation := "internallySupportedOnly", subject := .symbol c }

/-- Sample: `d1` has only internal support; `d2` also has external support. -/
def evidenceSample : Program :=
  { facts := [A "d1" "internalSupport" "lemA",
              A "d2" "internalSupport" "lemB", A "d2" "externalSupport" "paperX"]
    rules := evidenceRules }

/-- **A claim supported only internally is flagged.** -/
theorem internalOnly_fires :
    internalOnlyAtom "d1" ∈ deriveProgram evidenceSample 4 := by decide

/-- **A claim with external support is not flagged** — the stratified negation works. -/
theorem internalOnly_suppressed :
    internalOnlyAtom "d2" ∉ deriveProgram evidenceSample 4 := by decide

end

-- Build-time gate: the rule suites must be stratifiable, or the build fails.
run_cmd do
  let rules := Physlib.Meta.EvidenceIntegrity.falsificationRules ++
    Physlib.Meta.EvidenceIntegrity.evidenceRules
  let prog : Program := { facts := [], rules := rules }
  if prog.isStratified then
    logInfo "evidence-integrity: rules are stratifiable (safe negation)"
  else
    throwError "evidence-integrity: rules are NOT stratifiable — negation gate failed"

-- Gates demonstrated on the audit's real M9.69 neutral-branch acceptance data.
run_cmd
  logInfo s!"evidence-integrity: M9.69 neutral-branch gates pass = \
    {Physlib.Meta.EvidenceIntegrity.gatesPass Physlib.Meta.EvidenceIntegrity.m9_69_gates}"

end Physlib.Meta.EvidenceIntegrity

/-! ### Honesty bars -/

#physlib_axiom_clean_all [Physlib.Meta.EvidenceIntegrity.asserts_falsified_fires,
  Physlib.Meta.EvidenceIntegrity.dangling_fires,
  Physlib.Meta.EvidenceIntegrity.dangling_suppressed_when_replaced,
  Physlib.Meta.EvidenceIntegrity.gatesPass_iff,
  Physlib.Meta.EvidenceIntegrity.gates_fail_of_unsatisfied,
  Physlib.Meta.EvidenceIntegrity.internalOnly_fires,
  Physlib.Meta.EvidenceIntegrity.internalOnly_suppressed]
#physlib_non_vacuous_all [Physlib.Meta.EvidenceIntegrity.asserts_falsified_fires,
  Physlib.Meta.EvidenceIntegrity.dangling_fires,
  Physlib.Meta.EvidenceIntegrity.dangling_suppressed_when_replaced,
  Physlib.Meta.EvidenceIntegrity.gatesPass_iff,
  Physlib.Meta.EvidenceIntegrity.gates_fail_of_unsatisfied,
  Physlib.Meta.EvidenceIntegrity.internalOnly_fires,
  Physlib.Meta.EvidenceIntegrity.internalOnly_suppressed]
