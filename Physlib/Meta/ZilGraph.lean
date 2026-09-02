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
# The physlib knowledge graph as an inference program

Every `zil attach` block in physlib is an edge of a knowledge graph: a theorem linked by a relation
(`formalizes`, `supported_by`, `caveat`, `requires`, `derives`, `experimental_bound`, …) to a claim, a
paper, an assumption, or a numerical prediction — thousands of edges. Until now they were consumed only by
hand-rolled `run_cmd` cardinality loops (one per module, e.g. `Physlib.Meta.DerivedPredictions`), and the
inference rules that ought to run over them sat inert in comments.

This module defines an inference program over that graph for the ZIL Datalog engine
(`Zil.Datalog.deriveProgram`, stratified negation), so the rules run for real. Two layers here, and a
report surface in `Physlib.Meta.ZilGraphReport`:

* **The improvement rules** (`improvementRules`). Stratified-negation detectors for the gap classes that
  matter to CAT/EPT: `untestedRule` / `unclassifiedRule` / `unstatusedRule` flag `derives`-edges missing
  an `experimental_bound` / `prediction_class` / `epistemic_status`; `unsupportedRule` flags a
  `formalizes`-edge with no `supported_by`; `invalidStatusRule` flags an `epistemic_status` value outside
  the accepted vocabulary; `isDerivedByRule` is the reverse index physlib previously wrote only as a
  comment. Together the coverage and value rules are a declarative port of the hand-rolled
  `DerivedPredictions` ledger checks (the one part datalog cannot express — *at most one* of each, needing
  aggregation — stays in that module's `run_cmd`).
* **Machine-checked soundness** (`untested_fires_on_untested`, `untested_suppressed_when_tested`,
  `invalidStatus_fires_on_unknown`, `invalidStatus_suppressed_on_allowed`). Both negation patterns —
  missing-a-helper and out-of-vocabulary-against-a-reference-set — are shown by `decide` to fire on the
  offending edge and be *suppressed* on the clean one, so the stratification is verified, not merely
  executed. These are the gated (`#physlib_axiom_clean_all` / `#physlib_non_vacuous_all`) content, and a
  build-time `run_cmd` additionally fails the build unless the whole suite is stratifiable.

The coverage rules (`untested`/`unclassified`/`unstatused`) are one structural pattern — a positive base
relation minus its intensional has-a-helper — so the verified soundness of `untestedRule` certifies all
three; `invalidStatusRule` is the second, reference-set pattern, certified by its own pair.
-/

open Lean

namespace Physlib.Meta.ZilGraph

open Zil.Datalog

@[expose] public section

/-! ### The improvement rules -/

/-- A body/head pattern `object —relation→ subject` (physlib's `object # relation @ subject`). -/
def pat (object : Zil.Datalog.Term) (relation : String) (subject : Zil.Datalog.Term) : Pattern :=
  { object := object, relation := relation, subject := subject }

/-- Reverse index `constant —isDerivedBy→ declaration` from every `derives` edge (physlib's
rule-as-comment, now executed). -/
def isDerivedByRule : Rule :=
  { name := "isDerivedBy", head := pat (.variable "c") "isDerivedBy" (.variable "d")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c"))] }

/-- Intensional helper: a declaration `hasTest` if it carries any `experimental_bound` edge. -/
def hasTestRule : Rule :=
  { name := "hasTest", head := pat (.variable "d") "hasTest" (.variable "d")
    literals := [.positive (pat (.variable "d") "experimental_bound" (.variable "b"))] }

/-- **Gap rule (stratified negation).** A `derives` edge with no `experimental_bound` is an
`untestedPrediction` — a falsifiable claim the program has not anchored to data. -/
def untestedRule : Rule :=
  { name := "untestedPrediction", head := pat (.variable "d") "untestedPrediction" (.variable "c")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c")),
                 .negative (pat (.variable "d") "hasTest" (.variable "d"))] }

/-- Intensional helper: a declaration `hasSupport` if it carries any `supported_by` edge. -/
def hasSupportRule : Rule :=
  { name := "hasSupport", head := pat (.variable "d") "hasSupport" (.variable "d")
    literals := [.positive (pat (.variable "d") "supported_by" (.variable "p"))] }

/-- Intensional helper: a declaration is `openProblemScoped` if it carries an
`open_problem_scope` edge — an explicit declaration that the claim is an open-program
entry whose anchoring is the program scope itself, not a source. -/
def openProblemScopedRule : Rule :=
  { name := "openProblemScoped", head := pat (.variable "d") "openProblemScoped" (.variable "d")
    literals := [.positive (pat (.variable "d") "open_problem_scope" (.variable "p"))] }

/-- **Gap rule (stratified negation).** A `formalizes` edge with no `supported_by` is an
`unsupportedClaim` — a theorem asserting a claim while citing no source.  Claims that
explicitly declare themselves open-program entries (`open_problem_scope`) are exempt:
unsupported **by declared design** is not silently unsupported, and the report counts the
scoped population separately so the exemption stays visible. -/
def unsupportedRule : Rule :=
  { name := "unsupportedClaim", head := pat (.variable "d") "unsupportedClaim" (.variable "c")
    literals := [.positive (pat (.variable "d") "formalizes" (.variable "c")),
                 .negative (pat (.variable "d") "hasSupport" (.variable "d")),
                 .negative (pat (.variable "d") "openProblemScoped" (.variable "d"))] }

/-! #### Porting the `DerivedPredictions` ledger checks

`Physlib.Meta.DerivedPredictions` enforces, with a hand-rolled `run_cmd`, that every `derives` edge in its
ledger carries an `experimental_bound`, a `prediction_class`, and a valid `epistemic_status`. The coverage
half of each check (at least one) is a stratified-negation rule; `untestedRule` is the first, and the two
below are the others. The value check (`epistemic_status ∈ allowedEpistemicStatuses`) is
`invalidStatusRule`, which negates against an injected reference vocabulary.
The cardinality half (at most one) is not expressible in datalog without aggregation, so it stays in the
`run_cmd`. -/

/-- Intensional helper: a declaration `hasClass` if it carries any `prediction_class` edge. -/
def hasClassRule : Rule :=
  { name := "hasClass", head := pat (.variable "d") "hasClass" (.variable "d")
    literals := [.positive (pat (.variable "d") "prediction_class" (.variable "k"))] }

/-- **Coverage gap (stratified negation).** A `derives` edge with no `prediction_class`. -/
def unclassifiedRule : Rule :=
  { name := "unclassifiedPrediction", head := pat (.variable "d") "unclassifiedPrediction" (.variable "c")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c")),
                 .negative (pat (.variable "d") "hasClass" (.variable "d"))] }

/-- Intensional helper: a declaration `hasStatus` if it carries any `epistemic_status` edge. -/
def hasStatusRule : Rule :=
  { name := "hasStatus", head := pat (.variable "d") "hasStatus" (.variable "d")
    literals := [.positive (pat (.variable "d") "epistemic_status" (.variable "e"))] }

/-- **Coverage gap (stratified negation).** A `derives` edge with no `epistemic_status`. -/
def unstatusedRule : Rule :=
  { name := "unstatusedPrediction", head := pat (.variable "d") "unstatusedPrediction" (.variable "c")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c")),
                 .negative (pat (.variable "d") "hasStatus" (.variable "d"))] }

/-- The accepted `epistemic_status` vocabulary.

**Physical-prediction tier** (the original five): the first four are the `DerivedPredictions` ledger
values; `conditional-model` is the repo-wide category for a result that holds conditionally on an explicit
model's data (used outside the numerical-prediction ledger, e.g. in `Mathematics.DynamicalSystems`).

**Mathematical tier**: statuses for pure-mathematics results, which the physical-prediction scale has no
honest slot for — an `analytic-theorem` is neither an `inversion` nor `risky`. These carry
exact-theorem strength (see `statusStrictlyStronger`) and are held to no external evidence standard,
like `consistency-identity`. The members: `analytic-theorem`, `mathematical-identity`,
`exact-mathematical-identity`, `derived-identity`, `mathematical-analysis`,
`mathematical-construction`, `mathematical-counterexample`, `classification-theorem`,
`obstruction-theorem`, `bridge-theorem` (an exact theorem bridging two formalisms), `structural`.

**Conditional/loaded variants**: `conditional-analysis`, `conditional-model-theorem` and
`model-representation` are conditional-tier (they demand grounding, like `conditional-model`);
`data-loaded` is loaded-tier (it demands disclosure, like `ansatz-loaded`).

**Meta tier**: `repository-extension` marks repository-engineering work rather than a physical or
mathematical claim; it participates in no conformance demand and no strength comparison. -/
def allowedEpistemicStatuses : List String :=
  ["inversion", "consistency-identity", "ansatz-loaded", "risky", "conditional-model",
   -- mathematical tier
   "analytic-theorem", "mathematical-identity", "exact-mathematical-identity",
   "derived-identity", "mathematical-analysis", "mathematical-construction",
   "mathematical-counterexample", "classification-theorem", "obstruction-theorem",
   "bridge-theorem", "structural",
   -- conditional / loaded variants
   "conditional-analysis", "conditional-model-theorem", "model-representation", "data-loaded",
   -- meta
   "repository-extension"]

/-- The reference vocabulary as `allowedEpistemicStatus` self-edges, to be injected into the program
alongside the graph facts so `invalidStatusRule` can negate against it. -/
def allowedStatusFacts : List Atom :=
  allowedEpistemicStatuses.map fun v =>
    { object := .symbol v, relation := "allowedEpistemicStatus", subject := .symbol v }

/-- **Value gap (stratified negation against a reference set).** A declaration whose `epistemic_status`
value is not one of `allowedEpistemicStatuses`. -/
def invalidStatusRule : Rule :=
  { name := "invalidEpistemicStatus"
    head := pat (.variable "d") "invalidEpistemicStatus" (.variable "s")
    literals := [.positive (pat (.variable "d") "epistemic_status" (.variable "s")),
                 .negative (pat (.variable "s") "allowedEpistemicStatus" (.variable "s"))] }

/-- **Positive coverage (the constructive complement of the gaps).** A `derives` edge that carries all
three of `experimental_bound`, `prediction_class`, and `epistemic_status` is a fully documented
prediction — the publication-ready count, the positive form of what `DerivedPredictions` enforces. -/
def wellDocumentedRule : Rule :=
  { name := "wellDocumentedPrediction"
    head := pat (.variable "d") "wellDocumentedPrediction" (.variable "c")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c")),
                 .positive (pat (.variable "d") "hasTest" (.variable "d")),
                 .positive (pat (.variable "d") "hasClass" (.variable "d")),
                 .positive (pat (.variable "d") "hasStatus" (.variable "d"))] }

/-- **Consistency rule — a contradiction detector, not a coverage gap.** A declaration that
`assumes_primitive` a quantity — declares it a fundamental, *underived* input — which the graph *also*
derives (joined through the `isDerivedBy` reverse index) is flagged. This is the check that was missing
when a caveat called Newton's `G` a fundamental input while `Meta.DerivedPredictions` derives it
(`constant:newton-coupling-…`): the failure was that the primitiveness claim lived in free-text prose,
invisible to the graph. The remedy is structural — primitiveness/"is-an-input" claims must be stated as
`assumes_primitive @ "constant:X"` edges, never in a `caveat` string, so the reasoner can refute them
against the `derives` edges the same program already carries. -/
def assumedPrimitiveButDerivedRule : Rule :=
  { name := "assumedPrimitiveButDerived"
    head := pat (.variable "d") "assumedPrimitiveButDerived" (.variable "c")
    literals := [.positive (pat (.variable "d") "assumes_primitive" (.variable "c")),
                 .positive (pat (.variable "c") "isDerivedBy" (.variable "e"))] }

/-- Canonical reverse index `canonicalToken —canonicalDerivedBy→ declaration`: a declaration derives a
verbose `constant:` description that `denotes` a canonical quantity token. physlib's `derives` subjects are
verbose per-claim strings that never string-match across modules, so a canonical alias is the only way a
primitiveness claim stated with the *canonical* name can meet a derivation stated with a *verbose* one. -/
def canonicalDerivedByRule : Rule :=
  { name := "canonicalDerivedBy", head := pat (.variable "k") "canonicalDerivedBy" (.variable "d")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c")),
                 .positive (pat (.variable "c") "denotes" (.variable "k"))] }

/-- **Consistency rule (canonical / cross-module).** The cross-name form of `assumedPrimitiveButDerived`:
a declaration that `assumes_primitive` a *canonical* quantity token which some declaration derives under
*any verbose description aliased to it* (`denotes`) is flagged. The direct string join fires only within
one naming convention; this is what would actually catch a caveat calling Newton's canonical `G` an input
while the derivation carries the verbose `newton-coupling-is-…` description. -/
def assumedPrimitiveButCanonicallyDerivedRule : Rule :=
  { name := "assumedPrimitiveButCanonicallyDerived"
    head := pat (.variable "d") "assumedPrimitiveButCanonicallyDerived" (.variable "k")
    literals := [.positive (pat (.variable "d") "assumes_primitive" (.variable "k")),
                 .positive (pat (.variable "k") "canonicalDerivedBy" (.variable "e"))] }

/-- Intensional: a declaration `hasCaveat` if it carries any `caveat` edge. -/
def hasCaveatRule : Rule :=
  { name := "hasCaveat", head := pat (.variable "d") "hasCaveat" (.variable "d")
    literals := [.positive (pat (.variable "d") "caveat" (.variable "e"))] }

/-- Intensional: a premise `establishedPremise` if some declaration that `formalizes` it also carries an
`experimental_bound` (`hasTest`) — i.e. the premise is reached by evidence, not merely required. -/
def establishedPremiseRule : Rule :=
  { name := "establishedPremise", head := pat (.variable "c") "establishedPremise" (.variable "c")
    literals := [.positive (pat (.variable "d") "formalizes" (.variable "c")),
                 .positive (pat (.variable "d") "hasTest" (.variable "d"))] }

/-- **Consistency rule — evidence-scope gap.** A declaration that carries an `experimental_bound`
(`hasTest`, so it *looks* tested) but `requires` a premise that **no experimentally-bounded declaration
establishes**, while carrying no `caveat` disclosing the gap, is flagged. This mechanizes the OpenWave
M9.109 finding into a standing query: the anchor claims are experimentally anchored (Gouanère / Müller /
Margalit) yet the load-bearing premise `ΔS_I = mc²Δτ` is untested — the evidence does not reach the
premise. Disclosed claims (with a `caveat`) are exempt, so it flags only the *undisclosed* over-reach. -/
def undisclosedEvidenceGapRule : Rule :=
  { name := "undisclosedEvidenceGap"
    head := pat (.variable "d") "undisclosedEvidenceGap" (.variable "c")
    literals := [.positive (pat (.variable "d") "hasTest" (.variable "d")),
                 .positive (pat (.variable "d") "requires" (.variable "c")),
                 .negative (pat (.variable "c") "establishedPremise" (.variable "c")),
                 .negative (pat (.variable "d") "hasCaveat" (.variable "d"))] }

/-! #### Scenario-adaptive conformance (a policy-driven mechanism, not a fixed per-pattern rule)

The gap rules above each hard-code one pattern and hold *every* claim to it — so `unsupportedRule` flags an
exact `consistency-identity` for want of a source it does not need. The conformance mechanism instead makes
the required standard a **function of the claim's scenario** — its `epistemic_status` — read from an
*editable policy* `conformancePolicy` (`status —demands→ requirement`, injected like `allowedStatusFacts`).
One generic `nonconformant` rule then holds each claim only to what its status demands: a
`consistency-identity` demands nothing (never flagged); an `ansatz-loaded`/`risky` claim demands
*disclosure* (a `caveat` or a `supported_by`); a `conditional-model`/`inversion` demands *grounding* (a
source or a derivation). Re-tuning the audit is a policy row, not a new rule, and the same claim adapts to a
different bar as its status changes. The `demands` relation is pure data, so behaviour tracks the scenario. -/

/-- The conformance **policy** — editable data injected into the audit like `allowedStatusFacts`. Which
requirement each `epistemic_status` scenario demands; a status in no row (e.g. `consistency-identity`) is
held to no external standard. -/
def conformancePolicy : List Atom :=
  [{ object := .symbol "ansatz-loaded", relation := "demands", subject := .symbol "disclosure" },
   { object := .symbol "risky", relation := "demands", subject := .symbol "disclosure" },
   { object := .symbol "conditional-model", relation := "demands", subject := .symbol "grounding" },
   { object := .symbol "inversion", relation := "demands", subject := .symbol "grounding" },
   -- conditional / loaded variants of the mathematical extension follow their physical counterparts
   { object := .symbol "conditional-analysis", relation := "demands", subject := .symbol "grounding" },
   { object := .symbol "conditional-model-theorem", relation := "demands",
     subject := .symbol "grounding" },
   { object := .symbol "model-representation", relation := "demands", subject := .symbol "grounding" },
   { object := .symbol "data-loaded", relation := "demands", subject := .symbol "disclosure" }]

/-- Provision: a claim provides `disclosure` if it carries a `caveat`. -/
def providesDisclosureByCaveatRule : Rule :=
  { name := "provides.disclosure.caveat"
    head := pat (.variable "d") "provides" (.value (.symbol "disclosure"))
    literals := [.positive (pat (.variable "d") "caveat" (.variable "x"))] }

/-- Provision: a claim provides `disclosure` if it carries a `supported_by` source. -/
def providesDisclosureBySupportRule : Rule :=
  { name := "provides.disclosure.support"
    head := pat (.variable "d") "provides" (.value (.symbol "disclosure"))
    literals := [.positive (pat (.variable "d") "supported_by" (.variable "x"))] }

/-- Provision: a claim provides `grounding` if it carries a `supported_by` source. -/
def providesGroundingBySupportRule : Rule :=
  { name := "provides.grounding.support"
    head := pat (.variable "d") "provides" (.value (.symbol "grounding"))
    literals := [.positive (pat (.variable "d") "supported_by" (.variable "x"))] }

/-- Provision: a claim provides `grounding` if it `derives` something. -/
def providesGroundingByDerivesRule : Rule :=
  { name := "provides.grounding.derives"
    head := pat (.variable "d") "provides" (.value (.symbol "grounding"))
    literals := [.positive (pat (.variable "d") "derives" (.variable "x"))] }

/-- **The adaptive conformance check.** A claim is `nonconformant` for a requirement its
`epistemic_status` *demands* (per the injected `conformancePolicy`) but does not `provide`. The bar adapts
to the scenario: no policy row for a status ⇒ no demand ⇒ never flagged (exact identities are exempt);
change a policy row and every claim of that status re-tunes at once — the behaviour is data-driven, not a
fixed pattern. -/
def nonconformantRule : Rule :=
  { name := "nonconformant", head := pat (.variable "d") "nonconformant" (.variable "req")
    literals := [.positive (pat (.variable "d") "epistemic_status" (.variable "s")),
                 .positive (pat (.variable "s") "demands" (.variable "req")),
                 .negative (pat (.variable "d") "provides" (.variable "req"))] }

/-! #### Firm status-honesty gate: an exact identity may not rest on an undischarged physical postulate

The adaptive `nonconformant` mechanism deliberately exempts `consistency-identity` — an exact identity is
held to no external bar. That is right for a genuine identity but blind to a *mislabel*: a claim tagged
`consistency-identity` while it actually `requires` a physical postulate is not an exact identity, it is a
`conditional-model` wearing the wrong status. This gate catches exactly that, by pairing a **dynamical**
graph reading with one small classifying datum — the split the earlier flat `consistency-identity ∧
requires` rule lacked (it over-fired on ordinary math preconditions).

`dischargedPremise` reads the graph: a required premise some declaration `formalizes` or `derives` is
established in-program, so requiring it is ordinary exact-math structure (a lemma, a positivity/attainment
hypothesis, a satisfied PDE). That structural filter removes the bulk on its own. Among the *undischarged*
premises that remain, physical-vs-mathematical is irreducibly semantic — not readable from graph shape — so
it is supplied as data in `premiseKinds`. `statusOverclaim` then fires only on an exact identity whose
undischarged premise is a genuine *physical postulate* — an empirical assumption about nature, not a
derived result. A derived premise is not one, even when historically labelled `assumption:`: e.g.
`verlindeTemperature_at_horizon_is_hawking` requires screen equipartition, but equipartition is a *theorem*
(`Thermodynamics.verlinde_equipartition_from_NDOF`, from the classical equipartition theorem
`equipartition_quadraticDOF`), and its derivation is recorded as a `formalizes` edge, so it is **discharged**
and correctly **not** flagged. On the current graph the gate finds zero genuine over-claims; it is a standing
guard, and `unclassifiedExactPremise` surfaces any new undischarged premise of an exact identity not yet
classified so the datum stays auditable. -/

/-- A self-edge fact `token —relation→ token`, the injected-vocabulary idiom of `allowedStatusFacts`. -/
def selfEdge (relation token : String) : Atom :=
  { object := .symbol token, relation := relation, subject := .symbol token }

/-- Which `epistemic_status` values are exact, unconditional identities — the ones the firm honesty gate
holds to "no undischarged physical postulate." Only `consistency-identity`; injected like
`allowedStatusFacts` so the scope re-tunes by data, not by editing the rule. -/
def exactIdentityStatusFacts : List Atom :=
  [selfEdge "exactIdentityStatus" "consistency-identity"]

/-- The **premise-kind** classifying datum for the undischarged premises of exact identities. A premise is
either an empirical `physicalPostulatePremise` (an assumption about nature that could be false — requiring
it makes an "identity" conditional, the over-claim) or a `mathPrecondition` (a lemma / attainment /
positivity / non-degeneracy / domain restriction / convention / modelling setup — legitimate for an exact
identity). Only the physical-vs-math semantics that graph shape cannot decide lives here; the discharge
filter handles everything provable in-program. Extend it as `unclassifiedExactPremise` surfaces new
undischarged premises of exact identities. -/
def premiseKinds : List Atom :=
  [-- No current exact-identity premise is a bare physical postulate. The one physical-looking candidate,
   -- Verlinde screen equipartition, is DERIVED (`Thermodynamics.verlinde_equipartition_from_NDOF` from the
   -- classical equipartition theorem `equipartition_quadraticDOF`, Verlinde 2011's postulate upgraded to a
   -- theorem in the classical high-T limit). Its derivation is now recorded as a `formalizes` edge (in
   -- `Meta.DerivedPredictions`) under `claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom`,
   -- so the DISCHARGE filter handles it structurally — no datum entry needed. The `physicalPostulatePremise`
   -- relation stays defined for the rule + samples; the current graph simply has no instance of it.
   -- mathematical preconditions / conventions / modelling setups (legitimate for exact identities):
   selfEdge "mathPrecondition"
     "claim:the-attained-ground-state-obeys-the-derived-schrodinger-newton-virial-identity",
   selfEdge "mathPrecondition"
     "assumption:finite-state-relative-entropy-used-as-a-configuration-independent-imaginary-action-offset",
   selfEdge "mathPrecondition" "assumption:natural-units",
   selfEdge "mathPrecondition" "assumption:the-selected-tempered-potential-satisfies-poisson",
   -- the Chen–Vishwanath projective square `M*·M = βI` is a structure field of the supplied
   -- `ChenTimeReversalTwist` (used as `T.projective_square` in `insertChenTwist_twice`): an
   -- algebraic property of the input data, carried in binders — the exactness-with-hypotheses
   -- pattern, not a physical postulate.
   selfEdge "mathPrecondition"
     "assumption:the-virtual-twist-carries-a-checked-projective-square-M-star-M-equals-beta-I",
   selfEdge "mathPrecondition"
     "claim:the-state-actually-attains-the-constrained-minimum-on-the-normalized-compact-schwartz-core",
   selfEdge "mathPrecondition"
     "claim:nonzero-light-front-radial-coordinate-for-the-unsimplified-inverse-zeta-expression",
   selfEdge "mathPrecondition"
     "claim:the-light-front-endpoint-x-equals-one-is-excluded-from-the-spectator-density-formula",
   selfEdge "mathPrecondition"
     "claim:the-bulk-to-boundary-probe-obeys-the-zero-momentum-boundary-condition-pointwise-on-positive-ads-radius",
   -- the fundamental-solution hypothesis `Δ T = c·δ` of the generic tempered-convolution identity: a
   -- mathematical precondition (a distributional equation on the input), discharged for the Newton kernel
   selfEdge "mathPrecondition"
     "assumption:the-selected-complex-tempered-kernel-is-a-fundamental-solution-with-laplacian-c-times-dirac"]

/-- Intensional (structural, graph-driven): a premise is `dischargedPremise` if some declaration
`formalizes` it — established in-program, so requiring it is ordinary exact-math structure. -/
def dischargedByFormalizesRule : Rule :=
  { name := "dischargedPremise.formalizes"
    head := pat (.variable "c") "dischargedPremise" (.variable "c")
    literals := [.positive (pat (.variable "d") "formalizes" (.variable "c"))] }

/-- Intensional: a premise is `dischargedPremise` if some declaration `derives` it. -/
def dischargedByDerivesRule : Rule :=
  { name := "dischargedPremise.derives"
    head := pat (.variable "c") "dischargedPremise" (.variable "c")
    literals := [.positive (pat (.variable "d") "derives" (.variable "c"))] }

/-- Intensional (stratified negation): an exact-identity claim (`epistemic_status` an `exactIdentityStatus`)
that `requires` a premise no declaration discharges. These are the only candidates for a status over-claim;
the discharge filter removes premises the program proves, leaving the ones whose kind must be classified. -/
def exactIdentityBarePremiseRule : Rule :=
  { name := "exactIdentityBarePremise"
    head := pat (.variable "d") "exactIdentityBarePremise" (.variable "c")
    literals := [.positive (pat (.variable "d") "epistemic_status" (.variable "s")),
                 .positive (pat (.variable "s") "exactIdentityStatus" (.variable "s")),
                 .positive (pat (.variable "d") "requires" (.variable "c")),
                 .negative (pat (.variable "c") "dischargedPremise" (.variable "c"))] }

/-- **The firm honesty gate.** An exact identity whose undischarged premise is a `physicalPostulatePremise`
is a `statusOverclaim`: its `consistency-identity` label claims exact, unconditional truth while it in fact
rests on an assumption about nature. The remedy is a truthful status (`conditional-model`) or discharging
the postulate — not a caveat, so this does not exempt on `caveat` (unlike the disclosure detectors). -/
def statusOverclaimRule : Rule :=
  { name := "statusOverclaim", head := pat (.variable "d") "statusOverclaim" (.variable "c")
    literals := [.positive (pat (.variable "d") "exactIdentityBarePremise" (.variable "c")),
                 .positive (pat (.variable "c") "physicalPostulatePremise" (.variable "c"))] }

/-- **Coverage audit of the datum (stratified negation).** An undischarged premise of an exact identity
that is classified neither `physicalPostulatePremise` nor `mathPrecondition` — the gate cannot judge it, so
it is surfaced for triage. Keeps `premiseKinds` honest as the graph grows: a new bare premise shows up here
rather than being silently treated as harmless. -/
def unclassifiedExactPremiseRule : Rule :=
  { name := "unclassifiedExactPremise"
    head := pat (.variable "d") "unclassifiedExactPremise" (.variable "c")
    literals := [.positive (pat (.variable "d") "exactIdentityBarePremise" (.variable "c")),
                 .negative (pat (.variable "c") "physicalPostulatePremise" (.variable "c")),
                 .negative (pat (.variable "c") "mathPrecondition" (.variable "c"))] }

/-! #### Cross-name premise-derivation guard: discharge (and surface) a derived premise labelled `assumption:`

The discharge filter above matches a premise to its derivation by the SAME token string. But a premise
labelled `requires @ "assumption:X"` is often derived elsewhere under a DIFFERENT token — the equipartition
case: `verlinde_equipartition_from_NDOF` `formalizes`d `claim:screen-equipartition-…`, not `assumption:…`,
so the same-string join missed it and the fix had to rename the token. This is the `requires` analog of the
constant guard `assumedPrimitiveButCanonicallyDerived`, which defeats the same string mismatch for
`assumes_primitive` via the `canonicalAliases` `denotes` table. A curated `premiseAliases` table (relation
`premiseDenotes`, kept distinct from the constants' `denotes`) maps each `assumption:` premise whose content
the graph derives to its derived token; genuine postulates get no entry, so the table is the curated
allow/deny boundary. -/

/-- The curated **premise-alias table**: an `assumption:` premise token `premiseDenotes` the (differently
named) `claim:`/`constant:` token under which the graph actually derives its content. Injected like
`canonicalAliases`. Seeded with the three cross-name derived-but-assumed cases; genuine postulates
(`holographic-screen-bit-count` — though its area law is now the unique solution of inverse-square
phenomenology (`UniqueInverseSquareHolographicCoupling`) — `caticha-cafaro-inference-mass-…`,
`verlinde-displacement-entropy-ansatz` — now CHARACTERIZED by a conditional uniqueness theorem:
for nonzero acceleration it is the unique scalar entropy for which the entropic force at the Unruh
temperature reproduces inertia, hence equivalent to `F = ma` given those relations
(`DisplacementEntropyFromUnruhInertia`); the conditional entropic-action reading is a second premise
set for the same quantity.  Equivalence and rigidity, not a premise-free derivation —
`bisognano-wichmann-wedge`, the `model:` scaling defs) deliberately get NO entry. -/
def premiseAliases : List Atom :=
  [{ object := .symbol "assumption:complex-einstein-imaginary-sector-lambda-equals-kappa-S",
     relation := "premiseDenotes", subject := .symbol "claim:entropic-einstein-lambda-equals-kappa-s" },
   { object := .symbol "assumption:mass-clock-frequency-identification", relation := "premiseDenotes",
     subject := .symbol
       "claim:the-entropic-clock-time-unit-is-fixed-by-the-particle-mass-through-omega-c-equals-m-c-squared-over-hbar" },
   { object := .symbol "assumption:the-inference-scale-identification-G-equals-hbar-c-sigma-zero-to-the-fourth",
     relation := "premiseDenotes",
     subject := .symbol "constant:newton-coupling-is-hbar-c-times-inference-position-variance-to-the-fourth" }]

/-- **Discharge extension (the general form of the equipartition fix).** A premise `k` is discharged if it
`premiseDenotes` a token `c` that is itself discharged (some declaration `formalizes`/`derives` `c`). So a
cross-named derived premise is discharged WITHOUT renaming the physics token, and `exactIdentityBarePremise`
(hence the honesty gate) never fires on it. Positive recursion on `dischargedPremise`, like `dependsOn`. -/
def aliasDischargedPremiseRule : Rule :=
  { name := "dischargedPremise.alias"
    head := pat (.variable "k") "dischargedPremise" (.variable "k")
    literals := [.positive (pat (.variable "k") "premiseDenotes" (.variable "c")),
                 .positive (pat (.variable "c") "dischargedPremise" (.variable "c"))] }

/-- **The cross-name premise-mislabel detector (status-agnostic).** A declaration that `requires` an
`assumption:` premise `k` whose aliased token `c` the graph derives (`dischargedPremise c`) is flagged: the
premise is labelled an assumption but its content is proved. Broader than the honesty gate — it fires
regardless of the requirer's `epistemic_status`, so it surfaces token-hygiene cases (Λ=κS, ω_c, G-inference)
that sit on `ansatz-loaded`/`inversion` claims the `statusOverclaimRule` deliberately ignores. -/
def premiseAssumedButDerivedRule : Rule :=
  { name := "premiseAssumedButDerived"
    head := pat (.variable "d") "premiseAssumedButDerived" (.variable "k")
    literals := [.positive (pat (.variable "d") "requires" (.variable "k")),
                 .positive (pat (.variable "k") "premiseDenotes" (.variable "c")),
                 .positive (pat (.variable "c") "dischargedPremise" (.variable "c"))] }

/-- The improvement suite: a reverse index, three coverage gap detectors (missing `experimental_bound` /
`prediction_class` / `epistemic_status`), a source gap detector (missing `supported_by`), a value
validator for `epistemic_status`, the positive `wellDocumentedPrediction` coverage metric, the
`assumedPrimitiveButDerived` derived-vs-input guard with its canonical-alias companion, the
`undisclosedEvidenceGap` evidence-scope guard, and the **scenario-adaptive conformance** mechanism
(`provides.*` + `nonconformant`, driven by the editable `conformancePolicy`) — a declarative port of the
`DerivedPredictions` ledger checks plus the guards the OpenWave audits motivated, the last one policy-driven
rather than a fixed pattern. -/
def improvementRules : List Rule :=
  [isDerivedByRule, hasTestRule, untestedRule, hasSupportRule, openProblemScopedRule, unsupportedRule,
   hasClassRule, unclassifiedRule, hasStatusRule, unstatusedRule, invalidStatusRule,
   wellDocumentedRule, assumedPrimitiveButDerivedRule, canonicalDerivedByRule,
   assumedPrimitiveButCanonicallyDerivedRule, hasCaveatRule, establishedPremiseRule,
   undisclosedEvidenceGapRule, providesDisclosureByCaveatRule, providesDisclosureBySupportRule,
   providesGroundingBySupportRule, providesGroundingByDerivesRule, nonconformantRule,
   dischargedByFormalizesRule, dischargedByDerivesRule, aliasDischargedPremiseRule,
   exactIdentityBarePremiseRule, statusOverclaimRule, unclassifiedExactPremiseRule,
   premiseAssumedButDerivedRule]

/-! #### Dependency analysis: transitive `requires` closure and cycle detection

`requires` is the assumption edge (theorem → dependency or postulate). Its transitive closure `dependsOn`
is the full assumption footprint of a claim; a `circularDependency` — a declaration that transitively
requires itself — is a real soundness concern the flat graph hides. This is ordinary positive datalog (the
canonical recursive-closure example), kept separate from the negation-based gap suite because the closure
is `O(n²)` per step and usually only the cycle check is wanted. -/

/-- Base case: a direct `requires` edge is a dependency. -/
def dependsBaseRule : Rule :=
  { name := "dependsOn.base", head := pat (.variable "a") "dependsOn" (.variable "b")
    literals := [.positive (pat (.variable "a") "requires" (.variable "b"))] }

/-- Inductive case: dependency composes along `requires`. -/
def dependsTransRule : Rule :=
  { name := "dependsOn.trans", head := pat (.variable "a") "dependsOn" (.variable "c")
    literals := [.positive (pat (.variable "a") "requires" (.variable "b")),
                 .positive (pat (.variable "b") "dependsOn" (.variable "c"))] }

/-- A declaration that transitively requires itself: a circular assumption. -/
def circularDependencyRule : Rule :=
  { name := "circularDependency", head := pat (.variable "a") "circularDependency" (.variable "a")
    literals := [.positive (pat (.variable "a") "dependsOn" (.variable "a"))] }

/-- Transitive-closure and cycle rules over `requires`, run separately from `improvementRules`. -/
def dependencyRules : List Rule :=
  [dependsBaseRule, dependsTransRule, circularDependencyRule]

/-! #### Weakest-link audit: an exact identity may not transitively rest on a weaker-status result

`dependsOn` above closes over `requires` at the *token* level. Honest strength, though, flows between
DECLARATIONS: a claim's exact-identity label is only as strong as the weakest-status declaration it
transitively leans on. The bridge `dependsOnDecl(D, E)` connects declaration `D` to `E` when `D requires` a
premise that `E establishes` (`formalizes`/`derives` it, or `formalizes` a token that `D`'s premise
`premiseDenotes` — the cross-name case, reusing `premiseAliases`). Its transitive closure is the real
declaration-dependency DAG the flat edges do not give directly. `buriedConditionality(D, E)` then flags a
`consistency-identity` claim `D` that reaches, however deep, a declaration `E` whose `epistemic_status` is
strictly weaker (per the editable `statusStrictlyStronger` order) — the depth-generalization of
ProgramHealth's depth-1 hidden-debt, and the automated form of the Comparator's "what it does not prove
yet". Run separately from the gap suite (the closure is `O(n²)`), like `dependencyRules`. -/

/-- The statuses of exact-theorem strength: `consistency-identity` and the mathematical tier. -/
def exactStrengthStatuses : List String :=
  ["consistency-identity",
   "analytic-theorem", "mathematical-identity", "exact-mathematical-identity",
   "derived-identity", "mathematical-analysis", "mathematical-construction",
   "mathematical-counterexample", "classification-theorem", "obstruction-theorem",
   "bridge-theorem", "structural"]

/-- The conditional / loaded / falsifiable statuses every exact status strictly dominates. -/
def weakStrengthStatuses : List String :=
  ["ansatz-loaded", "conditional-model", "risky",
   "conditional-analysis", "conditional-model-theorem", "model-representation", "data-loaded"]

/-- The editable strength order: every exact-strength status is strictly stronger than any conditional,
loaded or falsifiable status — `statusStrictlyStronger(strong, weak)` facts generated as the product of
the two tier lists, injected like `allowedStatusFacts`. Extend with `inversion`/finer orderings by adding
rows — the semantic judgment lives in data. -/
def statusStrictlyStronger : List Atom :=
  exactStrengthStatuses.flatMap fun strong =>
    weakStrengthStatuses.map fun weak =>
      { object := .symbol strong, relation := "statusStrictlyStronger", subject := .symbol weak }

/-- Intensional: `E establishes P` if `E` `formalizes` `P`. -/
def establishesByFormalizesRule : Rule :=
  { name := "establishes.formalizes", head := pat (.variable "e") "establishes" (.variable "p")
    literals := [.positive (pat (.variable "e") "formalizes" (.variable "p"))] }

/-- Intensional: `E establishes P` if `E` `derives` `P`. -/
def establishesByDerivesRule : Rule :=
  { name := "establishes.derives", head := pat (.variable "e") "establishes" (.variable "p")
    literals := [.positive (pat (.variable "e") "derives" (.variable "p"))] }

/-- Intensional (cross-name): `E establishes P` if `E` `formalizes` a token `c` that the premise `P`
`premiseDenotes` — so the bridge sees a derivation recorded under a different token (the equipartition
pattern), reusing the `premiseAliases` table. -/
def establishesByAliasRule : Rule :=
  { name := "establishes.alias", head := pat (.variable "e") "establishes" (.variable "p")
    literals := [.positive (pat (.variable "e") "formalizes" (.variable "c")),
                 .positive (pat (.variable "p") "premiseDenotes" (.variable "c"))] }

/-- Base: `D dependsOnDecl E` if `D` `requires` a premise `E establishes`. -/
def dependsOnDeclBaseRule : Rule :=
  { name := "dependsOnDecl.base", head := pat (.variable "d") "dependsOnDecl" (.variable "e")
    literals := [.positive (pat (.variable "d") "requires" (.variable "p")),
                 .positive (pat (.variable "e") "establishes" (.variable "p"))] }

/-- Inductive: declaration dependency composes along `requires`∘`establishes` (positive recursion). -/
def dependsOnDeclTransRule : Rule :=
  { name := "dependsOnDecl.trans", head := pat (.variable "d") "dependsOnDecl" (.variable "e")
    literals := [.positive (pat (.variable "d") "dependsOnDecl" (.variable "f")),
                 .positive (pat (.variable "f") "requires" (.variable "p")),
                 .positive (pat (.variable "e") "establishes" (.variable "p"))] }

/-- Base (highest recall): `D dependsOnDecl E` if `D` is `supported_by` `E` — a direct declaration
reference (`supported_by @ "lean:E"`), no premise-token matching needed. `paper:`/`book:` targets self-
filter downstream (they carry no `epistemic_status`, so `buriedConditionality` never fires on them). -/
def dependsOnDeclBySupportRule : Rule :=
  { name := "dependsOnDecl.support", head := pat (.variable "d") "dependsOnDecl" (.variable "e")
    literals := [.positive (pat (.variable "d") "supported_by" (.variable "e"))] }

/-- Inductive: dependency composes along `supported_by` as well. -/
def dependsOnDeclBySupportTransRule : Rule :=
  { name := "dependsOnDecl.support.trans", head := pat (.variable "d") "dependsOnDecl" (.variable "e")
    literals := [.positive (pat (.variable "d") "dependsOnDecl" (.variable "f")),
                 .positive (pat (.variable "f") "supported_by" (.variable "e"))] }

/-- **The weakest-link detector.** A claim `D` whose `epistemic_status` is strictly stronger (per
`statusStrictlyStronger`) than a declaration `E` it transitively `dependsOnDecl` — an exact identity
buried-resting on a conditional/falsifiable result.  The negative literal is the **disclosure
exemption**: a `discloses @ "lean:E"` edge on `D` states, in the graph itself, that `D` knowingly
rests on the weaker-status `E` — and a *disclosed* conditionality is by definition not buried
(the per-pair triage that motivated the relation is `analysis/buried-conditionality-triage.md`).
Stratified negation on an extensional relation, like the gap rules. -/
def buriedConditionalityRule : Rule :=
  { name := "buriedConditionality", head := pat (.variable "d") "buriedConditionality" (.variable "e")
    literals := [.positive (pat (.variable "d") "epistemic_status" (.variable "sd")),
                 .positive (pat (.variable "e") "epistemic_status" (.variable "se")),
                 .positive (pat (.variable "d") "dependsOnDecl" (.variable "e")),
                 .positive (pat (.variable "sd") "statusStrictlyStronger" (.variable "se")),
                 .negative (pat (.variable "d") "discloses" (.variable "e"))] }

/-- Intensional: `P` is `establishedToken` if some declaration `establishes` it (formalizes / derives /
cross-name alias). Its complement — a required token nothing establishes — is a primitive input. -/
def establishedTokenRule : Rule :=
  { name := "establishedToken", head := pat (.variable "p") "establishedToken" (.variable "p")
    literals := [.positive (pat (.variable "e") "establishes" (.variable "p"))] }

/-- Base: `D`'s own undischarged `requires` premise is a primitive premise of `D`. -/
def directPrimitivePremiseRule : Rule :=
  { name := "transitivePrimitivePremise.direct"
    head := pat (.variable "d") "transitivePrimitivePremise" (.variable "p")
    literals := [.positive (pat (.variable "d") "requires" (.variable "p")),
                 .negative (pat (.variable "p") "establishedToken" (.variable "p"))] }

/-- **The transitive primitive-premise footprint (the grounding tree's leaves).** `D` transitively
`dependsOnDecl` a declaration `E` that `requires` a premise `P` no declaration `establishes` — a bare
postulate the whole chain rests on. op3.md's "transitive primitive premises" / the assumption ledger; the
per-claim postulate set that measures whether work reduces assumptions rather than adding interfaces. -/
def transitivePrimitivePremiseRule : Rule :=
  { name := "transitivePrimitivePremise"
    head := pat (.variable "d") "transitivePrimitivePremise" (.variable "p")
    literals := [.positive (pat (.variable "d") "dependsOnDecl" (.variable "e")),
                 .positive (pat (.variable "e") "requires" (.variable "p")),
                 .negative (pat (.variable "p") "establishedToken" (.variable "p"))] }

/-- Weakest-link + assumption-ledger rules: the declaration-dependency closure, the buried-conditionality
detector, and the transitive primitive-premise footprint. Run separately (the closure is `O(n²)`), like
`dependencyRules`; stratifiable (the primitive-premise rules negate `establishedToken`, one stratum up). -/
def weakestLinkRules : List Rule :=
  [establishesByFormalizesRule, establishesByDerivesRule, establishesByAliasRule,
   dependsOnDeclBaseRule, dependsOnDeclTransRule, dependsOnDeclBySupportRule,
   dependsOnDeclBySupportTransRule, buriedConditionalityRule,
   establishedTokenRule, directPrimitivePremiseRule, transitivePrimitivePremiseRule]

/-! ### Machine-checked soundness of the gap detector

A three-edge sample graph: `D1` derives `C1` and *is* experimentally bounded; `D2` derives `C2` and is
not. Under stratified negation the program must flag exactly `D2`. -/

/-- The sample graph: the `hasTest` helper and the `untestedPrediction` gap rule over three edges. -/
def sampleGraph : Program :=
  { facts := [{ object := .symbol "D1", relation := "derives", subject := .symbol "C1" },
              { object := .symbol "D1", relation := "experimental_bound", subject := .symbol "B1" },
              { object := .symbol "D2", relation := "derives", subject := .symbol "C2" }]
    rules := [hasTestRule, untestedRule] }

/-- The atom asserting that declaration `d`'s prediction `c` is untested. -/
def untestedAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "untestedPrediction", subject := .symbol c }

-- kernel reduction of the stratified closure needs headroom over the default depth
set_option maxRecDepth 8000

/-- **The gap rule fires on an untested prediction.** `D2` derives `C2` with no experimental bound, so
the closure contains the `untestedPrediction` atom for it. -/
theorem untested_fires_on_untested :
    untestedAtom "D2" "C2" ∈ deriveProgram sampleGraph 4 := by decide

/-- **The gap rule is suppressed on a tested prediction** — the stratified negation works. `D1` derives
`C1` but *has* an `experimental_bound`, so it is not flagged: no false positive. -/
theorem untested_suppressed_when_tested :
    untestedAtom "D1" "C1" ∉ deriveProgram sampleGraph 4 := by decide

/-- Sample for the open-problem exemption of the unsupported-claim gap: `U1` formalizes a
claim with no support and no scope → flagged; `U2` is identical but declares
`open_problem_scope` → exempt (unsupported by declared design, counted separately in the
report). -/
def openProblemSample : Program :=
  { facts := [{ object := .symbol "U1", relation := "formalizes", subject := .symbol "CU1" },
              { object := .symbol "U2", relation := "formalizes", subject := .symbol "CU2" },
              { object := .symbol "U2", relation := "open_problem_scope",
                subject := .symbol "scope-x" }]
    rules := [hasSupportRule, openProblemScopedRule, unsupportedRule] }

/-- The atom flagging `d` as formalizing the unsupported claim `c`. -/
def unsupportedAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "unsupportedClaim", subject := .symbol c }

/-- **The gap still fires on an unscoped unsupported claim.** -/
theorem unsupportedClaim_fires_on_unscoped :
    unsupportedAtom "U1" "CU1" ∈ deriveProgram openProblemSample 4 := by decide

/-- **The declared open-program entry is exempt.** -/
theorem unsupportedClaim_suppressed_on_open_problem_scope :
    unsupportedAtom "U2" "CU2" ∉ deriveProgram openProblemSample 4 := by decide

/-- A status sample: the reference vocabulary plus one valid (`risky`) and one out-of-vocabulary
(`speculative`) `epistemic_status` edge. The validator must flag exactly `D4`. -/
def statusSample : Program :=
  { facts := allowedStatusFacts ++
      [{ object := .symbol "D3", relation := "epistemic_status", subject := .symbol "risky" },
       { object := .symbol "D4", relation := "epistemic_status", subject := .symbol "speculative" }]
    rules := [invalidStatusRule] }

/-- The atom flagging declaration `d`'s status value `s` as outside the reference vocabulary. -/
def invalidStatusAtom (d s : String) : Atom :=
  { object := .symbol d, relation := "invalidEpistemicStatus", subject := .symbol s }

/-- **The validator fires on an out-of-vocabulary status.** `D4` carries `speculative`, not an allowed
`epistemic_status`, so it is flagged — negation against the injected reference vocabulary. -/
theorem invalidStatus_fires_on_unknown :
    invalidStatusAtom "D4" "speculative" ∈ deriveProgram statusSample 4 := by decide

/-- **The validator is suppressed on an allowed status.** `D3` carries `risky`, which is in the reference
vocabulary, so it is not flagged: no false positive. -/
theorem invalidStatus_suppressed_on_allowed :
    invalidStatusAtom "D3" "risky" ∉ deriveProgram statusSample 4 := by decide

/-- A dependency chain `a → b → c` via `requires`. -/
def dependencySample : Program :=
  { facts := [{ object := .symbol "a", relation := "requires", subject := .symbol "b" },
              { object := .symbol "b", relation := "requires", subject := .symbol "c" }]
    rules := dependencyRules }

/-- The atom asserting `a` transitively depends on `c`. -/
def dependsAtom (a c : String) : Atom :=
  { object := .symbol a, relation := "dependsOn", subject := .symbol c }

/-- **The transitive closure reaches two hops out.** `a requires b` and `b requires c`, so `a` depends on
`c` even though there is no direct edge — the full assumption footprint, not just the immediate one. -/
theorem depends_transitively :
    dependsAtom "a" "c" ∈ deriveProgram dependencySample 8 := by decide

/-- A cyclic dependency `a → b → a`. -/
def cyclicSample : Program :=
  { facts := [{ object := .symbol "a", relation := "requires", subject := .symbol "b" },
              { object := .symbol "b", relation := "requires", subject := .symbol "a" }]
    rules := dependencyRules }

/-- **A `requires` cycle is detected.** `a` transitively requires itself, so it is flagged circular — the
soundness check the flat graph cannot make. -/
theorem cycle_is_detected :
    ({ object := .symbol "a", relation := "circularDependency", subject := .symbol "a" } : Atom)
      ∈ deriveProgram cyclicSample 8 := by decide

/-- A documentation sample: `D5` derives `C5` with the full metadata triple; `D6` derives `C6` with only
an `experimental_bound`. The positive rule must accept exactly `D5`. -/
def documentedSample : Program :=
  { facts := [{ object := .symbol "D5", relation := "derives", subject := .symbol "C5" },
              { object := .symbol "D5", relation := "experimental_bound", subject := .symbol "B5" },
              { object := .symbol "D5", relation := "prediction_class", subject := .symbol "K5" },
              { object := .symbol "D5", relation := "epistemic_status", subject := .symbol "risky" },
              { object := .symbol "D6", relation := "derives", subject := .symbol "C6" },
              { object := .symbol "D6", relation := "experimental_bound", subject := .symbol "B6" }]
    rules := [hasTestRule, hasClassRule, hasStatusRule, wellDocumentedRule] }

/-- The atom certifying declaration `d`'s prediction `c` as fully documented. -/
def wellDocumentedAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "wellDocumentedPrediction", subject := .symbol c }

/-- **The positive rule accepts a fully documented prediction.** `D5` carries all three metadata edges,
so it is certified. -/
theorem wellDocumented_accepts_complete :
    wellDocumentedAtom "D5" "C5" ∈ deriveProgram documentedSample 4 := by decide

/-- **The positive rule rejects an incomplete one.** `D6` has an `experimental_bound` but no
`prediction_class` or `epistemic_status`, so it is not certified — the conjunction is strict. -/
theorem wellDocumented_rejects_incomplete :
    wellDocumentedAtom "D6" "C6" ∉ deriveProgram documentedSample 4 := by decide

/-- A primitiveness sample: `Dg` derives constant `G` (so `G isDerivedBy Dg`); `Dbad` `assumes_primitive`
`G` — a contradiction, since the program derives it; `Dok` `assumes_primitive` `Xprim`, which nothing
derives — a legitimate fundamental input. The rule must flag exactly `Dbad`. This is the miniature of the
real slip: a caveat calling Newton's `G` a fundamental input while `DerivedPredictions` derives it. -/
def primitiveSample : Program :=
  { facts := [{ object := .symbol "Dg", relation := "derives", subject := .symbol "G" },
              { object := .symbol "Dbad", relation := "assumes_primitive", subject := .symbol "G" },
              { object := .symbol "Dok", relation := "assumes_primitive", subject := .symbol "Xprim" }]
    rules := [isDerivedByRule, assumedPrimitiveButDerivedRule] }

/-- The atom flagging declaration `d`'s primitive-claim on `c` as contradicted by a derivation. -/
def assumedPrimitiveButDerivedAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "assumedPrimitiveButDerived", subject := .symbol c }

/-- **The consistency rule fires when a derived quantity is claimed primitive.** `Dbad` calls `G` a
fundamental input, but `Dg` derives it, so it is flagged — the check that would have caught the `G`-input
slip had the claim been stated structurally. -/
theorem assumedPrimitive_fires_on_derived :
    assumedPrimitiveButDerivedAtom "Dbad" "G" ∈ deriveProgram primitiveSample 4 := by decide

/-- **Suppressed on a genuinely primitive quantity.** `Dok` calls `Xprim` primitive and nothing derives
it, so it is not flagged: no false positive on a real fundamental input. -/
theorem assumedPrimitive_suppressed_on_genuine :
    assumedPrimitiveButDerivedAtom "Dok" "Xprim" ∉ deriveProgram primitiveSample 4 := by decide

/-- The curated **canonical-alias table**: a verbose `constant:` description `denotes` a stable canonical
quantity token, injected into the audit like `allowedStatusFacts`. This is how cross-module joins reach a
common name — physlib's `derives` subjects are verbose per-claim strings that never string-match. Entries
alias each verbose derivation to a canonical token (`newton-G`, `fine-structure-alpha`,
`cosmological-constant-lambda`, `weinberg-angle-sin-squared`); a quantity derived under several
descriptions (α has two) gets one entry per form, all pointing to the same canonical name. Extend this
table (not the physics modules, which cannot emit constant→constant edges) as more quantities need the
derived-vs-input guard. -/
def canonicalAliases : List Atom :=
  [{ object := .symbol "constant:newton-coupling-is-hbar-c-times-inference-position-variance-to-the-fourth",
     relation := "denotes", subject := .symbol "constant:newton-G" },
   { object := .symbol "constant:fine-structure-is-charge-mass-entanglement-nats-over-holographic-screen-bits",
     relation := "denotes", subject := .symbol "constant:fine-structure-alpha" },
   { object := .symbol "constant:fine-structure-is-electromagnetic-to-gravitational-force-ratio-at-planck-mass",
     relation := "denotes", subject := .symbol "constant:fine-structure-alpha" },
   { object := .symbol "constant:cosmological-constant-is-twelve-pi-c-cubed-over-hbar-g-n",
     relation := "denotes", subject := .symbol "constant:cosmological-constant-lambda" },
   { object := .symbol "constant:weinberg-angle-sin-squared-equals-three-eighths",
     relation := "denotes", subject := .symbol "constant:weinberg-angle-sin-squared" }]

/-- A canonical-alias sample on the **real** tokens: `Dg` derives the verbose G description physlib
actually uses, `canonicalAliases` maps it to canonical `constant:newton-G`, and `Dbad` `assumes_primitive`
`constant:newton-G`. The names differ, so the direct rule misses it; the canonical rule must flag `Dbad` —
the guard on the exact quantity that was mis-stated. -/
def canonicalPrimitiveSample : Program :=
  { facts := canonicalAliases ++
      [{ object := .symbol "Dg", relation := "derives",
         subject := .symbol "constant:newton-coupling-is-hbar-c-times-inference-position-variance-to-the-fourth" },
       { object := .symbol "Dbad", relation := "assumes_primitive", subject := .symbol "constant:newton-G" }]
    rules := [canonicalDerivedByRule, assumedPrimitiveButCanonicallyDerivedRule] }

/-- The atom flagging `d`'s canonical primitive-claim on `k` as contradicted by an aliased derivation. -/
def assumedPrimitiveButCanonicallyDerivedAtom (d k : String) : Atom :=
  { object := .symbol d, relation := "assumedPrimitiveButCanonicallyDerived", subject := .symbol k }

/-- **The canonical rule fires across differing names.** `Dbad` assumes the canonical `constant:newton-G`
primitive; `Dg` derives the verbose `newton-coupling-is-…` token the alias maps to it — the cross-module
contradiction the exact-string join cannot see. This is precisely the check that now catches a canonical
"G is an input" claim against physlib's verbose-named derivation of `G`. -/
theorem canonicalPrimitive_fires_across_names :
    assumedPrimitiveButCanonicallyDerivedAtom "Dbad" "constant:newton-G"
      ∈ deriveProgram canonicalPrimitiveSample 4 := by
  decide

/-- Validation that the *extended* aliases (α, Λ, sin²θ_W) exactly match physlib's `derives` subjects:
each is derived under its real verbose token, and a canonical primitiveness claim on it must be flagged.
α is tested through its `charge-mass-entanglement` form; its second form and the single forms of Λ and
sin²θ_W follow the same certified pattern. Kept as three focused samples so each `decide` stays small. -/
def canonicalAlphaSample : Program :=
  { facts := canonicalAliases ++
      [{ object := .symbol "Da", relation := "derives",
         subject := .symbol "constant:fine-structure-is-charge-mass-entanglement-nats-over-holographic-screen-bits" },
       { object := .symbol "Ba", relation := "assumes_primitive", subject := .symbol "constant:fine-structure-alpha" }]
    rules := [canonicalDerivedByRule, assumedPrimitiveButCanonicallyDerivedRule] }

def canonicalLambdaSample : Program :=
  { facts := canonicalAliases ++
      [{ object := .symbol "Dl", relation := "derives",
         subject := .symbol "constant:cosmological-constant-is-twelve-pi-c-cubed-over-hbar-g-n" },
       { object := .symbol "Bl", relation := "assumes_primitive", subject := .symbol "constant:cosmological-constant-lambda" }]
    rules := [canonicalDerivedByRule, assumedPrimitiveButCanonicallyDerivedRule] }

def canonicalWeinbergSample : Program :=
  { facts := canonicalAliases ++
      [{ object := .symbol "Dw", relation := "derives",
         subject := .symbol "constant:weinberg-angle-sin-squared-equals-three-eighths" },
       { object := .symbol "Bw", relation := "assumes_primitive", subject := .symbol "constant:weinberg-angle-sin-squared" }]
    rules := [canonicalDerivedByRule, assumedPrimitiveButCanonicallyDerivedRule] }

/-- **The extended guard fires for α.** A canonical `fine-structure-alpha` input-claim is flagged against
the verbose `charge-mass-entanglement` derivation — the α alias entry matches the real token. -/
theorem canonicalPrimitive_fires_on_alpha :
    assumedPrimitiveButCanonicallyDerivedAtom "Ba" "constant:fine-structure-alpha"
      ∈ deriveProgram canonicalAlphaSample 4 := by decide

/-- **The extended guard fires for Λ.** The `cosmological-constant-lambda` alias matches the real token. -/
theorem canonicalPrimitive_fires_on_lambda :
    assumedPrimitiveButCanonicallyDerivedAtom "Bl" "constant:cosmological-constant-lambda"
      ∈ deriveProgram canonicalLambdaSample 4 := by decide

/-- **The extended guard fires for sin²θ_W.** The `weinberg-angle-sin-squared` alias matches the real token. -/
theorem canonicalPrimitive_fires_on_weinberg :
    assumedPrimitiveButCanonicallyDerivedAtom "Bw" "constant:weinberg-angle-sin-squared"
      ∈ deriveProgram canonicalWeinbergSample 4 := by decide

/-- An evidence-scope sample mirroring the M9.109 finding. `Ct` carries an `experimental_bound` (looks
tested) and `requires` premise `P`, which `Dp` formalizes but does **not** test, and `Ct` has no caveat —
so the gap fires. `Cok` is the same but *discloses* it with a `caveat` → exempt. `Ce` requires `Pe`, which
`De` both formalizes and tests → the premise is established → not flagged. -/
def evidenceGapSample : Program :=
  { facts := [{ object := .symbol "Ct", relation := "experimental_bound", subject := .symbol "Bt" },
              { object := .symbol "Ct", relation := "requires", subject := .symbol "P" },
              { object := .symbol "Dp", relation := "formalizes", subject := .symbol "P" },
              { object := .symbol "Cok", relation := "experimental_bound", subject := .symbol "Bk" },
              { object := .symbol "Cok", relation := "requires", subject := .symbol "P" },
              { object := .symbol "Cok", relation := "caveat", subject := .symbol "disclosed" },
              { object := .symbol "Ce", relation := "experimental_bound", subject := .symbol "Be" },
              { object := .symbol "Ce", relation := "requires", subject := .symbol "Pe" },
              { object := .symbol "De", relation := "formalizes", subject := .symbol "Pe" },
              { object := .symbol "De", relation := "experimental_bound", subject := .symbol "Bde" }]
    rules := [hasTestRule, hasCaveatRule, establishedPremiseRule, undisclosedEvidenceGapRule] }

/-- The atom flagging `d`'s premise `c` as an undisclosed evidence-scope gap. -/
def undisclosedEvidenceGapAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "undisclosedEvidenceGap", subject := .symbol c }

/-- **The evidence-scope guard fires on the undisclosed over-reach.** `Ct` looks tested but requires `P`,
which no experimentally-bounded declaration establishes, and discloses no caveat — the M9.109 pattern. -/
theorem evidenceGap_fires_on_undisclosed :
    undisclosedEvidenceGapAtom "Ct" "P" ∈ deriveProgram evidenceGapSample 8 := by decide

/-- **Suppressed when the gap is disclosed.** `Cok` carries a `caveat`, so the over-reach is exempt — the
rule flags only undisclosed gaps. -/
theorem evidenceGap_suppressed_when_caveated :
    undisclosedEvidenceGapAtom "Cok" "P" ∉ deriveProgram evidenceGapSample 8 := by decide

/-- **Suppressed when evidence reaches the premise.** `Pe` is formalized by `De`, which *is* experimentally
bounded, so the premise is established and `Ce` is not flagged: no false positive. -/
theorem evidenceGap_suppressed_when_premise_established :
    undisclosedEvidenceGapAtom "Ce" "Pe" ∉ deriveProgram evidenceGapSample 8 := by decide

/-- A conformance sample showing the bar ADAPTS to the scenario. `Da` (`ansatz-loaded`, no caveat, no
source) is flagged for missing `disclosure`; `Db` (same, but caveated) is not. `Dc`
(`consistency-identity`, also no source) is **not** flagged — its status demands nothing, the adaptive
difference from the blanket `unsupportedRule`. `Dd` (`conditional-model`, no source, no derivation) is
flagged for missing `grounding`; `De` (same, but it `derives`) is not. -/
def conformanceSample : Program :=
  { facts := conformancePolicy ++
      [{ object := .symbol "Da", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Db", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Db", relation := "caveat", subject := .symbol "hedge" },
       { object := .symbol "Dc", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Dd", relation := "epistemic_status", subject := .symbol "conditional-model" },
       { object := .symbol "De", relation := "epistemic_status", subject := .symbol "conditional-model" },
       { object := .symbol "De", relation := "derives", subject := .symbol "someclaim" }]
    rules := [providesDisclosureByCaveatRule, providesDisclosureBySupportRule,
              providesGroundingBySupportRule, providesGroundingByDerivesRule, nonconformantRule] }

/-- The atom flagging `d` nonconformant for requirement `req`. -/
def nonconformantAtom (d req : String) : Atom :=
  { object := .symbol d, relation := "nonconformant", subject := .symbol req }

/-- **Fires on an undisclosed ansatz claim.** `Da` is `ansatz-loaded` with neither `caveat` nor source, so
its demanded `disclosure` is missing. -/
theorem nonconformant_fires_on_undisclosed_ansatz :
    nonconformantAtom "Da" "disclosure" ∈ deriveProgram conformanceSample 4 := by decide

/-- **Suppressed when disclosed.** `Db` carries a `caveat`, providing the demanded `disclosure`. -/
theorem nonconformant_suppressed_when_caveated :
    nonconformantAtom "Db" "disclosure" ∉ deriveProgram conformanceSample 4 := by decide

/-- **The adaptive exemption.** `Dc` is a `consistency-identity` with no source, yet is NOT flagged — its
status demands nothing, unlike the blanket `unsupportedRule` which would flag it. The standard adapts to
the scenario. -/
theorem nonconformant_exempts_consistency_identity :
    nonconformantAtom "Dc" "disclosure" ∉ deriveProgram conformanceSample 4 := by decide

/-- **Fires on an ungrounded conditional-model claim.** `Dd` demands `grounding` but has neither source nor
derivation. -/
theorem nonconformant_fires_on_ungrounded_conditional :
    nonconformantAtom "Dd" "grounding" ∈ deriveProgram conformanceSample 4 := by decide

/-- **Suppressed when grounded by a derivation.** `De` `derives`, providing the demanded `grounding`. -/
theorem nonconformant_suppressed_when_derived :
    nonconformantAtom "De" "grounding" ∉ deriveProgram conformanceSample 4 := by decide

/-- A status-honesty sample. All claims are `consistency-identity`. `Cphys` requires an undischarged
`physicalPostulatePremise` (`phys`) → over-claim. `Cmath` requires an undischarged `mathPrecondition`
(`matc`) → legitimate. `Cdis` requires a physical postulate (`physD`) that `Dp` **formalizes** → discharged,
so not flagged. `Ccond` requires `phys` but is `conditional-model` (not an exact status) → not flagged.
`Cunc` requires an unclassified undischarged premise (`untriaged`) → surfaced for triage. -/
def statusOverclaimSample : Program :=
  { facts :=
      [selfEdge "physicalPostulatePremise" "phys",
       selfEdge "mathPrecondition" "matc",
       selfEdge "physicalPostulatePremise" "physD",
       selfEdge "exactIdentityStatus" "consistency-identity",
       { object := .symbol "Cphys", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cphys", relation := "requires", subject := .symbol "phys" },
       { object := .symbol "Cmath", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cmath", relation := "requires", subject := .symbol "matc" },
       { object := .symbol "Cdis", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cdis", relation := "requires", subject := .symbol "physD" },
       { object := .symbol "Dp", relation := "formalizes", subject := .symbol "physD" },
       { object := .symbol "Ccond", relation := "epistemic_status", subject := .symbol "conditional-model" },
       { object := .symbol "Ccond", relation := "requires", subject := .symbol "phys" },
       { object := .symbol "Cunc", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cunc", relation := "requires", subject := .symbol "untriaged" }]
    rules := [dischargedByFormalizesRule, dischargedByDerivesRule, exactIdentityBarePremiseRule,
              statusOverclaimRule, unclassifiedExactPremiseRule] }

/-- The atom flagging `d`'s exact-identity status as over-claimed via physical premise `c`. -/
def statusOverclaimAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "statusOverclaim", subject := .symbol c }

/-- The atom surfacing `d`'s undischarged exact-identity premise `c` as awaiting classification. -/
def unclassifiedExactPremiseAtom (d c : String) : Atom :=
  { object := .symbol d, relation := "unclassifiedExactPremise", subject := .symbol c }

/-- **The firm gate fires on the genuine over-claim.** `Cphys` is an exact identity resting on an
undischarged physical postulate — the `verlindeTemperature`/equipartition pattern. -/
theorem statusOverclaim_fires_on_physical_postulate :
    statusOverclaimAtom "Cphys" "phys" ∈ deriveProgram statusOverclaimSample 6 := by decide

/-- **Suppressed on a math precondition — the fix for the earlier over-firing.** `Cmath` rests on an
undischarged *mathematical* precondition, which is legitimate structure for an exact identity. -/
theorem statusOverclaim_suppressed_on_math_precondition :
    statusOverclaimAtom "Cmath" "matc" ∉ deriveProgram statusOverclaimSample 6 := by decide

/-- **Suppressed when the premise is discharged.** `physD` is formalized by `Dp`, so it is established
in-program; requiring it is ordinary exact-math structure, not an over-claim. -/
theorem statusOverclaim_suppressed_when_discharged :
    statusOverclaimAtom "Cdis" "physD" ∉ deriveProgram statusOverclaimSample 6 := by decide

/-- **Suppressed on a non-exact status.** `Ccond` rests on the same physical postulate but is honestly
labelled `conditional-model`; only exact-identity statuses are held to this gate. -/
theorem statusOverclaim_suppressed_on_nonexact_status :
    statusOverclaimAtom "Ccond" "phys" ∉ deriveProgram statusOverclaimSample 6 := by decide

/-- **The triage detector fires on an unclassified bare premise.** `untriaged` is an undischarged premise of
an exact identity that `premiseKinds` classifies as neither physical nor mathematical. -/
theorem unclassifiedExactPremise_fires_on_untriaged :
    unclassifiedExactPremiseAtom "Cunc" "untriaged" ∈ deriveProgram statusOverclaimSample 6 := by decide

/-- **Triage is silent on a classified premise.** `phys` is classified, so it needs no triage. -/
theorem unclassifiedExactPremise_suppressed_when_classified :
    unclassifiedExactPremiseAtom "Cphys" "phys" ∉ deriveProgram statusOverclaimSample 6 := by decide

/-- A real-token sample. `Cverlinde` is an exact identity requiring the real screen-equipartition premise,
whose derivation lemma (`verlinde_equipartition_from_NDOF`) `formalizes` it → the premise is DISCHARGED
(structural), hence NOT flagged; `Cpoisson` requires the real satisfies-Poisson mathematical precondition,
classified `mathPrecondition`, also not flagged. Both certify a derived / mathematical premise of an exact
identity is correctly left alone. -/
def statusOverclaimRealSample : Program :=
  { facts := premiseKinds ++ exactIdentityStatusFacts ++
      [{ object := .symbol "Cverlinde", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cverlinde", relation := "requires",
         subject := .symbol "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom" },
       -- the derivation lemma formalizes screen equipartition → the premise is DISCHARGED (structural)
       { object := .symbol "Dequip", relation := "formalizes",
         subject := .symbol "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom" },
       { object := .symbol "Cpoisson", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cpoisson", relation := "requires",
         subject := .symbol "assumption:the-selected-tempered-potential-satisfies-poisson" }]
    rules := [dischargedByFormalizesRule, dischargedByDerivesRule, exactIdentityBarePremiseRule,
              statusOverclaimRule, unclassifiedExactPremiseRule] }

/-- **Silent on the real equipartition premise — it is derived, not postulated.** The derivation lemma
`verlinde_equipartition_from_NDOF` `formalizes` screen equipartition, so the premise is discharged and the
exact identity resting on it is not flagged. -/
theorem statusOverclaim_suppressed_on_real_equipartition_derived :
    statusOverclaimAtom "Cverlinde" "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom"
      ∉ deriveProgram statusOverclaimRealSample 6 := by decide

/-- **Silent on the real satisfies-Poisson precondition.** Classified `mathPrecondition`, so an exact
identity requiring it is legitimate and not flagged. -/
theorem statusOverclaim_suppressed_on_real_math_precondition :
    statusOverclaimAtom "Cpoisson" "assumption:the-selected-tempered-potential-satisfies-poisson"
      ∉ deriveProgram statusOverclaimRealSample 6 := by decide

/-- A cross-name premise-alias sample. `assumption:X` `premiseDenotes` the derived token `claim:Y`, which
`Dderiv` `formalizes`. `Dreq` requires `assumption:X` → flagged + `assumption:X` discharged; `Dgen` requires
`assumption:P`, a genuine postulate with no alias → not flagged; `Cid` is a `consistency-identity` requiring
`assumption:X`, which the alias discharges → the gate's triage does not surface it. -/
def premiseAliasSample : Program :=
  { facts :=
      [selfEdge "exactIdentityStatus" "consistency-identity",
       { object := .symbol "assumption:X", relation := "premiseDenotes", subject := .symbol "claim:Y" },
       { object := .symbol "Dderiv", relation := "formalizes", subject := .symbol "claim:Y" },
       { object := .symbol "Dreq", relation := "requires", subject := .symbol "assumption:X" },
       { object := .symbol "Dgen", relation := "requires", subject := .symbol "assumption:P" },
       { object := .symbol "Cid", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cid", relation := "requires", subject := .symbol "assumption:X" }]
    rules := [dischargedByFormalizesRule, dischargedByDerivesRule, aliasDischargedPremiseRule,
              premiseAssumedButDerivedRule, exactIdentityBarePremiseRule, unclassifiedExactPremiseRule] }

/-- The atom flagging `d`'s `assumption:` premise `k` as derived under another token. -/
def premiseAssumedButDerivedAtom (d k : String) : Atom :=
  { object := .symbol d, relation := "premiseAssumedButDerived", subject := .symbol k }

/-- **Fires across names.** `Dreq` requires `assumption:X`; its alias `claim:Y` is formalized by `Dderiv`, so
the mislabel is flagged even though the two token strings differ. -/
theorem premiseAssumedButDerived_fires_across_names :
    premiseAssumedButDerivedAtom "Dreq" "assumption:X" ∈ deriveProgram premiseAliasSample 6 := by decide

/-- **Suppressed on a genuine postulate.** `Dgen` requires `assumption:P`, which has no `premiseDenotes`
alias (no in-repo derivation), so it is not flagged — the table is the curated allow/deny boundary. -/
theorem premiseAssumedButDerived_suppressed_on_genuine_postulate :
    premiseAssumedButDerivedAtom "Dgen" "assumption:P" ∉ deriveProgram premiseAliasSample 6 := by decide

/-- **The honesty-gate win — no false flag, no rename.** `Cid` is a `consistency-identity` requiring
`assumption:X`; the alias discharges `assumption:X` (via the formalized `claim:Y`), so it is no longer a bare
premise and the gate's triage does not surface it. Without the alias it would appear as
`unclassifiedExactPremise` — this is the general form of the equipartition fix with no token rename. -/
theorem unclassifiedExactPremise_suppressed_on_cross_named_derived :
    unclassifiedExactPremiseAtom "Cid" "assumption:X" ∉ deriveProgram premiseAliasSample 6 := by decide

/-- A weakest-link sample (depth-1). `Cbad` (consistency-identity) requires `Pw`, formalized by the
ansatz-loaded `Ew` → buried conditionality. `Cok` requires `Ps`, formalized by the consistency-identity `Es`
→ not flagged (exact rests on exact). `Calias` requires `assumption:X`, which `premiseDenotes` `claim:Y`
formalized by the ansatz-loaded `Ealias` → flagged through the cross-name bridge.  `Cdisc` has `Cbad`'s
shape but `discloses` its weak dependency → exempt. -/
def weakestLinkSample : Program :=
  { facts := statusStrictlyStronger ++
      [{ object := .symbol "Cbad", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cbad", relation := "requires", subject := .symbol "Pw" },
       { object := .symbol "Ew", relation := "formalizes", subject := .symbol "Pw" },
       { object := .symbol "Ew", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Cok", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cok", relation := "requires", subject := .symbol "Ps" },
       { object := .symbol "Es", relation := "formalizes", subject := .symbol "Ps" },
       { object := .symbol "Es", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Calias", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Calias", relation := "requires", subject := .symbol "assumption:X" },
       { object := .symbol "assumption:X", relation := "premiseDenotes", subject := .symbol "claim:Y" },
       { object := .symbol "Ealias", relation := "formalizes", subject := .symbol "claim:Y" },
       { object := .symbol "Ealias", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Csup", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Csup", relation := "supported_by", subject := .symbol "lean:Ewk" },
       { object := .symbol "lean:Ewk", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Cprim", relation := "requires", subject := .symbol "assumption:bare" },
       { object := .symbol "Cdisc", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cdisc", relation := "requires", subject := .symbol "Pw" },
       { object := .symbol "Cdisc", relation := "discloses", subject := .symbol "Ew" }]
    rules := weakestLinkRules }

/-- The atom flagging `d` as buried-resting on the weaker-status declaration `e`. -/
def buriedConditionalityAtom (d e : String) : Atom :=
  { object := .symbol d, relation := "buriedConditionality", subject := .symbol e }

/-- **Fires on a direct weak dependency.** `Cbad` is an exact identity that requires a premise established
by the ansatz-loaded `Ew`. -/
theorem buriedConditionality_fires_direct :
    buriedConditionalityAtom "Cbad" "Ew" ∈ deriveProgram weakestLinkSample 6 := by decide

/-- **Suppressed when exact rests on exact.** `Cok` requires a premise established by the consistency-identity
`Es`; no status is strictly stronger than itself, so it is not flagged. -/
theorem buriedConditionality_suppressed_exact_on_exact :
    buriedConditionalityAtom "Cok" "Es" ∉ deriveProgram weakestLinkSample 6 := by decide

/-- **Fires across names.** `Calias`'s `assumption:X` premise is established by the ansatz-loaded `Ealias`
under the aliased `claim:Y` — the equipartition-style cross-name link, caught via `premiseDenotes`. -/
theorem buriedConditionality_fires_cross_name :
    buriedConditionalityAtom "Calias" "Ealias" ∈ deriveProgram weakestLinkSample 6 := by decide

/-- **Suppressed by disclosure.** `Cdisc` has exactly `Cbad`'s shape — an exact identity resting on the
ansatz-loaded `Ew` — but carries a `discloses` edge naming `Ew`: acknowledged conditionality is not
buried, and the detector stays quiet while `Cbad` still fires. -/
theorem buriedConditionality_suppressed_on_disclosed :
    buriedConditionalityAtom "Cdisc" "Ew" ∉ deriveProgram weakestLinkSample 6 := by decide

/-- A transitive sample. `Ctop` (consistency-identity) requires `Pm`, established by the *exact* `Emid`,
which itself requires `Pw2` established by the ansatz-loaded `Ew2`. The weakness is two levels deep. -/
def weakestLinkTransSample : Program :=
  { facts := statusStrictlyStronger ++
      [{ object := .symbol "Ctop", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Ctop", relation := "requires", subject := .symbol "Pm" },
       { object := .symbol "Emid", relation := "formalizes", subject := .symbol "Pm" },
       { object := .symbol "Emid", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Emid", relation := "requires", subject := .symbol "Pw2" },
       { object := .symbol "Ew2", relation := "formalizes", subject := .symbol "Pw2" },
       { object := .symbol "Ew2", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Cts", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "Cts", relation := "supported_by", subject := .symbol "lean:Fm" },
       { object := .symbol "lean:Fm", relation := "epistemic_status", subject := .symbol "consistency-identity" },
       { object := .symbol "lean:Fm", relation := "supported_by", subject := .symbol "lean:Ews" },
       { object := .symbol "lean:Ews", relation := "epistemic_status", subject := .symbol "ansatz-loaded" },
       { object := .symbol "Ew2", relation := "requires", subject := .symbol "assumption:deep-bare" }]
    rules := weakestLinkRules }

/-- **Fires transitively — the payoff.** `Ctop` reaches the ansatz-loaded `Ew2` only at depth 2, through an
exact intermediate. A depth-1 check misses it; the declaration-dependency closure catches it. -/
theorem buriedConditionality_fires_transitively :
    buriedConditionalityAtom "Ctop" "Ew2" ∈ deriveProgram weakestLinkTransSample 6 := by decide

/-- **The exact intermediate is not itself flagged.** `Ctop`'s *direct* dependency `Emid` is a
consistency-identity, so depth-1 sees nothing — which is exactly why the transitive closure is needed. -/
theorem buriedConditionality_suppressed_on_exact_intermediate :
    buriedConditionalityAtom "Ctop" "Emid" ∉ deriveProgram weakestLinkTransSample 6 := by decide

/-- **Fires through a `supported_by` reference — the high-recall source.** `Csup` (consistency-identity) is
directly `supported_by` the ansatz-loaded `lean:Ewk`; no premise-token matching is needed. -/
theorem buriedConditionality_fires_via_support :
    buriedConditionalityAtom "Csup" "lean:Ewk" ∈ deriveProgram weakestLinkSample 6 := by decide

/-- **Fires transitively through `supported_by`.** `Cts` is supported by the exact `lean:Fm`, which is in
turn supported by the ansatz-loaded `lean:Ews` — buried two levels down the support chain. -/
theorem buriedConditionality_fires_via_support_transitively :
    buriedConditionalityAtom "Cts" "lean:Ews" ∈ deriveProgram weakestLinkTransSample 6 := by decide

/-- The atom recording that `d` transitively rests on the primitive (unestablished) premise `p`. -/
def transitivePrimitivePremiseAtom (d p : String) : Atom :=
  { object := .symbol d, relation := "transitivePrimitivePremise", subject := .symbol p }

/-- **Fires on a direct bare premise.** `Cprim` requires `assumption:bare`, which nothing establishes — a
primitive input of the grounding tree. -/
theorem transitivePrimitivePremise_fires_direct :
    transitivePrimitivePremiseAtom "Cprim" "assumption:bare" ∈ deriveProgram weakestLinkSample 6 := by decide

/-- **Excludes an established premise.** `Cbad` requires `Pw`, but `Ew` `formalizes` `Pw`, so `Pw` is
established, not primitive, and is not listed. -/
theorem transitivePrimitivePremise_excludes_established :
    transitivePrimitivePremiseAtom "Cbad" "Pw" ∉ deriveProgram weakestLinkSample 6 := by decide

/-- **Fires transitively.** `Ctop` reaches `Ew2` down the dependency chain, and `Ew2` requires the bare
`assumption:deep-bare` — a primitive input of `Ctop` two levels deep. -/
theorem transitivePrimitivePremise_fires_transitively :
    transitivePrimitivePremiseAtom "Ctop" "assumption:deep-bare"
      ∈ deriveProgram weakestLinkTransSample 6 := by decide

end

-- Build-time gate: the improvement suite must be stratifiable (no relation depends negatively on
-- itself, directly or transitively), or the build fails — the executable honesty bar for the rules.
run_cmd do
  let rules := Physlib.Meta.ZilGraph.improvementRules ++ Physlib.Meta.ZilGraph.dependencyRules
    ++ Physlib.Meta.ZilGraph.weakestLinkRules
  let prog : Program := { facts := [], rules := rules }
  if prog.isStratified then
    logInfo "zil-graph: all rules are stratifiable (safe negation)"
  else
    throwError "zil-graph: rules are NOT stratifiable — negation gate failed"

end Physlib.Meta.ZilGraph

/-! ### Honesty bars on the verified gap-detector soundness theorems -/

#physlib_axiom_clean_all [Physlib.Meta.ZilGraph.untested_fires_on_untested,
  Physlib.Meta.ZilGraph.untested_suppressed_when_tested,
  Physlib.Meta.ZilGraph.invalidStatus_fires_on_unknown,
  Physlib.Meta.ZilGraph.invalidStatus_suppressed_on_allowed,
  Physlib.Meta.ZilGraph.depends_transitively,
  Physlib.Meta.ZilGraph.cycle_is_detected,
  Physlib.Meta.ZilGraph.wellDocumented_accepts_complete,
  Physlib.Meta.ZilGraph.wellDocumented_rejects_incomplete,
  Physlib.Meta.ZilGraph.assumedPrimitive_fires_on_derived,
  Physlib.Meta.ZilGraph.assumedPrimitive_suppressed_on_genuine,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_across_names,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_alpha,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_lambda,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_weinberg,
  Physlib.Meta.ZilGraph.evidenceGap_fires_on_undisclosed,
  Physlib.Meta.ZilGraph.evidenceGap_suppressed_when_caveated,
  Physlib.Meta.ZilGraph.evidenceGap_suppressed_when_premise_established,
  Physlib.Meta.ZilGraph.nonconformant_fires_on_undisclosed_ansatz,
  Physlib.Meta.ZilGraph.nonconformant_suppressed_when_caveated,
  Physlib.Meta.ZilGraph.nonconformant_exempts_consistency_identity,
  Physlib.Meta.ZilGraph.nonconformant_fires_on_ungrounded_conditional,
  Physlib.Meta.ZilGraph.nonconformant_suppressed_when_derived,
  Physlib.Meta.ZilGraph.statusOverclaim_fires_on_physical_postulate,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_math_precondition,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_when_discharged,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_nonexact_status,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_fires_on_untriaged,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_suppressed_when_classified,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_real_equipartition_derived,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_real_math_precondition,
  Physlib.Meta.ZilGraph.premiseAssumedButDerived_fires_across_names,
  Physlib.Meta.ZilGraph.premiseAssumedButDerived_suppressed_on_genuine_postulate,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_suppressed_on_cross_named_derived,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_direct,
  Physlib.Meta.ZilGraph.buriedConditionality_suppressed_exact_on_exact,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_cross_name,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_transitively,
  Physlib.Meta.ZilGraph.buriedConditionality_suppressed_on_exact_intermediate,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_via_support,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_via_support_transitively,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_fires_direct,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_excludes_established,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_fires_transitively]
#physlib_non_vacuous_all [Physlib.Meta.ZilGraph.untested_fires_on_untested,
  Physlib.Meta.ZilGraph.untested_suppressed_when_tested,
  Physlib.Meta.ZilGraph.invalidStatus_fires_on_unknown,
  Physlib.Meta.ZilGraph.invalidStatus_suppressed_on_allowed,
  Physlib.Meta.ZilGraph.depends_transitively,
  Physlib.Meta.ZilGraph.cycle_is_detected,
  Physlib.Meta.ZilGraph.wellDocumented_accepts_complete,
  Physlib.Meta.ZilGraph.wellDocumented_rejects_incomplete,
  Physlib.Meta.ZilGraph.assumedPrimitive_fires_on_derived,
  Physlib.Meta.ZilGraph.assumedPrimitive_suppressed_on_genuine,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_across_names,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_alpha,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_lambda,
  Physlib.Meta.ZilGraph.canonicalPrimitive_fires_on_weinberg,
  Physlib.Meta.ZilGraph.evidenceGap_fires_on_undisclosed,
  Physlib.Meta.ZilGraph.evidenceGap_suppressed_when_caveated,
  Physlib.Meta.ZilGraph.evidenceGap_suppressed_when_premise_established,
  Physlib.Meta.ZilGraph.nonconformant_fires_on_undisclosed_ansatz,
  Physlib.Meta.ZilGraph.nonconformant_suppressed_when_caveated,
  Physlib.Meta.ZilGraph.nonconformant_exempts_consistency_identity,
  Physlib.Meta.ZilGraph.nonconformant_fires_on_ungrounded_conditional,
  Physlib.Meta.ZilGraph.nonconformant_suppressed_when_derived,
  Physlib.Meta.ZilGraph.statusOverclaim_fires_on_physical_postulate,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_math_precondition,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_when_discharged,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_nonexact_status,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_fires_on_untriaged,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_suppressed_when_classified,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_real_equipartition_derived,
  Physlib.Meta.ZilGraph.statusOverclaim_suppressed_on_real_math_precondition,
  Physlib.Meta.ZilGraph.premiseAssumedButDerived_fires_across_names,
  Physlib.Meta.ZilGraph.premiseAssumedButDerived_suppressed_on_genuine_postulate,
  Physlib.Meta.ZilGraph.unclassifiedExactPremise_suppressed_on_cross_named_derived,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_direct,
  Physlib.Meta.ZilGraph.buriedConditionality_suppressed_exact_on_exact,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_cross_name,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_transitively,
  Physlib.Meta.ZilGraph.buriedConditionality_suppressed_on_exact_intermediate,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_via_support,
  Physlib.Meta.ZilGraph.buriedConditionality_fires_via_support_transitively,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_fires_direct,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_excludes_established,
  Physlib.Meta.ZilGraph.transitivePrimitivePremise_fires_transitively]
