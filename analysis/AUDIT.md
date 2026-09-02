# Formal-program audit infrastructure

A self-inspection layer for the physlib formal program. It reads physlib's own
`zil attach` knowledge graph (theorems linked by `formalizes` / `supported_by` /
`caveat` / `requires` / `epistemic_status` / `derives` / `experimental_bound` / …
edges) and the native `@[zil_level]` theorem-intents, and reports on the
program's rigor, coverage, honesty, and dependency structure.

Everything here measures **formal-graph hygiene and structure** — what the
program claims and how well those claims are supported and disclosed — **not**
whether the physics is correct.

All modules are gated by `#physlib_axiom_clean_all` + `#physlib_non_vacuous_all`,
use only the standard axioms, and add no dependency beyond the ZIL Datalog
engine (`Zil.Datalog`, which physlib already builds against).

## Modules (`Physlib/Meta/`)

| Module | What it does |
| --- | --- |
| `ZilGraph.lean` | Gap detectors over the graph — untested / unclassified / unstatused predictions, unsupported claims, out-of-vocabulary `epistemic_status`, `dependsOn` transitive closure + cycle detection, the positive `wellDocumentedPrediction`, and the `assumedPrimitiveButDerived` **consistency** check (a quantity declared a fundamental input via `assumes_primitive` while the graph `derives` it) with its canonical-alias companion (`canonicalAliases` `denotes` table + `assumedPrimitiveButCanonicallyDerived`) so the check joins across physlib's verbose per-claim constant names, and the `undisclosedEvidenceGap` check (an experimentally-anchored claim whose required premise no evidence reaches, disclosed by no `caveat` — mechanizing the OpenWave M9.109 finding that the anchor claims carry `experimental_bound` edges yet their load-bearing premise `ΔS_I = mc²Δτ` is untested), and a **scenario-adaptive conformance** mechanism (`nonconformant` + `provides.*`) whose required standard is a *function of each claim's `epistemic_status`* read from the editable `conformancePolicy` table — so an exact `consistency-identity` is held to no external bar while an `ansatz-loaded` claim must disclose and a `conditional-model` must ground, all re-tunable by a policy row rather than a new rule. Plus a **firm status-honesty gate** (`statusOverclaim` + `unclassifiedExactPremise`): an exact `consistency-identity` claim that `requires` an *undischarged physical postulate* is an over-claim (its honest status is `conditional-model`). A **dynamical** `dischargedPremise` reading (the premise is `formalizes`d/`derives`d in-program) removes the bulk — a required lemma / attainment / positivity / satisfied-PDE hypothesis is legitimate structure — leaving only the undischarged premises, whose irreducibly-semantic physical-vs-mathematical kind is the small `premiseKinds` datum; `unclassifiedExactPremise` surfaces any bare premise not yet classified so the datum stays auditable. This is the split the earlier flat `consistency-identity ∧ requires` rule lacked (it over-fired on 9 candidates, mostly math preconditions). On the current graph the gate finds **zero** genuine over-claims: the one physical-looking candidate, `equipartition-on-the-screen` (required by `verlindeTemperature_at_horizon_is_hawking`), is itself a *derived* theorem (`verlinde_equipartition_from_NDOF`, from the classical equipartition theorem — Verlinde 2011's postulate upgraded to a theorem), so it is **discharged structurally**: its derivation carries a `formalizes` edge (recorded in `DerivedPredictions`) and the dependency was renamed from `assumption:equipartition-on-the-screen` to a derived `claim:` token. The gate is a standing guard whose fire/suppress logic is `decide`-certified. Plus a **weakest-link auditor** (`buriedConditionality`, run separately like the cycle check): it builds the declaration-dependency DAG `dependsOnDecl(D,E)` from three sources — `D` `requires` a premise `E` `formalizes`/`derives`; a cross-named one via `premiseAliases`; and (highest recall) `D` directly `supported_by @ "lean:E"`, a declaration reference that needs no premise-token matching — then flags a `consistency-identity` claim that *transitively* rests on a weaker-status (ansatz/conditional/risky) declaration. It is the depth-generalization of ProgramHealth's depth-1 hidden-debt, and the automated form of the Comparator's "what it does not prove yet". The strength order is the editable `statusStrictlyStronger` datum; the report run is depth-bounded. Real-graph finding: **0** (2026-08-30) — the 21 full-root findings were triaged case by case in `analysis/buried-conditionality-triage.md` (13 proof-level dependencies, 28 citation artifacts across 41 pairs) and every pair is now an explicit `discloses` edge; the rule exempts disclosed pairs by stratified negation (`decide`-certified fire/suppress), so the detector again reports only *undisclosed* debt. The one flagged case — `newtonTemperedPotential3_laplacian` (`consistency-identity`) `supported_by` `temperedFundamentalSolution_convolution` — was traced to a **mislabel**: the convolution theorem is a `rw; rfl` *exact* distributional identity whose fundamental-solution hypothesis `Δ T = c·δ` is *mathematical* (its own caveat already stated the premise is discharged for the Newton kernel), so its `ansatz-loaded` status was wrong. Relabeling it `consistency-identity` and classifying the hypothesis a `mathPrecondition` cleared the finding honestly — the audit improving the program's epistemic self-representation, not just reporting on it. The same closure powers an **assumption ledger** (`transitivePrimitivePremise`, op3.md's PR-4 assumption engine): the transitive bare-postulate footprint each claim rests on — a premise no declaration `establishes`. Default scope: 83 distinct primitive premises over 728 declaration-dependencies (2026-08-27; was 54 over 527), emitted as a diffable `[assumption-ledger:metrics]` JSON line so "does new work reduce assumptions or add interfaces?" is measurable. Ranked by **exact-claim reach** (`[assumption-ledger:foundational-risk]` — of the dependents, how many are `consistency-identity`), because raw reach ≠ risk: `doubled-boost-mode` has the widest reach (12) but **zero** exact dependents — its claims are all honestly conditional, so it is low honesty risk despite the reach. The postulates that underwrite exact claims are mostly **math preconditions** (virial identity, satisfies-Poisson, attainment, natural-units — legitimate for an exact claim, the physical-vs-math distinction the honesty gate draws) plus one physical assumption (`…complex-tempered-kernel-is-a-fundamental-solution`, exact=1); `max_exact_reach = 2`. So no bare *physical* postulate underwrites exact claims at scale — a strong honesty result the raw blast-radius hid. Honest bound: the footprint is an *upper* bound — a few `claim:` "primitives" are actually established under a differently-worded token (the `establishes` recall limit), so the genuine bare postulates are the `assumption:`/`model:`-prefixed ones. Rules run through `Physlib.Meta.ZilDatalogFast.deriveProgramFast`, an indexed saturating evaluator **proved equal** to the reference `Zil.Datalog.deriveProgram` for every program and fuel budget — same atoms, same order, no side conditions (`deriveProgramFast_eq` in `Physlib.Meta.ZilDatalogFastEquiv`; the `#guard`s in `Physlib.Meta.ZilDatalogFastCheck` remain as compiled-code smoke tests); the reference engine no longer finishes at repo scale. Each rule's soundness is verified by `decide` on a sample. In the default build. |
| `ClaimMaturity.lean` | Six-axis maturity (`formal / numerical / stateExistence / physicalId / calibration / prediction`) with a **derived** level, coherence (a dependent axis can't outrun its prerequisite), an honest asserted-vs-derived guard, differentiated classification, and an evidence-backed `Claim` (a validated `formal` axis must name a witnessing theorem). 19 gated theorems. In the default build. |
| `TheoremIntentAudit.lean` | Cross-references the native `@[zil_level]` intents (`Zil.Datalog.theoremIntents`) against the graph — theorems declaring an abstraction level but lacking a `formalizes`/`supported_by` anchor. Leaf, on demand. |
| `EvidenceIntegrity.lean` | Falsification/supersession consistency (`assertsFalsified`, `danglingFalsified`), a structured `Gate` with a proved pass/fail composition, and evidence-class (`internallySupportedOnly`). Machinery for edges authored over time. In the default build. |
| `ProgramHealth.lean` | The synthesis. Six sections that **cross** the audits (where the value is): rigor tiers, rigor-weighted gaps, foundational spine + risk, cross-consistency, solid core, and hidden epistemic debt — plus a one-line diffable metrics JSON. Leaf, on demand. |

## Structured claims the audit can check (a rule can only refute what the graph can see)

The reasoner operates on graph *edges*, not on `caveat`/docstring **prose**. A claim written only in
prose is invisible to it. The concrete lesson (2026-07): a module's caveat called Newton's `G` a
*fundamental input* while `Meta.DerivedPredictions` derives it (`constant:newton-coupling-…`); every
`decide`-verified rule passed because the contradiction lived in free text, never as an edge.

**Convention.** State claims that a rule could refute as *edges*, not prose. In particular:

- **"X is a fundamental / underived input"** → `assumes_primitive @ "constant:X"` (never a caveat
  sentence). The `assumedPrimitiveButDerived` rule then refutes it against the `derives` edges the same
  program carries. If a quantity is derived somewhere, do not call it an input anywhere.
- **Cross-module joins need a canonical name.** `derives`/`formalizes` subjects are verbose per-claim
  strings that never string-match across modules, so a same-token join fires only within one naming
  convention. To make a quantity cross-checkable, alias its verbose token to a canonical one in
  `ZilGraph.canonicalAliases` (e.g. `constant:newton-G`) and state `assumes_primitive` with that canonical
  token; the `assumedPrimitiveButCanonicallyDerived` rule joins them. G is seeded — extend the table (not
  the physics modules, which cannot emit constant→constant edges) as more quantities need the guard.
- Reserve `caveat` for genuinely unstructured hedges (engineering conditionality, scope of validity) —
  not for assertions about primitiveness, support, or testedness that a relation already encodes.
- **Prefer a policy row over a new rule.** When a check is "claims of status X must provide Y", add a
  `conformancePolicy` row (`status —demands→ requirement`) and, if new, one `provides.*` rule — do not
  hard-code another blanket gap rule that holds every claim to the same bar. The standard should adapt to
  the claim's scenario (its `epistemic_status`), so exact identities are never false-flagged.
- **An exact identity must not rest on a bare physical postulate.** State a physical dependency as a
  `requires @ "assumption:X"` edge. The firm honesty gate flags a `consistency-identity` claim that
  `requires` an *undischarged* premise classified a `physicalPostulatePremise` — its honest status is
  `conditional-model` (remedy: relabel, or discharge the postulate with a proof). The **discharge** reading
  (`formalizes`/`derives`) exempts anything the program proves, so a required lemma / attainment /
  positivity / satisfied-PDE hypothesis never false-fires. Only the physical-vs-mathematical kind that graph
  shape cannot decide is data: classify each undischarged premise once in `ZilGraph.premiseKinds`, and
  `unclassifiedExactPremise` surfaces any new bare premise still needing that one-line datum. Judge by
  whether the premise is *derivable*, not by its token prefix — screen equipartition, once labelled
  `assumption:equipartition-on-the-screen`, is a derived theorem (`verlinde_equipartition_from_NDOF`). Its
  derivation now carries a `formalizes` edge and the dependency is renamed to a derived `claim:` token, so
  the discharge filter catches it structurally (no `premiseKinds` entry needed) — the preferred fix over a
  datum classification.
- **A cross-named derived premise gets a `premiseDenotes` alias, not a token rename.** When a premise
  `requires @ "assumption:X"` is actually derived under a *different* token (the equipartition pattern
  generalized), add a row to `ZilGraph.premiseAliases` mapping `assumption:X` → the derived
  `claim:`/`constant:` token. `aliasDischargedPremiseRule` then discharges it structurally (so the honesty
  gate never false-fires, without editing any physics module) and `premiseAssumedButDerivedRule` surfaces it
  as `[premise-hygiene]`. This is the `requires` analog of the constant guard
  `assumedPrimitiveButCanonicallyDerived`. Genuine postulates (displacement-entropy, holographic-bit-count,
  imported ansätze such as Caticha–Cafaro or Bisognano–Wichmann) get no row — the table is the allow/deny
  boundary. Seeded with Λ=κS, ω_c=mc²/ℏ, G=ℏcσ₀⁴.

## Scripts (`scripts/`)

| Script | Output |
| --- | --- |
| `zil-graph-report.sh` | `analysis/zil-graph-report.md` — the full repo-wide gap audit. |
| `physlib-program-health.sh` | `analysis/program-health.md` — the synthesis dashboard. |
| `physlib-health-ratchet.sh` | CI regression guard: fails if `undisclosed`, `out_of_vocab`, or `untested_numerical` grow above `analysis/health-baseline.json`. |

## Running it

```bash
# The dashboard (whole-library; a few minutes):
./scripts/physlib-program-health.sh      # writes analysis/program-health.md

# CI regression guard:
./scripts/physlib-health-ratchet.sh      # nonzero exit on a hygiene regression

# The in-default-build gates run automatically:
lake build                               # ZilGraph / ClaimMaturity / EvidenceIntegrity gates
```

To move the ratchet baseline after a deliberate, reviewed change:

```bash
lake build Physlib.Meta.ProgramHealth 2>&1 \
  | grep -oE '\{"edges":.*"hidden_debt":[0-9]+\}' | head -1 > analysis/health-baseline.json
```

## Current state (baseline)

```json
{"edges":4528, "exact_identities":218, "untested_numerical":0, "loaded_uncited":12,
 "undisclosed":0, "out_of_vocab":0, "physics_internal_only":2, "hidden_debt":43}
```

Reading: the exact-mathematics backbone (218 identities) is large and every
falsifiable numerical prediction is experimentally anchored (`untested_numerical`
= 0); no risky claim is undisclosed and no status is out of vocabulary (both
ratchet-guarded at 0). The open work is genuine but needs physics/citation
input: cite the remaining 12 uncited loaded claims (15 already cited from
source), externally ground the 2 physical identity claims, review which of the
43 hidden-debt claims truly inherit their dependency's caveat, and firm up the
load-bearing assumptions.
