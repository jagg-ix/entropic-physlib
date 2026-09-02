# Modules outside the build gates — coverage and CAT/EPT criticality

Generated 2026-08-11 against branch `entropic-physlib-linear-full`.
Regenerate the underlying numbers with the reachability computation described in §5.

## 1. What "uncovered" means here

`lake build` builds the transitive import closure of `Physlib.lean`. A module outside that
closure is **never compiled by CI**, so it can carry syntax errors, broken proofs, tripped
honesty gates, or stale claims indefinitely without anything going red. This is not
hypothetical: it is how two modules shipped broken to the shared remote on 2026-08-03 and sat
there for over a week, and how `Physlib.Meta.SpineAxiomAudit` came to be failing its own
non-vacuity gate unnoticed.

Two numbers are easy to confuse, so both are given:

| measure | count | meaning |
|---|---|---|
| files under `Physlib/` | 2382 | every `.lean` module |
| listed in `Physlib.lean` | 1930 | the root manifest |
| **reachable from the root** | **2261** | what `lake build` compiles (2148 at the start of this work) |
| additionally reachable via `Physlib.Meta.FullRootGate` | 115 | the gate leaves, incl. 98 Meta audits wired in at step 4 |
| **covered once the gate runs in CI** | **2376** | after this session's `build.yml` change |
| **still uncovered** | **6** | at the structural floor — see below |

`check_file_imports` reports 445 "missing" modules, but that check demands *direct listing* in
the manifest, and 211 of those are pulled in transitively by a listed module. **445 is not the
coverage gap; 217 is.** Do not use the `check_file_imports` number to size this work.

Wiring `FullRootGate` into `build.yml` (this session) rescues **505 claims across 17 modules** —
including `Meta.EntropicSpineZil` alone at 359. That was the single highest-leverage fix and it
is done. What follows is what remains.

## 2. What is still uncovered

**Six modules, and coverage is now at its structural maximum.** All six `import Physlib`, so none
can enter the manifest without an import cycle:

`Meta.ProgramHealth` · `Meta.TheoremIntentAudit` · `Meta.ZilDefinitionalOverclaimReport` ·
`Meta.ZilDiscoveryReport` · `Meta.ZilGraphAuditFull` · `Meta.ZilTypedRefReport`

Each is an O(n²) repo-wide report that would make a per-push merge gate unusable —
`TheoremIntentAudit` alone needs `set_option maxHeartbeats 0` and about nine minutes. They are
**on-demand by design, not an oversight**, and `FullRootGate` deliberately excludes them. One
`formalizes` claim and one gate invocation live in this set and are correspondingly unchecked by
CI; run the reports manually to exercise them.

Tiers P1–P4 are all cleared. The table below is kept as the record of what was triaged.

*(Metric note: an earlier revision reported "172 build-time honesty gates". That was the count of
modules carrying at least one gate, on the pre-promotion set — a module count mislabelled as a gate
count. Both quantities are now stated explicitly and on the same set.)*

| tier | modules | claims | intents | criterion |
|---|---|---|---|---|
| ~~**P1 — critical**~~ | **0** | — | — | **cleared** — promoted into the root manifest |
| ~~**P2 — high**~~ | **1** | 1 | — | **cleared** but for `ZilDefinitionalOverclaimReport`, which cannot be imported without a cycle |
| ~~**P3 — medium**~~ | **2** | 0 | — | **cleared** — 98 Meta audits wired into `FullRootGate`; the 2 left are the expensive on-demand reports |
| **P4 — low** | 48 | 0 | — | no claims, no gates — supporting material |

"CAT/EPT core area" means `EntropicTime`, `ComptonClock`, `Lorentz`, `ComplexEinstein`,
`Thermodynamics`, `Optics`, or `QFT.PathIntegral` — the entropic-clock spine and the gravity
sector it feeds.

### Criticality rationale

The ranking is by **what the program asserts through the module**, not by size or subject
appeal. A module with `formalizes` edges makes claims that appear in the ZIL graph and in any
report generated from it, so an uncompiled one contributes claims that **no build has ever
checked**. That is strictly worse than an uncompiled module with no claims, which can only waste
effort. Gates come second: a `#physlib_axiom_clean_all` that never runs is a guarantee the repo
believes it has and does not.

## 3. P1 — critical (11 modules)

Core-area modules making claims nothing verifies. Every one also carries a build-time gate that
never fires.

| module | claims | intents | gates | LOC |
|---|---|---|---|---|
| `Thermodynamics.RelativisticScreenKinematics` | 4 | 4 | 1 | 137 |
| `QM.CA.ComplexEinstein.HolographicElectrograviticResidual` | 3 | 3 | 1 | 151 |
| `QM.CA.Curvature.ReissnerNordstromRadialThermodynamics` | 3 | 4 | 1 | 120 |
| `QM.CA.EntropicTime.EntropicNewtonFiniteAtOrigin` | 3 | 3 | 1 | 123 |
| `QM.CA.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual` | 2 | 2 | 1 | 123 |
| `QM.CA.ComplexEinstein.LiouvilleComplexityElectrograviticResidual` | 2 | 2 | 1 | 115 |
| `QM.CA.ComplexEinstein.MaxwellStressEnergyProperties` | 2 | 2 | 1 | 99 |
| `QM.CA.ComptonClock.StrongPoissonHomogeneousDensity` | 2 | 2 | 1 | 109 |
| `QM.CA.EntropicTime.EntropicNewtonHydrogenBoundState` | 2 | 2 | 1 | 154 |
| `QM.CA.ComplexEinstein.CosmologicalConstantGlobalConstancy` | 1 | 1 | 1 | 72 |
| `QM.CA.ComplexEinstein.ElectrograviticResidualConservation` | 1 | 1 | 1 | 104 |

`RelativisticScreenKinematics` heads the list. It **was** broken — found by explicitly building
the orphan set during this session, and fixed the same day (`field_simp` now normalizes `√x * √x`
to `√x ^ 2`, so `Real.mul_self_sqrt` no longer matched; `Real.sq_sqrt` does). `Thermodynamics.SecondLaw.TimeSymmetricMarkovArrows`
was also broken and is likewise fixed — 6 errors, but only 2 real defects: `have :=` binds the
reserved `this` under an inherited `meta import Zil`, and the other 4 errors were cascade from those
two parse failures; it is P3 by
the claim criterion but corresponds to the Guff–Shastry–Rocco time-symmetric arrow work, so treat
it as P1 in practice.

The `ElectrograviticResidual` cluster (four modules) and the two `EntropicNewton` modules are
directly in the entropic-gravity line. `StrongPoissonHomogeneousDensity` sits in `ComptonClock`,
the arc this session extended.

## 4. P2 — high (57 modules, 150 claims)

Claim-bearing, outside the core areas. Top by claim count:

| module | claims | intents | gates | LOC |
|---|---|---|---|---|
| `CondensedMatter.NobleMetalBranchTransport` | 6 | 0 | 0 | 315 |
| `QM.CA.AdSCFT.ConformalWeylCurvatureLiouville` | 4 | 6 | 1 | 167 |
| `QM.CA.Curvature.AffineProjectionTensorGeometry` | 4 | 5 | 1 | 135 |
| `QM.CA.Curvature.HolographicNewtonFromBlackHoleHorizon` | 4 | 4 | 1 | 127 |
| `QM.CA.Curvature.KerrNewmanHorizonQuantities` | 4 | 4 | 1 | 139 |
| `QM.CA.Curvature.ReissnerNordstromHorizons` | 4 | 5 | 1 | 144 |
| `QM.CA.OperatorAlgebra.GegenbauerAllOrderEigenfunction` | 4 | 6 | 1 | 196 |
| `QM.CA.AdSCFT.GKPWittenConformalCovariance` | 3 | 4 | 1 | 124 |
| `QM.CA.AdSCFT.LiouvilleComplexityHolographicSpine` | 3 | 6 | 1 | 162 |
| `QM.CA.CanonicalTetradGravity.GravitonSelfEnergyLorentzInvariant` | 3 | 3 | 1 | 116 |
| `QM.CA.CanonicalTetradGravity.SourcedTTWaveComptonCoupling` | 3 | 5 | 1 | 142 |
| `QM.CA.Curvature.CovariantDerivativeCurvature` | 3 | 3 | 1 | 122 |
| `QM.CA.Curvature.CovariantDerivativeEndomorphism` | 3 | 4 | 1 | 130 |
| `QM.CA.Curvature.KerrNewmanCosmicCensorship` | 3 | 3 | 1 | 109 |
| `QM.CA.Curvature.KerrNewmanHorizons` | 3 | 4 | 1 | 124 |

Concentrated in `Curvature` (black-hole horizon quantities: Kerr–Newman, Reissner–Nordström) and
`AdSCFT` (Liouville complexity, GKP–Witten). These are the imported-GR and holography layers the
entropic-gravity claims lean on.

## 5. Where the uncovered modules live

| area | uncovered |
|---|---|
| `QM.CA.Lorentz` | 41 |
| `QM.CA.Curvature` | 33 |
| `QM.CA.Particles` | 7 |
| `QM.CA.AdSCFT` | 6 |
| `QM.CA.ComplexEinstein` | 6 |
| `QM.CA.CanonicalTetradGravity` | 5 |
| `QM.CA.OperatorAlgebra` | 3 |
| `QM.CA.EntropicTime` | 2 |
| `CondensedMatter.NobleMetalBranchTransport` | 1 |
| `Meta.AffineProjectionTensorGeometryAudit` | 1 |

Reachability is computed by parsing `import` lines from `Physlib.lean` and from
`Physlib/Meta/FullRootGate.lean`, taking the transitive closure over `Physlib/**/*.lean`, and
subtracting from the file set. It is a static computation and needs no build.

## 6. Recommended order

1. ~~Fix the two broken modules~~ — **done**. `RelativisticScreenKinematics` and
   `TimeSymmetricMarkovArrows` both compile; the full orphan set is green.
2. ~~Add P1 to the root manifest~~ — **done**. 12 modules (the 11 P1, plus
   `TimeSymmetricMarkovArrows`, P3 by the claim criterion but core in practice) are now imported by
   `Physlib.lean`, so their gates run in every default build. Uncovered claims fell 175 → 147.
3. ~~Add P2 in area batches~~ — **done**. Curvature (32 modules / 87 claims), then
   Particles+AdSCFT+CanonicalTetradGravity+OperatorAlgebra (19 / 47), then the remainder (4 / 12).
   Each batch built green before the next.
4. ~~P3~~ — **done**. 98 `Meta.*Audit` leaves went into `FullRootGate`'s import list rather than the
   root, as this document recommended; 215 previously dormant gate invocations now run and pass
   (gate build: exit 0, 679 gate invocations fired).
5. ~~P4~~ — **done**. 45 modules added (3 of the 48 were full-root leaves and were skipped).
   Coverage reached 2376/2382, the structural maximum.

## 8. The one preventive step left, and why it is a governance call

Coverage is fixed, but nothing *stops it reopening*: a new module added outside the root closure
would again go unbuilt. The mechanism already exists — `build.yml` runs `check_file_imports`, which
demands every module be **directly listed** in `Physlib.lean` — but that check cannot pass today
for two reasons, only one of which is about coverage:

1. **378 modules are transitively covered but not directly listed.** They all compile; listing them
   buys no coverage, only the ability to enforce.
2. **The manifest has never been sorted** — 94 out-of-order pairs, pre-existing, independent of any
   work here. `arrayImportSorted` fails on these.

Fixing both means rewriting ~2377 import lines in a file a parallel session also edits. That is a
near-certain merge conflict for zero coverage gain, so it is deliberately **not** done here. It is
worth doing at a quiet point, ideally as its own commit touching nothing else, after which
`check_file_imports` becomes a real gate and this document's subject cannot recur.

Do **not** bulk-add all 217 in one commit. Nothing has ever forced these to compile, two are
already known broken, and a single failing module in a 217-module addition makes the failure
un-attributable.

## 7. Honest limits of this document

- Compile status is settled and now clean: every manifest-missing module was built explicitly
  (445 targets). The first pass found **exactly two** failures, both named above; both were fixed
  and a second full pass is **`lake` exit 0, zero errors**. So there is no latent broken code in
  this backlog at all — the entire remaining risk is unverified *claims* and dormant *gates*.
- Error counts overstate damage in unbuilt code: `TimeSymmetricMarkovArrows` reported 6 errors
  arising from 2 defects, the rest cascade. Do not read an error count as a damage estimate here.
- Tiering uses namespace as a proxy for CAT/EPT relevance. A module can be core-relevant while
  living outside the listed namespaces; the tiers are a work order, not a judgement about physics.
- Claim counts are `formalizes` occurrences, which count edges rather than distinct claims — a
  module attaching one claim twice counts twice.
- "Uncovered" is about the *build*, not correctness. An uncovered module may be perfectly fine.
  The point is that nothing has checked.
