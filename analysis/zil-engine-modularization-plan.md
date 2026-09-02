# Zil.Engine modularization — execution instructions

**Purpose of this file.** A self-contained plan for a *fresh session* (no prior context) to convert
`zil-lang-jrg`'s native engine to the Lean 4 `module` system so physlib can import it, then adopt it in
physlib to end the O(n²) List-engine perf problems and gain provenance. Every fact below was verified by
inspection on 2026-07-27; re-verify with the commands given rather than trusting the numbers blindly.

---

## 0. Repos, paths, and the write-scope caveat

- **Target repo (where the conversion happens):** `zil-lang-jrg` at
  a sibling checkout (`../zil-lang-jrg` from the physlib worktree). This is a *sibling* of physlib and the default agent scope treats siblings as read-only — the
  executing session must be **explicitly cleared to write in `zil-lang-jrg`** before starting.
- **Consumer repo (adopts the engine):** the physlib worktree
  a physlib worktree (branch
  `zil-dissipation-landauer`, pushes to remote `private` / branch `entropic-physlib-linear-full`). physlib's
  ZIL dep is the local path dep `../zil-lang-jrg`, so a rebuilt zil-lang-jrg is picked up directly.
- **Build toolchain:** Lean `v4.31.0` via `lake`. zil-lang-jrg is already built (`.lake/build` present).

---

## 1. Why (the diagnosis this plan acts on)

physlib's `Physlib/Meta/*` ZIL infrastructure has grown large because it **re-implements features ZIL
already has, but only in ZIL's non-`module` world** — which physlib (all `module`-system files) cannot
import. Concretely:

- physlib runs a **List-based** engine (`Zil.Datalog.Eval.deriveProgram`, `matchPattern : List Atom` +
  `filterMap`/`foldl`) → **O(n²)**. Every perf problem in the physlib ZIL audit (a ~20-min full-root
  report, a weakest-link closure that will not scale, an "adaptive fuel/depth" hack that had to be reverted
  as unreliable) is a symptom of this.
- ZIL already has an **Array-indexed** engine with **saturation** and **provenance**
  (`Zil.Engine.Query.closure`/`closureOfEnvironment`, `Zil.Engine.Provenance.{FactNode,Trace,WitnessState}`)
  — but it is non-`module`, so physlib cannot import it.
- `Zil.Datalog` (the 21 module files physlib does use) is a **parallel from-scratch reimplementation**, not
  a wrapper over the real engine (verify: `grep -rE '^import Zil\.(Core|Engine)' Zil/Datalog/` returns
  nothing).

**Payoff of finishing the modularization:** physlib imports the real indexed engine → the perf problems
dissolve, reports gain "why did this gate fire" provenance, and later the reinvented governance layers
(assumption-ledger blast-radius, honesty gates) can be retired in favor of ZIL's native
`Impact`/`ProofObligation`/`TheoremAudit`.

---

## 2. Established facts (re-verify, don't trust blindly)

**F1 — The convert-together set is small: 16 files / ~2028 LOC** (the transitive `Zil.*` import closure of
`Zil.Engine`). In dependency order (leaves first):

```
Zil/Core/Term.lean            (35)
Zil/Core/Attribute.lean       (51)
Zil/Core/Relation.lean        (63)   -- defines `structure RelExpr`
Zil/Core/Rule.lean            (60)   -- defines `Zil.Rule`
Zil/Core/Macro.lean           (36)
Zil/Core/Declaration.lean     (430)  -- priv-heavy (22)
Zil/Core/DeclarationSet.lean  (161)  -- priv 13
Zil/Core/Program.lean         (47)
Zil/Core/Query.lean           (43)
Zil/Core/Userset.lean         (134)
Zil/Codec/Attribute.lean      (71)
Zil/Codec/Canonical.lean      (120)  -- priv 15
Zil/Environment/Knowledge.lean(97)
Zil/Profile/Core.lean         (116)
Zil/Engine/Query.lean         (231)  -- priv 21; defines `closure`, `closureOfEnvironment`, `solve`
Zil/Engine/Provenance.lean    (333)  -- priv 25; FactNode/Trace/WitnessState
```
Re-verify the closure + LOC with the Python snippet in §7.A. (The exact ordering may need adjustment —
compute it from actual imports; do not hand-trust this list.)

**F2 — Bottom-up conversion is SAFE: a non-`module` file CAN import a `module` file.** Verified
empirically (exit 0):
```bash
cd ../zil-lang-jrg
printf 'import Zil.Datalog.Basic\ndef t : Nat := 0\n' > ZilDirTest.lean
lake env lean ZilDirTest.lean; echo "exit=$?"   # 0 = direction OK
rm -f ZilDirTest.lean
```
Consequence: converting the 16 files to `module` does **not** break their ~20 non-`module` consumers
(`Zil/Impact.lean`, `Zil/ProofObligation.lean`, `Zil/CLI/Main.lean`, `Zil/Parser/*`, `Zil/Test/*`, …) —
those keep importing them. Only the reverse (`module`→non-`module`) is forbidden. So this is **not** an
all-85-file rewrite; it is a 16-file bottom-up conversion.

**F3 — The engine gives physlib what it needs.** `Zil/Engine/Query.lean` exposes
`closure (facts : Array Zil.RelExpr) (rules : Array Zil.Rule)`, `closureOfEnvironment (env) (fuel := 64)`,
and `solve … : Array Binding` — i.e. Array-indexed **saturation** (the direct replacement for physlib's
List `deriveProgram`), plus `Zil.Engine.Provenance` for witness traces.

**F4 — The one real cost is a model adapter.** The engine speaks `Zil.RelExpr` (`Zil/Core/Relation.lean:13
structure RelExpr`) + `Zil.Rule`; physlib's rules speak `Zil.Datalog.Atom{object,relation,subject}` +
`Zil.Datalog.Rule`. There is **no existing bridge** (`Zil.Datalog.Interop`/`Compat` bridge Datalog↔Datalog
only). The two models are structurally close, so a **thin adapter** (`Datalog.Atom → RelExpr`,
`Datalog.Rule → Zil.Rule`) is the intended path — not a full rule rewrite.

**F5 — Conversion template (proven by the 21 already-module `Zil.Datalog` files).** A module file opens:
```lean
module

@[expose] public section

namespace Zil.Core   -- (the file's namespace)
...
```
and its imports become `public import …`. See `Zil/Datalog/Basic.lean` for the canonical shape.

---

## 3. Phase 1 — modularize the 16-file engine closure  (in `zil-lang-jrg`)

Do it **bottom-up** (a `module` may only import other `module`s, so a file can't convert until all its
`Zil.*` imports already have). Per file:

1. Insert `module` as the very first line (before the copyright block? — check the Datalog files: they put
   `module` first, then content; match whatever the existing module files do).
2. Add `@[expose] public section` after the imports (blanket-expose first; tighten to granular
   `public`/`private` only if a clean interface is wanted later — do NOT let visibility perfection block
   the spike).
3. Convert every `import Zil.X` to `public import Zil.X`. Non-`Zil` imports (Lean/Std/Mathlib) follow the
   same `public import` treatment as in the Datalog files.
4. Keep existing `private def`s private; they're fine inside a module. The friction is usually
   `deriving`, macro definitions, and `meta`/elaboration code — convert exactly as the Datalog files do
   (e.g. `meta` sections, `public meta import`). If a `deriving` or macro breaks under `module`, mirror the
   pattern from the closest Datalog file that does the same thing.
5. `lake build Zil.Core.<File>` (or the module name) — must be green before moving up the chain.

**Order:** `Core.Term → Core.Attribute → Core.Relation → Core.Rule → Core.Macro → Core.Declaration →
Core.DeclarationSet → Core.Program → Core.Query → Core.Userset → Codec.Attribute → Codec.Canonical →
Environment.Knowledge → Profile.Core → Engine.Query → Engine.Provenance`. (Confirm with the real import
graph — §7.A.)

**After each file and at the end, verify F2 still holds** — i.e. the whole zil-lang-jrg package still
builds (the non-module consumers must still import the now-module files):
```bash
cd ../zil-lang-jrg && lake build 2>&1 | tail -5
```

**Definition of done for Phase 1:** `lake build Zil.Engine.Query` and `lake build Zil.Engine.Provenance`
are green, AND a physlib-style probe compiles:
```bash
cd ../zil-lang-jrg
printf 'module\npublic import Zil.Engine.Query\n' > EngineProbe.lean
lake env lean EngineProbe.lean; echo "exit=$?"   # 0 = physlib (module) can now import the engine
rm -f EngineProbe.lean
```

---

## 4. Phase 1b — physlib adopts the engine  (in the physlib worktree — THE PAYOFF)

This is what actually kills the perf problems. Target the report driver, not the rule definitions.

1. **Add `../zil-lang-jrg`'s `Zil.Engine`/`Zil.Core` to physlib's import surface.** physlib already deps on
   `zil-lang-jrg` (the `Zil.Datalog` layer). The new `module` `Zil.Engine`/`Core` are now importable from
   physlib's `module` files.
2. **Write the adapter** (physlib side, e.g. `Physlib/Meta/ZilEngineAdapter.lean`):
   `Zil.Datalog.Atom → Zil.RelExpr` and the physlib rule set (`Zil.Datalog.Rule`) → `Array Zil.Rule`, so the
   existing hand-authored rules in `Physlib/Meta/ZilGraph.lean` are reused unchanged.
3. **Swap the engine call in `Physlib/Meta/ZilGraphReport.lean`:** replace the List
   `deriveProgram { … } fuel` calls (there are three: the main improvement pass, the dependency-cycle pass,
   the weakest-link pass) with `Zil.Engine.Query.closureOfEnvironment`/`closure` over the adapted facts+rules.
   The weakest-link `dependsOnDecl` transitive closure is the O(n²) hotspot that motivated the reverted
   "adaptive fuel" — the indexed engine removes the need for any depth bound (run it to real fixpoint).
4. **Wire provenance:** thread `Zil.Engine.Provenance` so each `[honesty]`/`[weakest-link]` finding can print
   *why* it fired (the witness chain), not just *that* it fired.
5. **Re-run the full-root audit** (`Physlib.Meta.ZilGraphAuditFull` / `scripts/zil-graph-report.sh`) — it
   should now complete quickly at full-root scale (4589 edges) instead of the ~20-min List-engine grind, and
   the buried-conditionality result becomes exhaustive (no depth bound) — resolving the honesty gap that the
   reverted adaptive-depth hack could not.

**Definition of done for Phase 1b:** the full-root report runs to completion with the indexed engine, at
full transitive depth, in minutes not tens-of-minutes; findings carry provenance.

---

## 5. Phase 2 — modularize governance (optional, larger; do AFTER Phase 1 lands)

Modularize `Zil/Impact.lean` (change-impact/blast-radius), `Zil/ProofObligation.lean`, `Zil/TheoremAudit.lean`,
`Zil/QueryGovernance.lean` (+ their Core closure, which Phase 1 already covers). Then retire the physlib
reinventions they subsume: the assumption-ledger blast-radius / `dependsOnDecl` reach in
`Physlib/Meta/ZilGraph.lean` ↔ `Zil.Impact`; the honesty/proof-obligation gates ↔
`Zil.ProofObligation`/`TheoremAudit`. Each of these is ~300 LOC and priv-heavy; convert with the same recipe.
This shrinks `Physlib/Meta/*` toward "CAT/EPT domain rules only," which is the correct end-state split
(ZIL = engine + generic governance; physlib = domain rules).

---

## 6. Recommended first move: a 1-file SPIKE (≈1 hour, de-risks everything)

Modularize the smallest leaf, `Zil/Core/Term.lean` (35 LOC, no `Zil.*` imports), and prove all three
directions still work:
```bash
cd ../zil-lang-jrg
# 1. add `module` + `@[expose] public section` to Zil/Core/Term.lean per §5 template, then:
lake build Zil.Core.Term                       # (a) builds as a module
lake build                                     # (b) non-module consumers of Core.Term still build
printf 'module\npublic import Zil.Core.Term\n' > Probe.lean
lake env lean Probe.lean; echo $?; rm Probe.lean # (c) a module file can import it
```
If all three pass, the 16-file conversion is de-risked; proceed up the dependency order. If any fail, the
failure mode (usually a `deriving`/macro/visibility idiom) tells you the one recurring fix to template
across the rest.

---

## 7. Verification snippets

**A. Recompute the engine closure + LOC (don't trust §2's list):**
```bash
cd ../zil-lang-jrg
python3 - <<'PY'
import re,os
def imp(m):
    p='Zil/'+m.replace('Zil.','').replace('.','/')+'.lean'
    return re.findall(r'^import (Zil\.[\w.]+)',open(p).read(),re.M) if os.path.exists(p) else []
seen=set(); st=['Zil.Engine.Query','Zil.Engine.Provenance']
while st:
    m=st.pop()
    if m in seen: continue
    seen.add(m); st+=[d for d in imp(m) if d not in seen]
for m in sorted(seen):
    p='Zil/'+m.replace('Zil.','').replace('.','/')+'.lean'
    print(len(open(p).read().splitlines()) if os.path.exists(p) else 0, m)
print(len(seen),"files")
PY
```

**B. Which non-module files consume the closure (should keep building — F2):**
```bash
grep -rlE '^import Zil\.(Engine|Core)' Zil --include='*.lean' | grep -vE '^Zil/(Core|Engine)/'
```

**C. Confirm the direction rule still holds (F2) any time you doubt it:** the `ZilDirTest.lean` snippet in §2.

---

## 8. Gotchas seen while scoping / in the physlib ZIL work

- **`@[zil_level]` / attributes need `meta import Zil`** in the file that uses them (a physlib-side lesson,
  but the same "meta features need the meta import" rule applies when converting).
- **Two separate `@[..]` attribute blocks before one decl do NOT parse** — combine (`@[a, b] def`).
- **Editing a foundational module triggers a huge rebuild cascade** — e.g. touching one Schrödinger analysis
  file rebuilt ~300 modules. Expect Phase-1b physlib rebuilds to be long; batch edits.
- **Disk:** the machine's APFS container runs near-full (94% / <1 GiB free at times), which causes spurious
  `failed to write .olean` errors that look like build failures but aren't. Free space before long builds
  (session build-log captures under the scratchpad are safe to delete).
- **Do NOT** reintroduce any graph-size-adaptive depth/fuel to "make the report finish" — it produces
  false-negative "0"s and was explicitly rejected. The indexed engine is the correct fix; run to real
  fixpoint.

---

## 9. One-paragraph summary to hand the executing session

Convert the 16-file transitive closure of `Zil.Engine` (`Zil.Core.*` + `Zil.Engine.Query`/`Provenance` +
`Zil.Codec.Attribute`/`Canonical` + `Zil.Environment.Knowledge` + `Zil.Profile.Core`, ~2028 LOC) in
`zil-lang-jrg` to the Lean `module` system, bottom-up (leaves first), using the `module` + `@[expose]
public section` + `public import` template proven by the existing `Zil.Datalog` module files. This is safe
because non-`module` files can import `module` files (verified), so the ~20 non-module consumers don't
cascade. Then, in physlib, write a thin `Zil.Datalog.Atom/Rule → Zil.RelExpr/Rule` adapter and swap the
three `deriveProgram` calls in `Physlib/Meta/ZilGraphReport.lean` for `Zil.Engine.Query.closure`, wiring in
`Zil.Engine.Provenance`. That replaces the O(n²) List engine with the indexed native one — ending the
full-root report perf problem at real fixpoint (no depth bound) and adding why-explanations. Start with a
1-file spike on `Zil.Core.Term` to de-risk.
```
