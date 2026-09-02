# Removing the global `backward.isDefEq.respectTransparency=false` escapes

> **UPDATE 2026-08-27.** QuantumInfo is **done** — its flag is removed and the library builds green.
> See the commit `refactor(quantuminfo): drop the global defeq-transparency escape`. The method that
> worked was not to invent fixes but to converge on upstream, which had already solved this library by
> per-declaration escapes plus a few real proof repairs; QuantumInfo now carries 176 local escapes
> against upstream's 177. Two flags remain, on `Physlib` and `PhyslibAlpha`.
>
> One correction to the numbers below: the 97 errors were measured with all three flags removed at once,
> and lake skips modules downstream of a failure, so they were a **lower bound** in a stronger sense than
> stated. Removing QuantumInfo's flag alone surfaced 17 errors initially, but fixing those revealed more
> in previously-unreachable modules; the true total took ten build rounds to exhaust. Expect the same
> shape for Physlib: the 97 will grow as earlier failures are cleared.

Scoping experiment, 2026-08-27. Branch `recovery/entropic-physlib-linear-full-v433`
at the Lean 4.33 migration tip.

## The escape

`lakefile.toml` passes `-Dbackward.isDefEq.respectTransparency=false` to all
three libraries (`Physlib`, `PhyslibAlpha`, `QuantumInfo`). Upstream
`leanprover-community/physlib` does **not**: its `master` completed the same
4.33 bump (`a50684a19`) with only `-Dwarn.sorry=false` and
`-Dweak.says.verify=true`. So this fork carries an escape upstream does not
need, and the two lakefiles differ only in this flag.

The tree separately carries **344** local
`set_option backward.isDefEq.respectTransparency false in` escapes across
**123** files. Those are unaffected by this experiment -- the question is
only whether the *global* default is still load-bearing on top of them.

## Result: it is

Dropping the three flags and rebuilding from scratch fails.

- `lake build` exit 1
- **97 genuine proof failures** across **31 files**
  (128 `error:` lines, of which 31 are per-module `Lean exited with code 1`)
- This is a **lower bound**: lake skips modules downstream of a failed one,
  so files depending on e.g. `Relativity/Tensors/RealTensor/Vector/Basic.lean`
  were never compiled.

### Failure modes

| count | kind |
|-------|------|
| 40 | unsolved goals |
| 30 | `rewrite` failed: did not find an occurrence of the pattern |
| 3 | `simp` made no progress |
| 3 | `native_decide` failed to compile |
| 3 | (kernel) declaration has metavariables |
| 2 | `linarith` failed |
| 2 | type mismatch after simplification |
| 2 | `rfl` failed |

### Worst-affected files

| errors | file |
|--------|------|
| 15 | `Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean` |
| 12 | `QuantumInfo/ClassicalInfo/Prob.lean` |
| 9 | `Physlib/QuantumMechanics/ComplexAction/Particles/HadronFlavorModel.lean` |
| 6 | `Physlib/Relativity/LorentzGroup/Proper.lean` |
| 6 | `Physlib/QuantumMechanics/ComplexAction/Hopf/QuaternionIsoclinicHopfFibration.lean` |
| 5 | `Physlib/Relativity/LorentzGroup/Boosts/Basic.lean` |

The remaining 25 files carry 1-4 failures each; the long tail is dominated by
the dimensional-unit modules (`LengthUnit`, `TimeUnit`, `MassUnit`,
`ChargeUnit`, `TemperatureUnits`), which fail identically -- a `rfl`/`simp`
step that closed by unfolding through a reducibility barrier.

## Why the count understates the work

The two failures in `Relativity/Tensors/RealTensor/Vector/Basic.lean`
(`basis_inner`, `inner_basis`, lines 435/441) are the same two proofs the
migration commits had to weaken to `simp [-Fintype.sum_sum_type]`. Sites like
these are already known-fragile under transparency changes, and fixing them
needs real proof work rather than a mechanical rewrite.

## Recommended shape for the project

1. Do it **after** the upstream integration, not before -- 30 of these 31
   files also change on `upstream/master`, and upstream may already have
   fixed the same proofs while doing its own flag-free bump. Porting their
   fixes is cheaper than reinventing them.
2. Work library-by-library. `QuantumInfo` is separable (13 failures over 3
   files) and is also where `upstream/stdbasis-refactor` drops 17 local
   escapes wholesale -- see `e3a45ba3f`.
3. Convert to *local* escapes only where a proof genuinely needs the old
   behaviour, so the residual debt stays countable, and drop the global flag
   once each library is clean.

Do **not** land a change that trades 3 global flags for ~97 new local ones;
that inflates the 344 already present and moves away from upstream.

## Reproducing

```
sed -i '' 's/, "-Dbackward\.isDefEq\.respectTransparency=false"//' lakefile.toml
lake build
git checkout lakefile.toml
```

## Physlib: attempted, reverted, and what it established (2026-08-27)

QuantumInfo and PhyslibAlpha are done. Physlib was attempted with the same convergence method and
**reverted**; the tree keeps its one remaining flag. Three findings make it a different problem, and they
are the reason to plan it deliberately rather than grind at it.

### 1. Convergence only reaches a fifth of the library

Of Physlib's 2408 `.lean` files, only **461** exist upstream; **1947 are fork-only**. "Adopt upstream's
already-solved version" — the move that carried QuantumInfo (56 of 87 files) and PhyslibAlpha (all 31) —
covers under 20% here. The rest needs original work.

### 2. The fixes are *coupled* to the flag; the library cannot be converted incrementally

This is the decisive one. Upstream's version of the five dimensional-unit modules ends
`scale_div_self` with a `rfl` after the `simp`; this fork's does not, because the golf that removed it
was masked by the global flag. So:

* with the flag **off**, the `rfl` is **required** — without it, `unsolved goals`;
* with the flag **on**, the same `rfl` is **forbidden** — `No goals to be solved`.

The two configurations are mutually exclusive for these files. Landing upstream-converged versions ahead
of the flag removal is therefore impossible: a build with the flag still on rejects exactly the files the
removal needs. Verified — 13 such files were adopted and produced 16 errors of this shape
(`No goals to be solved`, plus kernel `declaration has metavariables` in `ComponentIdx/Single`).
**Physlib must be converted atomically: flag and files in one commit.**

### 3. Blind escape insertion overshoots and then stalls

Driving the loop mechanically — build, insert
`set_option backward.isDefEq.respectTransparency false in` at each failing declaration, rebuild — ran
eight rounds and moved 28 failing files to 8, but:

* it inserted its way to **696** escapes against upstream's **544**, overshooting by 152 with insertions
  that fixed nothing (rounds 7 and 8 each added ~22 escapes for zero net progress);
* it stalled at **28 errors in 8 files** that no escape fixes — `CKMMatrix/Basic` (9),
  `HadronFlavorModel` (9, including `native_decide` IR-compilation failures), plus
  `QuaternionIsoclinicHopfFibration`, `Tensors/Evaluation` and three anomaly-cancellation modules. These
  need real proof repair;
* placing the escape correctly is itself fiddly: it must go above the whole attached prefix — attributes,
  docstring, multi-line `variable ... in`, and a bare `noncomputable` line — and a naive insertion
  silently splits `noncomputable` from its `def`.

So the escape count is not a target to be reached; it is an outcome of doing the proof work. Converging
on upstream's 544 by insertion alone produces a worse configuration than the three global flags.

### Revised recommendation

Physlib's removal is a single atomic change of roughly this shape, and wants to be scheduled as its own
project rather than attempted opportunistically:

1. Do it **after** the upstream integration, so the 461 shared files arrive already converged and the
   coupling in finding 2 resolves itself for them.
2. Fix the ~28 hard sites by hand — they are concentrated in CKM, hadron flavour, and anomaly
   cancellation.
3. Add escapes only where a proof genuinely needs the old behaviour, and expect the total to land near
   upstream's 544 *because* the proofs were repaired, not by insertion.
