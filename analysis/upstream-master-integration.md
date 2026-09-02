# Integrating `upstream/master` into the fork

Attempt and findings, 2026-08-27, from `recovery/entropic-physlib-linear-full-v433`.

Resolution policy used: **keep the fork's API and merge around it** — every rename conflict resolved in
favour of the fork, upstream's other work taken.

## Shape of the divergence

`upstream/master` (`9c33f2ca2`) is 145 commits outside this branch; the branch is 1461 commits outside
the merge base (`87c4f192c`). `git rebase upstream/master` is therefore the wrong operation — it would
replay the entire fork. The integration is a merge.

Upstream is **already on Lean 4.33.0** (`a50684a19`), bumped without the
`backward.isDefEq.respectTransparency=false` flags this fork still carries in `lakefile.toml`.

A test merge produces 48 conflicting files. Only 11 are caused by this session's migration commits; the
other 37 are pre-existing fork/upstream divergence.

## Upstream restructured five module trees the fork actively develops

This is the whole difficulty. Upstream moved, and in places renamed the *namespace* of:

| base path | upstream path | fork importers |
|---|---|---|
| `QuantumMechanics/FiniteTarget/` | `QuantumMechanics/HilbertSpaces/FiniteTarget/` | 56 |
| `QuantumMechanics/DDimensions/` | `QuantumMechanics/HilbertSpaces/SpaceD/` | 31 |
| `QuantumMechanics/OneDimension/` | `HarmonicOscillator/`, `HilbertSpaces/`, `Operators/` `OneDimension/` | many |
| `FluidDynamics/NavierStokes/` | `FluidDynamics/CauchyFlow/`, `FluidFlow/` | several |

`FiniteTarget` is not a pure move: upstream renamed the namespace `QuantumMechanics.FiniteTarget` ->
`QuantumMechanics.FiniteHilbertSpace` and rewrote `Basic.lean` (177 differing lines). The fork's 15
QuantumInertialFrame modules are built on the old namespace.

Git's directory-rename detection silently relocates the fork's *new* files in those trees onto the
upstream paths. Left alone the merge also **deletes 46 fork `.lean` files** that upstream moved away and
the fork had not modified.

### The trees must not be rooted twice

The fork already ships `HilbertSpaces/SpaceD/` (8 files, byte-identical to upstream bar comments)
*alongside* `DDimensions/`. It builds only because `Physlib.lean` roots `DDimensions` and **not**
`HilbertSpaces/SpaceD` — both declare `namespace QuantumMechanics.SpaceDHilbertSpace`, so rooting both
would be duplicate declarations. Any resolution has to preserve that: keep upstream's copies on disk,
unrooted.

## What resolves mechanically

Everything structural, in a few seconds:

* **18 AU** (directory-rename relocations) — restore the fork's files at their original paths and drop
  the relocated copies.
* **4 UD** (upstream deleted, fork modified) — keep the fork's.
* **46 silent deletions** — restore from the fork tip.
* **1 AA** (`HilbertSpaces/SpaceD/PolyBddSchwartzSubmodule.lean`) — take upstream's; the 17-line diff is
  purely added explanatory comments on the same proof.
* `lean-toolchain` — both sides are `v4.33.0`; textual conflict only.
* `.gitignore`, `lakefile.toml`, `lake-manifest.json` — union. This keeps the fork's three
  `backward.isDefEq` flags and its `zil-lean` pin while taking upstream's two new `lean_exe` entries.
* `Physlib.lean` — take the fork's list verbatim (2061 imports, all resolving after the restores).
  Upstream's new modules stay on disk unrooted, to be added deliberately in a later pass.
* **4 content files** auto-resolve: upstream's side differs from the fork's only by an added
  `set_option backward.isDefEq.respectTransparency false in` (and `lemma` -> `theorem`). Taking
  upstream's is harmless while the global flag stays, and is progress toward dropping it.

That leaves **16 files / 49 hunks**.

## What does not resolve mechanically

Most of the 16 are cases where upstream golfed the same proof *better* than this branch did, and
upstream's version should simply win — e.g. `Relativity/Tensors/Basic.lean`, where upstream replaces a
hand-rolled `let P … change P t … apply induction_on_basis` with
`induction t using induction_on_basis with`, and `Tensors/Reindexing.lean`, where upstream discharges a
`grind (splits := 60)` with a new named lemma `Fin.succSuccAbove_succAbove_comm_apply`. Taking upstream's
side there reverts some of this session's golf, which is the right trade: it is duplicated effort that
upstream did better, and it reduces divergence.

Two are **genuine design conflicts** and are the real blockers.

### 1. `Physlib/Units/Dimension.lean` — incompatible designs of the core structure

* **Fork**: `Dimension` is a fixed six-field structure whose sixth field is `information`, a base
  dimension for Shannon entropy / bits / qubits, justified in its docstring by the Brillouin (1956) and
  Landauer (1961) argument, with `k_B` carrying `[E·Θ⁻¹·I⁻¹]`. At least eight modules depend on it,
  including `Physlib/Meta/ZilDimension.lean` — the ZIL dimensional-analysis meta layer.
* **Upstream**: `Dimension (B : Type)` carries `exponent : B → ℚ`, parameterised over a basis of base
  dimensions, with `LTMCTDimensionBase` (five charge-based generators, no information) as the default.
  Twelve upstream files use the parameterised form.

These cannot both be the definition of `Dimension`. Note the appealing end state: upstream's
parameterisation can *express* the fork's information dimension as a custom basis `B`, which would keep
the fork's physics while converging on upstream's design. That is a migration of the fork's units layer
and its ZIL dimension checker, not a merge resolution.

### 2. `Relativity/Tensors/ComplexTensor/Units/Basic.lean` — a fifth relocated tree

Initially this looked like a self-contained lemma rename. It is not; it is another tree relocation with
an API replacement, in the same class as the four above.

* Upstream moved the whole Weyl development from `Relativity/Tensors/ComplexTensor/Weyl/` (6 files, which
  the fork still has) to `Relativity/Fermions/Weyl/`.
* The basis accessors went with it: `dualLeftBasis` / `leftBasis` -> `DualLeftHandedWeyl.basis` /
  `LeftHandedWeyl.basis`. Upstream has **zero** occurrences of `dualLeftBasis`; the fork has **53**, and
  defines it in `ComplexTensor/Weyl/Basic.lean`, a file upstream deleted.
* In `Units/Basic.lean` upstream also introduced `δ`, `δ'`, `δL`, `δL'`, `δR`, `δR'` notation and
  *shuffled* lemma names rather than simply renaming them: the fork's
  `dualLeftLeftUnit_eq_dualLeftBasis_leftBasis` becomes `dualLeftLeftUnit_eq_basis`, while the fork's
  existing `dualLeftLeftUnit_eq_basis` becomes `dualLeftLeftUnit_eq_tensor_basis`. A naive rename would
  silently collide.

So this cannot be landed ahead of the merge as a tidy rename commit. It needs the same decision the other
trees need: adopt upstream's `Relativity/Fermions/Weyl/` layout and basis API, or keep the fork's.

## Recommended sequence

1. Settle the `Dimension` question first — it gates the units layer, and `ZilDimension.lean` sits on top
   of it. Expressing the fork's `information` dimension as an upstream basis `B` is the convergent
   option.
2. Decide the Weyl tree alongside it — same question, same shape: adopt `Relativity/Fermions/Weyl/`
   and `DualLeftHandedWeyl.basis` (53 fork call sites), or keep `ComplexTensor/Weyl/`.
3. Then run the mechanical resolution above and take upstream's side on the remaining golf conflicts.
4. Only then revisit the global `backward.isDefEq` removal
   (`analysis/defeq-transparency-removal.md`) — upstream's per-declaration escapes arrive with this
   merge and do much of that work.

## Reproducing the mechanical resolution

```
git worktree add /tmp/wti -b integrate/upstream-master HEAD
cd /tmp/wti && git merge --no-commit --no-ff upstream/master     # 48 conflicts
# restore fork trees at fork paths, keep UD files, union the config files,
# take the fork's Physlib.lean, take upstream's AA file
# -> 16 files / 49 hunks remain, per the sections above
```

Nothing from this attempt was committed; the branch is untouched.
