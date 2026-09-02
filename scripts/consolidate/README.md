# `scripts/consolidate/` — graph-driven module consolidation

Merges modules that the ZIL graph shows are one topic. File names cannot see that three
modules are three sections of one paper; the citation graph can.

```
./scripts/consolidate/run.sh                 # discover + plan, writes nothing
./scripts/consolidate/run.sh --apply         # plan, apply, verify
```

Stages, each runnable alone:

| stage | command | effect |
|---|---|---|
| 1 discover | `lake env lean scripts/consolidate/candidates.lean` | candidate edges from the elaborated graph |
| 2 plan | `consolidate.py plan` | clusters + safety checks → reviewable `plan.json` |
| 3 apply | `consolidate.py apply plan.json --apply` | merge, delete, repair imports |
| 4 verify | `consolidate.py verify plan.json` | dangling-import check, host builds, ZIL gate |

## What counts as a candidate

* **`PAIR` — mutual citation.** A cites B *and* B cites A. An import edge can only point
  one way, so a cycle in the citation graph means one topic in two files. This is the
  signal that found the three-module split of Bousso's *The holographic principle*.
* **`FRAG` — exclusive fragment.** Every citation a small module makes targets one single
  module. Off by default (`--include-fragments`), because some fragments are deliberate
  interface modules with their own audits.
* **`SUBJ` — split subject.** One claim subject with declarations in several modules.
  Reported for review only; it is usually several modules supplying evidence for one
  ledger axiom, which is correct as it stands.

One-directional citation is **ordinary layering** and is never emitted. Acting on it
would merge a library into everything that uses it.

## Safety rules, each learned by breaking something

* **Namespaces are preserved verbatim.** Every absorbed module keeps its own
  `namespace ... end` inside the host, so declaration full names never change and no
  external reference can break. Inferring a namespace from a `namespace` line and
  rewriting it repo-wide once corrupted 180 files, because one module declares the broad
  `Physlib.Thermodynamics`. The planner still reports broad namespaces as a note.
* **Sources are ordered topologically** by their import edges before concatenation. A
  block placed ahead of the lemma it consumes does not elaborate.
* **Imports are repaired repo-wide**, manifest included, and the host is inserted into the
  manifest in sorted position if absent.
* **Rollback is file-level.** `git checkout -- <file> ...`, never a directory: a
  directory-level restore silently reverted an unrelated fix from an earlier merge.
* **Dry run by default.** `apply` writes nothing without `--apply`.
* **Budgets.** `--max-files` (default 50) caps a round; `--max-lines` (default 1600)
  refuses clusters that would build a module larger than the repo's largest.

## Re-run after every round

Merging one pair routinely reveals a third member of the same arc that the pair was
masking — the radial-Poisson arc surfaced its third module only after the first two were
joined. A round is finished when a fresh discovery pass proposes nothing new.

## Reading the verify step

`verify` fails closed: it refuses to build while any file still imports an absorbed
module, and it prints the exact file-level `git checkout` line to undo the round if the
host build fails. Note that `lake build ... | grep ...` reports **grep's** exit status,
not lake's — always read the `Build completed successfully` line, never the pipeline's
status.
