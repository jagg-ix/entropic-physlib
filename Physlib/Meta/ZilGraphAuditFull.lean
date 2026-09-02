/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.DerivedPredictions
public import Physlib.Meta.ZilGraphReport

/-!
# Repo-wide ZIL knowledge-graph audit

Invokes `#zil_graph_report` (from `Physlib.Meta.ZilGraphReport`) over the entire `Physlib` library plus the
derived-predictions ledger, so the gap audit covers the whole knowledge graph rather than a demonstration
scope. This is a leaf module that nothing imports, so it is not part of the default build — run it on
demand (or via `tools/zil-graph-report.sh`):

```
lake build Physlib.Meta.ZilGraphAuditFull
```

The audit runs through `Physlib.Meta.ZilDatalogFast.deriveProgramFast`, the indexed saturating
evaluator, rather than the reference `Zil.Datalog.deriveProgram`. The reference engine is quadratic in
its dedup and unindexed in its joins, and stopped finishing on this graph entirely — a run was killed
after 5h32m. The indexed evaluator returns the identical atom list (checked by `#guard` against the
reference engine on every sample program in `Physlib.Meta.ZilDatalogFastCheck`) and completes the
repo-wide pass in ~2 minutes.
-/

#zil_graph_report
