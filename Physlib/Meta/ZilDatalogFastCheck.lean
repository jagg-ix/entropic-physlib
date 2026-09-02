/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public meta import Physlib.Meta.ZilGraph
public meta import Physlib.Meta.ZilDatalogFast

/-!
# The indexed evaluator agrees with the reference engine

`Physlib.Meta.ZilDatalogFast.deriveProgramFast` exists only to make the repo-wide audit finish; it
must
not change a single answer. The rule-soundness theorems in `Physlib.Meta.ZilGraph` are all stated
against
`Zil.Datalog.deriveProgram`, so what has to hold is that the fast evaluator returns *the very same
list*
— same atoms, same order — on every program those theorems exercise.

That agreement is no longer only tested — it is **proved**:
`Physlib.Meta.ZilDatalogFast.deriveProgramFast_eq` in `Physlib.Meta.ZilDatalogFastEquiv` shows
`deriveProgramFast p fuel = deriveProgram p fuel` for *every* program and fuel budget, with no
side conditions.  Each `#guard` below is an instance of that theorem, kept as a fast end-to-end
smoke test: it checks the agreement by *evaluation* on every sample program in
`Physlib.Meta.ZilGraph`, at the fuel values used by the soundness theorems and by
`Physlib.Meta.ZilGraphReport` (3, 4 and 8), and so also cross-checks the compiled code paths
(`Std.HashMap`/`Std.HashSet` at runtime) that the kernel-level proof does not execute.

These are list equalities, not set equalities: the fast evaluator deduplicates in first-occurrence
order
precisely so that this stronger statement is available and nothing downstream can depend on
ordering that
silently changed.
-/

open Zil.Datalog
open Physlib.Meta.ZilGraph
open Physlib.Meta.ZilDatalogFast

namespace Physlib.Meta.ZilDatalogFastCheck

/-! ### Gap detectors -/

#guard deriveProgramFast sampleGraph 4 == deriveProgram sampleGraph 4
#guard deriveProgramFast sampleGraph 8 == deriveProgram sampleGraph 8
#guard deriveProgramFast statusSample 4 == deriveProgram statusSample 4
#guard deriveProgramFast statusSample 8 == deriveProgram statusSample 8
#guard deriveProgramFast documentedSample 4 == deriveProgram documentedSample 4
#guard deriveProgramFast documentedSample 8 == deriveProgram documentedSample 8

/-! ### Dependency closure and cycles -/

#guard deriveProgramFast dependencySample 4 == deriveProgram dependencySample 4
#guard deriveProgramFast dependencySample 8 == deriveProgram dependencySample 8
#guard deriveProgramFast cyclicSample 4 == deriveProgram cyclicSample 4
#guard deriveProgramFast cyclicSample 8 == deriveProgram cyclicSample 8

/-! ### Primitive-vs-derived consistency, including the canonical-alias joins -/

#guard deriveProgramFast primitiveSample 4 == deriveProgram primitiveSample 4
#guard deriveProgramFast primitiveSample 8 == deriveProgram primitiveSample 8
#guard deriveProgramFast canonicalPrimitiveSample 4 == deriveProgram canonicalPrimitiveSample 4
#guard deriveProgramFast canonicalPrimitiveSample 8 == deriveProgram canonicalPrimitiveSample 8
#guard deriveProgramFast canonicalAlphaSample 4 == deriveProgram canonicalAlphaSample 4
#guard deriveProgramFast canonicalLambdaSample 4 == deriveProgram canonicalLambdaSample 4
#guard deriveProgramFast canonicalWeinbergSample 4 == deriveProgram canonicalWeinbergSample 4

/-! ### Evidence scope and adaptive conformance -/

#guard deriveProgramFast evidenceGapSample 4 == deriveProgram evidenceGapSample 4
#guard deriveProgramFast evidenceGapSample 8 == deriveProgram evidenceGapSample 8
#guard deriveProgramFast conformanceSample 4 == deriveProgram conformanceSample 4
#guard deriveProgramFast conformanceSample 8 == deriveProgram conformanceSample 8

/-! ### Status honesty -/

#guard deriveProgramFast statusOverclaimSample 4 == deriveProgram statusOverclaimSample 4
#guard deriveProgramFast statusOverclaimSample 8 == deriveProgram statusOverclaimSample 8
#guard deriveProgramFast statusOverclaimRealSample 4 == deriveProgram statusOverclaimRealSample 4
#guard deriveProgramFast premiseAliasSample 4 == deriveProgram premiseAliasSample 4
#guard deriveProgramFast premiseAliasSample 8 == deriveProgram premiseAliasSample 8

/-! ### Weakest link and the assumption ledger

These are the transitive-closure programs -- the ones the reference engine cannot finish at repo
scale --
so agreement here is the load-bearing check. Fuel 3 is what the report uses. -/

#guard deriveProgramFast weakestLinkSample 3 == deriveProgram weakestLinkSample 3
#guard deriveProgramFast weakestLinkSample 4 == deriveProgram weakestLinkSample 4
#guard deriveProgramFast weakestLinkSample 8 == deriveProgram weakestLinkSample 8
#guard deriveProgramFast weakestLinkTransSample 3 == deriveProgram weakestLinkTransSample 3
#guard deriveProgramFast weakestLinkTransSample 4 == deriveProgram weakestLinkTransSample 4
#guard deriveProgramFast weakestLinkTransSample 8 == deriveProgram weakestLinkTransSample 8

/-! ### Fuel exhaustion, not just saturation

At fuel 0 and 1 the closure is genuinely truncated. The fast evaluator's early exit must not make it
derive *more* than the reference engine would at the same budget. -/

#guard deriveProgramFast weakestLinkTransSample 0 == deriveProgram weakestLinkTransSample 0
#guard deriveProgramFast weakestLinkTransSample 1 == deriveProgram weakestLinkTransSample 1
#guard deriveProgramFast weakestLinkTransSample 2 == deriveProgram weakestLinkTransSample 2
#guard deriveProgramFast dependencySample 0 == deriveProgram dependencySample 0
#guard deriveProgramFast dependencySample 1 == deriveProgram dependencySample 1
#guard deriveProgramFast cyclicSample 1 == deriveProgram cyclicSample 1
#guard deriveProgramFast sampleGraph 0 == deriveProgram sampleGraph 0
#guard deriveProgramFast sampleGraph 1 == deriveProgram sampleGraph 1

end Physlib.Meta.ZilDatalogFastCheck
