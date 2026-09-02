/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Zil.Horn
public meta import Zil.Horn

/-!
# A certified Turing-level deterministic computation (the classical substrate)

`CertifiedCogwheelAutomaton` used `Zil.Horn` on a *reversible finite automaton* —
a permutation on six states.  That is the **weakest** deterministic model: its
whole dynamics is "advance one state", it is immediately periodic, and its
configuration space is finite, so certifying its cycle exercised none of Horn's
actual power (a `Fintype` `decide` reaches it in principle; the earlier overflow
was Mathlib's `cycleType`, not real difficulty).  A finite permutation is **not**
a Turing machine, and its Koopman `{2πk/N}` spectrum is "quantum" only in the
interpretational sense of the cellular-automaton programme — there is no
unitarity-with-interference, no Quantum Turing Machine, no BQP.

This module works at the level where Horn's certified reachability is genuinely
non-trivial: a **deterministic register machine over the Peano naturals**.  Two
counters `C1, C2 : ℕ` are *unbounded* — the configuration space `cfg(State,C1,C2)`
has **no `Fintype`**, so `decide` cannot enumerate it — and two-counter (Minsky)
machines are **Turing-complete**, hence their halting and recurrence are
undecidable in general.  Horn certifies a *specific bounded run* by bounded SLD
plus independent proof-tree replay:

```text
step(cfg(run, C1, s(C2)), cfg(run, s(C1), C2)).   % transfer one unit C2 → C1
step(cfg(run, C1, z),     cfg(halt, C1, z)).       % C2 exhausted → halt
runs(X, X, z).
runs(X, Y, s(N)) :- step(X, Z), runs(Z, Y, N).
```

The transfer step is injective (locally reversible; a total time-reversible
realization is Bennett's construction), and the machine computes `C1 := C1 + C2`
by a loop whose length **depends on the input** — a genuine computation, not a
fixed cycle.  `add_2_3_certified` and `add_0_5_certified` certify concrete runs;
the loop length (4 and 6 steps) scales with the input, and no finite state space
bounds the configurations the family visits.

## What is and is not claimed

* **Claimed (certified):** a Turing-level *deterministic classical* computation,
  with a kernel-checkable proof tree for each specific bounded run — something a
  finite permutation cannot express and a `Fintype` `decide` cannot obtain.  This
  is the deterministic **sub-quantum substrate** that the CAT/EPT ur-model posits
  underneath physics.
* **Not claimed:** any quantum content.  There is no finite Koopman spectrum here
  (the orbit is input-dependent, the config space infinite), no unitary dynamics,
  no QTM.  Whether — and how — quantum phenomenology emerges from such a
  deterministic substrate is the open problem of the programme; Horn, a classical
  logical certifier, cannot produce amplitudes or interference and does not
  address it.
* **The one honest physical reading:** the certified step count is the
  computation's *entropic time* — physical time as a count of computational steps
  — which is exact and kernel-checkable, and is the only bridge to physics this
  layer legitimately supports.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.CertifiedReversibleRegisterMachine

open Zil.Horn

/-- A deterministic two-register machine computing `C1 := C1 + C2` (transfer `C2`
into `C1`), over Peano-unbounded counters, plus Peano-counted reachability. -/
def registerMachineSource : String :=
  "step(cfg(run, C1, s(C2)), cfg(run, s(C1), C2)).\n" ++
  "step(cfg(run, C1, z), cfg(halt, C1, z)).\n" ++
  "runs(X, X, z).\n" ++
  "runs(X, Y, s(N)) :- step(X, Z), runs(Z, Y, N).\n"

/-- The parsed machine-plus-reachability Horn program. -/
def registerMachine : Program := (Parser.parseText registerMachineSource).toOption.getD []

/-- Run on input `(C1,C2) = (2,3)`: reach `(halt, 5, 0)` in exactly four steps. -/
def addQuery_2_3 : List Atom :=
  (Parser.parseGoalsText
    "runs(cfg(run, s(s(z)), s(s(s(z)))), cfg(halt, s(s(s(s(s(z))))), z), s(s(s(s(z)))))").toOption.getD []

/-- Run on input `(C1,C2) = (0,5)`: reach `(halt, 5, 0)` in exactly six steps —
the loop length grows with the input. -/
def addQuery_0_5 : List Atom :=
  (Parser.parseGoalsText
    ("runs(cfg(run, z, s(s(s(s(s(z)))))), cfg(halt, s(s(s(s(s(z))))), z), " ++
     "s(s(s(s(s(s(z)))))))")).toOption.getD []

/-- The HORC source parses (the machine encoding is well-formed). -/
theorem registerMachineSource_parses :
    (Parser.parseText registerMachineSource).toOption.isSome = true := by
  native_decide

/-- **Certified computation `2 + 3 = 5`.**  Bounded SLD plus independent
proof-tree replay certifies that from `(run, 2, 3)` the machine reaches
`(halt, 5, 0)` in exactly four steps — a Turing-level deterministic computation
over unbounded counters, with a kernel-checkable derivation. -/
theorem add_2_3_certified : HasCertifiedSolution registerMachine addQuery_2_3 128 := by
  horn_certify

/-- **Certified computation `0 + 5 = 5`.**  The same machine, a longer certified
run (six steps): the loop length scales with the input, so no finite state space
bounds the family of configurations. -/
theorem add_0_5_certified : HasCertifiedSolution registerMachine addQuery_0_5 128 := by
  horn_certify

-- Certified answers for the (2,3) run (expect one certified derivation).
#eval (solveCertifiedDepth registerMachine addQuery_2_3 128).solutions.length

end Physlib.QuantumMechanics.CertifiedReversibleRegisterMachine
