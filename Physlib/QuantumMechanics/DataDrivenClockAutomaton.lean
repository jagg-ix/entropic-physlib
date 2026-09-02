/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.KoopmanQuantization
public import Zil.Horn
public meta import Zil.Horn

/-!
# The data-driven clock: a Turing-level automaton whose transition computes only on data

A deterministic Turing-complete automaton has a single global tick, but its
transition function does *nontrivial* work only where there is **data**.  On the
quiescent region — blank tape, exhausted counters, empty lattice — the transition
is the **identity**: nothing is read, nothing is written, the configuration is a
**fixed point**.  So the physical, entropic clock is not the global tick; it
advances only where the state actually changes, i.e. where computation is
happening.  "No data ⇒ no computation ⇒ no time."

This module makes that precise and connects it to two pieces of the repository's
physics that turn out to be the same statement read two ways.

## The certified computation (layer b)

`dataClock` is a deterministic two-register machine (`Minsky`, hence
Turing-complete) over Peano-**unbounded** counters, with the halted state made an
**explicit fixed point** — the clock frozen once the data `C2` is spent:

```text
step(cfg(run, C1, s(C2)), cfg(run, s(C1), C2)).   % compute while there is data
step(cfg(run, C1, z),     cfg(halt, C1, z)).       % data exhausted → halt
step(cfg(halt, C1, C2),   cfg(halt, C1, C2)).      % halted: identity — clock frozen
```

`computing_certified` certifies (bounded SLD + proof-tree replay) a run that
changes state on every step while data remains; `halt_frozen_certified` certifies
that the halted, data-free configuration maps to itself — the transition ticks but
the state does not move.  The *entropic* time of the computation is the number of
state-**changing** steps (the data content), not the global tick count.

## The relation to TISE

`KoopmanQuantization.isPhysical_iff_fixed` states that the Page–Wootters /
Wheeler–DeWitt timeless constraint `(U_σ − 1)ψ = 0` is satisfied **exactly by the
fixed points** `U_σ ψ = ψ` — and its `koopmanTimelessConstraint` docstring names
that kernel *the stationary, time-independent-Schrödinger sector*.  So:

> data-free / quiescent (`σ` acts as identity)  ⟺  fixed point `U_σ ψ = ψ`
>  ⟺  TISE-stationary / timeless.

`vacuum_fixed` shows the data-free vacuum config is a fixed point of `dataClock`;
`timeless_constant_on_data` proves the converse pressure — any timeless amplitude
is **constant along a data orbit** (`stationary_pointwise` around the cycle): the
clock cannot resolve times within an orbit, so a state that distinguishes them is
*not* stationary — it evolves, i.e. the clock ticks precisely on data.  The
eigen-equation `U_σ ψ = e^{−iE}ψ` is the discrete TISE, and `E` is the clock rate;
`E = 0` (a fixed point) is the timeless vacuum.

## The relation to KL (both of them)

The same clock has a time-domain and a spectral-domain reading, and CAT/EPT's two
"KL"s are exactly those two domains:

* **Kullback–Leibler (time domain).**  The entropic-time increment per step is the
  relative entropy processed, `dτ ∝ D_KL(ρ_{t+1} ‖ ρ_t)` — the repository's
  entropic-clock *data-processing* H-theorem
  (`ComplexAction.EntropicTime.EntropicDataProcessingHTheorem`,
  `TotalCorrelationEntropicClock`).  On a fixed point the state does not change,
  `D_KL = 0`, and the clock does not advance: this is the information-theoretic
  form of "no data ⇒ no time".

* **Källén–Lehmann (spectral domain).**  The clock-rate spectrum — the eigenphases
  `e^{−iE}` of `U_σ`, i.e. the TISE eigenvalues — carries a **positive spectral
  density** `ρ(E) ≥ 0` (`QFT.OsterwalderSchrader.KallenLehmannPositivity`).  The
  vacuum sits at `E = 0` (the fixed point / stationary sector) and "data" is
  spectral weight above it; the TISE eigenvalues are the support of the
  Källén–Lehmann measure.

The two are Wick/Fourier duals — the time-domain KL increment and the
spectral-domain KL density are one entropic clock in complementary domains, the
same duality as entropic time ↔ imaginary modular time.  Horn certifies only the
classical deterministic substrate (the computation and its fixed points); the
spectral/quantum content is the Koopman lift, and whether it reproduces genuine
quantum phenomenology remains the open problem.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.DataDrivenClockAutomaton

open Zil.Horn
open Physlib.QuantumMechanics.KoopmanQuantization

/-! ### The certified data-driven computation -/

/-- A deterministic 2-register machine whose halted (data-free) state is an
explicit fixed point: the clock is frozen where there is no data. -/
def dataClockSource : String :=
  "step(cfg(run, C1, s(C2)), cfg(run, s(C1), C2)).\n" ++
  "step(cfg(run, C1, z), cfg(halt, C1, z)).\n" ++
  "step(cfg(halt, C1, C2), cfg(halt, C1, C2)).\n" ++
  "runs(X, X, z).\n" ++
  "runs(X, Y, s(N)) :- step(X, Z), runs(Z, Y, N).\n"

/-- The parsed data-driven machine. -/
def dataClock_program : Program := (Parser.parseText dataClockSource).toOption.getD []

/-- The computing phase: from `(run, 2, 3)` reach `(halt, 5, 0)` in four
state-changing steps (the data content plus the halt). -/
def computingQuery : List Atom :=
  (Parser.parseGoalsText
    "runs(cfg(run, s(s(z)), s(s(s(z)))), cfg(halt, s(s(s(s(s(z))))), z), s(s(s(s(z)))))").toOption.getD []

/-- The halted phase: the data-free configuration maps to itself for three ticks
— the clock ticks but the state does not move. -/
def frozenQuery : List Atom :=
  (Parser.parseGoalsText
    "runs(cfg(halt, s(s(s(s(s(z))))), z), cfg(halt, s(s(s(s(s(z))))), z), s(s(s(z))))").toOption.getD []

/-- The HORC source parses. -/
theorem dataClockSource_parses : (Parser.parseText dataClockSource).toOption.isSome = true := by
  native_decide

/-- **Clock ticks on data.**  The computation runs (changing state each step)
while data remains — a certified Turing-level deterministic computation. -/
theorem computing_certified : HasCertifiedSolution dataClock_program computingQuery 128 := by
  horn_certify

/-- **Clock frozen off data.**  The halted, data-free configuration is a fixed
point: it maps to itself, so no state change and no entropic time accrue. -/
theorem halt_frozen_certified : HasCertifiedSolution dataClock_program frozenQuery 128 := by
  horn_certify

/-! ### The relation to TISE (time-independent Schrödinger = timeless = fixed point) -/

/-- A small data-driven permutation of `Fin 4`: the vacuum config `0` is fixed
(data-free), the data configs `1, 2, 3` are on a 3-cycle (the clock cycles). -/
def dataClockPerm : Fin 4 ≃ Fin 4 where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- **The data-free vacuum is a fixed point** — the transition computes nothing
there, so (`isPhysical_iff_fixed`) it lies in the timeless / TISE-stationary
sector. -/
theorem vacuum_fixed : dataClockPerm 0 = 0 := rfl

/-- **Timeless ⟹ constant on data.**  Any TISE-stationary amplitude
(`U_σ ψ = ψ`) takes the same value on every state of a data orbit: the clock
cannot resolve times within an orbit.  A state that distinguishes the data
configurations is therefore not stationary — it evolves, i.e. the clock ticks
precisely where the data is. -/
theorem timeless_constant_on_data {ψ : lp (fun _ : Fin 4 => ℂ) 2}
    (h : koopman dataClockPerm ψ = ψ) :
    (ψ : Fin 4 → ℂ) 1 = ψ 2 ∧ (ψ : Fin 4 → ℂ) 2 = ψ 3 := by
  refine ⟨?_, ?_⟩
  · have h2 := stationary_pointwise h 2
    rwa [show dataClockPerm.symm 2 = 1 from rfl] at h2
  · have h3 := stationary_pointwise h 3
    rwa [show dataClockPerm.symm 3 = 2 from rfl] at h3

end Physlib.QuantumMechanics.DataDrivenClockAutomaton
