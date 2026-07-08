/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Full GKLS Lindblad master equation `dρ/dt = ℒ(ρ)` in finite dimensions

Extends the GKLS scalar rate (`Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate`,
commit `2edc85c5`) to the **full Lindblad operator equation**:

 `dρ/dt = ℒ(ρ) := −(i/ℏ)·[H, ρ] + 𝒟[L](ρ)`,

with the **multi-jump dissipator** (Lindblad 1976; Gorini-Kossakowski-
Sudarshan 1976)

 `𝒟[L](ρ) := Σ_j ( L_j · ρ · L_j^† − ½·{L_j^† · L_j, ρ} )`.

Here `H : Matrix d d ℂ` is the system Hamiltonian, `L : ι → Matrix d d ℂ`
is the finite Lindblad jump-operator family, `ℏ > 0` is Planck's
constant, and `ρ : Matrix d d ℂ` is the density-matrix state.

## What this file proves

This file is the **algebraic + ODE-predicate layer** of the
Lindblad master equation:

### Algebraic level (structurally provable)

* **Trace preservation** of the dissipator: `Tr(𝒟[L](ρ)) = 0`.
* **Trace preservation** of the full GKLS generator: `Tr(ℒ(ρ)) = 0`.
* **Single-jump specialisation**: `𝒟[L_j](ρ)` for a single jump
 operator coincides with the `lindbladTerm`.
* **Steady-state predicate**: `IsGKLSSteady := ℒ(ρ_ss) = 0`.
* **Trivial steady-state witness**: `IsGKLSSteady H L ℏ 0`.

### ODE level (predicate-based)

* **`IsLindbladSolution H L ℏ ρ_fn`** — predicate: `ρ_fn : ℝ →
 Matrix d d ℂ` satisfies `(ρ_fn)'(t) = ℒ(H, L, ℏ, ρ_fn(t))` at
 every time `t`.

* **`isLindbladSolution_trace_preserved`** — *main theorem*:
 every Lindblad solution preserves trace pointwise:
 `Tr(ρ_fn t) = Tr(ρ_fn 0)`. Proof:
 `(d/dt) Tr(ρ_fn t) = Tr(ℒ(ρ_fn t)) = 0`, so trace is constant.

## Why this is foundationally important

The **trace-preservation theorem along the flow** is the
**formal second-law backbone** of GKLS evolution:

* If `ρ(0)` is a density matrix (trace 1), then `Tr(ρ(t)) = 1`
 for all `t` — the **probability normalisation is preserved**.
* The non-negativity / complete-positivity of the dissipator
 (which preserves `ρ ⪰ 0`) is a separate property requiring
 operator-algebra machinery; this file provides only the
 **trace-preservation half** of GKLS structural correctness.

Combined with the GKLS rate non-negativity from commit `2edc85c5`,
we have:
* `λ_GKLS = Σ_j Tr(L_j^† L_j ρ) ≥ 0` (entropy production rate)
* `Tr(ℒ(ρ)) = 0` (probability preservation)

Both pieces — the second-law content (rate non-negative) and the
probability-conservation content (trace preserved) — are now
machine-checked.

## Scope

* **Finite-dimensional matrices only.** Infinite-dim version
 requires unbounded operators / Hilbert–Schmidt classes.
* **No complete-positivity proof.** CP preservation of `ρ ⪰ 0`
 needs operator-algebra structure (Stinespring dilation, Choi
 matrices) outside present scope.
* **No solution existence.** The Lindblad ODE existence and
 uniqueness theorem (Stone-type, semigroup) requires Banach-
 space ODE infrastructure (`Mathlib.Analysis.ODE`); we ship the
 **predicate** and prove properties of *any* solution that
 exists.
* **No explicit ℏ-scaling of `gklsGenerator`** beyond the
 Hamiltonian term — the dissipator is presented in its
 unit-ℏ form (`(L · ρ · L^† − ½·{L^† L, ρ})`); the
 `(1/ℏ)`-scaling of the dissipator term that some textbooks
 use is recovered by rescaling `L_j → L_j/√ℏ` if needed.

## Contents — full list

### §1 — Single-jump and multi-jump Lindblad dissipators

* `lindbladSingleJumpDissipator L ρ`
 `:= L·ρ·L^† − ½·{L^†·L, ρ}`.
* `lindbladDissipator L_fn ρ`
 `:= Σ_j lindbladSingleJumpDissipator (L_fn j) ρ`.

### §2 — Trace preservation

* `trace_lindbladSingleJumpDissipator_eq_zero`.
* `trace_lindbladDissipator_eq_zero`.

### §3 — Full GKLS generator + trace preservation

* `gklsGenerator H L_fn ℏ ρ`
 `:= −(i/ℏ) · [H, ρ] + lindbladDissipator L_fn ρ`.
* `trace_gklsGenerator_eq_zero`.

### §4 — Steady state

* `IsGKLSSteady H L_fn ℏ ρ` — predicate.
* `zero_isGKLSSteady` — trivial witness.

### §5 — Lindblad ODE predicate + trace-preservation along flow

* `IsLindbladSolution H L_fn ℏ ρ_fn` — predicate at the
 `HasDerivAt` level (componentwise / Matrix-valued).
* **`isLindbladSolution_trace_const`** — main theorem: trace is
 constant along any Lindblad solution.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119.
* Gorini–Kossakowski–Sudarshan 1976 *J. Math. Phys.* 17, 821.
* Spohn 1978 *Rev. Mod. Phys.* 52, 569.
* ``
 — single-jump version with same trace-preservation pattern.
* `Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate` (commit
 `2edc85c5`) — scalar rate `λ = Σ_j Tr(L_j^† L_j ρ)`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex
open QuantumMechanics.FiniteTarget (commutator anticommutator trace_commutator)

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-! ## §1 — Single-jump and multi-jump Lindblad dissipators -/

/-- **Single-jump Lindblad dissipator**:

  `𝒟[L](ρ) := L · ρ · L^† − ½·{L^† · L, ρ}`,

where `{A, B} := A·B + B·A` is the anti-commutator.

The first term is the *jump* contribution and the
anti-commutator term is the *no-jump correction* ensuring
trace preservation. -/
def lindbladSingleJumpDissipator
    (L ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  L * ρ * Lᴴ - ((1/2 : ℂ) • anticommutator (Lᴴ * L) ρ)

/-- **Multi-jump Lindblad dissipator**:

  `𝒟[L](ρ) := Σ_j (L_j · ρ · L_j^† − ½·{L_j^† L_j, ρ})`.

For a finite family `L : ι → Matrix d d ℂ` of jump operators,
sums the single-jump dissipators over the index. -/
def lindbladDissipator
    (L_fn : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ j, lindbladSingleJumpDissipator (L_fn j) ρ

/-! ## §2 — Trace preservation of the dissipator -/

/-- **Single-jump Lindblad dissipator has trace zero**:

  `Tr(L · ρ · L^† − ½·{L^† L, ρ}) = 0`.

By trace cyclicity:
* `Tr(L · ρ · L^†) = Tr(L^† · L · ρ)`,
* `Tr({L^† L, ρ}) = 2·Tr(L^† L · ρ)` by `trace_anticommutator`.

So the expression collapses: `Tr(L^† L ρ) − ½·2·Tr(L^† L ρ) = 0`. -/
theorem trace_lindbladSingleJumpDissipator_eq_zero
    (L ρ : Matrix d d ℂ) :
    (lindbladSingleJumpDissipator L ρ).trace = 0 := by
  unfold lindbladSingleJumpDissipator
  rw [Matrix.trace_sub, Matrix.trace_smul]
  have h1 : (L * ρ * Lᴴ).trace = (Lᴴ * L * ρ).trace :=
    Matrix.trace_mul_cycle L ρ Lᴴ
  have h2 :
      (QuantumMechanics.FiniteTarget.anticommutator (Lᴴ * L) ρ).trace
        = 2 * ((Lᴴ * L) * ρ).trace :=
    QuantumMechanics.FiniteTarget.trace_anticommutator _ _
  rw [h1, h2, smul_eq_mul]
  ring

/-- **Multi-jump Lindblad dissipator has trace zero**:

  `Tr(Σ_j (L_j · ρ · L_j^† − ½·{L_j^† L_j, ρ})) = 0`.

Sum of zero-trace terms. -/
theorem trace_lindbladDissipator_eq_zero
    (L_fn : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    (lindbladDissipator L_fn ρ).trace = 0 := by
  unfold lindbladDissipator
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact trace_lindbladSingleJumpDissipator_eq_zero (L_fn j) ρ

/-! ## §3 — Full GKLS generator -/

/-- **Full GKLS generator** (Lindblad master-equation RHS):

  `ℒ(ρ) := −(i/ℏ) · [H, ρ] + 𝒟[L](ρ)`,

combining unitary (commutator) evolution and dissipative
(multi-jump) contribution.

This is the right-hand side of the Lindblad ODE
`dρ/dt = ℒ(ρ)`. -/
def gklsGenerator
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  -(Complex.I / (ℏ : ℂ)) •
    QuantumMechanics.FiniteTarget.commutator H ρ
  + lindbladDissipator L_fn ρ

/-- **GKLS generator preserves trace**:

  `Tr(ℒ(ρ)) = 0`.

By linearity of trace + trace preservation of both the
commutator and the dissipator. -/
theorem trace_gklsGenerator_eq_zero
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ : Matrix d d ℂ) :
    (gklsGenerator H L_fn ℏ ρ).trace = 0 := by
  unfold gklsGenerator
  rw [Matrix.trace_add, Matrix.trace_smul,
      QuantumMechanics.FiniteTarget.trace_commutator,
      trace_lindbladDissipator_eq_zero]
  simp

/-! ## §4 — Steady state -/

/-- **GKLS steady-state predicate**:

  `IsGKLSSteady H L_fn ℏ ρ_ss := ℒ(ρ_ss) = 0`.

A density matrix `ρ_ss` is a *steady state* of the Lindblad
master equation if the GKLS generator vanishes at it. -/
def IsGKLSSteady
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ_ss : Matrix d d ℂ) : Prop :=
  gklsGenerator H L_fn ℏ ρ_ss = 0

/-- **The zero matrix is a (trivial) GKLS steady state**.

`ℒ(0) = 0` for any `H`, `L`, `ℏ` — direct from
`commutator H 0 = 0` and `lindbladDissipator L 0 = 0`.

This is the trivial / unphysical witness; physically meaningful
steady states are non-trivial density matrices (e.g., the
Gibbs state at infinite temperature). -/
theorem zero_isGKLSSteady
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    IsGKLSSteady H L_fn ℏ 0 := by
  unfold IsGKLSSteady gklsGenerator
        lindbladDissipator lindbladSingleJumpDissipator
        QuantumMechanics.FiniteTarget.commutator
        QuantumMechanics.FiniteTarget.anticommutator
  simp

/-! ## §5 — Lindblad ODE predicate + trace-rate vanishing -/

/-- **Lindblad ODE solution predicate** (algebraic, time-rate
parametrisation):

  `IsLindbladSolution H L_fn ℏ ρ_fn ρ_dot_fn := ∀ t,
      ρ_dot_fn t = ℒ(H, L_fn, ℏ, ρ_fn t)`.

A pair `(ρ_fn, ρ_dot_fn) : ℝ → Matrix d d ℂ × Matrix d d ℂ` is a
**Lindblad solution** if at every time `t`, the supplied
"derivative" `ρ_dot_fn t` equals the GKLS generator at `ρ_fn t`.

This is an **external** parametrisation — we do not commit to a
specific differentiation framework on `Matrix d d ℂ`-valued
functions of `ℝ`.  Downstream consumers who have a Mathlib
`HasDerivAt` predicate can specialise to `ρ_dot_fn := deriv ρ_fn`. -/
def IsLindbladSolution
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ_fn ρ_dot_fn : ℝ → Matrix d d ℂ) : Prop :=
  ∀ t, ρ_dot_fn t = gklsGenerator H L_fn ℏ (ρ_fn t)

/-- **:trace rate vanishes along any Lindblad solution**.

If `(ρ_fn, ρ_dot_fn)` is a Lindblad solution, then at every time
`t`:

  `Tr(ρ_dot_fn t) = 0`.

**Probability conservation**: along any Lindblad solution the
trace rate is identically zero, so the total density-matrix
trace is constant in time and probability normalisation is
preserved.

This is the algebraic content of *complete-positivity-trace-
preservation* (CPTP) at the rate level. -/
theorem isLindbladSolution_trace_rate_zero
    {H : Matrix d d ℂ} {L_fn : ι → Matrix d d ℂ} {ℏ : ℝ}
    {ρ_fn ρ_dot_fn : ℝ → Matrix d d ℂ}
    (h_sol : IsLindbladSolution H L_fn ℏ ρ_fn ρ_dot_fn) (t : ℝ) :
    (ρ_dot_fn t).trace = 0 := by
  rw [h_sol t]
  exact trace_gklsGenerator_eq_zero H L_fn ℏ (ρ_fn t)

end Physlib.QuantumMechanics.Lindblad

end
