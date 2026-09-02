/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.LindbladCPTP
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Lindblad 1976 CP-semigroup: integrated CPTP flow `Φ_t = exp(t·ℒ)`

Formalisation of the key direction of **Lindblad 1976, Theorem 1**
(*Commun. Math. Phys.* 48, 119, ref source PDF
`semigroups-lindblad-1976-1103899849.pdf`):

> Let `L` be a bounded `*`-map `𝒜 → 𝒜` and `Φ_t = exp(tL)`.
> Then `Φ_t ∈ CP(𝒜)` and `Φ_t(I) = I` iff `L ∈ CD(𝒜)`.

In finite-dimensional matrix algebras, this is the **CPTP
semigroup theorem**: for a GKLS / Lindblad generator
`ℒ(ρ) = −(i/ℏ)·[H, ρ] + 𝒟[L](ρ)`, the time-evolved
superoperator `Φ_t := exp(t·ℒ)` is a CPTP map for every `t ≥ 0`.

## Strategy of the proof

Lindblad's original proof (page 125 of the PDF) uses

* the Kadison-Schwarz inequality `Φ(X^†)·Φ(I)^{−1}·Φ(X) ≤ Φ(X^†X)`,
* differentiation at `t = 0`,
* the dissipation function `D(L; X, Y) := L(X^†Y) − L(X^†)·Y − X^†·L(Y) ≥ 0`,
* and the *Lie-Trotter product formula* `exp[t(L + L')] = lim_n [exp(tL/n)·exp(tL'/n)]^n`.

The finite-dimensional special case (this file) uses a
**three-piece Trotter decomposition** of the GKLS generator:

  `ℒ = ℒ_H + ℒ_J + ℒ_K`,

where

* **`ℒ_H(ρ) := −(i/ℏ)·[H, ρ]`** — Hamiltonian unitary generator,
* **`ℒ_J(ρ) := Σ_j L_j · ρ · L_j^†`** — multi-jump Kraus generator,
* **`ℒ_K(ρ) := −(1/2)·{Q[L], ρ}`** — drift anti-commutator generator.

For each individual piece, the **integrated flow is CP**:

* `exp(t·ℒ_H)(ρ) = U(t)·ρ·U(t)^†` with `U(t) := exp(−i·t·H/ℏ)`
  — unitary conjugation, single-Kraus form, CP.
* `exp(t·ℒ_K)(ρ) = exp(−t·Q[L]/2)·ρ·exp(−t·Q[L]/2)^†`
  (`Q[L]` Hermitian PSD) — exponential of PSD, single-Kraus form, CP.

The Lie-Trotter limit assembles these into the full GKLS flow,
which inherits CP from finite-dim CP closure under composition
and operator-norm limits.

## Contents


* `hamiltonianFlow t H ℏ ρ := exp(−i·t·H/ℏ)·ρ·exp(i·t·H/ℏ)`.
* `hamiltonianFlowChannel t H ℏ` — packaged as a `MatrixMap`.
* **`hamiltonianFlowChannel_isCompletelyPositive`** —
  unitary conjugation is CP (single-Kraus).


* `driftFlow t L_fn ρ := exp(−t·Q[L]/2)·ρ·exp(−t·Q[L]/2)^†`.
* `driftFlowChannel t L_fn` — packaged as a `MatrixMap`.
* **`driftFlowChannel_isCompletelyPositive`** — single-Kraus
  conjugation by Hermitian operator is CP.


* `hamiltonianDriftFlowChannel t H L_fn ℏ`
  `:= driftFlowChannel t L_fn ∘ hamiltonianFlowChannel t H ℏ`.
* **`hamiltonianDriftFlowChannel_isCompletelyPositive`** —
  composition of two CP maps is CP.

## Honest scope

This file provides the **CP content of two of the three Lindblad
pieces** and proves their composition is CP — corresponding to the
**Trotter approximant level** of the full theorem.

What is NOT shipped:

* The full integrated `exp(t·ℒ)` for the multi-jump dissipator
  including the Kraus-form `Σ_j L_j ρ L_j^†` term.  The jump
  generator's exponential is the harder piece:
  `exp(t·ℒ_J)(ρ) = Σ_k (t^k/k!) · J^k(ρ)` where each `J^k` is CP
  (composition closure) and the positive-coefficient series is CP
  (finset-sum closure).  Formalising this requires the
  infinite-sum closure of `IsCompletelyPositive` under series
  convergence — beyond the bounded sum already in
  `IsCompletelyPositive.add` / `.finset_sum`.

* The **Lie-Trotter product limit**, which combines the three
  Trotter pieces into `exp(t·ℒ)`.  Available in Mathlib via
  `NormedSpace.exp_add_of_commute` for commuting generators, but
  the non-commuting Trotter formula requires substantially more
  machinery.

* The **converse direction** of Lindblad Theorem 1: that if a CP
  semigroup is given, its generator must be in Lindblad form (CD).
  This direction uses Stinespring dilation + differentiation of
  the Kadison-Schwarz inequality.

What IS established by this file together with the prior commits:

| Property | Content | Status |
|----------|---------|--------|
| Rate non-negativity | `λ_GKLS ≥ 0` | `2edc85c5` |
| Trace preservation | `Tr(ℒ(ρ)) = 0` | `62441390` |
| Jump-part CP | `J[L]` is CP MatrixMap | `48ddc88d` |
| Drift coefficient PSD | `Q[L] ⪰ 0` | `48ddc88d` |
| Dissipator decomposition | `𝒟 = J − ½·{Q, ·}` | `48ddc88d` |
| **Hamiltonian flow CP** | `exp(t·ℒ_H)` is CP | **THIS** |
| **Drift flow CP** | `exp(t·ℒ_K)` is CP | **THIS** |
| **Hamiltonian∘Drift CP** | composition CP | **THIS** |

The remaining piece — **full multi-jump exponential** — is the
analytic content (matrix exponential series + CP series closure)
left for downstream.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1.
* Trotter 1959 *Proc. AMS* 10, 545 — Trotter product formula.
* `Mathlib.Analysis.Normed.Algebra.MatrixExponential` —
  `Matrix.exp`, `exp_conjTranspose`, `IsHermitian.exp`.
* `QuantumInfo.Channels.MatrixMap.of_kraus`,
  `of_kraus_isCompletelyPositive`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex MatrixMap NormedSpace
open scoped ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]


/-- **Hamiltonian unitary** at time `t`: `U(t) := exp(−i·t·H/ℏ)`.

The integrated Hamiltonian semigroup element.  Hermitian
conjugate is `U(t)^† = exp(+i·t·H/ℏ)` (when `H` is Hermitian).

This is the **Schrödinger-picture evolution operator** in
operator form. -/
def hamiltonianUnitary (t : ℝ) (H : Matrix d d ℂ) (ℏ : ℝ) : Matrix d d ℂ :=
  NormedSpace.exp (((-Complex.I) * ((t : ℂ) / (ℏ : ℂ))) • H)

/-- **Hamiltonian unitary conjugation flow**:

  `Φ_t^H(ρ) := U(t) · ρ · U(t)^†`,

the integrated `exp(t·ℒ_H)` where `ℒ_H(ρ) = −(i/ℏ)·[H, ρ]`.

Packaged as a `MatrixMap d d ℂ` (a `ℂ`-linear endomorphism on
matrices) for use with the QuantumInfo CP framework. -/
def hamiltonianFlowChannel (t : ℝ) (H : Matrix d d ℂ) (ℏ : ℝ) :
    MatrixMap d d ℂ :=
  MatrixMap.of_kraus
    (fun _ : Fin 1 => hamiltonianUnitary t H ℏ)
    (fun _ : Fin 1 => hamiltonianUnitary t H ℏ)

/-- **:the Hamiltonian unitary flow is completely
positive**.

`Φ_t^H(ρ) = U(t) · ρ · U(t)^†` is in single-Kraus form, so it is
CP by `MatrixMap.of_kraus_isCompletelyPositive` (with `κ = Fin 1`).

This is the **Lindblad theorem specialised to the Hamiltonian-
only generator** `ℒ_H(ρ) = −(i/ℏ)·[H, ρ]`: unitary conjugation
is CP for every `t ∈ ℝ`. -/
lemma hamiltonianFlowChannel_isCompletelyPositive
    (t : ℝ) (H : Matrix d d ℂ) (ℏ : ℝ) :
    (hamiltonianFlowChannel t H ℏ).IsCompletelyPositive := by
  unfold hamiltonianFlowChannel
  exact MatrixMap.of_kraus_isCompletelyPositive _


/-- **Drift damping operator** at time `t`:

  `D(t) := exp(−t · Q[L] / 2)`,

with `Q[L] := Σ_j L_j^† · L_j` the (PSD) drift coefficient.

Since `Q[L]` is Hermitian PSD, its exponential is Hermitian PSD,
and `D(t)` is Hermitian with operator norm ≤ 1.  This is the
**single-Kraus damping operator** for the anticommutator
generator `ℒ_K(ρ) = −(1/2)·{Q[L], ρ}`. -/
def driftDampingOperator (t : ℝ) (L_fn : ι → Matrix d d ℂ) :
    Matrix d d ℂ :=
  NormedSpace.exp ((-((t : ℂ) / 2)) • lindbladDriftCoefficient L_fn)

/-- **Drift damping flow** (single-Kraus):

  `Φ_t^K(ρ) := D(t) · ρ · D(t)^†`,

the integrated `exp(t·ℒ_K)` for the anticommutator generator
`ℒ_K(ρ) = −(1/2)·{Q[L], ρ}`.

Specialised to the Hermitian-PSD case where `D(t)` is Hermitian,
this is the **symmetric damping** form of the drift evolution. -/
def driftFlowChannel (t : ℝ) (L_fn : ι → Matrix d d ℂ) :
    MatrixMap d d ℂ :=
  MatrixMap.of_kraus
    (fun _ : Fin 1 => driftDampingOperator t L_fn)
    (fun _ : Fin 1 => driftDampingOperator t L_fn)

/-- **:the drift damping flow is completely positive**.

`Φ_t^K(ρ) = D(t) · ρ · D(t)^†` is in single-Kraus form, so it is
CP by `MatrixMap.of_kraus_isCompletelyPositive`.

This is the **Lindblad theorem specialised to the drift-only
anticommutator generator** `ℒ_K(ρ) = −(1/2)·{Q[L], ρ}`:
exponential damping by a PSD coefficient is CP for every `t ∈ ℝ`. -/
lemma driftFlowChannel_isCompletelyPositive
    (t : ℝ) (L_fn : ι → Matrix d d ℂ) :
    (driftFlowChannel t L_fn).IsCompletelyPositive := by
  unfold driftFlowChannel
  exact MatrixMap.of_kraus_isCompletelyPositive _


/-- **Hamiltonian-then-drift Trotter approximant** at time `t`:

  `Φ_t^{HK} := Φ_t^K ∘ Φ_t^H`.

This is the **first-order Lie-Trotter approximation** to the
combined Hamiltonian + drift flow `exp(t·(ℒ_H + ℒ_K))`.  The full
Lindblad flow `exp(t·ℒ)` adds the multi-jump term and is
obtained via the higher-order Trotter limit. -/
def hamiltonianDriftFlowChannel
    (t : ℝ) (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    MatrixMap d d ℂ :=
  LinearMap.comp (driftFlowChannel t L_fn) (hamiltonianFlowChannel t H ℏ)

/-- **The Hamiltonian-drift Trotter approximant is completely
positive**.

Composition of CP maps is CP (Lindblad 1976 Remark 3 page 122 /
`QuantumInfo.Channels.IsCompletelyPositive.comp`).  Both pieces
are individually CP (`hamiltonianFlowChannel_isCompletelyPositive`,
`driftFlowChannel_isCompletelyPositive`).

This establishes the **CP property of the Trotter-approximant
flow** — the load-bearing structural step toward the full Lindblad
CP-semigroup theorem.  The remaining steps (multi-jump
exponentiation + Trotter limit) are downstream. -/
lemma hamiltonianDriftFlowChannel_isCompletelyPositive
    (t : ℝ) (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    (hamiltonianDriftFlowChannel t H L_fn ℏ).IsCompletelyPositive := by
  have h_H : (hamiltonianFlowChannel t H ℏ).IsCompletelyPositive :=
    hamiltonianFlowChannel_isCompletelyPositive t H ℏ
  have h_K : (driftFlowChannel t L_fn).IsCompletelyPositive :=
    driftFlowChannel_isCompletelyPositive t L_fn
  unfold hamiltonianDriftFlowChannel
  exact MatrixMap.IsCompletelyPositive.comp h_H h_K

end Physlib.QuantumMechanics.Lindblad

end
