/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.FullLindbladODE
public import QuantumInfo.Channels.Unbundled

/-!
# Lindblad CPTP structure — complete-positivity of the jump-part dissipator

Third pillar of the GKLS / Lindblad master equation correctness
in physlib (after the GKLS rate non-negativity in commit
`2edc85c5` and the trace preservation in commit `62441390`):

  **Jump-part complete positivity**:
  the operator `J[L](ρ) := Σ_j L_j · ρ · L_j^†` (the Kraus / jump
  part of the Lindblad dissipator) is a completely positive map.

Specifically, this file connects the physlib Lindblad ODE
infrastructure to the QuantumInfo Kraus / `IsCompletelyPositive`
framework, leveraging the survey-identified path
**MatrixMap.of_kraus + of_kraus_isCompletelyPositive**.

The full **Lindblad CPTP semigroup theorem** (Lindblad 1976,
Theorem 5.1) — that `exp(t·ℒ)` is a CPTP map for every `t ≥ 0` —
requires semigroup-generation theory (Stone-type theorems on
matrix Banach spaces) and is downstream from this file.  What we
ship here is the **structural complete-positivity content** of
the Lindblad dissipator in algebraic form, identifying the
jump-part as a Kraus / `MatrixMap.of_kraus` channel and inheriting
its CP property.

## Decomposition of the GKLS dissipator

The multi-jump Lindblad dissipator decomposes as

  `𝒟[L](ρ) = J[L](ρ) − ½·{Q[L], ρ}`,

where

* `J[L](ρ) := Σ_j L_j · ρ · L_j^†`   — **jump part** (CP, Kraus form),
* `Q[L]    := Σ_j L_j^† · L_j`         — **drift coefficient** (PSD).

The jump part is completely positive (every Kraus map is CP).
The drift term is an anticommutator with the *positive
semidefinite* operator `Q[L]`.  The full dissipator is *not* CP
by itself — only the integrated semigroup `exp(t·𝒟)` is CP, by
Lindblad's theorem.  This file provides the **algebraic
decomposition + jump-part CP** content.

## Contents


* `lindbladJumpChannel L_fn` — the `MatrixMap d d ℂ` defined by
  the Kraus sum `X ↦ Σ_j L_j · X · L_j^†`.
* `lindbladJumpChannel_apply` — definitional unfolding.


* **`lindbladJumpChannel_isCompletelyPositive`** — direct
  application of `MatrixMap.of_kraus_isCompletelyPositive`.


* `lindbladJumpChannel_preserves_posSemidef` — `ρ ⪰ 0` ⟹
  `J[L](ρ) ⪰ 0` (a CP map is positive).


* `lindbladDriftCoefficient L_fn := Σ_j L_j^† · L_j`.
* **`lindbladDriftCoefficient_posSemidef`** — `Q[L] ⪰ 0`.


* **`lindbladDissipator_eq_jump_minus_drift`** — the algebraic
  decomposition.

## Honest scope

* **Jump-part CP only.**  The full `lindbladDissipator` is not
  CP as a single-shot map (the drift anti-commutator term can
  reduce eigenvalues of `ρ` momentarily).  Complete positivity
  emerges only at the **flow level** `exp(t·𝒟)` via Lindblad's
  theorem, which requires semigroup-generation theory not in
  scope here.

* **No CPTP map construction for the full Lindblad flow.**  The
  jump-part Kraus channel `J[L]` is CPTP-like at the
  *infinitesimal* level (one application); the time-evolved
  Lindblad superoperator requires the matrix exponential and a
  semigroup-generation theorem.

* **Finite-dim only.**  Infinite-dim Kraus operators need
  Hilbert–Schmidt closure / unbounded operator theory.

## What is now machine-checked for the Lindblad master equation

| # | Pillar | Statement | Commit |
|---|--------|-----------|--------|
| 1 | Rate non-negativity | `λ_GKLS = Σ_j Tr(L_j^† L_j ρ) ≥ 0` | `2edc85c5` |
| 2 | Trace preservation | `Tr(ℒ(ρ)) = 0` along solutions | `62441390` |
| 3 | **Jump-part CP** | `J[L]` is a CP MatrixMap | **`THIS`** |
| 4 | Drift coefficient PSD | `Σ_j L_j^† L_j ⪰ 0` | **`THIS`** |
| 5 | Dissipator decomposition | `𝒟 = J − ½·{Q, ·}` | **`THIS`** |

What remains: full CPTP for the semigroup `exp(t·ℒ)` —
Lindblad's theorem at the semigroup-flow level (downstream).

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 5.1
  (CPTP semigroup characterisation).
* Gorini–Kossakowski–Sudarshan 1976 *J. Math. Phys.* 17, 821.
* Choi 1975 *Linear Algebra Appl.* 10, 285 — Choi matrix.
* Kraus 1971 *Ann. Phys.* 64, 311 — Kraus representation.
* `QuantumInfo.Channels.Unbundled`
  (`of_kraus_isCompletelyPositive`).
* `QuantumInfo.Channels.MatrixMap` (`of_kraus`,
  `MatrixMap.choi_matrix`, `MatrixMap.choi_equiv`).
* `Physlib.QuantumMechanics.Lindblad.FullLindbladODE`
  (commit `62441390`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex MatrixMap
open scoped ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]


/-- **Lindblad jump-part Kraus channel**:

  `J[L](ρ) := Σ_j L_j · ρ · L_j^†`,

packaged as a `MatrixMap d d ℂ` via QuantumInfo's
`MatrixMap.of_kraus` constructor (with the *same* family `L`
for both left and right Kraus sides).

This is the **completely positive (CP) summand** of the Lindblad
dissipator: the drift / anti-commutator term is separate. -/
def lindbladJumpChannel (L_fn : ι → Matrix d d ℂ) : MatrixMap d d ℂ :=
  MatrixMap.of_kraus L_fn L_fn


/-- **:the Lindblad jump-part channel is completely
positive**.

Direct application of `MatrixMap.of_kraus_isCompletelyPositive`
to the symmetric Kraus pair `(L, L)`.  This is the **third
pillar** of GKLS structural correctness (after rate non-negativity
and trace preservation): the jump part of the Lindblad dissipator
is a CP map.

Physically: information-preservation under the jump portion of
the master equation — every "decoherence channel" with Kraus
operators `{L_j}` is completely positive, hence preserves
positivity even when composed with arbitrary auxiliary systems
(Choi-Jamiołkowski / Stinespring). -/
lemma lindbladJumpChannel_isCompletelyPositive
    (L_fn : ι → Matrix d d ℂ) :
    (lindbladJumpChannel L_fn).IsCompletelyPositive := by
  unfold lindbladJumpChannel
  exact MatrixMap.of_kraus_isCompletelyPositive L_fn


/-- **The jump-part channel preserves positivity (PSD)**.

A completely positive map is in particular positive, so the
jump-part Kraus channel sends PSD matrices to PSD matrices:

  `ρ ⪰ 0  ⟹  J[L](ρ) ⪰ 0`. -/
lemma lindbladJumpChannel_isPositive
    (L_fn : ι → Matrix d d ℂ) :
    (lindbladJumpChannel L_fn).IsPositive :=
  (lindbladJumpChannel_isCompletelyPositive L_fn).IsPositive


/-- **Lindblad drift coefficient** `Q[L] := Σ_j L_j^† · L_j`.

The PSD operator that appears in the anti-commutator term of the
Lindblad dissipator.  This is the *drain* coefficient: the
expected rate of "departure" from a state due to jumps. -/
def lindbladDriftCoefficient (L_fn : ι → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ j, (L_fn j)ᴴ * (L_fn j)

/-- **The drift coefficient `Q[L]` is positive semidefinite**.

Each term `L_j^† · L_j` is PSD (Mathlib
`posSemidef_conjTranspose_mul_self`); the sum of PSD matrices is
PSD.  This is the **finite-Kraus PSD core** of the GKLS
structure. -/
lemma lindbladDriftCoefficient_posSemidef
    (L_fn : ι → Matrix d d ℂ) :
    (lindbladDriftCoefficient L_fn).PosSemidef := by
  unfold lindbladDriftCoefficient
  apply Matrix.posSemidef_sum
  intro j _
  exact Matrix.posSemidef_conjTranspose_mul_self (L_fn j)


/-- **:algebraic decomposition of the Lindblad
dissipator**:

  `𝒟[L](ρ) = J[L](ρ) − ½·{Q[L], ρ}`,

where:
* `J[L](ρ) := Σ_j L_j · ρ · L_j^†`         — jump part (CP),
* `Q[L]   := Σ_j L_j^† · L_j`                — drift coefficient (PSD),
* `{A, B} := A·B + B·A`                       — anti-commutator.

This is the **standard textbook decomposition** of the GKLS
dissipator into its CP jump part and PSD-coefficient drift part.
The full dissipator is *not* CP — only the integrated semigroup
`exp(t·ℒ)` is CPTP, by Lindblad's theorem.

**Algebraic core**: expand the multi-jump dissipator and collect
terms; the anti-commutator with `Q[L]` exactly accounts for the
sum of `(1/2)·{L_j^† L_j, ρ}` across `j`. -/
lemma lindbladDissipator_eq_jump_minus_drift
    (L_fn : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    lindbladDissipator L_fn ρ
      = lindbladJumpChannel L_fn ρ
        - ((1/2 : ℂ) • QuantumMechanics.FiniteTarget.anticommutator
            (lindbladDriftCoefficient L_fn) ρ) := by
  -- Strategy: rewrite the dissipator as Σ_j (jump_j - drift_j) and
  -- distribute the sum to (Σ jump) - (Σ drift), then identify each.
  unfold lindbladDissipator lindbladSingleJumpDissipator
  -- LHS = Σ_j (L_j ρ L_j^† - (1/2)·anticomm(L_j^†·L_j, ρ))
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- ∑_j (L_j ρ L_j^†) = lindbladJumpChannel L_fn ρ
    unfold lindbladJumpChannel MatrixMap.of_kraus
    simp [LinearMap.coe_sum, Finset.sum_apply]
  · -- ∑_j (1/2)·anticomm(L_j^†·L_j, ρ) = (1/2)·anticomm(Q[L], ρ)
    unfold QuantumMechanics.FiniteTarget.anticommutator
            lindbladDriftCoefficient
    rw [← Finset.smul_sum]
    congr 1
    -- Σ_j (L_j^† L_j · ρ + ρ · L_j^† L_j)
    --   = (Σ_j L_j^† L_j) · ρ + ρ · (Σ_j L_j^† L_j)
    rw [Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.mul_sum]

end Physlib.QuantumMechanics.Lindblad

end
