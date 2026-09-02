/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import QuantumInfo.Channels.CPTP

/-!
# CPTP-proper Quantum Inertial Frame semigroup

The abstract `QIFSemigroup` (§7 of
`QuantumInertialFrame.lean`) carries a one-parameter family
`Φ : ℝ → MState d → MState d` with identity at `0` and the
composition law `Φ (τ₁+τ₂) ρ = Φ τ₁ (Φ τ₂ ρ)`, but does **not**
enforce complete positivity or trace preservation of each `Φ_τ` as
a *map* inside Lean: only the codomain `MState d` carries
positivity (per state).

This module promotes the carrier to use Meiburg's
`QuantumInfo.Channels.CPTP.CPTPMap d d ℂ` instead — a structure that
*does* carry complete positivity and trace preservation at the
type level via Choi-PSD + trace-1 fields.  Each `Φ τ : CPTPMap d d`
is then a fully verified CPTP map, not just a state-to-state
function that happens to land in `MState`.

## Carrier

`QIFSemigroupCPTP d` — `Φ : ℝ → CPTPMap d d ℂ` with the
semigroup laws encoded via `CPTPMap.id` and `CPTPMap.compose`
(infix `∘ₘ`).

## Bridges

* `QIFSemigroupCPTP.trivial` — `Φ_τ := CPTPMap.id` for all `τ`.
* `QIFSemigroupCPTP.toAbstract` — the abstract `QIFSemigroup`
  induced by application of the CPTP family to states.  The
  semigroup laws on the abstract side are *derived* from the CPTP
  semigroup laws via `CPTPMap.compose_eq`.

## What this resolves

The earlier earlier status note after an earlier version said:

> Not a CPTP-properness check: `QIFSemigroup` doesn't enforce complete
> positivity inside Lean — `MState` carries trace-1 positivity, but the
> CPTP property of `Φ_τ` as a *map* requires more machinery.

This module supplies that machinery by routing through
`CPTPMap d d ℂ`.

## References

* Lindblad 1976, Gorini-Kossakowski-Sudarshan 1976 — CPTP semigroups.
* Stinespring 1955 — completely positive maps on operator algebras.
* Meiburg, `Lean-QuantumInfo` — `CPTPMap d d ℂ` carrier with
  `CPTPMap.id`, `CPTPMap.compose` (`∘ₘ`), `compose_assoc`,
  `id_compose`, `compose_id`, `compose_eq`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open QuantumInfo.Finite

namespace QuantumMechanics.FiniteTarget


/-- A **CPTP-proper QIF semigroup** is a one-parameter family of
`CPTPMap d d ℂ` maps with identity at `τ = 0` and the semigroup
composition law `Φ (τ₁ + τ₂) = Φ τ₁ ∘ₘ Φ τ₂`.

Unlike the abstract `QIFSemigroup` carrier (which lives at the
`MState → MState` level and only enforces positivity through the
codomain), this structure enforces complete positivity and trace
preservation **as map-level properties** via Mathlib /
Lean-QuantumInfo's `CPTPMap`.

Physically: the paper's `Φ_τ` (Eq. `qrf_semigroup_tau`)
*is* a CPTP semigroup; this carrier records that fact at the
type level. -/
structure QIFSemigroupCPTP (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The CPTP-channel family `τ ↦ Φ_τ`. -/
  Φ          : ℝ → CPTPMap d d ℂ
  /-- Identity at `τ = 0`. -/
  Φ_zero     : Φ 0 = CPTPMap.id
  /-- Semigroup composition (via `CPTPMap.compose`, infix `∘ₘ`). -/
  Φ_compose  : ∀ τ₁ τ₂ : ℝ, Φ (τ₁ + τ₂) = Φ τ₁ ∘ₘ Φ τ₂

namespace QIFSemigroupCPTP

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Composition is commutative under parameter addition**: time
parameters commute, so `Φ τ₁ ∘ₘ Φ τ₂ = Φ τ₂ ∘ₘ Φ τ₁`. -/
lemma Φ_compose_comm (S : QIFSemigroupCPTP d) (τ₁ τ₂ : ℝ) :
    S.Φ τ₁ ∘ₘ S.Φ τ₂ = S.Φ τ₂ ∘ₘ S.Φ τ₁ := by
  rw [← S.Φ_compose, add_comm, S.Φ_compose]

/-- **Three-step composition**:
`Φ ((τ₁+τ₂)+τ₃) = Φ τ₁ ∘ₘ Φ τ₂ ∘ₘ Φ τ₃`
(using the left-associative `∘ₘ`, which matches the left-associative
real-number addition under the standard convention). -/
lemma Φ_compose_three (S : QIFSemigroupCPTP d) (τ₁ τ₂ τ₃ : ℝ) :
    S.Φ ((τ₁ + τ₂) + τ₃) = S.Φ τ₁ ∘ₘ S.Φ τ₂ ∘ₘ S.Φ τ₃ := by
  rw [S.Φ_compose, S.Φ_compose]


/-- The **trivial CPTP semigroup**: `Φ_τ := CPTPMap.id` for all `τ`.

Models the equilibrium-QIF reduction at the CPTP level: when the
QIF is at equilibrium for every state, the reduced dynamics is the
identity channel at every time. -/
def trivial (d : Type*) [Fintype d] [DecidableEq d] : QIFSemigroupCPTP d where
  Φ          := fun _ => CPTPMap.id
  Φ_zero     := rfl
  Φ_compose  := fun _ _ => (CPTPMap.id_compose CPTPMap.id).symm

/-- The trivial CPTP semigroup's `Φ_τ` equals `CPTPMap.id` for every
`τ`. -/
@[simp] lemma trivial_Φ (τ : ℝ) :
    (trivial d).Φ τ = CPTPMap.id := rfl

/-- The trivial CPTP semigroup acts as the identity on states at every
`τ`. -/
@[simp] lemma trivial_apply (τ : ℝ) (ρ : MState d) :
    (trivial d).Φ τ ρ = ρ := by
  rw [trivial_Φ]
  exact CPTPMap.id_MState ρ


/-- **CPTP-proper semigroup induces the abstract `QIFSemigroup`**.

Apply each `Φ τ : CPTPMap d d` to a state to get the
`MState → MState` action; the abstract semigroup laws follow from
the CPTP semigroup laws via `CPTPMap.compose_eq`.

This is the operational claim: a CPTP-proper QIF semigroup is, in
particular, an abstract QIF semigroup — the CPTP-properness is a
*strengthening* of the abstract carrier, not a separate concept. -/
def toAbstract (S : QIFSemigroupCPTP d) : QIFSemigroup d where
  Φ            := fun τ ρ => S.Φ τ ρ
  Φ_zero       := fun ρ => by
    rw [S.Φ_zero]
    exact CPTPMap.id_MState ρ
  Φ_compose    := fun τ₁ τ₂ ρ => by
    have h := S.Φ_compose τ₁ τ₂
    calc S.Φ (τ₁ + τ₂) ρ
        = (S.Φ τ₁ ∘ₘ S.Φ τ₂) ρ := by rw [h]
      _ = S.Φ τ₁ (S.Φ τ₂ ρ)   := CPTPMap.compose_eq ρ

/-- The trivial CPTP semigroup's abstract image equals the trivial
abstract semigroup (state-level action: both the identity on every
state). -/
lemma toAbstract_trivial_apply (τ : ℝ) (ρ : MState d) :
    (trivial d).toAbstract.Φ τ ρ = ρ :=
  trivial_apply τ ρ

end QIFSemigroupCPTP

end QuantumMechanics.FiniteTarget

end
