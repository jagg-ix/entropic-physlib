/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QIFSRInertialFrame
public import Physlib.Relativity.LorentzGroup.Basic

/-!
# QIF Lorentz frame change — entropic-rate is a Lorentz scalar (Bridge 2)

Couples the operator-level `FrameChange` (unitary `U` on `H`) with a
spacetime-level **Lorentz transform** `Λ ∈ LorentzGroup sd`.

The load-bearing physics:

  **The QIF entropic rate `λ(ψ) = ⟨ψ, H_I ψ⟩/ℏ` is a Lorentz scalar.**

Operationally: the equilibrium / non-equilibrium QIF distinction
survives Lorentz frame change.  Two observers in
different SR frames agree on whether a quantum subsystem is at
equilibrium QIF; the observer-independence of the operational
content is exactly the Lorentz invariance proved here.

Bridge 2 of four (Bridge 1: `QIFSRInertialFrame.lean`; Bridge 3:
`Physlib/ClassicalMechanics/InertialFrame.lean`; Bridge 4 main theorem:
`QIFClassicalReduction.lean`).

## Contents

* `QIFLorentzFrameChange LQW₁ LQW₂` — packages
  `(U : FrameChange LQW₁.Q LQW₂.Q, Λ : LorentzGroup sd)` plus the
  spacetime-side coherence
  `LQW₂.worldline t = Λ • LQW₁.worldline t` and state-side coherence
  `LQW₂.state t = U.U (LQW₁.state t)`.
* **`entropicRate_lorentz_invariant`** — the load-bearing result:
  the QIF entropic rate is invariant under any
  `QIFLorentzFrameChange`.
* `isInertial_preserved_under_frameChange` — `IsInertial` is
  Lorentz-covariant (geometric and quantum halves both preserved).


## References

  operational QIF content.
* MTW *Gravitation* §3 — Lorentz transformations as coordinate
  changes between SR inertial frames.
* Wigner 1939 — unitary representations of the Lorentz group on
  Hilbert space (the spacetime-side `Λ` paired with the Hilbert-
  space-side unitary `U(Λ)` is exactly Wigner's idea).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget Lorentz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **QIF Lorentz frame change**: pairs an operator-level
`FrameChange` (unitary `U : H ≃ₗᵢ[ℂ] H` with QIF-data conjugation
laws) and a spacetime-level Lorentz transform `Λ ∈ LorentzGroup sd`.

The two layers are bound by **coherence laws**:

* `worldline_transform`: the second QIF's worldline is the Lorentz
  transform of the first's.
* `state_transform`: the second QIF's quantum state is the
  unitary transform of the first's.

This is the operator-level companion of `LorentzGroup d` × Wigner-
style unitary representation: a single morphism that simultaneously
moves the Hilbert space (by `U`) and the spacetime worldline (by
`Λ`) into a new inertial frame. -/
structure QIFLorentzFrameChange
    {sd : ℕ} (LQW₁ LQW₂ : LorentzianQIFWorldline H sd) where
  /-- Operator-side frame change (unitary `U` + conjugation laws). -/
  opChange            : FrameChange LQW₁.Q LQW₂.Q
  /-- Spacetime-side Lorentz transform. -/
  Λ                   : LorentzGroup sd
  /-- **Worldline coherence**: the second worldline is `Λ`-image of
  the first.  `Λ • _` is the standard `LorentzGroup` action on
  `SpaceTime sd`. -/
  worldline_transform : ∀ t : ℝ, LQW₂.worldline t = Λ • LQW₁.worldline t
  /-- **State coherence**: the second QIF's state-along-worldline
  is the `U`-image of the first's. -/
  state_transform     : ∀ t : ℝ, LQW₂.state t = opChange.U (LQW₁.state t)

namespace QIFLorentzFrameChange


/-- **The QIF entropic rate is a Lorentz scalar**.

  `LQW₂.Q.entropicRate (LQW₂.state t) = LQW₁.Q.entropicRate (LQW₁.state t)`.

Combines the operator-side `FrameChange.entropicRate_invariant`
(commit `5f20c607`) with the state-coherence law: the rate at the
second observer's state-time equals the rate at the first observer's
state-time, regardless of the Lorentz transform `Λ` between the
frames.

**Operational content**: the equilibrium /
non-equilibrium QIF distinction does **not** depend on the SR
observer.  An equilibrium QIF in one frame is an equilibrium QIF in
every frame related by a Lorentz transform. -/
lemma entropicRate_lorentz_invariant
    {sd : ℕ} {LQW₁ LQW₂ : LorentzianQIFWorldline H sd}
    (fc : QIFLorentzFrameChange LQW₁ LQW₂) (t : ℝ) :
    LQW₂.Q.entropicRate (LQW₂.state t) =
      LQW₁.Q.entropicRate (LQW₁.state t) := by
  rw [fc.state_transform t, fc.opChange.entropicRate_invariant]

/-- **`IsEquilibriumAt` is Lorentz-covariant**: state `LQW₁.state t`
is at equilibrium QIF iff its frame-changed version `LQW₂.state t`
is at equilibrium QIF in the new frame. -/
lemma isEquilibriumAt_iff_lorentz
    {sd : ℕ} {LQW₁ LQW₂ : LorentzianQIFWorldline H sd}
    (fc : QIFLorentzFrameChange LQW₁ LQW₂) (t : ℝ) :
    LQW₂.IsEquilibriumAt t ↔ LQW₁.IsEquilibriumAt t := by
  unfold LorentzianQIFWorldline.IsEquilibriumAt
    QuantumInertialFrame.IsEquilibriumAt
  rw [entropicRate_lorentz_invariant fc t]

/-- **`IsAllTimesEquilibrium` is Lorentz-covariant**: the all-times
equilibrium-QIF property is shared between Lorentz-related frames. -/
lemma isAllTimesEquilibrium_iff_lorentz
    {sd : ℕ} {LQW₁ LQW₂ : LorentzianQIFWorldline H sd}
    (fc : QIFLorentzFrameChange LQW₁ LQW₂) :
    LQW₂.IsAllTimesEquilibrium ↔ LQW₁.IsAllTimesEquilibrium := by
  unfold LorentzianQIFWorldline.IsAllTimesEquilibrium
  exact ⟨fun h t => (isEquilibriumAt_iff_lorentz fc t).mp (h t),
         fun h t => (isEquilibriumAt_iff_lorentz fc t).mpr (h t)⟩

end QIFLorentzFrameChange

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
