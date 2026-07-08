/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QuantumInertialFrameLorentzian
public import Physlib.QuantumMechanics.Lindblad.GreensFunction
public import Physlib.Thermodynamics.SecondLaw

/-!
# Lorentzian Quantum Inertial Frame from a Lindblad jump

Concrete consumer of `LorentzianQIFWorldline` and
`LorentzianQIFEquilibriumBridge`: builds a Lorentzian QIF worldline
from a specific physical model (a Hermitian generator `H_R` plus a
Lindblad jump operator `L`, a positive `ℏ`, a state `ψ`, and a
spacetime worldline `γ`) and **derives** the equilibrium-reversible
bridge as a *theorem* rather than supplying it as a
consumer-provided `Prop`.

This connects the abstract structure
(`Physlib.Relativity.Special.QuantumInertialFrameLorentzian`) to
physlib's existing Lindblad / positive-generator second-law
infrastructure (`Physlib.QuantumMechanics.Lindblad.GreensFunction`,
`Physlib.Thermodynamics.SecondLaw.ofPositiveGeneratorArrow`).

## What this resolves

The earlier status note after an earlier version said:

> Not a complete physics derivation: e.g., the strict-dissipation bridge
> and equilibrium-reversible bridge are Prop-level constitutive
> identifications supplied by consumers per physical model. Connecting them
> to specific Hamiltonians (e.g. Unruh-DeWitt detector responses) is a
> separate task.

This file supplies that connection for the Lindblad-jump case.  For
this specific Hamiltonian setup, the equilibrium-reversible bridge
*holds as a derived theorem* — no `Prop` is taken as a hypothesis,
no consumer supplies the identification.

## Setup

* `H_R H_I : H →L[ℂ] H` with `H_I = adjoint L ∘L L = L†L` (positive
  by `lindbladDissipator_isPositive`).
* `EntropyArrowWorldline` from `ofLindbladJump H_R L hbar hbar_pos ψ`
  (whose `S_I_along t = 2 · ⟨ψ, H_I ψ⟩ · t` is a linear function
  of `t`).
* State `ψ` is **frozen** along the parameter (Heisenberg-picture
  convention; matches `ofLindbladJump`'s constant-ψ usage).
* Worldline `γ : ℝ → SpaceTime sd` is consumer-supplied.

## Main results

* `lindbladQIF` — builds the operator-level `QuantumInertialFrame`
  from `(H_R, L, ℏ, ℏ_pos)`.
* `fromLindbladJump` — builds the full
  `LorentzianQIFWorldline H sd` (QIF + entropy-arrow + frozen state +
  worldline) from a Lindblad jump.
* `fromLindbladJump_equilibrium_iff` — for this construction,
  `IsAllTimesEquilibrium ↔ L ψ = 0` (operator-level characterisation
  of equilibrium QIF via the dissipative kernel).
* `fromLindbladJump_reversible_iff` — for this construction,
  `W.IsReversible ↔ L ψ = 0` (thermodynamic characterisation).
* **Main theorem** `fromLindbladJump_equilibriumBridge` — the
  equilibrium-reversible bridge is *derived as a theorem* for the
  Lindblad-jump construction.  Not a `Prop`; not a consumer input.

## References

* Lindblad 1976, Gorini-Kossakowski-Sudarshan 1976 — Lindblad form
  `H_eff = H_R - i·H_I` with `H_I = L†L ≥ 0`.
* Stinespring 1955 — complete positivity of `L†L`.
  Quantum Reference Frames" — operational definition of equilibrium
  QIF.
* Sergi & Giaquinta 2016 — `d‖ψ‖²/dt = −(2/ℏ)·⟨H_I⟩` decay-rate
  convention.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget
open Physlib.QuantumMechanics.Lindblad.GreensFunction
open Physlib.Thermodynamics.SecondLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Operator-level QIF from a Lindblad pair `(H_R, L)` -/

/-- **Operator-level QIF from a Lindblad jump operator**.

Given `H_R : H →L[ℂ] H` (Hermitian generator) and `L : H →L[ℂ] H`
(jump operator), the QIF has `H_I := L†L` (positive by
`lindbladDissipator_isPositive`).  No positivity hypothesis on
`H_I` is needed — it is supplied as a theorem from the operator
structure `L†L ≥ 0`. -/
def lindbladQIF
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) :
    QuantumInertialFrame H where
  H_R            := H_R
  H_I            := lindbladDissipator L
  H_I_isPositive := lindbladDissipator_isPositive L
  hbar           := hbar
  hbar_pos       := hbar_pos

/-- The Lindblad QIF's entropic rate equals `lindbladRate L ψ / ℏ`. -/
theorem lindbladQIF_entropicRate
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (lindbladQIF H_R L hbar hbar_pos).entropicRate ψ =
      lindbladRate L ψ / hbar := by
  unfold QuantumInertialFrame.entropicRate lindbladQIF lindbladRate
  rfl

/-- **Equilibrium QIF at `ψ` ↔ `L ψ = 0`** for the Lindblad QIF.

The operator-level dissipative kernel: the QIF is at equilibrium on
`ψ` iff the jump operator annihilates `ψ` (no transitions can occur
from `ψ`).  This is the special-case form of the general
`ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`
for `H_I = L†L`. -/
theorem lindbladQIF_isEquilibriumAt_iff_L_apply_zero
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (lindbladQIF H_R L hbar hbar_pos).IsEquilibriumAt ψ ↔ L ψ = 0 := by
  unfold QuantumInertialFrame.IsEquilibriumAt
  rw [lindbladQIF_entropicRate, div_eq_zero_iff, lindbladRate_eq_normSq]
  constructor
  · rintro (h | h)
    · exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
    · exact absurd h (ne_of_gt hbar_pos)
  · intro h
    left
    rw [h, norm_zero]; ring

/-! ## §2 — Full Lorentzian QIF worldline from a Lindblad jump -/

/-- **Build a Lorentzian QIF worldline from a Lindblad jump**.

The data:

* `H_R L : H →L[ℂ] H` — Hermitian and jump operators.
* `hbar > 0` — Planck constant.
* `ψ : H` — quantum state (frozen along the worldline parameter).
* `worldline : ℝ → SpaceTime sd` — Lorentzian-spacetime embedding
  (consumer-supplied; e.g. constant-velocity straight line for
  inertial Probe A, hyperbolic curve for hovering Probe B).

The entropy-arrow worldline comes from
`ofLindbladJump H_R L hbar hbar_pos ψ`, whose `S_I_along t` is the
linear function `2 · ⟨ψ, H_I ψ⟩ · t = 2 · lindbladRate L ψ · t`. -/
def fromLindbladJump (sd : ℕ)
    (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (worldline : ℝ → SpaceTime sd) :
    LorentzianQIFWorldline H sd where
  Q         := lindbladQIF H_R L hbar hbar_pos
  W         := ofLindbladJump H_R L hbar hbar_pos ψ
  state     := fun _ => ψ
  worldline := worldline

namespace fromLindbladJump

variable {sd : ℕ}
  (H_R L : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
  (worldline : ℝ → SpaceTime sd)

/-- For the Lindblad construction, the QIF is at equilibrium at every
parameter iff `L ψ = 0` (state-level characterisation).

The state is frozen at `ψ`, so all-times equilibrium reduces to a
single-state condition; for the lindbladQIF that condition is
`L ψ = 0` via the dissipative-kernel characterisation. -/
theorem isAllTimesEquilibrium_iff :
    (fromLindbladJump sd H_R L hbar hbar_pos ψ worldline).IsAllTimesEquilibrium ↔ L ψ = 0 := by
  unfold LorentzianQIFWorldline.IsAllTimesEquilibrium
    LorentzianQIFWorldline.IsEquilibriumAt fromLindbladJump
  rw [show
    (∀ t : ℝ, (lindbladQIF H_R L hbar hbar_pos).IsEquilibriumAt ψ)
      ↔ (lindbladQIF H_R L hbar hbar_pos).IsEquilibriumAt ψ from
    ⟨fun h => h 0, fun h _ => h⟩]
  exact lindbladQIF_isEquilibriumAt_iff_L_apply_zero H_R L hbar hbar_pos ψ

/-- For the Lindblad construction, the entropy-arrow worldline is
reversible iff `L ψ = 0` (thermodynamic-level characterisation).

`S_I_along t = 2 · lindbladRate L ψ · t` is constant iff the slope
vanishes, i.e. `lindbladRate L ψ = 0 = ‖L ψ‖² = 0`. -/
theorem isReversible_iff :
    (fromLindbladJump sd H_R L hbar hbar_pos ψ worldline).W.IsReversible ↔ L ψ = 0 := by
  unfold fromLindbladJump ofLindbladJump ofPositiveGeneratorArrow
    ofEntropyControlledSystem positiveGeneratorSystem
  unfold EntropyArrowWorldline.IsReversible
  have hne : hbar ≠ 0 := ne_of_gt hbar_pos
  constructor
  · intro h
    have h01 := h 0 1
    simp at h01
    -- h01 : hbar = 0 ∨ (lindbladDissipator L).reApplyInnerSelf ψ = 0
    have h_rate : (lindbladDissipator L).reApplyInnerSelf ψ = 0 :=
      h01.resolve_left hne
    -- Convert to L ψ = 0 via lindbladRate_eq_normSq
    have h_norm_sq : ‖L ψ‖ ^ 2 = 0 := by
      rw [← lindbladRate_eq_normSq]; exact h_rate
    exact norm_eq_zero.mp
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_norm_sq)
  · intro hL t₁ t₂
    have h_rate : (lindbladDissipator L).reApplyInnerSelf ψ = 0 := by
      change lindbladRate L ψ = 0
      rw [lindbladRate_eq_normSq, hL, norm_zero]; ring
    simp [h_rate]

/-! ## §3 — Derived equilibrium-reversible bridge -/

/-- **equilibrium-reversible bridge is a derived theorem
for the Lindblad-jump construction.**

The Prop-level constitutive identification
`LorentzianQIFEquilibriumBridge` is *not* supplied as a consumer
hypothesis here — it is **proved** for the Lindblad-jump
construction by chaining `isReversible_iff` and
`isAllTimesEquilibrium_iff` through the common operational anchor
`L ψ = 0`.

Physically: for any Lindblad-jump model, the thermodynamic
reversibility of the entropy arrow and the quantum-mechanical
equilibrium of the QIF are *the same condition*, both equivalent to
"the jump operator annihilates the state". -/
theorem equilibriumBridge :
    LorentzianQIFEquilibriumBridge
      (fromLindbladJump sd H_R L hbar hbar_pos ψ worldline) where
  reversible_iff_equilibrium := by
    rw [isReversible_iff, isAllTimesEquilibrium_iff]

end fromLindbladJump

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
