/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QIFLorentzFrameChange
public import Physlib.Relativity.Special.UnruhEntropicRate

/-!
# Unruh frame change — accelerated observers DISAGREE on QIF classification

## Scope correction to commit `fed131ca`

The Lorentz-invariance theorem of Bridge 2
(`QIFLorentzFrameChange.entropicRate_lorentz_invariant`) holds
**only for inertial-to-inertial frame changes** — those related by
a Lorentz transform `Λ ∈ LorentzGroup sd` plus a unitary `U : H ≃ₗᵢ[ℂ] H`.

For **inertial-to-accelerated frame changes** (e.g., between a
free-falling and a hovering observer near a horizon), the QIF
classification IS observer-dependent: this is the **Unruh effect**.

The previous summary statement "two SR observers will agree" was
imprecise — it should have said "two **inertial** SR observers
related by a Lorentz transform will agree". Generic SR observers
(which can be accelerated) need not agree, exactly as the Unruh
effect demonstrates.

This file formalises that distinction.

## The Unruh effect at the QIF level

* **Inertial observer**: sees the Minkowski vacuum with QIF
 entropic rate `λ = 0` (equilibrium QIF / vacuum).
* **Accelerated observer** at proper acceleration `a > 0`: sees the
 *same quantum state* as a thermal KMS state at Unruh temperature
 `T_U = ℏa/(2πck_B)`, with QIF entropic rate
 `λ_U = a/(2πc) > 0` (non-equilibrium QIF / thermal bath).

These two observers DISAGREE on the QIF classification. The
relating transformation is a **Bogoliubov transformation** —
positive- and negative-frequency mode mixing — which is **not** a
unitary `U ∈ H ≃ₗᵢ[ℂ] H` in the `QIFLorentzFrameChange` sense.

## Contents

* `UnruhFrameChange LQW_inertial LQW_accelerated M` — `Prop` structure
 asserting the inertial QIF is at equilibrium while the accelerated
 QIF has entropic rate `λ_U` from `UnruhEntropicRate M`.
* `lambdaU_pos` — strict positivity of the Unruh rate at positive
 proper acceleration.
* **`qif_disagreement`** — load-bearing theorem: the two observers
 disagree on the QIF classification.
* `inertial_isEquilibriumAt_accelerated_not` — `IsEquilibriumAt` is
 observer-dependent under accelerated frame change.
* **`no_QIFLorentzFrameChange_at_unruh_disagreement`** — the
 contrapositive: if two QIFs disagree (one at λ = 0, other at λ_U > 0),
 they cannot be related by a `QIFLorentzFrameChange`. This pins
 down the exact scope of Bridge 2's Lorentz invariance.

## References

* Unruh 1976 *Notes on black-hole evaporation* — Unruh radiation.
* Davies 1975 — scalar particle production in Rindler frames.
* Bisognano-Wichmann 1975 — modular flow on the wedge algebra
 realises the Rindler/Unruh thermal state structurally.
 experiment" — operational distinction (inertial / hovering /
 free-fall).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget Physlib.Relativity.Special

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Unruh frame change structure -/

/-- **Unruh frame change**: an inertial QIF and an accelerated
(Rindler) QIF that DISAGREE on the equilibrium classification of
the underlying quantum state.

This is the **complement** of `QIFLorentzFrameChange`:

* `QIFLorentzFrameChange` (Bridge 2): inertial-to-inertial frame
  changes that PRESERVE the QIF entropic rate (Lorentz scalar).
* `UnruhFrameChange` (this file): inertial-to-accelerated frame
  changes that CHANGE the QIF entropic rate from `0` to `λ_U`
  (Unruh effect).

The relating transformation between the two Hilbert-space states
is a **Bogoliubov transformation** (mixing positive- and
negative-frequency modes), not a unitary in the
`QIFLorentzFrameChange` sense.  This file does not formalise the
Bogoliubov transformation explicitly — instead, it asserts the
*operational consequence* (disagreement on QIF classification) as
a `Prop` structure, with `M : UnruhEntropicRate` supplying the rate
parameter. -/
structure UnruhFrameChange {sd : ℕ}
    (LQW_inertial LQW_accelerated : LorentzianQIFWorldline H sd)
    (M : UnruhEntropicRate) : Prop where
  /-- The inertial QIF is at all-times equilibrium — the inertial
  observer sees the vacuum (`λ = 0`). -/
  inertial_at_equilibrium : LQW_inertial.IsAllTimesEquilibrium
  /-- The accelerated QIF's entropic rate equals the Unruh rate
  `λ_U = a/(2πc)` at every parameter — the accelerated observer
  sees a thermal KMS state. -/
  accelerated_at_unruh_rate : ∀ t : ℝ,
    LQW_accelerated.Q.entropicRate (LQW_accelerated.state t) = M.lambdaU
  /-- The proper acceleration is strictly positive (otherwise the
  accelerated observer is just another inertial observer and would
  agree with the first — see `QIFLorentzFrameChange`). -/
  proper_acceleration_pos : 0 < M.a

namespace UnruhFrameChange

variable {sd : ℕ}
  {LQW_inertial LQW_accelerated : LorentzianQIFWorldline H sd}
  {M : UnruhEntropicRate}

/-! ## §2 — Strict positivity of the Unruh rate -/

/-- **The Unruh rate is strictly positive** at positive proper
acceleration: `λ_U = a/(2πc) > 0` when `a > 0` and `c > 0`. -/
theorem lambdaU_pos
    (U : UnruhFrameChange LQW_inertial LQW_accelerated M) :
    0 < M.lambdaU := by
  unfold UnruhEntropicRate.lambdaU
  exact div_pos U.proper_acceleration_pos M.two_pi_c_pos

/-! ## §3 — The Unruh-effect disagreement theorem -/

/-- **THE UNRUH EFFECT (operational)**: two SR observers — one
inertial, one accelerated — **DISAGREE** on the QIF classification.

* The **inertial observer** measures entropic rate `λ = 0`
  (equilibrium QIF / vacuum).
* The **accelerated observer** measures entropic rate `λ = λ_U > 0`
  (non-equilibrium QIF / thermal at Unruh temperature `T_U`).

This is the load-bearing operational content of the Unruh effect at
the QIF level: the equilibrium-QIF classification is **not** invariant
under accelerated frame changes.

It is the *complement* of Bridge 2's
`QIFLorentzFrameChange.entropicRate_lorentz_invariant` — together,
the two theorems pin down the exact scope of QIF Lorentz invariance:
inertial-to-inertial only. -/
theorem qif_disagreement
    (U : UnruhFrameChange LQW_inertial LQW_accelerated M) (t : ℝ) :
    LQW_inertial.Q.entropicRate (LQW_inertial.state t) = 0 ∧
    0 < LQW_accelerated.Q.entropicRate (LQW_accelerated.state t) := by
  refine ⟨U.inertial_at_equilibrium t, ?_⟩
  rw [U.accelerated_at_unruh_rate t]
  exact U.lambdaU_pos

/-- **`IsEquilibriumAt` is observer-dependent under Unruh frame
change**: the inertial QIF is at equilibrium while the accelerated
QIF is NOT. -/
theorem inertial_isEquilibriumAt_accelerated_not
    (U : UnruhFrameChange LQW_inertial LQW_accelerated M) (t : ℝ) :
    LQW_inertial.IsEquilibriumAt t ∧
    ¬ LQW_accelerated.IsEquilibriumAt t := by
  refine ⟨U.inertial_at_equilibrium t, ?_⟩
  intro h
  unfold LorentzianQIFWorldline.IsEquilibriumAt
    QuantumInertialFrame.IsEquilibriumAt at h
  rw [U.accelerated_at_unruh_rate t] at h
  exact absurd h (ne_of_gt U.lambdaU_pos)

end UnruhFrameChange

/-! ## §4 — Bridge 2 scope: no `QIFLorentzFrameChange` at Unruh disagreement -/

/-- **Contrapositive scope-pinning of Bridge 2**.

If two Lorentzian QIFs satisfy an Unruh frame change (one inertial
at equilibrium, the other accelerated at `λ_U > 0`), then they
**cannot** be related by a `QIFLorentzFrameChange` (Bridge 2):

 `UnruhFrameChange ⟹ ¬ ∃ QIFLorentzFrameChange`.

This formalises the *scope* of Bridge 2's Lorentz invariance.
The contrapositive of
`QIFLorentzFrameChange.entropicRate_lorentz_invariant`:

 If `λ₁ ≠ λ₂` for two QIFs, then they're not related by a
 `QIFLorentzFrameChange` (because `QIFLorentzFrameChange` would
 force `λ₁ = λ₂`).

Operational content: the QIF Lorentz invariance holds only for
**inertial-to-inertial** changes. Inertial-to-accelerated changes
(Unruh) genuinely change the QIF classification — they are *not*
in the scope of Bridge 2. -/
theorem no_QIFLorentzFrameChange_at_unruh_disagreement
    {sd : ℕ}
    {LQW_inertial LQW_accelerated : LorentzianQIFWorldline H sd}
    {M : UnruhEntropicRate}
    (U : UnruhFrameChange LQW_inertial LQW_accelerated M) :
    ¬ ∃ _ : QIFLorentzFrameChange LQW_inertial LQW_accelerated, True := by
  rintro ⟨fc, _⟩
  -- If fc exists, then entropicRate is Lorentz-invariant: λ₂ = λ₁
  have h_invariant := fc.entropicRate_lorentz_invariant 0
  -- But inertial λ₁ = 0, accelerated λ₂ = λ_U > 0
  have h_acc_zero :
      LQW_accelerated.Q.entropicRate (LQW_accelerated.state 0) = 0 := by
    rw [h_invariant]
    exact U.inertial_at_equilibrium 0
  have h_acc_pos :
      0 < LQW_accelerated.Q.entropicRate (LQW_accelerated.state 0) := by
    rw [U.accelerated_at_unruh_rate 0]
    exact U.lambdaU_pos
  linarith

/-! ## §5 — Three-probe thought experiment (operational interpretation) -/

/-- **Three-probe thought experiment**: three identical detectors
near a Schwarzschild horizon — inertial (far away), hovering
(proper acceleration `a > 0`), free-falling (transient).

Inertial vs hovering: a `UnruhFrameChange` structure.  The inertial
observer sees vacuum (equilibrium QIF); the hovering observer sees
thermal radiation at Unruh temperature (non-equilibrium QIF).

This file's `qif_disagreement` realises the operational content of
the inertial/hovering pair: the QIF classification depends on the
observer's frame condition (inertial vs accelerated), exactly as
the paper claims.

The free-fall case is a *transient* non-equilibrium QIF that
reverts to equilibrium asymptotically (paper §3); not formalised
here.  Hovering ↔ inertial is the load-bearing operational
distinction, and that distinction is the `UnruhFrameChange`. -/
example {sd : ℕ}
    (LQW_inertial LQW_hovering : LorentzianQIFWorldline H sd)
    (M : UnruhEntropicRate)
    (U : UnruhFrameChange LQW_inertial LQW_hovering M)
    (t : ℝ) :
    -- inertial probe A: vacuum (equilibrium QIF)
    LQW_inertial.Q.entropicRate (LQW_inertial.state t) = 0 ∧
    -- hovering probe B: thermal (non-equilibrium QIF at λ_U)
    LQW_hovering.Q.entropicRate (LQW_hovering.state t) = M.lambdaU :=
  ⟨U.inertial_at_equilibrium t, U.accelerated_at_unruh_rate t⟩

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
