/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Physlib.Relativity.Special.QuantumInertialFrameLorentzian
public import Physlib.Thermodynamics.SecondLaw

/-!
# Identity-dissipator Quantum Inertial Frame (`H_I = 1` case)

A maximally generic dissipative QIF: any Hermitian `H_R` paired with
the **identity dissipator** `H_I := 1` (positive trivially via
`ContinuousLinearMap.isPositive_one`).

Operationally: every state carries the same dissipation rate
`λ(ψ) = ‖ψ‖²/ℏ` — the dissipation is *uniform* across the Hilbert
space.  The only equilibrium state is `ψ = 0` (the trivial vector).

Connects `Physlib.Thermodynamics.SecondLaw.identityDissipatorArrow`
(which already exists) into the Lorentzian-QIF framework so the
"identity dissipator" can be treated as a frame.

## Main definitions

* `identityDissipatorQIF H_R ℏ ℏ_pos` — operator-level QIF with
  `H_I = 1`.
* `fromIdentityDissipator sd H_R ℏ ℏ_pos ψ γ` — full
  `LorentzianQIFWorldline` from the identity-dissipator
  construction, using `identityDissipatorArrow` as the entropy arrow.
* `fromIdentityDissipator.equilibriumBridge` — bridge derived as a
  theorem, with common anchor `ψ = 0`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget
open Physlib.Thermodynamics.SecondLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **Identity-dissipator QIF**: `H_R` arbitrary Hermitian, `H_I := 1`. -/
def identityDissipatorQIF (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) :
    QuantumInertialFrame H where
  H_R            := H_R
  H_I            := 1
  H_I_isPositive := ContinuousLinearMap.isPositive_one
  hbar           := hbar
  hbar_pos       := hbar_pos

/-- For the identity-dissipator QIF, the entropic rate at state `ψ`
is `‖ψ‖²/ℏ`. -/
lemma identityDissipatorQIF_entropicRate
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (identityDissipatorQIF H_R hbar hbar_pos).entropicRate ψ =
      ‖ψ‖ ^ 2 / hbar := by
  unfold QuantumInertialFrame.entropicRate identityDissipatorQIF
  simp only [ContinuousLinearMap.reApplyInnerSelf,
    ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  exact_mod_cast rfl

/-- For the identity-dissipator QIF, equilibrium at `ψ` iff `ψ = 0`. -/
lemma identityDissipatorQIF_isEquilibriumAt_iff
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (identityDissipatorQIF H_R hbar hbar_pos).IsEquilibriumAt ψ ↔ ψ = 0 := by
  unfold QuantumInertialFrame.IsEquilibriumAt
  rw [identityDissipatorQIF_entropicRate]
  have hne : hbar ≠ 0 := ne_of_gt hbar_pos
  constructor
  · intro h
    have h2 : ‖ψ‖ ^ 2 = 0 := by
      have := (div_eq_zero_iff (a := ‖ψ‖ ^ 2) (b := hbar)).mp h
      exact this.resolve_right hne
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  · intro h
    rw [h, norm_zero]; ring


/-- **`fromIdentityDissipator`** — bundles the identity-dissipator QIF
with the existing `identityDissipatorArrow` entropy arrow, a frozen
state, and a consumer-supplied worldline. -/
def fromIdentityDissipator (sd : ℕ)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (γ : ℝ → SpaceTime sd) :
    LorentzianQIFWorldline H sd where
  Q         := identityDissipatorQIF H_R hbar hbar_pos
  W         := identityDissipatorArrow H_R hbar hbar_pos ψ
  state     := fun _ => ψ
  worldline := γ

namespace fromIdentityDissipator

variable {sd : ℕ}
  (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
  (γ : ℝ → SpaceTime sd)

/-- For the identity-dissipator construction,
`IsAllTimesEquilibrium ↔ ψ = 0`. -/
lemma isAllTimesEquilibrium_iff :
    (fromIdentityDissipator sd H_R hbar hbar_pos ψ γ).IsAllTimesEquilibrium ↔ ψ = 0 := by
  unfold LorentzianQIFWorldline.IsAllTimesEquilibrium
    LorentzianQIFWorldline.IsEquilibriumAt fromIdentityDissipator
  rw [show
    (∀ t : ℝ, (identityDissipatorQIF H_R hbar hbar_pos).IsEquilibriumAt ψ)
      ↔ (identityDissipatorQIF H_R hbar hbar_pos).IsEquilibriumAt ψ from
    ⟨fun h => h 0, fun h _ => h⟩]
  exact identityDissipatorQIF_isEquilibriumAt_iff H_R hbar hbar_pos ψ

/-- For the identity-dissipator construction,
`W.IsReversible ↔ ψ = 0`. -/
lemma isReversible_iff :
    (fromIdentityDissipator sd H_R hbar hbar_pos ψ γ).W.IsReversible ↔ ψ = 0 := by
  unfold fromIdentityDissipator identityDissipatorArrow
    ofPositiveGeneratorArrow ofEntropyControlledSystem positiveGeneratorSystem
  unfold EntropyArrowWorldline.IsReversible
  have hne : hbar ≠ 0 := ne_of_gt hbar_pos
  constructor
  · intro h
    have h01 := h 0 1
    simp at h01
    -- h01 : hbar = 0 ∨ (1 : H →L[ℂ] H).reApplyInnerSelf ψ = 0
    have h_re : (1 : H →L[ℂ] H).reApplyInnerSelf ψ = 0 :=
      h01.resolve_left hne
    -- reApplyInnerSelf (1 : H →L[ℂ] H) ψ = re ⟨ψ, ψ⟩ = ‖ψ‖²
    have h_norm_sq : ‖ψ‖ ^ 2 = 0 := by
      have h_eq : (1 : H →L[ℂ] H).reApplyInnerSelf ψ = ‖ψ‖ ^ 2 := by
        unfold ContinuousLinearMap.reApplyInnerSelf
        simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
        exact_mod_cast rfl
      linarith [h_eq ▸ h_re]
    exact norm_eq_zero.mp
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_norm_sq)
  · intro hψ t₁ t₂
    have h_re : (1 : H →L[ℂ] H).reApplyInnerSelf ψ = 0 := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      simp [hψ]
    simp [h_re]

/-- **equilibrium-reversible bridge for the identity-
dissipator construction.**  Both arms reduce to `ψ = 0`. -/
lemma equilibriumBridge :
    LorentzianQIFEquilibriumBridge
      (fromIdentityDissipator sd H_R hbar hbar_pos ψ γ) where
  reversible_iff_equilibrium := by
    rw [isReversible_iff, isAllTimesEquilibrium_iff]

end fromIdentityDissipator

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
