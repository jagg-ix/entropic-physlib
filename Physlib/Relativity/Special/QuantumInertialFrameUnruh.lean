/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QuantumInertialFrameLorentzianFromLindblad
public import Physlib.Relativity.Special.UnruhEntropicRate

/-!
# Unruh / Rindler Quantum Inertial Frame from a thermal-bath jump operator

Adapts physlib's existing `UnruhEntropicRate` structure
(`Physlib.Relativity.Special.UnruhEntropicRate`) to the Lindblad-QIF
framework: for a uniformly accelerated observer with proper
acceleration `a > 0` and an operator-level "coupling" `X : H →L[ℂ] H`
(typically a position-type operator), the **thermal-bath jump
operator** is

  `L_U(a, c, X) := √(λ_U) · X`,    `λ_U := a / (2π c)`

and the resulting `lindbladQIF` is the **Unruh QIF**.  The equilibrium
condition `Q.IsEquilibriumAt ψ` then reduces (via the existing
`lindbladQIF_isEquilibriumAt_iff_L_apply_zero`) to the operator-level
kernel condition `L_U ψ = 0`, equivalently `X ψ = 0` whenever
`λ_U > 0`.

Connection to the Hawking-temperature bridge (already in
`UnruhEntropicRate.lambdaU_eq_kB_hawking_over_hbar`): the Unruh
entropic rate `λ_U` equals `k_B · T_H / ℏ` with `T_H` the
Hawking-Unruh temperature, so the Unruh QIF realises the
*Connes-Rovelli thermal-time* identification at the Unruh
temperature.

## Main definitions and theorems

* `unruhJump a c X` — `L_U := √(λ_U) · X`.
* `unruhQIF H_R X a c hbar` — operator-level QIF from the Unruh
  jump.
* `fromUnruh sd H_R X a c hbar ψ worldline` — full Lorentzian QIF
  worldline.
* `fromUnruh.equilibriumBridge` — bridge derived as a theorem
  (inherits from `fromLindbladJump.equilibriumBridge`).

## References

* Unruh 1976, Davies 1975, Hawking 1975.
* Connes-Rovelli 1994 — thermal-time hypothesis.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget
open Physlib.Relativity.Special

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Unruh thermal-bath jump operator -/

/-- **Unruh thermal-bath jump operator** `L_U := √(λ_U) · X` with
`λ_U := a / (2π c)`.  Couples the Hilbert-space operator `X`
(typically a position-type operator) to a thermal bath at the Unruh
temperature `T_U = ℏ a / (2π c k_B)`. -/
def unruhJump (a c : ℝ) (X : H →L[ℂ] H) : H →L[ℂ] H :=
  ((Real.sqrt (a / (2 * Real.pi * c)) : ℂ)) • X

/-- The Unruh jump operator's coefficient is the square root of the
Unruh entropic rate `λ_U := a/(2πc)`. -/
theorem unruhJump_eq (a c : ℝ) (X : H →L[ℂ] H) :
    unruhJump a c X = ((Real.sqrt (a / (2 * Real.pi * c)) : ℂ)) • X := rfl

/-! ## §2 — Operator-level Unruh QIF -/

/-- **Unruh / Rindler QIF**: lindbladQIF with the Unruh thermal-bath
jump operator. -/
def unruhQIF (H_R X : H →L[ℂ] H) (a c hbar : ℝ) (hbar_pos : 0 < hbar) :
    QuantumInertialFrame H :=
  lindbladQIF H_R (unruhJump a c X) hbar hbar_pos

/-- **Equilibrium iff `L_U ψ = 0`** for the Unruh QIF — direct
specialisation of `lindbladQIF_isEquilibriumAt_iff_L_apply_zero`. -/
theorem unruhQIF_isEquilibriumAt_iff_L_apply_zero
    (H_R X : H →L[ℂ] H) (a c hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (unruhQIF H_R X a c hbar hbar_pos).IsEquilibriumAt ψ ↔
      unruhJump a c X ψ = 0 :=
  lindbladQIF_isEquilibriumAt_iff_L_apply_zero H_R (unruhJump a c X)
    hbar hbar_pos ψ

/-- **Equilibrium-condition simplification at positive `λ_U`**:
when `a > 0` (and `c > 0`), `L_U ψ = √(λ_U)·X ψ = 0` iff `X ψ = 0`. -/
theorem unruhQIF_isEquilibriumAt_iff_X_apply_zero
    (H_R X : H →L[ℂ] H) (a c hbar : ℝ)
    (h_a : 0 < a) (h_c : 0 < c) (hbar_pos : 0 < hbar) (ψ : H) :
    (unruhQIF H_R X a c hbar hbar_pos).IsEquilibriumAt ψ ↔ X ψ = 0 := by
  rw [unruhQIF_isEquilibriumAt_iff_L_apply_zero]
  unfold unruhJump
  constructor
  · intro h
    have h_lambda : 0 < a / (2 * Real.pi * c) :=
      div_pos h_a (by positivity)
    have h_sqrt : Real.sqrt (a / (2 * Real.pi * c)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr h_lambda)
    have h_complex : ((Real.sqrt (a / (2 * Real.pi * c)) : ℂ)) ≠ 0 := by
      exact_mod_cast h_sqrt
    exact smul_eq_zero.mp h |>.resolve_left h_complex
  · intro h
    show ((Real.sqrt (a / (2 * Real.pi * c)) : ℂ)) • (X ψ) = 0
    rw [h, smul_zero]

/-! ## §3 — Full Unruh Lorentzian QIF worldline -/

/-- **Full Unruh Lorentzian QIF worldline** from a Hermitian generator,
a coupling operator `X`, the kinematic parameters `(a, c, ℏ)`, a
frozen state `ψ`, and a worldline embedding `γ`.  Delegates to
`fromLindbladJump` with the Unruh jump operator. -/
def fromUnruh (sd : ℕ)
    (H_R X : H →L[ℂ] H) (a c hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (γ : ℝ → SpaceTime sd) :
    LorentzianQIFWorldline H sd :=
  fromLindbladJump sd H_R (unruhJump a c X) hbar hbar_pos ψ γ

namespace fromUnruh

variable {sd : ℕ}
  (H_R X : H →L[ℂ] H) (a c hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
  (γ : ℝ → SpaceTime sd)

/-- **equilibrium-reversible bridge for the Unruh
construction.**  Inherits the bridge from `fromLindbladJump`: both
arms reduce to the operational anchor `L_U ψ = 0` (equivalently
`X ψ = 0` at positive `a, c`). -/
theorem equilibriumBridge :
    LorentzianQIFEquilibriumBridge
      (fromUnruh sd H_R X a c hbar hbar_pos ψ γ) :=
  fromLindbladJump.equilibriumBridge H_R (unruhJump a c X) hbar hbar_pos ψ γ

end fromUnruh

/-! ## §4 — Bridge to physlib's `UnruhEntropicRate` structure -/

/-- **Identification of the Unruh-jump rate with the `UnruhEntropicRate`
`lambdaU`**: the square of the jump-operator coefficient is the Unruh
entropic rate encoded in `UnruhEntropicRate`.

For any `UnruhEntropicRate M` (structure with `kB, a, c`), the
coefficient `√(M.a / (2π M.c))` is `√(M.lambdaU)`, so squaring
recovers `M.lambdaU`.  This ties the operator-level Unruh QIF to
physlib's existing entropic-rate framework. -/
theorem unruhJump_coeff_sq_eq_lambdaU (M : UnruhEntropicRate)
    (X : H →L[ℂ] H) :
    Real.sqrt (M.a / (2 * Real.pi * M.c)) ^ 2 = M.lambdaU := by
  unfold UnruhEntropicRate.lambdaU
  exact Real.sq_sqrt
    (div_nonneg M.a_nonneg (le_of_lt M.two_pi_c_pos))

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
