/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame

/-!
# Reversible Quantum Inertial Frame (`H_I = 0` case)

Concrete instance of `QuantumInertialFrame` for the **reversible**
(non-dissipative) regime: any Hermitian generator `H_R` paired with
the zero dissipator `H_I := 0`. This is the QIF governing standard
unitary quantum mechanics, in which:

* every state is an equilibrium-QIF state (`λ(ψ) = 0` for all ψ),
* the dissipative kernel annihilates every state (`H_I ψ = 0` for
  all ψ, trivially since `H_I = 0`),
* the complex Hamiltonian reduces to the Hermitian part
  (`H_C ψ = H_R ψ`).

Used to instantiate the QIF representative for **non-dissipative physical
models** (free particle, harmonic oscillator, phase clocks, ideal
twin paradox, ...), where the operator-level data is just `H_R` and
the worldline / spacetime structure provides the remaining content.

Companion file
`Physlib/Relativity/Special/QuantumInertialFrameFromPhaseClockTwin.lean`
wires this reversible-QIF constructor to physlib's existing
`PhaseClock` and `InstantaneousTwinParadox` structures.

## Main definitions and theorems

* `reversibleQIF H_R hbar hbar_pos` — operator-level reversible QIF
  with `H_I = 0`.
* `reversibleQIF_entropicRate` — `λ(ψ) = 0` for any state.
* `reversibleQIF_isEquilibriumAt` — every state is at equilibrium.
* `reversibleQIF_H_I_apply_zero` — `H_I ψ = 0` for every state
  (trivially, since `H_I = 0`).
* `reversibleQIF_complexHamiltonian_eq_H_R` — `H_C = H_R` as
  operators.

## References

* Garcia 2026 APS PRL submission v3, §"Equilibrium vs Non-Equilibrium
  Quantum Reference Frames" — equilibrium-QIF reduction to unitary
  evolution.
* Sergi & Giaquinta 2016 — `H_I = 0` reversible limit of the
  Nagao-Nielsen complex-Hamiltonian framework.

No new axioms. std-3 throughout.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- **Reversible Quantum Inertial Frame** with `H_I := 0`.

The non-dissipative operator-level QIF structure.  Positivity of
`H_I = 0` is automatic via `ContinuousLinearMap.isPositive_zero`. -/
def reversibleQIF (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) :
    QuantumInertialFrame H where
  H_R            := H_R
  H_I            := 0
  H_I_isPositive := ContinuousLinearMap.isPositive_zero
  hbar           := hbar
  hbar_pos       := hbar_pos

/-- For a reversible QIF, the entropic rate `λ(ψ) = 0` for every state. -/
@[simp] theorem reversibleQIF_entropicRate
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (reversibleQIF H_R hbar hbar_pos).entropicRate ψ = 0 := by
  unfold QuantumInertialFrame.entropicRate reversibleQIF
  simp [ContinuousLinearMap.reApplyInnerSelf]

/-- For a reversible QIF, every state is an equilibrium-QIF state. -/
theorem reversibleQIF_isEquilibriumAt
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (reversibleQIF H_R hbar hbar_pos).IsEquilibriumAt ψ :=
  reversibleQIF_entropicRate H_R hbar hbar_pos ψ

/-- For a reversible QIF, the dissipative kernel annihilates every
state — trivially, since `H_I = 0`. -/
@[simp] theorem reversibleQIF_H_I_apply_zero
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (reversibleQIF H_R hbar hbar_pos).H_I ψ = 0 := rfl

/-- For a reversible QIF, the complex Hamiltonian reduces to `H_R`
on every state: `H_C ψ = H_R ψ`. -/
@[simp] theorem reversibleQIF_complexHamiltonian_apply
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (reversibleQIF H_R hbar hbar_pos).complexHamiltonian ψ = H_R ψ := by
  unfold QuantumInertialFrame.complexHamiltonian reversibleQIF
  simp

/-- For a reversible QIF, the complex Hamiltonian *as an operator*
equals `H_R`. -/
theorem reversibleQIF_complexHamiltonian
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) :
    (reversibleQIF H_R hbar hbar_pos).complexHamiltonian = H_R := by
  unfold QuantumInertialFrame.complexHamiltonian reversibleQIF
  simp

/-- **TISE recovery on every `H_R`-eigenstate** for a reversible QIF.
Specialisation of `tise_at_equilibrium` to the zero-dissipator
regime: at a reversible QIF, the TISE for the full complex
Hamiltonian holds on every `H_R`-eigenstate. -/
theorem reversibleQIF_tise
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    {ψ : H} {E : ℂ} (h_eig : H_R ψ = E • ψ) :
    (reversibleQIF H_R hbar hbar_pos).complexHamiltonian ψ = E • ψ := by
  rw [reversibleQIF_complexHamiltonian_apply, h_eig]

end QuantumMechanics.FiniteTarget

end
