/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible

/-!
# Free quantum-inertial-frame oscillator (`H_I = 0`, scaled-identity `H_R`)

The simplest non-Lindblad QIF: a **free single-frequency oscillator**
modelled as a reversible QIF (`H_I = 0`) with Hermitian generator
`H_R := ℏω · I` (scaled identity).

Every state is then an `H_R`-eigenstate with the *same* energy `ℏω`,
so the TISE for the full complex Hamiltonian holds on every state,
and the accumulated quantum phase over geometric proper time `τ` is
`exp(−i ω τ)` — exactly the reading of a
`Physlib.QuantumMechanics.Clock.Phase.PhaseClock` of angular
frequency `ω`.

This is the **degenerate single-frequency** limit of a quantum
harmonic oscillator (where the full QHO spectrum `ℏω(k + 1/2)` is
replaced by a single `ℏω` band).  For multi-level / multi-mode
treatment, consumers would supply an `H_R` carrying the number
operator on a truncated mode space; the present file shows the
QIF infrastructure works for any reversible setup.

## References

  regime.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- **Free single-frequency QIF** at angular frequency `ω`:
`H_R := ℏω · I`, `H_I := 0`.

Every state is a degenerate `H_R`-eigenstate with energy `ℏω`. -/
def freeQIF (omega hbar : ℝ) (hbar_pos : 0 < hbar) :
    QuantumInertialFrame H :=
  reversibleQIF ((hbar * omega : ℂ) • (1 : H →L[ℂ] H)) hbar hbar_pos

/-- Every state is an `H_R`-eigenstate with eigenvalue `ℏω`. -/
@[simp] lemma freeQIF_H_R_apply (omega hbar : ℝ) (hbar_pos : 0 < hbar)
    (ψ : H) :
    (freeQIF (H := H) omega hbar hbar_pos).H_R ψ = (hbar * omega : ℂ) • ψ := by
  simp [freeQIF, reversibleQIF]

/-- **TISE on every state** — the free QIF is degenerate; every state
satisfies the TISE with energy `ℏω`. -/
lemma freeQIF_tise (omega hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (freeQIF (H := H) omega hbar hbar_pos).complexHamiltonian ψ
      = (hbar * omega : ℂ) • ψ :=
  reversibleQIF_tise _ _ _ (freeQIF_H_R_apply omega hbar hbar_pos ψ)

/-- The free QIF is at equilibrium on every state (`λ ≡ 0`). -/
lemma freeQIF_isEquilibriumAt (omega hbar : ℝ) (hbar_pos : 0 < hbar)
    (ψ : H) :
    (freeQIF (H := H) omega hbar hbar_pos).IsEquilibriumAt ψ :=
  reversibleQIF_isEquilibriumAt _ _ _ ψ

end QuantumMechanics.FiniteTarget

end
