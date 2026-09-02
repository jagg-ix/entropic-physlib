/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation

/-!
# Zitterbewegung on the operator side: constant in time is not the same as commuting with `H`

`ElectronZitterbewegung` establishes the factor of two **spectrally**: the rest-frame oscillation
operator `2H = 2mβ` squares to `(2ω_C)²·1`, so `ω_Z = 2ω_C` comes from the `E₊ − E₋` two-sheet
structure.  Dirac's original derivation instead runs through the *operator dynamics* of the velocity
`α`, and it is there that Sherry raised two inconsistencies.

Roy, Basu & Roy, *On the derivation of Zitterbewegung*, Phys. Lett. A **137** (1989) 7–8, resolve
them, and their resolution is a single distinction:

  "α'(0) is a constant with respect to time but it does not commute with the Hamiltonian `H`;
   in other words, α'(0) is not a c-number with respect to `H`, though it is constant with time."

Sherry's inconsistencies come from reading *time-independent operator* as *conserved quantity*.
They are different statements, and §A separates them exactly: a fixed Schrödinger operator has a
constant Heisenberg transform **iff** it commutes with the evolution.  Since the odd part of the
velocity does not commute with `H`, its Heisenberg transform genuinely oscillates and no
inconsistency arises.

§B supplies the operator-side origin of the factor of two that `ElectronZitterbewegung` obtains
spectrally.  The odd velocity part *anticommutes* with the free Hamiltonian, and anticommuting with
`H` flips the sign of every power of `H`.  Conjugating past the evolution therefore turns
`e^{−iHt}` into `e^{+iHt}`, so the two factors compound and the oscillation runs at `2H/ℏ` rather
than `H/ℏ` — the same `ω_Z = 2ω_C` reached from the dynamics rather than from the gap.

Both sections are exact matrix algebra over the `CompleteDiracEquation` α/β infrastructure, whose
`diracAlpha_beta_anticomm` is the anticommutation §B abstracts.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZitterbewegungOperatorConsistency

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### §A — The Sherry resolution: fixed operator ≠ constant Heisenberg transform -/

/-- Heisenberg conjugation of a fixed Schrödinger operator by a unitary. -/
def heisenbergConj (U A : Matrix n n ℂ) : Matrix n n ℂ := Uᴴ * A * U

/-- **A fixed operator has a constant Heisenberg transform exactly when it commutes with the
evolution.**  This is the distinction Roy, Basu & Roy identify as the source of Sherry's
inconsistencies: `α'(0)` is a constant *operator*, which does not make it a constant of the
*motion*.  Only commuting with `H` does that, and the odd velocity part does not commute. -/
theorem heisenbergConj_eq_self_iff_commute (U A : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    heisenbergConj U A = A ↔ A * U = U * A := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  unfold heisenbergConj
  constructor
  · intro h
    calc A * U = (1 : Matrix n n ℂ) * A * U := by rw [Matrix.one_mul]
      _ = (U * Uᴴ) * A * U := by rw [hU']
      _ = U * (Uᴴ * A * U) := by simp [Matrix.mul_assoc]
      _ = U * A := by rw [h]
  · intro h
    calc Uᴴ * A * U = Uᴴ * (A * U) := by rw [Matrix.mul_assoc]
      _ = Uᴴ * (U * A) := by rw [h]
      _ = (Uᴴ * U) * A := by rw [Matrix.mul_assoc]
      _ = A := by rw [hU, Matrix.one_mul]

/-- **Non-commuting fixed operators do move.**  Contrapositive reading of the above: if the operator
fails to commute with the evolution, its Heisenberg transform is *not* the operator itself — which is
precisely the trembling, not a contradiction. -/
theorem heisenbergConj_ne_self_of_not_commute {U A : Matrix n n ℂ} (hU : Uᴴ * U = 1)
    (h : A * U ≠ U * A) : heisenbergConj U A ≠ A := by
  intro hc
  exact h ((heisenbergConj_eq_self_iff_commute U A hU).mp hc)

/-! ### §B — Anticommutation is where the factor of two comes from -/

/-- **Anticommuting with `H` flips the sign of every power of `H`.**  If `A H = −H A` then
`A Hᵏ = (−1)ᵏ Hᵏ A`.  Applied to the exponential evolution this sends `e^{−iHt}` to `e^{+iHt}` on
passing `A` through, so the two exponentials compound and the oscillation frequency doubles — the
operator-dynamics origin of `ω_Z = 2 ω_C`, which `ElectronZitterbewegung` reaches from the `E₊ − E₋`
gap instead. -/
theorem anticomm_pow {A H : Matrix n n ℂ} (h : A * H = -(H * A)) :
    ∀ k : ℕ, A * H ^ k = (-1 : ℂ) ^ k • (H ^ k * A) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc A * H ^ (k + 1) = (A * H ^ k) * H := by rw [pow_succ, Matrix.mul_assoc]
      _ = ((-1 : ℂ) ^ k • (H ^ k * A)) * H := by rw [ih]
      _ = (-1 : ℂ) ^ k • (H ^ k * (A * H)) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (-1 : ℂ) ^ k • (H ^ k * (-(H * A))) := by rw [h]
      _ = (-1 : ℂ) ^ (k + 1) • (H ^ (k + 1) * A) := by
          rw [Matrix.mul_neg, smul_neg, pow_succ, pow_succ]
          rw [Matrix.mul_assoc]
          module

/-- **The Dirac velocity components anticommute with the mass term.**  `CompleteDiracEquation`'s
`diracAlpha_beta_anticomm` is exactly the hypothesis §B needs: at rest the Hamiltonian is `mβ`, so
each `αᵢ` anticommutes with it and the trembling runs at twice the rest-energy frequency. -/
theorem alpha_anticomm_rest_hamiltonian
    (s : Matrix (Fin 2) (Fin 2) ℂ) (m : ℂ) :
    Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation.diracAlpha s * (m • Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation.diracBeta)
      = -((m • Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation.diracBeta) *
          Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation.diracAlpha s) := by
  have hab := Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation.diracAlpha_beta_anticomm s
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
  congr 1
  linear_combination (norm := module) hab

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZitterbewegungOperatorConsistency

end
