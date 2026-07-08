/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Operators.Unitary
public import QuantumInfo.States.Entanglement
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Landauer's bound, derived from a unitary dilation (uncorrelated initial discharged)

The Landauer quantum `ln 2` is derived, not assumed; and the "system and environment
initially uncorrelated" premise is itself *discharged* for an actual product state via
von Neumann product additivity (proved here from `spectrum_prod`).

* `Hₛ_prod` / `Sᵥₙ_prod` — Shannon and von Neumann entropy are additive on products
  (`Sᵥₙ(ρ ⊗ σ) = Sᵥₙ ρ + Sᵥₙ σ`), proved from `negMulLog_mul` and `spectrum_prod`.
* `Sᵥₙ_uniform` / `Sᵥₙ_uniform_qubit` — `Sᵥₙ(I/d) = log d`; a fair bit has entropy `ln 2`.
* `entropy_balance_of_unitary` — unitary invariance + subadditivity ⇒ the marginal
  entropy sum is non-decreasing.
* `landauer_export` — erasing a fair bit (final system marginal pure) exports `≥ ln 2`.
* `landauer_export_product` — the same for an *actual product* initial state
  `(maximally-mixed qubit) ⊗ ρ_E`, where the uncorrelated-initial premise is no longer
  assumed but follows from `Sᵥₙ_prod`. Only the erasure-success premise remains.
-/

set_option autoImplicit false

open scoped MState
open ProbDistribution

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.Landauer

/-! ## Product additivity of entropy -/

/-- Shannon entropy is additive on product distributions. -/
theorem Hₛ_prod {α β : Type*} [Fintype α] [Fintype β]
    (d1 : ProbDistribution α) (d2 : ProbDistribution β) :
    Hₛ (d1.prod d2) = Hₛ d1 + Hₛ d2 := by
  have key : ∀ (i : α) (j : β),
      H₁ ((d1.prod d2) (i, j)) = (d2 j : ℝ) * H₁ (d1 i) + (d1 i : ℝ) * H₁ (d2 j) := by
    intro i j
    simp only [prod_def, H₁, Prob.coe_mul]
    exact Real.negMulLog_mul _ _
  simp only [Hₛ, Fintype.sum_prod_type, key, Finset.sum_add_distrib]
  have e1 : (∑ i, ∑ j, (d2 j : ℝ) * H₁ (d1 i)) = ∑ i, H₁ (d1 i) := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul, normalized, one_mul]
  have e2 : (∑ i, ∑ j, (d1 i : ℝ) * H₁ (d2 j)) = ∑ j, H₁ (d2 j) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, normalized, one_mul]
  rw [e1, e2]

variable {d dE : Type*} [Fintype d] [DecidableEq d] [Fintype dE] [DecidableEq dE]

/-- Von Neumann entropy is additive on product states (from `spectrum_prod` + `Hₛ_prod`). -/
theorem Sᵥₙ_prod (ρ : MState d) (σ : MState dE) :
    Sᵥₙ (ρ.prod σ) = Sᵥₙ ρ + Sᵥₙ σ := by
  have h : Sᵥₙ (ρ.prod σ) = Hₛ (ρ.spectrum.prod σ.spectrum) := by
    obtain ⟨e, he⟩ := MState.spectrum_prod ρ σ
    simp only [Sᵥₙ, Hₛ]
    rw [← Equiv.sum_comp e (fun x => H₁ ((ρ.prod σ).spectrum.prob x))]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ _
    show H₁ ((ρ ⊗ᴹ σ).spectrum (e (i, j))) = H₁ ((ρ.spectrum.prod σ.spectrum) (i, j))
    rw [he i j, prod_def]
  rw [h, Hₛ_prod]; rfl

/-- For a product (uncorrelated) state the entropy is the sum of the marginal
entropies -- discharging the `entropy_balance` `h_uncorr` premise. -/
theorem uncorrelated_product (ρ : MState d) (σ : MState dE) :
    Sᵥₙ (ρ.prod σ) = Sᵥₙ (ρ.prod σ).traceRight + Sᵥₙ (ρ.prod σ).traceLeft := by
  rw [MState.traceRight_prod_eq, MState.traceLeft_prod_eq]; exact Sᵥₙ_prod ρ σ

/-! ## Maximally-mixed entropy and the Landauer floor -/

/-- The maximally-mixed state has von Neumann entropy `log d`. -/
theorem Sᵥₙ_uniform [Nonempty d] :
    Sᵥₙ (MState.uniform : MState d) = Real.log (Finset.univ.card (α := d)) := by
  rw [MState.uniform, Sᵥₙ_ofClassical, Hₛ_uniform]

/-- A maximally-mixed qubit (a fair bit) has von Neumann entropy `ln 2`. -/
theorem Sᵥₙ_uniform_qubit : Sᵥₙ (MState.uniform : MState (Fin 2)) = Real.log 2 := by
  rw [Sᵥₙ_uniform]; simp

/-- Unitary invariance of von Neumann entropy. -/
theorem Sᵥₙ_U_conj' (ρ : MState (d × dE)) (U : 𝐔[d × dE]) :
    Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ := by
  simp only [Sᵥₙ, MState.U_conj_spectrum_eq]

/-- Unitary invariance + subadditivity ⇒ the marginal entropy sum is non-decreasing. -/
theorem entropy_balance_of_unitary (ρ : MState (d × dE)) (U : 𝐔[d × dE])
    (h_uncorr : Sᵥₙ ρ = Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft
      ≤ Sᵥₙ (U ◃ ρ).traceRight + Sᵥₙ (U ◃ ρ).traceLeft := by
  rw [← h_uncorr, ← Sᵥₙ_U_conj' ρ U]
  exact Sᵥₙ_subadditivity (U ◃ ρ)

/-- **Landauer's bound (general).** A fair bit (`traceRight = uniform`), uncorrelated
(`h_uncorr`), erased so the final system marginal is pure (`h_final_pure`), exports
`≥ ln 2` of entropy. -/
theorem landauer_export (ρ : MState (Fin 2 × dE)) (U : 𝐔[Fin 2 × dE])
    (h_uncorr : Sᵥₙ ρ = Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft)
    (h_sys_mix : ρ.traceRight = MState.uniform)
    (h_final_pure : Sᵥₙ (U ◃ ρ).traceRight = 0) :
    Real.log 2 ≤ Sᵥₙ (U ◃ ρ).traceLeft - Sᵥₙ ρ.traceLeft := by
  have hbal := entropy_balance_of_unitary ρ U h_uncorr
  rw [h_sys_mix, Sᵥₙ_uniform_qubit, h_final_pure] at hbal
  linarith

/-- **Landauer's bound for an actual product state.** Erasing a maximally-mixed qubit
that starts as a genuine product `uniform ⊗ ρ_E` (so the uncorrelated-initial premise is
*discharged* by `Sᵥₙ_prod`), with the erasure succeeding, exports `≥ ln 2` of entropy to
the environment. The only remaining premise is that the erasure succeeded. -/
theorem landauer_export_product (ρE : MState dE) (U : 𝐔[Fin 2 × dE])
    (h_final_pure : Sᵥₙ (U ◃ ((MState.uniform : MState (Fin 2)).prod ρE)).traceRight = 0) :
    Real.log 2 ≤ Sᵥₙ (U ◃ ((MState.uniform : MState (Fin 2)).prod ρE)).traceLeft - Sᵥₙ ρE := by
  have h := landauer_export ((MState.uniform : MState (Fin 2)).prod ρE) U
    (uncorrelated_product MState.uniform ρE)
    (MState.traceRight_prod_eq MState.uniform ρE)
    h_final_pure
  rwa [MState.traceLeft_prod_eq] at h

end Physlib.QuantumMechanics.RelationalTime.Landauer

end
