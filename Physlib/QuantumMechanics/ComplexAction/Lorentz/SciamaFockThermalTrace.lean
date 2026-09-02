/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion

/-!
# The Fock-space operator trace `Tr(ρ Ô)` of the Hartle–Hawking thermal state (Sciama Eq. 18/19)

`SciamaThermalDensityMatrix` had the Hartle–Hawking state as a c-number Gibbs distribution `p_n = r^n(1−r)`;
`SciamaFockL2Completion` built the genuine ℓ² Hilbert space with the number states `|n⟩` as an orthonormal
Hilbert basis.  This closes the loop: the algebraic Fock space includes densely into `ℓ²`, the number
operator's diagonal matrix elements are computed with the *actual inner product*, and the thermal trace
`Tr(ρ Ô) = Σ_n p_n ⟨n|Ô|n⟩` in the number basis reproduces the results already known at the c-number level —
Sciama Eq. 18 (`⟨H|Ô|H⟩ = Tr(ρ Ô)`) at the diagonal level.

* `incl` — the linear inclusion of the algebraic Fock space `ℕ →₀ ℂ` into `ℓ²`; `incl_range = fockCore`,
  `incl_denseRange` — its image is the dense core.
* `numberOp_diag_matrixElement` — `⟨n|N|n⟩ = n`: the number operator's diagonal matrix element computed via
  the ℓ² inner product from the algebraic eigenvalue equation `N|n⟩ = n|n⟩`.
* `norm_incl_numberOp_numberKet`, `numberOp_unbounded` — `‖N|n⟩‖ = n` has no uniform bound: the number
  operator is genuinely unbounded, so it is only densely defined (on `fockCore`), never continuous on `ℓ²`.
* `thermalTrace_normalized` — `Tr(ρ) = Σ_n p_n ⟨n|n⟩ = 1` (unit trace).
* `thermalTrace_number` — `Tr(ρ N) = Σ_n p_n ⟨n|N|n⟩ = ⟨N⟩ = boseEinstein(β,E)`: the operator trace of the
  number in the thermal state is the Bose–Einstein occupation.

Honest scope: the diagonal trace `Σ_n ⟨n|·|n⟩` in the number basis (the trace evaluated on the Hilbert basis)
for the diagonal thermal state; the full trace-class theory (basis-independence, `ρ` as a bounded operator) is
separate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **The inclusion** of the algebraic Fock space `ℕ →₀ ℂ` into the ℓ² completion, sending each number state
to its ℓ² number state. -/
def incl : (ℕ →₀ ℂ) →ₗ[ℂ] FockHilbert := Finsupp.linearCombination ℂ fockKet

@[simp] theorem incl_numberKet (n : ℕ) : incl (numberKet n) = fockKet n := by
  rw [incl, numberKet, Finsupp.linearCombination_single, one_smul]

/-- **[Image is the dense core]** the algebraic Fock space maps onto the dense core `fockCore`. -/
theorem incl_range : LinearMap.range incl = fockCore := by
  rw [incl, fockCore, Finsupp.range_linearCombination]

/-- **[Dense inclusion]** the algebraic Fock space is dense in `ℓ²` via `incl`. -/
theorem incl_denseRange : DenseRange (incl : (ℕ →₀ ℂ) → FockHilbert) := by
  unfold DenseRange
  rw [← LinearMap.coe_range, incl_range]
  exact fockCore_dense

/-- **[Number diagonal matrix element] `⟨n|N|n⟩ = n`.**  Computed with the ℓ² inner product from the
algebraic eigenvalue equation `N|n⟩ = n|n⟩` (`numberOp_numberKet`) — the diagonal of the number operator in
the number basis. -/
theorem numberOp_diag_matrixElement (n : ℕ) :
    ⟪incl (numberKet n), incl (numberOp (numberKet n))⟫ = (n : ℂ) := by
  rw [numberOp_numberKet, map_smul, incl_numberKet, inner_smul_right, fockKet_inner]
  simp

/-- **[Identity diagonal matrix element] `⟨n|n⟩ = 1`.** -/
theorem identity_diag_matrixElement (n : ℕ) :
    ⟪incl (numberKet n), incl (numberKet n)⟫ = 1 := by
  rw [incl_numberKet, fockKet_inner]
  simp

/-- **[Number operator norm on the states] `‖N|n⟩‖ = n`.** -/
theorem norm_incl_numberOp_numberKet (n : ℕ) :
    ‖incl (numberOp (numberKet n))‖ = (n : ℝ) := by
  rw [numberOp_numberKet, map_smul, incl_numberKet, norm_smul, fockKet_norm, mul_one]
  simp

/-- **[The number operator is unbounded]** there is no uniform bound on `‖N|n⟩‖` over the unit number states
`‖|n⟩‖ = 1` — the number operator is genuinely unbounded, so it is only *densely* defined (on `fockCore`),
never a continuous operator on all of `ℓ²`.  The ladder operators `a`, `a†` are likewise unbounded
(`‖a|n⟩‖ = √n`, `‖a†|n⟩‖ = √(n+1)`). -/
theorem numberOp_unbounded : ∀ C : ℝ, ∃ n : ℕ, C < ‖incl (numberOp (numberKet n))‖ := by
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact ⟨n, by rw [norm_incl_numberOp_numberKet]; exact hn⟩

/-- **[Unit trace] `Tr(ρ) = Σ_n p_n ⟨n|n⟩ = 1`.**  The thermal density matrix has unit trace in the number
basis. -/
theorem thermalTrace_normalized (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, thermalProbability β E n * (⟪incl (numberKet n), incl (numberKet n)⟫).re = 1 := by
  have hre : ∀ n : ℕ, (⟪incl (numberKet n), incl (numberKet n)⟫ : ℂ).re = 1 := by
    intro n; rw [identity_diag_matrixElement]; simp
  simp_rw [hre, mul_one]
  exact thermalProbability_tsum_one β E h

/-- **[Thermal number trace] `Tr(ρ N) = Σ_n p_n ⟨n|N|n⟩ = boseEinstein(β,E)`.**  The operator trace of the
number in the Hartle–Hawking thermal state, evaluated in the number (Hilbert) basis, is the Bose–Einstein
occupation — Sciama Eq. 18 (`⟨H|Ô|H⟩ = Tr(ρ Ô)`) at the diagonal level, agreeing with the c-number
`thermal_mean_occupation`. -/
theorem thermalTrace_number (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, thermalProbability β E n * (⟪incl (numberKet n), incl (numberOp (numberKet n))⟫).re
      = boseEinstein β E := by
  have hre : ∀ n : ℕ, (⟪incl (numberKet n), incl (numberOp (numberKet n))⟫ : ℂ).re = (n : ℝ) := by
    intro n; rw [numberOp_diag_matrixElement]; simp
  simp_rw [hre]
  rw [← thermal_mean_occupation β E h]
  exact tsum_congr (fun n => mul_comm _ _)

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

end
