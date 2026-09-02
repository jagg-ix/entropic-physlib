/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive

/-!
# The Boltzmann operator `e^{-βH}` and the Gibbs state `ρ = e^{-βH}/Z`

The (unnormalized) thermal operator `e^{-βH}`, built as the diagonal multiplier by the Boltzmann factors
`e^{-βE_n} = e^{-βω(n+½)}`, and the identification of the Hartle–Hawking density matrix with the **normalized
Boltzmann operator**: `ρ = e^{-βH}/Z`, the defining relation of the Gibbs state.

* `boltzmannOp β ω` — `e^{-βH} : ℓ² →L[ℂ] ℓ²`, the diagonal multiplier by `e^{-βω(n+½)}`.
* `boltzmannOp_apply_fockKet` — `e^{-βH}|n⟩ = e^{-βω(n+½)}|n⟩` (the Boltzmann factors as eigenvalues).
* `partitionFunction` — `Z = e^{-βω/2}/(1-e^{-βω}) = Σₙ e^{-βω(n+½)}`.
* `densityOp_eq_boltzmann` — `ρ = Z⁻¹ · e^{-βH}`: the density matrix is the normalized Boltzmann operator.

Honest scope: the diagonal Boltzmann operator and its identification `ρ = e^{-βH}/Z` (with `H = ℏω(N+½)`,
`E = ω`).  `Z` is the closed-form geometric partition function.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBoltzmannOperator

open scoped ENNReal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive

/-- **The Boltzmann factor** `e^{-βE_n} = e^{-βω(n+½)}` (the `n`-th eigenvalue of `e^{-βH}`). -/
def boltzmannFactor (β ω : ℝ) (n : ℕ) : ℝ := Real.exp (-(β * ω * ((n : ℝ) + 1 / 2)))

/-- **The partition function** `Z = e^{-βω/2}/(1 - e^{-βω})`. -/
def partitionFunction (β ω : ℝ) : ℝ := Real.exp (-(β * ω / 2)) * (1 - Real.exp (-(β * ω)))⁻¹

/-- **[Gibbs = normalized Boltzmann, coordinate form] `p_n = Z⁻¹ e^{-βω(n+½)}`.** -/
theorem boltzmann_thermalProbability (β ω : ℝ) (h : 0 < β * ω) (n : ℕ) :
    thermalProbability β ω n = (partitionFunction β ω)⁻¹ * boltzmannFactor β ω n := by
  have hne : (1 : ℝ) - Real.exp (-(β * ω)) ≠ 0 := by have := exp_neg_lt_one β ω h; linarith
  have he : Real.exp (-(β * ω / 2)) ≠ 0 := Real.exp_ne_zero _
  have hexp : boltzmannFactor β ω n = Real.exp (-(β * ω / 2)) * Real.exp (-(β * ω)) ^ n := by
    rw [boltzmannFactor, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [thermalProbability, partitionFunction, hexp]
  field_simp

/-- **The Boltzmann factors as a bounded `ℓ^∞` diagonal.** -/
def boltzmannDiag (β ω : ℝ) (h : 0 < β * ω) : lp (fun _ : ℕ => ℂ) ∞ :=
  ⟨fun n => (boltzmannFactor β ω n : ℂ), by
    show Memℓp (fun n => (boltzmannFactor β ω n : ℂ)) ∞
    rw [memℓp_infty_iff]
    refine ⟨1, ?_⟩
    rintro x ⟨n, rfl⟩
    simp only [boltzmannFactor, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have hpos : 0 ≤ β * ω * ((n : ℝ) + 1 / 2) := mul_nonneg h.le (by positivity)
    linarith⟩

@[simp] theorem boltzmannDiag_coe (β ω : ℝ) (h : 0 < β * ω) (n : ℕ) :
    (boltzmannDiag β ω h : ∀ _ : ℕ, ℂ) n = (boltzmannFactor β ω n : ℂ) := rfl

/-- **The Boltzmann operator** `e^{-βH}`: the diagonal multiplier by the Boltzmann factors. -/
def boltzmannOp (β ω : ℝ) (h : 0 < β * ω) : FockHilbert →L[ℂ] FockHilbert :=
  lp.holderL 2 (fun _ : ℕ => ContinuousLinearMap.mul ℂ ℂ) mul_norm_le (boltzmannDiag β ω h)

/-- **[Diagonal action] `(e^{-βH}ψ)_n = e^{-βω(n+½)} ψ_n`.** -/
theorem boltzmannOp_apply_coe (β ω : ℝ) (h : 0 < β * ω) (ψ : FockHilbert) (n : ℕ) :
    (boltzmannOp β ω h ψ) n = (boltzmannFactor β ω n : ℂ) * ψ n := by
  simp only [boltzmannOp, lp.holderL, LinearMap.mkContinuous₂_apply, lp.holderₗ_apply_apply_coe,
    ContinuousLinearMap.mul_apply', boltzmannDiag_coe]

/-- **[Boltzmann eigenstates] `e^{-βH}|n⟩ = e^{-βω(n+½)}|n⟩`.** -/
theorem boltzmannOp_apply_fockKet (β ω : ℝ) (h : 0 < β * ω) (n : ℕ) :
    boltzmannOp β ω h (fockKet n) = (boltzmannFactor β ω n : ℂ) • fockKet n := by
  apply lp.ext
  funext i
  rw [boltzmannOp_apply_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, fockKet, lp.coeFn_single]
  rcases eq_or_ne i n with hi | hi
  · subst hi; simp
  · rw [Pi.single_eq_of_ne hi]; ring

/-- **[Gibbs state = normalized Boltzmann operator] `ρ = Z⁻¹ · e^{-βH} = e^{-βH}/Z`.**  The Hartle–Hawking
density matrix is the operator exponential of the Hamiltonian, normalized by the partition function. -/
theorem densityOp_eq_boltzmann (β ω : ℝ) (h : 0 < β * ω) :
    densityOp β ω h = ((partitionFunction β ω)⁻¹ : ℂ) • boltzmannOp β ω h := by
  ext ψ : 1
  apply lp.ext
  funext n
  rw [densityOp_apply_coe, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    boltzmannOp_apply_coe, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← boltzmann_thermalProbability β ω h n]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBoltzmannOperator

end
