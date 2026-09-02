/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap
public import QuantumInfo.States.Mixed.MState
meta import Zil

/-!
# The thermofield double as the finite Gibbs variational minimizer

Suzuki's TFD amplitude is already `exp (-βE/2)` in `Basic`, where its square is proved equal to
the Matsubara Boltzmann weight `exp (-βE)`.  This module normalizes those squared amplitudes by the
partition function and reuses the finite Gibbs variational carrier.  Thus the reduced diagonal TFD
state is exactly the Gibbs distribution, saturates the variational bound, and is stationary under
the doubled-space hat-Hamiltonian.

This is a finite diagonal statement.  It does not construct a partial trace on an infinite tensor
product, prove purification uniqueness, or establish type-III thermofield theory.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap
open Physlib.QFT.PathIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational

open Basic

variable {ι : Type*}

/-- The reduced diagonal TFD weight: squared thermal amplitude divided by the partition function. -/
noncomputable def tfdReducedWeight (E : ι → ℝ) (β Z : ℝ) (i : ι) : ℝ :=
  thermalWeight β (E i) ^ 2 / Z

/-- Squaring Suzuki's TFD amplitude and normalizing gives the Gibbs weight exactly. -/
theorem tfdReducedWeight_eq_gibbsWeight (E : ι → ℝ) (β Z : ℝ) :
    tfdReducedWeight E β Z = fun i => Real.exp (-(β * E i)) / Z := by
  funext i
  rw [tfdReducedWeight, thermalWeight_sq]
  rfl

theorem tfdReducedWeight_pos (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z) (i : ι) :
    0 < tfdReducedWeight E β Z i := by
  rw [tfdReducedWeight_eq_gibbsWeight]
  exact div_pos (Real.exp_pos _) hZ

theorem tfdReducedWeight_normalized [Fintype ι] (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    ∑ i, tfdReducedWeight E β Z i = 1 := by
  rw [tfdReducedWeight_eq_gibbsWeight, ← Finset.sum_div, hpartition, div_self hZ.ne']

/-- The finite TFD energy data, packaged as the common Gibbs variational carrier. -/
noncomputable def tfdVariationalSystem [Fintype ι] (E : ι → ℝ) (β Z : ℝ)
    (hβ : 0 < β) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    FiniteGibbsVariationalSystem ι where
  energy := E
  beta := β
  partition := Z
  beta_pos := hβ
  partition_pos := hZ
  partition_eq := hpartition

/-- **The reduced TFD state is the variational minimizer.**  Its free energy equals the Gibbs
free energy because its probabilities are exactly the normalized squared TFD amplitudes. -/
theorem tfdReducedState_saturates_gibbs [Fintype ι] (E : ι → ℝ) (β Z : ℝ)
    (hβ : 0 < β) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    finiteTrialFreeEnergy (tfdReducedWeight E β Z) E β = gibbsFreeEnergy Z β := by
  rw [tfdReducedWeight_eq_gibbsWeight]
  exact gibbsState_saturates E β Z hZ hβ hpartition

/-- Every positive normalized trial state has free energy at least that of the reduced TFD state. -/
theorem tfdReducedState_minimizes_freeEnergy [Fintype ι]
    (E : ι → ℝ) (p : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hβ : 0 < β) (hZ : 0 < Z)
    (hnorm : ∑ i, p i = 1)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    finiteTrialFreeEnergy (tfdReducedWeight E β Z) E β ≤ finiteTrialFreeEnergy p E β := by
  rw [tfdReducedState_saturates_gibbs E β Z hβ hZ hpartition]
  exact trialFreeEnergy_ge_gibbs p E β Z hp hZ hnorm hβ hpartition

/-- The excess above the TFD minimizer is exactly the relative-entropy free-energy gap. -/
theorem trial_sub_tfd_eq_relativeEntropy_gap [Fintype ι]
    (E : ι → ℝ) (p : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hβ : 0 < β) (hZ : 0 < Z)
    (hnorm : ∑ i, p i = 1)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    finiteTrialFreeEnergy p E β - finiteTrialFreeEnergy (tfdReducedWeight E β Z) E β =
      freeEnergyGap p (tfdReducedWeight E β Z) β := by
  rw [tfdReducedState_saturates_gibbs E β Z hβ hZ hpartition,
    tfdReducedWeight_eq_gibbsWeight]
  exact trialFreeEnergy_sub_gibbs_eq_gap p E β Z hp hZ hnorm hβ

/-! ## Exact finite purification and partial trace -/

/-- The normalized Gibbs distribution represented by the squared TFD amplitudes. -/
noncomputable def tfdReducedDistribution [Fintype ι]
    (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (- (β * E i)) = Z) : ProbDistribution ι :=
  ProbDistribution.mk' (tfdReducedWeight E β Z)
    (fun i => (tfdReducedWeight_pos E β Z hZ i).le)
    (tfdReducedWeight_normalized E β Z hZ hpartition)

private theorem norm_sq_sqrt_tfdReducedWeight (E : ι → ℝ) (β Z : ℝ)
    (hZ : 0 < Z) (i : ι) :
    ‖((Real.sqrt (tfdReducedWeight E β Z i) : ℝ) : ℂ)‖ ^ 2 =
      tfdReducedWeight E β Z i := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (tfdReducedWeight_pos E β Z hZ i).le]

/-- The finite thermofield-double purification
`|Ωβ⟩ = ∑ᵢ √pᵢ |i⟩⊗|i⟩`, constructed as an actual normalized ket. -/
noncomputable def tfdPurificationKet [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (- (β * E i)) = Z) : Ket (ι × ι) where
  vec p := if p.1 = p.2 then ((Real.sqrt (tfdReducedWeight E β Z p.1) : ℝ) : ℂ) else 0
  normalized' := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ i, ∑ j, ‖if i = j then ((Real.sqrt (tfdReducedWeight E β Z i) : ℝ) : ℂ)
          else 0‖ ^ 2 = ∑ i, tfdReducedWeight E β Z i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp [Real.sq_sqrt (tfdReducedWeight_pos E β Z hZ i).le]
        · intro j _ hji
          simp [Ne.symm hji]
        · simp
      _ = 1 := tfdReducedWeight_normalized E β Z hZ hpartition

/-- The right partial trace of the pure TFD ket is exactly the classical Gibbs density matrix. -/
theorem tfdPurification_traceRight [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (- (β * E i)) = Z) :
    (MState.pure (tfdPurificationKet E β Z hZ hpartition)).traceRight =
      MState.ofClassical (tfdReducedDistribution E β Z hZ hpartition) := by
  apply MState.ext_m
  ext i j
  change (∑ k, (if i = k then ((Real.sqrt (tfdReducedWeight E β Z i) : ℝ) : ℂ) else 0) *
      (starRingEnd ℂ) (if j = k then ((Real.sqrt (tfdReducedWeight E β Z j) : ℝ) : ℂ) else 0)) =
    if i = j then (tfdReducedWeight E β Z i : ℂ) else 0
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp only [if_pos]
      rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal]
      have hs : Real.sqrt (tfdReducedWeight E β Z i) *
          Real.sqrt (tfdReducedWeight E β Z i) = tfdReducedWeight E β Z i := by
        simpa [pow_two] using Real.sq_sqrt (tfdReducedWeight_pos E β Z hZ i).le
      exact_mod_cast hs
    · intro k _ hki
      simp [Ne.symm hki]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · have hjk : j ≠ k := fun hjk => hij (hik.trans hjk.symm)
      simp [hik, hjk]
    · simp [hik]

/-- By symmetry of the TFD ket, tracing out the left factor gives the same Gibbs state. -/
theorem tfdPurification_traceLeft [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hpartition : ∑ i, Real.exp (- (β * E i)) = Z) :
    (MState.pure (tfdPurificationKet E β Z hZ hpartition)).traceLeft =
      MState.ofClassical (tfdReducedDistribution E β Z hZ hpartition) := by
  apply MState.ext_m
  ext i j
  change (∑ k, (if k = i then ((Real.sqrt (tfdReducedWeight E β Z k) : ℝ) : ℂ) else 0) *
      (starRingEnd ℂ) (if k = j then ((Real.sqrt (tfdReducedWeight E β Z k) : ℝ) : ℂ) else 0)) =
    if i = j then (tfdReducedWeight E β Z i : ℂ) else 0
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp only [if_pos]
      rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal]
      have hs : Real.sqrt (tfdReducedWeight E β Z i) *
          Real.sqrt (tfdReducedWeight E β Z i) = tfdReducedWeight E β Z i := by
        simpa [pow_two] using Real.sq_sqrt (tfdReducedWeight_pos E β Z hZ i).le
      exact_mod_cast hs
    · intro k _ hki
      simp [hki]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · have hkj : k ≠ j := fun hkj => hij (hki.symm.trans hkj)
      simp [hki, hij]
    · simp [hki]

/-! ## Wedge modular/KMS specialization -/

/-- The reduced TFD probabilities for the two-level wedge modular Hamiltonian are definitionally
the Gibbs weights of the existing Bisognano--Wichmann/Kay--Wald variational system. -/
theorem wedgeTfdReducedWeight_eq_kmsGibbsWeight (κ ℏ : ℝ) :
    tfdReducedWeight (![0, modularHamEigenvalue κ ℏ]) 1
        (1 + wedgeModularEigenvalue κ ℏ) =
      (wedgeKmsVariationalSystem κ ℏ).gibbsWeight := by
  rw [tfdReducedWeight_eq_gibbsWeight]
  rfl

/-- The finite wedge thermofield ket has the wedge-KMS Gibbs density as its computed right
partial trace.  This is the exact finite density-matrix bridge between TFD purification and the
repository's modular/KMS variational carrier. -/
theorem wedgeTfdPurification_traceRight (κ ℏ : ℝ) :
    (MState.pure (tfdPurificationKet (![0, modularHamEigenvalue κ ℏ]) 1
      (1 + wedgeModularEigenvalue κ ℏ)
      (wedgeKmsVariationalSystem κ ℏ).partition_pos (wedgeKmsPartition_eq κ ℏ))).traceRight =
    MState.ofClassical (tfdReducedDistribution (![0, modularHamEigenvalue κ ℏ]) 1
      (1 + wedgeModularEigenvalue κ ℏ)
      (wedgeKmsVariationalSystem κ ℏ).partition_pos (wedgeKmsPartition_eq κ ℏ)) :=
  tfdPurification_traceRight (![0, modularHamEigenvalue κ ℏ]) 1
    (1 + wedgeModularEigenvalue κ ℏ)
    (wedgeKmsVariationalSystem κ ℏ).partition_pos (wedgeKmsPartition_eq κ ℏ)

/-- **TFD = wedge-KMS variational vacuum in the finite carrier.**  The partial trace's probability
law saturates the wedge Gibbs free energy, while every positive normalized trial law lies above it.
This packages purification and finite vacuum passivity as statements about the same state. -/
theorem wedgeTfd_is_finiteVacuumPassive (p : Fin 2 → ℝ) (κ ℏ : ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : ∑ i, p i = 1) :
    finiteTrialFreeEnergy
        (tfdReducedWeight (![0, modularHamEigenvalue κ ℏ]) 1
          (1 + wedgeModularEigenvalue κ ℏ))
        (![0, modularHamEigenvalue κ ℏ]) 1 =
        gibbsFreeEnergy (1 + wedgeModularEigenvalue κ ℏ) 1 ∧
      gibbsFreeEnergy (1 + wedgeModularEigenvalue κ ℏ) 1 ≤
        finiteTrialFreeEnergy p (![0, modularHamEigenvalue κ ℏ]) 1 := by
  exact ⟨tfdReducedState_saturates_gibbs (![0, modularHamEigenvalue κ ℏ]) 1
      (1 + wedgeModularEigenvalue κ ℏ) (by norm_num)
      (wedgeKmsVariationalSystem κ ℏ).partition_pos (wedgeKmsPartition_eq κ ℏ),
    wedgeKms_freeEnergy_minimized p κ ℏ hp hnorm⟩

section MatrixEquilibrium

variable {n : ℕ}

/-- The diagonal Hamiltonian in the energy eigenbasis used by the finite TFD carrier. -/
noncomputable def tfdHamiltonianMatrix (E : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (E i : ℂ)

/-- The reduced TFD density matrix in the same energy eigenbasis. -/
noncomputable def tfdReducedDensityMatrix (E : Fin n → ℝ) (β Z : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (tfdReducedWeight E β Z i : ℂ)

/-- **Dynamical equilibrium.**  The reduced TFD Gibbs density is annihilated by Suzuki's
hat-Hamiltonian because both it and the Hamiltonian are diagonal in the selected energy basis. -/
theorem tfdReducedDensity_hatHamiltonian_stationary (E : Fin n → ℝ) (β Z : ℝ) :
    hatHamiltonian (tfdHamiltonianMatrix E) (tfdReducedDensityMatrix E β Z) = 0 := by
  rw [hatHamiltonian_apply]
  simp [tfdHamiltonianMatrix, tfdReducedDensityMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

end MatrixEquilibrium

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedWeight_eq_gibbsWeight where
  formalizes @ "claim:the-normalized-squared-suzuki-thermofield-amplitude-is-exactly-the-gibbs-weight",
  supported_by @ "paper:suzuki-thermo-field-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedState_minimizes_freeEnergy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedState_saturates_gibbs",
  formalizes @ "claim:the-finite-diagonal-thermofield-double-reduced-state-minimizes-the-gibbs-free-energy",
  requires @ "claim:the-normalized-squared-suzuki-thermofield-amplitude-is-exactly-the-gibbs-weight",
  caveat @ "claim:finite-diagonal-reduced-state-only-not-an-infinite-tensor-product-partial-trace-or-type-three-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.trial_sub_tfd_eq_relativeEntropy_gap where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedWeight_eq_gibbsWeight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap",
  formalizes @ "claim:the-trial-free-energy-excess-above-the-tfd-minimizer-is-exactly-scaled-relative-entropy"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedDensity_hatHamiltonian_stationary where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.hatHamiltonian_apply",
  formalizes @ "claim:the-finite-diagonal-tfd-gibbs-density-is-stationary-under-the-suzuki-hat-hamiltonian",
  caveat @ "claim:stationarity-is-in-the-selected-common-energy-eigenbasis"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdPurification_traceRight where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:the-finite-thermofield-double-is-an-actual-purification-of-the-gibbs-state",
  requires @ "claim:the-normalized-squared-suzuki-thermofield-amplitude-is-exactly-the-gibbs-weight",
  caveat @ "claim:exact-finite-dimensional-density-matrix-partial-trace-not-an-infinite-type-three-factorization"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.wedgeTfd_is_finiteVacuumPassive where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems.DynamicalTimeReversalGaugeModel.partition_pos",
  formalizes @ "claim:the-finite-wedge-tfd-purification-reduces-to-the-kms-gibbs-minimizer-and-is-vacuum-passive",
  requires @ "claim:the-finite-thermofield-double-is-an-actual-purification-of-the-gibbs-state",
  requires @ "claim:wedge-kms-state-minimizes-finite-free-energy-and-has-nonnegative-relative-entropy-deficit",
  caveat @ "claim:finite-two-level-diagonal-wedge-shadow-not-type-three-complete-passivity"

zil_file_contract physlib.tfdGibbsVariational where
  promises "Suzuki's squared thermofield amplitudes, after partition normalization, are exactly the finite Gibbs weights.  The normalized thermofield ket is an actual purification whose two computed partial traces are that Gibbs density; the reduced state saturates and minimizes the Gibbs variational functional, its excess is measured by relative entropy, and it is stationary under the TFD hat-Hamiltonian."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.thermalWeight_sq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.hatHamiltonian",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.gibbsState_saturates"]
  forbids_substitutes ["an infinite-dimensional or type-III partial trace theorem",
    "uniqueness of the variational minimizer beyond the finite positive diagonal carrier"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedWeight_eq_gibbsWeight,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdPurification_traceRight,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdPurification_traceLeft,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.wedgeTfd_is_finiteVacuumPassive,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedState_minimizes_freeEnergy,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.trial_sub_tfd_eq_relativeEntropy_gap,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational.tfdReducedDensity_hatHamiltonian_stationary]

/- ZIL-END -/
