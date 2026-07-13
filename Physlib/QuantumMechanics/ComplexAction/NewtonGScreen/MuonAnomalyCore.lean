/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.KinematicsCore
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Muon-anomaly core for the entropic screen: `a = α/(2π)`, `a = 1/sinh²η = K²−1`, `α = 2π(K²−1)`

The light muon `g − 2` chain the Newton-`G` screen derivation uses, free of the
`Dirac.FourSpinorDiracHamiltonian` stack:

* `FirstQuantizedQED.AnomalousMagneticMoment` — Schwinger's one-loop value `a = α/(2π)`;
* `MuonAnomaly.AnomalyRapidity` — the rapidity anomaly `a = 1/sinh²η = K²−1`;
* `MuonAnomaly.AnomalousMagneticMoment` — the numeric bounds at `α = 1/137` vs the measured `a_μ`;
* `MuonAnomaly.SchwingerRapidityEquation` — the isolated equation `α = 2π(K²−1)`.

## References

* J. Schwinger, *On Quantum-Electrodynamics and the Magnetic Moment of the Electron*, Phys. Rev.
  **73** (1948) 416 — the one-loop anomaly `a = α/(2π)`.
* V. Bargmann, L. Michel, V. L. Telegdi, *Precession of the Polarization of Particles Moving in a
  Homogeneous Electromagnetic Field*, Phys. Rev. Lett. **2** (1959) 435 — the storage-ring
  kinematics.
* G. W. Bennett et al. (Muon `g−2`, BNL), Phys. Rev. D **73** (2006) 072003; B. Abi et al. (Muon
  `g−2`, Fermilab), Phys. Rev. Lett. **126** (2021) 141801 — the measured `a_μ = 0.00116592`.

The rapidity anomaly `a = 1/sinh²η` is the **storage-ring g−2 relation** `a = 1/(γ²−1)` with
`γ = cosh η` the Lorentz factor (`cosh²η − sinh²η = 1`); hence `a = K²−1` for `K = coth η`, and
`α = 2π(K²−1)` follows from Schwinger's `a = α/(2π)`. Only the identification of `K = coth η` with
the entanglement Schmidt number is this framework's. -/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

/-- **Schwinger's one-loop anomalous magnetic moment** `a = α/(2π)`. -/
noncomputable def schwingerAnomaly (α : ℝ) : ℝ := α / (2 * Real.pi)

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **The anomalous moment at rapidity `η`** `a = 1/sinh²η = csch²η`. -/
noncomputable def rapidityAnomaly (η : ℝ) : ℝ := 1 / (Real.sinh η) ^ 2

/-- **[g-2 is the Schmidt number squared minus one]** `a = K² − 1 = coth²η − 1`. -/
lemma rapidityAnomaly_eq_schmidt_sq_sub_one (η : ℝ) (hη : 0 < η) :
    rapidityAnomaly η = (schmidtNumber η) ^ 2 - 1 := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  unfold rapidityAnomaly schmidtNumber
  rw [div_pow]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-- **[The rapidity anomaly is the storage-ring g−2 relation]** `a = 1/(γ²−1)` with `γ = cosh η` the
Lorentz factor (`cosh²η − sinh²η = 1`) — the storage-ring anomalous-precession condition,
`γ = cosh η` the boosted-Compton (de Broglie) energy. -/
lemma rapidityAnomaly_eq_inv_lorentz_sq_sub_one (η : ℝ) :
    rapidityAnomaly η = 1 / (Real.cosh η ^ 2 - 1) := by
  have h : Real.cosh η ^ 2 - 1 = Real.sinh η ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq η]
  unfold rapidityAnomaly
  rw [h]

/-- **[Schmidt defect and Lorentz defect are reciprocal]** `K²−1 = 1/(γ²−1)` with `K = coth η`,
`γ = cosh η`: the framework's muon-anomaly Schmidt defect is the reciprocal of the standard
Lorentz defect — both are the anomaly `a`, linking `rapidityAnomaly_eq_schmidt_sq_sub_one`
and `rapidityAnomaly_eq_inv_lorentz_sq_sub_one` with no new algebra. -/
lemma schmidt_defect_eq_inv_lorentz_defect (η : ℝ) (hη : 0 < η) :
    (schmidtNumber η) ^ 2 - 1 = 1 / (Real.cosh η ^ 2 - 1) := by
  rw [← rapidityAnomaly_eq_schmidt_sq_sub_one η hη, rapidityAnomaly_eq_inv_lorentz_sq_sub_one η]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

/-- **[The leading muon anomaly at `α ≈ 1/137`] `0.001161 < a_μ^{(2)} < 0.001162`.** -/
lemma muonSchwingerAnomaly_bounds :
    0.001161 < schwingerAnomaly ((1 : ℝ) / 137) ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.001162 := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold schwingerAnomaly
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith [Real.pi_lt_d4]
  · rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_gt_d4]

/-- **[The leading term is below the measured value] `a_μ^{(2)} < a_μ ≈ 0.00116592`.** -/
lemma muonSchwingerAnomaly_lt_measured : schwingerAnomaly ((1 : ℝ) / 137) < 0.00116592 := by
  have h := muonSchwingerAnomaly_bounds.2
  linarith

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic

/-- **[The isolated equation]** `α = 2π·a(η)` with `a(η) = rapidityAnomaly η`. -/
lemma alpha_isolated (α η : ℝ) (hη : 0 < η) (h : schwingerAnomaly α = rapidityAnomaly η) :
    α = 2 * Real.pi * rapidityAnomaly η := by
  have hs : Real.sinh η ≠ 0 := (Real.sinh_pos_iff.mpr hη).ne'
  unfold schwingerAnomaly rapidityAnomaly at h
  rw [rapidityAnomaly]
  field_simp [Real.pi_ne_zero, hs] at h ⊢
  linarith

/-- **[`α = 2π(K² − 1)`]** the fine-structure constant is `2π` times the Schmidt-number defect. -/
lemma alpha_eq_twoPi_schmidt_defect (α η : ℝ) (hη : 0 < η)
    (h : schwingerAnomaly α = rapidityAnomaly η) :
    α = 2 * Real.pi * ((schmidtNumber η) ^ 2 - 1) := by
  rw [alpha_isolated α η hη h, rapidityAnomaly_eq_schmidt_sq_sub_one η hη]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation

end
