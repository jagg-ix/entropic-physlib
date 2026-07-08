/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential

/-!
# Bohmian minimal coupling and the Aharonov-Bohm phase

Ports the Bohm/Aharonov material from `catept-main` in a physlib-native
form and connects it to the existing complex-action/Bohm infrastructure.

Source material:

* `CATEPTMain.Integration.QuantumInfoFisherBridge.ab_phase_shift_invariant`:
  the Aharonov-Bohm phase difference is invariant under a global phase shift.
* `CATEPTMain.Domains.Adapters.BohmianEM.bohmianEMAction`: the minimally
  coupled Bohmian-EM imaginary action is the displaced Gaussian
  `sum_mu (v_mu - A_mu)^2 / 2`.
* `CATEPTMain.Integration.GravitasBridge.bohmianEM_action_expansion`:
  the displaced square expands as free kinetic action minus the cross term
  plus the gauge-potential square.

The connection to the rest of physlib is the existing
`GravLapse.BohmQuantumPotential`: the AB phase is a pure
complex-action phase (`S_I = 0`), while the Bohmian-EM displaced action is
an imaginary action feeding both the Born damping `bornWeight` and the
de Broglie-Bohm readout `bohmQuantumPotential`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.BohmMadelung.BohmAharonovPhase

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential

/-! ## §A — Aharonov-Bohm phase as a gauge-invariant phase difference -/

/-- The Aharonov-Bohm phase difference between two interferometer arms. -/
def abPhase (φ₁ φ₂ : ℝ) : ℝ := φ₁ - φ₂

/-- The unit-modulus Aharonov-Bohm phase weight. -/
noncomputable def abPhaseWeight (φ₁ φ₂ : ℝ) : ℂ :=
  Complex.exp (((abPhase φ₁ φ₂ : ℝ) : ℂ) * Complex.I)

/-- Port of `ab_phase_shift_invariant`: a global phase shift cancels from the
Aharonov-Bohm phase difference. -/
theorem abPhase_globalShift_invariant (φ₁ φ₂ δ : ℝ) :
    abPhase (φ₁ + δ) (φ₂ + δ) = abPhase φ₁ φ₂ := by
  unfold abPhase
  ring

/-- The AB phase weight is invariant under the same global phase shift. -/
theorem abPhaseWeight_globalShift_invariant (φ₁ φ₂ δ : ℝ) :
    abPhaseWeight (φ₁ + δ) (φ₂ + δ) = abPhaseWeight φ₁ φ₂ := by
  unfold abPhaseWeight
  rw [abPhase_globalShift_invariant]

/-- The AB phase is exactly the reversible complex-action phase with `S_I = 0`. -/
theorem abPhaseWeight_eq_complexActionPathIntegralWeight
    (φ₁ φ₂ ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    abPhaseWeight φ₁ φ₂ =
      complexActionPathIntegralWeight (ℏ * abPhase φ₁ φ₂) 0 ℏ := by
  unfold abPhaseWeight complexActionPathIntegralWeight
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  congr 1
  push_cast
  field_simp
  ring

/-- The AB phase inserted as the real Madelung action is globally phase-shift
invariant.  The imaginary action `S_I` is untouched. -/
theorem abPhase_madelungAmplitude_globalShift_invariant
    (φ₁ φ₂ δ S_I ℏ : ℝ) :
    madelungAmplitude (ℏ * abPhase (φ₁ + δ) (φ₂ + δ)) S_I ℏ =
      madelungAmplitude (ℏ * abPhase φ₁ φ₂) S_I ℏ := by
  rw [abPhase_globalShift_invariant]

/-! ## §B — Bohmian-EM displaced Gaussian action -/

/-- Four-component Bohmian velocity / background-potential configuration. -/
abbrev BohmianEMConfig := Fin 4 → ℝ

/-- Port of the Bohmian-EM displaced Gaussian imaginary action:
`S_I(v) = sum_mu (v_mu - A_mu)^2 / 2`. -/
noncomputable def bohmianEMAction (A v : BohmianEMConfig) : ℝ :=
  (∑ μ : Fin 4, (v μ - A μ) ^ 2) / 2

/-- The Bohmian-EM imaginary action is nonnegative. -/
theorem bohmianEMAction_nonneg (A v : BohmianEMConfig) :
    0 ≤ bohmianEMAction A v := by
  unfold bohmianEMAction
  exact div_nonneg (Finset.sum_nonneg fun μ _ => sq_nonneg (v μ - A μ)) (by norm_num)

/-- At zero background potential, the action is the free Bohmian kinetic square. -/
theorem bohmianEMAction_zero_background (v : BohmianEMConfig) :
    bohmianEMAction (fun _ => 0) v = (∑ μ : Fin 4, v μ ^ 2) / 2 := by
  unfold bohmianEMAction
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Expanded form of the minimally coupled Bohmian action:
`|v - A|^2/2 = |v|^2/2 - <v,A> + |A|^2/2`. -/
theorem bohmianEMAction_expansion (A v : BohmianEMConfig) :
    bohmianEMAction A v =
      (∑ μ : Fin 4, v μ ^ 2) / 2
        - (∑ μ : Fin 4, v μ * A μ)
        + (∑ μ : Fin 4, A μ ^ 2) / 2 := by
  unfold bohmianEMAction
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

/-- The action is invariant under reflection through the background potential:
`v ↦ 2A - v`. -/
theorem bohmianEMAction_reflection_invariant (A v : BohmianEMConfig) :
    bohmianEMAction A (fun μ => 2 * A μ - v μ) = bohmianEMAction A v := by
  unfold bohmianEMAction
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-! ## §C — Link to Bohmian quantum potential and Born damping -/

/-- The minimally coupled Bohmian action feeds a nonnegative dBB quantum
potential readout. -/
theorem bohmianEM_quantumPotential_nonneg
    (A v : BohmianEMConfig) (ℏ m : ℝ) (hℏ : 0 ≤ ℏ) (hm : 0 < m) :
    0 ≤ bohmQuantumPotential (bohmianEMAction A v) ℏ m :=
  bohmQuantumPotential_nonneg _ ℏ m (bohmianEMAction_nonneg A v) hℏ hm

/-- The Bohmian-EM Born damping is bounded by `1` when `ℏ > 0`, because its
imaginary action is nonnegative. -/
theorem bohmianEM_bornWeight_le_one
    (A v : BohmianEMConfig) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    bornWeight (bohmianEMAction A v) ℏ ≤ 1 := by
  unfold bornWeight
  exact Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith [bohmianEMAction_nonneg A v]) hℏ.le)

/-- The Madelung pilot wave with AB real phase and Bohmian-EM imaginary action
has Born modulus `bornWeight (S_I)`. -/
theorem abBohm_madelungAmplitude_norm
    (φ₁ φ₂ ℏ : ℝ) (A v : BohmianEMConfig) :
    ‖madelungAmplitude (ℏ * abPhase φ₁ φ₂) (bohmianEMAction A v) ℏ‖ =
      bornWeight (bohmianEMAction A v) ℏ :=
  madelungAmplitude_norm _ _ _

/-- Main result: Aharonov-Bohm phase invariance and minimally coupled Bohmian
imaginary action share the same complex-action/Born-weight structure. -/
theorem bohm_aharonov_phase_synthesis
    (φ₁ φ₂ δ ℏ m : ℝ) (hℏ : 0 < ℏ) (hm : 0 < m) (A v : BohmianEMConfig) :
    abPhase (φ₁ + δ) (φ₂ + δ) = abPhase φ₁ φ₂
      ∧ abPhaseWeight φ₁ φ₂ =
        complexActionPathIntegralWeight (ℏ * abPhase φ₁ φ₂) 0 ℏ
      ∧ 0 ≤ bohmianEMAction A v
      ∧ 0 ≤ bohmQuantumPotential (bohmianEMAction A v) ℏ m
      ∧ ‖madelungAmplitude (ℏ * abPhase φ₁ φ₂) (bohmianEMAction A v) ℏ‖ =
        bornWeight (bohmianEMAction A v) ℏ := by
  exact
    ⟨abPhase_globalShift_invariant φ₁ φ₂ δ,
      abPhaseWeight_eq_complexActionPathIntegralWeight φ₁ φ₂ ℏ hℏ.ne',
      bohmianEMAction_nonneg A v,
      bohmianEM_quantumPotential_nonneg A v ℏ m hℏ.le hm,
      abBohm_madelungAmplitude_norm φ₁ φ₂ ℏ A v⟩

end Physlib.QuantumMechanics.ComplexAction.BohmMadelung.BohmAharonovPhase

end
