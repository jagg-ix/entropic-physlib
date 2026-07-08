/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinStatistics
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

/-!
# Hopf fiber phases and the Kálnay Bose-bilinear fermion

This file links the spinor Hopf-fibration bridge to the concrete Kálnay Bose-bilinear
realization.

`Hopf.FibrationSpinStatistics` proves that the spin-`1/2` ribbon sign `-1` is Hopf
fiber data: it changes the spinor representative but not the Hopf/Bloch/Poincare base
point. `BoseFermiOperatorAlgebra.BoseBilinearRealization` proves that the concrete single-boson-sector
Bose bilinear `boseBilinear = a† b` is a genuine fermion mode.

The bridge here is the common `S¹` phase action:

* multiplying the spinor by a unit phase preserves `hopfBase`;
* multiplying the concrete Kálnay bilinear by the same unit phase preserves the CAR and
  preserves the fermion number projector;
* at the fermion ribbon phase `ribbonTwist (1/2) = -1`, this gives the exact connection
  between the Hopf fiber sign, the spin-`1/2` double cover, and the Kálnay
  Bose-bilinear fermion witness.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationKalnayBoseBilinear

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
open Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

/-! ## §A — the same unit phase preserves Hopf base and Kálnay CAR -/

/-- The Kálnay Bose bilinear with a global complex phase. -/
def phaseScaledBoseBilinear (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  u • boseBilinear

/-- **[Unit phase preserves the concrete Kálnay CAR witness]**. The Kálnay
Bose-bilinear fermion mode remains a fermion mode after multiplication by any unit
complex phase. -/
theorem phaseScaledBoseBilinear_isFermionMode (u : ℂ) (hu : star u * u = 1) :
    IsFermionMode (phaseScaledBoseBilinear u) := by
  constructor
  · simp [phaseScaledBoseBilinear, boseBilinear_mul_self]
  · have hu' : u * star u = 1 := by simpa [mul_comm] using hu
    simp only [phaseScaledBoseBilinear, star_smul, smul_mul_smul_comm]
    rw [hu', hu, one_smul, one_smul]
    exact boseBilinear_isFermionMode.2

/-- **[Unit phase preserves the Kálnay number projector]**. The global phase acts on
the field representative, not on the observable `n = f†f`. -/
theorem fermionNumber_phaseScaledBoseBilinear (u : ℂ) (hu : star u * u = 1) :
    fermionNumber (phaseScaledBoseBilinear u) = fermionNumber boseBilinear := by
  have hu' : u * star u = 1 := by simpa [mul_comm] using hu
  unfold fermionNumber phaseScaledBoseBilinear
  simp only [star_smul, smul_mul_smul_comm]
  rw [hu, one_smul]

/-- **[Hopf/Kálnay common phase action]**. A unit `S¹` phase simultaneously preserves
the Hopf base of a spinor and the concrete Kálnay Bose-bilinear CAR realization. -/
theorem hopf_kalnay_common_unit_phase (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    hopfBase (phaseRotate u χ) = hopfBase χ
      ∧ IsFermionMode (phaseScaledBoseBilinear u)
      ∧ fermionNumber (phaseScaledBoseBilinear u) = fermionNumber boseBilinear :=
  ⟨hopfBase_phase_invariant u χ hu, phaseScaledBoseBilinear_isFermionMode u hu,
    fermionNumber_phaseScaledBoseBilinear u hu⟩

/-! ## §B — the fermion ribbon phase and the concrete Bose-bilinear witness -/

/-- **[The fermion ribbon phase preserves the Kálnay Bose-bilinear CAR]**. Since
`ribbonTwist (1/2) = -1`, the Hopf/ribbon fermion sign is a unit phase on the concrete
Bose-bilinear fermion witness. -/
theorem ribbonTwist_phaseScaledBoseBilinear_isFermionMode :
    IsFermionMode (phaseScaledBoseBilinear (ribbonTwist (1 / 2))) := by
  apply phaseScaledBoseBilinear_isFermionMode
  rw [ribbonTwist_fermion]
  exact neg_one_unitPhase

/-- **[The fermion ribbon phase preserves the Kálnay number projector]**. -/
theorem fermionNumber_ribbonTwist_phaseScaledBoseBilinear :
    fermionNumber (phaseScaledBoseBilinear (ribbonTwist (1 / 2)))
      = fermionNumber boseBilinear := by
  apply fermionNumber_phaseScaledBoseBilinear
  rw [ribbonTwist_fermion]
  exact neg_one_unitPhase

/-- **[Hopf ribbon sign + Kálnay Bose-bilinear realization]**. The spin-`1/2`
ribbon phase is invisible on the Hopf base and preserves the concrete Kálnay
Bose-bilinear CAR witness, whose number operator is the checked rank-one projector. -/
theorem hopf_ribbonTwist_kalnay_bose_bilinear_realization (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate (ribbonTwist (1 / 2)) χ) = hopfBase χ
      ∧ spinHalfRotation (2 * Real.pi) *ᵥ χ = phaseRotate (ribbonTwist (1 / 2)) χ
      ∧ IsFermionMode (phaseScaledBoseBilinear (ribbonTwist (1 / 2)))
      ∧ fermionNumber (phaseScaledBoseBilinear (ribbonTwist (1 / 2))) = !![0, 0; 0, 1] :=
  ⟨hopfBase_ribbonTwist_fermion_invariant χ,
    by
      rw [ribbonTwist_fermion]
      exact spinHalfRotation_two_pi_mulVec χ,
    ribbonTwist_phaseScaledBoseBilinear_isFermionMode,
    by
      rw [fermionNumber_ribbonTwist_phaseScaledBoseBilinear]
      exact fermionNumber_boseBilinear⟩

/-- **[Hopf/Kálnay/spin-statistics assembled]**. The Kálnay Bose-bilinear fermion
is the concrete CAR witness used by the spin-statistics parity structure, while the same
fermion sign is the Hopf fiber phase and the spin-`1/2` `2π` sign. -/
theorem hopf_kalnay_spin_statistics_bilinear_link
    (G : Matrix (Fin 2) (Fin 2) ℂ) (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate (ribbonTwist (1 / 2)) χ) = hopfBase χ
      ∧ spinHalfRotation (2 * Real.pi) *ᵥ χ = phaseRotate (ribbonTwist (1 / 2)) χ
      ∧ spinRotation G (2 * Real.pi) = -1
      ∧ fermionParity boseBilinear * fermionParity boseBilinear = 1
      ∧ fermionParity boseBilinear * boseBilinear = -(boseBilinear * fermionParity boseBilinear) := by
  let hHopf := hopf_ribbonTwist_kalnay_bose_bilinear_realization χ
  let hSpin := spin_statistics_connection G boseBilinear boseBilinear_isFermionMode
  exact ⟨hHopf.1, hHopf.2.1, hSpin.1, hSpin.2.1, hSpin.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationKalnayBoseBilinear

end
