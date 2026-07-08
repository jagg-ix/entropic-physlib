/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

/-!
# Hopf fibers, the fermion ribbon twist, and the spin-1/2 double cover

This file connects the spinor Hopf map to the repo's two existing spin-statistics structures:

* `Hopf.FibrationSpinorMap`: the Hopf base point is the Stokes/Bloch/Poincare vector of a
  two-spinor and is invariant under unit complex phases.
* `Hopf.ChargeConjugationRibbonTwist`: the spin-`1/2` ribbon twist is the fermion sign `-1`.
* `Hopf.SpinHalfDoubleCover`: a `2π` spinor rotation is `-1`, while a `4π` rotation is `1`.

The result is the precise, checkable content behind the tau notes' "Hopf fibration explains
720-degree spinor rotation" statement:

* a `2π` spinor rotation changes the fiber phase by `-1`;
* the Hopf base point is unchanged, because the global phase is `S¹` fiber data;
* a `4π` rotation returns the spinor itself.

No knot/topological-electron claim is made here; this is only the standard spinor/Hopf
double-cover statement.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinStatistics

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

/-! ## §A — the fermion sign is Hopf-fiber data -/

lemma neg_one_unitPhase : star (-1 : ℂ) * (-1 : ℂ) = 1 := by norm_num

lemma one_unitPhase : star (1 : ℂ) * (1 : ℂ) = 1 := by norm_num

/-- **[`-1` phase rotation is spinor negation]**. -/
theorem phaseRotate_neg_one (χ : Fin 2 → ℂ) : phaseRotate (-1) χ = -χ := by
  ext i
  simp [phaseRotate]

/-- **[`1` phase rotation is the identity]**. -/
theorem phaseRotate_one (χ : Fin 2 → ℂ) : phaseRotate 1 χ = χ := by
  ext i
  simp [phaseRotate]

/-- **[The fermion sign is invisible on the Hopf base]**. Multiplication by `-1` changes the
spinor fiber representative, but not the Bloch/Poincare base point. -/
theorem hopfBase_neg_phase_invariant (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate (-1) χ) = hopfBase χ :=
  hopfBase_phase_invariant (-1) χ neg_one_unitPhase

/-- **[The trivial phase is invisible on the Hopf base]**. -/
theorem hopfBase_one_phase_invariant (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate 1 χ) = hopfBase χ :=
  hopfBase_phase_invariant 1 χ one_unitPhase

/-- **[The spin-`1/2` ribbon twist is a Hopf-fiber phase]**. Since `θ(1/2) = -1`,
the fermion ribbon twist changes only the Hopf fiber representative, not the base point. -/
theorem hopfBase_ribbonTwist_fermion_invariant (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate (ribbonTwist (1 / 2)) χ) = hopfBase χ := by
  rw [ribbonTwist_fermion]
  exact hopfBase_neg_phase_invariant χ

/-- **[The transposition sign is also invisible on the Hopf base]**. The fermion ribbon sign
equals the sign of a swap, and that sign acts only in the Hopf fiber. -/
theorem hopfBase_swap_sign_invariant {α : Type*} [DecidableEq α] [Fintype α] {i j : α}
    (hij : i ≠ j) (χ : Fin 2 → ℂ) :
    hopfBase (phaseRotate (((Equiv.Perm.sign (Equiv.swap i j) : ℤ) : ℂ)) χ) = hopfBase χ := by
  rw [← ribbonTwist_half_eq_swap_sign hij]
  exact hopfBase_ribbonTwist_fermion_invariant χ

/-! ## §B — the spin-1/2 double cover descends to the Hopf base -/

/-- **[`2π` spinor rotation is the `-1` Hopf-fiber phase]**. -/
theorem spinHalfRotation_two_pi_mulVec (χ : Fin 2 → ℂ) :
    spinHalfRotation (2 * Real.pi) *ᵥ χ = phaseRotate (-1) χ := by
  rw [spinHalfRotation_two_pi, phaseRotate_neg_one]
  ext i
  fin_cases i
  · simp
  · simp

/-- **[`4π` spinor rotation is the identity on spinors]**. -/
theorem spinHalfRotation_four_pi_mulVec (χ : Fin 2 → ℂ) :
    spinHalfRotation (4 * Real.pi) *ᵥ χ = χ := by
  rw [spinHalfRotation_four_pi]
  simp

/-- **[The `2π` spinor sign is invisible on the Hopf base]**. A `2π` rotation sends the spinor
to `-χ`, but the Hopf base point is unchanged. -/
theorem hopfBase_spinHalfRotation_two_pi (χ : Fin 2 → ℂ) :
    hopfBase (spinHalfRotation (2 * Real.pi) *ᵥ χ) = hopfBase χ := by
  rw [spinHalfRotation_two_pi_mulVec]
  exact hopfBase_neg_phase_invariant χ

/-- **[The `4π` spinor rotation is trivially invisible on the Hopf base]**. -/
theorem hopfBase_spinHalfRotation_four_pi (χ : Fin 2 → ℂ) :
    hopfBase (spinHalfRotation (4 * Real.pi) *ᵥ χ) = hopfBase χ := by
  rw [spinHalfRotation_four_pi_mulVec]

/-- **[Hopf fibration + spin-statistics double cover, assembled]**. The `2π` spinor
rotation is the fermion `-1` fiber phase and leaves the Hopf base unchanged; the `4π`
rotation returns the spinor itself and also leaves the base unchanged. -/
theorem hopf_spin_statistics_doubleCover (χ : Fin 2 → ℂ) :
    spinHalfRotation (2 * Real.pi) *ᵥ χ = phaseRotate (ribbonTwist (1 / 2)) χ
      ∧ hopfBase (spinHalfRotation (2 * Real.pi) *ᵥ χ) = hopfBase χ
      ∧ spinHalfRotation (4 * Real.pi) *ᵥ χ = χ
      ∧ hopfBase (spinHalfRotation (4 * Real.pi) *ᵥ χ) = hopfBase χ := by
  rw [ribbonTwist_fermion]
  exact ⟨spinHalfRotation_two_pi_mulVec χ, hopfBase_spinHalfRotation_two_pi χ,
    spinHalfRotation_four_pi_mulVec χ, hopfBase_spinHalfRotation_four_pi χ⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinStatistics

end
