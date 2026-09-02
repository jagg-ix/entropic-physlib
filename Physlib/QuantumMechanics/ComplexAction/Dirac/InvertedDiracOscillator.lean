/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorPseudoHermitian
public import Physlib.Mathematics.InnerProductSpace.Adjoint
public import Mathlib.Tactic

/-!
# Inverted Dirac oscillator

This module formalizes the algebraic part of Mustapha Maamache, *Inverted
Dirac oscillator* (2026), arXiv:2606.15303v1.  The paper starts from the
ordinary four-spinor Dirac Hamiltonian and replaces the oscillator
non-minimal substitution by the real sign choice

`p ↦ p - mωβq`.

The resulting block Hamiltonian is non-Hermitian in the ordinary Hilbert
metric, but its lower-component equation reduces to an inverted harmonic
oscillator with a spin-orbit term.  A quarter-turn squeeze maps that reduced
inverted oscillator to `i` times the ordinary harmonic oscillator.

The file reuses existing infrastructure:

* `Dirac.FourSpinorDiracHamiltonian` for the free four-spinor Dirac matrix;
* `OperatorAlgebra.InvertedOscillatorPseudoHermitian` for the existing
  inverted-oscillator growth model.

## References

* M. Maamache, *Inverted Dirac oscillator*, arXiv:2606.15303v1, Eqs. (3),
  (4), (14), (16)--(20), (23), (24).
* M. Moshinsky and A. Szczepaniak, *The Dirac oscillator*, J. Phys. A:
  Math. Gen. 22 (1989), L817.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open Matrix Complex
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.InvertedDiracOscillator

/-! ## A. Four-spinor inverted Dirac oscillator -/

/-- The concrete block Hamiltonian of the inverted Dirac oscillator,
Eq. (4) of Maamache.  It is the four-spinor Dirac Hamiltonian with the
real non-minimal coupling `p ↦ p - mωβq`, written in the same Dirac
representation used by `diracHamiltonian4`. -/
def invertedDiracOscillatorHamiltonian
    (p1 p2 p3 q1 q2 q3 m omega c : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let mωq1 : ℝ := m * omega * q1
  let mωq2 : ℝ := m * omega * q2
  let mωq3 : ℝ := m * omega * q3
  !![((m * c ^ 2 : ℝ) : ℂ), 0,
      ((c * (p3 + mωq3) : ℝ) : ℂ),
      ((c * (p1 + mωq1) : ℝ) : ℂ) - ((c * (p2 + mωq2) : ℝ) : ℂ) * I;
     0, ((m * c ^ 2 : ℝ) : ℂ),
      ((c * (p1 + mωq1) : ℝ) : ℂ) + ((c * (p2 + mωq2) : ℝ) : ℂ) * I,
      -((c * (p3 + mωq3) : ℝ) : ℂ);
     ((c * (p3 - mωq3) : ℝ) : ℂ),
      ((c * (p1 - mωq1) : ℝ) : ℂ) - ((c * (p2 - mωq2) : ℝ) : ℂ) * I,
      -((m * c ^ 2 : ℝ) : ℂ), 0;
     ((c * (p1 - mωq1) : ℝ) : ℂ) + ((c * (p2 - mωq2) : ℝ) : ℂ) * I,
      -((c * (p3 - mωq3) : ℝ) : ℂ), 0, -((m * c ^ 2 : ℝ) : ℂ)]

/-- At zero oscillator coupling and in units `c=1`, the inverted Dirac
oscillator is exactly the existing free four-spinor Dirac Hamiltonian. -/
lemma invertedDiracOscillator_zeroFrequency (p1 p2 p3 q1 q2 q3 m : ℝ) :
    invertedDiracOscillatorHamiltonian p1 p2 p3 q1 q2 q3 m 0 1 =
      diracHamiltonian4 p1 p2 p3 m := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [invertedDiracOscillatorHamiltonian, diracHamiltonian4_concrete]

/-- The real oscillator coupling appears with opposite signs in the two
off-diagonal Dirac blocks.  This is the algebraic matrix-entry witness for
the non-Hermitian sign asymmetry in Eq. (4). -/
lemma invertedDiracOscillator_offDiagonal3_defect
    (p1 p2 p3 q1 q2 q3 m omega c : ℝ) :
    invertedDiracOscillatorHamiltonian p1 p2 p3 q1 q2 q3 m omega c (0 : Fin 4) (2 : Fin 4)
      - invertedDiracOscillatorHamiltonian p1 p2 p3 q1 q2 q3 m omega c (2 : Fin 4) (0 : Fin 4)
        = ((2 * c * m * omega * q3 : ℝ) : ℂ) := by
  simp [invertedDiracOscillatorHamiltonian]
  ring

/-! ## B. Reduced inverted oscillator and the quarter-turn squeeze -/

/-- Algebraic data of the quarter-turn squeeze used in Eq. (16): momentum is
multiplied by a phase whose square is `i`, position by a phase whose square
is `-i`, and the two phase factors multiply to one. -/
structure QuarterTurnDilation where
  /-- The momentum phase factor. -/
  phaseP : ℂ
  /-- The position phase factor. -/
  phaseQ : ℂ
  /-- Momentum squares pick up the factor `i`. -/
  phaseP_sq : phaseP ^ 2 = I
  /-- Position squares pick up the factor `-i`. -/
  phaseQ_sq : phaseQ ^ 2 = -I
  /-- The angular-momentum product `pq` is invariant. -/
  phaseP_mul_phaseQ : phaseP * phaseQ = 1

namespace QuarterTurnDilation

/-- The position and momentum phases also multiply to one in the opposite
order, since they are complex scalars. -/
lemma phaseQ_mul_phaseP (D : QuarterTurnDilation) : D.phaseQ * D.phaseP = 1 := by
  rw [mul_comm, D.phaseP_mul_phaseQ]

end QuarterTurnDilation

/-- The ordinary harmonic-oscillator quadratic form `p²/(2m)+mω²q²/2`. -/
def harmonicOscillatorQuadratic (p2 q2 m omega : ℂ) : ℂ :=
  p2 / (2 * m) + m * omega ^ 2 * q2 / 2

/-- The inverted harmonic-oscillator quadratic form `p²/(2m)-mω²q²/2`. -/
def invertedOscillatorQuadratic (p2 q2 m omega : ℂ) : ℂ :=
  p2 / (2 * m) - m * omega ^ 2 * q2 / 2

/-- Eq. (17) at the quadratic level: the quarter-turn squeeze maps the
inverted oscillator to `i` times the ordinary harmonic oscillator. -/
lemma quarterTurn_invertedQuadratic_eq_I_harmonic (D : QuarterTurnDilation)
    (p2 q2 m omega : ℂ) :
    invertedOscillatorQuadratic (D.phaseP ^ 2 * p2) (D.phaseQ ^ 2 * q2) m omega =
      I * harmonicOscillatorQuadratic p2 q2 m omega := by
  rw [invertedOscillatorQuadratic, harmonicOscillatorQuadratic, D.phaseP_sq, D.phaseQ_sq]
  ring

/-- The reduced ordinary Dirac-oscillator operator appearing after the
quarter-turn transformation, Eq. (20):
`H_os - 3ℏω/2 - (2ω/ℏ) S·L`. -/
def standardDiracOscillatorReduced (p2 q2 spinOrbit m omega hbar : ℂ) : ℂ :=
  harmonicOscillatorQuadratic p2 q2 m omega - (3 / 2 : ℂ) * hbar * omega -
    (2 : ℂ) * omega / hbar * spinOrbit

/-- The reduced inverted Dirac-oscillator operator of Eq. (14):
`p²/(2m)-mω²q²/2 - i(3ℏω/2 + (2ω/ℏ)S·L)`. -/
def invertedDiracOscillatorReduced (p2 q2 spinOrbit m omega hbar : ℂ) : ℂ :=
  invertedOscillatorQuadratic p2 q2 m omega - I * ((3 / 2 : ℂ) * hbar * omega +
    (2 : ℂ) * omega / hbar * spinOrbit)

/-- Eqs. (18)--(20): after the quarter-turn squeeze, the reduced inverted
Dirac oscillator is `i` times the ordinary reduced Dirac oscillator.  The
spin-orbit term is unchanged because the squeeze leaves the `pq` angular
momentum product invariant. -/
lemma quarterTurn_invertedReduced_eq_I_standard (D : QuarterTurnDilation)
    (p2 q2 spinOrbit m omega hbar : ℂ) :
    invertedDiracOscillatorReduced
        (D.phaseP ^ 2 * p2) (D.phaseQ ^ 2 * q2) spinOrbit m omega hbar =
      I * standardDiracOscillatorReduced p2 q2 spinOrbit m omega hbar := by
  rw [invertedDiracOscillatorReduced, standardDiracOscillatorReduced,
    quarterTurn_invertedQuadratic_eq_I_harmonic]
  ring

/-! ## C. Spin-orbit spectrum and inverted-oscillator growth link -/

/-- The spin-orbit eigenvalue
`S·L = ℏ²/2 (j(j+1)-l(l+1)-3/4)` for spin `1/2`. -/
def spinOrbitEigenvalue (l j hbar : ℂ) : ℂ :=
  hbar ^ 2 / 2 * (j * (j + 1) - l * (l + 1) - (3 / 4 : ℂ))

/-- The reduced energy expression obtained by inserting the oscillator and
spin-orbit eigenvalues into Eq. (20). -/
def transformedEnergyLevel (n l j hbar omega : ℂ) : ℂ :=
  hbar * omega * (n + (3 / 2 : ℂ)) - (3 / 2 : ℂ) * hbar * omega -
    (2 : ℂ) * omega / hbar * spinOrbitEigenvalue l j hbar

/-- With nonzero `ℏ`, the transformed level reduces to the compact
spin-orbit formula obtained from Eq. (22). -/
lemma transformedEnergyLevel_eq (n l j hbar omega : ℂ) (hhbar : hbar ≠ 0) :
    transformedEnergyLevel n l j hbar omega =
      hbar * omega * (n - (j * (j + 1) - l * (l + 1) - (3 / 4 : ℂ))) := by
  rw [transformedEnergyLevel, spinOrbitEigenvalue]
  field_simp [hhbar]
  ring

/-- The inverted Dirac oscillator uses the existing inverted-oscillator
hyperbolic growth model for its unstable reduced sector. -/
abbrev invertedDiracOscillatorRunawayEnergy :=
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorPseudoHermitian.invertedEnergyGrowth

/-- The reduced inverted Dirac oscillator inherits the existing IQHO
hyperbolic growth law. -/
lemma invertedDiracOscillatorRunawayEnergy_eq (E0 kappa t : ℝ) :
    invertedDiracOscillatorRunawayEnergy E0 kappa t = E0 * Real.cosh (2 * kappa * t) := rfl

/-! ## D. Non-unitary state transform and metric normalization -/

/-- The metric inner product induced by the inverse squeeze `ρ⁻¹`.
This is the left-hand side of Eq. (24) before spelling out the adjoint:
`⟪ρ⁻¹ φ, ρ⁻¹ ψ⟫`. -/
def pseudoMetricInner {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace' ℂ H] (rhoInv : H → H) (φ ψ : H) : ℂ :=
  inner ℂ (rhoInv φ) (rhoInv ψ)

/-- The same metric inner product written with the metric operator
`(ρ⁻¹)†ρ⁻¹`, matching Eq. (24). -/
def metricOperatorInner {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace' ℂ H] (rhoInv rhoInvAdj : H → H) (φ ψ : H) : ℂ :=
  inner ℂ φ (rhoInvAdj (rhoInv ψ))

/-- The pseudo-metric inner product is exactly the metric-operator expression
when `rhoInvAdj` is the adjoint of `rhoInv`. -/
lemma pseudoMetricInner_eq_metricOperatorInner {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [InnerProductSpace' ℂ H]
    {rhoInv rhoInvAdj : H → H} (hAdj : HasAdjoint ℂ rhoInv rhoInvAdj)
    (φ ψ : H) :
    pseudoMetricInner rhoInv φ ψ = metricOperatorInner rhoInv rhoInvAdj φ ψ := by
  rw [pseudoMetricInner, metricOperatorInner]
  exact (hAdj.adjoint_inner_right (x := φ) (y := rhoInv ψ)).symm

/-- If the inverted state is obtained by the non-unitary map
`ψ_r = ρ ψ_os`, and `ρ⁻¹ρ = 1`, then its pseudo-metric norm is the
ordinary norm of the oscillator state. -/
lemma pseudoMetricInner_transformed_state {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [InnerProductSpace' ℂ H]
    {rho rhoInv : H → H} (hLeft : ∀ ψ : H, rhoInv (rho ψ) = ψ)
    (ψ : H) :
    pseudoMetricInner rhoInv (rho ψ) (rho ψ) = inner ℂ ψ ψ := by
  simp [pseudoMetricInner, hLeft]

/-- Eq. (24): if the ordinary oscillator state is normalized, then the
inverted-oscillator state `ψ_r = ρψ_os` is normalized in the metric
`(ρ⁻¹)†ρ⁻¹`.  This is the mathematically precise normalization needed
because the squeeze is non-unitary. -/
lemma metricOperator_normalization_transformed_state {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [InnerProductSpace' ℂ H]
    {rho rhoInv rhoInvAdj : H → H} (hAdj : HasAdjoint ℂ rhoInv rhoInvAdj)
    (hLeft : ∀ ψ : H, rhoInv (rho ψ) = ψ) {ψ : H}
    (hNorm : inner ℂ ψ ψ = 1) :
    metricOperatorInner rhoInv rhoInvAdj (rho ψ) (rho ψ) = 1 := by
  rw [← pseudoMetricInner_eq_metricOperatorInner hAdj]
  rw [pseudoMetricInner_transformed_state hLeft, hNorm]

end Physlib.QuantumMechanics.ComplexAction.Dirac.InvertedDiracOscillator

end
