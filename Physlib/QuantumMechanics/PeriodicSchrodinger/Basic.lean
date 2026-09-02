/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# Periodic Schrödinger diffraction geometry

This file formalizes the geometric substrate of Veliev's perturbation theory
for the multidimensional periodic Schrödinger operator.

For a quasimomentum `k : Fin d → ℝ`, the free Bloch energy is

`E₀(k) = |k|² = ∑ᵢ kᵢ²`.

A reciprocal-lattice displacement `b` defines the diffraction defect

`Δ_b(k) = E₀(k) - E₀(k+b)`.

The diffraction hyperplane is the zero set of this defect. Resonance and
nonresonance regions are defined by comparing `|Δ_b(k)|` with a positive
threshold. The definitions are finite-dimensional in physical momentum space,
while the reciprocal-mode index used downstream may be infinite.

The final section also records the transport-effective-mass interface used by
the optical carrier models: the inverse mass is the Hessian of a Bloch-band
energy.  This is deliberately distinct from a Dirac gap coefficient in a
two-band Hamiltonian and from a holographic screen/cell mass.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open scoped BigOperators

/-- Momentum or quasimomentum in `d` Euclidean dimensions. -/
abbrev Momentum (d : ℕ) := Fin d → ℝ

/-- Free Bloch energy `|k|²`. -/
def freeEnergy {d : ℕ} (k : Momentum d) : ℝ :=
  ∑ i, k i ^ 2

@[simp] theorem freeEnergy_zero {d : ℕ} :
    freeEnergy (0 : Momentum d) = 0 := by
  simp [freeEnergy]

/-- Euclidean momentum translation. -/
def momentumShift {d : ℕ} (k b : Momentum d) : Momentum d :=
  fun i => k i + b i

/-- Difference between the free energies of two modes separated by `b`. -/
def diffractionDefect {d : ℕ} (k b : Momentum d) : ℝ :=
  freeEnergy k - freeEnergy (momentumShift k b)

/-- The diffraction defect is affine in `k`:
`|k|²-|k+b|² = -2 k·b-|b|²`. -/
theorem diffractionDefect_eq {d : ℕ} (k b : Momentum d) :
    diffractionDefect k b =
      ∑ i, (-2 * k i * b i - b i ^ 2) := by
  unfold diffractionDefect freeEnergy momentumShift
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The exact diffraction hyperplane `|k|²=|k+b|²`. -/
def OnDiffractionHyperplane {d : ℕ} (k b : Momentum d) : Prop :=
  freeEnergy k = freeEnergy (momentumShift k b)

/-- Hyperplane membership is equivalent to vanishing diffraction defect. -/
theorem onDiffractionHyperplane_iff_defect_zero {d : ℕ}
    (k b : Momentum d) :
    OnDiffractionHyperplane k b ↔ diffractionDefect k b = 0 := by
  simp [OnDiffractionHyperplane, diffractionDefect, sub_eq_zero]

/-- Equivalent affine equation for the diffraction hyperplane. -/
theorem onDiffractionHyperplane_iff_affine {d : ℕ}
    (k b : Momentum d) :
    OnDiffractionHyperplane k b ↔
      (∑ i, (-2 * k i * b i - b i ^ 2)) = 0 := by
  rw [onDiffractionHyperplane_iff_defect_zero,
    diffractionDefect_eq]

/-- `k` lies in the resonance strip associated with `b` and width `ε`. -/
def InResonanceStrip {d : ℕ}
    (k b : Momentum d) (ε : ℝ) : Prop :=
  |diffractionDefect k b| < ε

/-- Closed resonance strip. -/
def InClosedResonanceStrip {d : ℕ}
    (k b : Momentum d) (ε : ℝ) : Prop :=
  |diffractionDefect k b| ≤ ε

/-- Nonresonance relative to one reciprocal displacement. -/
def IsNonresonantFor {d : ℕ}
    (k b : Momentum d) (ε : ℝ) : Prop :=
  ε ≤ |diffractionDefect k b|

/-- Every exact diffraction point belongs to every positive resonance strip. -/
theorem onDiffractionHyperplane_in_resonance {d : ℕ}
    (k b : Momentum d) {ε : ℝ} (hε : 0 < ε)
    (hk : OnDiffractionHyperplane k b) :
    InResonanceStrip k b ε := by
  rw [InResonanceStrip,
    (onDiffractionHyperplane_iff_defect_zero k b).mp hk]
  simpa using hε

/-- Strict resonance and nonresonance are disjoint. -/
theorem resonance_not_nonresonant {d : ℕ}
    (k b : Momentum d) (ε : ℝ)
    (hres : InResonanceStrip k b ε) :
    ¬ IsNonresonantFor k b ε := by
  unfold InResonanceStrip at hres
  unfold IsNonresonantFor
  exact not_le_of_gt hres

/-- Resonance relative to at least one displacement in a finite truncation.
The truncation is indexed by an arbitrary finite label type, avoiding a
classical equality requirement on real momentum vectors. -/
def InFiniteResonanceDomain {d : ℕ} {ι : Type*}
    [DecidableEq ι]
    (mode : ι → Momentum d) (modes : Finset ι)
    (k : Momentum d) (ε : ℝ) : Prop :=
  ∃ a ∈ modes, InResonanceStrip k (mode a) ε

/-- Nonresonance relative to every displacement in a finite truncation. -/
def InFiniteNonresonanceDomain {d : ℕ} {ι : Type*}
    [DecidableEq ι]
    (mode : ι → Momentum d) (modes : Finset ι)
    (k : Momentum d) (ε : ℝ) : Prop :=
  ∀ a ∈ modes, IsNonresonantFor k (mode a) ε

/-- Finite resonance and finite nonresonance domains are disjoint. -/
theorem finiteResonance_not_finiteNonresonance
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (mode : ι → Momentum d) (modes : Finset ι)
    (k : Momentum d) (ε : ℝ)
    (hres : InFiniteResonanceDomain mode modes k ε) :
    ¬ InFiniteNonresonanceDomain mode modes k ε := by
  rintro hnon
  rcases hres with ⟨a, ha, hstrip⟩
  exact resonance_not_nonresonant k (mode a) ε hstrip (hnon a ha)

/-- An abstract reciprocal lattice embedded in momentum space. The mode type
may be infinite. -/
structure ReciprocalLattice (d : ℕ) where
  Mode : Type*
  [decidableEqMode : DecidableEq Mode]
  momentum : Mode → Momentum d
  zeroMode : Mode
  momentum_zero : momentum zeroMode = 0

attribute [instance] ReciprocalLattice.decidableEqMode

/-- Free Bloch energy of a reciprocal mode at quasimomentum `t`. -/
def modeEnergy {d : ℕ} (Γ : ReciprocalLattice d)
    (t : Momentum d) (γ : Γ.Mode) : ℝ :=
  freeEnergy (momentumShift (Γ.momentum γ) t)

/-- Degeneracy of two free Bloch modes at a fixed quasimomentum. -/
def ModesDiffract {d : ℕ} (Γ : ReciprocalLattice d)
    (t : Momentum d) (γ₁ γ₂ : Γ.Mode) : Prop :=
  modeEnergy Γ t γ₁ = modeEnergy Γ t γ₂

/-- Diffraction between modes is symmetric. -/
theorem modesDiffract_symm {d : ℕ} (Γ : ReciprocalLattice d)
    (t : Momentum d) (γ₁ γ₂ : Γ.Mode) :
    ModesDiffract Γ t γ₁ γ₂ ↔ ModesDiffract Γ t γ₂ γ₁ := by
  constructor <;> intro h <;> exact h.symm

/-! ## Transport mass from a one-dimensional Bloch band -/

/-- The curvature of a one-dimensional band energy at quasimomentum `k`.

The definition is the second derivative `E''(k)`.  It is an analytic band
quantity; it is not the coefficient of a Dirac mass term. -/
noncomputable def bandCurvature (energy : ℝ → ℝ) (k : ℝ) : ℝ :=
  deriv (deriv energy) k

/-- The transport effective mass associated with a band-energy Hessian:
`m_eff = ℏ² / E''(k)`. -/
noncomputable def carrierEffectiveMassFromBand
    (energy : ℝ → ℝ) (hbar k : ℝ) : ℝ :=
  hbar ^ 2 / bandCurvature energy k

/-- A parabolic band with edge energy `edge` and carrier mass `mass`. -/
noncomputable def parabolicBandEnergy
    (edge hbar mass k : ℝ) : ℝ :=
  edge + hbar ^ 2 * k ^ 2 / (2 * mass)

/-- The group-energy derivative of the parabolic band. -/
theorem deriv_parabolicBandEnergy (edge hbar mass : ℝ) :
    deriv (parabolicBandEnergy edge hbar mass) =
      fun k => (hbar ^ 2 / mass) * k := by
  funext k
  unfold parabolicBandEnergy
  convert HasDerivAt.deriv
    ((HasDerivAt.const_mul (hbar ^ 2) (hasDerivAt_pow 2 k))
      |>.div_const (2 * mass) |>.const_add edge) using 1
  · ring

/-- The Hessian of a parabolic band is the constant `ℏ² / mass`. -/
theorem bandCurvature_parabolic (edge hbar mass k : ℝ) :
    bandCurvature (parabolicBandEnergy edge hbar mass) k =
      hbar ^ 2 / mass := by
  rw [bandCurvature, deriv_parabolicBandEnergy edge hbar mass]
  exact (hasDerivAt_const_mul (x := k) (hbar ^ 2 / mass)).deriv

/-- The Hessian definition recovers the mass parameter of a parabolic band. -/
theorem carrierEffectiveMassFromBand_parabolic
    (edge hbar mass k : ℝ) (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) :
    carrierEffectiveMassFromBand
        (parabolicBandEnergy edge hbar mass) hbar k = mass := by
  rw [carrierEffectiveMassFromBand,
    bandCurvature_parabolic edge hbar mass k]
  field_simp

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
