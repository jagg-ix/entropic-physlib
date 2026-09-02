/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade

/-!
# Time-integrated finite Fourier dissipation cascade

This module integrates the exact finite Fourier differential cascade already
proved for the diagonal entropically damped Stokes evolution. The fundamental
theorem of calculus gives, for arbitrary endpoints `a` and `b`,

* `E(b) + 2ν ∫ₐᵇ Ω + 2λ ∫ₐᵇ E = E(a)`,
* `Ω(b) + 2ν ∫ₐᵇ P + 2λ ∫ₐᵇ Ω = Ω(a)`,
* `P(b) + 2ν ∫ₐᵇ S + 2λ ∫ₐᵇ P = P(a)`.

For positive viscosity, non-negative damping, and `T ≥ 0`, these identities
produce genuine interval-integral Leray/Sobolev budgets. In particular,

`∫₀ᵀ Ω ≤ E(0)/(2ν)`

and the finite Fourier BKM-surrogate integral satisfies

`∫₀ᵀ (Ω + P) ≤ (E(0) + Ω(0))/(2ν)`.

The factor `2` is not an extra physical claim: it follows from the repository
convention `kineticEnergy = ∑ âᵢ²`, without the conventional prefactor `1/2`.

These are exact finite-dimensional linear Galerkin identities. They do not
construct an infinite-dimensional weak solution, include the pressure
projection or nonlinear triadic interaction, or prove the analytic
`L∞` Beale--Kato--Majda criterion or nonlinear Navier--Stokes regularity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade

open Physlib.QFT.PathIntegral
open NSFieldFourierSobolevHierarchy
open NSFourierDampedStokesSemigroup
open NSFourierSobolevDissipationCascade
open VorticityCoadjointEnstrophy

/-! ## A. Continuity of the evolved Sobolev functionals -/

private lemma dampedStokesEvolution_weightedEnergy_continuous
    (v : NSFieldFourier) (weight : Fin v.N → ℝ) (nu lam : ℝ) :
    Continuous (fun t => ∑ i : Fin v.N,
      weight i * (dampedStokesEvolution v nu lam t).amp i ^ 2) := by
  apply continuous_finsetSum
  intro i _
  have hi : Continuous (fun t => (dampedStokesEvolution v nu lam t).amp i) := by
    exact continuous_apply i |>.comp
      (stokesGalerkinOperator_continuous v.freq nu lam v.amp)
  fun_prop

/-- The kinetic energy of the finite Fourier evolution is continuous in time. -/
lemma dampedStokesEvolution_kineticEnergy_continuous
    (v : NSFieldFourier) (nu lam : ℝ) :
    Continuous (fun t =>
      NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t)) := by
  change Continuous (fun t => ∑ i : Fin v.N,
    (dampedStokesEvolution v nu lam t).amp i ^ 2)
  simpa only [one_mul] using
    dampedStokesEvolution_weightedEnergy_continuous v (fun _ => 1) nu lam

/-- The enstrophy of the finite Fourier evolution is continuous in time. -/
lemma dampedStokesEvolution_enstrophy_continuous
    (v : NSFieldFourier) (nu lam : ℝ) :
    Continuous (fun t =>
      NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) := by
  exact dampedStokesEvolution_weightedEnergy_continuous
    v (fun i => (v.freq i : ℝ) ^ 2) nu lam

/-- The palinstrophy of the finite Fourier evolution is continuous in time. -/
lemma dampedStokesEvolution_palinstrophy_continuous
    (v : NSFieldFourier) (nu lam : ℝ) :
    Continuous (fun t =>
      NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) := by
  exact dampedStokesEvolution_weightedEnergy_continuous
    v (fun i => (v.freq i : ℝ) ^ 4) nu lam

/-- The super-palinstrophy of the finite Fourier evolution is continuous in
time. -/
lemma dampedStokesEvolution_superPalinstrophy_continuous
    (v : NSFieldFourier) (nu lam : ℝ) :
    Continuous (fun t =>
      NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) := by
  exact dampedStokesEvolution_weightedEnergy_continuous
    v (fun i => (v.freq i : ℝ) ^ 6) nu lam

/-- At time zero the diagonal Stokes evolution is the original finite Fourier
field. -/
@[simp]
lemma dampedStokesEvolution_zero
    (v : NSFieldFourier) (nu lam : ℝ) :
    dampedStokesEvolution v nu lam 0 = v := by
  cases v with
  | mk N freq amp =>
      simp [dampedStokesEvolution]

/-! ## B. Exact interval-integral balances -/

/-- The exact time-integrated kinetic-energy identity
`E(b) + 2ν∫Ω + 2λ∫E = E(a)`. -/
lemma dampedStokesEvolution_kineticEnergy_integralBalance
    (v : NSFieldFourier) (nu lam a b : ℝ) :
    NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam b) +
        2 * nu * (∫ t in a..b,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
        2 * lam * (∫ t in a..b,
          NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t)) =
      NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam a) := by
  have hE := dampedStokesEvolution_kineticEnergy_continuous v nu lam
  have hΩ := dampedStokesEvolution_enstrophy_continuous v nu lam
  have hderiv :
      ∀ t ∈ Set.uIcc a b,
        HasDerivAt
          (fun s => NSFieldFourier.kineticEnergy
            (dampedStokesEvolution v nu lam s))
          (-2 * nu * NSFieldFourier.enstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.kineticEnergy
              (dampedStokesEvolution v nu lam t)) t :=
    fun t _ => dampedStokesEvolution_kineticEnergy_hasDerivAt v nu lam t
  have hint :
      IntervalIntegrable
        (fun t =>
          -2 * nu * NSFieldFourier.enstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.kineticEnergy
              (dampedStokesEvolution v nu lam t))
        MeasureTheory.volume a b :=
    ((hΩ.const_mul (-2 * nu)).sub (hE.const_mul (2 * lam))).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  · linarith
  · exact (hΩ.const_mul (-2 * nu)).intervalIntegrable a b
  · exact (hE.const_mul (2 * lam)).intervalIntegrable a b

/-- The exact time-integrated enstrophy identity
`Ω(b) + 2ν∫P + 2λ∫Ω = Ω(a)`. -/
lemma dampedStokesEvolution_enstrophy_integralBalance
    (v : NSFieldFourier) (nu lam a b : ℝ) :
    NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam b) +
        2 * nu * (∫ t in a..b,
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) +
        2 * lam * (∫ t in a..b,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) =
      NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam a) := by
  have hΩ := dampedStokesEvolution_enstrophy_continuous v nu lam
  have hP := dampedStokesEvolution_palinstrophy_continuous v nu lam
  have hderiv :
      ∀ t ∈ Set.uIcc a b,
        HasDerivAt
          (fun s => NSFieldFourier.enstrophy
            (dampedStokesEvolution v nu lam s))
          (-2 * nu * NSFieldFourier.palinstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.enstrophy
              (dampedStokesEvolution v nu lam t)) t :=
    fun t _ => dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t
  have hint :
      IntervalIntegrable
        (fun t =>
          -2 * nu * NSFieldFourier.palinstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.enstrophy
              (dampedStokesEvolution v nu lam t))
        MeasureTheory.volume a b :=
    ((hP.const_mul (-2 * nu)).sub (hΩ.const_mul (2 * lam))).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  · linarith
  · exact (hP.const_mul (-2 * nu)).intervalIntegrable a b
  · exact (hΩ.const_mul (2 * lam)).intervalIntegrable a b

/-- The exact time-integrated palinstrophy identity
`P(b) + 2ν∫S + 2λ∫P = P(a)`. -/
lemma dampedStokesEvolution_palinstrophy_integralBalance
    (v : NSFieldFourier) (nu lam a b : ℝ) :
    NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam b) +
        2 * nu * (∫ t in a..b,
          NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) +
        2 * lam * (∫ t in a..b,
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) =
      NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam a) := by
  have hP := dampedStokesEvolution_palinstrophy_continuous v nu lam
  have hS := dampedStokesEvolution_superPalinstrophy_continuous v nu lam
  have hderiv :
      ∀ t ∈ Set.uIcc a b,
        HasDerivAt
          (fun s => NSFieldFourier.palinstrophy
            (dampedStokesEvolution v nu lam s))
          (-2 * nu * NSFieldFourier.superPalinstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.palinstrophy
              (dampedStokesEvolution v nu lam t)) t :=
    fun t _ => dampedStokesEvolution_palinstrophy_hasDerivAt v nu lam t
  have hint :
      IntervalIntegrable
        (fun t =>
          -2 * nu * NSFieldFourier.superPalinstrophy
              (dampedStokesEvolution v nu lam t) -
            2 * lam * NSFieldFourier.palinstrophy
              (dampedStokesEvolution v nu lam t))
        MeasureTheory.volume a b :=
    ((hS.const_mul (-2 * nu)).sub (hP.const_mul (2 * lam))).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  · linarith
  · exact (hS.const_mul (-2 * nu)).intervalIntegrable a b
  · exact (hP.const_mul (2 * lam)).intervalIntegrable a b

/-! ## C. Positive-time Leray and entropic-time budgets -/

/-- The exact kinetic-energy balance from time zero. The right-hand side
simplifies to the initial Fourier energy. -/
lemma dampedStokesEvolution_kineticEnergy_integralBalance_zero
    (v : NSFieldFourier) (nu lam T : ℝ) :
    NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam T) +
        2 * nu * (∫ t in 0..T,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
        2 * lam * (∫ t in 0..T,
          NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t)) =
      NSFieldFourier.kineticEnergy v := by
  simpa using dampedStokesEvolution_kineticEnergy_integralBalance v nu lam 0 T

/-- A genuine interval-integral Leray enstrophy budget for the finite
evolution: `∫₀ᵀ Ω ≤ E(0)/(2ν)`. -/
lemma dampedStokesEvolution_integratedEnstrophy_le_initialEnergy
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    (∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) ≤
      NSFieldFourier.kineticEnergy v / (2 * nu) := by
  have hbalance :=
    dampedStokesEvolution_kineticEnergy_integralBalance_zero v nu lam T
  have hET : 0 ≤ NSFieldFourier.kineticEnergy
      (dampedStokesEvolution v nu lam T) :=
    NSFieldFourier.kineticEnergy_nonneg _
  have hIE : 0 ≤ ∫ t in 0..T,
      NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t) :=
    intervalIntegral.integral_nonneg hT fun t _ =>
      NSFieldFourier.kineticEnergy_nonneg _
  have hscaled :
      2 * nu * (∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) ≤
        NSFieldFourier.kineticEnergy v := by
    nlinarith
  rw [le_div_iff₀ (by positivity : 0 < 2 * nu)]
  simpa only [mul_comm] using hscaled

/-- The actual interval-integrated enstrophy controls the existing entropic
orbit-traversal clock:
`(ν/ħ)∫₀ᵀ Ω ≤ E(0)/(2ħ)`. -/
lemma dampedStokesEvolution_orbitTraversal_le_initialEnergy
    (v : NSFieldFourier) (nu lam hbar T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hhbar : 0 < hbar) (hT : 0 ≤ T) :
    orbitTraversal nu hbar
        (∫ t in 0..T,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) ≤
      NSFieldFourier.kineticEnergy v / (2 * hbar) := by
  have hI :=
    dampedStokesEvolution_integratedEnstrophy_le_initialEnergy
      v nu lam T hnu hl hT
  unfold orbitTraversal
  calc
    nu / hbar * (∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
        ≤ nu / hbar * (NSFieldFourier.kineticEnergy v / (2 * nu)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = NSFieldFourier.kineticEnergy v / (2 * hbar) := by
      field_simp

/-- The next Sobolev budget:
`∫₀ᵀ P ≤ Ω(0)/(2ν)`. -/
lemma dampedStokesEvolution_integratedPalinstrophy_le_initialEnstrophy
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    (∫ t in 0..T,
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) ≤
      NSFieldFourier.enstrophy v / (2 * nu) := by
  have hbalance :=
    dampedStokesEvolution_enstrophy_integralBalance v nu lam 0 T
  simp only [dampedStokesEvolution_zero] at hbalance
  have hΩT : 0 ≤ NSFieldFourier.enstrophy
      (dampedStokesEvolution v nu lam T) :=
    NSFieldFourier.enstrophy_nonneg _
  have hIΩ : 0 ≤ ∫ t in 0..T,
      NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) :=
    intervalIntegral.integral_nonneg hT fun t _ =>
      NSFieldFourier.enstrophy_nonneg _
  have hscaled :
      2 * nu * (∫ t in 0..T,
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) ≤
        NSFieldFourier.enstrophy v := by
    nlinarith
  rw [le_div_iff₀ (by positivity : 0 < 2 * nu)]
  simpa only [mul_comm] using hscaled

/-- The `H³` budget:
`∫₀ᵀ S ≤ P(0)/(2ν)`. -/
lemma dampedStokesEvolution_integratedSuperPalinstrophy_le_initialPalinstrophy
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    (∫ t in 0..T,
        NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) ≤
      NSFieldFourier.palinstrophy v / (2 * nu) := by
  have hbalance :=
    dampedStokesEvolution_palinstrophy_integralBalance v nu lam 0 T
  simp only [dampedStokesEvolution_zero] at hbalance
  have hPT : 0 ≤ NSFieldFourier.palinstrophy
      (dampedStokesEvolution v nu lam T) :=
    NSFieldFourier.palinstrophy_nonneg _
  have hIP : 0 ≤ ∫ t in 0..T,
      NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) :=
    intervalIntegral.integral_nonneg hT fun t _ =>
      NSFieldFourier.palinstrophy_nonneg _
  have hscaled :
      2 * nu * (∫ t in 0..T,
        NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) ≤
        NSFieldFourier.palinstrophy v := by
    nlinarith
  rw [le_div_iff₀ (by positivity : 0 < 2 * nu)]
  simpa only [mul_comm] using hscaled

/-! ## D. Actual interval-integral BKM surrogate -/

/-- The actual interval integral of the finite Fourier BKM-surrogate density is
controlled internally by the initial `H⁰ + H¹` budget:
`∫₀ᵀ (Ω + P) ≤ (E(0) + Ω(0))/(2ν)`.

This closes the external palinstrophy-budget hypothesis for this specific
linear evolution. It is not the analytic `L∞` BKM criterion. -/
lemma dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    (∫ t in 0..T,
        (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) ≤
      (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
        (2 * nu) := by
  have hΩint : IntervalIntegrable
      (fun t => NSFieldFourier.enstrophy
        (dampedStokesEvolution v nu lam t)) MeasureTheory.volume 0 T :=
    (dampedStokesEvolution_enstrophy_continuous v nu lam).intervalIntegrable 0 T
  have hPint : IntervalIntegrable
      (fun t => NSFieldFourier.palinstrophy
        (dampedStokesEvolution v nu lam t)) MeasureTheory.volume 0 T :=
    (dampedStokesEvolution_palinstrophy_continuous v nu lam).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add hΩint hPint]
  have hΩ :=
    dampedStokesEvolution_integratedEnstrophy_le_initialEnergy
      v nu lam T hnu hl hT
  have hP :=
    dampedStokesEvolution_integratedPalinstrophy_le_initialEnstrophy
      v nu lam T hnu hl hT
  calc
    (∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
          ∫ t in 0..T,
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)
        ≤ NSFieldFourier.kineticEnergy v / (2 * nu) +
            NSFieldFourier.enstrophy v / (2 * nu) :=
      add_le_add hΩ hP
    _ = (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
        (2 * nu) := by ring

/-! ## E. Assembled integrated cascade -/

/-- Assemble the three exact time-integrated `H⁰ → H¹ → H² → H³`
dissipation identities. -/
lemma dampedStokesEvolution_integratedSobolevDissipationCascade
    (v : NSFieldFourier) (nu lam a b : ℝ) :
    (NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam b) +
          2 * nu * (∫ t in a..b,
            NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
          2 * lam * (∫ t in a..b,
            NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t)) =
        NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam a)) ∧
      (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam b) +
          2 * nu * (∫ t in a..b,
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) +
          2 * lam * (∫ t in a..b,
            NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) =
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam a)) ∧
      (NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam b) +
          2 * nu * (∫ t in a..b,
            NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) +
          2 * lam * (∫ t in a..b,
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) =
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam a)) :=
  ⟨dampedStokesEvolution_kineticEnergy_integralBalance v nu lam a b,
    dampedStokesEvolution_enstrophy_integralBalance v nu lam a b,
    dampedStokesEvolution_palinstrophy_integralBalance v nu lam a b⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade

end
