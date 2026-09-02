/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LeftRiemannSumConvergence
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSBKMSurrogateBudget

/-!
# Discrete-to-continuous bridge for the damped Fourier Sobolev budgets

The older Navier--Stokes budget layer uses the repository's fixed-step
`leftRiemannSum`, while the exact damped Stokes cascade uses Mathlib interval
integrals. This module proves that these are compatible for the actual finite
Fourier evolution.

For nonnegative viscosity and damping, kinetic energy, enstrophy, and
palinstrophy are non-increasing on every positive time interval. The generic
`LeftRiemannSumConvergence` theorem therefore applies and gives:

* convergence of the discrete enstrophy and palinstrophy budgets;
* explicit errors bounded by `Ω(0)/N` and `P(0)/N`;
* convergence of the discrete entropic proper time;
* convergence of the discrete BKM surrogate to the actual interval integral.
* a finite-resolution BKM certificate with explicit `1/N` remainder.

The capstone combines that convergence with the exact continuous budget

`∫₀ᵀ (Ω + P) ≤ (E(0) + Ω(0))/(2ν)`.

These are finite-dimensional diagonal Galerkin results. The BKM expression is
the repository's `Ω + P` surrogate, not the analytic vorticity `L∞` criterion.
No nonlinear pressure-projected Navier--Stokes flow or Leray weak solution is
constructed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge

open Filter Set Topology
open Physlib.Mathematics.LeftRiemannSum
open NSFieldFourierSobolevHierarchy
open NSFourierDampedStokesSemigroup
open NSFourierSobolevDissipationCascade
open NSFourierIntegratedDissipationCascade

/-! ## A. Monotonicity of the evolved Sobolev functionals -/

/-- Kinetic energy is non-increasing on `[0,T]` for nonnegative viscosity and
damping. -/
lemma dampedStokesEvolution_kineticEnergy_antitoneOn
    (v : NSFieldFourier) (nu lam T : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    AntitoneOn
      (fun t => NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t))
      (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    (dampedStokesEvolution_kineticEnergy_continuous v nu lam).continuousOn
  · intro t ht
    exact
      (dampedStokesEvolution_kineticEnergy_hasDerivAt v nu lam t).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    rw [(dampedStokesEvolution_kineticEnergy_hasDerivAt v nu lam t).deriv]
    have hΩ :=
      NSFieldFourier.enstrophy_nonneg (dampedStokesEvolution v nu lam t)
    have hE :=
      NSFieldFourier.kineticEnergy_nonneg (dampedStokesEvolution v nu lam t)
    nlinarith [mul_nonneg hnu hΩ, mul_nonneg hl hE]

/-- Enstrophy is non-increasing on `[0,T]` for nonnegative viscosity and
damping. -/
lemma dampedStokesEvolution_enstrophy_antitoneOn
    (v : NSFieldFourier) (nu lam T : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    AntitoneOn
      (fun t => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
      (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    (dampedStokesEvolution_enstrophy_continuous v nu lam).continuousOn
  · intro t ht
    exact
      (dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    rw [(dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t).deriv]
    have hP :=
      NSFieldFourier.palinstrophy_nonneg (dampedStokesEvolution v nu lam t)
    have hΩ :=
      NSFieldFourier.enstrophy_nonneg (dampedStokesEvolution v nu lam t)
    nlinarith [mul_nonneg hnu hP, mul_nonneg hl hΩ]

/-- Palinstrophy is non-increasing on `[0,T]` for nonnegative viscosity and
damping. -/
lemma dampedStokesEvolution_palinstrophy_antitoneOn
    (v : NSFieldFourier) (nu lam T : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    AntitoneOn
      (fun t => NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))
      (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    (dampedStokesEvolution_palinstrophy_continuous v nu lam).continuousOn
  · intro t ht
    exact
      (dampedStokesEvolution_palinstrophy_hasDerivAt v nu lam t).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    rw [(dampedStokesEvolution_palinstrophy_hasDerivAt v nu lam t).deriv]
    have hS :=
      NSFieldFourier.superPalinstrophy_nonneg (dampedStokesEvolution v nu lam t)
    have hP :=
      NSFieldFourier.palinstrophy_nonneg (dampedStokesEvolution v nu lam t)
    nlinarith [mul_nonneg hnu hS, mul_nonneg hl hP]

/-! ## B. Enstrophy and palinstrophy convergence -/

/-- The discrete enstrophy functional converges to the actual interval
integral along the damped Stokes evolution. -/
lemma dampedStokesEvolution_integratedEnstrophy_tendsto
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    Tendsto
      (fun n : ℕ => NSFieldFourier.integratedEnstrophy n
        (fun t => dampedStokesEvolution v nu lam t) T)
      atTop
      (𝓝 (∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))) := by
  unfold NSFieldFourier.integratedEnstrophy
  exact tendsto_leftRiemannSum_integral
    (fun t => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
    hT (dampedStokesEvolution_enstrophy_antitoneOn v nu lam T hnu hl)
    (fun t _ => NSFieldFourier.enstrophy_nonneg _)

/-- At resolution `n`, the discrete enstrophy error is at most
`Ω(0)/n`. -/
lemma dampedStokesEvolution_integratedEnstrophy_error
    (v : NSFieldFourier) (n : ℕ) (nu lam T : ℝ)
    (hn : 0 < n) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    |NSFieldFourier.integratedEnstrophy n
        (fun t => dampedStokesEvolution v nu lam t) T -
      ∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)| ≤
      step n * NSFieldFourier.enstrophy v := by
  unfold NSFieldFourier.integratedEnstrophy
  simpa using abs_leftRiemannSum_sub_integral_le n hn
    (fun t => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
    hT (dampedStokesEvolution_enstrophy_antitoneOn v nu lam T hnu hl)
    (fun t _ => NSFieldFourier.enstrophy_nonneg _)

/-- The discrete palinstrophy functional converges to the actual interval
integral along the damped Stokes evolution. -/
lemma dampedStokesEvolution_integratedPalinstrophy_tendsto
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    Tendsto
      (fun n : ℕ => NSFieldFourier.integratedPalinstrophy n
        (fun t => dampedStokesEvolution v nu lam t) T)
      atTop
      (𝓝 (∫ t in 0..T,
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) := by
  unfold NSFieldFourier.integratedPalinstrophy
  exact tendsto_leftRiemannSum_integral
    (fun t => NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))
    hT (dampedStokesEvolution_palinstrophy_antitoneOn v nu lam T hnu hl)
    (fun t _ => NSFieldFourier.palinstrophy_nonneg _)

/-- At resolution `n`, the discrete palinstrophy error is at most
`P(0)/n`. -/
lemma dampedStokesEvolution_integratedPalinstrophy_error
    (v : NSFieldFourier) (n : ℕ) (nu lam T : ℝ)
    (hn : 0 < n) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    |NSFieldFourier.integratedPalinstrophy n
        (fun t => dampedStokesEvolution v nu lam t) T -
      ∫ t in 0..T,
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)| ≤
      step n * NSFieldFourier.palinstrophy v := by
  unfold NSFieldFourier.integratedPalinstrophy
  simpa using abs_leftRiemannSum_sub_integral_le n hn
    (fun t => NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))
    hT (dampedStokesEvolution_palinstrophy_antitoneOn v nu lam T hnu hl)
    (fun t _ => NSFieldFourier.palinstrophy_nonneg _)

/-! ## C. BKM surrogate and entropic proper-time convergence -/

/-- The older discrete BKM surrogate converges to the actual interval integral
of `Ω + P`. This is a finite Fourier surrogate, not the analytic `L∞` BKM
criterion. -/
lemma dampedStokesEvolution_bkmSurrogateIntegral_tendsto
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    Tendsto
      (fun n : ℕ => NSFieldFourier.bkmSurrogateIntegral n
        (fun t => dampedStokesEvolution v nu lam t) T)
      atTop
      (𝓝 (∫ t in 0..T,
        (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)))) := by
  have hΩ :=
    dampedStokesEvolution_integratedEnstrophy_tendsto
      v nu lam T hnu hl hT
  have hP :=
    dampedStokesEvolution_integratedPalinstrophy_tendsto
      v nu lam T hnu hl hT
  have hadd := hΩ.add hP
  unfold NSFieldFourier.bkmSurrogateIntegral
  rw [intervalIntegral.integral_add
    ((dampedStokesEvolution_enstrophy_continuous v nu lam).intervalIntegrable 0 T)
    ((dampedStokesEvolution_palinstrophy_continuous v nu lam).intervalIntegrable 0 T)]
  exact hadd

/-- At every positive resolution `n`, the discrete BKM-surrogate error is at
most `(Ω(0) + P(0))/n`. -/
lemma dampedStokesEvolution_bkmSurrogateIntegral_error
    (v : NSFieldFourier) (n : ℕ) (nu lam T : ℝ)
    (hn : 0 < n) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    |NSFieldFourier.bkmSurrogateIntegral n
        (fun t => dampedStokesEvolution v nu lam t) T -
      ∫ t in 0..T,
        (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))| ≤
      step n *
        (NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) := by
  have hΩ :=
    dampedStokesEvolution_integratedEnstrophy_error
      v n nu lam T hn hnu hl hT
  have hP :=
    dampedStokesEvolution_integratedPalinstrophy_error
      v n nu lam T hn hnu hl hT
  rw [intervalIntegral.integral_add
    ((dampedStokesEvolution_enstrophy_continuous v nu lam).intervalIntegrable 0 T)
    ((dampedStokesEvolution_palinstrophy_continuous v nu lam).intervalIntegrable 0 T)]
  unfold NSFieldFourier.bkmSurrogateIntegral
  calc
    |(NSFieldFourier.integratedEnstrophy n
          (fun t => dampedStokesEvolution v nu lam t) T +
        NSFieldFourier.integratedPalinstrophy n
          (fun t => dampedStokesEvolution v nu lam t) T) -
      ((∫ t in 0..T,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
        ∫ t in 0..T,
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))|
        =
      |(NSFieldFourier.integratedEnstrophy n
          (fun t => dampedStokesEvolution v nu lam t) T -
        ∫ t in 0..T,
          NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) +
       (NSFieldFourier.integratedPalinstrophy n
          (fun t => dampedStokesEvolution v nu lam t) T -
        ∫ t in 0..T,
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))| := by
            congr 1
            ring
    _ ≤
        |NSFieldFourier.integratedEnstrophy n
            (fun t => dampedStokesEvolution v nu lam t) T -
          ∫ t in 0..T,
            NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)| +
        |NSFieldFourier.integratedPalinstrophy n
            (fun t => dampedStokesEvolution v nu lam t) T -
          ∫ t in 0..T,
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)| :=
      abs_add_le _ _
    _ ≤ step n * NSFieldFourier.enstrophy v +
        step n * NSFieldFourier.palinstrophy v :=
      add_le_add hΩ hP
    _ = step n *
        (NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) := by
      ring

/-- The discrete entropic proper time converges to
`(ν/ħ) ∫₀ᵀ Ω`. No time quantization is asserted. -/
lemma dampedStokesEvolution_entropicProperTime_tendsto
    (v : NSFieldFourier) (nu lam hbar T : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    Tendsto
      (fun n : ℕ => NSFieldFourier.entropicProperTime n
        (fun t => dampedStokesEvolution v nu lam t) nu hbar T)
      atTop
      (𝓝 (nu / hbar * ∫ t in 0..T,
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))) := by
  unfold NSFieldFourier.entropicProperTime
  exact
    (dampedStokesEvolution_integratedEnstrophy_tendsto
      v nu lam T hnu hl hT).const_mul _

/-! ## D. Capstone: discrete BKM limit and certified continuous budget -/

/-- The fixed-step BKM surrogate converges to the actual interval integral,
and that limit is bounded by the initial `H⁰ + H¹` Sobolev budget. -/
lemma dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget
    (v : NSFieldFourier) (nu lam T : ℝ)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    Tendsto
        (fun n : ℕ => NSFieldFourier.bkmSurrogateIntegral n
          (fun t => dampedStokesEvolution v nu lam t) T)
        atTop
        (𝓝 (∫ t in 0..T,
          (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)))) ∧
      (∫ t in 0..T,
          (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) ≤
        (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
          (2 * nu) :=
  ⟨dampedStokesEvolution_bkmSurrogateIntegral_tendsto
      v nu lam T hnu.le hl hT,
    dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget
      v nu lam T hnu hl hT⟩

/-! ## E. Finite-resolution certified budget -/

/-- Every positive fixed-step resolution has an immediately usable certified
budget:

`BKMₙ(T) ≤ (E(0) + Ω(0))/(2ν) + (Ω(0) + P(0))/n`.

Unlike the preceding limit theorem, this statement applies directly to a
specific resolution selected by computation or CI. -/
lemma dampedStokesEvolution_discreteBkm_le_certifiedBudget
    (v : NSFieldFourier) (n : ℕ) (nu lam T : ℝ)
    (hn : 0 < n) (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    NSFieldFourier.bkmSurrogateIntegral n
        (fun t => dampedStokesEvolution v nu lam t) T ≤
      (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
          (2 * nu) +
        step n *
          (NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) := by
  have herr :=
    dampedStokesEvolution_bkmSurrogateIntegral_error
      v n nu lam T hn hnu.le hl hT
  have hdiscrete :
      NSFieldFourier.bkmSurrogateIntegral n
          (fun t => dampedStokesEvolution v nu lam t) T -
        (∫ t in 0..T,
          (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) ≤
        step n *
          (NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) :=
    (le_abs_self _).trans herr
  have hcontinuous :=
    dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget
      v nu lam T hnu hl hT
  linarith

/-! ## F. Tolerance-driven resolution selection -/

/-- A concrete fixed-step resolution sufficient to make the BKM quadrature
remainder smaller than `ε`.

The extra successor makes the defining inequality strict, including when the
ratio `(Ω(0) + P(0))/ε` is already a natural number. -/
noncomputable def bkmToleranceResolution
    (v : NSFieldFourier) (ε : ℝ) : ℕ :=
  Nat.ceil
      ((NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) / ε) +
    1

/-- The selected tolerance resolution is always positive. -/
lemma bkmToleranceResolution_pos (v : NSFieldFourier) (ε : ℝ) :
    0 < bkmToleranceResolution v ε := by
  simp [bkmToleranceResolution]

/-- Every resolution at least the selected threshold has quadrature remainder
strictly below `ε`. -/
lemma bkmToleranceResolution_remainder_lt
    (v : NSFieldFourier) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : bkmToleranceResolution v ε ≤ n) :
    step n *
        (NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v) < ε := by
  let C : ℝ :=
    NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v
  have hratio_ceil : C / ε ≤ (Nat.ceil (C / ε) : ℝ) :=
    Nat.le_ceil _
  have hceil_selected :
      (Nat.ceil (C / ε) : ℝ) <
        (bkmToleranceResolution v ε : ℕ) := by
    simp [bkmToleranceResolution, C]
  have hselected_n :
      (bkmToleranceResolution v ε : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hratio_n : C / ε < (n : ℝ) :=
    hratio_ceil.trans_lt (hceil_selected.trans_le hselected_n)
  have hnpos : 0 < n := (bkmToleranceResolution_pos v ε).trans_le hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC_lt : C < (n : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hratio_n
    simpa [mul_comm] using hratio_n
  rw [show step n * C = C / (n : ℝ) by
    simp [step, div_eq_mul_inv, mul_comm]]
  exact (div_lt_iff₀ hnr).2 (by simpa [mul_comm] using hC_lt)

/-- Any resolution above the concrete tolerance threshold certifies the
discrete BKM surrogate within an additive `ε` of the continuous Sobolev
budget. -/
lemma dampedStokesEvolution_discreteBkm_le_budget_add_tolerance
    (v : NSFieldFourier) (ε : ℝ) (n : ℕ) (nu lam T : ℝ)
    (hε : 0 < ε) (hn : bkmToleranceResolution v ε ≤ n)
    (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    NSFieldFourier.bkmSurrogateIntegral n
        (fun t => dampedStokesEvolution v nu lam t) T ≤
      (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
          (2 * nu) +
        ε := by
  have hnpos : 0 < n := (bkmToleranceResolution_pos v ε).trans_le hn
  have hcert :=
    dampedStokesEvolution_discreteBkm_le_certifiedBudget
      v n nu lam T hnpos hnu hl hT
  have hrem :=
    bkmToleranceResolution_remainder_lt v ε hε n hn
  exact hcert.trans (add_le_add_right hrem.le _)

/-- For every positive requested tolerance, there is a positive resolution
threshold after which every fixed-step BKM surrogate satisfies the certified
continuous budget plus that tolerance. The witness is the explicit
`bkmToleranceResolution`. -/
lemma dampedStokesEvolution_exists_resolution_for_bkm_tolerance
    (v : NSFieldFourier) (ε nu lam T : ℝ)
    (hε : 0 < ε) (hnu : 0 < nu) (hl : 0 ≤ lam) (hT : 0 ≤ T) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      NSFieldFourier.bkmSurrogateIntegral n
          (fun t => dampedStokesEvolution v nu lam t) T ≤
        (NSFieldFourier.kineticEnergy v + NSFieldFourier.enstrophy v) /
            (2 * nu) +
          ε := by
  refine ⟨bkmToleranceResolution v ε, bkmToleranceResolution_pos v ε, ?_⟩
  intro n hn
  exact dampedStokesEvolution_discreteBkm_le_budget_add_tolerance
    v ε n nu lam T hε hn hnu hl hT

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge

end
