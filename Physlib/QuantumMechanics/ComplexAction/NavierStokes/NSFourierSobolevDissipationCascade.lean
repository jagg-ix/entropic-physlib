/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect

/-!
# Finite Fourier Sobolev dissipation cascade

For the repository's diagonal finite Fourier Stokes evolution, this module
proves the exact hierarchy

* `E' = -2ν Ω - 2λ E`,
* `Ω' = -2ν P - 2λ Ω`,
* `P' = -2ν S - 2λ P`,

using the existing kinetic energy, enstrophy, palinstrophy, and
super-palinstrophy. Non-negative viscosity, damping, and time contract all
four levels. The instantaneous BKM-surrogate density `Ω + P` receives its
corresponding exact derivative and contraction theorem.

The enstrophy identity is also connected to the existing `enstrophyRate` and
`imaginaryNoetherDefect` carriers with the explicitly defined bookkeeping
term `VS_eff = -λΩ`. This is not an identification with the nonlinear
Navier--Stokes vortex-stretching integral.

These are finite-dimensional linear Galerkin results. They do not construct
an infinite-dimensional PDE semigroup, add a pressure projection or triadic
nonlinearity, or establish Navier--Stokes existence or regularity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade

open Physlib.QFT.PathIntegral
open NSFieldFourierSobolevHierarchy
open NSFourierDampedStokesSemigroup
open NSVortexStretchingDefect

/-! ## A. Weighted diagonal-energy kernel -/

private lemma dampedStokesEvolution_weightedEnergy_hasDerivAt
    (v : NSFieldFourier) (weight : Fin v.N → ℝ) (nu lam t : ℝ) :
    HasDerivAt
      (fun s => ∑ i : Fin v.N,
        weight i * (dampedStokesEvolution v nu lam s).amp i ^ 2)
      (-2 * nu * ∑ i : Fin v.N,
          weight i * (v.freq i : ℝ) ^ 2 *
            (dampedStokesEvolution v nu lam t).amp i ^ 2 -
        2 * lam * ∑ i : Fin v.N,
          weight i * (dampedStokesEvolution v nu lam t).amp i ^ 2) t := by
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin v.N,
        weight i * (dampedStokesEvolution v nu lam s).amp i ^ 2)
      (∑ i : Fin v.N,
        weight i *
          (2 * (dampedStokesEvolution v nu lam t).amp i *
            (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
              (dampedStokesEvolution v nu lam t).amp i))) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h :=
      ((dampedStokesEvolution_amp_hasDerivAt v nu lam t i).pow 2).const_mul
        (weight i)
    refine
      (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · rfl
    · norm_num
  have hderiv :
      -2 * nu * ∑ i : Fin v.N,
          weight i * (v.freq i : ℝ) ^ 2 *
            (dampedStokesEvolution v nu lam t).amp i ^ 2 -
        2 * lam * ∑ i : Fin v.N,
          weight i * (dampedStokesEvolution v nu lam t).amp i ^ 2 =
      ∑ i : Fin v.N,
        weight i *
          (2 * (dampedStokesEvolution v nu lam t).amp i *
            (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
              (dampedStokesEvolution v nu lam t).amp i)) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hderiv]
  exact hsum

private lemma dampedStokesEvolution_weightedEnergy_le
    (v : NSFieldFourier) (weight : Fin v.N → ℝ) (nu lam t : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    (∑ i : Fin v.N,
        weight i * (dampedStokesEvolution v nu lam t).amp i ^ 2) ≤
      ∑ i : Fin v.N, weight i * v.amp i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  rw [dampedStokesEvolution_amp, mul_pow]
  have hprop_nonneg :
      0 ≤ damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam :=
    (damped_heat_propagator_pos _ _ _).le
  have hprop_le :
      damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam ≤ 1 :=
    damped_heat_propagator_le_one t (nu * (v.freq i : ℝ) ^ 2) lam
      ht (mul_nonneg hnu (sq_nonneg _)) hl
  have hsq :
      damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg
      (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam - 1)]
  have hamp : 0 ≤ v.amp i ^ 2 := sq_nonneg _
  calc
    weight i *
        (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam ^ 2 *
          v.amp i ^ 2)
        ≤ weight i * (1 * v.amp i ^ 2) := by
          gcongr
          exact hweight i
    _ = weight i * v.amp i ^ 2 := by ring

/-! ## B. Exact Sobolev dissipation identities -/

/-- The exact finite-Galerkin enstrophy balance
`Ω'(t) = -2ν P(t) - 2λ Ω(t)`. -/
lemma dampedStokesEvolution_enstrophy_hasDerivAt
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
      (fun s => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam s))
      (-2 * nu * NSFieldFourier.palinstrophy
          (dampedStokesEvolution v nu lam t) -
        2 * lam * NSFieldFourier.enstrophy
          (dampedStokesEvolution v nu lam t)) t := by
  change HasDerivAt
    (fun s => ∑ i : Fin v.N,
      (v.freq i : ℝ) ^ 2 * (dampedStokesEvolution v nu lam s).amp i ^ 2)
    (-2 * nu * ∑ i : Fin v.N,
        (v.freq i : ℝ) ^ 4 * (dampedStokesEvolution v nu lam t).amp i ^ 2 -
      2 * lam * ∑ i : Fin v.N,
        (v.freq i : ℝ) ^ 2 * (dampedStokesEvolution v nu lam t).amp i ^ 2) t
  refine
    (dampedStokesEvolution_weightedEnergy_hasDerivAt
      v (fun i => (v.freq i : ℝ) ^ 2) nu lam t).congr_deriv ?_
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact finite-Galerkin palinstrophy balance
`P'(t) = -2ν S(t) - 2λ P(t)`. -/
lemma dampedStokesEvolution_palinstrophy_hasDerivAt
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
      (fun s => NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam s))
      (-2 * nu * NSFieldFourier.superPalinstrophy
          (dampedStokesEvolution v nu lam t) -
        2 * lam * NSFieldFourier.palinstrophy
          (dampedStokesEvolution v nu lam t)) t := by
  change HasDerivAt
    (fun s => ∑ i : Fin v.N,
      (v.freq i : ℝ) ^ 4 * (dampedStokesEvolution v nu lam s).amp i ^ 2)
    (-2 * nu * ∑ i : Fin v.N,
        (v.freq i : ℝ) ^ 6 * (dampedStokesEvolution v nu lam t).amp i ^ 2 -
      2 * lam * ∑ i : Fin v.N,
        (v.freq i : ℝ) ^ 4 * (dampedStokesEvolution v nu lam t).amp i ^ 2) t
  refine
    (dampedStokesEvolution_weightedEnergy_hasDerivAt
      v (fun i => (v.freq i : ℝ) ^ 4) nu lam t).congr_deriv ?_
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## C. Contraction of the existing Sobolev hierarchy -/

/-- Enstrophy is non-increasing under non-negative viscosity, damping, and
time. -/
lemma dampedStokesEvolution_enstrophy_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) ≤
      NSFieldFourier.enstrophy v := by
  change
    (∑ i : Fin v.N,
      (v.freq i : ℝ) ^ 2 * (dampedStokesEvolution v nu lam t).amp i ^ 2) ≤
      ∑ i : Fin v.N, (v.freq i : ℝ) ^ 2 * v.amp i ^ 2
  exact
    dampedStokesEvolution_weightedEnergy_le
      v (fun i => (v.freq i : ℝ) ^ 2) nu lam t
      (fun _ => by positivity) hnu hl ht

/-- Palinstrophy is non-increasing under non-negative viscosity, damping, and
time. -/
lemma dampedStokesEvolution_palinstrophy_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) ≤
      NSFieldFourier.palinstrophy v := by
  change
    (∑ i : Fin v.N,
      (v.freq i : ℝ) ^ 4 * (dampedStokesEvolution v nu lam t).amp i ^ 2) ≤
      ∑ i : Fin v.N, (v.freq i : ℝ) ^ 4 * v.amp i ^ 2
  exact
    dampedStokesEvolution_weightedEnergy_le
      v (fun i => (v.freq i : ℝ) ^ 4) nu lam t
      (fun _ => by positivity) hnu hl ht

/-- Super-palinstrophy is non-increasing under non-negative viscosity,
damping, and time. -/
lemma dampedStokesEvolution_superPalinstrophy_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t) ≤
      NSFieldFourier.superPalinstrophy v := by
  change
    (∑ i : Fin v.N,
      (v.freq i : ℝ) ^ 6 * (dampedStokesEvolution v nu lam t).amp i ^ 2) ≤
      ∑ i : Fin v.N, (v.freq i : ℝ) ^ 6 * v.amp i ^ 2
  exact
    dampedStokesEvolution_weightedEnergy_le
      v (fun i => (v.freq i : ℝ) ^ 6) nu lam t
      (fun _ => by positivity) hnu hl ht

/-- The complete existing `H⁰`--`H³` finite Fourier hierarchy is
non-increasing under the diagonal damped Stokes evolution. -/
lemma dampedStokesEvolution_sobolevHierarchy_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t) ≤
        NSFieldFourier.kineticEnergy v ∧
      NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) ≤
        NSFieldFourier.enstrophy v ∧
      NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) ≤
        NSFieldFourier.palinstrophy v ∧
      NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t) ≤
        NSFieldFourier.superPalinstrophy v :=
  ⟨dampedStokesEvolution_kineticEnergy_le v nu lam t hnu hl ht,
    dampedStokesEvolution_enstrophy_le v nu lam t hnu hl ht,
    dampedStokesEvolution_palinstrophy_le v nu lam t hnu hl ht,
    dampedStokesEvolution_superPalinstrophy_le v nu lam t hnu hl ht⟩

/-! ## D. Existing enstrophy-rate and defect carriers -/

/-- Express the exact enstrophy derivative through the existing rate carrier
with `VS_eff = -λΩ`. The effective term is bookkeeping for this linear model,
not the nonlinear vortex-stretching integral. -/
lemma dampedStokesEvolution_enstrophy_hasDerivAt_enstrophyRate
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
      (fun s => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam s))
      (enstrophyRate
        (-lam * NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
        nu
        (NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) t := by
  refine (dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t).congr_deriv ?_
  unfold enstrophyRate
  ring

/-- The existing imaginary-defect carrier is non-negative for the effective
linear term `VS_eff = -λΩ` when `ν, λ ≥ 0`. -/
lemma dampedStokesEvolution_effectiveDefect_nonneg
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    0 ≤ imaginaryNoetherDefect nu
      (NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))
      (-lam * NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) := by
  unfold imaginaryNoetherDefect
  have hP := NSFieldFourier.palinstrophy_nonneg (dampedStokesEvolution v nu lam t)
  have hE := NSFieldFourier.enstrophy_nonneg (dampedStokesEvolution v nu lam t)
  have hnuP : 0 ≤ nu * NSFieldFourier.palinstrophy
      (dampedStokesEvolution v nu lam t) := mul_nonneg hnu hP
  have hlamE : 0 ≤ lam * NSFieldFourier.enstrophy
      (dampedStokesEvolution v nu lam t) := mul_nonneg hl hE
  linarith

/-- The effective enstrophy rate of the diagonal damped Stokes evolution is
non-positive for `ν, λ ≥ 0`. -/
lemma dampedStokesEvolution_enstrophyRate_nonpos
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    enstrophyRate
      (-lam * NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t))
      nu
      (NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) ≤ 0 := by
  rw [← defect_nonneg_iff_enstrophyRate_nonpos]
  exact dampedStokesEvolution_effectiveDefect_nonneg v nu lam t hnu hl

/-! ## E. BKM-surrogate density and assembled cascade -/

/-- The instantaneous finite Fourier BKM-surrogate density `Ω + P` has exact
derivative `-2ν(P + S) - 2λ(Ω + P)`. This is not the analytic `L∞`
Beale--Kato--Majda criterion. -/
lemma dampedStokesEvolution_bkmSurrogateDensity_hasDerivAt
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
      (fun s =>
        NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam s) +
          NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam s))
      (-2 * nu *
          (NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) +
            NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t)) -
        2 * lam *
          (NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
            NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t))) t := by
  have h :=
    (dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t).add
      (dampedStokesEvolution_palinstrophy_hasDerivAt v nu lam t)
  refine h.congr_deriv ?_
  ring

/-- The instantaneous finite Fourier BKM-surrogate density is non-increasing
under non-negative viscosity, damping, and time. -/
lemma dampedStokesEvolution_bkmSurrogateDensity_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) +
        NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) ≤
      NSFieldFourier.enstrophy v + NSFieldFourier.palinstrophy v :=
  add_le_add
    (dampedStokesEvolution_enstrophy_le v nu lam t hnu hl ht)
    (dampedStokesEvolution_palinstrophy_le v nu lam t hnu hl ht)

/-- Assemble the exact `H⁰ → H¹ → H² → H³` dissipation cascade from the
existing Fourier/Sobolev functionals. -/
lemma dampedStokesEvolution_sobolevDissipationCascade
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
        (fun s => NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam s))
        (-2 * nu * NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t) -
          2 * lam * NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t)) t ∧
      HasDerivAt
        (fun s => NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam s))
        (-2 * nu * NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t) -
          2 * lam * NSFieldFourier.enstrophy (dampedStokesEvolution v nu lam t)) t ∧
      HasDerivAt
        (fun s => NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam s))
        (-2 * nu * NSFieldFourier.superPalinstrophy (dampedStokesEvolution v nu lam t) -
          2 * lam * NSFieldFourier.palinstrophy (dampedStokesEvolution v nu lam t)) t :=
  ⟨dampedStokesEvolution_kineticEnergy_hasDerivAt v nu lam t,
    dampedStokesEvolution_enstrophy_hasDerivAt v nu lam t,
    dampedStokesEvolution_palinstrophy_hasDerivAt v nu lam t⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade

end
