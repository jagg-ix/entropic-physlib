/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CurvatureEntropyCouplingKernel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

/-!
# ADM strain, Noether defect, and entropy production

Ports the useful ADM/relative-entropy algebra from the helper repository under
standard names and connects it to the existing Navier-Stokes and
curvature/entropy kernels.

The file contains:

* a finite-dimensional strain tensor with an incompressible trace law;
* the ADM lapse `N = Omega / (2 nu)` and extrinsic curvature `K = S / N`;
* symmetry and trace-zero propagation from strain to `K`;
* the scalar relative-entropy analog `Omega / (2 nu)`;
* the Noether defect `nu P - VS`, reusing `NavierStokes.NSVortexStretchingDefect`;
* a bridge to the local curvature/entropy production rate.

No helper namespaces or helper-specific abbreviations are imported.


-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ADMStrainEntropyProduction

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CurvatureEntropyCouplingKernel

variable {ι : Type*} [Fintype ι]

/-- A symmetric strain tensor with the incompressible trace condition. -/
structure StrainTensorData (ι : Type*) [Fintype ι] where
  components : Matrix ι ι ℝ
  symm : ∀ i j : ι, components i j = components j i
  trace_zero : (∑ i : ι, components i i) = 0

/-- ADM geometric data induced by strain, enstrophy, and viscosity. -/
structure ADMStrainGeometry (ι : Type*) [Fintype ι] where
  enstrophy : ℝ
  enstrophy_pos : 0 < enstrophy
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  strain : StrainTensorData ι
  lapse : ℝ
  lapse_eq : lapse = enstrophy / (2 * viscosity)
  lapse_pos : 0 < lapse

/-- Canonical ADM strain geometry with lapse `N = Omega / (2 nu)`. -/
noncomputable def ADMStrainGeometry.mkCanonical
    (Omega nu : ℝ) (hOmega : 0 < Omega) (hnu : 0 < nu) (S : StrainTensorData ι) :
    ADMStrainGeometry ι where
  enstrophy := Omega
  enstrophy_pos := hOmega
  viscosity := nu
  viscosity_pos := hnu
  strain := S
  lapse := Omega / (2 * nu)
  lapse_eq := rfl
  lapse_pos := div_pos hOmega (mul_pos two_pos hnu)

/-- ADM extrinsic curvature components `K_ij = S_ij / N`. -/
noncomputable def extrinsicCurvature (G : ADMStrainGeometry ι) : Matrix ι ι ℝ :=
  fun i j => G.strain.components i j / G.lapse

/-- With `N = Omega/(2 nu)`, the ADM curvature is `K_ij = S_ij * (2 nu / Omega)`. -/
lemma extrinsicCurvature_eq_strain_scaled
    (G : ADMStrainGeometry ι) (i j : ι) :
    extrinsicCurvature G i j =
      G.strain.components i j * (2 * G.viscosity / G.enstrophy) := by
  unfold extrinsicCurvature
  rw [G.lapse_eq]
  have hOmega : G.enstrophy ≠ 0 := ne_of_gt G.enstrophy_pos
  have hTwoNu : (2 * G.viscosity : ℝ) ≠ 0 := by nlinarith [G.viscosity_pos]
  field_simp [hOmega, hTwoNu]

/-- Symmetric strain induces symmetric extrinsic curvature. -/
lemma extrinsicCurvature_symm (G : ADMStrainGeometry ι) :
    Matrix.transpose (extrinsicCurvature G) = extrinsicCurvature G := by
  ext i j
  simpa [extrinsicCurvature, Matrix.transpose_apply] using
    congrArg (fun a : ℝ => a / G.lapse) (G.strain.symm j i)

/-- Incompressible strain gives trace-free ADM extrinsic curvature. -/
lemma extrinsicCurvature_trace_zero (G : ADMStrainGeometry ι) :
    (∑ i : ι, extrinsicCurvature G i i) = 0 := by
  unfold extrinsicCurvature
  have hsum :
      (∑ i : ι, G.strain.components i i / G.lapse) =
        (∑ i : ι, G.strain.components i i) / G.lapse := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  rw [hsum, G.strain.trace_zero, zero_div]

/-- The Navier-Stokes relative-entropy analog `S_rel = Omega/(2 nu)`. -/
noncomputable def relativeEntropyFromEnstrophy (Omega nu : ℝ) : ℝ :=
  Omega / (2 * nu)

/-- Positivity of `Omega/(2 nu)`. -/
lemma relativeEntropyFromEnstrophy_nonneg (Omega nu : ℝ) (hOmega : 0 ≤ Omega) (hnu : 0 < nu) :
    0 ≤ relativeEntropyFromEnstrophy Omega nu := by
  unfold relativeEntropyFromEnstrophy
  exact div_nonneg hOmega (le_of_lt (mul_pos two_pos hnu))

/-- The Noether defect `nu P - VS`, reusing the existing NS kernel. -/
abbrev noetherDefect (nu P VS : ℝ) : ℝ :=
  imaginaryNoetherDefect nu P VS

/-- The ADM lapse is the relative-entropy analog `Omega/(2 nu)`. -/
lemma canonical_lapse_eq_relativeEntropyFromEnstrophy
    (Omega nu : ℝ) (hOmega : 0 < Omega) (hnu : 0 < nu) (S : StrainTensorData ι) :
    (ADMStrainGeometry.mkCanonical (ι := ι) Omega nu hOmega hnu S).lapse =
      relativeEntropyFromEnstrophy Omega nu := by
  rfl

/-- Defect positivity is exactly the `VS <= nu P` condition. -/
lemma noetherDefect_nonneg_iff_vs_le_nuP (nu P VS : ℝ) :
    0 ≤ noetherDefect nu P VS ↔ VS ≤ nu * P := by
  exact defect_nonneg_iff nu P VS

/-- If the enstrophy rate is `2(VS - nu P)`, then the entropy rate is `-(nu P - VS)/nu`. -/
lemma relativeEntropyRate_eq_neg_defect_over_viscosity
    (dS VS nu P : ℝ) (hnu : nu ≠ 0)
    (hRate : dS = enstrophyRate VS nu P / (2 * nu)) :
    dS = -noetherDefect nu P VS / nu := by
  rw [hRate]
  unfold enstrophyRate noetherDefect imaginaryNoetherDefect
  field_simp [hnu]
  ring

/-- For positive viscosity, nonnegative defect is exactly nonpositive entropy-production rate. -/
lemma relativeEntropyRate_nonpos_iff_defect_nonneg
    (D nu : ℝ) (hnu : 0 < nu) :
    -D / nu ≤ 0 ↔ 0 ≤ D := by
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hnu)
    have hnu_ne : nu ≠ 0 := ne_of_gt hnu
    have hneg : -D ≤ 0 := by
      simpa [hnu_ne] using hmul
    linarith
  · intro hD
    have hneg : -D ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hneg (le_of_lt hnu)

/-- The entropy-rate criterion is the same `VS <= nu P` condition. -/
lemma relativeEntropyRate_nonpos_iff_vs_le_nuP
    (VS nu P : ℝ) (hnu : 0 < nu) :
    -noetherDefect nu P VS / nu ≤ 0 ↔ VS ≤ nu * P := by
  rw [relativeEntropyRate_nonpos_iff_defect_nonneg (D := noetherDefect nu P VS) (nu := nu) hnu]
  exact noetherDefect_nonneg_iff_vs_le_nuP nu P VS

/-- ADM trace-freeness, defect positivity, and entropy monotonicity assembled. -/
lemma adm_strain_entropy_production_bridge
    (G : ADMStrainGeometry ι) (VS P : ℝ) :
    (∑ i : ι, extrinsicCurvature G i i) = 0
      ∧ (0 ≤ noetherDefect G.viscosity P VS ↔ VS ≤ G.viscosity * P)
      ∧ (-noetherDefect G.viscosity P VS / G.viscosity ≤ 0
          ↔ VS ≤ G.viscosity * P) := by
  exact ⟨extrinsicCurvature_trace_zero G,
    noetherDefect_nonneg_iff_vs_le_nuP G.viscosity P VS,
    relativeEntropyRate_nonpos_iff_vs_le_nuP VS G.viscosity P G.viscosity_pos⟩

/-- The ADM/Noether defect criterion is compatible with the existing local curvature/entropy production
rate: under the same positivity hypotheses, both the defect and the local rate are nonnegative. -/
lemma defect_and_curvatureEntropyProduction_nonneg
    (VS nu P kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hreg : VS ≤ nu * P)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 ≤ noetherDefect nu P VS
      ∧ 0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi := by
  exact ⟨(noetherDefect_nonneg_iff_vs_le_nuP nu P VS).mpr hreg,
    localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
      hkB hbeta hredshift hlambda0 halpha heps hgamma hricci⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ADMStrainEntropyProduction

end
