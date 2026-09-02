/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
public import Physlib.SpaceAndTime.Space.Translations

/-!
# Distributional static weak-field Einstein `00` equation

The smooth, connection-derived `3+1` carrier proves

`G₀₀^(1) = 2 ∇²Φ / c²`.

This module continues that already-derived scalar coefficient to distribution-valued potentials.
For a scalar distribution `Φ` and mass-density distribution `ρ`, it defines

* `G₀₀^(1)[Φ] = (2/c²) • ΔᵈΦ`;
* `T₀₀[ρ] = c² • ρ`;
* the distributional linearized equation
  `G₀₀^(1)[Φ] = (8πG/c⁴) • T₀₀[ρ]`.

For `c ≠ 0`, this equation is equivalent to the distributional Poisson law
`ΔᵈΦ = (4πG) • ρ`.  The construction commutes with spatial translations.

Only the scalar, static, linearized `00` equation is extended to distributions here.  No full
distribution-valued curvature tensor, multiplication of singular distributions, smooth rest-dust
field, or exact nonlinear Einstein solution is asserted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00

open scoped Space
open Physlib
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1

/-! ## A. Smooth normalization and its distributional continuation -/

/-- The smooth connection-derived carrier fixes the `00` coefficient used below. -/
lemma weakFieldLinearizedEinstein4Spatial_apply_00
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    weakFieldLinearizedEinstein4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c 0 0 =
      2 * spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2 := by
  rw [weakFieldLinearizedEinstein4Spatial_eq]
  rfl

/-- The distribution-valued continuation of the static linearized Einstein `00` component. -/
def weakFieldLinearizedEinstein00Distribution3
    (c : ℝ) (Φ : (Space 3) →d[ℝ] ℝ) : (Space 3) →d[ℝ] ℝ :=
  (2 / c ^ 2) • Δᵈ Φ

/-- The distribution-valued rest-energy density `T₀₀ = c²ρ`. -/
def restDustStressEnergy00Distribution3
    (c : ℝ) (ρ : (Space 3) →d[ℝ] ℝ) : (Space 3) →d[ℝ] ℝ :=
  c ^ 2 • ρ

/-! ## B. Distributional Einstein-Poisson equivalence -/

/-- The scalar distributional static linearized Einstein `00` equation. -/
def DistributionalWeakFieldEinstein00Equation3
    (G c : ℝ) (Φ ρ : (Space 3) →d[ℝ] ℝ) : Prop :=
  weakFieldLinearizedEinstein00Distribution3 c Φ =
    (8 * Real.pi * G / c ^ 4) • restDustStressEnergy00Distribution3 c ρ

/-- Distributional Poisson implies the static linearized Einstein `00` equation. -/
lemma distributionalWeakFieldEinstein00Equation3_of_poisson
    (G c : ℝ) (Φ ρ : (Space 3) →d[ℝ] ℝ) (hc : c ≠ 0)
    (hPoisson : Δᵈ Φ = (4 * Real.pi * G) • ρ) :
    DistributionalWeakFieldEinstein00Equation3 G c Φ ρ := by
  unfold DistributionalWeakFieldEinstein00Equation3
    weakFieldLinearizedEinstein00Distribution3 restDustStressEnergy00Distribution3
  rw [hPoisson]
  simp only [smul_smul]
  congr 1
  field_simp [hc]
  ring

/-- The static linearized Einstein `00` equation recovers distributional Poisson. -/
lemma poisson_of_distributionalWeakFieldEinstein00Equation3
    (G c : ℝ) (Φ ρ : (Space 3) →d[ℝ] ℝ) (hc : c ≠ 0)
    (hEFE : DistributionalWeakFieldEinstein00Equation3 G c Φ ρ) :
    Δᵈ Φ = (4 * Real.pi * G) • ρ := by
  unfold DistributionalWeakFieldEinstein00Equation3
    weakFieldLinearizedEinstein00Distribution3 restDustStressEnergy00Distribution3 at hEFE
  have hscaled := congrArg (fun T : (Space 3) →d[ℝ] ℝ => (c ^ 2 / 2) • T) hEFE
  simp only [smul_smul] at hscaled
  have hleft : (c ^ 2 / 2) * (2 / c ^ 2) = 1 := by
    field_simp [hc]
  have hright :
      (c ^ 2 / 2) * ((8 * Real.pi * G / c ^ 4) * c ^ 2) = 4 * Real.pi * G := by
    field_simp [hc]
    ring
  rw [hleft, hright, one_smul] at hscaled
  exact hscaled

/-- For nonzero `c`, distributional Poisson and the scalar linearized Einstein equation coincide. -/
lemma distributionalWeakFieldEinstein00Equation3_iff_poisson
    (G c : ℝ) (Φ ρ : (Space 3) →d[ℝ] ℝ) (hc : c ≠ 0) :
    DistributionalWeakFieldEinstein00Equation3 G c Φ ρ ↔
      Δᵈ Φ = (4 * Real.pi * G) • ρ :=
  ⟨poisson_of_distributionalWeakFieldEinstein00Equation3 G c Φ ρ hc,
    distributionalWeakFieldEinstein00Equation3_of_poisson G c Φ ρ hc⟩

/-! ## C. Spatial translation covariance -/

/-- The distributional weak-field Einstein `00` carrier commutes with translations. -/
lemma weakFieldLinearizedEinstein00Distribution3_translate
    (a : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (Φ : (Space 3) →d[ℝ] ℝ) :
    weakFieldLinearizedEinstein00Distribution3 c (Space.distTranslate a Φ) =
      Space.distTranslate a (weakFieldLinearizedEinstein00Distribution3 c Φ) := by
  rw [weakFieldLinearizedEinstein00Distribution3,
    weakFieldLinearizedEinstein00Distribution3,
    Space.distLaplacian_distTranslate, map_smul]

/-- The distribution-valued rest-energy carrier commutes with translations. -/
lemma restDustStressEnergy00Distribution3_translate
    (a : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (ρ : (Space 3) →d[ℝ] ℝ) :
    restDustStressEnergy00Distribution3 c (Space.distTranslate a ρ) =
      Space.distTranslate a (restDustStressEnergy00Distribution3 c ρ) := by
  rw [restDustStressEnergy00Distribution3, restDustStressEnergy00Distribution3, map_smul]

/-- A common translation of potential and source preserves the scalar distributional equation. -/
lemma DistributionalWeakFieldEinstein00Equation3.translate
    {G c : ℝ} {Φ ρ : (Space 3) →d[ℝ] ℝ}
    (hEFE : DistributionalWeakFieldEinstein00Equation3 G c Φ ρ)
    (a : EuclideanSpace ℝ (Fin 3)) :
    DistributionalWeakFieldEinstein00Equation3 G c
      (Space.distTranslate a Φ) (Space.distTranslate a ρ) := by
  unfold DistributionalWeakFieldEinstein00Equation3 at hEFE ⊢
  rw [weakFieldLinearizedEinstein00Distribution3_translate,
    restDustStressEnergy00Distribution3_translate, ← map_smul, hEFE]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00

end
