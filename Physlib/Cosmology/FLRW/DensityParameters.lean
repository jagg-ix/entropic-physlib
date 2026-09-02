/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
/-!

# Density parameters and the standard cosmological model

The critical density and the density parameters of an FLRW universe.  Formalized
here (leveraging `FriedmannEquation.FirstOrderFriedmann`): the critical density
`ρ_cr = 3H²/(8πG)`, the matter/curvature/dark-energy density parameters, and the
**closure relation** `Ω + Ω_Λ + Ω_K = 1` — the first Friedmann equation divided by
`H²` (`closure_relation`; its `Λ = 0` face `Ω + Ω_K = 1` is `closure_relation_no_lambda`).
The reduced-Hubble-function and age-integral items stay as TODOs.

-/

@[expose] public section

namespace Cosmology.FLRW.DensityParameters

open Time
open Cosmology.FLRW.FriedmannEquation

/-- **The critical density** `ρ_cr = 3H²/(8πG)` — the total energy density of a
spatially flat (`k = 0`, `Λ = 0`) FLRW universe at Hubble rate `H`. -/
noncomputable def criticalDensity (H G : ℝ) : ℝ := 3 * H ^ 2 / (8 * Real.pi * G)

/-- **The (matter) density parameter** `Ω = ρ/ρ_cr = 8πGρ/(3H²)`. -/
noncomputable def densityParameter (ρ H G : ℝ) : ℝ := 8 * Real.pi * G * ρ / (3 * H ^ 2)

/-- The density parameter is the ratio `ρ/ρ_cr`. -/
lemma densityParameter_eq_ratio (ρ H G : ℝ) (hHz : H ≠ 0) (hG : G ≠ 0) :
    densityParameter ρ H G = ρ / criticalDensity H G := by
  unfold densityParameter criticalDensity
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The curvature density parameter** `Ω_K = −kc²/(a²H²)`. -/
noncomputable def curvatureDensityParameter (k a H c : ℝ) : ℝ :=
  -(k * c ^ 2) / (a ^ 2 * H ^ 2)

/-- **The dark-energy density parameter** `Ω_Λ = Λc²/(3H²)`. -/
noncomputable def darkEnergyDensityParameter (Λ H c : ℝ) : ℝ :=
  Λ * c ^ 2 / (3 * H ^ 2)

/-- **[The closure relation] `Ω + Ω_Λ + Ω_K = 1`** — the first Friedmann equation
divided through by `H²`: the density parameters of matter, dark energy and
curvature sum to unity.  A flat universe (`k = 0`) has `Ω + Ω_Λ = 1`; the sign of
`Ω_K` is the sign of `−k`. -/
theorem closure_relation (a ρ : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t)
    (haz : a t ≠ 0) (hHz : hubbleConstant a t ≠ 0) :
    densityParameter (ρ t) (hubbleConstant a t) G
        + darkEnergyDensityParameter Λ (hubbleConstant a t) c
        + curvatureDensityParameter k (a t) (hubbleConstant a t) c = 1 := by
  have haSq : (a t) ^ 2 ≠ 0 := pow_ne_zero 2 haz
  have hHSq : (hubbleConstant a t) ^ 2 ≠ 0 := pow_ne_zero 2 hHz
  -- clear the inner `/a²` from the first Friedmann equation
  have hclean : (∂ₜ a t) ^ 2 * 3
      = 8 * Real.pi * G * ρ t * (a t) ^ 2 - 3 * k * c ^ 2
        + Λ * c ^ 2 * (a t) ^ 2 := by
    have h := hfirst
    unfold FirstOrderFriedmann at h
    rw [div_pow] at h
    field_simp at h
    linear_combination h
  have hHa2 : (hubbleConstant a t) ^ 2 * (a t) ^ 2 = (∂ₜ a t) ^ 2 := by
    simp only [hubbleConstant, div_pow]
    rw [div_mul_cancel₀ _ haSq]
  -- combine the three density parameters over the common denominator `3a²H²`
  have hcommon : densityParameter (ρ t) (hubbleConstant a t) G
        + darkEnergyDensityParameter Λ (hubbleConstant a t) c
        + curvatureDensityParameter k (a t) (hubbleConstant a t) c
      = (8 * Real.pi * G * ρ t * (a t) ^ 2 + Λ * c ^ 2 * (a t) ^ 2 - 3 * k * c ^ 2)
        / (3 * (a t) ^ 2 * (hubbleConstant a t) ^ 2) := by
    unfold densityParameter darkEnergyDensityParameter curvatureDensityParameter
    field_simp
    ring
  rw [hcommon, div_eq_one_iff_eq (by positivity)]
  linear_combination -hclean - 3 * hHa2

/-- **[Closure at `Λ = 0`] `Ω + Ω_K = 1`** — the two-component closure relation
named in the standard cosmology texts. -/
theorem closure_relation_no_lambda (a ρ : Time → ℝ) (k G c : ℝ) (t : Time)
    (hfirst : FirstOrderFriedmann a ρ k 0 G c t)
    (haz : a t ≠ 0) (hHz : hubbleConstant a t ≠ 0) :
    densityParameter (ρ t) (hubbleConstant a t) G
        + curvatureDensityParameter k (a t) (hubbleConstant a t) c = 1 := by
  have h := closure_relation a ρ k 0 G c t hfirst haz hHz
  unfold darkEnergyDensityParameter at h
  rw [show (0 : ℝ) * c ^ 2 / (3 * (hubbleConstant a t) ^ 2) = 0 by ring] at h
  linarith

/-- **[The critical density is the flat total]** at `Ω = 1` (with `Ω_Λ = Ω_K = 0`)
the energy density equals the critical density: `ρ = ρ_cr`. -/
theorem density_eq_critical_of_flat (ρ H G : ℝ)
    (hHz : H ≠ 0) (hG : G ≠ 0) (hΩ : densityParameter ρ H G = 1) :
    ρ = criticalDensity H G := by
  rw [densityParameter_eq_ratio ρ H G hHz hG] at hΩ
  have hcr : criticalDensity H G ≠ 0 := by
    unfold criticalDensity
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    positivity
  field_simp at hΩ
  linarith [hΩ]

end Cosmology.FLRW.DensityParameters

TODO "Define the reduced Hubble function `E(a) = H / H₀` and the normalized
  Friedmann equation `E(a)² = Σ_x Ω_{x0} f_x(a) + Ω_{K0} / a²`."

TODO "Define the Friedmann equation of the standard cosmological model
  `E(a)² = Ω_Λ + Ω_{m0} a⁻³ + Ω_{r0} a⁻⁴ + Ω_{K0} a⁻²`."

TODO "Define the age of the universe `t₀ = H₀⁻¹ ∫₀¹ da / (a E(a))` and prove
  `t₀ ∝ 1 / H₀`."

TODO "Define the radiation-matter and matter-Λ equality scale factors
  `a_eq = Ω_{r0} / Ω_{m0}` and `a_Λ = (Ω_{m0} / Ω_Λ)^(1/3)`."
