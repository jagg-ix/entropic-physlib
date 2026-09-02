/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.SpectralInequalities
public import Physlib.FluidDynamics.NavierStokes.NoetherInvariant

/-!
# Torus Fourier Fubini spectral bridge

This file ports the Lean-checkable finite content of
`verification/zil/ns_fourier_deriv_fubini_analysis.zc` §§8-10 into physlib.
It deliberately does not encode paper-outline items as strings, status flags,
or named promises.  Every exported declaration below is a definition or theorem
with a proof term.

The formalized layer is the finite spectral kernel:

* a mode derivative is multiplication by `2π i kᵢ`;
* the squared multiplier norm is the directional derivative weight;
* summing all directions gives `(2π)² · H¹`;
* finite Fubini exchanges the mode and direction sums;
* the `Fin.succAbove` split isolates one torus direction from the remaining
  directions;
* Cauchy-Schwarz gives the finite `H¹² ≤ H⁰ · H²` spectral estimate;
* the same spectral scale links to the Navier-Stokes enstrophy hierarchy and
  to the entropic proper-time rate carrier.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.FubiniSpectral

open TorusFourier.DerivativeMultiplier
open TorusFourier.SpectralInequalities
open TorusFourier.PeriodicTorusFourierSobolev
open NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.FluidDynamics.NavierStokes.NoetherInvariant


/-- The Fourier-space eigenvalue of the `i`-th torus derivative generator. -/
def torusDerivativeGeneratorEigenvalue {ι : Type*} (i : ι) (k : ι → ℤ) : ℂ :=
  fourierDerivativeMultiplier i k

@[simp]
lemma torusDerivativeGeneratorEigenvalue_eq {ι : Type*} (i : ι) (k : ι → ℤ) :
    torusDerivativeGeneratorEigenvalue i k =
      ((2 * Real.pi * (k i : ℝ)) : ℂ) * Complex.I := by
  rfl

/-- If the mode has zero `i`-component, the `i`-th derivative generator has zero eigenvalue. -/
lemma torusDerivativeGeneratorEigenvalue_zero_component {ι : Type*}
    (i : ι) (k : ι → ℤ) (hki : k i = 0) :
    torusDerivativeGeneratorEigenvalue i k = 0 := by
  simp [torusDerivativeGeneratorEigenvalue, fourierDerivativeMultiplier, hki]

/--
Finite replacement for the analytic spectral-generator identity:
the derivative coefficient is the generator eigenvalue times the Fourier
amplitude.
-/
lemma directionalDerivativeCoeff_eq_generator_mul {ι : Type*}
    (i : ι) (k : ι → ℤ) (amp : ℝ) :
    directionalDerivativeCoeff i k amp =
      torusDerivativeGeneratorEigenvalue i k * (amp : ℂ) := by
  rfl

/-- The finite spectral-generator coefficient has the expected squared norm. -/
lemma finite_spectral_generator_norm_sq {ι : Type*}
    (i : ι) (k : ι → ℤ) (amp : ℝ) :
    ‖directionalDerivativeCoeff i k amp‖ ^ 2 =
      directionalDerivativeWeight i k amp :=
  norm_sq_directionalDerivativeCoeff i k amp

variable {ι : Type*} [Fintype ι] (F : FiniteTorusFourierFamily ι)

/--
Finite Plancherel/H¹ realization: summing the squared derivative-generator
weights gives `(2π)²` times the finite Fourier `H¹` seminorm.
-/
lemma finite_spectral_generator_h1_realization :
    finiteTorusGradientEnergy F = derivativeScale * F.h1Seminorm :=
  finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm F

/--
Finite spectral estimate that downstream EPT/BKM code can use now:
the squared gradient energy is controlled by `H⁰ · H²`.
-/
lemma finite_spectral_generator_agmon_kernel :
    finiteTorusGradientEnergy F ^ 2 ≤
      derivativeScale ^ 2 * (F.l2Energy * finiteTorusH2Seminorm F) :=
  finiteTorusGradientEnergy_sq_le_scaled_l2_mul_h2 F

/--
Under Constantin-Iyer (`ℏ = 2ν`), if an EPT enstrophy profile `Omega`
is represented at time `t` by the finite torus gradient energy, then the
entropic-time rate is half the finite spectral `H¹` energy.
-/
lemma entropicProperTimeRate_eq_half_finite_spectral_h1_under_CI
    (c : EnstrophyEPTConstants) (hCI : c.CI) (Omega : ℝ → ℝ) (t : ℝ)
    (hOmega : Omega t = finiteTorusGradientEnergy F) :
    entropicProperTimeRate c Omega t =
      (1 / 2 : ℝ) * (derivativeScale * F.h1Seminorm) := by
  rw [entropicProperTimeRate_under_CI c hCI Omega t, hOmega,
    finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm F]


/-- Finite Fubini for sums over a product index. -/
lemma finite_product_sum_fubini {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (w : α × β → R) :
    (∑ p : α × β, w p) = ∑ a : α, ∑ b : β, w (a, b) := by
  classical
  rw [← Finset.sum_product]
  simp

/-- Finite tensoriality for the mode/direction derivative-energy sum. -/
lemma finite_gradient_energy_fubini :
    finiteTorusGradientEnergy F =
      ∑ i : ι, finiteTorusDirectionalDerivativeEnergy F i := by
  unfold finiteTorusGradientEnergy finiteTorusDirectionalDerivativeEnergy
  rw [Finset.sum_comm]

/--
Finite `Tⁿ⁺¹ ≃ T¹ᵢ × Tⁿ` direction split: the total gradient energy is the
chosen fiber direction plus the remaining `succAbove` directions.
-/
lemma finite_gradient_energy_direction_split {n : ℕ}
    (F : FiniteTorusFourierFamily (Fin n.succ)) (i : Fin n.succ) :
    finiteTorusGradientEnergy F =
      finiteTorusDirectionalDerivativeEnergy F i +
        ∑ j : Fin n, finiteTorusDirectionalDerivativeEnergy F (Fin.succAbove i j) := by
  rw [finite_gradient_energy_fubini]
  exact Fin.sum_univ_succAbove (fun j => finiteTorusDirectionalDerivativeEnergy F j) i


/--
The connected finite kernel available today: derivative multiplier, finite H¹
Plancherel, finite `H¹² ≤ H⁰·H²`, EPT rate under Constantin-Iyer, and the
Navier-Stokes Fourier enstrophy/palinstrophy inequality.  This theorem avoids
claiming the full analytic BKM criterion; it states only the finite pieces that
are already proved in physlib.
-/
lemma finite_ept_spectral_enstrophy_kernel
    (F : FiniteTorusFourierFamily (Fin 3))
    (v : NSFieldFourier)
    (c : EnstrophyEPTConstants) (hCI : c.CI) (Omega : ℝ → ℝ) (t : ℝ)
    (hOmega : Omega t = finiteTorusGradientEnergy F) (i : Fin 3) :
    finiteTorusGradientEnergy F =
        finiteTorusDirectionalDerivativeEnergy F i +
          ∑ j : Fin 2, finiteTorusDirectionalDerivativeEnergy F (Fin.succAbove i j)
      ∧ finiteTorusGradientEnergy F = derivativeScale * F.h1Seminorm
      ∧ finiteTorusGradientEnergy F ^ 2 ≤
          derivativeScale ^ 2 * (F.l2Energy * finiteTorusH2Seminorm F)
      ∧ entropicProperTimeRate c Omega t =
          (1 / 2 : ℝ) * (derivativeScale * F.h1Seminorm)
      ∧ v.enstrophy ^ 2 ≤ v.kineticEnergy * v.palinstrophy := by
  exact
    ⟨finite_gradient_energy_direction_split F i,
      finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm F,
      finiteTorusGradientEnergy_sq_le_scaled_l2_mul_h2 F,
      entropicProperTimeRate_eq_half_finite_spectral_h1_under_CI F c hCI Omega t hOmega,
      TorusFourier.SpectralInequalities.NSField.enstrophy_sq_le_kineticEnergy_mul_palinstrophy v⟩

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.FubiniSpectral

end
