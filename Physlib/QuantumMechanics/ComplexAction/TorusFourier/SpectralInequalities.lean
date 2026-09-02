/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.DerivativeMultiplier
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Torus Fourier spectral inequalities

This file ports the clean finite Fourier Cauchy-Schwarz inequalities into the
canonical physlib torus-Fourier layer.

For a finite periodic torus family, it proves the spectral interpolation
estimate

`H¹² ≤ H⁰ · H²`.

Combined with `TorusFourier.DerivativeMultiplier`, this gives a checked
gradient-energy estimate for the finite derivative multiplier:

`‖∇F‖²² ≤ (2π)⁴ · H⁰ · H²`.

The file also ports the same Cauchy-Schwarz pattern to the existing real
`NSFieldFourier` hierarchy (`kineticEnergy`, `enstrophy`, `palinstrophy`,
`superPalinstrophy`) and keeps a bridge theorem connecting both surfaces.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.SpectralInequalities

open TorusFourier.PeriodicTorusFourierSobolev
open TorusFourier.DerivativeMultiplier
open NavierStokes.NSFieldFourierSobolevHierarchy

/-! ## Finite torus Fourier spectral scale -/

variable {ι : Type*} [Fintype ι] (F : FiniteTorusFourierFamily ι)

/-- Finite `H²` Fourier seminorm of a periodic torus family. -/
def finiteTorusH2Seminorm : ℝ :=
  ∑ n : Fin F.N, torusWaveNumberSq (F.wave n) ^ 2 * F.amp n ^ 2

/-- The finite `H²` seminorm is nonnegative. -/
lemma finiteTorusH2Seminorm_nonneg : 0 ≤ finiteTorusH2Seminorm F := by
  unfold finiteTorusH2Seminorm
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)

/--
Finite torus Fourier interpolation: the squared `H¹` seminorm is bounded by
the product of the `H⁰` energy and the `H²` seminorm.
-/
lemma finiteTorusH1_sq_le_l2_mul_h2 :
    F.h1Seminorm ^ 2 ≤ F.l2Energy * finiteTorusH2Seminorm F := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun n : Fin F.N => F.amp n)
    (g := fun n : Fin F.N => torusWaveNumberSq (F.wave n) * F.amp n)
  calc
    F.h1Seminorm ^ 2
        = (∑ n : Fin F.N,
            F.amp n * (torusWaveNumberSq (F.wave n) * F.amp n)) ^ 2 := by
          unfold TorusFourier.PeriodicTorusFourierSobolev.FiniteTorusFourierFamily.h1Seminorm
            TorusFourier.PeriodicTorusFourierSobolev.fourierH1Weight
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          ring
    _ ≤ (∑ n : Fin F.N, F.amp n ^ 2) *
        ∑ n : Fin F.N, (torusWaveNumberSq (F.wave n) * F.amp n) ^ 2 := hcs
    _ = F.l2Energy * finiteTorusH2Seminorm F := by
          unfold TorusFourier.PeriodicTorusFourierSobolev.FiniteTorusFourierFamily.l2Energy
            finiteTorusH2Seminorm
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          ring

/--
The derivative-multiplier gradient energy satisfies the scaled spectral
interpolation estimate.
-/
lemma finiteTorusGradientEnergy_sq_le_scaled_l2_mul_h2 :
    finiteTorusGradientEnergy F ^ 2 ≤
      derivativeScale ^ 2 * (F.l2Energy * finiteTorusH2Seminorm F) := by
  rw [finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm F]
  calc
    (derivativeScale * F.h1Seminorm) ^ 2 =
        derivativeScale ^ 2 * F.h1Seminorm ^ 2 := by
          ring
    _ ≤ derivativeScale ^ 2 * (F.l2Energy * finiteTorusH2Seminorm F) :=
        mul_le_mul_of_nonneg_left
          (finiteTorusH1_sq_le_l2_mul_h2 F)
          (sq_nonneg derivativeScale)

/-- A finite bandlimit controls the `H²` seminorm by the `H¹` seminorm. -/
lemma finiteTorusH2Seminorm_le_bandlimit_mul_h1
    (K : ℝ)
    (hBand : ∀ n : Fin F.N, torusWaveNumberSq (F.wave n) ≤ K) :
    finiteTorusH2Seminorm F ≤ K * F.h1Seminorm := by
  unfold finiteTorusH2Seminorm
    TorusFourier.PeriodicTorusFourierSobolev.FiniteTorusFourierFamily.h1Seminorm
    TorusFourier.PeriodicTorusFourierSobolev.fourierH1Weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  let a : ℝ := torusWaveNumberSq (F.wave n)
  let b : ℝ := F.amp n ^ 2
  have ha : 0 ≤ a := torusWaveNumberSq_nonneg (F.wave n)
  have hb : 0 ≤ b := sq_nonneg _
  have haK : a ≤ K := hBand n
  calc
    torusWaveNumberSq (F.wave n) ^ 2 * F.amp n ^ 2
        = a * (a * b) := by
          simp [a, b]
          ring
    _ ≤ K * (a * b) :=
        mul_le_mul_of_nonneg_right haK (mul_nonneg ha hb)
    _ = K * (torusWaveNumberSq (F.wave n) * F.amp n ^ 2) := by
        simp [a, b]

/-! ## Navier-Stokes scalar Fourier hierarchy -/

namespace NSField

open NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/--
Fourier Agmon/Cauchy-Schwarz inequality:
`enstrophy² ≤ kineticEnergy · palinstrophy`.
-/
lemma enstrophy_sq_le_kineticEnergy_mul_palinstrophy
    (v : NSFieldFourier) :
    v.enstrophy ^ 2 ≤ v.kineticEnergy * v.palinstrophy := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : Fin v.N => v.amp i)
    (g := fun i : Fin v.N => (v.freq i : ℝ) ^ 2 * v.amp i)
  calc
    v.enstrophy ^ 2
        = (∑ i : Fin v.N,
            v.amp i * ((v.freq i : ℝ) ^ 2 * v.amp i)) ^ 2 := by
          unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i : Fin v.N, v.amp i ^ 2) *
        ∑ i : Fin v.N, ((v.freq i : ℝ) ^ 2 * v.amp i) ^ 2 := hcs
    _ = v.kineticEnergy * v.palinstrophy := by
          unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy
            NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring

/--
Next-level Fourier Agmon/Cauchy-Schwarz inequality:
`palinstrophy² ≤ enstrophy · superPalinstrophy`.
-/
lemma palinstrophy_sq_le_enstrophy_mul_superPalinstrophy
    (v : NSFieldFourier) :
    v.palinstrophy ^ 2 ≤ v.enstrophy * v.superPalinstrophy := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : Fin v.N => (v.freq i : ℝ) * v.amp i)
    (g := fun i : Fin v.N => (v.freq i : ℝ) ^ 3 * v.amp i)
  calc
    v.palinstrophy ^ 2
        = (∑ i : Fin v.N,
            ((v.freq i : ℝ) * v.amp i) *
              ((v.freq i : ℝ) ^ 3 * v.amp i)) ^ 2 := by
          unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i : Fin v.N, ((v.freq i : ℝ) * v.amp i) ^ 2) *
        ∑ i : Fin v.N, ((v.freq i : ℝ) ^ 3 * v.amp i) ^ 2 := hcs
    _ = v.enstrophy * v.superPalinstrophy := by
          unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy
            NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.superPalinstrophy
          congr 1 <;>
            (apply Finset.sum_congr rfl; intro i _; ring)

/--
Monotone Fourier energy hierarchy under the torus spectral gap:
`H⁰ ≤ H¹ ≤ H² ≤ H³`.
-/
lemma energy_hierarchy
    (v : NSFieldFourier) (hfreq : ∀ i : Fin v.N, 1 ≤ v.freq i) :
    v.kineticEnergy ≤ v.enstrophy ∧
      v.enstrophy ≤ v.palinstrophy ∧
      v.palinstrophy ≤ v.superPalinstrophy := by
  refine ⟨poincare v hfreq, ?_, ?_⟩
  · unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy
      NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy
    apply Finset.sum_le_sum
    intro i _
    have hk : (1 : ℝ) ≤ (v.freq i : ℝ) := by
      exact_mod_cast hfreq i
    have hk2 : (1 : ℝ) ≤ (v.freq i : ℝ) ^ 2 := by nlinarith
    calc
      (v.freq i : ℝ) ^ 2 * v.amp i ^ 2
          = 1 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := by ring
      _ ≤ (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) :=
          mul_le_mul_of_nonneg_right hk2
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (v.freq i : ℝ) ^ 4 * v.amp i ^ 2 := by ring
  · unfold NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy
      NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.superPalinstrophy
    apply Finset.sum_le_sum
    intro i _
    have hk : (1 : ℝ) ≤ (v.freq i : ℝ) := by
      exact_mod_cast hfreq i
    have hk2 : (1 : ℝ) ≤ (v.freq i : ℝ) ^ 2 := by nlinarith
    calc
      (v.freq i : ℝ) ^ 4 * v.amp i ^ 2
          = 1 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) := by ring
      _ ≤ (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) :=
          mul_le_mul_of_nonneg_right hk2
            (mul_nonneg (by positivity) (sq_nonneg _))
      _ = (v.freq i : ℝ) ^ 6 * v.amp i ^ 2 := by ring

/-- The Agmon estimate plus the spectral gap gives `enstrophy² ≤ enstrophy · palinstrophy`. -/
lemma enstrophy_sq_le_enstrophy_mul_palinstrophy_of_gap
    (v : NSFieldFourier) (hfreq : ∀ i : Fin v.N, 1 ≤ v.freq i) :
    v.enstrophy ^ 2 ≤ v.enstrophy * v.palinstrophy := by
  exact le_trans
    (enstrophy_sq_le_kineticEnergy_mul_palinstrophy v)
    (mul_le_mul_of_nonneg_right (poincare v hfreq) (palinstrophy_nonneg v))

end NSField

/-! ## Bridge between the finite torus and NS Fourier surfaces -/

/--
The finite torus interpolation theorem, the derivative-multiplier estimate, and
the existing NS Fourier hierarchy satisfy the same Cauchy-Schwarz spectral
pattern.
-/
lemma finite_torus_gradient_and_ns_spectral_agmon
    (F : FiniteTorusFourierFamily (Fin 3))
    (v : NSFieldFourier) :
    F.h1Seminorm ^ 2 ≤ F.l2Energy * finiteTorusH2Seminorm F
      ∧ finiteTorusGradientEnergy F ^ 2 ≤
          derivativeScale ^ 2 * (F.l2Energy * finiteTorusH2Seminorm F)
      ∧ v.enstrophy ^ 2 ≤ v.kineticEnergy * v.palinstrophy :=
  ⟨finiteTorusH1_sq_le_l2_mul_h2 F,
    finiteTorusGradientEnergy_sq_le_scaled_l2_mul_h2 F,
    NSField.enstrophy_sq_le_kineticEnergy_mul_palinstrophy v⟩

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.SpectralInequalities

end
