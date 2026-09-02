/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaResummation
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay
public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

/-!
# Path-integral diagonalization and tunneling entropy bridge

This file records two concrete links that were implicit across the repo.

* **CSW side.** The theta heat equation, Poisson/theta resummation, Verlinde convolution
  theorem, and Wilson/Verlinde diagonalization are the same Fourier diagonalization
  read at four levels: one theta mode, the theta multiplet, the fusion convolution, and
  Wilson-loop operators.
* **Tunneling/resonance side.** Bhaduri's inverted-oscillator resonance
  `E = (n+1/2)a - i(l+1/2)b` has imaginary part exactly
  `imaginaryEnergyOfRate ((l+1/2)b)`. Thus the inverted-oscillator decay/tunneling
  width is the Bender entropy-production width, and the Nagao--Nielsen path weight
  decays with that width.

The Dirac/zitterbewegung link is kept explicit: the rest-frame Dirac branch splitting
`omega_Z = 2 omega_C` and the Dirac `alpha`/`beta` anticommutation carrier are bundled
with the Bhaduri entropy-rate projection.


-/

set_option autoImplicit false

open Complex

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.Basic

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
open Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling


/-- **CSW theta/convolution diagonalization package.** The single theta-mode heat equation,
the `S`-matrix theta resummation, the Verlinde convolution theorem, and Wilson-operator
diagonalization are all available simultaneously from the repo's existing CSW carriers. -/
lemma csw_heat_theta_convolution_wilson_diagonalization
    (k : ℕ) (hk : 0 < k) (mode τ z : ℂ) (hτ : 0 < τ.im)
    (a q : Fin k) (f g : Fin k → ℂ) :
    deriv (fun w => thetaMode (k : ℂ) mode w z) τ
        = (1 / (4 * Complex.I * (Real.pi : ℂ) * (k : ℂ)))
          * deriv (fun w => deriv (fun w' => thetaMode (k : ℂ) mode τ w') w) z
      ∧ (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
        = (1 / (Real.sqrt k : ℂ))
          * jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ))
      ∧ (∀ x : Fin k,
        cswDFT (cswConvolution f g) x = (Real.sqrt k : ℂ) * cswDFT f x * cswDFT g x)
      ∧ cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
        = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  exact ⟨thetaMode_heat_equation (k : ℂ) mode τ z hkC,
    cswSMatrix_thetaBasis_resummation k hk a τ z hτ,
    fun x => cswDFT_convolution hk f g x,
    cswWilsonVerlinde_diagonalization k hk a q⟩

/-- The level-2 path-integral diagonalization package is the analytic carrier
used by the half-filled FQHE topological-order bundle: heat/theta evolution,
theta resummation, Verlinde convolution, Wilson diagonalization, and the FQHE
complete-order theorem are available together. -/
lemma halfFilling_pathIntegral_diagonalization_with_topologicalOrder
    (G : CSWGeometricQuantizationPackage 2 (by norm_num))
    (mode τ z : ℂ) (hτ : 0 < τ.im) (a q : Fin 2) (f g : Fin 2 → ℂ) :
    deriv (fun w => thetaMode (2 : ℂ) mode w z) τ
        = (1 / (4 * Complex.I * (Real.pi : ℂ) * (2 : ℂ)))
          * deriv (fun w => deriv (fun w' => thetaMode (2 : ℂ) mode τ w') w) z
      ∧ (∑ b : Fin 2, cswSMatrix 2 a b * cswThetaBasis 2 b τ z)
        = (1 / (Real.sqrt 2 : ℂ))
          * jacobiTheta₂ (z - (a.val : ℂ) / (2 : ℂ)) (τ / (2 : ℂ))
      ∧ (∀ x : Fin 2,
        cswDFT (cswConvolution f g) x = (Real.sqrt 2 : ℂ) * cswDFT f x * cswDFT g x)
      ∧ (cswWilsonVerlindeOperator 2 a (fun b => (starRingEnd ℂ) (cswSMatrix 2 b q))
        = fun c => cswVerlindeEigenvalue 2 (by norm_num) a q * (starRingEnd ℂ) (cswSMatrix 2 c q))
      ∧ HasHalfFillingCompleteTopologicalOrder := by
  rcases csw_heat_theta_convolution_wilson_diagonalization 2 (by norm_num) mode τ z hτ a q f g
    with ⟨hHeat, hTheta, hConv, hWilson⟩
  exact ⟨hHeat, hTheta, hConv, hWilson, halfFilling_completeTopologicalOrder_checked G⟩


/-- Bhaduri's complex resonance energy
`E = (n+1/2)a - i(l+1/2)b`, with `a = hbar omega_1` and
`b = hbar omega_2` in the paper's notation. -/
noncomputable def bhaduriResonanceEnergy (n : ℤ) (l : ℕ) (a b : ℝ) : ℂ :=
  ((n : ℂ) + 1 / 2) * (a : ℂ) - Complex.I * (((l : ℂ) + 1 / 2) * (b : ℂ))

/-- The inverted-oscillator entropy-production rate read from Bhaduri's resonance:
`dot S_I = (l+1/2)b`. -/
noncomputable def bhaduriInvertedEntropyRate (l : ℕ) (b : ℝ) : ℝ :=
  ((l : ℝ) + 1 / 2) * b

@[simp] lemma bhaduriResonanceEnergy_re (n : ℤ) (l : ℕ) (a b : ℝ) :
    (bhaduriResonanceEnergy n l a b).re = ((n : ℝ) + 1 / 2) * a := by
  simp [bhaduriResonanceEnergy]

@[simp] lemma bhaduriResonanceEnergy_im (n : ℤ) (l : ℕ) (a b : ℝ) :
    (bhaduriResonanceEnergy n l a b).im = -bhaduriInvertedEntropyRate l b := by
  simp [bhaduriResonanceEnergy, bhaduriInvertedEntropyRate]

/-- **Bhaduri resonance = Bender complex energy.** The Bhaduri pole is exactly
`complexEnergyOfRate E_R dotS_I` with `dotS_I = (l+1/2)b`. -/
lemma bhaduriResonanceEnergy_eq_complexEnergyOfRate (n : ℤ) (l : ℕ) (a b : ℝ) :
    bhaduriResonanceEnergy n l a b =
      complexEnergyOfRate (((n : ℝ) + 1 / 2) * a) (bhaduriInvertedEntropyRate l b) := by
  apply Complex.ext <;> simp [bhaduriResonanceEnergy, complexEnergyOfRate, bhaduriInvertedEntropyRate]

/-- **Imaginary energy equals the Bender entropy-rate imaginary energy.**
The imaginary part of Bhaduri's contour-rotated/tunneling resonance is exactly
`imaginaryEnergyOfRate ((l+1/2)b)`. -/
lemma bhaduri_imaginaryEnergy_eq_entropyRate (n : ℤ) (l : ℕ) (a b : ℝ) :
    (bhaduriResonanceEnergy n l a b).im =
      imaginaryEnergyOfRate (bhaduriInvertedEntropyRate l b) := by
  simp [imaginaryEnergyOfRate]

/-- The inverted-oscillator width is the Bender width of the same entropy-production
rate: `Gamma = 2(l+1/2)b`. -/
lemma bhaduri_widthFromRate_eq_inverted_width (l : ℕ) (b : ℝ) :
    widthFromRate (bhaduriInvertedEntropyRate l b) = 2 * (((l : ℝ) + 1 / 2) * b) := by
  simp [widthFromRate, bhaduriInvertedEntropyRate]

/-- The Bhaduri resonance energy is exactly a zero of the Selberg-zeta factor already
formalized in `OperatorAlgebra.ZetaInvertedOscillator`. -/
lemma bhaduri_selberg_factor_zero {a b : ℝ} (ha : a ≠ 0) (n : ℤ) (l : ℕ) :
    1 + Complex.exp
      ((2 * (Real.pi : ℂ) * Complex.I / a)
        * (bhaduriResonanceEnergy n l a b + Complex.I * ((l : ℂ) + 1 / 2) * b)) = 0 := by
  exact (selberg_factor_eq_zero_iff (a := a) (b := b) ha l
    (bhaduriResonanceEnergy n l a b)).mpr ⟨n, by
      simp [bhaduriResonanceEnergy]
      ring⟩

/-- The Nagao--Nielsen path-weight modulus decays at half the Bhaduri/Bender width. -/
lemma bhaduri_nnPathWeight_eq_expNegHalfWidth (S_R ℏ t : ℝ) (l : ℕ) (b : ℝ) (hℏ : ℏ ≠ 0) :
    ‖nnPathWeight S_R (bhaduriInvertedEntropyRate l b * t) ℏ‖
      = Real.exp (-(widthFromRate (bhaduriInvertedEntropyRate l b) * t) / (2 * ℏ)) :=
  norm_nnPathWeight_eq_expNegHalfWidth S_R (bhaduriInvertedEntropyRate l b) ℏ t hℏ


/-- **Dirac/zitterbewegung + tunneling entropy bridge.** The Dirac rest-frame branch
splitting, the Dirac `alpha`/`beta` anticommutation carrier, and the Bhaduri tunneling
resonance all agree with the same entropy-rate convention. -/
lemma dirac_zitterbewegung_bhaduri_entropy_link
    (mass lightSpeed hbar : ℝ) (hmass : 0 ≤ mass)
    (s : Matrix (Fin 2) (Fin 2) ℂ) (n : ℤ) (l : ℕ) (a b : ℝ) :
    zitterbewegungFrequency 0 mass lightSpeed hbar = 2 * comptonFrequency mass lightSpeed hbar
      ∧ diracAlpha s * diracBeta + diracBeta * diracAlpha s = 0
      ∧ (bhaduriResonanceEnergy n l a b).im =
        imaginaryEnergyOfRate (bhaduriInvertedEntropyRate l b)
      ∧ bhaduriResonanceEnergy n l a b =
        complexEnergyOfRate (((n : ℝ) + 1 / 2) * a) (bhaduriInvertedEntropyRate l b) :=
  ⟨zitterbewegung_rest_eq_two_compton mass lightSpeed hbar hmass,
    diracAlpha_beta_anticomm s,
    bhaduri_imaginaryEnergy_eq_entropyRate n l a b,
    bhaduriResonanceEnergy_eq_complexEnergyOfRate n l a b⟩

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.Basic

end
