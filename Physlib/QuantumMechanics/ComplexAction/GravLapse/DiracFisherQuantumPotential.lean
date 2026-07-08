/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential

/-!
# The complex Dirac proper-time imaginary action and its Fisher / NN-contour quantum potential

Ports the **complex-Dirac** theorems of the `reference tree` bridges (`ProperTimeFeynCalcBridge`,
`SpinorPathIntegralBridge`) into physlib and links them to the Nagao–Nielsen contour quantum potential
and its Fisher-information reading (`GravLapse.FisherQuantumPotential.nnContour_quantumPotential_is_fisher`).
`physlib` cannot import `reference tree` (the dependency runs the other way), so the Dirac structures are
re-proved here and tied to the existing lapse/contour/Fisher objects.

The Euclidean Dirac propagator has the Schwinger proper-time representation
`1/(p²+m²) = ∫₀^∞ e^{−(p²+m²)t} dt` (`feyncalcEuclideanProperTimeKernel`), so the **Dirac proper-time
imaginary action** is `S_I = (p²+m²)·t = E_D²·t` (the Euclidean denominator times proper time), where
`E_D = √(p²+m²)` is the Dirac dispersion. The merged spinor path integral is
`R·e^{(i/ℏ)S_R − (1/ℏ)S_I}` with entropic proper time `τ_ent = S_I/ℏ` (`SpinorPathIntegralBridge`).

* **§A — the Dirac proper-time imaginary action** (`diracProperTimeImaginaryAction`,
  `diracGap_eq_bogoliubovEnergy_sq`). `S_I = (p²+m²)·t`, with gap `E_I = p²+m²` **equal to the
  Bogoliubov/Dirac dispersion squared** `E_D² = bogoliubovEnergy(p,m)²` — anchoring the Dirac proper time to
  the existing `Bogoliubov.Transformation` energy.
* **§B — link to the NN contour and the Born weight** (`diracProperTime_eq_nnImaginaryAction`,
  `diracProperTimeKernel_eq_bornWeight`). `S_I = (p²+m²)t` **is** an `nnImaginaryAction` (gap `p²+m²`,
  coordinate proper time `t`), and the proper-time kernel `e^{−(p²+m²)t/ℏ}` is the Born weight / entropic
  damping `bornWeight S_I ℏ`.
* **§C — the Dirac quantum potential is the Fisher quantum potential**
  (`dirac_quantumPotential_is_fisher`, `dirac_quantumPotential_nonneg`). When the Dirac proper-time
  imaginary action equals the Fisher information `I(p)`, the Dirac quantum potential **is** the Fisher
  quantum potential (via `nnContour_quantumPotential_is_fisher`); it is non-negative because the gap
  `p²+m² ≥ 0` (no pilot wave).
* **§D — the merged spinor kernel and entropic proper time** (`diracSpinorKernel`, `diracSpinorKernel_norm`,
  `diracEntropicProperTime_eq_nn`, `diracSpinorKernel_reversible`). The spinor path-integral kernel
  `R·e^{(i/ℏ)S_R − (1/ℏ)S_I}` has modulus `‖R‖·e^{−S_I/ℏ}` (the entropic suppression of off-diagonal
  coherence), its entropic proper time `τ_ent = S_I/ℏ` is the contour `nnEntropicTime`, and the reversible
  Dirac limit `S_I = 0` (`H_I → 0`) gives the unitary spinor kernel `‖R‖`.
* **§E — agreement with the QED Complex Feynman–Kac path integral** (`dirac_properTime_modulus_eq_qed_FK`,
  `diracQEDModel`, `diracQEDModel_FK_measure_valid`). The Dirac proper-time kernel `e^{−(p²+m²)t/ℏ}` equals
  the modulus of the measure-valid QED weight when `(p²+m²)t = H_{I,1}+H_{I,2}`; and the Dirac proper time
  **is** a `qedExchangeModel` (fermion line `H_{I,1} = (p²+m²)t`, `H_{I,2} = 0`), so it inherits the QED
  Complex FK measure-validity (`qed_FK_measure_valid` via `complex_FK_rigorous`): the otherwise oscillatory
  Dirac path integral is the *same* rigorous entropically-damped Bochner integral as the QED exchange.

## References

* reference tree `reference tree/Integration/ProperTimeFeynCalcBridge.lean`
  (`feyncalcEuclideanProperTimeKernel`, `feyncalcDiracProperTimeKernel`) and
  `reference tree/complex-action/entropic-time/complex-action/entropic-time/SpinorPathIntegralBridge.lean` (`mergedSpinorKernel`, `entropicProperTime`,
  `dirac_limit_hermitian`) — the ported theorems.
* J. Schwinger, *On gauge invariance and vacuum polarization*, Phys. Rev. 82 (1951) 664 — proper-time
  representation of the propagator.
* Repo dependencies: `GravLapse.FisherQuantumPotential` (`nnContour_quantumPotential_is_fisher`,
  `fisherQuantumPotential`), `GravLapse.BohmQuantumPotential` (`nnImaginaryAction`, `nnEntropicTime`,
  `bohmQuantumPotential`, `bornWeight`), `Bogoliubov.Transformation` (`bogoliubovEnergy`),
  `PathIntegral.ComplexActionPathIntegralWeight` (`complexActionPathIntegralWeight`, `kuikenWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.DiracFisherQuantumPotential

open Physlib.QuantumMechanics.ComplexAction.GravLapse.FisherQuantumPotential
open Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.StatisticalMechanics
open MeasureTheory

variable {Φ : Type}

/-! ## §A — the Dirac proper-time imaginary action `S_I = (p²+m²)·t = E_D²·t` -/

/-- **[Port — reference tree `ProperTimeFeynCalcBridge`] The Euclidean Dirac proper-time (Schwinger) imaginary
action** `S_I = (p²+m²)·t`. From `1/(p²+m²) = ∫₀^∞ e^{−(p²+m²)t} dt`, the imaginary action accumulated over
Schwinger proper time `t` is the Euclidean denominator `p²+m² = E_D²` times `t`. -/
noncomputable def diracProperTimeImaginaryAction (p m t : ℝ) : ℝ := (p ^ 2 + m ^ 2) * t

/-- **[Link — Dirac dispersion] The Dirac proper-time gap is the Bogoliubov/Dirac dispersion squared.**
`p² + m² = bogoliubovEnergy(p, m)² = E_D²` (`Bogoliubov.Transformation.bogoliubovEnergy = √(p²+m²)`): the gap
of the Dirac proper time is the squared relativistic energy. -/
theorem diracGap_eq_bogoliubovEnergy_sq (p m : ℝ) : bogoliubovEnergy p m ^ 2 = p ^ 2 + m ^ 2 := by
  unfold bogoliubovEnergy; exact Real.sq_sqrt (by positivity)

/-! ## §B — link to the Nagao–Nielsen contour and the Born weight -/

/-- **[Link] The Dirac proper-time imaginary action IS a Nagao–Nielsen contour imaginary action.**
`diracProperTimeImaginaryAction p m t = nnImaginaryAction (p²+m²) t`: the Dirac case is the §F contour
imaginary action with gap `E_I = p²+m²` and coordinate proper time `t`. -/
theorem diracProperTime_eq_nnImaginaryAction (p m t : ℝ) :
    diracProperTimeImaginaryAction p m t = nnImaginaryAction (p ^ 2 + m ^ 2) t := rfl

/-- **[Link] The Dirac proper-time kernel is the Born weight / entropic damping.**
`e^{−(p²+m²)t/ℏ} = bornWeight ((p²+m²)t) ℏ`: the Schwinger proper-time damping is the contour Born weight at
the Dirac imaginary action. -/
theorem diracProperTimeKernel_eq_bornWeight (p m t ℏ : ℝ) :
    Real.exp (-((p ^ 2 + m ^ 2) * t) / ℏ) = bornWeight (diracProperTimeImaginaryAction p m t) ℏ := rfl

/-! ## §C — the Dirac quantum potential is the Fisher quantum potential -/

/-- **[Link — the headline] The Dirac proper-time quantum potential is the Fisher quantum potential.** When
the Dirac proper-time imaginary action `(p²+m²)·t` equals the Fisher information `I(p)`, the Dirac contour
quantum potential is the Fisher quantum potential (via `nnContour_quantumPotential_is_fisher`): the complex
Dirac field's de Broglie–Bohm quantum potential is the Fisher information of its Euclidean density. -/
theorem dirac_quantumPotential_is_fisher (data : FisherInformationData Φ) (φ : Φ) (p m t ℏ M : ℝ)
    (h : diracProperTimeImaginaryAction p m t = data.fisherInfo φ) :
    bohmQuantumPotential (diracProperTimeImaginaryAction p m t) ℏ M = fisherQuantumPotential data φ ℏ M :=
  nnContour_quantumPotential_is_fisher data φ (p ^ 2 + m ^ 2) t ℏ M h

/-- **[No pilot wave] The Dirac proper-time quantum potential is non-negative.** Because the gap
`p² + m² ≥ 0` and the proper time `t ≥ 0`, the Dirac quantum potential `Q = (p²+m²)t·ℏ/(2M) ≥ 0` — a
property of the Euclidean dispersion, no wavefunction required. -/
theorem dirac_quantumPotential_nonneg (p m t ℏ M : ℝ) (ht : 0 ≤ t) (hℏ : 0 ≤ ℏ) (hM : 0 < M) :
    0 ≤ bohmQuantumPotential (diracProperTimeImaginaryAction p m t) ℏ M := by
  rw [diracProperTime_eq_nnImaginaryAction]
  exact nnContour_quantumPotential_nonneg _ _ _ _ (by positivity) ht hℏ hM

/-! ## §D — the merged spinor kernel and entropic proper time -/

/-- **[Port — `SpinorPathIntegralBridge.mergedSpinorKernel`] The merged Dirac spinor path-integral kernel**
`R·e^{(i/ℏ)S_R − (1/ℏ)S_I}` — the spinor transport amplitude `R` times the complex-action/entropic-time master weight. -/
noncomputable def diracSpinorKernel (R : ℂ) (S_R S_I ℏ : ℝ) : ℂ := R * complexActionPathIntegralWeight S_R S_I ℏ

/-- **[Port] The spinor kernel modulus is the entropic suppression** `‖R‖·e^{−S_I/ℏ}` — off-diagonal
coherence is damped by the imaginary action (`kuikenWeight ℏ S_I = e^{−S_I/ℏ}`). -/
theorem diracSpinorKernel_norm (R : ℂ) (S_R S_I ℏ : ℝ) :
    ‖diracSpinorKernel R S_R S_I ℏ‖ = ‖R‖ * kuikenWeight ℏ S_I := by
  rw [diracSpinorKernel, norm_mul, master_modulus_is_kuiken]

/-- **[Port + link — `entropicProperTime`] The Dirac entropic proper time is the contour entropic time.**
`τ_ent = S_I/ℏ = (p²+m²)t/ℏ = nnEntropicTime (p²+m²) t ℏ`: the spinor entropic proper time is the §H contour
entropic time, *not* the Schwinger coordinate proper time `t`. -/
theorem diracEntropicProperTime_eq_nn (p m t ℏ : ℝ) :
    diracProperTimeImaginaryAction p m t / ℏ = nnEntropicTime (p ^ 2 + m ^ 2) t ℏ := rfl

/-- **[Port — `dirac_limit_hermitian`] The reversible Dirac limit gives a unitary spinor kernel.** At
`S_I = 0` (the anti-Hermitian `H_I → 0` / reversible limit), the spinor kernel modulus is `‖R‖`: no entropic
suppression, the standard unitary Dirac transport. -/
theorem diracSpinorKernel_reversible (R : ℂ) (S_R ℏ : ℝ) :
    ‖diracSpinorKernel R S_R 0 ℏ‖ = ‖R‖ := by
  rw [diracSpinorKernel_norm, kuikenWeight]; norm_num

/-! ## §E — the Dirac proper-time agrees with the QED Complex Feynman–Kac path integral -/

/-- **[Agreement] The Dirac proper-time kernel equals the QED Complex FK weight modulus.** When the Dirac
proper-time imaginary action `(p²+m²)t` equals the QED-exchange imaginary action `H_{I,1}+H_{I,2}`, the
Schwinger proper-time damping `e^{−(p²+m²)t/ℏ}` is exactly the modulus of the measure-valid QED weight
(`PathIntegral.QEDPathIntegralMeasureValid.qed_cameronMartin_eq_weight_modulus`): the two path integrals agree on the
Cameron–Martin / entropic-damping factor. -/
theorem dirac_properTime_modulus_eq_qed_FK (ℏ p m t HI1 HI2 x : ℝ)
    (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) (h : (p ^ 2 + m ^ 2) * t = HI1 + HI2) :
    bornWeight (diracProperTimeImaginaryAction p m t) ℏ
      = ‖(PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖ := by
  rw [PathIntegral.QEDPathIntegralMeasureValid.qed_cameronMartin_eq_weight_modulus, bornWeight,
    diracProperTimeImaginaryAction, h]
  congr 1; ring

/-- **[Agreement — the model] The Dirac proper-time path integral IS a QED-exchange Complex FK model.** The
Dirac proper time is the `qedExchangeModel` with the fermion line with `H_{I,1} = (p²+m²)t` (the Dirac
dispersion squared × proper time) and `H_{I,2} = 0`: a single measure-valid model. -/
noncomputable def diracQEDModel (ℏ p m t : ℝ) (hℏ : 0 < ℏ) (ht : 0 ≤ t) :
    Physlib.QFT.PathIntegral.MeasurePathIntegralModel ℝ :=
  PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ ((p ^ 2 + m ^ 2) * t) 0 hℏ
    (mul_nonneg (by positivity) ht) le_rfl

/-- The Dirac-QED model's weight modulus is the Dirac proper-time kernel `e^{−(p²+m²)t/ℏ}`. -/
theorem diracQEDModel_modulus (ℏ p m t : ℝ) (hℏ : 0 < ℏ) (ht : 0 ≤ t) (x : ℝ) :
    ‖(diracQEDModel ℏ p m t hℏ ht).weight x‖ = bornWeight (diracProperTimeImaginaryAction p m t) ℏ := by
  rw [diracQEDModel, PathIntegral.QEDPathIntegralMeasureValid.qed_cameronMartin_eq_weight_modulus, bornWeight,
    diracProperTimeImaginaryAction]
  congr 1; ring

/-- **[Agreement — measure-validity] The Dirac proper-time path integral is an absolutely-convergent
Bochner integral.** Like the QED Complex FK (`qed_FK_measure_valid`, via `complex_FK_rigorous`), the Dirac
proper-time model's observable integral is Bochner-integrable with `‖⟨obs⟩‖ ≤ C·Z`: the otherwise
non-measure oscillatory Dirac path integral is the rigorous entropically-damped complex Feynman–Kac
integral. The Dirac proper-time and the QED Complex FK are the *same* measure-valid construction. -/
theorem diracQEDModel_FK_measure_valid (ℏ p m t : ℝ) (hℏ : 0 < ℏ) (ht : 0 ≤ t)
    (obs : ℝ → ℂ) (hMeas : Measurable obs) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂(diracQEDModel ℏ p m t hℏ ht).μ, ‖obs x‖ ≤ C) :
    MeasureTheory.Integrable (fun x => obs x * (diracQEDModel ℏ p m t hℏ ht).weight x)
        (diracQEDModel ℏ p m t hℏ ht).μ
      ∧ ‖(diracQEDModel ℏ p m t hℏ ht).complexFKExpectation obs‖
          ≤ C * (diracQEDModel ℏ p m t hℏ ht).partitionFunction :=
  PathIntegral.QEDPathIntegralMeasureValid.qed_FK_measure_valid ℏ ((p ^ 2 + m ^ 2) * t) 0 hℏ
    (mul_nonneg (by positivity) ht) le_rfl obs hMeas C hC hBound

end Physlib.QuantumMechanics.ComplexAction.GravLapse.DiracFisherQuantumPotential

end
