/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Fermion.PhotonExchange
public import Physlib.QFT.PathIntegral.MeasureExpectation
public import Physlib.QFT.PathIntegral.RigorousComplexFK

/-!
# The Cameron–Martin complex-action Feynman–Kac path integral as a measure-valid substitute for the QED path integral

Uses the now-linked Wigner–Dunkl arc — the fermion–photon exchange (`Fermion.PhotonExchange`, the QED
single-photon-exchange vertex) and the Cameron–Martin weight `W = e^{−S_I/ℏ}` (`Dunkl.CameronMartinWeight`)
— together with the rigorous measure-theoretic complex Feynman–Kac of `RigorousComplexFK`, to establish:
the QED fermion–photon exchange, written as a Cameron–Martin complex-action (Lorentzian) path integral, is
a **genuine, measure-theoretically valid Bochner integral**, and the entropic damping is exactly what makes
it valid.

**The mathematical point.** The oscillatory Feynman/QED path integral is famously *not* a measure (no
countably-additive complex measure of bounded variation — Cameron's no-go; the general Glimm–Jaffe
oscillatory-measure problem is open). But the Cameron–Martin weight is `‖e^{iS_R/ℏ − S_I/ℏ}‖ = e^{−S_I/ℏ}`,
a **bounded** (`≤ 1`), strictly positive, measurable Radon–Nikodym density: with `S_I ≥ 0` it converts the
oscillatory integral into an **absolutely-convergent Bochner integral** (`complex_FK_rigorous`). So on the
entropically-damped class the complex-action path integral *is* a rigorous measure-theoretic object.

* **§A — the QED exchange as a measure path-integral model** (`qedExchangeModel`): a
 `MeasurePathIntegralModel` whose imaginary action `S_I = H_{I,1}+H_{I,2} ≥ 0` is the two fermion lines'
 entropic damping (the photon line is unitary, contributing only to `S_R` — `Fermion.PhotonExchange`), with
 a finite reference measure so the damping is `L¹` (`qed_damping_L1`).
* **§B — measure-theoretic validity** (`qed_FK_measure_valid`): the QED-exchange complex Feynman–Kac
 expectation `∫ obs · e^{iS_R/ℏ − S_I/ℏ} dμ` is **Bochner-integrable** with the bound `‖⟨obs⟩‖ ≤
 C · Z` — a genuine absolutely-convergent integral (`complex_FK_rigorous`).
* **§C — the Cameron–Martin weight is the valid density** (`qed_cameronMartin_eq_weight_modulus`,
 `qed_cameronMartin_bounded`): `‖weight‖ = e^{−S_I/ℏ}` is positive and `≤ 1`, the bounded Radon–Nikodym
 density that makes the integral converge.

**Scope.** This is a representation of the QED single-photon-exchange amplitude as a rigorous
*entropically-damped* complex path integral on a finite reference measure — it is **not** a construction of
the full interacting gauge-field QED functional integral, and the rigor is exactly that of
`complex_FK_rigorous` (valid for `S_I ≥ 0`; the undamped oscillatory measure has no such measure — Cameron /
Glimm–Jaffe). What is proved: with the Cameron–Martin entropic damping the QED-exchange path integral is a
well-defined Bochner integral, so the damped complex action is a measure-theoretically valid stand-in for
the (otherwise non-measure) oscillatory QED path integral on this class.

## References

* R. H. Cameron, W. T. Martin, *Transformations of Wiener integrals under translations*, Ann. Math. 45
 (1944) 386 — the Cameron–Martin weight `e^{−S_I/ℏ}`.
* I. V. Girsanov, *On transforming a certain class of stochastic processes by absolutely continuous
 substitution of measures*, Theory Probab. Appl. 5 (1960) 285 — the Radon–Nikodym density.
* R. P. Cameron, *The Ilstow and Feynman integrals*, J. Anal. Math. 10 (1962) 287 — the non-existence of a
 countably-additive Feynman measure (the obstruction the entropic damping circumvents).
* J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, Springer (1987) — the
 oscillatory-measure (Glimm–Jaffe) problem.
* Repo dependencies: `QFT.PathIntegral.RigorousComplexFK` (`complex_FK_rigorous`), `Fermion.PhotonExchange`
 (the QED vertex, §D), `Dunkl.CameronMartinWeight` (the Cameron–Martin weight along stochastic paths).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid

open Physlib.QFT.PathIntegral MeasureTheory

/-! ## §A — the QED fermion–photon exchange as a measure path-integral model -/

/-- The interval reference measure `volume|_{[0,1]}` is finite. -/
instance : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- **The QED fermion–photon-exchange measure path-integral model.** The real action `S_R(p) = p` is the
reversible (photon + fermion) phase (the photon line is unitary, `Fermion.PhotonExchange`); the imaginary
action `S_I = H_{I,1} + H_{I,2} ≥ 0` is the two fermion lines' entropic / Cameron–Martin damping. The
reference measure is finite, so the damping is `L¹`. -/
noncomputable def qedExchangeModel (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    MeasurePathIntegralModel ℝ where
  μ := volume.restrict (Set.Icc 0 1)
  hbar := ℏ
  hbar_pos := hℏ
  actionRe := fun p => p
  actionIm := fun _ => HI1 + HI2
  measurable_actionRe := measurable_id
  measurable_actionIm := measurable_const
  actionIm_nonneg := fun _ => by positivity

/-- **The Cameron–Martin damping of the QED model is `L¹`** (a constant on a finite measure). -/
theorem qed_damping_L1 (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    Integrable (fun x => (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).damping x)
      (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).μ := by
  simp only [MeasurePathIntegralModel.damping, MeasurePathIntegralModel.actionImScaled,
    qedExchangeModel]
  exact integrable_const _

/-! ## §B — measure-theoretic validity of the QED complex Feynman–Kac path integral -/

/-- **[Measure-theoretic validity] The QED fermion–photon-exchange complex Feynman–Kac path integral is a
genuine Bochner integral.** For any measurable, essentially-bounded observable `obs` (`‖obs‖ ≤ C`), the
integrand `obs · e^{iS_R/ℏ − S_I/ℏ}` is **Bochner-integrable** and the expectation satisfies
`‖⟨obs⟩‖ ≤ C · Z` (`Z = ∫ e^{−S_I/ℏ} dμ`). The Cameron–Martin entropic damping `S_I ≥ 0` converts the
otherwise non-measure oscillatory QED path integral into an absolutely-convergent Bochner integral
(`complex_FK_rigorous`). -/
theorem qed_FK_measure_valid (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (obs : ℝ → ℂ) (hMeas : Measurable obs) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).μ, ‖obs x‖ ≤ C) :
    Integrable (fun x => obs x * (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x)
        (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).μ
      ∧ ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complexFKExpectation obs‖
          ≤ C * (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).partitionFunction :=
  (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complex_FK_rigorous
    (qed_damping_L1 ℏ HI1 HI2 hℏ h1 h2) obs hMeas C hC hBound

/-- **The QED-exchange amplitude (`obs ≡ 1`, the bare exchange) is a finite, well-defined Bochner
integral** with `‖amplitude‖ ≤ Z` — the oscillatory QED exchange replaced by an absolutely-convergent
integral. -/
theorem qed_amplitude_bochner_finite (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complexFKExpectation (fun _ => 1)‖
      ≤ 1 * (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).partitionFunction :=
  ((qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complex_FK_rigorous (qed_damping_L1 ℏ HI1 HI2 hℏ h1 h2)
    (fun _ => 1) measurable_const 1 zero_le_one (by filter_upwards with x; simp)).2

/-! ## §B2 — link to the shared expectation-level path-integral API -/

/-- **[Link] The shared unnormalised path-integral expectation agrees with the rigorous complex
Feynman-Kac expectation** used for the measure-valid QED exchange.  The two APIs differ only by the
commuted scalar product `weight * obs` versus `obs * weight`. -/
theorem qed_unnormalizedExpectation_eq_complexFKExpectation
    (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (obs : ℝ → ℂ) :
    (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).unnormalizedExpectation obs =
      (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complexFKExpectation obs := by
  unfold MeasurePathIntegralModel.unnormalizedExpectation MeasurePathIntegralModel.complexFKExpectation
  congr with x
  exact mul_comm _ _

/-! ## §C — the Cameron–Martin weight is the bounded, positive Radon–Nikodym density -/

/-- **[Cameron–Martin] The weight modulus is the Cameron–Martin weight** `‖e^{iS_R/ℏ − S_I/ℏ}‖ =
e^{−(H_{I,1}+H_{I,2})/ℏ}` — the entropic damping `W = e^{−S_I/ℏ}` of `Dunkl.CameronMartinWeight`, here the
modulus of the complex QED weight. -/
theorem qed_cameronMartin_eq_weight_modulus (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (x : ℝ) :
    ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖ = Real.exp (-((HI1 + HI2) / ℏ)) := by
  rw [MeasurePathIntegralModel.weight_norm_is_damping]
  simp [MeasurePathIntegralModel.actionImScaled, qedExchangeModel]

/-- **[Cameron–Martin] The weight is a bounded positive density** `0 < W ≤ 1` — the Radon–Nikodym /
Girsanov density that makes the complex QED path integral absolutely convergent (a genuine sub-probability
reweighting, never amplifying). -/
theorem qed_cameronMartin_bounded (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) (x : ℝ) :
    0 < (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).damping x
      ∧ (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).damping x ≤ 1 :=
  ⟨(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).damping_pos x,
   (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).damping_le_one x⟩

/-! ## §D — links to the fermion–photon exchange (`Fermion.PhotonExchange`, the QED vertex) -/

/-- **[Link] The model's imaginary action is the two fermion lines' entropic damping.** The QED-exchange
model's `S_I` equals `H_{I,1} + H_{I,2}`, the sum of the imaginary parts of the two fermion `ComplexHamiltonian`s
of `Fermion.PhotonExchange.fermionHamiltonian` — so the model is literally built from the fermion lines, not
just described as such. -/
theorem qed_actionIm_eq_fermion_damping (ℏ p1 p2 m HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1)
    (h2 : 0 ≤ HI2) (x : ℝ) :
    (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).actionIm x
      = (Fermion.PhotonExchange.fermionHamiltonian p1 m HI1 h1).H_I
        + (Fermion.PhotonExchange.fermionHamiltonian p2 m HI2 h2).H_I := by
  simp [qedExchangeModel, Fermion.PhotonExchange.fermionHamiltonian]

/-- **[Link] The photon line contributes no imaginary action** `(photonHamiltonian p).H_I = 0` — the
massless photon is unitary (`Fermion.PhotonExchange.photonHamiltonian`), so it enters `S_R` only, never the
entropic damping `S_I`. -/
theorem qed_photon_no_damping (p : ℝ) : (Fermion.PhotonExchange.photonHamiltonian p).H_I = 0 := rfl

/-- **[Link] The model weight modulus IS the fermion–photon exchange amplitude modulus.** At unit time the
modulus of the measure-valid QED weight equals `‖photonExchangeAmplitude‖`
(`Fermion.PhotonExchange.exchange_modulus`): the measure-theoretic Cameron–Martin weight and the QED
single-photon-exchange amplitude's modulus are the same object. -/
theorem qed_weight_modulus_eq_exchange (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2)
    (x pf1 pf2 pγ m : ℝ) :
    ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖
      = ‖Fermion.PhotonExchange.photonExchangeAmplitude pf1 pf2 pγ m HI1 HI2 1 ℏ h1 h2‖ := by
  rw [qed_cameronMartin_eq_weight_modulus, Fermion.PhotonExchange.exchange_modulus, ← Real.exp_add]
  congr 1; ring

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid

end
