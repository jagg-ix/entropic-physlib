/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality

/-!
# Calibrated distances: the standard-distance interface for the entropic arc

Implements the standard-distances refactor: the operational identification
`r = ℓ·log K` becomes a *hypothesis* (`IsEntanglementCalibrated`), every
ratio-only theorem of the entropic arc lifts to it verbatim, and each standard
theory plugs in its own distance:

* **the interface** — `IsEntanglementCalibrated r ℓ K` (`r = ℓ·log K`), with the decay
  and growth faces `calibrated_decay` (`e^{−r/ℓ} = 1/K`) and `calibrated_exp`
  (`e^{r/ℓ} = K`);
* **generic lifts** — `calibrated_vacuumBell` (`e^{−r/ℓ} = tanh η`, the Reeh–Schlieder
  face), `calibrated_boost_sq` (`cosh²η·(e^{2r/ℓ}−1) = e^{2r/ℓ}`),
  `calibrated_bornWeight` (`|w(r/ℓ)|² = tanh η`), `calibrated_boost_frame`
  (the Ghosal frame at velocity `e^{−r/ℓ}` is `thermoBogoliubov (−η)`) — the proofs
  are one-line lifts of the entropic theorems, since those never used more than the
  calibration;
* **the instances** — `IsEntanglementCalibrated.of_sq` (squared form, serving the
  special-relativistic `empiricalDistanceVector` interval and Szabados's
  normal-coordinate radial distance, which state `r²`-identities);
  `entropicProperDistance_isCalibrated` (the CAT/EPT instance, definitional);
  `dist_log_isCalibrated` (the Mathlib metric-space instance on the log axis,
  `dist (log a) (log b) = log(a/b)` — the `ScaleLine` face); the quantum-information
  instance is the statement itself (`K` is a Schmidt datum);
* **the Feynman–Stückelberg link** (§D) — Thomson's lecture identity
  `e^{−i(−E)(−t)} = e^{−iEt}` (`feynman_stueckelberg_phase`): flipping energy sign and
  time direction together is invisible in the phase — the `U(1)` face of the CPT gauge
  (`TimeSymmetricMarkovArrows.PT_conjugation_fixes`,
  `chargeConj_flips_chirality`); and `wick_rotation_gives_calibration`
  — the same phase at the Compton energy `E = mc²/ℏ`, Wick-rotated to imaginary time
  `t = −i·r/c`, **is** the calibration decay `e^{−r/λ_C}`: the backward-in-time
  (positronic) branch and the spacelike Compton/Yukawa decay that grounds the QFT
  calibration instance are two faces of one exponential.

**Honest layering.**  The interface contains only the calibration algebra; which
physical distance satisfies it is each instance's own claim (definitional for the
entropic arc, hypothesis-form for SR/GR, a lecture-level standard fact for the QFT
Yukawa face — the propagator analysis behind it is not formalized).

## References

* M. A. Thomson, *Particle Physics*, Cambridge Michaelmas 2011, handout slide 67
  (the Feynman–Stückelberg interpretation); E. C. G. Stückelberg, Helv. Phys. Acta
  **14** (1941) 588; R. P. Feynman, Phys. Rev. **76** (1949) 749.
* Carrier reuse: `ComptonClock.EntropicProperDistance`, `FrequencyTrinity`
  (`comptonWavelength`), `MuonAnomaly.SchmidtRapidityHyperbolicUnification`
  (`schmidtNumber`), `Foundations.RelativeStateConventionality`
  (`bornWeight_eq_boost_velocity`), `Relativity.Special.SimultaneityConventionShear`
  (`lorentzFrame_eq_thermoBogoliubov`), `ThermoFieldDynamics.TFDImaginaryPart`
  (`thermoBogoliubov`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.Relativity.Special.SimultaneityConventionShear
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.CalibratedDistance

/-! ## §A — the interface -/

/-- **The entanglement calibration**: a distance `r`, a length standard `ℓ`, and a
Schmidt datum `K` are calibrated when `r = ℓ·log K` — the operational identification
of the entropic arc, as a hypothesis any theory's distance can satisfy. -/
def IsEntanglementCalibrated (r ℓ K : ℝ) : Prop := r = ℓ * Real.log K

/-- Constructor from a squared identity (the form the SR interval and the Szabados
radial distance forms provide): `r² = (ℓ log K)²` with both sides nonnegative. -/
theorem IsEntanglementCalibrated.of_sq {r ℓ K : ℝ} (hr : 0 ≤ r)
    (hpos : 0 ≤ ℓ * Real.log K) (h : r ^ 2 = (ℓ * Real.log K) ^ 2) :
    IsEntanglementCalibrated r ℓ K := by
  unfold IsEntanglementCalibrated
  nlinarith [h, hr, hpos]

/-- **The decay face**: at a calibrated distance the exponential suppression is `1/K`. -/
theorem calibrated_decay {r ℓ K : ℝ} (h : IsEntanglementCalibrated r ℓ K)
    (hℓ : ℓ ≠ 0) (hK : 0 < K) : Real.exp (-(r / ℓ)) = K⁻¹ := by
  rw [h, mul_div_cancel_left₀ _ hℓ, Real.exp_neg, Real.exp_log hK]

/-- **The growth face**: `e^{r/ℓ} = K`. -/
theorem calibrated_exp {r ℓ K : ℝ} (h : IsEntanglementCalibrated r ℓ K)
    (hℓ : ℓ ≠ 0) (hK : 0 < K) : Real.exp (r / ℓ) = K := by
  rw [h, mul_div_cancel_left₀ _ hℓ, Real.exp_log hK]

/-! ## §B — the generic lifts: the entropic theorems at any calibrated distance -/

/-- **The vacuum Bell decay at a calibrated distance** — the Reeh–Schlieder face,
now available to any theory whose distance is calibrated to the Schmidt number. -/
theorem calibrated_vacuumBell {r ℓ η : ℝ} (hη : 0 < η)
    (h : IsEntanglementCalibrated r ℓ (schmidtNumber η)) (hℓ : ℓ ≠ 0) :
    Real.exp (-(r / ℓ)) = Real.tanh η := by
  rw [calibrated_decay h hℓ (div_pos (Real.cosh_pos η) (Real.sinh_pos_iff.mpr hη)),
    schmidtNumber, Real.tanh_eq_sinh_div_cosh, inv_div]

/-- **The boost square at a calibrated distance**: `cosh²η·(e^{2r/ℓ} − 1) = e^{2r/ℓ}` —
the frequency boost is a definite function of the calibrated separation alone. -/
theorem calibrated_boost_sq {r ℓ η : ℝ} (hη : 0 < η)
    (h : IsEntanglementCalibrated r ℓ (schmidtNumber η)) (hℓ : ℓ ≠ 0) :
    Real.cosh η ^ 2 * (Real.exp (2 * (r / ℓ)) - 1) = Real.exp (2 * (r / ℓ)) := by
  have hK : 0 < schmidtNumber η := div_pos (Real.cosh_pos η) (Real.sinh_pos_iff.mpr hη)
  have hsq : Real.exp (2 * (r / ℓ)) = schmidtNumber η ^ 2 := by
    rw [two_mul, Real.exp_add, calibrated_exp h hℓ hK, sq]
  rw [hsq]
  exact boost_sq_schmidt_relation η hη

/-- **The Born weight at a calibrated distance**: the entropic history weight at the
action `r/ℓ` is `tanh η` — the branch weight in any calibrated theory. -/
theorem calibrated_bornWeight {r ℓ η : ℝ} (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) (hη : 0 < η)
    (h : IsEntanglementCalibrated r ℓ (schmidtNumber η)) (hℓ : ℓ ≠ 0) :
    Complex.normSq (historyWeight S_R (r / ℓ) ℏ) = Real.tanh η := by
  rw [show r / ℓ = Real.log (schmidtNumber η) from by
    rw [h, mul_div_cancel_left₀ _ hℓ]]
  exact bornWeight_eq_boost_velocity S_R ℏ η hℏ hη

/-- **The boost frame at a calibrated distance**: the rocket whose velocity is the
calibrated decay implements the Bogoliubov boost — the Ghosal weld for any calibrated
theory. -/
theorem calibrated_boost_frame {r ℓ η : ℝ} (hη : 0 < η)
    (h : IsEntanglementCalibrated r ℓ (schmidtNumber η)) (hℓ : ℓ ≠ 0) :
    lorentzFrame (Real.exp (-(r / ℓ))) 1 (Real.cosh η) = thermoBogoliubov (-η) := by
  rw [calibrated_vacuumBell hη h hℓ]
  exact lorentzFrame_eq_thermoBogoliubov η

/-! ## §C — the standard instances -/

/-- **The CAT/EPT instance is definitional**: the entropic proper distance satisfies
its own calibration. -/
theorem entropicProperDistance_isCalibrated (m c ħ η : ℝ) :
    IsEntanglementCalibrated (entropicProperDistance m c ħ η)
      (comptonWavelength m c ħ) (schmidtNumber η) := rfl

/-- **The Mathlib metric-space instance**: on the log axis the standard distance is
calibrated with unit standard and scale-ratio Schmidt datum,
`dist (log a) (log b) = log(a/b)` — the `ScaleLine` face of the arc. -/
theorem dist_log_isCalibrated (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) :
    IsEntanglementCalibrated (dist (Real.log a) (Real.log b)) 1 (a / b) := by
  unfold IsEntanglementCalibrated
  rw [Real.dist_eq, one_mul,
    abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hab)),
    Real.log_div (lt_of_lt_of_le hb hab).ne' hb.ne']

/-! ## §D — the Feynman–Stückelberg link -/

/-- **The Feynman–Stückelberg phase identity** (Thomson, slide 67):
`e^{−i(−E)(−t)} = e^{−iEt}` — a negative-energy solution running backward in time has
exactly the phase of a positive-energy antiparticle running forward.  The double flip
is invisible: the `U(1)` face of the CPT gauge
(`TimeSymmetricMarkovArrows.PT_conjugation_fixes` on kinematics,
`chargeConj_flips_chirality` on the Weyl algebra, the two-sided semigroup's two
branches on the arrows). -/
theorem feynman_stueckelberg_phase (E t : ℝ) :
    Complex.exp (-Complex.I * (-E : ℝ) * (-t : ℝ)) =
      Complex.exp (-Complex.I * E * t) := by
  congr 1
  push_cast
  ring

/-- **Wick rotation turns the Feynman–Stückelberg phase into the calibration decay**:
at the Compton energy `E = mc²/ℏ` and imaginary time `t = −i·r/c`, the phase becomes
`e^{−r/λ_C}` — the spacelike Compton/Yukawa suppression that grounds the QFT instance
of `IsEntanglementCalibrated`.  The positronic backward branch and the calibrated
spacelike decay are two faces of one exponential. -/
theorem wick_rotation_gives_calibration (m c ħ r : ℝ) :
    Complex.exp (-Complex.I * ((m * c ^ 2 / ħ : ℝ) : ℂ) * (-Complex.I * ((r / c : ℝ) : ℂ)))
      = ((Real.exp (-(r / comptonWavelength m c ħ)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  rw [comptonWavelength]
  push_cast
  field_simp
  linear_combination (↑m * ↑c * ↑r * (↑ħ)⁻¹ : ℂ) * Complex.I_sq

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.CalibratedDistance

end
