/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
meta import Zil

/-!
# The muon `g − 2` as a rapidity defect — the operating-point momentum relation via the Hyperbolic Unification

A better approach to the muon `g − 2` than the fitted "entropic loop" / "gravitational back-reaction"
postdictions: instead of tuning a coupling to the *number* `251×10⁻¹¹`, frame what the experiment **measures**
— the anomalous spin precession `ω_a = a·(eB/mc)` — through the relativistic spin kinematics (Thomas–BMT),
which is intrinsically a **rapidity** effect, and hence is exactly the repo's **Hyperbolic Unification**
(`MuonAnomaly.SchmidtRapidityHyperbolicUnification`: `E = cosh η`, momentum `ξ = sinh η`, `β = tanh η`,
Schmidt number `K = coth η`).

The storage ring runs at the **operating-point momentum**, where the electric-field contribution to the spin
precession vanishes — the condition `a = 1/(γ² − 1)`. With `γ = cosh η` (the Lorentz factor is the
Bogoliubov energy) and `ξ = sinh η` (the momentum), this is

  `a = 1/(γ² − 1) = 1/sinh²η = csch²η`   (`anomaly`),

and — the unification — exactly the Schmidt number squared minus one:

  `a = K² − 1 = coth²η − 1`   (`anomaly_eq_schmidt_sq_sub_one`).

So the anomalous moment **is** the entanglement (Schmidt) measure of the Hyperbolic Unification at the operating-point
rapidity. Unlike the fits, this yields a genuine **cross-check** (a prediction of a *relation*, not a number):
`γ = √(1 + 1/a) = cosh η` (`gamma_anomaly`); for the measured `a ≈ 1.166×10⁻³` this gives
`γ ≈ 29.3` — the actual operating point of the BNL/Fermilab rings (`p ≈ 3.094 GeV/c`).

* **§A — the operating-point momentum anomaly relation (Thomas–BMT, exact).** `anomaly η = 1/sinh²η`;
  `anomaly_eq_cosh` (`= 1/(γ²−1)`), `anomaly_pos`, `gFactor_anomaly` (`g = 2(1 + csch²η)`).
* **§B — the Hyperbolic Unification.** `anomaly_eq_schmidt_sq_sub_one`: `a = K² − 1` with the Schmidt
  number `K = coth η` — g-2 is the entanglement-as-rapidity measure at the operating-point rapidity.
* **§C — the operating-point Lorentz factor (the cross-check).** `gamma a = √(1 + 1/a)`;
  `gamma_anomaly`: `γ = cosh η` — `a` *determines* the operating-point momentum (a relation, not a fit).

**Honest layering.** Exact and operational: the operating-point momentum relation
`a = 1/(γ²−1) = 1/sinh²η = K²−1` is exact relativistic spin kinematics — no dropped factors and no units
error. It supplies a physical *operational reconstruction* of the Schmidt coordinate from storage-ring
kinematics: `K(γ) = γ/√(γ²−1)`. The paper-reported `γ ≈ 29.3` gives `K ∈ (1.0005, 1.0006)` without using
`α` in the Lean definition (`fermilabMagicGamma_determines_schmidtNumber`). It is not, however, an
independent prediction of `a_μ`: the magic operating point is itself selected through the Thomas–BMT anomaly
relation. This is a calibration/kinematic consistency channel, not direct Schmidt tomography of a QFT
bipartition. The 2025 Theory Initiative update finds no current statistically
significant Standard-Model/experiment discrepancy; the formalized result concerns the measured magnetic anomaly
and its operational hyperbolic carrier, not a claim of unresolved new physics.

## References

* Thomas–BMT spin precession; Muon `g − 2` operating point `a = 1/(γ²−1)`, with the Fermilab ring using
  `γ ≈ 29.3` and momentum near `3.094 GeV/c`: Muon `g − 2` Collaboration, final 2025 measurement to
  127 ppb; M. Sorbara for the collaboration, RICAP-24 (2025). R. Aliberti et al., Muon `g − 2` Theory
  Initiative update (2025). `Physlib` (`MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber`,
  `FirstQuantizedQED.AnomalousMagneticMoment.gFactor`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity


/-- **The operating-point momentum anomalous moment** `a = 1/sinh²η = csch²η` — at the operating-point momentum (where the
electric-field spin precession vanishes), the anomaly is the inverse-square of the rapidity sinh (the
momentum `ξ = sinh η`). -/
noncomputable def anomaly (η : ℝ) : ℝ := 1 / (Real.sinh η) ^ 2

/-- **[`a = 1/(γ² − 1)`]** the standard operating-point momentum condition, with `γ = cosh η`: `a = 1/(cosh²η − 1)`
(and `cosh²η − 1 = sinh²η`). -/
lemma anomaly_eq_cosh (η : ℝ) :
    anomaly η = 1 / ((Real.cosh η) ^ 2 - 1) := by
  unfold anomaly
  rw [show (Real.cosh η) ^ 2 - 1 = (Real.sinh η) ^ 2 from by
    nlinarith [Real.cosh_sq_sub_sinh_sq η]]

/-- **[`a > 0`]** the operating-point momentum anomaly is positive (for `η > 0`). -/
lemma anomaly_pos (η : ℝ) (hη : 0 < η) : 0 < anomaly η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold anomaly; positivity

/-- **[The g-factor at the operating-point rapidity]** `g = 2(1 + a) = 2(1 + csch²η)`. -/
lemma gFactor_anomaly (η : ℝ) :
    gFactor (anomaly η) = 2 * (1 + 1 / (Real.sinh η) ^ 2) := by
  rw [gFactor, anomaly]


/-- **[g-2 is the Schmidt number squared minus one]** `a = K² − 1 = coth²η − 1` with the Schmidt number
`K = coth η = cosh η/sinh η` of the Hyperbolic Unification. The muon anomalous moment **is** the
entanglement-as-rapidity measure at the operating-point rapidity (`cosh²η − sinh²η = 1` ⟹ `coth²η − 1 = csch²η`). -/
lemma anomaly_eq_schmidt_sq_sub_one (η : ℝ) (hη : 0 < η) :
    anomaly η = (schmidtNumber η) ^ 2 - 1 := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  unfold anomaly schmidtNumber
  rw [div_pow]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

/-- **[The g-factor is twice the squared Schmidt number] `g = 2K²`** — combining the standard Landé relation
`g = 2(1 + a)` with the Hyperbolic Unification `a = K² − 1` collapses to `g = 2K²`, where `K = schmidtNumber η =
coth η` is the entanglement Schmidt number at the operating-point rapidity. The measured g-factor of the muon thus reads
off the squared entanglement of its mode directly: the Dirac value `g = 2` corresponds to `K = 1` (no
entanglement, `η → ∞`), and the anomaly `g − 2 = 2(K² − 1)` is the entanglement excess above the unentangled
limit. -/
lemma gFactor_eq_two_schmidt_sq (η : ℝ) (hη : 0 < η) :
    gFactor (anomaly η) = 2 * (schmidtNumber η) ^ 2 := by
  rw [gFactor, anomaly_eq_schmidt_sq_sub_one η hη]; ring


/-- **The operating-point Lorentz factor** `γ = √(1 + 1/a)` — the storage-ring Lorentz factor at which the
electric-field spin precession cancels, as a function of the anomaly `a`. -/
noncomputable def gamma (a : ℝ) : ℝ := Real.sqrt (1 + 1 / a)

/-- **[`γ = cosh η`]** the operating-point Lorentz factor recovered from the operating-point momentum anomaly is exactly
`cosh η` — i.e. `a` *determines* the operating-point momentum (`γ = cosh η`, a relation, not a fit). For the measured
`a ≈ 1.166×10⁻³` this gives `γ ≈ 29.3`, the actual ring operating point. -/
lemma gamma_anomaly (η : ℝ) (hη : 0 < η) :
    gamma (anomaly η) = Real.cosh η := by
  have hs : Real.sinh η ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hη)
  unfold gamma anomaly
  rw [one_div_one_div,
    show 1 + (Real.sinh η) ^ 2 = (Real.cosh η) ^ 2 from by nlinarith [Real.cosh_sq_sub_sinh_sq η],
    Real.sqrt_sq (le_of_lt (Real.cosh_pos η))]

/-! ## D. Operational reconstruction of the Schmidt coordinate from ring kinematics -/

/-- The operational Schmidt number reconstructed from a supplied Lorentz factor,
`K(γ) = γ / √(γ² - 1)`. For the storage-ring operating point this uses the measured/design beam
kinematics rather than the fine-structure constant. This makes `K` operational, but the magic operating
point was selected using the anomaly-dependent Thomas–BMT cancellation and is not independent evidence
for the anomaly value. -/
noncomputable def schmidtNumberFromGamma (γ : ℝ) : ℝ :=
  γ / Real.sqrt (γ ^ 2 - 1)

/-- The Thomas–BMT magic-momentum anomaly reconstructed from the Lorentz factor,
`a(γ) = 1 / (γ² - 1)`. -/
noncomputable def magicAnomalyFromGamma (γ : ℝ) : ℝ :=
  1 / (γ ^ 2 - 1)

/-- The Lorentz-factor reconstruction satisfies the Schmidt-defect identity exactly:
`K(γ)² - 1 = 1/(γ² - 1)`. -/
lemma schmidtNumberFromGamma_sq_sub_one (γ : ℝ) (hγ : 1 < γ) :
    schmidtNumberFromGamma γ ^ 2 - 1 = magicAnomalyFromGamma γ := by
  have hγ2 : 0 < γ ^ 2 - 1 := by nlinarith
  unfold schmidtNumberFromGamma magicAnomalyFromGamma
  rw [div_pow, Real.sq_sqrt hγ2.le]
  field_simp
  ring

/-- A physical Lorentz factor above one reconstructs a genuine Schmidt number above one. -/
lemma one_lt_schmidtNumberFromGamma (γ : ℝ) (hγ : 1 < γ) :
    1 < schmidtNumberFromGamma γ := by
  have hγ2 : 0 < γ ^ 2 - 1 := by nlinarith
  have hKpos : 0 < schmidtNumberFromGamma γ := by
    exact div_pos (lt_trans one_pos hγ) (Real.sqrt_pos.mpr hγ2)
  have hdef := schmidtNumberFromGamma_sq_sub_one γ hγ
  have ha : 0 < magicAnomalyFromGamma γ := by
    exact one_div_pos.mpr hγ2
  nlinarith

/-- Reconstructing `K` from `γ = cosh η` gives exactly the existing hyperbolic Schmidt number
`coth η`; the experimental Lorentz-factor channel and the entanglement-rapidity carrier coincide. -/
lemma schmidtNumberFromGamma_cosh (η : ℝ) (hη : 0 < η) :
    schmidtNumberFromGamma (Real.cosh η) = schmidtNumber η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold schmidtNumberFromGamma schmidtNumber
  rw [show Real.cosh η ^ 2 - 1 = Real.sinh η ^ 2 by
    nlinarith [Real.cosh_sq_sub_sinh_sq η]]
  rw [Real.sqrt_sq hs.le]

/-- The approximate Fermilab/BNL magic Lorentz factor reported for the `3.094 GeV/c`
storage-ring beam. This records the published operating-point datum, not a fitted Lean parameter. -/
noncomputable def fermilabMagicGamma : ℝ := 293 / 10

/-- The operational Schmidt number reconstructed from the published magic Lorentz factor. -/
noncomputable def fermilabMagicSchmidtNumber : ℝ :=
  schmidtNumberFromGamma fermilabMagicGamma

/-- At the paper-reported `γ = 29.3`, the Schmidt defect is the exact rational
`K² - 1 = 100/85749`. -/
lemma fermilabMagicSchmidtDefect_exact :
    fermilabMagicSchmidtNumber ^ 2 - 1 = (100 : ℝ) / 85749 := by
  rw [show fermilabMagicSchmidtNumber =
      schmidtNumberFromGamma fermilabMagicGamma by rfl]
  rw [schmidtNumberFromGamma_sq_sub_one fermilabMagicGamma (by
    norm_num [fermilabMagicGamma])]
  norm_num [magicAnomalyFromGamma, fermilabMagicGamma]

/-- The published storage-ring Lorentz factor operationally fixes the Schmidt coordinate in the same narrow
interval as the QED-derived target: `1.0005 < K < 1.0006`. This is a kinematic consistency check, not an
independent anomaly prediction, because the magic operating point is anomaly-dependent. -/
lemma fermilabMagicSchmidtNumber_bounds :
    1.0005 < fermilabMagicSchmidtNumber
      ∧ fermilabMagicSchmidtNumber < 1.0006 := by
  have hKpos : 0 < fermilabMagicSchmidtNumber := by
    unfold fermilabMagicSchmidtNumber
    exact lt_trans one_pos
      (one_lt_schmidtNumberFromGamma fermilabMagicGamma (by
        norm_num [fermilabMagicGamma]))
  have hdef := fermilabMagicSchmidtDefect_exact
  constructor <;> nlinarith

/-- The Lorentz-factor channel fixes the corresponding anomaly at the experimentally relevant
`10⁻³` scale, without using `α`: `0.001166 < K² - 1 < 0.001167`. -/
lemma fermilabMagicSchmidtDefect_bounds :
    0.001166 < fermilabMagicSchmidtNumber ^ 2 - 1
      ∧ fermilabMagicSchmidtNumber ^ 2 - 1 < 0.001167 := by
  rw [fermilabMagicSchmidtDefect_exact]
  norm_num

/-- **Paper-to-experiment Schmidt reconstruction.** The reported storage-ring Lorentz
factor fixes `K > 1`, locates it in `(1.0005, 1.0006)`, and gives a Schmidt defect in
`(0.001166, 0.001167)`. Thus the repository has a physical operational route to `K`; it does not have
direct entanglement tomography or an anomaly-independent prediction from this magic-momentum datum. -/
lemma fermilabMagicGamma_determines_schmidtNumber :
    1 < fermilabMagicSchmidtNumber
      ∧ 1.0005 < fermilabMagicSchmidtNumber
      ∧ fermilabMagicSchmidtNumber < 1.0006
      ∧ 0.001166 < fermilabMagicSchmidtNumber ^ 2 - 1
      ∧ fermilabMagicSchmidtNumber ^ 2 - 1 < 0.001167 := by
  exact ⟨one_lt_schmidtNumberFromGamma fermilabMagicGamma (by
      norm_num [fermilabMagicGamma]),
    fermilabMagicSchmidtNumber_bounds.1,
    fermilabMagicSchmidtNumber_bounds.2,
    fermilabMagicSchmidtDefect_bounds.1,
    fermilabMagicSchmidtDefect_bounds.2⟩


/-! ## E. Why the magic point cannot test the two-route agreement

`SchmidtNumberFromAlpha` records in prose that the `α` and `γ` channels agree at the magic operating
point because that point is *selected* by the Thomas–BMT cancellation.  §E makes that a theorem
rather than a caveat, and in doing so identifies where the agreement would carry content.

The magic Lorentz factor is `γ = √(1 + 1/a)`, so `γ² − 1 = 1/a` and the reconstructed anomaly is `a`
identically — the `γ` channel returns the number it was built from.  Detune the momentum and the
identity breaks at once: agreement holds **iff** the detuning is trivial.  So a two-route agreement
measured at the magic momentum is a tautology, while the same agreement measured off-magic would be
a genuine constraint on `K = coth η` carrying one value through two independent determinations. -/

/-- **The `γ` route returns the anomaly it was built from.**  At the magic operating point the
reconstructed anomaly `1/(γ² − 1)` is exactly the `a` that fixed `γ`, so the agreement of the `α`
and `γ` channels there is forced by construction and is not evidence for the anomaly value. -/
theorem magicAnomalyFromGamma_gamma (a : ℝ) (ha : 0 < a) :
    magicAnomalyFromGamma (gamma a) = a := by
  have hpos : (0 : ℝ) ≤ 1 + 1 / a := by positivity
  unfold magicAnomalyFromGamma gamma
  rw [Real.sq_sqrt hpos]
  field_simp
  ring

/-- **Agreement holds exactly at the magic point and nowhere else.**  Scaling the operating-point
Lorentz factor by `s > 0` leaves the reconstructed anomaly equal to `a` **iff** `s² = 1`.

This is the falsifiable form of the two-route claim.  At `s = 1` the equality is the tautology above,
so the Fermilab magic-momentum data cannot test it.  At any `s ≠ 1` — an off-magic detuned run — the
kinematic reconstruction is no longer anomaly-derived, and requiring it to still return the
`α`-channel value is a real constraint that the data can refuse. -/
theorem anomaly_agreement_iff_magic {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    magicAnomalyFromGamma (s * gamma a) = a ↔ s ^ 2 = 1 := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hap : (0 : ℝ) < a + 1 := by linarith
  have hpos : (0 : ℝ) ≤ 1 + 1 / a := by positivity
  have hX : (gamma a) ^ 2 = 1 + 1 / a := by
    unfold gamma; rw [Real.sq_sqrt hpos]
  have hsq : (s * gamma a) ^ 2 - 1 = (s ^ 2 * (a + 1) - a) / a := by
    rw [mul_pow, hX]; field_simp
  unfold magicAnomalyFromGamma
  rw [hsq, one_div_div]
  constructor
  · intro hEqA
    have hN : s ^ 2 * (a + 1) - a ≠ 0 := by
      intro hz
      rw [hz, div_zero] at hEqA
      exact hane hEqA.symm
    have hmul : a = a * (s ^ 2 * (a + 1) - a) := (div_eq_iff hN).mp hEqA
    have hone : (1 : ℝ) = s ^ 2 * (a + 1) - a :=
      mul_left_cancel₀ hane (by rw [mul_one]; exact hmul)
    have hfac : s ^ 2 * (a + 1) = 1 * (a + 1) := by linarith
    exact mul_right_cancel₀ (ne_of_gt hap) hfac
  · intro hs1
    rw [hs1, one_mul]
    have hsimp : a + 1 - a = 1 := by ring
    rw [hsimp, div_one]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly_eq_schmidt_sq_sub_one where
  formalizes @ "claim:the-anomaly-is-the-schmidt-number-squared-minus-one-a-equals-K-squared-minus-one",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:operational-identification-of-the-anomaly-with-a-schmidt-number-rapidity-not-a-derivation-of-a-mu"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.gFactor_eq_two_schmidt_sq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly_eq_schmidt_sq_sub_one",
  formalizes @ "claim:the-g-factor-is-twice-the-schmidt-number-squared",
  requires @ "claim:the-anomaly-is-the-schmidt-number-squared-minus-one-a-equals-K-squared-minus-one"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.magicAnomalyFromGamma_gamma where
  formalizes @ "claim:at-the-thomas-bmt-magic-operating-point-the-kinematic-lorentz-factor-route-returns-the-anomaly-it-was-constructed-from-so-the-two-channel-agreement-there-is-a-tautology",
  epistemic_status @ "consistency-identity",
  caveat @ "this-is-the-negative-half-of-the-two-route-claim-it-shows-the-magic-point-agreement-carries-no-evidential-weight-it-does-not-refute-the-underlying-identification"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly_agreement_iff_magic where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-alpha-channel-and-storage-ring-kinematic-reconstructions-of-the-schmidt-number-agree-if-and-only-if-the-operating-point-is-exactly-magic-so-only-off-magic-data-can-test-the-two-route-claim",
  epistemic_status @ "consistency-identity",
  requires @ "claim:at-the-thomas-bmt-magic-operating-point-the-kinematic-lorentz-factor-route-returns-the-anomaly-it-was-constructed-from-so-the-two-channel-agreement-there-is-a-tautology",
  experimental_bound @ "value:fermilab-magic-gamma-29.3-and-a-mu-measured-to-127-ppb;test:an-off-magic-detuned-run-must-still-return-the-alpha-channel-schmidt-number-the-reconstruction-drifts-at-about-twice-the-fractional-detuning-so-a-0.1-percent-detune-moves-the-reconstructed-anomaly-by-0.2-percent-which-is-four-orders-above-the-measurement-precision",
  caveat @ "agreement-measured-at-the-magic-momentum-cannot-support-the-claim-because-the-operating-point-is-selected-by-the-anomaly-dependent-thomas-bmt-cancellation"

zil_file_contract physlib.anomalyRapidity where
  promises "The muon anomaly as a Schmidt-number rapidity: the anomaly is the Schmidt number squared minus one, and the g-factor is twice the Schmidt number squared, casting the storage-ring observable as an entanglement-rapidity reading."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.gamma"]
  forbids_substitutes ["a derivation of the Schmidt number from a state before using it, the identification is operational",
    "the frequency-to-a-mu extraction, which imports external ratios"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.anomaly_eq_schmidt_sq_sub_one,
    Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.gFactor_eq_two_schmidt_sq]

/- ZIL-END -/
