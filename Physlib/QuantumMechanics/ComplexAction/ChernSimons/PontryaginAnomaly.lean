/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
meta import Zil

/-!
# Chern-Simons/Pontryagin anomaly bridge

This file gives a compact, standard witness for the anomaly relation used
around Chern-Simons current divergence, Pontryagin density, and charge
flow.  It is deliberately smaller than the helper source: the core
objects are the current divergence, topological source, Pontryagin
density, information anomaly term, and in/out charges.

The bridge links this anomaly witness to the existing Chern-Simons/Witten
Wilson-Verlinde operator diagonalization, so anomaly-charge statements
and modular Wilson-loop statements can be used in one theorem.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly

/-- Standard Chern-Simons/Pontryagin normalization `1 / (16π²)`. -/
def chernSimonsPontryaginNormalization : ℝ :=
  (1 : ℝ) / (16 * Real.pi ^ 2)

/--
A compact anomaly witness.

The witness records:
* a Chern-Simons current divergence;
* an equivalent topological source;
* a Pontryagin contribution plus an additional anomaly term;
* an integrated charge jump.
-/
structure ChernSimonsPontryaginAnomalyWitness (M : Type*) [MeasurableSpace M] where
  /-- Background measure for the anomaly integral. -/
  μ : Measure M
  /-- Divergence of the Chern-Simons current. -/
  currentDivergence : M → ℝ
  /-- Topological source equal to the current divergence. -/
  topologicalSource : M → ℝ
  /-- Pontryagin density contribution. -/
  pontryaginDensity : M → ℝ
  /-- Additional information-anomaly density. -/
  informationAnomaly : M → ℝ
  /-- Incoming charge. -/
  qIn : ℝ
  /-- Outgoing charge. -/
  qOut : ℝ
  /-- Pointwise identification of current divergence with the topological source. -/
  divergence_eq_source : ∀ x, currentDivergence x = topologicalSource x
  /-- Pointwise anomaly split into Pontryagin density plus the additional anomaly term. -/
  anomaly_split_pointwise :
    ∀ x, currentDivergence x =
      chernSimonsPontryaginNormalization * pontryaginDensity x + informationAnomaly x
  /-- Integrated charge jump carried by the Chern-Simons current divergence. -/
  charge_jump_eq_current_integral :
    qOut - qIn = ∫ x, currentDivergence x ∂ μ

namespace ChernSimonsPontryaginAnomalyWitness

variable {M : Type*} [MeasurableSpace M]
variable (W : ChernSimonsPontryaginAnomalyWitness M)


/-- The normalized instanton density carried by the witness:
`q(x) = (1 / 16π²) Pontryagin(x)`. -/
def instantonDensity : M → ℝ :=
  fun x => chernSimonsPontryaginNormalization * W.pontryaginDensity x

/-- The integrated instanton number associated to the witness.  Integrality is
not asserted here; this is the analytic integral of the normalized density. -/
def instantonNumber : ℝ :=
  ∫ x, W.instantonDensity x ∂ W.μ

/-- The instanton number is the normalized Pontryagin integral. -/
lemma instantonNumber_eq_normalized_pontryagin_integral :
    W.instantonNumber =
      chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ) := by
  unfold instantonNumber instantonDensity
  rw [integral_const_mul]

/-- The pointwise anomaly split can be read as instanton density plus the
additional information-anomaly density. -/
lemma anomaly_split_pointwise_eq_instantonDensity (x : M) :
    W.currentDivergence x = W.instantonDensity x + W.informationAnomaly x := by
  simpa [instantonDensity] using W.anomaly_split_pointwise x

/-- The topological source has the same pointwise Pontryagin/anomaly split. -/
lemma source_split_pointwise (x : M) :
    W.topologicalSource x =
      chernSimonsPontryaginNormalization * W.pontryaginDensity x + W.informationAnomaly x := by
  calc
    W.topologicalSource x = W.currentDivergence x := (W.divergence_eq_source x).symm
    _ = chernSimonsPontryaginNormalization * W.pontryaginDensity x + W.informationAnomaly x :=
        W.anomaly_split_pointwise x

/-- The charge jump can be written as the integral of the topological source. -/
lemma charge_jump_eq_source_integral :
    W.qOut - W.qIn = ∫ x, W.topologicalSource x ∂ W.μ := by
  rw [W.charge_jump_eq_current_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => W.divergence_eq_source x

/-- Outgoing charge equals incoming charge plus the topological-source integral. -/
lemma qOut_eq_qIn_plus_source_integral :
    W.qOut = W.qIn + ∫ x, W.topologicalSource x ∂ W.μ := by
  have h := W.charge_jump_eq_source_integral
  linarith

/--
If the Pontryagin and additional anomaly densities are integrable, the
charge jump splits into their two integrated contributions.
-/
lemma charge_jump_eq_pontryagin_information_integral
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut - W.qIn =
      chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ)
        + ∫ x, W.informationAnomaly x ∂ W.μ := by
  rw [W.charge_jump_eq_current_integral]
  calc
    ∫ x, W.currentDivergence x ∂ W.μ =
        ∫ x, chernSimonsPontryaginNormalization * W.pontryaginDensity x
              + W.informationAnomaly x ∂ W.μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => W.anomaly_split_pointwise x
    _ = (∫ x, chernSimonsPontryaginNormalization * W.pontryaginDensity x ∂ W.μ)
          + ∫ x, W.informationAnomaly x ∂ W.μ := by
          exact integral_add (hPontryagin.const_mul chernSimonsPontryaginNormalization) hInformation
    _ = chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ)
          + ∫ x, W.informationAnomaly x ∂ W.μ := by
          rw [integral_const_mul]

/-- The charge jump splits into instanton number plus the integrated
information-anomaly term. -/
lemma charge_jump_eq_instantonNumber_plus_information_integral
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut - W.qIn =
      W.instantonNumber + ∫ x, W.informationAnomaly x ∂ W.μ := by
  rw [W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation,
    W.instantonNumber_eq_normalized_pontryagin_integral]

/-- Outgoing charge with the integrated Pontryagin/anomaly split. -/
lemma qOut_eq_qIn_plus_pontryagin_information_integral
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut =
      W.qIn + (chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ)
        + ∫ x, W.informationAnomaly x ∂ W.μ) := by
  have h := W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation
  linarith

/-- If the additional anomaly density vanishes, the charge jump is purely Pontryagin. -/
lemma charge_jump_eq_pontryagin_integral_of_information_zero
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation_zero : W.informationAnomaly = fun _ => 0) :
    W.qOut - W.qIn =
      chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ) := by
  have hInformation : Integrable W.informationAnomaly W.μ := by
    rw [hInformation_zero]
    exact integrable_zero M ℝ W.μ
  rw [W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation,
    hInformation_zero]
  simp

/-- If the additional anomaly density vanishes, the charge jump is exactly
the instanton number. -/
lemma charge_jump_eq_instantonNumber_of_information_zero
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation_zero : W.informationAnomaly = fun _ => 0) :
    W.qOut - W.qIn = W.instantonNumber := by
  rw [W.charge_jump_eq_pontryagin_integral_of_information_zero hPontryagin hInformation_zero,
    W.instantonNumber_eq_normalized_pontryagin_integral]

/-- **[The ABJ anomaly: axial charge conservation ⟺ the topological and information anomalies cancel].**
The axial charge is conserved across the region (`qOut = qIn`) *exactly* when the instanton number and the
integrated information-anomaly density sum to zero. Generically they do not: this is the Adler–Bell–Jackiw
anomaly — the failure of naive axial-current conservation, the axial charge jump being carried by the
Pontryagin/topological term. -/
lemma axialCharge_conserved_iff_anomaly_cancels
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut = W.qIn ↔ W.instantonNumber + ∫ x, W.informationAnomaly x ∂ W.μ = 0 := by
  rw [← W.charge_jump_eq_instantonNumber_plus_information_integral hPontryagin hInformation,
    sub_eq_zero]

end ChernSimonsPontryaginAnomalyWitness


/-- Magnetic flux quantized by an integer topological charge.  This is the
Dirac-monopole normalization `e g = 2π n`, expressed without asserting a
particular monopole solution or mass spectrum. -/
def quantizedMagneticFlux (electricCoupling : ℝ) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) / electricCoupling

/-- The quantized magnetic flux satisfies the Dirac quantization equality when
the electric coupling is nonzero. -/
lemma electricCoupling_mul_quantizedMagneticFlux
    (electricCoupling : ℝ) (n : ℤ) (he : electricCoupling ≠ 0) :
    electricCoupling * quantizedMagneticFlux electricCoupling n =
      2 * Real.pi * (n : ℝ) := by
  unfold quantizedMagneticFlux
  field_simp [he]

/-- A compact monopole-charge witness: an integer charge `n`, a nonzero
electric coupling, and the magnetic flux fixed by Dirac quantization. -/
structure DiracMonopoleCharge where
  electricCoupling : ℝ
  topologicalCharge : ℤ
  coupling_ne_zero : electricCoupling ≠ 0

namespace DiracMonopoleCharge

variable (D : DiracMonopoleCharge)

/-- The magnetic flux associated to the integer topological charge. -/
def magneticFlux : ℝ :=
  quantizedMagneticFlux D.electricCoupling D.topologicalCharge

/-- The Dirac quantization condition `e g = 2π n`. -/
lemma dirac_quantization :
    D.electricCoupling * D.magneticFlux =
      2 * Real.pi * (D.topologicalCharge : ℝ) :=
  electricCoupling_mul_quantizedMagneticFlux
    D.electricCoupling D.topologicalCharge D.coupling_ne_zero

/-- The neutral topological sector has zero quantized magnetic flux. -/
lemma magneticFlux_zero_of_topologicalCharge_zero
    (h : D.topologicalCharge = 0) : D.magneticFlux = 0 := by
  unfold magneticFlux quantizedMagneticFlux
  rw [h]
  norm_num

end DiracMonopoleCharge

open ChernSimons.Gravity

/--
Combined bridge: a Chern-Simons/Pontryagin charge-jump witness and the
existing Wilson/Verlinde diagonalization can be used simultaneously.
-/
lemma charge_jump_and_wilsonVerlinde_diagonalization
    {M : Type*} [MeasurableSpace M]
    (W : ChernSimonsPontryaginAnomalyWitness M)
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ)
    (k : ℕ) (hk : 0 < k) (a q : Fin k) :
    W.qOut - W.qIn =
      chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ)
        + ∫ x, W.informationAnomaly x ∂ W.μ
      ∧ cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
        = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) :=
  ⟨W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation,
    cswWilsonVerlinde_diagonalization k hk a q⟩

/--
Combined bridge: the anomaly charge jump can be read as instanton number plus
information anomaly while Wilson/Verlinde diagonalization supplies the
Chern-Simons loop-sector diagonal basis.
-/
lemma instantonNumber_and_wilsonVerlinde_diagonalization
    {M : Type*} [MeasurableSpace M]
    (W : ChernSimonsPontryaginAnomalyWitness M)
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ)
    (k : ℕ) (hk : 0 < k) (a q : Fin k) :
    W.qOut - W.qIn =
      W.instantonNumber + ∫ x, W.informationAnomaly x ∂ W.μ
      ∧ cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
        = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) :=
  ⟨W.charge_jump_eq_instantonNumber_plus_information_integral hPontryagin hInformation,
    cswWilsonVerlinde_diagonalization k hk a q⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.ChernSimonsPontryaginAnomalyWitness.instantonNumber_eq_normalized_pontryagin_integral where
  formalizes @ "claim:the-instanton-number-is-the-pontryagin-density-integral-normalized-by-one-over-sixteen-pi-squared",
  supported_by @ "paper:adler-bell-jackiw-axial-anomaly"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.ChernSimonsPontryaginAnomalyWitness.axialCharge_conserved_iff_anomaly_cancels where
  formalizes @ "claim:the-axial-charge-is-conserved-iff-the-instanton-number-and-the-information-anomaly-integral-cancel-the-adler-bell-jackiw-anomaly",
  requires @ "claim:the-instanton-number-is-the-pontryagin-density-integral-normalized-by-one-over-sixteen-pi-squared",
  supported_by @ "paper:adler-bell-jackiw-axial-anomaly",
  caveat @ "claim:the-pointwise-anomaly-split-of-the-current-divergence-into-pontryagin-plus-information-density-is-a-witness-input-not-derived"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.DiracMonopoleCharge.dirac_quantization where
  formalizes @ "claim:the-dirac-quantization-condition-electric-coupling-times-magnetic-flux-is-two-pi-times-the-integer-topological-charge",
  supported_by @ "paper:dirac-1931-quantised-singularities"

zil_file_contract physlib.pontryaginAnomaly where
  promises "The Chern-Simons/Pontryagin topological sector of the axial anomaly: the instanton number is the Pontryagin-density integral normalized by one over sixteen pi squared; the axial charge is conserved iff the instanton number and the integrated information-anomaly density cancel (the Adler-Bell-Jackiw anomaly, generically nonzero); and the Dirac quantization condition fixes the monopole magnetic flux to two pi times an integer topological charge."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.ChernSimonsPontryaginAnomalyWitness",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.chernSimonsPontryaginNormalization",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.quantizedMagneticFlux"]
  forbids_substitutes ["a field-theoretic derivation of the anomaly split of the current divergence, which is a witness input",
    "an assertion of integrality of the instanton number, which is not asserted from the analytic integral alone"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.ChernSimonsPontryaginAnomalyWitness.instantonNumber_eq_normalized_pontryagin_integral,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.ChernSimonsPontryaginAnomalyWitness.axialCharge_conserved_iff_anomaly_cancels,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.DiracMonopoleCharge.dirac_quantization]

/- ZIL-END -/
