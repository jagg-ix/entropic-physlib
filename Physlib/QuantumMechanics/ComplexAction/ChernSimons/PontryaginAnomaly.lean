/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith

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

No additional assumptions.
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
  /-- Integrated charge jump encoded in the Chern-Simons current divergence. -/
  charge_jump_eq_current_integral :
    qOut - qIn = ∫ x, currentDivergence x ∂ μ

namespace ChernSimonsPontryaginAnomalyWitness

variable {M : Type*} [MeasurableSpace M]
variable (W : ChernSimonsPontryaginAnomalyWitness M)

/-! ## §A — Pontryagin density as instanton density -/

/-- The normalized instanton density encoded in the witness:
`q(x) = (1 / 16π²) Pontryagin(x)`. -/
def instantonDensity : M → ℝ :=
  fun x => chernSimonsPontryaginNormalization * W.pontryaginDensity x

/-- The integrated instanton number associated to the witness.  Integrality is
not asserted here; this is the analytic integral of the normalized density. -/
def instantonNumber : ℝ :=
  ∫ x, W.instantonDensity x ∂ W.μ

/-- The instanton number is the normalized Pontryagin integral. -/
theorem instantonNumber_eq_normalized_pontryagin_integral :
    W.instantonNumber =
      chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ) := by
  unfold instantonNumber instantonDensity
  rw [integral_const_mul]

/-- The pointwise anomaly split can be read as instanton density plus the
additional information-anomaly density. -/
theorem anomaly_split_pointwise_eq_instantonDensity (x : M) :
    W.currentDivergence x = W.instantonDensity x + W.informationAnomaly x := by
  simpa [instantonDensity] using W.anomaly_split_pointwise x

/-- The topological source has the same pointwise Pontryagin/anomaly split. -/
theorem source_split_pointwise (x : M) :
    W.topologicalSource x =
      chernSimonsPontryaginNormalization * W.pontryaginDensity x + W.informationAnomaly x := by
  calc
    W.topologicalSource x = W.currentDivergence x := (W.divergence_eq_source x).symm
    _ = chernSimonsPontryaginNormalization * W.pontryaginDensity x + W.informationAnomaly x :=
        W.anomaly_split_pointwise x

/-- The charge jump can be written as the integral of the topological source. -/
theorem charge_jump_eq_source_integral :
    W.qOut - W.qIn = ∫ x, W.topologicalSource x ∂ W.μ := by
  rw [W.charge_jump_eq_current_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => W.divergence_eq_source x

/-- Outgoing charge equals incoming charge plus the topological-source integral. -/
theorem qOut_eq_qIn_plus_source_integral :
    W.qOut = W.qIn + ∫ x, W.topologicalSource x ∂ W.μ := by
  have h := W.charge_jump_eq_source_integral
  linarith

/--
If the Pontryagin and additional anomaly densities are integrable, the
charge jump splits into their two integrated contributions.
-/
theorem charge_jump_eq_pontryagin_information_integral
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
theorem charge_jump_eq_instantonNumber_plus_information_integral
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut - W.qIn =
      W.instantonNumber + ∫ x, W.informationAnomaly x ∂ W.μ := by
  rw [W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation,
    W.instantonNumber_eq_normalized_pontryagin_integral]

/-- Outgoing charge with the integrated Pontryagin/anomaly split. -/
theorem qOut_eq_qIn_plus_pontryagin_information_integral
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation : Integrable W.informationAnomaly W.μ) :
    W.qOut =
      W.qIn + (chernSimonsPontryaginNormalization * (∫ x, W.pontryaginDensity x ∂ W.μ)
        + ∫ x, W.informationAnomaly x ∂ W.μ) := by
  have h := W.charge_jump_eq_pontryagin_information_integral hPontryagin hInformation
  linarith

/-- If the additional anomaly density vanishes, the charge jump is purely Pontryagin. -/
theorem charge_jump_eq_pontryagin_integral_of_information_zero
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
theorem charge_jump_eq_instantonNumber_of_information_zero
    (hPontryagin : Integrable W.pontryaginDensity W.μ)
    (hInformation_zero : W.informationAnomaly = fun _ => 0) :
    W.qOut - W.qIn = W.instantonNumber := by
  rw [W.charge_jump_eq_pontryagin_integral_of_information_zero hPontryagin hInformation_zero,
    W.instantonNumber_eq_normalized_pontryagin_integral]

end ChernSimonsPontryaginAnomalyWitness

/-! ## §B — quantized magnetic flux representative for monopole charge -/

/-- Magnetic flux quantized by an integer topological charge.  This is the
Dirac-monopole normalization `e g = 2π n`, expressed without asserting a
particular monopole solution or mass spectrum. -/
def quantizedMagneticFlux (electricCoupling : ℝ) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) / electricCoupling

/-- The quantized magnetic flux satisfies the Dirac quantization equality when
the electric coupling is nonzero. -/
theorem electricCoupling_mul_quantizedMagneticFlux
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
theorem dirac_quantization :
    D.electricCoupling * D.magneticFlux =
      2 * Real.pi * (D.topologicalCharge : ℝ) :=
  electricCoupling_mul_quantizedMagneticFlux
    D.electricCoupling D.topologicalCharge D.coupling_ne_zero

/-- The neutral topological sector has zero quantized magnetic flux. -/
theorem magneticFlux_zero_of_topologicalCharge_zero
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
theorem charge_jump_and_wilsonVerlinde_diagonalization
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
theorem instantonNumber_and_wilsonVerlinde_diagonalization
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
