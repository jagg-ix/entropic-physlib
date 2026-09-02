/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
public import Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral
public import Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons.TrefoilKauffmanRepoLinks
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
meta import Zil

/-!
# The Lorentz force between D0 and D6 branes

This module formalizes the equation-level core of Billó--Di Vecchia--Frau--Lerda--Pesando--Russo--Sciuto,
*The Lorentz Force between D0 and D6 Branes in String and M(atrix) Theory*, Mod. Phys. Lett. A **13**
(1998) 2977--2990.

The paper computes the same velocity-linear interaction in three presentations:

* the D0 probe coupled to the R--R one-form sourced, by Hodge duality, by the D6 brane;
* the R--R odd-spin boundary-state amplitude;
* the unpaired chiral fermion in the Matrix-theory one-loop determinant.

The formalization reuses the repository's actual Lorentz-force numerator
`Lorentz.ForceBCJDual.lorentzForceNum` and Mathlib's Gaussian integral.  It proves:

* **§A -- transverse Hodge geometry.**  The component relations
  `∂₇C₇ = ∂₈A₉`, `∂₈C₇ = -∂₇A₉` imply that the two transverse gradients are orthogonal and have the
  same norm.
* **§B -- probe/source coefficient.**  The D-brane charge normalization `μ₀ μ₆ = 2π` turns the Wess--Zumino
  coefficient `μ₀ μ₆/(4π)` into `1/2`, hence `V_odd(r) = -v/(2r)` (Eqs. 1.5--1.7).  A concrete
  antisymmetric Faraday tensor realizes this potential as an existing `lorentzForceNum` component.
* **§C -- exact radial and time-reversal behavior.**  The potential is odd in velocity and its radial
  derivative gives the inverse-square Lorentz force.
* **§D -- Matrix-theory Schwinger step.**  The Gaussian change of variables in Eq. 3.12 is proved as an
  actual Lebesgue-integral identity.  Together with the charge calculation it packages the exact
  probe/string/Matrix coefficient match of Eqs. 1.7, 2.24 and 3.13.
* **§E -- shared complex-action carrier.**  The positive Euclidean continuation of the protected odd
  interaction has the exact Nagao--Nielsen damping norm.  Under visible action and rest-clock matches,
  the existing Ooguri--Vafa--Verlinde/IKKT theorem identifies that same weight with the Type-IIB matrix
  weight, the Compton phase, and half the rest Zitterbewegung phase.  A finite-measure analytic carrier
  then supports the proved Witten Wilson integral, Verlinde `S`-matrix braiding, trefoil Stokes cycle,
  and normalized rapidity-selected contour.

## Honest scope

Lean proves the Hodge-component algebra, charge normalization, concrete Lorentz-force realization,
radial derivative and Gaussian integral.  The boundary-state/GSO calculation producing Eq. 2.24 and the
functional-determinant/chiral-zero-mode reduction producing Eq. 3.11 are cited paper inputs; this module
does not replace either calculation by a renamed algebraic formula.  The OVV/D0 action match and
rest-energy clock match are explicit premises.  Sharing a complex-action carrier does not identify D0--D6
scattering with a trefoil, nor does the finite reference measure construct the full continuum field measure.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Matrix
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.IIBMatrixModel
open Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DZeroDSixLorentzForce

open TrefoilThimble

/-! ## A. The transverse Hodge-duality relations -/

/-- The four derivatives entering the D6 seven-form / D0 one-form duality relation around Eq. (1.5).
`C` denotes the D6 R--R seven-form component `A₀₁₂...₆`; `A` denotes the D0 one-form component `A₉`.
The two equations say that the transverse gradient of `A₉` is the quarter-turn of the gradient of `C`. -/
structure DZeroDSixTransverseHodgeData where
  d7C : ℝ
  d8C : ℝ
  d7A : ℝ
  d8A : ℝ
  dual7 : d7C = d8A
  dual8 : d8C = -d7A

/-- **The Hodge-related transverse gradients are orthogonal.**  This is the local geometric content of
`∂₇C = ∂₈A₉` and `∂₈C = -∂₇A₉`: a Hodge quarter-turn is perpendicular to the original gradient. -/
theorem dZeroDSix_hodge_gradients_orthogonal (D : DZeroDSixTransverseHodgeData) :
    D.d7C * D.d7A + D.d8C * D.d8A = 0 := by
  rw [D.dual7, D.dual8]
  ring

/-- **The Hodge-related transverse gradients have equal squared norm.** -/
theorem dZeroDSix_hodge_gradients_equal_norm (D : DZeroDSixTransverseHodgeData) :
    D.d7C ^ 2 + D.d8C ^ 2 = D.d7A ^ 2 + D.d8A ^ 2 := by
  rw [D.dual7, D.dual8]
  ring

/-! ## B. D-brane charge normalization and a concrete Lorentz-force carrier -/

/-- The D0 Wess--Zumino velocity coupling after inserting the D6 magnetic potential, before using
`μ₀ μ₆ = 2π`.  Natural string units and the sign convention of Eqs. (1.5)--(1.7) are used. -/
noncomputable def dZeroDSixChargeNormalizedPotential (mu0 mu6 v r : ℝ) : ℝ :=
  -(mu0 * mu6 / (4 * Real.pi)) * v / r

/-- The R--R odd-spin / Lorentz potential of Eqs. (1.7) and (2.24), `V_odd(r) = -v/(2r)`. -/
noncomputable def dZeroDSixLorentzPotential (v r : ℝ) : ℝ := -v / (2 * r)

/-- **The D-brane charge product derives the universal half coefficient.**  From `μ₀ μ₆ = 2π`, the
probe Wess--Zumino coupling reduces exactly to `V_odd(r) = -v/(2r)`. -/
theorem dZeroDSix_chargeNormalizedPotential_eq (mu0 mu6 v r : ℝ)
    (hcharge : mu0 * mu6 = 2 * Real.pi) :
    dZeroDSixChargeNormalizedPotential mu0 mu6 v r = dZeroDSixLorentzPotential v r := by
  unfold dZeroDSixChargeNormalizedPotential dZeroDSixLorentzPotential
  rw [hcharge]
  field_simp [Real.pi_ne_zero]
  ring

/-- A concrete antisymmetric magnetic Faraday tensor in a transverse `(1,2)` plane with
`F₁₂ = -1/(2r)`.  It embeds the paper's reduced transverse interaction in the repository's four-component
Lorentz-force carrier. -/
noncomputable def dZeroDSixMagneticTensor (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun mu nu =>
    if mu = 1 ∧ nu = 2 then -(1 / (2 * r))
    else if mu = 2 ∧ nu = 1 then 1 / (2 * r)
    else 0

/-- The probe velocity supported on the second transverse coordinate. -/
def dZeroProbeVelocity (v : ℝ) : Fin 4 → ℝ := fun mu => if mu = 2 then v else 0

/-- **The D0--D6 odd potential is an actual Lorentz-force component.**  Contracting the concrete
antisymmetric magnetic tensor with the probe velocity gives `F₁₂v² = -v/(2r)`, using the existing
`lorentzForceNum = (F V)_μ` rather than introducing a parallel force definition. -/
theorem dZeroDSixLorentzPotential_eq_force_component (v r : ℝ) :
    dZeroDSixLorentzPotential v r =
      lorentzForceNum (dZeroDSixMagneticTensor r) (dZeroProbeVelocity v) 1 := by
  simp [dZeroDSixLorentzPotential, lorentzForceNum, dZeroDSixMagneticTensor,
    dZeroProbeVelocity, Matrix.mulVec, dotProduct]
  ring

/-! ## C. Velocity parity and the radial force -/

/-- The R--R odd-spin potential is odd under reversal of the relative velocity. -/
theorem dZeroDSixLorentzPotential_timeReversal (v r : ℝ) :
    dZeroDSixLorentzPotential (-v) r = -dZeroDSixLorentzPotential v r := by
  unfold dZeroDSixLorentzPotential
  ring

/-- The radial Lorentz force `-∂ᵣV_odd = -v/(2r²)`. -/
noncomputable def dZeroDSixRadialForce (v r : ℝ) : ℝ := -v / (2 * r ^ 2)

/-- **The inverse-square radial force is derived from the paper's potential.** -/
theorem dZeroDSixLorentzPotential_hasDerivAt (v : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (dZeroDSixLorentzPotential v) (-dZeroDSixRadialForce v r) r := by
  have h := (hasDerivAt_inv hr).const_mul (-v / 2)
  have hp : dZeroDSixLorentzPotential v = fun x : ℝ => (-v / 2) * x⁻¹ := by
    funext x
    unfold dZeroDSixLorentzPotential
    ring
  rw [hp]
  rw [show -dZeroDSixRadialForce v r = (-v / 2) * (-(r ^ 2)⁻¹) by
    unfold dZeroDSixRadialForce
    ring]
  exact h

/-- Multiplying by the separation removes the radial denominator and exposes the exact odd coefficient
`r V_odd(r) = -v/2`.  This is the scale-independent coefficient protected by the R--R odd-spin
nonzero-mode cancellation in the paper. -/
theorem dZeroDSix_radius_mul_potential (v : ℝ) {r : ℝ} (hr : r ≠ 0) :
    r * dZeroDSixLorentzPotential v r = -v / 2 := by
  unfold dZeroDSixLorentzPotential
  field_simp [hr]

/-! ## D. The Matrix-theory Schwinger/Gaussian identity -/

/-- **Billó et al. Eq. (3.12), proved as a Lebesgue integral.**  For positive Schwinger parameter `s` and
velocity `v`, rescaling the Gaussian time integral restores precisely the factor `1/v`:
`√(s/π) ∫ exp[-s(vτ)²] dτ = 1/v`.

This is the analytic step used to turn the velocity-independent chiral-projector term in the Matrix
determinant into the velocity-linear odd interaction of Eq. (3.13). -/
theorem dZeroDSix_matrix_velocity_gaussian_identity (s v : ℝ) (hs : 0 < s) (hv : 0 < v) :
    Real.sqrt (s / Real.pi) *
        (∫ tau : ℝ, Real.exp (-s * (v * tau) ^ 2)) = 1 / v := by
  have hchange := Measure.integral_comp_mul_left
    (fun x : ℝ => Real.exp (-s * x ^ 2)) v
  have hint : (∫ tau : ℝ, Real.exp (-s * (v * tau) ^ 2)) =
      |v⁻¹| * (∫ x : ℝ, Real.exp (-s * x ^ 2)) := by
    simpa only [smul_eq_mul] using hchange
  rw [hint, integral_gaussian s, abs_of_pos (inv_pos.mpr hv)]
  calc
    Real.sqrt (s / Real.pi) * (v⁻¹ * Real.sqrt (Real.pi / s)) =
        v⁻¹ * (Real.sqrt (s / Real.pi) * Real.sqrt (Real.pi / s)) := by ring
    _ = v⁻¹ * Real.sqrt ((s / Real.pi) * (Real.pi / s)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ s / Real.pi)]
    _ = v⁻¹ := by
      rw [show (s / Real.pi) * (Real.pi / s) = 1 by
          field_simp [hs.ne', Real.pi_ne_zero],
        Real.sqrt_one, mul_one]
    _ = 1 / v := by rw [one_div]

/-- **Probe/string/Matrix closure at the protected odd coefficient.**  The charge-normalized probe
potential is the concrete Lorentz-force component; its protected coefficient is `-v/2`; and the Matrix
Schwinger time integral supplies exactly `1/v`.  The R--R boundary-state computation identifies this same
canonical potential with Eq. (2.24), while the first and third conjuncts are independently checked here. -/
theorem dZeroDSix_probe_string_matrix_lorentz_closure (mu0 mu6 s v : ℝ) {r : ℝ}
    (hcharge : mu0 * mu6 = 2 * Real.pi) (hr : r ≠ 0) (hs : 0 < s) (hv : 0 < v) :
    dZeroDSixChargeNormalizedPotential mu0 mu6 v r =
        lorentzForceNum (dZeroDSixMagneticTensor r) (dZeroProbeVelocity v) 1
      ∧ r * dZeroDSixLorentzPotential v r = -v / 2
      ∧ Real.sqrt (s / Real.pi) *
          (∫ tau : ℝ, Real.exp (-s * (v * tau) ^ 2)) = 1 / v := by
  exact ⟨dZeroDSix_chargeNormalizedPotential_eq mu0 mu6 v r hcharge |>.trans
      (dZeroDSixLorentzPotential_eq_force_component v r),
    dZeroDSix_radius_mul_potential v hr,
    dZeroDSix_matrix_velocity_gaussian_identity s v hs hv⟩

/-! ## E. Complex-action, Type-IIB Matrix, and Witten--Verlinde links -/

/-- The positive Euclidean/entropic action associated with evolving for parameter time `tau`
against the odd D0--D6 potential.  It is defined as `-tau * V_odd`, so this is an explicit
Euclidean-continuation carrier, not a claim that the Lorentzian velocity-odd potential is itself an
imaginary action. -/
noncomputable def dZeroDSixOddEuclideanAction (v r tau : ℝ) : ℝ :=
  tau * (v / (2 * r))

/-- The Euclidean odd action is exactly minus the time-integrated protected Lorentz potential. -/
theorem dZeroDSixOddEuclideanAction_eq_neg_time_mul_potential (v r tau : ℝ) :
    dZeroDSixOddEuclideanAction v r tau =
      -tau * dZeroDSixLorentzPotential v r := by
  unfold dZeroDSixOddEuclideanAction dZeroDSixLorentzPotential
  ring

/-- Forward motion, positive separation, and nonnegative elapsed parameter time select the damping
sector `S_I >= 0`. -/
theorem dZeroDSixOddEuclideanAction_nonneg {v r tau : ℝ}
    (hv : 0 ≤ v) (hr : 0 < r) (htau : 0 ≤ tau) :
    0 ≤ dZeroDSixOddEuclideanAction v r tau := by
  unfold dZeroDSixOddEuclideanAction
  exact mul_nonneg htau (div_nonneg hv (mul_nonneg (by norm_num) hr.le))

/-- At fixed forward velocity and positive separation, the D0--D6 Euclidean odd action is monotone in
elapsed parameter time. -/
theorem dZeroDSixOddEuclideanAction_monotone_time {v r : ℝ}
    (hv : 0 ≤ v) (hr : 0 < r) :
    Monotone (fun tau => dZeroDSixOddEuclideanAction v r tau) := by
  intro tau₁ tau₂ htau
  unfold dZeroDSixOddEuclideanAction
  exact mul_le_mul_of_nonneg_right htau (div_nonneg hv (mul_nonneg (by norm_num) hr.le))

/-- The D0--D6 odd Euclidean sector evaluated by the repository's common Nagao--Nielsen
complex-action kernel. -/
noncomputable def dZeroDSixNagaoNielsenWeight (v r tau hbar : ℝ) : ℂ :=
  lorentzianKernel 0 (dZeroDSixOddEuclideanAction v r tau) hbar

/-- **The odd interaction becomes exact entropic damping.**  The norm of its Nagao--Nielsen weight
is `exp (-S_I / hbar)`, proved by reusing the common complex-action kernel theorem. -/
@[zil_level bridge_theorem]
theorem dZeroDSixNagaoNielsenWeight_norm (v r tau hbar : ℝ) :
    ‖dZeroDSixNagaoNielsenWeight v r tau hbar‖ =
      Real.exp (-(dZeroDSixOddEuclideanAction v r tau / hbar)) := by
  exact lorentzianKernel_norm_is_damping 0 (dZeroDSixOddEuclideanAction v r tau) hbar

/-- **The D0--D6 path-weight norm is antitone in elapsed time.**  This is the operational entropic arrow
of the Euclidean odd sector: increasing a nonnegative imaginary action cannot amplify the path weight. -/
@[zil_level bridge_theorem]
theorem dZeroDSixNagaoNielsenWeight_norm_antitone_time
    {v r hbar : ℝ} (hv : 0 ≤ v) (hr : 0 < r) (hhbar : 0 < hbar) :
    Antitone (fun tau => ‖dZeroDSixNagaoNielsenWeight v r tau hbar‖) := by
  intro tau₁ tau₂ htau
  change ‖dZeroDSixNagaoNielsenWeight v r tau₂ hbar‖ ≤
    ‖dZeroDSixNagaoNielsenWeight v r tau₁ hbar‖
  rw [dZeroDSixNagaoNielsenWeight_norm, dZeroDSixNagaoNielsenWeight_norm]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact div_le_div_of_nonneg_right
    (dZeroDSixOddEuclideanAction_monotone_time hv hr htau) hhbar.le

/-- **OVV/IKKT Matrix string to D0--D6 entropic-clock bridge.**

If the rescaled IIB matrix action matches the OVV flux action, and the latter's imaginary action is
calibrated both to the D0--D6 Euclidean odd action and to a rest-energy clock, then the same matrix
path weight is the D0--D6 Nagao--Nielsen weight.  Its modulus is the corresponding damping, while its
dimensionless imaginary action is both the Compton phase and half the rest-frame Zitterbewegung phase.
The two calibration equalities are deliberately explicit premises. -/
@[zil_level bridge_theorem]
theorem iibOvv_dZeroDSix_entropicClock_chain
    {N d : ℕ} (g hbar : ℝ) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (W : ℂ) (v r tauD0 m c tauClock : ℝ) (hm : 0 ≤ m) (hhbar : 0 < hbar)
    (haction : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : ℂ))
    (hD0 : ovvImaginaryAction hbar W = dZeroDSixOddEuclideanAction v r tauD0)
    (hclock : ovvImaginaryAction hbar W = m * c ^ 2 * tauClock) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu) =
        dZeroDSixNagaoNielsenWeight v r tauD0 hbar
      ∧ ‖iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu)‖ =
        Real.exp (-(dZeroDSixOddEuclideanAction v r tauD0 / hbar))
      ∧ dZeroDSixOddEuclideanAction v r tauD0 / hbar =
        comptonPhase m c hbar tauClock
      ∧ dZeroDSixOddEuclideanAction v r tauD0 / hbar =
        (zitterbewegungFrequency 0 m c hbar / 2) * tauClock
      ∧ 0 ≤ comptonFrequency m c hbar := by
  have hChain := iib_ovv_entropicTime_compton_zitterbewegung_chain
    g hbar hg A W m c tauClock hm hhbar haction hclock
  have hMatrix := hChain.1
  have hFlux := hChain.2.1
  have hCompton := hChain.2.2.1
  have hZitter := hChain.2.2.2.1
  have hFreq := entropicTime_rate_nonneg m c hbar hm hhbar
  have hWeight :
      iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu) =
        dZeroDSixNagaoNielsenWeight v r tauD0 hbar := by
    calc
      _ = fluxInsertion W := hMatrix
      _ = lorentzianKernel 0 (ovvImaginaryAction hbar W) hbar := hFlux
      _ = dZeroDSixNagaoNielsenWeight v r tauD0 hbar := by
        rw [hD0]
        rfl
  refine ⟨hWeight, ?_, ?_, ?_, hFreq⟩
  · rw [hWeight]
    exact dZeroDSixNagaoNielsenWeight_norm v r tauD0 hbar
  · rw [← hD0]
    exact hCompton
  · rw [← hD0]
    exact hZitter

/-- **Finite-rapidity D0--D6/OVV/IKKT closure.**  Under the separately visible action matches, the
same Type-IIB matrix weight is the D0--D6 Nagao--Nielsen weight, its dimensionless imaginary action is
`log K(eta)`, and its positive-rapidity modulus is exactly `tanh eta = 1/K(eta)`. -/
@[zil_level bridge_theorem]
theorem iibOvv_dZeroDSix_rapidity_chain
    {N d : ℕ} (g hbar : ℝ) (hg : 0 < g)
    (A : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (W : ℂ) (v r tau eta : ℝ) (hhbar : hbar ≠ 0) (heta : 0 < eta)
    (haction : -iibBosonic A = Complex.I * (ovvImaginaryAction hbar W : ℂ))
    (hD0 : ovvImaginaryAction hbar W = dZeroDSixOddEuclideanAction v r tau)
    (hRapidity : dZeroDSixOddEuclideanAction v r tau = entropicAction hbar eta) :
    iibBosonicPathWeight g hbar
        (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu) =
        dZeroDSixNagaoNielsenWeight v r tau hbar
      ∧ dZeroDSixOddEuclideanAction v r tau / hbar =
        Real.log (schmidtNumber eta)
      ∧ ‖iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu)‖ = Real.tanh eta := by
  have hMatrix := iibRescaledBosonicPathWeight_eq_fluxInsertion_of_normalized_match
    g hbar hg A W hhbar haction
  have hFlux := fluxInsertion_eq_ovvKernel W hbar hhbar
  have hWeight :
      iibBosonicPathWeight g hbar
          (fun mu ↦ ((Real.sqrt g : ℝ) : ℂ) • A mu) =
        dZeroDSixNagaoNielsenWeight v r tau hbar := by
    calc
      _ = fluxInsertion W := hMatrix
      _ = lorentzianKernel 0 (ovvImaginaryAction hbar W) hbar := hFlux
      _ = dZeroDSixNagaoNielsenWeight v r tau hbar := by rw [hD0]; rfl
  refine ⟨hWeight, ?_, ?_⟩
  · rw [hRapidity]
    unfold entropicAction
    field_simp
  · rw [hWeight, dZeroDSixNagaoNielsenWeight_norm, hRapidity]
    exact suppression_eq_tanh hbar eta hhbar heta

/-- A finite-measure complex-action carrier whose imaginary action is the D0--D6 odd Euclidean
action.  This packages the analytic input needed by the existing Witten Wilson-integral constructor;
it does not identify the finite reference measure with the full D-brane or Chern--Simons field measure. -/
noncomputable def dZeroDSixFiniteMeasureModel
    {Field : Type*} [MeasurableSpace Field]
    (mu : Measure Field) (hbar v r tau : ℝ) (hhbar : 0 < hbar)
    (hSI : 0 ≤ dZeroDSixOddEuclideanAction v r tau) :
    MeasurePathIntegralModel Field where
  μ := mu
  hbar := hbar
  hbar_pos := hhbar
  actionRe := fun _ => 0
  actionIm := fun _ => dZeroDSixOddEuclideanAction v r tau
  measurable_actionRe := measurable_const
  measurable_actionIm := measurable_const
  actionIm_nonneg := fun _ => hSI

/-- Finiteness of the supplied reference measure is preserved by the D0--D6 action decoration. -/
instance dZeroDSixFiniteMeasureModel_isFinite
    {Field : Type*} [MeasurableSpace Field]
    (mu : Measure Field) [IsFiniteMeasure mu]
    (hbar v r tau : ℝ) (hhbar : 0 < hbar)
    (hSI : 0 ≤ dZeroDSixOddEuclideanAction v r tau) :
    IsFiniteMeasure (dZeroDSixFiniteMeasureModel mu hbar v r tau hhbar hSI).μ := by
  change IsFiniteMeasure mu
  infer_instance

/-- **Witten--Chern--Simons/Verlinde/trefoil and Nagao--Nielsen contour closure.**

On the finite-measure carrier with the D0--D6 imaginary action, Wilson braiding is an actual integrable
complex-action observable with the rigorous FK norm bound.  Its value is the conjugated Verlinde
`S`-matrix entry; the Hopf `R`-matrix obeys Yang--Baxter; the first nonabelian trefoil Stokes cycle has
coefficients `(1,-1)`; and the rapidity-selected Nagao--Nielsen contour is normalized. -/
@[zil_level bridge_theorem]
theorem dZeroDSix_wittenVerlindeTrefoil_contour_chain
    {Field : Type*} [MeasurableSpace Field]
    (mu : Measure Field) [IsFiniteMeasure mu]
    (hbar v r tau : ℝ) (hhbar : 0 < hbar)
    (hSI : 0 ≤ dZeroDSixOddEuclideanAction v r tau)
    (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) (a b : Fin k)
    (theta epsilon : ℝ) (hepsilon : 0 < epsilon) :
    let model := dZeroDSixFiniteMeasureModel mu hbar v r tau hhbar hSI
    let value : Fin k × Fin k → ℂ := fun p => wilsonBraidingPhase k p.1 p.2
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let Witten := wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model (fun p _ => value p) H
    (Integrable (fun x => Witten.wilsonObservable (a, b) x * Witten.model.weight x)
        Witten.model.μ
      ∧ ‖Witten.wilsonIntegral (a, b)‖ ≤
        ‖wilsonBraidingPhase k a b‖ * Witten.partitionFunction)
      ∧ braidC1 s * braidC2 s * braidC1 s = braidC2 s * braidC1 s * braidC2 s
      ∧ wilsonBraidingPhase k a b =
        (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b)
      ∧ trefoilCycle_after_5_over_6 J1 = 1
      ∧ trefoilCycle_after_5_over_6 J5 = -1
      ∧ (∫ x : ℝ,
          deltaEpsC epsilon (Complex.exp (massShellContourAngle theta * Complex.I) * x) *
            Complex.exp (massShellContourAngle theta * Complex.I)) = 1 := by
  dsimp only
  refine ⟨complexActionFiniteMeasure_braidingPhaseWilson_supplies_witten_FK
      (model := dZeroDSixFiniteMeasureModel mu hbar v r tau hhbar hSI)
      k (a, b), ?_⟩
  rcases analyticContinuation_hopfWilsonBraiding_and_trefoilCycle
      s hs k hk a b with ⟨hYB, hVerlinde, hJ1, hJ5⟩
  exact ⟨hYB, hVerlinde, hJ1, hJ5,
    massShellContour_normalization theta epsilon hepsilon⟩

/-- **The Witten braiding integral is exactly the Verlinde matrix entry times the partition function.**

The previous theorem supplied existence and a norm bound.  Here the constant Wilson-braiding observable
and the zero real action of the D0--D6 Euclidean carrier allow the integral to be evaluated exactly. -/
@[zil_level bridge_theorem]
theorem dZeroDSix_braidingWilsonIntegral_eq_verlinde_mul_partition
    {Field : Type*} [MeasurableSpace Field]
    (mu : Measure Field) [IsFiniteMeasure mu]
    (hbar v r tau : ℝ) (hhbar : 0 < hbar)
    (hSI : 0 ≤ dZeroDSixOddEuclideanAction v r tau)
    (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    let model := dZeroDSixFiniteMeasureModel mu hbar v r tau hhbar hSI
    let value : Fin k × Fin k → ℂ := fun p => wilsonBraidingPhase k p.1 p.2
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let Witten := wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model (fun p _ => value p) H
    Witten.wilsonIntegral (a, b) =
      ((Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b)) *
        (Witten.partitionFunction : ℂ) := by
  dsimp only
  let model := dZeroDSixFiniteMeasureModel mu hbar v r tau hhbar hSI
  let value : Fin k × Fin k → ℂ := fun p => wilsonBraidingPhase k p.1 p.2
  let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
  let Witten := wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
    model (fun p _ => value p) H
  have hRe : ∀ x : Field, model.actionRe x = 0 := fun _ => rfl
  have hWeightIntegral :
      (∫ x : Field, model.weight x ∂model.μ) = (model.partitionFunction : ℂ) := by
    calc
      (∫ x : Field, model.weight x ∂model.μ) =
          ∫ x : Field, (model.damping x : ℂ) ∂model.μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          model.weight_eq_damping_of_actionRe_zero hRe x
      _ = (model.partitionFunction : ℂ) := by
        rw [MeasurePathIntegralModel.partitionFunction, integral_complex_ofReal]
  change Witten.wilsonIntegral (a, b) =
    ((Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b)) *
      (Witten.partitionFunction : ℂ)
  rw [Witten.wilsonIntegral_eq_integral]
  change (∫ x : Field, wilsonBraidingPhase k a b * model.weight x ∂model.μ) = _
  rw [integral_const_mul, hWeightIntegral,
    analyticContinuation_wilsonBraiding_eq_S k hk a b]
  rfl

/- ZIL-BEGIN -/

zil attach dZeroDSix_hodge_gradients_orthogonal where
  formalizes @ "claim:d0-d6-hodge-duality-quarter-turn-makes-the-transverse-rr-gradients-orthogonal",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equation-1-5",
  caveat @ "claim:component-level-transverse-hodge-reduction-not-a-ten-dimensional-differential-form-construction"

zil attach dZeroDSix_hodge_gradients_equal_norm where
  formalizes @ "claim:d0-d6-hodge-duality-preserves-the-transverse-gradient-norm",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equation-1-5",
  caveat @ "claim:local-component-identity-not-a-global-d6-rr-background-existence-theorem"

zil attach dZeroDSix_chargeNormalizedPotential_eq where
  formalizes @ "claim:d0-d6-charge-quantization-derives-the-one-half-lorentz-potential-coefficient",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equations-1-5-through-1-7",
  requires @ "claim:d-brane-rr-charge-product-mu0-mu6-equals-two-pi",
  caveat @ "claim:exact-wess-zumino-coefficient-reduction-in-natural-string-units-not-a-calibration-of-brane-charges"

zil attach dZeroDSixLorentzPotential_eq_force_component where
  formalizes @ "claim:d0-d6-odd-potential-is-a-concrete-component-of-the-existing-lorentz-force-carrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzForceNum",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equations-1-6-and-1-7",
  caveat @ "claim:four-component-transverse-embedding-not-the-complete-ten-dimensional-d-brane-field-strength"

zil attach dZeroDSixLorentzPotential_hasDerivAt where
  formalizes @ "claim:d0-d6-velocity-linear-one-over-r-potential-derives-an-inverse-square-radial-force",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equation-1-7",
  caveat @ "claim:radial-derivative-of-the-protected-potential-not-a-full-d0-worldline-existence-or-stability-result"

zil attach dZeroDSix_matrix_velocity_gaussian_identity where
  formalizes @ "claim:matrix-theory-schwinger-gaussian-time-integral-restores-exactly-the-inverse-velocity-factor",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equation-3-12",
  supported_by @ "lean:integral_gaussian",
  caveat @ "claim:proved-gaussian-step-not-a-construction-of-the-full-matrix-theory-functional-determinant"

zil attach dZeroDSix_probe_string_matrix_lorentz_closure where
  formalizes @ "claim:d0-d6-probe-rr-odd-string-and-matrix-presentations-share-the-protected-lorentz-coefficient",
  supported_by @ "paper:billo-di-vecchia-et-al-1998-equations-1-7-2-24-and-3-13",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzForceNum",
  requires @ "claim:the-boundary-state-gso-computation-supplies-the-rr-odd-potential-of-equation-2-24",
  requires @ "claim:the-chiral-projector-determinant-reduction-supplies-the-schwinger-integrand-of-equation-3-11",
  caveat @ "claim:coefficient-level-cross-presentation-consistency-theorem-not-an-independent-derivation-of-string-matrix-duality"

zil attach dZeroDSixNagaoNielsenWeight_norm where
  formalizes @ "claim:d0-d6-odd-euclidean-action-has-the-common-nagao-nielsen-entropy-damping-modulus",
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel_norm_is_damping",
  requires @ "claim:the-d0-d6-lorentz-potential-is-euclidean-continued-as-si-equals-minus-time-times-v-odd",
  caveat @ "claim:explicit-euclidean-continuation-carrier-not-a-derivation-that-the-lorentzian-odd-potential-is-an-imaginary-action"

zil attach dZeroDSixNagaoNielsenWeight_norm_antitone_time where
  formalizes @ "claim:d0-d6-euclidean-odd-complex-action-weight-is-antitone-in-elapsed-entropic-time",
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel_norm_is_damping",
  requires @ "claim:forward-relative-velocity-positive-separation-and-positive-hbar-select-the-nonnegative-damping-sector",
  caveat @ "claim:monotone-amplitude-damping-for-the-explicit-euclidean-sector-not-a-complete-d0-d6-open-system-dynamics"

zil attach iibOvv_dZeroDSix_entropicClock_chain where
  formalizes @ "claim:ovv-type-iib-matrix-weight-d0-d6-entropic-action-and-compton-zitterbewegung-clock-share-one-complex-action-carrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge.iib_ovv_entropicTime_compton_zitterbewegung_chain",
  requires @ "claim:ikkt-bosonic-action-matches-the-ovv-flux-imaginary-action",
  requires @ "claim:ovv-imaginary-action-is-calibrated-to-the-d0-d6-euclidean-odd-action",
  requires @ "claim:the-same-imaginary-action-is-calibrated-to-rest-energy-times-proper-time",
  caveat @ "claim:conditional-shared-kernel-and-clock-theorem-not-a-derivation-of-string-matrix-duality-or-particle-mass-from-compactification"

zil attach iibOvv_dZeroDSix_rapidity_chain where
  formalizes @ "claim:d0-d6-ovv-ikkt-shared-weight-has-log-k-entropic-phase-and-positive-rapidity-tanh-modulus",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge.ovvEntropicPhase_eq_logSchmidtNumber",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge.norm_fluxInsertion_eq_tanh_of_rapidityCalibration",
  requires @ "claim:the-d0-d6-euclidean-odd-action-is-calibrated-to-hbar-log-of-the-schmidt-number",
  caveat @ "claim:conditional-rapidity-parametrization-not-a-derivation-of-the-d0-d6-trajectory-from-ikkt-dynamics"

zil attach dZeroDSix_wittenVerlindeTrefoil_contour_chain where
  formalizes @ "claim:d0-d6-complex-action-carrier-supports-witten-wilson-braiding-verlinde-s-matrix-trefoil-stokes-and-normalized-nagao-nielsen-contour-data",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_braidingPhaseWilson_supplies_witten_FK",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.analyticContinuation_hopfWilsonBraiding_and_trefoilCycle",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContour_normalization",
  caveat @ "claim:topological-observables-on-a-shared-finite-measure-complex-action-carrier-not-a-physical-identification-of-d0-d6-scattering-with-a-trefoil-knot",
  caveat @ "claim:finite-reference-measure-instantiation-not-the-full-cs-or-d-brane-continuum-functional-measure"

zil attach dZeroDSix_braidingWilsonIntegral_eq_verlinde_mul_partition where
  formalizes @ "claim:on-the-d0-d6-euclidean-carrier-the-witten-braiding-integral-is-exactly-the-conjugated-verlinde-s-entry-times-the-partition-function",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.analyticContinuation_wilsonBraiding_eq_S",
  supported_by @ "lean:Physlib.QFT.PathIntegral.MeasurePathIntegralModel.weight_eq_damping_of_actionRe_zero",
  caveat @ "claim:exact-constant-observable-evaluation-on-the-finite-measure-carrier-not-a-computation-of-the-full-interacting-cs-continuum-measure"

zil_file_contract physlib.dZeroDSixLorentzForce where
  promises "The equation-level D0-D6 Lorentz-force core of Billo et al.: transverse Hodge geometry, the half coefficient derived from RR charge normalization, a concrete existing-Lorentz-carrier realization, radial/time-reversal behavior, and the proved Matrix-theory Schwinger Gaussian identity assembling the protected probe/string/Matrix coefficient match. Its explicit positive Euclidean continuation is evaluated by the common Nagao-Nielsen kernel. Under separate visible OVV/IKKT action and Compton-clock calibrations that kernel is the Type-IIB matrix weight and carries the Compton and half-Zitterbewegung phases. A finite-measure version supports the rigorous Witten Wilson observable, its Verlinde S-matrix value, the trefoil Stokes coefficients, and normalized permitted contour."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.lorentzForceNum",
    "lean:integral_gaussian",
    "claim:d-brane-rr-charge-product-mu0-mu6-equals-two-pi",
    "paper:billo-di-vecchia-et-al-1998-equation-2-24",
    "paper:billo-di-vecchia-et-al-1998-equation-3-11",
    "lean:Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge.iib_ovv_entropicTime_compton_zitterbewegung_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_braidingPhaseWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.analyticContinuation_hopfWilsonBraiding_and_trefoilCycle",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContour_normalization"
  ]
  forbids_substitutes [
    "claiming the component Hodge relations construct the full ten-dimensional D6 supergravity solution",
    "claiming the algebraic half coefficient derives D-brane charge quantization",
    "relabeling the supplied R-R odd-spin boundary-state result as a Lean derivation of the GSO amplitude",
    "relabeling the Gaussian Schwinger identity as a construction of the Matrix-theory fermionic determinant",
    "claiming coefficient agreement alone proves the complete nonperturbative equivalence of string and Matrix theory",
    "identifying the paper's protected odd potential with the even NS-NS/R-R Coulomb interaction",
    "claiming the conditional OVV and D0-D6 action match derives string-Matrix duality",
    "identifying a shared path-integral carrier with a physical equivalence between D0-D6 scattering and the trefoil",
    "calling the finite reference-measure realization the full Chern-Simons or D-brane continuum functional measure"
  ]
  witnessed_by [
    dZeroDSix_hodge_gradients_orthogonal,
    dZeroDSix_hodge_gradients_equal_norm,
    dZeroDSix_chargeNormalizedPotential_eq,
    dZeroDSixLorentzPotential_eq_force_component,
    dZeroDSixLorentzPotential_timeReversal,
    dZeroDSixLorentzPotential_hasDerivAt,
    dZeroDSix_radius_mul_potential,
    dZeroDSix_matrix_velocity_gaussian_identity,
    dZeroDSix_probe_string_matrix_lorentz_closure,
    dZeroDSixOddEuclideanAction_eq_neg_time_mul_potential,
    dZeroDSixOddEuclideanAction_nonneg,
    dZeroDSixOddEuclideanAction_monotone_time,
    dZeroDSixNagaoNielsenWeight_norm,
    dZeroDSixNagaoNielsenWeight_norm_antitone_time,
    iibOvv_dZeroDSix_entropicClock_chain,
    iibOvv_dZeroDSix_rapidity_chain,
    dZeroDSix_wittenVerlindeTrefoil_contour_chain,
    dZeroDSix_braidingWilsonIntegral_eq_verlinde_mul_partition
  ]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DZeroDSixLorentzForce

end
