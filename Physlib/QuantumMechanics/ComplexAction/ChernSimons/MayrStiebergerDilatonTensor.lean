/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.DifferentialForms
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Module
meta import Zil

/-!
# Dilaton, antisymmetric tensor, and one-loop gauge fields

This module formalizes the reusable mathematical core of Mayr--Stieberger,
*Dilaton, antisymmetric tensor and gauge fields in string effective theories at
the one-loop level* (Nuclear Physics B 412 (1994), 502--522).

The results are deliberately separated by epistemic status:

* `genusWeight_succ` is the exact genus recursion following from the constant
  dilaton coupling to the world-sheet Euler characteristic;
* `dilaton_threshold_scale_shift` is the paper's exact change from Planck to
  string cutoff once `M_string = M_Planck / sqrt (Re S)` is fixed;
* `greenSchwarzTensorFieldStrength_gauge_invariant` and
  `extDeriv_greenSchwarzTensorFieldStrength` use the repository's genuine
  differential forms, so the Green--Schwarz three-form and modified Bianchi
  identity work on finite- or infinite-dimensional normed model spaces;
* `oneLoop1PI_vanishes_iff_smatrix_is_external` isolates the subtraction made
  in the paper.  It does **not** claim that generic symmetry alone proves the
  string amplitude equals its external-leg contribution.

The four-form in the modified Bianchi identity is the differential-form
counterpart of the Pontryagin density already carried by
`ChernSimons.PontryaginAnomaly`; no second Pontryagin normalization is defined.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor

open ContinuousAlternatingMap
open Physlib.Mathematics.LovelockRund

/-! ## Constant dilaton and the genus expansion -/

/-- The constant-dilaton Euler coupling `2 (1 - genus) phi0` from the
world-sheet curvature term. -/
def genusEulerCoupling (phi0 : ℝ) (genus : ℕ) : ℝ :=
  2 * (1 - (genus : ℝ)) * phi0

/-- Euclidean path-integral weight of the constant-dilaton Euler term. -/
def genusWeight (phi0 : ℝ) (genus : ℕ) : ℝ :=
  Real.exp (-genusEulerCoupling phi0 genus)

/-- Increasing the genus by one multiplies the constant-dilaton weight by
`exp (2 phi0)`.  This is the exact loop-counting recursion behind the paper's
genus expansion. -/
theorem genusWeight_succ (phi0 : ℝ) (genus : ℕ) :
    genusWeight phi0 (genus + 1) = Real.exp (2 * phi0) * genusWeight phi0 genus := by
  rw [genusWeight, genusWeight, ← Real.exp_add]
  congr 1
  simp only [genusEulerCoupling, Nat.cast_add, Nat.cast_one]
  ring

/-! ## Physical-basis threshold scale -/

/-- The string cutoff in the paper's physical basis.  The positive real
parameter `dilaton` represents `Re S`. -/
def stringScale (MPlanck dilaton : ℝ) : ℝ :=
  MPlanck / √dilaton

/-- The dilaton term in the one-loop gauge threshold is precisely the change
of running cutoff from `MPlanck` to `stringScale MPlanck dilaton`:

`b log(MPlanck / mu) - (b/2) log(dilaton)
  = b log(Mstring / mu)`.

This is an exact scale identity conditional on the physical-basis relation
`Mstring = MPlanck / sqrt(dilaton)`; it is not an independent prediction of a
gauge coupling or of the dilaton vacuum expectation value. -/
theorem dilaton_threshold_scale_shift
    (b MPlanck mu dilaton : ℝ)
    (hM : MPlanck ≠ 0) (hmu : mu ≠ 0) (hS : 0 < dilaton) :
    b * Real.log (MPlanck / mu) - (b / 2) * Real.log dilaton =
      b * Real.log (stringScale MPlanck dilaton / mu) := by
  rw [Real.log_div hM hmu]
  rw [stringScale, Real.log_div (div_ne_zero hM (Real.sqrt_ne_zero'.mpr hS)) hmu]
  rw [Real.log_div hM (Real.sqrt_ne_zero'.mpr hS)]
  rw [Real.log_sqrt hS.le]
  ring

/-! ## Green--Schwarz antisymmetric tensor -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : WithTop ℕ∞}

/-- The Chern--Simons-modified antisymmetric-tensor field strength
`H = dB - k omega3`.  It is a genuine differential three-form on the model
space `E`. -/
def greenSchwarzTensorFieldStrength
    (B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ) :
    DifferentialForm ℝ E ℝ 3 :=
  extDeriv B + (-k) • omega3

/-- Compensated transformation of the antisymmetric two-form. -/
def greenSchwarzShiftB
    (B Lambda : DifferentialForm ℝ E ℝ 2) (k : ℝ) :
    DifferentialForm ℝ E ℝ 2 :=
  B + k • Lambda

/-- The matching transgression shift `omega3 -> omega3 + d Lambda`. -/
def greenSchwarzShiftCS
    (omega3 : DifferentialForm ℝ E ℝ 3)
    (Lambda : DifferentialForm ℝ E ℝ 2) :
    DifferentialForm ℝ E ℝ 3 :=
  omega3 + extDeriv Lambda

/-- The modified three-form is invariant under the compensated tensor and
Chern--Simons shifts.  This is the gauge mechanism behind the paper's
modified antisymmetric-tensor field strength. -/
theorem greenSchwarzTensorFieldStrength_gauge_invariant
    (B Lambda : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3) (k : ℝ)
    (hB : Differentiable ℝ B) (hLambda : Differentiable ℝ Lambda) :
    greenSchwarzTensorFieldStrength
        (greenSchwarzShiftB B Lambda k) (greenSchwarzShiftCS omega3 Lambda) k =
      greenSchwarzTensorFieldStrength B omega3 k := by
  funext x
  rw [show greenSchwarzTensorFieldStrength
      (greenSchwarzShiftB B Lambda k) (greenSchwarzShiftCS omega3 Lambda) k =
      extDeriv (B + k • Lambda) + (-k) • (omega3 + extDeriv Lambda) by rfl]
  rw [Pi.add_apply, extDeriv_add (hB x) (hLambda.const_smul k x), extDeriv_smul]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [show greenSchwarzTensorFieldStrength B omega3 k x =
      extDeriv B x + (-k) • omega3 x by rfl]
  module

/-- If `omega3` transgresses the Pontryagin four-form `P4`, then the
Green--Schwarz field strength obeys the modified Bianchi identity
`dH = -k P4`.

The proof reuses `extDeriv_extDeriv`; smoothness and differentiability are
visible hypotheses rather than hidden componentwise commutation assumptions.
-/
theorem extDeriv_greenSchwarzTensorFieldStrength
    (B : DifferentialForm ℝ E ℝ 2)
    (omega3 : DifferentialForm ℝ E ℝ 3)
    (P4 : DifferentialForm ℝ E ℝ 4) (k : ℝ)
    (hB : ContDiff ℝ r B) (hr : minSmoothness ℝ 2 ≤ r)
    (hdB : Differentiable ℝ (extDeriv B))
    (homega3 : Differentiable ℝ omega3)
    (htransgression : extDeriv omega3 = P4) :
    extDeriv (greenSchwarzTensorFieldStrength B omega3 k) = (-k) • P4 := by
  funext x
  rw [show greenSchwarzTensorFieldStrength B omega3 k =
      extDeriv B + (-k) • omega3 by rfl]
  rw [extDeriv_add (hdB x) (homega3.const_smul (-k) x), extDeriv_smul]
  rw [show extDeriv (extDeriv B) x = 0 by
    exact congrFun (extDeriv_extDeriv hB hr) x]
  rw [congrFun htransgression x]
  simp

/-! ## Honest one-loop 1PI subtraction -/

/-- For the paper's decomposition
`deltaS = deltaGamma_1PI + deltaZ * g_tree`, the one-loop 1PI vertex vanishes
iff the computed S-matrix correction is exhausted by external-leg
renormalization.  The string-amplitude equality is the paper-specific input;
this theorem formalizes exactly what follows from it. -/
theorem oneLoop1PI_vanishes_iff_smatrix_is_external
    (deltaGamma1PI deltaZ gTree : ℂ) :
    deltaGamma1PI + deltaZ * gTree = deltaZ * gTree ↔ deltaGamma1PI = 0 := by
  constructor
  · intro h
    exact add_eq_right.mp h
  · intro h
    simp [h]

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.genusWeight_succ where
  formalizes @ "claim:constant-dilaton-euler-coupling-multiplies-each-successive-string-genus-weight-by-exp-two-phi-zero",
  supported_by @ "paper:mayr-stieberger-1994-equation-2"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.dilaton_threshold_scale_shift where
  formalizes @ "claim:the-one-loop-dilaton-threshold-term-shifts-the-running-cutoff-from-planck-scale-to-string-scale",
  supported_by @ "paper:mayr-stieberger-1994-equations-29-31",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:conditional-on-the-physical-basis-relation-m-string-equals-m-planck-over-sqrt-re-s-not-an-independent-gauge-coupling-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.greenSchwarzTensorFieldStrength_gauge_invariant where
  formalizes @ "claim:the-chern-simons-modified-antisymmetric-tensor-field-strength-is-invariant-under-compensated-two-form-and-transgression-shifts",
  supported_by @ "paper:mayr-stieberger-1994-equation-32"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.extDeriv_greenSchwarzTensorFieldStrength where
  formalizes @ "claim:the-green-schwarz-three-form-obeys-a-pontryagin-sourced-modified-bianchi-identity",
  requires @ "claim:the-chern-simons-three-form-transgresses-the-pontryagin-four-form",
  supported_by @ "paper:mayr-stieberger-1994-equation-32",
  caveat @ "claim:the-transgression-identity-is-an-explicit-premise-while-d-squared-b-equals-zero-and-the-resulting-modified-bianchi-identity-are-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.oneLoop1PI_vanishes_iff_smatrix_is_external where
  formalizes @ "claim:the-one-loop-dilaton-or-antisymmetric-tensor-gauge-gauge-1pi-vertex-vanishes-exactly-when-the-string-s-matrix-correction-is-exhausted-by-external-leg-renormalization",
  supported_by @ "paper:mayr-stieberger-1994-equations-27-31-and-39-40",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-string-amplitude-equals-external-leg-contribution-is-the-paper-specific-computation-and-is-not-derived-from-generic-symmetry"

zil_file_contract physlib.mayrStiebergerDilatonTensor where
  promises "The reusable mathematical core of Mayr and Stieberger's one-loop string effective theory: exact constant-dilaton genus weighting; the Planck-to-string threshold-scale identity; a genuine continuum Green-Schwarz three-form with compensated gauge invariance and Pontryagin-sourced modified Bianchi identity; and an honest iff separating the paper's string-amplitude input from the vanishing 1PI conclusion."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.LovelockRund.DifferentialForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.chernSimonsPontryaginNormalization"]
  forbids_substitutes ["a claim that generic symmetry alone proves the paper-specific one-loop string amplitude",
    "an independent prediction of the dilaton vacuum value or gauge coupling from the threshold-scale identity",
    "a coordinate-component replacement for the repository's continuum exterior derivative"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.genusWeight_succ,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.dilaton_threshold_scale_shift,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.greenSchwarzTensorFieldStrength_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.extDeriv_greenSchwarzTensorFieldStrength,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor.oneLoop1PI_vanishes_iff_smatrix_is_external]

/- ZIL-END -/
