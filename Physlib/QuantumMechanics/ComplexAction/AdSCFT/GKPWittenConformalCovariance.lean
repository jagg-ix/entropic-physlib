/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
meta import Zil

/-!
# Full conformal covariance of the GKP–Witten correlator

`GKPWittenAdSCFTDictionary` established only **dilation** covariance of the bulk-to-boundary kernel and the
scaling of `cftTwoPoint`.  The dictionary's actual deliverable is that the boundary two-point function is
*conformally fixed* to `|x − y|^{−2Δ}` — which needs the full boundary conformal group
(translations, dilations, inversions/special-conformal), not scaling alone.  This module supplies the two
missing covariances and, with the existing dilation, exhibits the separated two-point function as
covariant under all three generators of the (1D boundary) conformal group.

* `cftTwoPointSep` — the separated correlator `⟨O(x)O(y)⟩ = |x − y|^{−2Δ}`.
* `bulkToBoundaryKernel_translation` / `cftTwoPointSep_translation` — **translation** invariance.
* `cftTwoPointSep_dilation` — **dilation** `⟨O(λx)O(λy)⟩ = λ^{−2Δ}⟨O(x)O(y)⟩`.
* `cftTwoPointSep_inversion` — **inversion / special-conformal** `⟨O(1/x)O(1/y)⟩ = (|x||y|)^{2Δ}⟨O(x)O(y)⟩`.

Honest scope: this fixes the two-point function's transformation law under the conformal generators (the
conformally-covariant form `|x−y|^{−2Δ}`); it is not a Witten-diagram integral evaluation or a derivation
of the AdS/CFT correspondence itself.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

/-- **The separated boundary two-point function** `⟨O(x)O(y)⟩ = |x − y|^{−2Δ}`. -/
def cftTwoPointSep (Δ x y : ℝ) : ℝ := |x - y| ^ (-2 * Δ)

/-- The separated correlator at `y = 0` is the repo's `cftTwoPoint`. -/
theorem cftTwoPointSep_eq_cftTwoPoint (Δ x : ℝ) : cftTwoPointSep Δ x 0 = cftTwoPoint Δ x := by
  unfold cftTwoPointSep cftTwoPoint
  rw [sub_zero]

/-- **Translation invariance of the bulk-to-boundary kernel** `K_Δ(z, x+a; x₀+a) = K_Δ(z, x; x₀)`. -/
@[zil_level physical_theorem]
theorem bulkToBoundaryKernel_translation (Δ z x x₀ a : ℝ) :
    bulkToBoundaryKernel Δ z (x + a) (x₀ + a) = bulkToBoundaryKernel Δ z x x₀ := by
  unfold bulkToBoundaryKernel
  rw [show x + a - (x₀ + a) = x - x₀ from by ring]

/-- **Translation invariance of the two-point function** `⟨O(x+a)O(y+a)⟩ = ⟨O(x)O(y)⟩`. -/
@[zil_level physical_theorem]
theorem cftTwoPointSep_translation (Δ x y a : ℝ) :
    cftTwoPointSep Δ (x + a) (y + a) = cftTwoPointSep Δ x y := by
  unfold cftTwoPointSep
  rw [show x + a - (y + a) = x - y from by ring]

/-- **Dilation covariance of the two-point function** `⟨O(λx)O(λy)⟩ = λ^{−2Δ}⟨O(x)O(y)⟩` (`λ > 0`). -/
@[zil_level physical_theorem]
theorem cftTwoPointSep_dilation (Δ x y l : ℝ) (hl : 0 < l) :
    cftTwoPointSep Δ (l * x) (l * y) = l ^ (-2 * Δ) * cftTwoPointSep Δ x y := by
  unfold cftTwoPointSep
  rw [show l * x - l * y = l * (x - y) from by ring, abs_mul, abs_of_pos hl,
    Real.mul_rpow hl.le (abs_nonneg _)]

/-- `|x⁻¹ − y⁻¹| = |x − y|/(|x|·|y|)` — the inversion contracts boundary separations. -/
theorem abs_inv_sub_inv (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    |x⁻¹ - y⁻¹| = |x - y| / (|x| * |y|) := by
  rw [inv_sub_inv hx hy, abs_div, abs_mul, abs_sub_comm y x]

/-- **Inversion (special-conformal) covariance of the two-point function**
`⟨O(1/x)O(1/y)⟩ = (|x|·|y|)^{2Δ}⟨O(x)O(y)⟩` (`x, y ≠ 0`) — the third conformal generator.  Together with
translation and dilation this exhibits `|x − y|^{−2Δ}` as the conformally-fixed correlator. -/
@[zil_level physical_theorem]
theorem cftTwoPointSep_inversion (Δ x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    cftTwoPointSep Δ x⁻¹ y⁻¹ = (|x| * |y|) ^ (2 * Δ) * cftTwoPointSep Δ x y := by
  have hB : (0 : ℝ) < |x| * |y| := mul_pos (abs_pos.mpr hx) (abs_pos.mpr hy)
  unfold cftTwoPointSep
  rw [abs_inv_sub_inv x y hx hy, Real.div_rpow (abs_nonneg _) hB.le,
    show (-2 * Δ : ℝ) = -(2 * Δ) from by ring, Real.rpow_neg hB.le (2 * Δ), div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance

zil attach bulkToBoundaryKernel_translation where
  formalizes @ "claim:the-gkp-witten-bulk-to-boundary-kernel-is-translation-invariant-in-the-boundary-coordinate"

zil attach cftTwoPointSep_dilation where
  formalizes @ "claim:the-gkp-witten-boundary-two-point-function-transforms-under-dilation-by-lambda-to-the-minus-two-delta-the-conformal-scaling"

zil attach cftTwoPointSep_inversion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.abs_inv_sub_inv",
  formalizes @ "claim:the-gkp-witten-boundary-two-point-function-transforms-under-inversion-special-conformal-by-the-product-of-the-absolute-values-to-the-two-delta-the-third-conformal-generator-fixing-the-correlator-form"

zil_file_contract physlib.gkpWittenConformalCovariance where
  promises "Full conformal covariance of the GKP-Witten boundary two-point function, supplying the translation and inversion covariances that the dictionary left only at the dilation level. The separated correlator is the absolute value of x minus y to the minus two delta. The bulk-to-boundary kernel and the two-point function are translation invariant in the boundary coordinate; the two-point function transforms under dilation by lambda to the minus two delta; and under inversion, the special-conformal generator, by the product of the absolute values of x and y to the two delta. Together with dilation, translation and inversion are the three generators of the one-dimensional boundary conformal group, so this exhibits the correlator absolute value of x minus y to the minus two delta as conformally fixed. Honest scope: this fixes the two-point function's transformation law under the conformal generators; it is not a Witten-diagram integral evaluation or a derivation of the AdS/CFT correspondence itself."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.bulkToBoundaryKernel",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.cftTwoPoint"
  ]
  forbids_substitutes [
    "reading the conformal transformation laws of the two-point function as a Witten-diagram integral evaluation or a derivation of the holographic correspondence"
  ]
  witnessed_by [
    bulkToBoundaryKernel_translation,
    cftTwoPointSep_translation,
    cftTwoPointSep_dilation,
    cftTwoPointSep_inversion
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gkpWittenConformalCovariance
