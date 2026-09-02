/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
meta import Zil

/-!
# Synthesis of the Caputa–Takayanagi AdS/CFT Liouville-complexity arc

This joins the four modules of the Liouville path-integral-complexity arc into their common
statement:

* `LiouvilleComplexityHolographicSpine` — the complexity `S_L = (c/24π)∫…`, its vacuum value
  `(c/6)(1/ε−1)`, and the central-charge spine (complexity coefficient = RT entropy);
* `LiouvilleHyperbolicAdSSlice` — the optimized metric is the hyperbolic AdS slice, Weyl factor
  `adSPoincareFactor = e^{2φ}`;
* `ConformalWeylCurvatureLiouville` — the Weyl-curvature transform `K = −e^{-2φ}φ''`, and the
  Liouville equation of motion `φ'' = μe^{2φ}` ⟺ constant negative curvature (the minimality step);
* `LiouvilleComplexityElectrograviticResidual` — the shared boundary central charge.

* `adSPoincareSlice_liouville_derived_curvature` — the concrete link: the AdS Poincaré Weyl factor
  (`adSPoincareFactor 1 z`, `LiouvilleHyperbolicAdSSlice`) is `e^{2φ}` with the vacuum Liouville
  field `φ = −log z`, that field solves the Liouville EOM, and its Gauss curvature is *derived* to
  be `−1` — upgrading the earlier *asserted* hyperbolic slice to one derived from the minimality.
* `liouville_arc_synthesis` — the three-module statement: minimality (EOM ⟺ constant curvature),
  the AdS-slice Weyl factor `e^{2φ}`, and the vacuum complexity = Ryu–Takayanagi entropy.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal

/-- **The AdS Poincaré slice's constant curvature is derived from the Liouville minimality.**  The
Poincaré Weyl factor `adSPoincareFactor 1 z = (1/z)²` (`LiouvilleHyperbolicAdSSlice`) is `e^{2φ}` with
the vacuum Liouville field `φ = −log z`; that field solves the Liouville equation of motion; and its
Gauss curvature is *derived* (`ConformalWeylCurvatureLiouville`) to be the constant `−1` — the
hyperbolic AdS slice, now obtained from the minimality rather than asserted. -/
@[zil_level bridge_theorem]
theorem adSPoincareSlice_liouville_derived_curvature (z : ℝ) (hz : 0 < z) :
    adSPoincareFactor 1 z = Real.exp (2 * (fun s => -Real.log s) z)
      ∧ deriv (deriv (fun s => -Real.log s)) z = 1 * Real.exp (2 * (fun s => -Real.log s) z)
      ∧ conformalGaussCurvature (fun s => -Real.log s) z = -1 := by
  refine ⟨?_, poincareVacuum_solves_liouville z hz, poincareVacuum_gaussCurvature z hz⟩
  show adSPoincareFactor 1 z = Real.exp (2 * (-Real.log z))
  rw [adSPoincareFactor_eq_exp_two_liouvilleField 1 z (one_div_pos.mpr hz), one_div, Real.log_inv]

/-- **The three-module synthesis of the Liouville-complexity arc.**  For the optimized metric:
(i) the minimality — the Liouville equation of motion `φ'' = μe^{2φ}` is equivalent to constant
negative Gauss curvature `−μ` (`ConformalWeylCurvatureLiouville`); (ii) the AdS-slice Weyl factor is
`e^{2φ}`, `log(e^{2φ}) = 2φ = 2 log(L/w)` (`LiouvilleHyperbolicAdSSlice`); and (iii) at the
Brown–Henneaux central charge the vacuum path-integral complexity equals the Ryu–Takayanagi entropy
of the AdS radius (`LiouvilleComplexityHolographicSpine`). -/
@[zil_level bridge_theorem]
theorem liouville_arc_synthesis (φ : ℝ → ℝ) (μ z L w R G ε : ℝ) (hG : G ≠ 0) :
    (deriv (deriv φ) z = μ * Real.exp (2 * φ z) ↔ conformalGaussCurvature φ z = -μ)
      ∧ Real.log (adSPoincareFactor L w) = 2 * Real.log (L / w)
      ∧ vacuumLiouvilleComplexity (brownHenneaux R G) ε = rtAreaEntropy R G * (1 / ε - 1) :=
  ⟨liouville_eom_iff_constant_curvature φ μ z,
   log_adSPoincareFactor_eq_two_liouvilleField L w,
   vacuumLiouvilleComplexity_brownHenneaux R G ε hG⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis

zil attach adSPoincareSlice_liouville_derived_curvature where
  formalizes @ "claim:the-ads-poincare-slice-weyl-factor-is-e-to-the-two-phi-with-the-vacuum-liouville-field-minus-log-z-which-solves-the-liouville-equation-of-motion-and-whose-gauss-curvature-is-derived-to-be-minus-one-upgrading-the-asserted-hyperbolic-slice-to-one-derived-from-the-minimality",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_gaussCurvature"

zil attach liouville_arc_synthesis where
  formalizes @ "claim:the-three-module-synthesis-of-the-liouville-complexity-arc-the-minimality-equation-of-motion-equivalent-to-constant-negative-curvature-the-ads-slice-weyl-factor-e-to-the-two-phi-and-the-vacuum-complexity-equal-to-the-ryu-takayanagi-entropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.liouville_eom_iff_constant_curvature",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine.vacuumLiouvilleComplexity_brownHenneaux"

zil_file_contract physlib.liouvilleAdSArcSynthesis where
  promises "Joining the four modules of the Caputa-Takayanagi Liouville path-integral-complexity arc into their common statement. The AdS Poincare slice Weyl factor is e to the two phi with the vacuum Liouville field minus log z, that field solves the Liouville equation of motion, and its Gauss curvature is derived to be constant minus one, upgrading the earlier asserted hyperbolic slice to one derived from the minimality. The three-module synthesis records the minimality, the Liouville equation of motion equivalent to constant negative curvature, together with the AdS-slice Weyl factor e to the two phi and the vacuum path-integral complexity equal to the Ryu-Takayanagi entropy of the AdS radius at the Brown-Henneaux central charge."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalGaussCurvature",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal.adSPoincareFactor",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine.vacuumLiouvilleComplexity"
  ]
  forbids_substitutes [
    "reading the synthesis as a single derivation rather than a linking of the four arc modules",
    "claiming the path-integral optimization is derived beyond the closed minimality equation-of-motion step"
  ]
  witnessed_by [
    adSPoincareSlice_liouville_derived_curvature,
    liouville_arc_synthesis
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.liouvilleAdSArcSynthesis
