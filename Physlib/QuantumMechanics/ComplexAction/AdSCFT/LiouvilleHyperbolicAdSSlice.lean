/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
meta import Zil

/-!
# The Liouville-optimized metric is the hyperbolic AdS slice

Caputa–Takayanagi (JHEP 11(2017)097) optimize a 2D CFT path-integral over the Weyl ansatz
`ds² = e^{2φ}(dz² + dx²)` (their eq. 2.5); the optimized metric is hyperbolic — constant negative
curvature — and coincides with a time slice of AdS.  For the Poincaré-AdS slice the Weyl factor is
`e^{2φ} = (L/z)²`, i.e. the Liouville field is `φ = log(L/z)` (their `φ = −log z + const`).

The repo has the Poincaré Weyl factor `adSPoincareFactor L z = (L/z)²`
(`CausalDiamond.AdSPoincareConformal`) and a proven constant-negative-curvature hyperbolic 2D
metric `frMetric` with `scalarCurvature = −1` (`EntropicTime.FisherRaoGaussianLeviCivita`).  This
module connects the Weyl factor to the Liouville field and bundles the hyperbolic-slice geometry.

* `adSPoincareFactor_eq_exp_two_liouvilleField` — the Poincaré Weyl factor is `e^{2φ}` with the
  Liouville field `φ = log(L/z)`.
* `log_adSPoincareFactor_eq_two_liouvilleField` — equivalently `log(e^{2φ}) = 2φ`.
* `liouville_optimized_hyperbolic_slice` — the AdS-slice Weyl factor is `e^{2φ}` and the hyperbolic
  slice has constant negative scalar curvature `−1`: the geometry of the Caputa–Takayanagi
  path-integral optimization.

Honest scope: this identifies the optimized metric as the hyperbolic AdS slice and records its
Weyl factor and constant curvature.  It does *not* prove that this metric *minimizes* the Liouville
action (the optimization/minimality step needs the position-dependent Weyl-curvature transform
`R̃ = e^{-2φ}(R − 2Δφ)`, which the repo does not have — the genuine open gap).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

/-- **The Poincaré-AdS Weyl factor is `e^{2φ}`** with the Liouville field `φ = log(L/z)`: the
Caputa–Takayanagi optimization ansatz `ds² = e^{2φ}(dz²+dx²)` at the AdS slice. -/
@[zil_level bridge_theorem]
theorem adSPoincareFactor_eq_exp_two_liouvilleField (L z : ℝ) (h : 0 < L / z) :
    adSPoincareFactor L z = Real.exp (2 * Real.log (L / z)) := by
  unfold adSPoincareFactor
  rw [show (2 : ℝ) * Real.log (L / z) = Real.log ((L / z) ^ 2) from by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/-- **The Liouville field is half the log of the Weyl factor**, `log(e^{2φ}) = 2φ = 2 log(L/z)`. -/
@[zil_level physical_theorem]
theorem log_adSPoincareFactor_eq_two_liouvilleField (L z : ℝ) :
    Real.log (adSPoincareFactor L z) = 2 * Real.log (L / z) := by
  unfold adSPoincareFactor
  rw [Real.log_pow]; push_cast; ring

/-- **The Liouville-optimized metric is the hyperbolic AdS slice.**  Its Weyl factor is
`e^{2φ}` (the Liouville field `φ = log(L/z)`), and the hyperbolic slice has constant negative
scalar curvature `−1` — the constant-negative-curvature (AdS) geometry produced by the
Caputa–Takayanagi path-integral optimization. -/
@[zil_level bridge_theorem]
theorem liouville_optimized_hyperbolic_slice (L z σ : ℝ) (hσ : σ ≠ 0) :
    Real.log (adSPoincareFactor L z) = 2 * Real.log (L / z)
      ∧ scalarCurvature (frMetricInv σ) (frRiemann σ) = -1 :=
  ⟨log_adSPoincareFactor_eq_two_liouvilleField L z, frScalarCurvature σ hσ⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice

zil attach adSPoincareFactor_eq_exp_two_liouvilleField where
  formalizes @ "claim:the-poincare-ads-weyl-factor-l-over-z-squared-is-e-to-the-two-phi-with-the-liouville-field-phi-equal-log-l-over-z-the-caputa-takayanagi-optimization-ansatz-at-the-ads-slice"

zil attach liouville_optimized_hyperbolic_slice where
  formalizes @ "claim:the-liouville-optimized-metric-is-the-hyperbolic-ads-slice-its-weyl-factor-is-e-to-the-two-phi-and-the-hyperbolic-slice-has-constant-negative-scalar-curvature-minus-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frScalarCurvature"

zil_file_contract physlib.liouvilleHyperbolicAdSSlice where
  promises "Identifying the Caputa-Takayanagi path-integral-optimized metric as the hyperbolic AdS slice. The optimization ansatz is the Weyl-rescaled metric e to the two phi times flat, and at the Poincare-AdS slice the Weyl factor is L over z squared, so the Liouville field is phi equal log L over z: the Poincare Weyl factor is e to the two phi, and the log of the Weyl factor is two phi. The optimized metric is the hyperbolic AdS slice, whose Fisher-Rao presentation has constant negative scalar curvature minus one - the constant-negative-curvature AdS geometry produced by the path-integral optimization. This identifies the optimized geometry and records its Weyl factor and constant curvature, but does not prove that this metric minimizes the Liouville action, which needs the position-dependent Weyl-curvature transform R tilde equals e to the minus two phi times R minus two Laplacian phi, a genuine open gap."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSPoincareConformal.adSPoincareFactor",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frScalarCurvature"
  ]
  forbids_substitutes [
    "claiming the Liouville-action minimality is proved rather than only the identification of the optimized geometry",
    "omitting the position-dependent Weyl-curvature transform needed for the optimization step"
  ]
  witnessed_by [
    adSPoincareFactor_eq_exp_two_liouvilleField,
    log_adSPoincareFactor_eq_two_liouvilleField,
    liouville_optimized_hyperbolic_slice
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.liouvilleHyperbolicAdSSlice
