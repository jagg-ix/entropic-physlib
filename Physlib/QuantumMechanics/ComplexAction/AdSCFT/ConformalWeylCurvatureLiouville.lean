/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
meta import Zil

/-!
# The 2D Weyl-curvature transform and the Liouville equation of motion

For a 2D metric conformal to the flat one, `ds² = e^{2φ}(dx² + dz²)` with `φ = φ(z)`, the Gauss
curvature is derived from the Levi-Civita connection exactly as in
`EntropicTime.AlphaOrderGaussianCurvature`: the Christoffel symbol is `Γ = φ'` (the Liouville-field
gradient), the surviving Riemann component is `R^x{}_{zxz} = −φ''`, and the Gauss curvature is

`K = R^x{}_{zxz} / g_{zz} = −e^{-2φ} φ''`  (`conformalGaussCurvature_eq`),

the Caputa–Takayanagi / eq. 6.6 Weyl-curvature transform (flat reference).  Minimizing the Liouville
action gives its equation of motion `φ'' = μ e^{2φ}` (their eq. 3.12/3.19), which is *equivalent* to
constant negative Gauss curvature `K = −μ` — the hyperbolic AdS time slice:

`φ'' = μ e^{2φ}  ↔  K = −μ`  (`liouville_eom_iff_constant_curvature`).

So the optimized (minimal-complexity) metric has constant negative curvature — this closes the
minimality/EOM step of the path-integral optimization.  The vacuum Liouville field `φ = −log z`
solves the EOM with `μ = 1` and gives `K = −1` (`poincareVacuum_solves_liouville`,
`poincareVacuum_gaussCurvature`), the constant-negative-curvature AdS slice of
`LiouvilleHyperbolicAdSSlice`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville

/-- **The Christoffel symbol of the conformal metric** `Γ = ½ g^{zz} ∂_z g_{xx}` for
`g = e^{2φ}·δ`. -/
def christoffelConformal (φ : ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-(2 * φ z)) * deriv (fun s => Real.exp (2 * φ s)) z

/-- **The Christoffel symbol is the Liouville-field gradient** `Γ = φ'`, derived from the conformal
metric `e^{2φ}·δ` by the chain rule `∂_z e^{2φ} = 2φ' e^{2φ}`. -/
@[zil_level bridge_theorem]
theorem christoffelConformal_eq (φ : ℝ → ℝ) (z dφ : ℝ) (hφ : HasDerivAt φ dφ z) :
    christoffelConformal φ z = dφ := by
  unfold christoffelConformal
  have hexp : HasDerivAt (fun s => Real.exp (2 * φ s)) (Real.exp (2 * φ z) * (2 * dφ)) z :=
    (hφ.const_mul 2).exp
  rw [hexp.deriv, Real.exp_neg]
  field_simp

/-- **The surviving Riemann component** `R^x{}_{zxz} = −∂_z Γ + Γ² − Γ²` for the conformal metric —
the `μ`-independent form (as in `AlphaOrderGaussianCurvature`), equal to `−φ''`. -/
def conformalRiemann (φ : ℝ → ℝ) (z : ℝ) : ℝ :=
  -deriv (fun s => deriv φ s) z + deriv φ z * deriv φ z - deriv φ z * deriv φ z

/-- `R^x{}_{zxz} = −φ''`. -/
@[zil_level physical_theorem]
theorem conformalRiemann_eq (φ : ℝ → ℝ) (z : ℝ) :
    conformalRiemann φ z = -deriv (deriv φ) z := by
  unfold conformalRiemann
  ring

/-- **The Gauss curvature of the conformal metric** `K = R^x{}_{zxz}/g_{zz}`. -/
def conformalGaussCurvature (φ : ℝ → ℝ) (z : ℝ) : ℝ :=
  conformalRiemann φ z / Real.exp (2 * φ z)

/-- **The 2D Weyl-curvature transform** `K = −e^{-2φ} φ''` (Caputa–Takayanagi eq. 6.6, flat
reference), derived from the conformal metric through its Levi-Civita connection. -/
@[zil_level bridge_theorem]
theorem conformalGaussCurvature_eq (φ : ℝ → ℝ) (z : ℝ) :
    conformalGaussCurvature φ z = -Real.exp (-(2 * φ z)) * deriv (deriv φ) z := by
  unfold conformalGaussCurvature
  rw [conformalRiemann_eq, Real.exp_neg]
  ring

/-- **The Liouville equation of motion is equivalent to constant negative curvature.**  The
minimal-complexity Liouville field `φ'' = μ e^{2φ}` (Caputa–Takayanagi eq. 3.12/3.19) holds *iff*
the conformal metric has constant Gauss curvature `K = −μ` — so the optimized metric is the
hyperbolic (constant-negative-curvature) AdS slice.  This closes the minimality/EOM step. -/
@[zil_level bridge_theorem]
theorem liouville_eom_iff_constant_curvature (φ : ℝ → ℝ) (μ z : ℝ) :
    deriv (deriv φ) z = μ * Real.exp (2 * φ z) ↔ conformalGaussCurvature φ z = -μ := by
  have hE : Real.exp (2 * φ z) ≠ 0 := Real.exp_ne_zero _
  rw [conformalGaussCurvature_eq, Real.exp_neg]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linarith [h]

/-- **The vacuum Liouville field solves the equation of motion.**  The Caputa–Takayanagi vacuum
`φ = −log z` (their `φ = −log z + const`) satisfies `φ'' = e^{2φ}` (`μ = 1`), since
`φ'' = 1/z²` and `e^{2φ} = 1/z²`. -/
@[zil_level physical_theorem]
theorem poincareVacuum_solves_liouville (z : ℝ) (hz : 0 < z) :
    deriv (deriv (fun s => -Real.log s)) z = 1 * Real.exp (2 * (fun s => -Real.log s) z) := by
  have hz' : z ≠ 0 := hz.ne'
  show deriv (deriv (fun s => -Real.log s)) z = 1 * Real.exp (2 * (-Real.log z))
  have hderiv1 : deriv (fun s => -Real.log s) = fun s => -s⁻¹ := by
    funext s; simp [Real.deriv_log]
  have h2 : deriv (fun s => -s⁻¹) z = (z ^ 2)⁻¹ := by
    have h0 := (hasDerivAt_inv hz').neg
    rw [neg_neg] at h0
    exact h0.deriv
  rw [hderiv1, h2, one_mul,
    show (2 : ℝ) * (-Real.log z) = -(2 * Real.log z) from by ring, Real.exp_neg,
    show (2 : ℝ) * Real.log z = Real.log (z ^ 2) from by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- **The vacuum Liouville field gives constant negative curvature `K = −1`** — the hyperbolic AdS
time slice of `LiouvilleHyperbolicAdSSlice`. -/
@[zil_level bridge_theorem]
theorem poincareVacuum_gaussCurvature (z : ℝ) (hz : 0 < z) :
    conformalGaussCurvature (fun s => -Real.log s) z = -1 :=
  (liouville_eom_iff_constant_curvature (fun s => -Real.log s) 1 z).mp
    (poincareVacuum_solves_liouville z hz)

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville

zil attach christoffelConformal_eq where
  supported_by @ "lean:HasVarAdjDerivAt.const_mul",
  formalizes @ "claim:the-christoffel-symbol-of-the-two-dimensional-conformal-metric-e-to-the-two-phi-times-flat-is-the-liouville-field-gradient-phi-prime-derived-by-the-chain-rule"

zil attach conformalGaussCurvature_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalRiemann_eq",
  formalizes @ "claim:the-two-dimensional-weyl-curvature-transform-the-gauss-curvature-of-the-conformal-metric-is-minus-e-to-the-minus-two-phi-times-phi-double-prime-derived-from-the-levi-civita-connection"

zil attach liouville_eom_iff_constant_curvature where
  supported_by @ "lean:conformalGaussCurvature_eq",
  formalizes @ "claim:the-liouville-equation-of-motion-phi-double-prime-equals-mu-e-to-the-two-phi-is-equivalent-to-constant-negative-gauss-curvature-minus-mu-so-the-minimal-complexity-optimized-metric-is-the-hyperbolic-ads-slice-closing-the-minimality-step"

zil attach poincareVacuum_gaussCurvature where
  formalizes @ "claim:the-vacuum-liouville-field-minus-log-z-gives-constant-negative-curvature-minus-one-the-hyperbolic-ads-time-slice",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_solves_liouville"

zil_file_contract physlib.conformalWeylCurvatureLiouville where
  promises "The two-dimensional Weyl-curvature transform and the Liouville equation of motion, closing the minimality step of the Caputa-Takayanagi path-integral optimization. For the conformal metric e to the two phi times flat with phi a function of z, the Christoffel symbol is derived from the metric by the chain rule to be the Liouville-field gradient phi prime, the surviving Riemann component is minus phi double prime, and the Gauss curvature is minus e to the minus two phi times phi double prime, the eq 6.6 Weyl-curvature transform. The Liouville equation of motion phi double prime equals mu e to the two phi is equivalent to constant negative Gauss curvature minus mu, so the minimal-complexity optimized metric has constant negative curvature - the hyperbolic AdS time slice. The vacuum Liouville field minus log z solves the equation of motion and gives constant curvature minus one."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalGaussCurvature",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.christoffelConformal"
  ]
  forbids_substitutes [
    "reading the flat-reference Weyl transform as the general curved-reference transform which carries an extra R g phi term",
    "dropping the differentiability hypothesis needed for the Christoffel chain-rule derivation"
  ]
  witnessed_by [
    christoffelConformal_eq,
    conformalRiemann_eq,
    conformalGaussCurvature_eq,
    liouville_eom_iff_constant_curvature,
    poincareVacuum_solves_liouville,
    poincareVacuum_gaussCurvature
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.conformalWeylCurvatureLiouville
