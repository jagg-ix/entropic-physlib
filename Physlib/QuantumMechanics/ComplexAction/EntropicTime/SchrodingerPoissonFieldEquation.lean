/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
public import Physlib.SpaceAndTime.Space.Translations
meta import Zil

/-!
# The Schrödinger–Poisson field equation: the continuum weak Poisson law

Composing the Newtonian convolution potential `φ_ρ = (1/‖·‖) ⋆ ρ`
(`NewtonianConvolutionPotential`) with the point-source weak Poisson equation
(`WeakNewtonPoisson`) gives the **continuum** weak Poisson law for a mass density `ρ`:

  `∫ φ_ρ(x)·Δη(x) dx = −4π ∫ ρ(y)·η(y) dy`

i.e. `−Δφ_ρ = 4πρ` weakly. The chain is: translate the origin pairing to
`∫ Δη(x)·‖x−y‖⁻¹ dx = −4π·η(y)` (`newtonKernel_weakPoisson_at`, via the repo's
`distTranslate` machinery and the proved fundamental solution), then apply Fubini
(`integral_integral_swap`) against `φ_ρ(x) = ∫ ρ(y)/‖x−y‖ dy`. This is the field equation
of the Schrödinger–Poisson / Schrödinger–Newton system (`ComplexEinstein.EinsteinSchrodingerNonrelLimit`).
-/

set_option autoImplicit false

open MeasureTheory SchwartzMap
open scoped Space
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation

open Space

/-- **[The Newton-kernel weak Poisson equation at an arbitrary point]** the origin pairing
translated to `y`: `∫ (Δη)(x)·‖x−y‖⁻¹ dx = −4π·η(y)`, via the repo's `distTranslate` machinery and
the proved fundamental solution. -/
@[zil_level physical_theorem]
lemma newtonKernel_weakPoisson_at (η : 𝓢(Space 3, ℝ)) (y : Space 3) :
    ∫ x, laplacianSchwartz η x • (‖x - y‖ ^ (- (((3 : ℕ) : ℤ) - 2)) : ℝ) = -(4 * Real.pi) * η y := by
  have hvadd : Space.basis.repr y +ᵥ (0 : Space 3) = y := by ext i; simp
  have hEq : distOfFunction (fun x : Space 3 => ‖x - y‖ ^ (- (((3 : ℕ) : ℤ) - 2)))
        (IsDistBounded.pow_shift _ y (by omega))
      = Space.distTranslate (Space.basis.repr y)
          (distOfFunction (fun z : Space 3 => ‖z‖ ^ (- (((3 : ℕ) : ℤ) - 2)))
            (IsDistBounded.pow _ (by omega))) := by
    rw [distTranslate_ofFunction]
    congr 1
  rw [← distOfFunction_distLaplacian_apply _ (IsDistBounded.pow_shift _ y (by omega)), hEq,
    distLaplacian_distTranslate, distLaplacian_fundamentalSolution_norm_zpow,
    volume_metricBall_three_real, map_smul, distTranslate_diracDelta, hvadd,
    ContinuousLinearMap.smul_apply, Physlib.Distribution.diracDelta_apply, smul_eq_mul]
  push_cast
  try ring

/-- **[The Schrödinger–Poisson field equation — continuum weak Poisson law]**
`∫ φ_ρ(x)·Δη(x) dx = −4π ∫ ρ(y)·η(y) dy`, i.e. `−Δφ_ρ = 4πρ` weakly, for the Newtonian convolution
potential `φ_ρ` of a mass density `ρ`. The product-integrability hypothesis licenses the Fubini
swap. -/
@[zil_level physical_theorem]
theorem convolutionPotential_weakPoisson (ρ : Space 3 → ℝ) (η : 𝓢(Space 3, ℝ))
    (hInt : Integrable (Function.uncurry fun x y : Space 3 =>
      laplacianSchwartz η x • (ρ y / ‖x - y‖)) (volume.prod volume)) :
    ∫ x, laplacianSchwartz η x • newtonianConvolutionPotential ρ x =
      -(4 * Real.pi) * ∫ y, ρ y * η y := by
  have hkernel : ∀ x y : Space 3,
      (‖x - y‖ ^ (- (((3 : ℕ) : ℤ) - 2)) : ℝ) = ‖x - y‖⁻¹ := by
    intro x y; norm_num
  have hstep : ∀ y : Space 3,
      (∫ x, laplacianSchwartz η x • (ρ y / ‖x - y‖)) = -(4 * Real.pi) * η y * ρ y := by
    intro y
    have hfun : (fun x => laplacianSchwartz η x • (ρ y / ‖x - y‖))
        = (fun x => ρ y • (laplacianSchwartz η x • (‖x - y‖ ^ (- (((3 : ℕ) : ℤ) - 2)) : ℝ))) := by
      funext x; rw [hkernel]; simp only [smul_eq_mul, div_eq_mul_inv]; ring
    rw [hfun, integral_smul, newtonKernel_weakPoisson_at]
    ring
  calc ∫ x, laplacianSchwartz η x • newtonianConvolutionPotential ρ x
      = ∫ x, ∫ y, laplacianSchwartz η x • (ρ y / ‖x - y‖) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show laplacianSchwartz η x • (∫ y, ρ y / ‖x - y‖) =
          ∫ y, laplacianSchwartz η x • (ρ y / ‖x - y‖)
        rw [integral_smul]
    _ = ∫ y, ∫ x, laplacianSchwartz η x • (ρ y / ‖x - y‖) := integral_integral_swap hInt
    _ = ∫ y, -(4 * Real.pi) * η y * ρ y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact hstep y
    _ = -(4 * Real.pi) * ∫ y, ρ y * η y := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation.convolutionPotential_weakPoisson where
  formalizes @ "claim:the-schrodinger-poisson-field-equation-continuum-weak-poisson-law-the-integral-of-the-newtonian-convolution-potential-of-rho-against-the-schwartz-laplacian-of-eta-equals-minus-four-pi-times-the-integral-of-rho-times-eta-i-e-minus-laplacian-phi-rho-equals-four-pi-rho-weakly",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.newtonKernel_weakPoisson_origin",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential",
  caveat @ "claim:the-fubini-swap-is-licensed-by-an-explicit-product-integrability-hypothesis-on-the-joint-integrand"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation.newtonKernel_weakPoisson_at where
  supported_by @ "lean:Space.distLaplacian_distTranslate",
  formalizes @ "claim:the-newton-kernel-weak-poisson-pairing-at-an-arbitrary-point-y-the-integral-of-the-schwartz-laplacian-of-eta-against-one-over-norm-x-minus-y-equals-minus-four-pi-times-eta-at-y-the-origin-pairing-translated-by-y"

zil_file_contract physlib.schrodingerPoissonFieldEquation where
  promises "The continuum weak Poisson law / Schrodinger-Poisson field equation, composing the Newtonian convolution potential (NewtonianConvolutionPotential) with the point-source weak Poisson equation (WeakNewtonPoisson). newtonKernel_weakPoisson_at translates the origin pairing to an arbitrary point: the integral of the Schwartz Laplacian of eta against 1/norm(x-y) equals minus four pi times eta at y, via the repo's distTranslate machinery (distTranslate_ofFunction, distLaplacian_distTranslate, distTranslate_diracDelta) and the proved fundamental solution. convolutionPotential_weakPoisson then delivers the continuum law: the integral of phi_rho against the Schwartz Laplacian of eta equals minus four pi times the integral of rho times eta (that is, minus Laplacian phi_rho equals four pi rho weakly), by Fubini (integral_integral_swap) against phi_rho(x) = integral of rho(y)/norm(x-y). This is the field equation of the Schrodinger-Poisson / Schrodinger-Newton system. Honest: the Fubini swap is licensed by an explicit product-integrability hypothesis on the joint integrand."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.newtonKernel_weakPoisson_origin",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.distOfFunction_distLaplacian_apply"]
  forbids_substitutes ["the point-source pairing alone, whereas this is the continuum convolution-potential source",
    "an unconditional Fubini swap, whereas the product-integrability hypothesis is carried explicitly"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation.newtonKernel_weakPoisson_at,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation.convolutionPotential_weakPoisson]

/- ZIL-END -/
