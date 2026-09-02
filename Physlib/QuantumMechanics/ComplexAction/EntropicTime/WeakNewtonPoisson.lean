/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
meta import Zil

/-!
# The distributional Laplacian is self-adjoint on test functions

This module supplies the keystone pairing that turns the repo's *distributional* fundamental-solution
identity `Δᵈ(distOfFunction ‖x‖^{2-d}) = c·δ₀` into a *concrete integral* against the pointwise
Laplacian of a test function:

  `(Δᵈ u) η = u (laplacianSchwartz η)`,

where `laplacianSchwartz : 𝓢 →L 𝓢` is the Schwartz Laplacian `∑ᵢ ∂ᵢ∂ᵢ` (built exactly as the existing
`gradSchwartz` is built), and `laplacianSchwartz η x = Δ η x` pointwise. Specializing to
`u = distOfFunction f` gives `(Δᵈ (distOfFunction f)) η = ∫ x, f x · Δη x`. This is the adjoint (two
integrations by parts, the two signs cancelling) exposed by `fderivD_apply`.
-/

set_option autoImplicit false

open MeasureTheory SchwartzMap
open scoped Space

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson

open Space

/-- The `i`-th partial derivative as a continuous linear map on Schwartz space,
`∂ᵢ = evalCLM (basis i) ∘ fderivCLM` — the atom of both `gradSchwartz` and the Laplacian below. -/
noncomputable def partialSchwartz {d} (i : Fin d) : 𝓢(Space d, ℝ) →L[ℝ] 𝓢(Space d, ℝ) :=
  SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) ∘L SchwartzMap.fderivCLM ℝ (Space d) ℝ

/-- The Schwartz Laplacian `∑ᵢ ∂ᵢ∂ᵢ`, built like `gradSchwartz`. -/
noncomputable def laplacianSchwartz {d} : 𝓢(Space d, ℝ) →L[ℝ] 𝓢(Space d, ℝ) :=
  ∑ i, partialSchwartz i ∘L partialSchwartz i

lemma partialSchwartz_apply {d} (i : Fin d) (η : 𝓢(Space d, ℝ)) (x : Space d) :
    partialSchwartz i η x = fderiv ℝ (⇑η) x (basis i) := rfl

/-- **[The distributional Laplacian is self-adjoint against a test function]**
`(Δᵈ u) η = u (laplacianSchwartz η)` for every distribution `u`. Two integrations by parts
(`fderivD_apply` applied through the gradient and the divergence) contribute two minus signs that
cancel. -/
@[zil_level physical_theorem]
lemma distLaplacian_apply_eq {d} (u : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ)) :
    Space.distLaplacian u η = u (laplacianSchwartz η) := by
  show (Space.distDiv (Space.distGrad u)) η = u (laplacianSchwartz η)
  rw [distDiv_apply_eq_sum_distDeriv, laplacianSchwartz, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [distDeriv_apply, Distribution.fderivD_apply]
  simp only [PiLp.neg_apply, distGrad_apply]
  rw [distDeriv_apply, Distribution.fderivD_apply, neg_neg]
  rfl

/-- Specializing the self-adjoint pairing to a function-induced distribution: the distributional
Laplacian of `distOfFunction f`, tested against `η`, is the integral of `f` against the Schwartz
Laplacian of `η`. -/
@[zil_level physical_theorem]
lemma distOfFunction_distLaplacian_apply {d} (f : Space d → ℝ) (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Space.distLaplacian (Space.distOfFunction f hf) η = ∫ x, laplacianSchwartz η x • f x := by
  rw [distLaplacian_apply_eq, distOfFunction_apply]

/-- **[The Newton-kernel weak Poisson equation at the origin]** the concrete form of the
fundamental-solution identity: `∫ (Δη)(x)·‖x‖⁻¹ dx = −4π·η(0)` in three dimensions (with
`Δη = laplacianSchwartz η`, the Schwartz Laplacian). This is
`distLaplacian_fundamentalSolution_norm_zpow` at `d = 3` paired with `η` through the self-adjoint
bridge `distLaplacian_apply_eq` — the weak Poisson equation `−Δ(1/‖x‖) = 4π·δ₀`. -/
@[zil_level physical_theorem]
lemma newtonKernel_weakPoisson_origin (η : 𝓢(Space 3, ℝ)) :
    ∫ x, laplacianSchwartz η x • (‖x‖ ^ (- (((3 : ℕ) : ℤ) - 2)) : ℝ) = -(4 * Real.pi) * η 0 := by
  rw [← distOfFunction_distLaplacian_apply _ (IsDistBounded.pow _ (by omega)),
    distLaplacian_fundamentalSolution_norm_zpow, volume_metricBall_three_real,
    ContinuousLinearMap.smul_apply, Physlib.Distribution.diracDelta_apply, smul_eq_mul]
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.distLaplacian_apply_eq where
  formalizes @ "claim:the-repo-distributional-laplacian-is-self-adjoint-against-a-schwartz-test-function-the-distributional-laplacian-of-a-distribution-u-paired-with-eta-equals-u-applied-to-the-schwartz-laplacian-of-eta-two-integrations-by-parts-whose-signs-cancel",
  supported_by @ "lean:Physlib.Distribution.fderivD_apply",
  supported_by @ "lean:Space.distDiv_apply_eq_sum_distDeriv"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.newtonKernel_weakPoisson_origin where
  formalizes @ "claim:the-newton-kernel-weak-poisson-equation-at-the-origin-in-three-dimensions-the-integral-of-the-schwartz-laplacian-of-eta-against-the-newton-kernel-one-over-norm-x-equals-minus-four-pi-times-eta-at-zero-the-concrete-integral-form-of-minus-laplacian-of-one-over-norm-x-equals-four-pi-dirac-delta",
  supported_by @ "lean:Space.distLaplacian_fundamentalSolution_norm_zpow",
  caveat @ "claim:this-is-the-origin-centered-point-source-weak-poisson-pairing-the-continuum-source-integral-phi-rho-against-laplacian-eta-follows-by-translation-and-fubini-with-a-product-integrability-hypothesis"

zil_file_contract physlib.weakNewtonPoisson where
  promises "The keystone self-adjoint pairing turning the repo's distributional fundamental-solution identity into a concrete integral against the pointwise Laplacian of a test function. laplacianSchwartz is the Schwartz Laplacian sum over i of the second partial derivatives, built exactly as the existing gradSchwartz. distLaplacian_apply_eq proves the distributional Laplacian is self-adjoint: distLaplacian u eta = u (laplacianSchwartz eta) for every distribution u, via distDiv_apply_eq_sum_distDeriv and fderivD_apply applied twice (the two minus signs cancel). distOfFunction_distLaplacian_apply specializes this to a function-induced distribution: distLaplacian (distOfFunction f) eta = integral of f against the Schwartz Laplacian of eta. newtonKernel_weakPoisson_origin then delivers the concrete weak Poisson equation for the Newton kernel in three dimensions: the integral of the Schwartz Laplacian of eta against 1/norm(x) equals minus four pi times eta at zero (the concrete form of minus Laplacian of 1/norm(x) equals four pi Dirac delta), from distLaplacian_fundamentalSolution_norm_zpow at d=3 paired with eta through the self-adjoint bridge. Honest: this is the origin-centered point-source weak Poisson pairing; the continuum-source integral phi_rho against Laplacian eta follows by translation and Fubini with a product-integrability hypothesis."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Space.distLaplacian_fundamentalSolution_norm_zpow",
    "lean:Physlib.Distribution.fderivD_apply",
    "lean:Space.distDiv_apply_eq_sum_distDeriv"]
  forbids_substitutes ["keeping the identity purely distributional as u = c dirac delta, whereas this exposes the concrete integral against the pointwise Schwartz Laplacian",
    "a smooth-function Laplacian that ignores the singular kernel, whereas the fundamental-solution delta is the content"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.distLaplacian_apply_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.distOfFunction_distLaplacian_apply,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.WeakNewtonPoisson.newtonKernel_weakPoisson_origin]

/- ZIL-END -/