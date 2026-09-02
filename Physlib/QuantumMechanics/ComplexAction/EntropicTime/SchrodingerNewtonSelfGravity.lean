/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerPoissonFieldEquation
meta import Zil

/-!
# Schrödinger–Newton self-gravity: positivity of the potential and the Hartree energy

For a nonnegative mass density `ρ` — in particular a quantum probability density `ρ = |ψ|²` — the
Newtonian convolution potential and its self-interaction energy are nonnegative:

* `newtonianConvolutionPotential_nonneg` — `φ_ρ(x) = ∫ ρ(y)/‖x−y‖ dy ≥ 0`, since the Newton kernel is
  positive and the source nonnegative;
* `newtonianSelfEnergy_nonneg` — `∫ φ_ρ·ρ = ∬ ρ(x)ρ(y)/‖x−y‖ ≥ 0`, the nonnegative gravitational
  self-interaction (Hartree/Choquard) energy of the density.

These are the sign properties of the self-gravity of a Schrödinger–Newton state
(`SchrodingerPoissonFieldEquation`, `NewtonianConvolutionPotential`).
-/

set_option autoImplicit false

open MeasureTheory
open scoped Space
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity

/-- **[The self-gravity potential is nonnegative]** `φ_ρ(x) = ∫ ρ(y)/‖x−y‖ dy ≥ 0` for a nonnegative
mass density `ρ` (e.g. a quantum probability density `ρ = |ψ|²`): the Newton kernel is positive. -/
@[zil_level physical_theorem]
theorem newtonianConvolutionPotential_nonneg (ρ : Space 3 → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (x : Space 3) :
    0 ≤ newtonianConvolutionPotential ρ x := by
  rw [newtonianConvolutionPotential]
  exact integral_nonneg fun y => div_nonneg (hρ y) (norm_nonneg _)

/-- **[The gravitational self-interaction (Hartree) energy is nonnegative]**
`∫ φ_ρ·ρ = ∬ ρ(x)ρ(y)/‖x−y‖ ≥ 0` for a nonnegative mass density `ρ` — the positive self-gravity
binding energy of a Schrödinger–Newton state. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_nonneg (ρ : Space 3 → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    0 ≤ newtonianSelfEnergy ρ := by
  rw [newtonianSelfEnergy_eq_doubleIntegral]
  refine integral_nonneg fun x => ?_
  exact integral_nonneg fun y => div_nonneg (mul_nonneg (hρ x) (hρ y)) (norm_nonneg _)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianSelfEnergy_nonneg where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral",
  formalizes @ "claim:the-gravitational-self-interaction-hartree-energy-of-a-nonnegative-mass-density-the-double-integral-of-rho-x-rho-y-over-norm-x-minus-y-is-nonnegative-the-positive-self-gravity-binding-energy-of-a-schrodinger-newton-state"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianConvolutionPotential_nonneg where
  formalizes @ "claim:the-newtonian-self-gravity-convolution-potential-of-a-nonnegative-mass-density-is-nonnegative-because-the-newton-kernel-one-over-norm-x-minus-y-is-positive"

zil_file_contract physlib.schrodingerNewtonSelfGravity where
  promises "Sign properties of the self-gravity of a Schrodinger-Newton state, for a nonnegative mass density rho (in particular a quantum probability density rho = |psi|^2). newtonianConvolutionPotential_nonneg proves the self-gravity potential phi_rho(x) = integral of rho(y)/norm(x-y) is nonnegative, since the Newton kernel is positive and the source nonnegative. newtonianSelfEnergy_nonneg proves the gravitational self-interaction (Hartree/Choquard) energy integral of phi_rho times rho = double integral of rho(x)rho(y)/norm(x-y) is nonnegative -- the positive self-gravity binding energy. Both reduce, via newtonianSelfEnergy_eq_doubleIntegral, to nonnegativity of a nonnegative integrand by integral_nonneg."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential"]
  forbids_substitutes ["a signed density, whereas the positivity requires a nonnegative source rho",
    "the potential-energy sign convention alone, whereas this is the kernel-positivity double-integral bound"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianConvolutionPotential_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianSelfEnergy_nonneg]

/- ZIL-END -/
