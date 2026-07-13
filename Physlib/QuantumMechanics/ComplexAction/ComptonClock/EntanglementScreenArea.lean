/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.KinematicsCore
public import Physlib.Thermodynamics.VerlindeNewtonGravityCore

/-!
# The entanglement-screen holographic bit count

The one-region entanglement screen at the entropic proper distance `r = λ_C·log K`: its Verlinde
holographic bit count `N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m²`, and the fine-structure constant `α`
used to eliminate `α` in the Newton-`G` derivation.

## References

* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029 —
  `N = Ac³/(Gℏ)`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic
open Physlib.Thermodynamics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-- **The fine-structure constant** `α = e²/(4πε₀ℏc)`. -/
noncomputable def fineStructure (e eps0 ħ c : ℝ) : ℝ := e ^ 2 / (4 * Real.pi * eps0 * ħ * c)

/-- **The holographic bit count of the entanglement screen**:
`N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m²` — for the sphere `A = sphereArea r` at the entropic proper
radius `r = λ_C·log K`. -/
lemma entanglementScreen_holographicBits (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c
      = 4 * Real.pi * (ħ * c / G) * Real.log (schmidtNumber η) ^ 2 / m ^ 2 := by
  unfold holographicBits sphereArea entropicProperDistance comptonWavelength
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

end
