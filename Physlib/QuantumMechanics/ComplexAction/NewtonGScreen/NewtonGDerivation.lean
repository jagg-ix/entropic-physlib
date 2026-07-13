/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.KinematicsCore
public import Physlib.Thermodynamics.VerlindeNewtonGravityCore
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-!
# Newton's constant from the entropic screen (holographic-saturation route)

Three algebraic steps take the entropic screen at rapidity `η` (`K = coth η` the Schmidt number) to
a formula for Newton's constant:

* `screen_product` — the screen product law `G·α = (e/m)²(log K)²/(ε₀·N)`, `N` the holographic bit
  count of the sphere at the entropic proper radius `r = λ_C·log K`;
* `newtonG_from_system` — eliminating `α = e²/(4πε₀ℏc)` from the product law gives
  `G = 4π·ħc·(log K)²/(m²·N)`;
* `newtonG_derivation` — under holographic saturation `N = 4·log K` this reduces to
  `G = π·ħc·log K/m²`.

These are exact algebraic identities. The last uses the saturation hypothesis `N = 4·log K` as an
input and yields `G` as a function of `η` through `log K`.

## References

* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029; T.
  Jacobson, *Thermodynamics of Spacetime*, Phys. Rev. Lett. **75** (1995) 1260.
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.Thermodynamics

namespace Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.NewtonGDerivation

/-- **The screen product law** `G·α = (e/m)²·(log K)²/(ε₀·N)` with `N` the holographic bit count of
the one-region screen: substituting the bit count eliminates `ℏ` and `c`. An exact consistency
identity — `N` itself depends on `G`. -/
lemma screen_product (e eps0 m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η) :
    G * fineStructure e eps0 ħ c
      = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 := (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

/-- **Eliminating `α` from the product law** gives `G = 4π·ħc·(log K)²/(m²·N)`: feeding
`α = e²/(4πε₀ℏc)` into the product law `G·α = (e/m)²(log K)²/(ε₀·N)`, the charge `e` and `ε₀` cancel
and `α` drops out. -/
lemma newtonG_from_system (e eps0 m c ħ G η N : ℝ)
    (heps : eps0 ≠ 0) (hħ : ħ ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (hN : N ≠ 0)
    (hprod : G * fineStructure e eps0 ħ c
              = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2 / (eps0 * N)) :
    G = 4 * Real.pi * ħ * c * Real.log (schmidtNumber η) ^ 2 / (m ^ 2 * N) := by
  have hπ := Real.pi_ne_zero
  have hαval : fineStructure e eps0 ħ c = e ^ 2 / (4 * Real.pi * eps0 * ħ * c) := rfl
  have hαne : fineStructure e eps0 ħ c ≠ 0 := by
    rw [hαval]
    exact div_ne_zero (pow_ne_zero 2 he)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) heps) hħ) hc)
  have hG_eq : G = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2 / (eps0 * N)
      / fineStructure e eps0 ħ c := by rw [eq_div_iff hαne]; exact hprod
  rw [hG_eq, hαval]
  field_simp

/-- **Newton's constant from the screen under holographic saturation.** At the entropic screen at
rapidity `η`, with the holographic bit count saturated at `N = 4·log K`, Newton's constant is
`G = π·ħc·log K/m²` — its functional form under the saturation hypothesis, a function of `η`
through `log K`. -/
lemma newtonG_derivation (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (he : e ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (hsat : holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c
            = 4 * Real.log (schmidtNumber η)) :
    G = Real.pi * ħ * c * Real.log (schmidtNumber η) / m ^ 2 := by
  have hlog : Real.log (schmidtNumber η) ≠ 0 := (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hN : holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c ≠ 0 := by
    rw [hsat]; exact mul_ne_zero (by norm_num) hlog
  have hprod := screen_product e eps0 m c ħ G η hm hc hħ hG hη
  have hsol := newtonG_from_system e eps0 m c ħ G η
    (holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) heps hħ hc he hN hprod
  rw [hsat] at hsol
  rw [hsol]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.NewtonGDerivation

end
