/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.KinematicsCore
public import Physlib.Thermodynamics.VerlindeNewtonGravityCore

/-!
# The area of the one-region entanglement screen

The one-region model of the entangled pair has a *size*: the entropic proper distance
`r = λ_C·log K` (`EntropicProperDistance`, `K = coth η` the Schmidt number). This module closes
that radius into a **screen**, derives the equation for its area and the Verlinde holographic bit
count of that area, and isolates the fine-structure constant from the bit count.

* `entanglementScreenArea` — `A(η) = 4π·λ_C²·(log K)²`: the area of the sphere at the one-region
  radius is the Compton area `λ_C²` times the *squared* entanglement entropy (in nats).
* `entanglementScreen_holographicBits` — `N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m²`: the Verlinde bit
  count of that screen, the squared Planck-to-particle mass ratio times the squared entanglement
  nats (`ℏc/G = m_P²`).
* `fineStructure_from_screenBits` / `newtonG_from_screenBits` — feeding the bit count into
  `α = e²/(4πε₀ℏc)` eliminates `ℏc` and isolates `α = (e/m)²·(log K)²/(ε₀·G·N)`; read backwards the
  same identity fixes Newton's constant `G = (e/m)²·(log K)²/(ε₀·α·N)`.

## References

* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029 —
  `N = Ac³/(Gℏ)`.
* T. Faulkner, M. Guica, T. Hartman, R. C. Myers, M. Van Raamsdonk, *Gravitation from entanglement
  in holographic CFTs*, JHEP **03** (2014) 051, arXiv:1312.7856; H. Casini, M. Huerta, R. C. Myers,
  *Towards a derivation of holographic entanglement entropy*, JHEP **05** (2011) 036,
  arXiv:1102.0440 — the entanglement-entropy route to the gravitational sector.
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. **126** (2011)
  1021, arXiv:1104.3381 — the complex-action framework.

The area equation `A = 4πλ_C²(log K)²`, the bit count `N = 4π(m_P/m)²(log K)²` and the
fine-structure isolation `α = (e/m)²(log K)²/(ε₀GN)` are this framework's; the references above are
the external results they build on. -/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic
open Physlib.Thermodynamics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-! ## A. The area equation -/

/-- **The area of the one-region entanglement screen**:
`A(η) = 4π·λ_C²·(log K)²` — the sphere at the entropic proper radius `r = λ_C·log K`
has the Compton area times the squared entanglement entropy (in nats). The size of the
one region is quadratic in its entanglement. -/
lemma entanglementScreenArea (m c ħ η : ℝ) :
    sphereArea (entropicProperDistance m c ħ η)
      = 4 * Real.pi * comptonWavelength m c ħ ^ 2
          * Real.log (schmidtNumber η) ^ 2 := by
  unfold sphereArea entropicProperDistance
  ring

/-! ## B. The holographic face: bits on the screen -/

/-- **The holographic bit count of the entanglement screen**:
`N = A·c³/(Gℏ) = 4π·(ℏc/G)·(log K)²/m²` — since `ℏc/G = m_P²` (the squared Planck mass),
this is `N = 4π·(m_P/m)²·(log K)²`: squared Planck-to-particle mass ratio times squared
entanglement nats. The mass ratio enters through the two factorizations of `ℏ/c` —
`λ_C·m = ℏ/c = ℓ_P·m_P` — so `λ_C/ℓ_P = m_P/m`. -/
lemma entanglementScreen_holographicBits (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c
      = 4 * Real.pi * (ħ * c / G) * Real.log (schmidtNumber η) ^ 2 / m ^ 2 := by
  unfold holographicBits sphereArea entropicProperDistance comptonWavelength
  field_simp

/-! ## C. Isolating the fine-structure constant from the screen

Feeding the screen's holographic bit count `N = 4π(m_P/m)²(log K)²` (the entropic route to
Newton's `G` of §B) into `α = e²/(4πε₀ℏc)` eliminates `ℏc` in favor of measurable ratios and the
fine-structure constant is **isolated**:

  `α = (e/m)²·(log K)²/(ε₀·G·N)`

— squared charge-to-mass ratio times squared entanglement nats over `ε₀·G·(bit count)`; read the
other way, the same identity *solves for `G`* in terms of `α`, the charge-to-mass ratio and
the screen count: `G = (e/m)²·(log K)²/(ε₀·α·N)`. -/

/-- **The fine-structure constant** `α = e²/(4πε₀ℏc)`. -/
noncomputable def fineStructure (e eps0 ħ c : ℝ) : ℝ := e ^ 2 / (4 * Real.pi * eps0 * ħ * c)

/-- **The squared Planck mass** `m_P² = ℏc/G` — the mass whose gravitational coupling is one. -/
noncomputable def planckMassSq (G ħ c : ℝ) : ℝ := ħ * c / G

/-- **The gravitational coupling** `α_G = Gm²/(ℏc)` — gravity's fine-structure constant. -/
noncomputable def gravitationalCoupling (G m ħ c : ℝ) : ℝ := G * m ^ 2 / (ħ * c)

/-- **[The fine-structure constant isolated from the screen]**
`α = (e/m)²·(log K)²/(ε₀·G·N)` with `N` the holographic bit count of the one-region
entanglement screen: the charge-to-mass ratio and the squared entanglement nats, divided by
`ε₀·G` times the bit count — `ℏ` and `c` eliminated through the entropic `G`-equation of §B. -/
lemma fineStructure_from_screenBits (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η) :
    fineStructure e eps0 ħ c
      = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * G
            * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

/-- **[Newton's constant derived from `α` and the screen]**
`G = (e/m)²·(log K)²/(ε₀·α·N)`: the same identity read backwards — the entropic bit count, the
fine-structure constant and the charge-to-mass ratio fix Newton's constant. -/
lemma newtonG_from_screenBits (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (he : e ≠ 0) :
    G = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * fineStructure e eps0 ħ c
            * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

end
