/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhHolographicGEinstein
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm

/-!
# The electrogravitic system from the Unruh screen: gravity + gauge off one holographic bit-count

Extends the Unruh–holographic-`G` Einstein equation (`SciamaUnruhHolographicGEinstein`) to the full
**electrogravitic** (Einstein–Maxwell) system of `EntropicTime.ElectroGravitationalBitForm`, in which gravity
and the gauge (electromagnetic) sector are read off the *same* holographic screen.

The electrogravitic system `electrogravitic_system_bitForm` bundles exactly the arc's ingredients:

* its **real sector** `einsteinFieldEquation Ric scalarR g T (8πG/c⁴)` is the Unruh–Clausius Einstein equation
  (`SciamaUnruhEinsteinEquationOfState.einstein_from_sciamaUnruh`, `T_U = sciamaUnruhTemperature`);
* its **imaginary sector** `Λ = (8πG/c⁴)•S` is the entropic curvature of the complex Einstein equation
  (`SciamaUnruhComplexEinsteinFermion.sciamaUnruh_complexEinstein`, `Λ = κS`);
* its **coupling** `8πG/c⁴ = 8π(A/N)/(ℏc)` is the holographic area-per-bit (`A/N = ℓ_P²`), the same
  bit-count `G` as `einstein_from_sciamaUnruh_holographicG`;
* it carries the **BCJ double copy** `gravity = gauge²` (`SciamaFockBCJAdSCFT`), and the residual is governed by
  the boundary central charge `c = N²/4` (`SciamaFockAdSCFT.n4SYM_cylinderCasimir`,
  `BoundaryCentralChargeElectrograviticResidual`).

* `sciamaUnruh_electrogravitic_coupling` — the Einstein–Maxwell coupling `8πG/c⁴ = 8π(A/N)/(ℏc)`: gravity and
  gauge share the one area-per-bit of the Unruh/holographic screen.
* `sciamaUnruh_electrogravitic_system` — **the electrogravitic Einstein–Maxwell equation at the Unruh screen**:
  with the Unruh-derived matter Einstein (real) and the entropic curvature (imaginary), the electromagnetic
  potential `A` and the complex-mass split source the electrogravitic field equation at the bit-count coupling.

So the accelerated-detector Unruh temperature fixes the thermal input, the screen bit-count fixes `G`, and the
gauge field couples through the same bits: gravity and electromagnetism are two sectors of one holographic
equation.

Honest scope: the instantiation of the electrogravitic system at the Unruh/holographic screen and the bit-form
coupling.  The Einstein–Maxwell content, Maxwell–Bianchi, and BCJ double copy are carried by
`ElectroGravitationalBitForm`; here they are tied to the Unruh-derived real/imaginary sectors and the screen
`G`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhElectrogravitic

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm

/-- **[Gravity and gauge share one area-per-bit] `8πG/c⁴ = 8π(A/N)/(ℏc)`.**  The electrogravitic
Einstein–Maxwell coupling is the holographic area-per-bit of the Unruh screen — the same bit-count `G` as
`einstein_from_sciamaUnruh_holographicG`; gravity and electromagnetism couple through the same information
bits. -/
theorem sciamaUnruh_electrogravitic_coupling (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits

/-- **[The electrogravitic Einstein–Maxwell equation at the Unruh screen].**  With the Unruh–Clausius matter
Einstein equation (`hReal`, the real sector), the entropic curvature (`hImag`, `Λ = κS`, the imaginary sector),
the complex-mass split, and the electromagnetic potential `A`, the electrogravitic field equation holds at the
holographic bit-count coupling `8πG/c⁴ = 8π(A/N)/(ℏc)` — gravity and gauge off one screen. -/
theorem sciamaUnruh_electrogravitic_system {ι : Type*} [Fintype ι]
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (m_R m_I S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hReal : einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4))
    (hImag : Λ = (8 * Real.pi * G / c ^ 4) • S)
    (hsplit : m_I * c ^ 2 = S₁ + S₂) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)
        m_R m_I c S₁ S₂ k A
      ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  electrogravitic_system_bitForm Ric scalarR g Λ T S m_R m_I S₁ S₂ k A G ℏ c N R
    hℏ hc hG hR hbits hReal hImag hsplit

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhElectrogravitic

end
