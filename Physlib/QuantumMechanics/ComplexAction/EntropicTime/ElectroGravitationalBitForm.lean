/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicEinsteinConservationBits
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

/-!
# The electrogravitic (Einstein-Maxwell) equations with `G` as a bit count

The electrogravitic field equations couple gravity to electromagnetism: gravity is sourced by the
electromagnetic stress-energy, `G_{μν} = κ T^{EM}_{μν}`, the electromagnetic sector obeys the
homogeneous Maxwell equation `dF = 0`, and — through the **BCJ double copy** — the gravity sector is
the *square* of the gauge sector. The repository already packages all of this in the
`ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation` structure; this
module derives it with `G` in the area-per-bit form of the arc, `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`
(`einsteinCoupling_bitForm`), leveraging that structure — no re-derivation.

The three faces of the double copy, all at the bit-count coupling:

* **kinematic** — the gauge Maxwell-Faraday Bianchi identity `k_{[λ}F_{μν]} = 0` (`dF = 0`,
  `ElectroGravitationalFieldEquation.maxwellBianchi`) *is* the BCJ kinematic Jacobi identity *is* the
  gravity first Bianchi;
* **conservation** — the gravity second Bianchi `∇^μ G_{μν} = 0`, Einstein-contracted to the
  electromagnetic stress-energy, gives `∇^μ T^{EM}_{μν} = 0`
  (`ElectroGravitationalFieldEquation.stressEnergyConservation`, via `contracted_bianchi_conservation`);
* **entropic** — the gravity entropic source is the gauge² sum `m_I c² = S₁ + S₂`, so the amplitude
  factorizes `exp(−m_I c²) = exp(−S₁)·exp(−S₂)` (`ElectroGravitationalFieldEquation.bcjDoubleCopy`,
  gravity = gauge²).

With `G` the bit count `N`, the screen double copy `G·α = (c_s n_s)²/(ε₀ N)`
(`BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system`) reads the
gauge coupling `α` and gravity `G` off the same holographic screen: the electrogravitic coupling is one
bit count.

* **§A** construct the electrogravitic system at `κ = 8πG/c⁴`, coupling in bit form.
* **§B** the electrogravitic equations: Einstein-Maxwell, Maxwell Bianchi, gravity = gauge², bit form.
* **§C** electromagnetic stress-energy conservation from the gravity second Bianchi, bit form.

## References

* A. Bac et al., arXiv:2302.12739; the BCJ double copy (Bern-Carrasco-Johansson). Sorkin, Phys. Rev. D
  12 (1975) 385 — the entropic curvature defect.
* Repo carriers: `ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation`,
  `PTSymmetricQFT.MaxwellFaraday.faraday`, `GravitationalCouplingSystem.einsteinCoupling_bitForm`.
-/

set_option autoImplicit false

@[expose] public section

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm

variable {ι : Type*}

/-! ## A. Construct the electrogravitic system at the area-per-bit coupling -/

/-- **[The electrogravitic system at the bit-count `G`]** from the Einstein-Maxwell equation
`G_{μν} = κ T^{EM}_{μν}` (`hReal`), the entropic curvature `Λ = κ S` (`hImag`) and the gauge² mass
split `m_I c² = S₁ + S₂` (`hsplit`) at `κ = 8πG/c⁴`, the full `ElectroGravitationalFieldEquation` holds
(`of_einstein_maxwell`), and the coupling is the area-per-bit form `8π(A/N)/(ℏc)` when
`N = holographicBits (sphereArea R) G ℏ c`. -/
theorem electrogravitic_system_bitForm
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (m_R m_I S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hReal : einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4))
    (hImag : Λ = (8 * Real.pi * G / c ^ 4) • S)
    (hsplit : m_I * c ^ 2 = S₁ + S₂) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)
        m_R m_I c S₁ S₂ k A
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ : 8 * Real.pi * G / c ^ 4 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) (pow_ne_zero 4 hc)
  exact ⟨ElectroGravitationalFieldEquation.of_einstein_maxwell hκ hReal hImag hsplit k A,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## B. The electrogravitic equations in bit form -/

/-- **[The electrogravitic equations at the bit-count `G`]** an electrogravitic solution at
`κ = 8πG/c⁴` delivers, at the area-per-bit coupling: the **Einstein-Maxwell** equation
`G_{μν} = κ T^{EM}_{μν}` with entropic curvature `Λ = κ S`; the **Maxwell-Faraday Bianchi** identity
`k_{[λ}F_{μν]} = 0` (`dF = 0`); the **gravity = gauge²** double copy
`exp(−m_I c²) = exp(−S₁)·exp(−S₂)`; and the coupling `κ = 8π(A/N)/(ℏc)`. -/
theorem electrogravitic_equations_bitForm
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) (G ℏ N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)
        m_R m_I c S₁ S₂ k A) :
    (einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
        ∧ Λ = (8 * Real.pi * G / c ^ 4) • S)
    ∧ (∀ lam μ ν : Fin 4,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
    ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  ⟨H.einsteinMaxwell, H.maxwellBianchi, H.bcjDoubleCopy,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## C. Electromagnetic stress-energy conservation from the gravity second Bianchi -/

/-- **[Electromagnetic stress-energy conservation at the bit-count `G`]** for an electrogravitic
solution at `κ = 8πG/c⁴`, when the gravity second Bianchi holds (`∇^μ G_{μν} = 0`) and is
Einstein-contracted to the electromagnetic stress-energy (`∇^μ G = κ ∇^μ T`), the electromagnetic
stress-energy is conserved `∇^μ T^{EM}_{μν} = 0` (`stressEnergyConservation`, the gravity-side contract
of the double copy dual to the gauge Bianchi `dF = 0`), and the coupling is `8π(A/N)/(ℏc)`. -/
theorem electrogravitic_conservation_bitForm
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ) (G ℏ N R : ℝ)
    (divG divT : Fin 4 → ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)
        m_R m_I c S₁ S₂ k A)
    (hEinstein : divG = (8 * Real.pi * G / c ^ 4) • divT) (hSecondBianchi : divG = 0) :
    divT = 0
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  ⟨H.stressEnergyConservation divG divT hEinstein hSecondBianchi,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm

end
