/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein

/-!
# The entropic Einstein equation is consistent: conservation in bit form

The consistency capstone of the arc. Any Einstein equation `G_μν = κ T_μν` is compatible with matter
only if the stress-energy is conserved, and that follows from the contracted Bianchi identity
`∇^μ G_μν = 0` (the diffeomorphism invariance of curvature): `bianchi_implies_conservation` gives
`∇^μ T_μν = 0`. Here we carry that consistency through the area-per-bit form of `G`.

With `G` read as the holographic bit count `N = holographicBits (sphereArea R) G ℏ c`, so that the
Einstein coupling is `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`), the divergence-free
Einstein tensor still forces `∇^μ T_μν = 0`. The whole complex Einstein equation `𝒢 = κ(T + iS)` is
consistent: the real sector `G_μν = κ T_μν` with conserved `T`, and the entropic imaginary sector
`Λ = κ S` (`HorizonNagaoContourBitEinstein.entropic_einstein_bitForm`), all at the one bit count that
carries the free-fall acceleration, the horizon decoherence, and the cosmological constant.

* **§A** `∇^μ T_μν = 0` and the bit-form coupling, from the contracted Bianchi identity.
* **§B** the consistent complex Einstein equation in bit form: real sector conserved, entropic sector
  sourced, coupling as a bit count.

## References

* Repo carriers: `ComplexEinstein.EinsteinFieldEquationsPhysLean.bianchi_implies_conservation`,
  `ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein`,
  `Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm`.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicEinsteinConservationBits

variable {ι : Type*}

@[expose] public section

/-! ## A. Stress-energy conservation in bit form -/

/-- **[The entropic Einstein equation conserves stress-energy]** for the bit-form Einstein equation
`G_μν = (8πG/c⁴) T_μν` with `N = holographicBits (sphereArea R) G ℏ c`, the contracted Bianchi
identity `∇^μ G_μν = 0` forces `∇^μ T_μν = 0` (`bianchi_implies_conservation`), and the coupling is the
area-per-bit form `8π(A/N)/(ℏc)`. Reading `G` as a bit count does not spoil the diffeomorphism
consistency of the field equation. -/
theorem entropic_einstein_conservation_bitForm
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4))
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) :
    Div T = 0 ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ : 8 * Real.pi * G / c ^ 4 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) (pow_ne_zero 4 hc)
  exact ⟨bianchi_implies_conservation Div Ric scalarR g T (8 * Real.pi * G / c ^ 4) hEFE hBianchi hκ,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## B. The consistent complex Einstein equation in bit form -/

/-- **[The complex Einstein equation is consistent in bit form]** from the single identification
`N = holographicBits (sphereArea R) G ℏ c` and a divergence-free Einstein tensor, a solution of the
complex field equation `𝒢 = κ(T + iS)` at `κ = 8πG/c⁴` delivers all of: the real Einstein equation
`G_μν = κ T_μν`; the entropic imaginary curvature `Λ = κ S`; the conservation `∇^μ T_μν = 0`; and the
coupling `κ = 8π(A/N)/(ℏc)` as a bit count. Curvature, entropic source, conservation and the
information-theoretic `G`, one consistent statement. -/
theorem entropic_gravity_consistent_bitForm
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hcomplex : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S
      (8 * Real.pi * G / c ^ 4))
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) :
    einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
    ∧ Λ = (8 * Real.pi * G / c ^ 4) • S
    ∧ Div T = 0
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ : 8 * Real.pi * G / c ^ 4 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) (pow_ne_zero 4 hc)
  obtain ⟨hreal, himag⟩ :=
    (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)).mp
      hcomplex
  exact ⟨hreal, himag,
    bianchi_implies_conservation Div Ric scalarR g T (8 * Real.pi * G / c ^ 4) hreal hBianchi hκ,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicEinsteinConservationBits
