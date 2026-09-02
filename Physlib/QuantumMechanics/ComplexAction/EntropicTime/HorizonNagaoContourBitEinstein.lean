/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FreeFallUniversalityFisherMass
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
# The horizon Nagao–Nielsen contour, the bit count, and the entropic Einstein equation

This binds the weak-equivalence-principle arc (`FreeFallUniversalityFisherMass`) to the two remaining
faces of the imaginary action `S_I`: the **Nagao–Nielsen decoherence path integral** and the
**entropic (imaginary) sector of the Einstein equation** — all governed by the one holographic bit
count `N = holographicBits (sphereArea R) G ℏ c = A c³/(Gℏ)`.

The complex path weight of a single history is `e^{iS/ℏ}` with `S = S_R + iS_I`
(`NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight`); its modulus
`‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}` (`norm_nnPathWeight`) is the Feynman–Vernon influence-functional
**decoherence factor** (`CaldeiraLeggettInfluenceFunctional.feynmanVernon_modulus_is_decoherence`). For
a **horizon** — the curved-space element — the imaginary action is
`S_I = c³A/(4G)` (`horizonImaginaryAction`), so in the area-per-bit form of `G`

  `S_I = ℏ N/4`   and   `‖e^{iS/ℏ}‖ = e^{−N/4} = e^{−S_BH}`:

the **Bekenstein–Hawking entropy is a quarter of the bit count**, and the curved-space decoherence
factor is `e^{−N/4}`. The same `S_I` is the scalar avatar of the entropic stress-energy `S` that
sources the imaginary curvature `Λ = κ S` of the complex Einstein equation
(`ComplexEinstein.FieldEquations`, cf. `EntropicTime.ClockEntropyNagaoGravity`).

* **§A** the horizon imaginary action `S_I = ℏ N/4` and its Nagao–Nielsen contour / decoherence
  modulus `e^{−N/4}`, with `G` in the area-per-bit form.
* **§B** the entropic Einstein equation in bit form: the complex `𝒢 = κ(T + iS)` splits into the real
  `G_μν = κ T_μν` and the imaginary `Λ = κ S`, with `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`.
* **§C** the bit count `N` governs all three faces at once: the horizon decoherence `e^{−N/4}`, the
  universal free-fall acceleration `4π M c³/(ℏ N)` (`FreeFallUniversalityFisherMass`), and the Einstein
  coupling `8π(A/N)/(ℏc)`.

## References

* E. Verlinde, JHEP 04 (2011) 029; J. D. Bekenstein, Phys. Rev. D 7 (1973) 2333 — the area-per-bit `G`
  and the horizon entropy `S_BH = A/(4ℓ_P²)`.
* A. O. Caldeira, A. J. Leggett, Physica A 121 (1983) 587 — the influence-functional decoherence.
* Repo carriers: `MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction`,
  `NonHermitianComplexAction.EntropicDampingEquivalence.norm_nnPathWeight`,
  `ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein`,
  `EntropicTime.ClockEntropyNagaoGravity`.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FreeFallUniversalityFisherMass

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein

@[expose] public section

/-! ## A. The horizon Nagao–Nielsen contour is the bit count -/

/-- **[The horizon imaginary action is a quarter of the bit count] `S_I = ℏ N/4`.** The imaginary
action of a horizon of area `A`, `S_I = c³A/(4G)` (`horizonImaginaryAction`), equals `ℏ/4` times the
holographic bit count `N = A c³/(Gℏ)`. This is the Bekenstein–Hawking entropy `S_BH = A/(4ℓ_P²) = N/4`
(in units of `ℏ`), written through `G` in the area-per-bit form. -/
theorem horizon_imaginaryAction_eq_quarter_bits (G c A ℏ : ℝ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) :
    horizonImaginaryAction G c A = ℏ * holographicBits A G ℏ c / 4 := by
  unfold horizonImaginaryAction holographicBits
  field_simp

/-- **[The horizon Nagao–Nielsen contour / decoherence modulus is `e^{−N/4}`]** The modulus of the
complex path weight of a horizon history, `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}`, is `e^{−N/4}` at the holographic
bit count: the Bekenstein–Hawking survival/decoherence factor `e^{−S_BH}`. This is the curved-space
value of the Feynman–Vernon influence-functional decoherence factor
(`CaldeiraLeggettInfluenceFunctional.feynmanVernon_modulus_is_decoherence`), with the horizon's
`S_I = c³A/(4G)` as the decoherence exponent. -/
theorem horizon_nnContour_bitCount (S_R G c A ℏ : ℝ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) :
    ‖nnPathWeight S_R (horizonImaginaryAction G c A) ℏ‖
      = Real.exp (-(holographicBits A G ℏ c / 4)) := by
  rw [norm_nnPathWeight_horizon]
  have h : c ^ 3 / (4 * G) * A / ℏ = holographicBits A G ℏ c / 4 := by
    unfold holographicBits; field_simp
  rw [h]

/-! ## B. The entropic Einstein equation in area-per-bit form -/

/-- **[The entropic Einstein equation in bit form]** At the Einstein coupling `κ = 8πG/c⁴`, a solution
of the complex field equation `𝒢 = κ(T + iS)` (`complexEinsteinFieldEquation`) splits into the real
`G_μν = κ T_μν` (`einsteinFieldEquation`) and the imaginary `Λ = κ S` — the entropic stress-energy `S`
(the matrix avatar of the Nagao–Nielsen imaginary action `S_I`) sourcing the imaginary curvature `Λ`.
From the single identification `N = holographicBits (sphereArea R) G ℏ c`, the coupling is the
area-per-bit form `κ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`): the full complex Einstein equation
with `G` read as a bit count. -/
theorem entropic_einstein_bitForm {ι : Type*} (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S
      (8 * Real.pi * G / c ^ 4)) :
    einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
    ∧ Λ = (8 * Real.pi * G / c ^ 4) • S
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  obtain ⟨hreal, himag⟩ :=
    (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)).mp hEFE
  exact ⟨hreal, himag, einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## C. One bit count for decoherence, free fall, and the Einstein coupling -/

/-- **[The bit count governs gravity]** From the single identification
`N = holographicBits (sphereArea R) G ℏ c`, the one bit count `N` sets three faces of gravity at once:

* the **horizon Nagao–Nielsen contour / decoherence** modulus `‖e^{iS/ℏ}‖ = e^{−N/4} = e^{−S_BH}`;
* the **universal free-fall** acceleration `a = G M/R² = 4π M c³/(ℏ N)`
  (`FreeFallUniversalityFisherMass.freeFall_acceleration_bitForm`), test-mass-independent;
* the **Einstein coupling** `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`).

Decoherence of histories, the equivalence principle, and the curvature–matter coupling are three
readings of the same holographic bit count. -/
theorem bitCount_governs_gravity (S_R G M ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ = Real.exp (-(N / 4))
    ∧ G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  refine ⟨?_, freeFall_acceleration_bitForm G M ℏ c N R hℏ hc hG hR hbits,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩
  rw [horizon_nnContour_bitCount S_R G c (sphereArea R) ℏ hG hℏ, hbits]

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
