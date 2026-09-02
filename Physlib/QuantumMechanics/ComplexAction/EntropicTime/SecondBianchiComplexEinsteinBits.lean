/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicEinsteinConservationBits
public import Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi
public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

/-!
# Second-Bianchi conservation of the complex Einstein equations with `G` as a bit count

The second (differential) Bianchi identity `∇^μ G_{μν} = 0` — the Levi-Civita companion of the
diffeomorphism invariance of curvature — forces the source to be conserved. This module derives that
conservation for the **complex Einstein equation** `𝒢 = κ(T + iS)` with `G` read in the area-per-bit
form of the arc, leveraging the repository's existing second-Bianchi machinery (no re-derivation).

* **Real sector (Loinger Eq. 13).** The contracted second Bianchi identity gives `∇G = 0`
  (`Curvature.DiffeomorphismMetricVariation.einsteinDivergence_zero_of_secondBianchi`); with
  `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`) this is `∇T = 0` at the entropic coupling.
* **Complex sector.** On a solution of `𝒢 = κ(T + iS)` satisfying the second Bianchi, the complex
  gravitational tensor `𝒜` is divergence-free `∇^μ 𝒜 = 0`, and **both** the real matter `∇T = 0` and
  the entropic source `∇S = 0` are conserved
  (`Curvature.ComplexDAlembertSecondBianchi.complex_dAlembert_bianchi`) — the second Bianchi read
  through Levi-Civita's d'Alembert balance.

The connection carrying this is the **Levi-Civita** one, fixed by the metric through the Koszul formula
`Γ_{cab} = ½(γ_{bca} + γ_{acb} − γ_{cab})`
(`Curvature.JacobiRicciBianchiTetrad.TetradConnection.koszul`), whose curvature's first Bianchi is the
frame Jacobi identity and whose second Bianchi is the conservation above. With `G` the bit count `N`,
the whole complex Einstein system — real curvature, entropic sector, and their conservation — is carried
in the area-per-bit coupling `8π(A/N)/(ℏc)`.

* **§A** real second-Bianchi conservation `∇G = 0`, coupling in bit form.
* **§B** complex second-Bianchi conservation `∇𝒜 = 0 ∧ ∇T = 0 ∧ ∇S = 0`, coupling in bit form.
* **§C** the complex Einstein system conserved at the isolated bit-count `G`.

## References

* A. Bac et al., arXiv:2302.12739; N. Van den Bergh, arXiv:1302.6448 — the second Bianchi identity.
* Repo carriers: `ComplexDAlembertSecondBianchi.complex_dAlembert_bianchi`,
  `DiffeomorphismMetricVariation.einsteinDivergence_zero_of_secondBianchi`,
  `JacobiRicciBianchiTetrad.TetradConnection.koszul`, `GravitationalCouplingSystem.einsteinCoupling_bitForm`.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi
open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SecondBianchiComplexEinsteinBits

/-! ## A. Real second-Bianchi conservation, coupling in bit form -/

/-- **[The contracted second Bianchi gives `∇G = 0` at the area-per-bit coupling]** the contracted
second Bianchi identity forces the divergence of the Einstein tensor to vanish
(`einsteinDivergence_zero_of_secondBianchi`, Loinger Eq. 13), and the Einstein coupling is the
area-per-bit form `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`). With `G` read as the bit
count `N`, the Levi-Civita Einstein tensor is still conserved. -/
theorem einstein_divergence_secondBianchi_bitForm {ι : Type*} [Fintype ι]
    (divRicci gradScalar : ι → ℝ) (hB : contractedSecondBianchi divRicci gradScalar)
    (G ℏ c N R : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    einsteinDivergence divRicci gradScalar = 0
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  ⟨einsteinDivergence_zero_of_secondBianchi divRicci gradScalar hB,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## B. Complex second-Bianchi conservation, coupling in bit form -/

/-- **[The complex Einstein equation is conserved by the second Bianchi, coupling in bit form]** on a
solution of `𝒢 = κ(T + iS)` at `κ = 8πG/c⁴` satisfying the second Bianchi
`∇^μ (G_{μν} + iΛ_{μν}) = 0`, the complex gravitational tensor is divergence-free `∇^μ 𝒜 = 0`, the real
matter is conserved `∇T = 0`, and the entropic source is conserved `∇S = 0`
(`complex_dAlembert_bianchi`), all at the area-per-bit coupling `8π(A/N)/(ℏc)`. Reading `G` as a bit
count preserves the conservation of both the matter and the entropic sectors. -/
theorem complex_einstein_secondBianchi_bitForm {ι : Type*} [Fintype ι]
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S
      (8 * Real.pi * G / c ^ 4))
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0) :
    complexDiv Div
        (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ (8 * Real.pi * G / c ^ 4)) = 0
    ∧ Div T = 0
    ∧ Div S = 0
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ : 8 * Real.pi * G / c ^ 4 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) (pow_ne_zero 4 hc)
  obtain ⟨hgrav, _, hT, hS⟩ :=
    complex_dAlembert_bianchi Div Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4) hκ hEFE hBianchi
  exact ⟨hgrav, hT, hS, einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## C. The complex Einstein system conserved at the bit-count `G` -/

/-- **[The complex Einstein system is conserved at the isolated bit-count `G`]** from the single
identification `N = holographicBits (sphereArea R) G ℏ c` and the second Bianchi identity, a solution
of `𝒢 = κ(T + iS)` at `κ = 8πG/c⁴` delivers together: the real Einstein equation `G_μν = κ T_μν`, the
entropic imaginary curvature `Λ = κ S`, the conservations `∇T = 0` and `∇S = 0`, and the coupling
`κ = 8π(A/N)/(ℏc)` as a bit count. Real curvature, entropic sector and their Levi-Civita conservation,
one bit count. -/
theorem complex_einstein_system_conserved_bitForm {ι : Type*} [Fintype ι]
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S
      (8 * Real.pi * G / c ^ 4))
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0) :
    einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
    ∧ Λ = (8 * Real.pi * G / c ^ 4) • S
    ∧ Div T = 0
    ∧ Div S = 0
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  obtain ⟨hreal, himag⟩ :=
    (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S (8 * Real.pi * G / c ^ 4)).mp hEFE
  obtain ⟨_, hT, hS, hbit⟩ :=
    complex_einstein_secondBianchi_bitForm Div Ric scalarR g Λ T S G ℏ c N R
      hℏ hc hG hR hbits hEFE hBianchi
  exact ⟨hreal, himag, hT, hS, hbit⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SecondBianchiComplexEinsteinBits
