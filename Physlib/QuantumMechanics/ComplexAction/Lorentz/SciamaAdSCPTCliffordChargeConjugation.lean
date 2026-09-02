/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBulkCorrespondence
public import Physlib.Relativity.CliffordAlgebra

/-!
# The charge-conjugation matrix `C = Γ⁰` on the Clifford algebra (Gomis 2507.12467, Eq. 2.3)

Gomis writes the `𝒩 = 4` gaugino as a `10d` Majorana–Weyl spinor whose `Γ^M` obey the `Cliff(1,9)` relation
(Eq. 2.3) `{Γ^M, Γ^N} = 2η^{MN}`, and takes the charge-conjugation matrix real, `C = Γ⁰`.  This module realizes
that structure in the `4d` Dirac representation (`Physlib.Relativity`'s `spaceTime.γ`, signature `(+,−,−,−)`) —
the spinor content the `10d` `Γ^M` reduce to (footnote 4: `𝟏𝟔 → (𝟐,𝟏;𝟒) ⊕ (𝟏,𝟐;𝟒)`).

* `chargeConjugation_clifford` — the Clifford defining relation `{Γ^μ, Γ^ν} = 2η^{μν}` (Eq. 2.3), from which `C`
  is built.
* `chargeConjugation_involutive` — `C² = 1` (`(Γ⁰)² = η⁰⁰𝟙 = 𝟙`): the charge-conjugation matrix is an
  **involution**, matching `C² = 1` of the discrete symmetry (`SciamaAdSCPTBulkCorrespondence.bulkC_involutive`).
* `chargeConjugation_intertwines` — `C Γ^μ C⁻¹ = η^{μμ} Γ^μ` (`Γ⁰ Γ^μ Γ⁰ = η^{μμ} Γ^μ`): conjugation by `C = Γ⁰`
  fixes the timelike `Γ⁰` and flips every spacelike `Γ^i` — the sign pattern `η^{μμ}` that reappears as the
  **coordinate reflections** `R_M` of the bulk dual `bulkC = Ω(−1)^{F_L}R_{456789}` (Eq. 1.2).

So the discrete `C` of `SciamaAdSCPTCorrespondence` has a concrete matrix realization: the real Clifford element
`Γ⁰` with `C² = 1`, whose adjoint action is the signature reflection `η^{μμ}` dual to the geometric `AdS₅×S⁵`
reflections.

Honest scope: the `4d` Dirac realization of the Clifford relation, `C = Γ⁰`, `C² = 1`, and the `η^{μμ}`
intertwining.  The full `10d` `Cliff(1,9)` Majorana–Weyl structure and the `C Γ^M C⁻¹ = ±(Γ^M)ᵀ` transpose
property are the paper's content, contextualized here in the reduced representation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCliffordChargeConjugation

open spaceTime
open spaceTime.γ

/-- **[Eq. 2.3] The charge-conjugation matrix `C = Γ⁰`** — real in the Dirac representation. -/
def chargeConjugationMatrix : Matrix (Fin 4) (Fin 4) ℂ := γ0

/-- **[Eq. 2.3, the Clifford relation] `{Γ^μ, Γ^ν} = 2η^{μν} 𝟙`.**  The defining anticommutator of the algebra
`C` is built on. -/
theorem chargeConjugation_clifford (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ =
      if μ = ν then (2 * diracMetricDiagonal μ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0 :=
  spaceTime.γ.anticommutation μ ν

/-- **[`C` is an involution] `C² = 1`.**  `(Γ⁰)² = η⁰⁰𝟙 = 𝟙` — matching `C² = 1` of the discrete symmetry. -/
theorem chargeConjugation_involutive :
    chargeConjugationMatrix * chargeConjugationMatrix = 1 := by
  unfold chargeConjugationMatrix
  exact γ0_mul_γ0

/-- **[`C Γ^μ C⁻¹ = η^{μμ} Γ^μ`] `Γ⁰ Γ^μ Γ⁰ = η^{μμ} Γ^μ`.**  Conjugation by `C = Γ⁰` fixes `Γ⁰` and flips each
spacelike `Γ^i` — the signature sign pattern `η^{μμ}` dual to the bulk coordinate reflections. -/
theorem chargeConjugation_intertwines (μ : Fin 4) :
    chargeConjugationMatrix * γ μ * chargeConjugationMatrix = diracMetricDiagonal μ • γ μ := by
  unfold chargeConjugationMatrix
  fin_cases μ <;> simp [γ, diracMetricDiagonal, γ0, γ1, γ2, γ3, Matrix.one_fin_four]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCliffordChargeConjugation

end
