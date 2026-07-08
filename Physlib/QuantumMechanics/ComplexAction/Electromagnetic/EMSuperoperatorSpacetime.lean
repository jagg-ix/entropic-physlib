/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator

/-!
# The electromagnetic superoperators and spacetime symmetry

Links the electromagnetic field superoperators of `Electromagnetic.EMFieldSuperoperator` — the adjoint `ad_F = [F, ·]`
(`emFieldAdjoint`) and the Heisenberg/Liouville time generator `𝓛_F = −i[F, ·]` (`emLiouvillian`) — to the
**spacetime symmetry** structure: the Lorentz group acting by conjugation, the PT total inversion, and the
formula-side geometric action.

The field strength `F^μ_ν` is a spacetime 2-tensor (a Lorentz Lie-algebra element), so a spacetime symmetry
`Λ` acts on it by conjugation `Λ F Λ⁻¹`. Both superoperators are then **covariant**: conjugating the
superoperator by `Λ` is the same as forming the superoperator of the transformed field — the EM
superoperators transform as the spacetime symmetry group dictates.

* **§A — Lorentz covariance of the adjoint** (`emFieldAdjoint_conj`). `Λ · ad_F(X) · Λ⁻¹ =
  ad_{ΛFΛ⁻¹}(ΛXΛ⁻¹)` — the EM superoperator intertwines with any spacetime Lorentz transformation.
* **§B — PT total inversion** (`emFieldAdjoint_faraday_pt`). Under the spacetime total inversion
  `(k, A) ↦ (−k, −A)` the field strength is invariant (`PTSymmetricQFT.MaxwellFaraday.faraday_pt`,
  `(−1)² = +1`), so the EM superoperator is unchanged — the rank-2 `F` is PT-even.
* **§C — Lorentz scalar / conservation** (`emFieldAdjoint_trace_zero`). `Tr(ad_F X) = 0` — the trace (a
  Lorentz scalar) of a commutator vanishes by cyclicity, the same cyclicity that underlies the matter /
  Bianchi conservation (`GravitationalFieldEquations.MatterConservationDivergenceFree`).
* **§D — covariance of the time generator** (`emLiouvillian_conj`). The Heisenberg/Liouville generator
  `𝓛_F = −i[F, ·]` is Lorentz-covariant too (`Λ · 𝓛_F(Y) · Λ⁻¹ = 𝓛_{ΛFΛ⁻¹}(ΛYΛ⁻¹)`); the central `−i`
  passes through the conjugation. This is the matrix realization of the formula-side equivariance
  `PTSymmetricQFT.FieldSuperoperator.fieldAdjoint_conj` (`σ ∘ ad_X ∘ σ⁻¹ = ad_{σX}` under the geometric
  action `σ(g)`) — both superoperators are covariant under their spacetime symmetry group.

## References

* The electromagnetic field strength as a spacetime 2-tensor / Lorentz Lie-algebra element; the Lorentz
  covariance of operator (super)operators.
* Repo dependencies: `Electromagnetic.EMFieldSuperoperator` (`emFieldAdjoint`, `emLiouvillian`);
  `PTSymmetricQFT.MaxwellFaraday.faraday_pt` (PT total inversion);
  `PTSymmetricQFT.FieldSuperoperator.fieldAdjoint_conj` (the formula-side geometric-action equivariance).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSpacetime

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator

/-! ## §A — Lorentz covariance of the EM adjoint superoperator -/

/-- **[Lorentz covariance] `Λ · ad_F(X) · Λ⁻¹ = ad_{ΛFΛ⁻¹}(ΛXΛ⁻¹)`.** A spacetime symmetry `Λ` (any
invertible transformation, `Λ⁻¹Λ = 1`) intertwines the EM superoperator: conjugating `ad_F` by `Λ` gives the
superoperator of the Lorentz-transformed field — the EM superoperator is a spacetime-covariant object. -/
theorem emFieldAdjoint_conj (Λ Λi F X : Mat) (hr : Λi * Λ = 1) :
    Λ * emFieldAdjoint F X * Λi = emFieldAdjoint (Λ * F * Λi) (Λ * X * Λi) := by
  simp only [emFieldAdjoint_apply]
  have key : ∀ P Q : Mat, (Λ * P * Λi) * (Λ * Q * Λi) = Λ * (P * Q) * Λi := fun P Q => by
    rw [show (Λ * P * Λi) * (Λ * Q * Λi) = Λ * P * (Λi * Λ) * Q * Λi by noncomm_ring, hr]
    noncomm_ring
  rw [key F X, key X F]; noncomm_ring

/-! ## §B — the spacetime PT total inversion -/

/-- **[PT total inversion] The EM superoperator is PT-even.** Under the spacetime total inversion
`(k, A) ↦ (−k, −A)` the field strength is invariant (`faraday_pt`, `(−1)² = +1` on the rank-2 `F`), so the
generated superoperator is unchanged. -/
theorem emFieldAdjoint_faraday_pt (k A : Fin 4 → ℝ) :
    emFieldAdjoint (faraday (-k) (-A)) = emFieldAdjoint (faraday k A) := by
  rw [faraday_pt]

/-! ## §C — the Lorentz-scalar trace and conservation -/

/-- **[Conservation / cyclicity] `Tr(ad_F X) = 0`.** The trace — a Lorentz scalar — of the commutator
`[F, X]` vanishes by cyclicity (`Tr(FX) = Tr(XF)`). This is the same trace-cyclicity that underlies matter /
Bianchi conservation. -/
theorem emFieldAdjoint_trace_zero (F X : Mat) : (emFieldAdjoint F X).trace = 0 := by
  rw [emFieldAdjoint_apply, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-! ## §D — covariance of the EM time-evolution generator -/

/-- **[Lorentz covariance of the Heisenberg generator] `Λ · 𝓛_F(Y) · Λ⁻¹ = 𝓛_{ΛFΛ⁻¹}(ΛYΛ⁻¹)`.** The EM
Liouville / time-evolution generator `𝓛_F = −i[F, ·]` is Lorentz-covariant; the central `−i` passes through
the conjugation. This is the matrix realization of `PTSymmetricQFT.FieldSuperoperator.fieldAdjoint_conj` — the
formula-side equivariance of the adjoint superoperator under the geometric action `σ(g)`. -/
theorem emLiouvillian_conj (Λ Λi F Y : Matrix (Fin 4) (Fin 4) ℂ) (hr : Λi * Λ = 1) :
    Λ * emLiouvillian F Y * Λi = emLiouvillian (Λ * F * Λi) (Λ * Y * Λi) := by
  rw [emLiouvillian_apply, emLiouvillian_apply]
  have key : ∀ P Q : Matrix (Fin 4) (Fin 4) ℂ, (Λ * P * Λi) * (Λ * Q * Λi) = Λ * (P * Q) * Λi :=
    fun P Q => by
      rw [show (Λ * P * Λi) * (Λ * Q * Λi) = Λ * P * (Λi * Λ) * Q * Λi by noncomm_ring, hr]
      noncomm_ring
  rw [key F Y, key Y F, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  noncomm_ring

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSpacetime

end
