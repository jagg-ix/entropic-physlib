/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSpacetime

/-!
# The combined Lorentz–electromagnetic superoperator

Constructs a *single* superoperator that combines the **spacetime Lorentz generator** and the
**electromagnetic field** into one object. Both the EM field strength `F` and a spacetime Lorentz generator
`J` (boost / rotation) are antisymmetric `4×4` matrices — elements of the Lorentz Lie algebra `𝔰𝔬(1,3)` — so
their sum `J + F` is again such an element, and its adjoint is the **combined superoperator**

  `𝒢_{J,F} = ad_{J + F} = [J + F, ·]`.

It is not a bridge but a genuine superoperator: applied to an operator it returns `[J+F, X]`; it decomposes
as `ad_J` (the spacetime infinitesimal Lorentz transformation) plus `ad_F` (the electromagnetic adjoint of
`Electromagnetic.EMFieldSuperoperator`); and the two parts *interact* — the spacetime generator `J` transforms the field `F`
by `ad_J(F) = [J, F]`, the infinitesimal Lorentz transformation of the field strength, with the cross-term
`[ad_J, ad_F] = ad_{[J,F]}`.

* **§A — the combined generator** (`emLorentzGenerator`, `emLorentzGenerator_apply`,
  `emLorentzGenerator_decompose`, `emLorentzGenerator_pure_em`, `emLorentzGenerator_pure_spacetime`).
  `𝒢_{J,F} = ad_J + ad_F`; `F = 0` recovers the pure Lorentz generator, `J = 0` the pure EM superoperator.
* **§B — the spacetime/EM interaction** (`spacetime_transforms_em`, `emLorentzGenerator_cross`).
  `ad_J(F) = [J, F]` is the Lorentz transform of the field; `[ad_J, ad_F] = ad_{[J,F]}`.
* **§C — inherited structure and spacetime covariance** (`emLorentzGenerator_leibniz`,
  `emLorentzGenerator_jacobi`, `emLorentzGenerator_trace_zero`, `emLorentzGenerator_conj`). A derivation;
  Jacobi; traceless; and Lorentz-covariant under conjugation.
* **§D — the combined time-evolution generator** (`covariantLiouvillian`, `covariantLiouvillian_apply`,
  `covariantLiouvillian_decompose`). Over `ℂ`, the Heisenberg generator of a combined Hamiltonian `H + F`
  (spacetime + EM), `𝓛_{H+F} = −i[H + F, ·] = 𝓛_H + 𝓛_F`.

## References

* The electromagnetic field strength and the Lorentz generators as common elements of `𝔰𝔬(1,3)`; the adjoint
  (Liouville/Heisenberg) action.
* Repo dependencies: `Electromagnetic.EMFieldSuperoperator` (`emFieldAdjoint`, `emLiouvillian`, the Lie structure);
  `Electromagnetic.EMSuperoperatorSpacetime` (`emFieldAdjoint_conj`, `emFieldAdjoint_trace_zero`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSpacetime

/-! ## §A — the combined Lorentz–EM generator -/

/-- **The combined superoperator** `𝒢_{J,F} = ad_{J + F}` — the adjoint of the sum of a spacetime Lorentz
generator `J` and the electromagnetic field strength `F` (both `𝔰𝔬(1,3)` elements). -/
noncomputable def emLorentzGenerator (J F : Mat) : Mat →ₗ[ℝ] Mat := emFieldAdjoint (J + F)

/-- **`𝒢_{J,F}(X) = [J + F, X]`**. -/
@[simp] theorem emLorentzGenerator_apply (J F X : Mat) :
    emLorentzGenerator J F X = (J + F) * X - X * (J + F) := by
  rw [emLorentzGenerator, emFieldAdjoint_apply]

/-- **[Combines both] `𝒢_{J,F} = ad_J + ad_F`** — the combined generator is the spacetime Lorentz adjoint
plus the electromagnetic adjoint. -/
theorem emLorentzGenerator_decompose (J F : Mat) :
    emLorentzGenerator J F = emFieldAdjoint J + emFieldAdjoint F := by
  refine LinearMap.ext fun X => ?_
  simp only [emLorentzGenerator, emFieldAdjoint_apply, LinearMap.add_apply]
  noncomm_ring

/-- **Pure electromagnetic** `𝒢_{0,F} = ad_F`. -/
theorem emLorentzGenerator_pure_em (F : Mat) : emLorentzGenerator 0 F = emFieldAdjoint F := by
  rw [emLorentzGenerator, zero_add]

/-- **Pure spacetime** `𝒢_{J,0} = ad_J` — the pure Lorentz generator. -/
theorem emLorentzGenerator_pure_spacetime (J : Mat) :
    emLorentzGenerator J 0 = emFieldAdjoint J := by
  rw [emLorentzGenerator, add_zero]

/-! ## §B — the spacetime/electromagnetic interaction -/

/-- **The spacetime generator transforms the field** `ad_J(F) = [J, F]` — the infinitesimal Lorentz
transformation of the field strength (the spacetime part acting on the electromagnetic part). -/
theorem spacetime_transforms_em (J F : Mat) : emFieldAdjoint J F = J * F - F * J :=
  emFieldAdjoint_apply J F

/-- **The cross-term** `[ad_J, ad_F] = ad_{[J,F]}` — the commutator of the spacetime and electromagnetic
superoperators is the superoperator of the Lorentz-transformed field `[J, F]`. -/
theorem emLorentzGenerator_cross (J F X : Mat) :
    emFieldAdjoint J (emFieldAdjoint F X) - emFieldAdjoint F (emFieldAdjoint J X)
      = emFieldAdjoint (emFieldAdjoint J F) X :=
  emFieldAdjoint_ad_hom J F X

/-! ## §C — inherited structure and spacetime covariance -/

/-- **`𝒢_{J,F}` is a derivation** `𝒢(XY) = 𝒢(X)·Y + X·𝒢(Y)`. -/
theorem emLorentzGenerator_leibniz (J F X Y : Mat) :
    emLorentzGenerator J F (X * Y)
      = emLorentzGenerator J F X * Y + X * emLorentzGenerator J F Y := by
  rw [emLorentzGenerator]; exact emFieldAdjoint_leibniz (J + F) X Y

/-- **The Jacobi identity** for the combined generator. -/
theorem emLorentzGenerator_jacobi (J F G X : Mat) :
    emFieldAdjoint (J + F) (emFieldAdjoint G X) + emFieldAdjoint G (emFieldAdjoint X (J + F))
      + emFieldAdjoint X (emFieldAdjoint (J + F) G) = 0 :=
  emFieldAdjoint_jacobi (J + F) G X

/-- **`Tr(𝒢_{J,F}(X)) = 0`** — the combined generator is traceless (a commutator). -/
theorem emLorentzGenerator_trace_zero (J F X : Mat) :
    (emLorentzGenerator J F X).trace = 0 := by
  rw [emLorentzGenerator]; exact emFieldAdjoint_trace_zero (J + F) X

/-- **[Lorentz covariance] `Λ · 𝒢_{J,F}(X) · Λ⁻¹ = 𝒢_{ΛJΛ⁻¹, ΛFΛ⁻¹}(ΛXΛ⁻¹)`** — the combined superoperator
transforms covariantly under a spacetime symmetry `Λ`. -/
theorem emLorentzGenerator_conj (Λ Λi J F X : Mat) (hr : Λi * Λ = 1) :
    Λ * emLorentzGenerator J F X * Λi
      = emLorentzGenerator (Λ * J * Λi) (Λ * F * Λi) (Λ * X * Λi) := by
  rw [emLorentzGenerator, emFieldAdjoint_conj Λ Λi (J + F) X hr, emLorentzGenerator_apply,
    emFieldAdjoint_apply]
  noncomm_ring

/-! ## §D — the combined time-evolution generator (`ℂ`) -/

/-- **The combined Liouville/Heisenberg generator** `𝓛_{H+F} = −i[H + F, ·]` — the unitary time evolution
under a spacetime Hamiltonian `H` together with the electromagnetic field `F`. -/
noncomputable def covariantLiouvillian (H F : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  emLiouvillian (H + F)

/-- **`𝓛_{H+F}(Y) = −i[H + F, Y]`**. -/
theorem covariantLiouvillian_apply (H F Y : Matrix (Fin 4) (Fin 4) ℂ) :
    covariantLiouvillian H F Y = -Complex.I • ((H + F) * Y - Y * (H + F)) := by
  rw [covariantLiouvillian, emLiouvillian_apply]

/-- **[Combines both] `𝓛_{H+F} = 𝓛_H + 𝓛_F`** — the combined time generator is the spacetime Hamiltonian
evolution plus the electromagnetic evolution. -/
theorem covariantLiouvillian_decompose (H F : Matrix (Fin 4) (Fin 4) ℂ) :
    covariantLiouvillian H F = emLiouvillian H + emLiouvillian F := by
  refine LinearMap.ext fun Y => ?_
  simp only [covariantLiouvillian, emLiouvillian_apply, LinearMap.add_apply]
  rw [← smul_add]; congr 1; noncomm_ring

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator

end
