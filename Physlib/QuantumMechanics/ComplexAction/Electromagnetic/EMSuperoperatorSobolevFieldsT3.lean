/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The combined EM–spacetime superoperator on Sobolev-valued fields over `T³`

Makes the combined Lorentz–electromagnetic superoperator `𝒢_{J,F} = ad_{J+F}`
(`Electromagnetic.EMLorentzCombinedSuperoperator.emLorentzGenerator`) act on **actual function-space fields** — operator-valued
fields over the 3-torus `T³`, in the Sobolev/`Lᵖ` setting of the Dual-Sphere-Fiber kernel
(`Hopf.DualSphereSobolevPerfectSquare`). The operator space `Mat = Matrix (Fin 4) (Fin 4) ℝ` is finite-dimensional,
so the superoperator is a **continuous** linear map (here given the `ℓ∞`-operator norm), and a continuous
linear map lifts cleanly to fields: smoothness is preserved, and it descends to a bounded operator on `Lᵖ`.

* **§A — the superoperator as a continuous linear map** (`emSpacetimeCLM`, `emSpacetimeCLM_apply`).
  `emSpacetimeCLM J F = ad_{J+F} : Mat →L[ℝ] Mat`, with `emSpacetimeCLM J F X = (J+F)X − X(J+F)`.
* **§B — smoothness on `T³` fields** (`emSpacetime_preserves_contDiff`). For an operator-valued field
  `A : ℝ³ → Mat` (the universal cover of `T³`), if `A` is smooth then so is `x ↦ 𝒢_{J,F}(A(x))` — the
  superoperator maps smooth fields to smooth fields. The domain dimension `3` is the dimension whose
  critical Sobolev exponent is `6` and whose Hölder dual is the `6/5` of `Hopf.DualSphereSobolevPerfectSquare`.
* **§C — `Lᵖ`/Sobolev fields on `T³`** (`emSpacetimeLp`, `emSpacetimeLp_zero`). The superoperator descends to
  a bounded linear operator on `Lᵖ(T³, Mat)` (`ContinuousLinearMap.compLp`); it is linear, sending `0 ↦ 0`.

## References

* `ContinuousLinearMap.compLp` (bounded operators act on `Lᵖ`); the critical Sobolev embedding
  `H¹(ℝ³) ↪ L⁶` and its `6/5` dual.
* Repo dependencies: `Electromagnetic.EMLorentzCombinedSuperoperator` (`emLorentzGenerator`);
  `Hopf.DualSphereSobolevPerfectSquare` (`sobolevConjugate_three`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSobolevFieldsT3

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open MeasureTheory

-- The `ℓ∞`-operator norm on the operator space, so that the finite-dimensional superoperator becomes a
-- *continuous* linear map (a local instance — not a global default, to avoid a norm diamond on `Matrix`).
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

/-! ## §A — the combined EM–spacetime superoperator as a continuous linear map -/

/-- **The combined EM–spacetime superoperator as a bounded operator** `𝒢_{J,F} = ad_{J+F} : Mat →L[ℝ] Mat`.
Finite-dimensionality makes the adjoint superoperator continuous. -/
noncomputable def emSpacetimeCLM (J F : Mat) : Mat →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap (emLorentzGenerator J F)

/-- **`𝒢_{J,F}(X) = (J+F)X − X(J+F)`** as a continuous map. -/
@[simp] theorem emSpacetimeCLM_apply (J F X : Mat) :
    emSpacetimeCLM J F X = (J + F) * X - X * (J + F) :=
  emLorentzGenerator_apply J F X

/-! ## §B — smoothness on `T³ ≅ ℝ³` fields -/

/-- **[Smoothness preserved] The superoperator maps smooth operator-valued fields to smooth ones.** For a
field `A : ℝ³ → Mat` over the universal cover of `T³`, smoothness of `A` implies smoothness of
`x ↦ 𝒢_{J,F}(A(x))` — composition with the continuous linear superoperator. -/
theorem emSpacetime_preserves_contDiff (J F : Mat)
    (A : EuclideanSpace ℝ (Fin 3) → Mat) (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => emLorentzGenerator J F (A x)) :=
  (emSpacetimeCLM J F).contDiff.comp hA

/-! ## §C — `Lᵖ`/Sobolev fields on `T³` -/

/-- **[Bounded operator on `Lᵖ`] The EM–spacetime superoperator acts on `Lᵖ(T³, Mat)`.** As a bounded
linear map it descends, via `ContinuousLinearMap.compLp`, to a bounded operator on the `Lᵖ` (Sobolev)
fields over the 3-torus. -/
noncomputable def emSpacetimeLp {Ω : Type*} [MeasureSpace Ω] (p : ENNReal) (J F : Mat)
    (A : Lp Mat p (volume : Measure Ω)) : Lp Mat p (volume : Measure Ω) :=
  (emSpacetimeCLM J F).compLp A

/-- **The `Lᵖ` operator is a.e. the pointwise superoperator** `(emSpacetimeLp p J F A)(x) = 𝒢_{J,F}(A(x))`
almost everywhere — the `Lᵖ` lift acts by the EM–spacetime superoperator pointwise. -/
theorem emSpacetimeLp_ae {Ω : Type*} [MeasureSpace Ω] (p : ENNReal) (J F : Mat)
    (A : Lp Mat p (volume : Measure Ω)) :
    emSpacetimeLp p J F A =ᵐ[(volume : Measure Ω)] fun x => emSpacetimeCLM J F (A x) :=
  (emSpacetimeCLM J F).coeFn_compLp A

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSobolevFieldsT3

end
