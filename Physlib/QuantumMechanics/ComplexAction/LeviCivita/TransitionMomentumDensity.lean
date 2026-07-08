/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionGeneralRelativity
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen

/-!
# The transition-to-GR force ratio is the momentum density (§2 ↔ §5 ↔ the complex action)

Links Levi-Civita's **§5 transition to general relativity**
(`LeviCivita.TransitionGeneralRelativity`, the physical energy-tensor ratios) to the **relativistic
momentum-density vector** (`LeviCivita.MomentumDensityNagaoNielsen`, `relMomentumDensity = T *ᵥ u`), closing
a loop back to §2 of the same paper.

Levi-Civita's §2 identifies the time–space components of the energy tensor with the **momentum density**:
`T_0i = T_i0 = −c qᵢ` (`q` the momentum density vector). The §5 **force / energy-flow ratio**
`forceRatio = T_0i/√(−g₀₀gᵢᵢ)` is therefore the physically-normalized momentum density. This file proves
that identification through the momentum-density formalism:

* the **rest-frame four-velocity** `u = e₀` (`restFourVelocity`, the time basis) contracts the energy
  tensor to its `T_·0` column, whose spatial part is the momentum density
  (`restMomentumDensity_apply`: `relMomentumDensity T e₀ (inr i) = T_i0`);
* on the flat (Minkowski) metric the **force ratio equals that momentum density**
  (`forceRatio_eq_momentumDensity`, using `T` symmetric `T_0i = T_i0`): the §5 force/energy-flow ratio is
  the rest-frame relativistic momentum density of §2;
* and that momentum density is the **real (reversible) sector of the complex momentum density**
  `q_ℂ = (T + iS) *ᵥ u` of the Nagao–Nielsen complex action
  (`relMomentumDensity = Re q_ℂ`, `complexMomentumDensity_re`): the §5 matter energy tensor `T` is the
  real sector, the entropic stress `S` the imaginary sector.

So the §5 transition's force/energy-flow ratio, the §2 momentum density, and the real sector of the
complex-action/entropic-time complex momentum density are one quantity — the locally-measured momentum current that, in the
Euclidean limit, is the bare special-relativistic `T_0i`, and in general relativity is the metric ratio.

* **§A — the rest-frame momentum density is the `T_·0` column** (`restFourVelocity`,
  `restMomentumDensity_apply`).
* **§B — the §5 force ratio is the momentum density (real sector of the complex action)**
  (`forceRatio_eq_momentumDensity`, `leviCivita_transition_momentumDensity`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §2 `T_0i = −c qᵢ`, §5). structures:
  `LeviCivita.TransitionGeneralRelativity` (`forceRatio`, `forceRatio_minkowski`),
  `LeviCivita.MomentumDensityNagaoNielsen` (`relMomentumDensity`, `complexMomentumDensity`,
  `complexMomentumDensity_re`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionMomentumDensity

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionGeneralRelativity
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.MomentumDensityNagaoNielsen
open Matrix

variable {d : ℕ}

/-! ## §A — the rest-frame momentum density is the `T_·0` column -/

/-- **The rest-frame four-velocity** `u = e₀` — the time basis vector, the four-velocity of an observer at
rest in the `x₀` direction. -/
def restFourVelocity : Fin 1 ⊕ Fin d → ℝ := Pi.single (Sum.inl 0) 1

/-- **[The rest-frame momentum density is the `T_i0` component] `(T *ᵥ e₀)_i = T_i0`.** Contracting the
energy tensor with the rest-frame four-velocity selects the `T_·0` column; its spatial component is the
momentum density `T_i0` of Levi-Civita §2 (`T_i0 = −c qᵢ`). -/
theorem restMomentumDensity_apply (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (i : Fin d) :
    relMomentumDensity T restFourVelocity (Sum.inr i) = T (Sum.inr i) (Sum.inl 0) := by
  simp [relMomentumDensity, restFourVelocity, Matrix.mulVec_single]

/-! ## §B — the §5 force ratio is the momentum density (real sector of the complex action) -/

/-- **[The §5 force/energy-flow ratio is the rest-frame momentum density] `T_0i/√(−η₀₀ηᵢᵢ) = (T *ᵥ e₀)_i`.**
On the flat metric the force ratio reduces to the bare component `T_0i` (`forceRatio_minkowski`), which for
a symmetric energy tensor (`T_0i = T_i0`) is the spatial momentum density `(T *ᵥ e₀)_i` of §2. The §5
transition's force/energy-flow ratio is the relativistic momentum density. -/
theorem forceRatio_eq_momentumDensity (T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (hT : Tᵀ = T) (i : Fin d) :
    forceRatio T minkowskiMatrix i = relMomentumDensity T restFourVelocity (Sum.inr i) := by
  have hsym : T (Sum.inl 0) (Sum.inr i) = T (Sum.inr i) (Sum.inl 0) := by
    have h := congrFun (congrFun hT (Sum.inr i)) (Sum.inl 0)
    rwa [Matrix.transpose_apply] at h
  rw [forceRatio_minkowski, restMomentumDensity_apply, hsym]

/-- **[The §5 transition's energy tensor is the momentum density and the real sector of the complex action].**
For a symmetric energy tensor `T` and the entropic stress `S`:

* the §5 force/energy-flow ratio is the rest-frame relativistic momentum density,
  `T_0i/√(−η₀₀ηᵢᵢ) = (T *ᵥ e₀)_i` (Levi-Civita §2, `T_0i = −c qᵢ`);
* that momentum density is the real sector of the Nagao–Nielsen complex momentum density,
  `(T *ᵥ e₀)_i = Re q_ℂ_i`, with `S` the imaginary (entropic) sector;
* the stress and energy-density ratios reduce to the bare special-relativistic components
  `T_ik` and `T₀₀`.

So §5's force/energy-flow ratio, §2's momentum density, and the real sector of the complex-action/entropic-time complex
momentum density are one locally-measured quantity — the bare `T_0i` in the Euclidean limit, the metric
ratio in general relativity. -/
theorem leviCivita_transition_momentumDensity
    (T S : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hT : Tᵀ = T) (i k : Fin d) :
    forceRatio T minkowskiMatrix i = relMomentumDensity T restFourVelocity (Sum.inr i)
      ∧ relMomentumDensity T restFourVelocity (Sum.inr i)
          = (complexMomentumDensity T S restFourVelocity (Sum.inr i)).re
      ∧ stressRatio T minkowskiMatrix i k = T (Sum.inr i) (Sum.inr k)
      ∧ energyDensityRatio T minkowskiMatrix = T (Sum.inl 0) (Sum.inl 0) :=
  ⟨forceRatio_eq_momentumDensity T hT i,
    (complexMomentumDensity_re T S restFourVelocity (Sum.inr i)).symm,
    stressRatio_minkowski T i k, energyDensityRatio_minkowski T⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.TransitionMomentumDensity

end
