/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-!
# Winding-number quantum numbers on the actual fermionic field operators (Fock realization)

The winding-number / topological-charge picture carries three fermionic quantum numbers at the
*scalar/algebraic* layer: charge = winding (`Hopf.ChargeConjugationRibbonTwist.qCharacter`), spin-statistics =
ribbon twist
(`ribbonTwist (1/2) = −1`), and Pauli volume (`EntangledRegionFrequencyTimeDilation.pauliRegionSize`,
`fermiDirac < 1`). This file lifts all three onto the **actual fermionic field operators** of
`Fermion.FockFunctor` (`Fock M = ExteriorAlgebra ℝ M`, `creationOp = ι m·`, the CAR `car`,
Pauli `creationOp_sq`), so each scalar quantum number becomes a theorem about `creationOp`.

* **§A — creation is one-particle linear.** `creationOp_smul`, `creationOp_add`: `a†` is linear in the
  one-particle vector (needed for the charge grading and statistics).
* **§B — spin-statistics on the operators.** `creationOp_anticomm`: `{a†(m), a†(m')} = 0` (from the exterior
  `ι_mul_ι_add_swap` at `Q = 0`); `creationOp_swap`: `a†(m)a†(m') = − a†(m')a†(m)`; and the bridge
  `creationOp_swap_eq_ribbon`: the operator **swap sign is the spin-½ ribbon twist**,
  `a†(m)a†(m') = (ribbonTwist ½).re · a†(m')a†(m)` — the abstract framing `θ(½) = −1` realized as the
  concrete fermionic minus sign. `creationOp_sq` (`a†² = 0`, `Fermion.FockFunctor`) is the same-mode Pauli
  exclusion that is the operator root of the additive `pauliRegionSize` and of `fermiDirac < 1`.
* **§C — charge = number grading.** `secondQuant_scalar_creationOp`: the U(1) action
  `Γ(c·id)` scales each creation by `c` (`Γ(c·id) a†(m) = c · a†(m) Γ(c·id)`), so an `n`-creation state
  scales by `cⁿ` — the charge-`n` eigenvalue, the operator realization of `qCharacter Q : tⁿ ↦ Qⁿ` and of
  the additive charge law `chargeState_mul`.

**Honest layering.** Genuine operator theorems: §A–§C are exact facts about `creationOp` on the exterior
algebra. The identifications "`a†` swap sign = `ribbonTwist ½`" (§B) and "`Γ(c·id)`
scaling = `qCharacter`" (§C) are the bridges that make the scalar winding-number quantum numbers
operator-valued. The mass leg (`comptonMass` ↔ `diracEnergy`) and the entanglement/entropic-time leg
(`MState` + `entropicGap`) are separate integrations, not in this file.

## References

* `Physlib` (`Fermion.FockFunctor` `creationOp`/`car`/`creationOp_sq`,
  `Hopf.ChargeConjugationRibbonTwist` `ribbonTwist`/`qCharacter`). Mathlib `CliffordAlgebra.ι_mul_ι_add_swap`.


-/

set_option autoImplicit false

open CliffordAlgebra
open Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Winding.ChargeFockRealization

variable {M : Type*} [AddCommGroup M] [Module ℝ M]


/-- **[Creation is scalar-linear]** `a†(c·m) = c·a†(m)` — the creation operator is `ℝ`-linear in the
one-particle vector. -/
lemma creationOp_smul (c : ℝ) (m : M) (x : Fock M) :
    creationOp (c • m) x = c • creationOp m x := by
  simp only [creationOp, map_smul, smul_mul_assoc]

/-- **[Creation is additive]** `a†(m + m') = a†(m) + a†(m')`. -/
lemma creationOp_add (m m' : M) (x : Fock M) :
    creationOp (m + m') x = creationOp m x + creationOp m' x := by
  simp only [creationOp, map_add, add_mul]


/-- **[Creation operators anticommute]** `{a†(m), a†(m')} = 0`: the canonical fermionic anticommutation of
two creation operators, from the exterior-algebra symmetric product `ι m·ι m' + ι m'·ι m = 0` at `Q = 0`. -/
lemma creationOp_anticomm (m m' : M) (x : Fock M) :
    creationOp m (creationOp m' x) + creationOp m' (creationOp m x) = 0 := by
  simp only [creationOp]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ι_mul_ι_add_swap]
  simp [QuadraticMap.polar]

/-- **[Creation swap]** `a†(m) a†(m') = − a†(m') a†(m)`. -/
lemma creationOp_swap (m m' : M) (x : Fock M) :
    creationOp m (creationOp m' x) = - creationOp m' (creationOp m x) :=
  eq_neg_of_add_eq_zero_left (creationOp_anticomm m m' x)

/-- **[Spin-statistics: the swap sign is the spin-½ ribbon twist]** `a†(m) a†(m') = (ribbonTwist ½).re ·
a†(m') a†(m)`: the operator anticommutation minus sign of the fermionic field is exactly the topological
spin factor `ribbonTwist (1/2) = −1`. The abstract framing becomes the concrete fermionic sign. -/
lemma creationOp_swap_eq_ribbon (m m' : M) (x : Fock M) :
    creationOp m (creationOp m' x) = (ribbonTwist (1 / 2)).re • creationOp m' (creationOp m x) := by
  rw [ribbonTwist_fermion]
  simp only [Complex.neg_re, Complex.one_re, neg_smul, one_smul]
  exact creationOp_swap m m' x

/-- **[Same-mode Pauli exclusion]** `a†(m)² = 0` (`Fermion.FockFunctor.creationOp_sq`): two fermions cannot
occupy the same mode — the operator root of the additive Pauli volume (`pauliRegionSize`) and of the bounded
occupation `fermiDirac < 1`. -/
lemma pauli_same_mode (m : M) (x : Fock M) : creationOp m (creationOp m x) = 0 :=
  creationOp_sq m x


/-- **[The U(1) charge action scales each creation by `c`]** `Γ(c·id) a†(m) = c · a†(m) Γ(c·id)`: the
second-quantized scalar `c·id` multiplies every creation operator by `c`, so an `n`-creation (charge-`n`)
state is scaled by `cⁿ` — the operator realization of the winding charge `qCharacter Q : tⁿ ↦ Qⁿ` and of the
additive charge law `chargeState_mul`. -/
lemma secondQuant_scalar_creationOp (c : ℝ) (m : M) (x : Fock M) :
    secondQuant (c • LinearMap.id) (creationOp m x)
      = c • creationOp m (secondQuant (c • LinearMap.id) x) := by
  rw [secondQuant_creationOp]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, creationOp_smul]

end Physlib.QuantumMechanics.ComplexAction.Winding.ChargeFockRealization

end
