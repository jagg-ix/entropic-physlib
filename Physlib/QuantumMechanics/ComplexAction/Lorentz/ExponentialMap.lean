/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.BoostGenerator
public import Physlib.Relativity.LorentzAlgebra.ExponentialMap
public import Physlib.Relativity.LorentzAlgebra.Basis

/-!
# The arc's boost generator exponentiates to a Lorentz transformation (the exponential map)

Uses PhysLean's standard **Lorentz-algebra exponential map** (`Physlib.Relativity.LorentzAlgebra`,
`exp_mem_lorentzGroup` / `exp_mem_restricted_lorentzGroup`), which the arc had left floating, on the
boost generator whose `(t, xᵢ)` block is the arc's Bogoliubov boost generator
(`Lorentz.BoostGenerator.bogoliubovGenerator_eq_boostGenerator_block`).

The boost generator `lorentzAlgebra.boostGenerator i` is a member of the Lorentz algebra `𝔰𝔬(1,3)`
(`boostGenerator_mem`), so its matrix exponential `NormedSpace.exp (boostGenerator i)` is a **proper
orthochronous Lorentz transformation** (`boostGenerator_exp_restricted`, via PhysLean's
`exp_mem_restricted_lorentzGroup`). Since the `(t, xᵢ)` block of `boostGenerator i` is the arc's
`bogoliubovGenerator`, the arc's Bogoliubov boost is the `(1+1)` restriction of this exponentiated
`𝔰𝔬(1,3)` boost — `boost = exp(generator)` realized through the standard exponential map.

* **§A — the generator exponentiates into the Lorentz group**
  (`boostGenerator_exp_mem_lorentzGroup`, `boostGenerator_exp_restricted`).
* **§B — the link to the arc** (`arc_boostGenerator_exponentiates`).

So `LorentzAlgebra/ExponentialMap` is no longer floating: it is the algebra→group exponential of the
boost generator carrying the arc's Bogoliubov boost.

**Scope note.** The *explicit value* `NormedSpace.exp (η • bogoliubovGenerator) = thermoBogoliubov η`
(the closed-form `cosh η · 1 + sinh η · K` of the `2×2` matrix exponential of the involution `K² = 1`)
is a separate analytic computation — the hyperbolic analogue of Mathlib's quaternion exponential
(`expSeries` even/odd `cosh`/`sinh` split) — and is left as the remaining piece; here the link is the
*structural* one (membership + proper orthochronicity) that genuinely consumes `exp_mem_*`.

## References

* PhysLean: `Physlib.Relativity.LorentzAlgebra.ExponentialMap` (`exp_mem_lorentzGroup`,
  `exp_mem_restricted_lorentzGroup`), `LorentzAlgebra/Basis` (`boostGenerator`, `boostGenerator_mem`).
  Repo carrier: `Lorentz.BoostGenerator`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ExponentialMap

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open lorentzAlgebra


/-- **[The boost generator exponentiates into the Lorentz group] `exp(B_i) ∈ O(1,3)`.** The `𝔰𝔬(1,3)`
boost generator `boostGenerator i` (`boostGenerator_mem`) exponentiates, via PhysLean's standard
Lorentz-algebra exponential map (`exp_mem_lorentzGroup`), to a Lorentz transformation. -/
lemma boostGenerator_exp_mem_lorentzGroup (i : Fin 3) :
    NormedSpace.exp (boostGenerator i) ∈ LorentzGroup 3 :=
  exp_mem_lorentzGroup ⟨boostGenerator i, boostGenerator_mem i⟩

/-- **[The exponentiated boost is proper orthochronous] `exp(B_i) ∈ SO⁺(1,3)`.** The matrix
exponential of the boost generator is a **restricted** (proper, orthochronous) Lorentz transformation
(`exp_mem_restricted_lorentzGroup`) — a genuine boost in the identity component. -/
lemma boostGenerator_exp_restricted (i : Fin 3) :
    (⟨NormedSpace.exp (boostGenerator i), boostGenerator_exp_mem_lorentzGroup i⟩ : LorentzGroup 3)
      ∈ LorentzGroup.restricted 3 :=
  exp_mem_restricted_lorentzGroup ⟨boostGenerator i, boostGenerator_mem i⟩


/-- **[The arc's Bogoliubov boost is the exponentiated `𝔰𝔬(1,3)` boost generator].** The `(t, xᵢ)`
off-diagonal of `boostGenerator i` is the arc's `bogoliubovGenerator` (the `2×2` boost generator
`[[0,1],[1,0]]`, `Lorentz.BoostGenerator`), and `boostGenerator i` exponentiates via PhysLean's
exponential map to a proper orthochronous Lorentz transformation. So the arc's Bogoliubov boost
`thermoBogoliubov = exp(η · K)` is the `(1+1)` restriction of the standard `boost = exp(generator)`. -/
lemma arc_boostGenerator_exponentiates (i : Fin 3) :
    lorentzAlgebra.boostGenerator i (Sum.inl 0) (Sum.inr i) = bogoliubovGenerator 0 1
      ∧ NormedSpace.exp (boostGenerator i) ∈ LorentzGroup 3
      ∧ (⟨NormedSpace.exp (boostGenerator i), boostGenerator_exp_mem_lorentzGroup i⟩ :
            LorentzGroup 3) ∈ LorentzGroup.restricted 3 :=
  ⟨(Lorentz.BoostGenerator.bogoliubovGenerator_eq_boostGenerator_block i).2.1,
    boostGenerator_exp_mem_lorentzGroup i, boostGenerator_exp_restricted i⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ExponentialMap

end
