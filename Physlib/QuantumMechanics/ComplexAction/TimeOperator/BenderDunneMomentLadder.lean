/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment

/-!
# The Bender–Dunne moment ladder: the `r`-moment time-operator domain

The general moment-domain structure of the Bender–Dunne time-of-arrival operators `T_{−m,n}` (Bunao & Galapon,
arXiv:1509.00340, §3): the operator maps a vector into `L²` only when its **first several moments vanish**. The
`j`-th moment `∫ qʲ φ` is the linear functional weighted by the `j`-th power of the (possibly Nagao–Nielsen
complex) coordinate `q`; the domain is the joint kernel of the first `r` of them, `⨅_{j<r} ker(∫qʲ·)`.

This unifies the whole time-operator domain ladder as instances of one construction:

* `r = 1` — the **zeroth moment** `∫φ = 0`: the CTO canonical domain (`TimeEnergyCCRMultipleSolutions.sumForm`);
* `r = 2` — **zeroth and first** `∫φ = 0 ∧ ∫qφ = 0`: the `T_{−1,1}` / Nagao–Nielsen domain
  (`NagaoNielsenBenderDunneComplexMoment.nnBenderDunneDomain`);
* general `r` — the higher `T_{−m,n}` needing `r` moment conditions.

* **§A — the `j`-th moment functional.** `momentForm q j φ = ∑_k q_k^j φ_k`; **`momentForm_zero_apply`**
  (`= ∑ φ`, the zeroth moment) and the connections **`momentForm_zero_eq_sumForm`** (`= sumForm`) and
  **`momentForm_one_eq_nnMomentForm`** (`= nnMomentForm q`, the NN complex first moment).
* **§B — the `r`-moment domain.** `benderDunneMomentDomain q r = ⨅_{j : Fin r} ker(momentForm q j)`;
  **`mem_benderDunneMomentDomain_iff`** (`∈ ↔ ∀ j < r, ∑_k q_k^j φ_k = 0`), the vanishing of the first `r` moments.

**Honest layering.** All are exact `LinearMap`/`Finset`/`Submodule` identities over an arbitrary field (so the
Nagao–Nielsen complex coordinate `q ∈ ℂⁿ` is a special case). The `L²(ℝ)` square-integrability and the number of
moment conditions actually required for a given `T_{−m,n}` are the paper's analytic results; here the domain is the
exact joint moment kernel.

## References

* Bunao & Galapon, arXiv:1509.00340 (2015), §3. Generalizes `TimeOperator.BenderDunneTimeOperatorDomain` and
  `NagaoNielsenBenderDunneComplexMoment`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneMomentLadder

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}


/-- The **`j`-th moment functional** `φ ↦ ∑_k q_k^j φ_k` — the `∫ qʲ φ` moment weighted by the `j`-th power of the
coordinate `q` (real, or Nagao–Nielsen complex), as a `𝕜`-linear map. -/
noncomputable def momentForm (q : Fin n → 𝕜) (j : ℕ) : (Fin n → 𝕜) →ₗ[𝕜] 𝕜 where
  toFun φ := ∑ k, (q k) ^ j * φ k
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma momentForm_apply (q : Fin n → 𝕜) (j : ℕ) (φ : Fin n → 𝕜) :
    momentForm q j φ = ∑ k, (q k) ^ j * φ k := rfl

/-- **The zeroth moment is the sum** `momentForm q 0 φ = ∑ φ` (`q_k^0 = 1`). -/
lemma momentForm_zero_apply (q φ : Fin n → 𝕜) : momentForm q 0 φ = ∑ k, φ k := by
  simp [momentForm_apply]

/-- **The zeroth moment is `sumForm`** — the `r = 1` case is the CTO canonical domain functional. -/
lemma momentForm_zero_eq_sumForm (q : Fin n → ℂ) : momentForm q 0 = sumForm := by
  ext φ; simp [momentForm_apply, sumForm_apply]

/-- **The first moment is `nnMomentForm`** — the `r = 2` case adds the Nagao–Nielsen complex first moment. -/
lemma momentForm_one_eq_nnMomentForm (q : Fin n → ℂ) : momentForm q 1 = nnMomentForm q := by
  ext φ; simp [momentForm_apply, nnMomentForm_apply]


/-- The **`r`-moment Bender–Dunne domain** `⨅_{j<r} ker(∫qʲ·) = {φ : ∀ j < r, ∑_k q_k^j φ_k = 0}` — the domain of
`T_{−m,n}` as the joint kernel of the first `r` moment functionals; `r = 1` is `canonicalDomain`, `r = 2` is
`nnBenderDunneDomain`. -/
noncomputable def benderDunneMomentDomain (q : Fin n → 𝕜) (r : ℕ) : Submodule 𝕜 (Fin n → 𝕜) :=
  ⨅ j : Fin r, LinearMap.ker (momentForm q (j : ℕ))

/-- **Membership is the vanishing of the first `r` moments** `φ ∈ benderDunneMomentDomain q r ↔
∀ j < r, ∑_k q_k^j φ_k = 0`. -/
lemma mem_benderDunneMomentDomain_iff (q : Fin n → 𝕜) (r : ℕ) (φ : Fin n → 𝕜) :
    φ ∈ benderDunneMomentDomain q r ↔ ∀ j : Fin r, ∑ k, (q k) ^ (j : ℕ) * φ k = 0 := by
  simp [benderDunneMomentDomain, Submodule.mem_iInf, LinearMap.mem_ker, momentForm_apply]

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneMomentLadder
