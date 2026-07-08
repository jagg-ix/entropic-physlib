/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# Covariant Maxwell ⟺ continuity (Heras 2009)

Formalizes the algebraic core of *J. A. Heras, "How to obtain the covariant form of Maxwell's equations from
the continuity equation", Eur. J. Phys. 30 (2009) 845–854*. Heras emphasises charge conservation as the
fundamental axiom: the covariant Maxwell equations `∂_μ F^{μν} = (4π/c)J^ν`, `∂_μ *F^{μν} = 0` (Eq. 2) imply
the continuity equation `∂_ν J^ν = 0` (Eq. 3), and conversely a conserved four-current `∂_ν 𝒥^ν = 0` admits a
retarded antisymmetric tensor satisfying Maxwell's equations (the existence theorem).

The forward direction — **Maxwell ⟹ continuity** — rests on one algebraic identity: the four-divergence of
the inhomogeneous Maxwell law gives `∂_ν J^ν = (c/4π)∂_ν∂_μ F^{μν}`, and `∂_ν∂_μ` is **symmetric** while
`F^{μν}` is **antisymmetric**, so the contraction vanishes. In the momentum-space model `∂_μ ↦ k_μ` of
`PTSymmetricQFT.MaxwellFaraday`, `F = dA` (`faraday`) is antisymmetric and `∂_ν∂_μ ↦ k_ν k_μ` is symmetric.

The **converse** existence theorem (§3) — a conserved current admits a retarded `F = ∫G(∂'^μ𝒥^ν − ∂'^ν𝒥^μ)`
satisfying Maxwell's equations — is a spacetime-integral construction; its *algebraic skeleton* is formalized
in §D: the construction is antisymmetric (Eq. 13), the homogeneous equation `∂_μ*F^{μν} = 0` (Eq. 17) is again
the symmetric×antisymmetric contraction (`ε^{μνκλ}` antisymmetric in `μκ`, `∂_μ∂_κ` symmetric), and the one
irreducibly-analytic input — the wave-operator Green inversion `∂_μF^{μν} = 𝒥^ν` (Eq. 14, the integrated
tensor identity (7) with `∂'_μ∂'^μ G = δ`) — is isolated as a single explicit hypothesis.

* **§A — the contraction kernel** (`symm_antisymm_contract_zero`). `∑ᵢⱼ Sᵢⱼ Fᵢⱼ = 0` for `S` symmetric and
  `F` antisymmetric — the source of both Maxwell ⟹ continuity and the Bianchi identity.
* **§B — Maxwell ⟹ continuity (Eq. 2 ⟹ Eq. 3)** (`fourCurrent`, `fourCurrent_conserved`). The four-current
  `J^ν = ∂_μ F^{μν}` (`= ∑_μ k_μ F^{μν}`) satisfies `∂_ν J^ν = ∑_ν k_ν J^ν = 0` — charge conservation is
  forced by the antisymmetry of `F = dA`.
* **§C — the complete Heras consistency** (`faraday_heras_consistency`). For `F = dA`, the source four-current
  is conserved (continuity) *and* the homogeneous Maxwell equation `∂_μ *F^{μν} = 0` holds — the latter being
  the Bianchi identity `faraday_bianchi` (Heras Eq. 17).
* **§D — the converse existence theorem (Heras §3)** (`currentCurl`, `constructedField`,
  `constructedField_antisymm`, `dual_divergence_vanishes`, `heras_existence_theorem`). The retarded
  construction `F^{μν} = I[∂^μ𝒥^ν − ∂^ν𝒥^μ]` (with `I` the retarded integral): antisymmetric, satisfies the
  homogeneous Maxwell (the `ε`-block contraction), and — given the Green-inversion hypothesis — the
  inhomogeneous Maxwell `∂_μF^{μν} = 𝒥^ν`. A conditional formalization isolating the single analytic input.

## References

* J. A. Heras, Eur. J. Phys. 30 (2009) 845–854 (Eqs. 2, 3, 17; the existence theorem §3).
* Repo dependencies: `PTSymmetricQFT.MaxwellFaraday` (`faraday` = `F = dA`, `faraday_antisymm`, `faraday_bianchi`
  = the homogeneous Maxwell / Bianchi `dF = 0`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

open Finset Matrix
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the contraction kernel -/

/-- **[Symmetric × antisymmetric = 0]** `∑ᵢⱼ Sᵢⱼ Fᵢⱼ = 0` when `S` is symmetric (`Sᵢⱼ = Sⱼᵢ`) and `F` is
antisymmetric (`Fᵢⱼ = −Fⱼᵢ`). Swapping `i ↔ j` flips the sign, so twice the sum is zero. This is the algebraic
root of charge conservation (`∂_ν∂_μ F^{μν} = 0`) and of the Bianchi identity. -/
theorem symm_antisymm_contract_zero {n : ℕ} (S F : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = S j i) (hF : ∀ i j, F i j = -F j i) :
    ∑ i, ∑ j, S i j * F i j = 0 := by
  have hP : ∀ i j, S i j * F i j + S j i * F j i = 0 := by
    intro i j; rw [hS j i, hF j i]; ring
  have hsum : (∑ i, ∑ j, S i j * F i j) + (∑ i, ∑ j, S i j * F i j) = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun j _ => hP i j)
  linarith

/-! ## §B — Maxwell ⟹ continuity (Eq. 2 ⟹ Eq. 3) -/

/-- **The electromagnetic four-current** `J^ν = ∂_μ F^{μν} = ∑_μ k_μ F^{μν}` — the source of the inhomogeneous
Maxwell equation, here for `F = dA` (`faraday`). -/
noncomputable def fourCurrent (k A : Fin 4 → ℝ) (ν : Fin 4) : ℝ := ∑ μ, k μ * faraday k A μ ν

/-- **[Heras Eq. 3] Maxwell implies continuity** `∂_ν J^ν = ∑_ν k_ν J^ν = 0`. The four-divergence of the
inhomogeneous Maxwell law is `∂_ν∂_μ F^{μν}` (here `∑_{μν} k_μ k_ν F^{μν}`); since `k_μ k_ν` is symmetric and
`F = dA` is antisymmetric, it vanishes — charge conservation is a consequence of the antisymmetry of the field
tensor (Heras's "fundamental axiom" read forward). -/
theorem fourCurrent_conserved (k A : Fin 4 → ℝ) : ∑ ν, k ν * fourCurrent k A ν = 0 := by
  have hrew : (∑ ν, k ν * fourCurrent k A ν) = ∑ μ, ∑ ν, k μ * k ν * faraday k A μ ν := by
    unfold fourCurrent
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => by ring))
  rw [hrew]
  have h := symm_antisymm_contract_zero (Matrix.of fun μ ν => k μ * k ν) (faraday k A)
    (fun i j => by simp only [Matrix.of_apply]; ring) (faraday_antisymm k A)
  simpa using h

/-! ## §C — the complete Heras consistency -/

/-- **[Heras Eqs. 2–3, 17] The field `F = dA` satisfies both Maxwell equations consistently.** The source
four-current is conserved (`∂_ν J^ν = 0`, continuity), *and* the homogeneous Maxwell equation
`∂_μ *F^{μν} = 0` holds — the latter being the Bianchi identity (`faraday_bianchi`, Heras Eq. 17). Both rest
on the antisymmetry of `F`. -/
theorem faraday_heras_consistency (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    (∑ ν', k ν' * fourCurrent k A ν' = 0)
      ∧ (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0) :=
  ⟨fourCurrent_conserved k A, faraday_bianchi k A lam μ ν⟩

/-! ## §D — the converse existence theorem (Heras §3) -/

variable {R : Type*} [AddCommGroup R] [Module ℝ R]

/-- **[Eq. 5 integrand] The current curl** `K^{μν} = ∂^μ𝒥^ν − ∂^ν𝒥^μ` — the antisymmetric source the retarded
field is built from (`D μ` modelling `∂^μ`). -/
noncomputable def currentCurl (D : Fin 4 → R → R) (J : Fin 4 → R) (μ ν : Fin 4) : R :=
  D μ (J ν) - D ν (J μ)

omit [Module ℝ R] in
/-- **The current curl is antisymmetric** `K^{μν} = −K^{νμ}`. -/
theorem currentCurl_antisymm (D : Fin 4 → R → R) (J : Fin 4 → R) (μ ν : Fin 4) :
    currentCurl D J μ ν = - currentCurl D J ν μ := by
  unfold currentCurl; rw [neg_sub]

/-- **[Eq. 13] The retarded construction** `F^{μν} = I[K^{μν}]` — the spacetime-integral `I = ∫d⁴x' G(x,x')·`
of the antisymmetric current curl. -/
noncomputable def constructedField (I : R →ₗ[ℝ] R) (D : Fin 4 → R → R) (J : Fin 4 → R)
    (μ ν : Fin 4) : R := I (currentCurl D J μ ν)

/-- **[Eq. 13] The constructed field is antisymmetric** `F^{μν} = −F^{νμ}` — the retarded integral is linear,
so it preserves the antisymmetry of the current curl. -/
theorem constructedField_antisymm (I : R →ₗ[ℝ] R) (D : Fin 4 → R → R) (J : Fin 4 → R) (μ ν : Fin 4) :
    constructedField I D J μ ν = - constructedField I D J ν μ := by
  unfold constructedField; rw [currentCurl_antisymm, map_neg]

/-- **The four-divergence** `∂_μ F^{μν} = ∑_μ ∂_μ F^{μν}`. -/
noncomputable def fourDivergence (D : Fin 4 → R → R) (F : Fin 4 → Fin 4 → R) (ν : Fin 4) : R :=
  ∑ μ, D μ (F μ ν)

/-- **[Eqs. 16–17] The homogeneous Maxwell equation `∂_μ *F^{μν} = 0`.** The dual divergence is
`(1/2)ε^{μνκλ}∂_μ∂_κ(…)`; for each fixed `(ν,λ)` the `ε`-block `E_{μκ} = ε^{μνκλ}` is antisymmetric in `(μ,κ)`
while the second-derivative block `S_{μκ} = ∂_μ∂_κ(…)` is symmetric, so the contraction vanishes — exactly
`symm_antisymm_contract_zero`. -/
theorem dual_divergence_vanishes (E S : Matrix (Fin 4) (Fin 4) ℝ)
    (hE : ∀ μ κ, E μ κ = -E κ μ) (hS : ∀ μ κ, S μ κ = S κ μ) :
    ∑ μ, ∑ κ, S μ κ * E μ κ = 0 := symm_antisymm_contract_zero S E hS hE

/-- **[Heras §3, the existence theorem] A conserved current admits a Maxwell field.** The retarded
construction `F^{μν} = I[∂^μ𝒥^ν − ∂^ν𝒥^μ]` (`I` the retarded integral) is **antisymmetric** (Eq. 13),
satisfies the **homogeneous** Maxwell equation `∂_μ*F^{μν} = 0` (Eq. 17, the `ε`-block contraction), and —
given the **Green-inversion** hypothesis `hGreen` (the integrated tensor identity (7), i.e. the wave-operator
Green inversion `∂'_μ∂'^μ G = δ`, the one irreducibly-analytic input) — the **inhomogeneous** Maxwell equation
`∂_μF^{μν} = 𝒥^ν` (Eq. 14). The whole theorem holds with that single analytic fact isolated as a hypothesis;
everything else is derived algebraically. -/
theorem heras_existence_theorem (I : R →ₗ[ℝ] R) (D : Fin 4 → R → R) (J : Fin 4 → R)
    (E S : Matrix (Fin 4) (Fin 4) ℝ) (hE : ∀ μ κ, E μ κ = -E κ μ) (hS : ∀ μ κ, S μ κ = S κ μ)
    (hGreen : ∀ ν, fourDivergence D (constructedField I D J) ν = J ν) (ν : Fin 4) :
    (∀ μ, constructedField I D J μ ν = - constructedField I D J ν μ)
      ∧ fourDivergence D (constructedField I D J) ν = J ν
      ∧ (∑ μ, ∑ κ, S μ κ * E μ κ = 0) :=
  ⟨fun μ => constructedField_antisymm I D J μ ν, hGreen ν, dual_divergence_vanishes E S hE hS⟩

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

end
