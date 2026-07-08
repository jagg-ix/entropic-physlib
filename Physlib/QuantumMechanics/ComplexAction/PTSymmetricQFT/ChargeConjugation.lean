/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality

/-!
# Greaves–Thomas §3: charge conjugation and the PT/CPT distinction

Formalizes §3 of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674): the **charge-conjugation
automorphism** `C_$` (their Eq. 14) and the formal **PT vs. CPT** distinction. Both PT and CPT are
spacetime symmetries with `ω(g) ∈ L↓₊` (proper non-orthochronous — reversing both parity and time); they
differ by whether the induced automorphism of `K^form` is *charge-preserving* (PT) or *charge-conjugating*
(CPT, exchanging the particle/anti-particle sectors `W⁺ ↔ W⁻`).

Given an involution `$ : W → W` of the field-value covectors (`$ ∘ $ = id`), Greaves–Thomas define the
**`$`-conjugation** by (Eq. 14)

  `C_$(Φ^λ_{ξ₁⋯ξₙ}) = Φ^{$λ}_{ξ₁⋯ξₙ}`,   `C_$(XY) = C_$(X)C_$(Y)`,   `C_$(X+Y) = C_$(X)+C_$(Y)`,

the unique algebra automorphism of `K^form` extending `$`. In this formalization `K^form = TensorAlgebra ℂ U`
and `C_$` is exactly the dual formula automorphism `tensorAlgEquiv $` of `PTSymmetricQFT.FieldFormulaDuality`,
now read as charge conjugation.

* **§A — the `$`-conjugation automorphism** (`chargeConjugation`, `chargeConjugation_ι`,
  `chargeConjugation_mul`). `C_$ = tensorAlgEquiv $`, satisfying Eq. 14.
* **§B — internal charge conjugation is a `ℤ₂` symmetry** (`chargeConjugation_involutive`,
  `chargeConjugation_sq_refl`). An *internal charge conjugation* is an **involution** `# : V → V`; then
  `C_# ∘ C_# = id`, so `#` generates a `ℤ₂ = {±1}` geometric action (acting trivially on `M`) — charge
  conjugation as a "spacetime symmetry."
* **§C — charge conjugation relates PT to CPT** (`chargeConjugation_comp`, `cpt_eq_chargeConj_comp_pt`).
  `C_# ∘ σ_e = σ_{#∘e}`: if `σ_e` is a (charge-preserving) **PT** transformation, then `C_# ∘ σ_e` is the
  (charge-conjugating) **CPT** transformation — Greaves–Thomas's claim that `C_#` records PT to CPT
  (Definition 5).

The concrete spinor instance is `FirstQuantizedQED.CPTAntiunitary.chargeConj` (`C ψ = iγ²ψ*`); the anti-linear
`$ = ∗` case (`C_∗`, relating the classical and quantum actions `[ρω]_q = C_∗ ∘ [ρω]` for time-reversing
`g`) is the `conjFactor true` of `PTSymmetricQFT.TemporalOrientation` — `C_#` is `ℂ`-linear, `C_∗` anti-linear.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §3 (Eq. 14, Definitions 4–5; charge
  conjugation `C_#` and `C_∗`).
* Repo dependencies: `PTSymmetricQFT.FieldFormulaDuality` (`tensorAlgEquiv`, `tensorMap`); the concrete spinor
  `C`/`P`/`T` of `FirstQuantizedQED.CPTAntiunitary`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — the `$`-conjugation automorphism `C_$` -/

/-- **[Greaves–Thomas Eq. 14] The `$`-conjugation automorphism** `C_$` of `K^form` — the unique algebra
automorphism extending an involution `$` of the field symbols, `C_$(Φ^λ) = Φ^{$λ}`. It is the dual formula
automorphism `tensorAlgEquiv $`. -/
noncomputable def chargeConjugation (c : U ≃ₗ[ℂ] U) : KForm U ≃ₐ[ℂ] KForm U := tensorAlgEquiv c

/-- **[Eq. 14] `C_$` acts on a field symbol by `$`**: `C_$(Φ^λ) = Φ^{$λ}`. -/
theorem chargeConjugation_ι (c : U ≃ₗ[ℂ] U) (s : U) :
    chargeConjugation c (TensorAlgebra.ι ℂ s) = TensorAlgebra.ι ℂ (c s) := by
  simp [chargeConjugation, tensorAlgEquiv_apply, tensorMap_ι]

/-- **[Eq. 14] `C_$` is multiplicative** `C_$(XY) = C_$(X)C_$(Y)` — the algebra-hom extension rule. -/
theorem chargeConjugation_mul (c : U ≃ₗ[ℂ] U) (X Y : KForm U) :
    chargeConjugation c (X * Y) = chargeConjugation c X * chargeConjugation c Y := map_mul _ _ _

/-- **`C_$` is additive** `C_$(X+Y) = C_$(X)+C_$(Y)`. -/
theorem chargeConjugation_add (c : U ≃ₗ[ℂ] U) (X Y : KForm U) :
    chargeConjugation c (X + Y) = chargeConjugation c X + chargeConjugation c Y := map_add _ _ _

/-! ## §B — internal charge conjugation is a `ℤ₂` symmetry -/

/-- **[Internal charge conjugation] `C_#` is an involution** `C_# ∘ C_# = id` when `#` is an involution
(`# ∘ # = id`). The internal charge conjugation `#` thus generates a `ℤ₂ = {±1}` geometric action (acting
trivially on spacetime) — charge conjugation as a "spacetime symmetry." -/
theorem chargeConjugation_involutive (c : U ≃ₗ[ℂ] U) (hinv : ∀ s, c (c s) = s) (F : KForm U) :
    chargeConjugation c (chargeConjugation c F) = F := by
  simp only [chargeConjugation, tensorAlgEquiv_apply]
  rw [← AlgHom.comp_apply, ← tensorMap_comp,
    show (c : U →ₗ[ℂ] U).comp (c : U →ₗ[ℂ] U) = LinearMap.id from by ext s; simp [hinv],
    tensorMap_id]
  rfl

/-- **The `ℤ₂` charge-conjugation symmetry** `C_# ∘ C_# = id` at the automorphism level — `#` of order 2. -/
theorem chargeConjugation_sq_refl (c : U ≃ₗ[ℂ] U) (hinv : ∀ s, c (c s) = s) :
    (chargeConjugation c).trans (chargeConjugation c) = AlgEquiv.refl :=
  AlgEquiv.ext (fun F => chargeConjugation_involutive c hinv F)

/-! ## §C — charge conjugation relates PT to CPT -/

/-- **[Composition] `C_# ∘ σ_e = σ_{#∘e}`.** Charge conjugation precomposes the field-symbol map of any
formula automorphism. -/
theorem chargeConjugation_comp (hash e : U ≃ₗ[ℂ] U) (F : KForm U) :
    chargeConjugation hash (tensorAlgEquiv e F)
      = tensorMap ((hash : U →ₗ[ℂ] U).comp (e : U →ₗ[ℂ] U)) F := by
  simp only [chargeConjugation, tensorAlgEquiv_apply]
  rw [← AlgHom.comp_apply, ← tensorMap_comp]

/-- **[Greaves–Thomas Def. 4] A charge grading** `γ` (with `γ² = id`): the `±1` eigenspaces are the
particle / anti-particle sectors `W⁺ / W⁻`. A symbol map `σ` is **charge-preserving** if it *commutes* with
`γ` (`σ(Wᵋ) = Wᵋ`). -/
def IsChargePreserving (γ σ : U →ₗ[ℂ] U) : Prop := σ.comp γ = γ.comp σ

/-- **[Greaves–Thomas Def. 4] Charge-conjugating**: `σ` *anti-commutes* with the charge grading
(`σ(Wᵋ) = W⁻ᵋ`, exchanging particle and anti-particle sectors). -/
def IsChargeConjugating (γ σ : U →ₗ[ℂ] U) : Prop := σ.comp γ = -(γ.comp σ)

/-- **[Greaves–Thomas Def. 5] Charge conjugation records PT to CPT.** If `#` is charge-conjugating (the
internal charge conjugation, exchanging `W⁺ ↔ W⁻`) and `σ` is a charge-preserving **PT** transformation,
then `# ∘ σ` is charge-conjugating — a **CPT** transformation. This is the formal sense in which `C_#`
relates PT and CPT. -/
theorem chargeConjugating_comp_chargePreserving (γ hash σ : U →ₗ[ℂ] U)
    (hhash : IsChargeConjugating γ hash) (hσ : IsChargePreserving γ σ) :
    IsChargeConjugating γ (hash.comp σ) := by
  unfold IsChargeConjugating IsChargePreserving at *
  rw [LinearMap.comp_assoc, hσ, ← LinearMap.comp_assoc, hhash, LinearMap.neg_comp,
    LinearMap.comp_assoc]

/-- **Charge conjugation is an involution back to charge-preserving**: `# ∘ #` is charge-preserving (`C_#² =
id` at the sector level) — `CPT ∘ CPT = PT`. -/
theorem chargeConjugating_comp_self (γ hash : U →ₗ[ℂ] U) (hhash : IsChargeConjugating γ hash) :
    IsChargePreserving γ (hash.comp hash) := by
  unfold IsChargeConjugating IsChargePreserving at *
  rw [LinearMap.comp_assoc, hhash, LinearMap.comp_neg, ← LinearMap.comp_assoc, hhash,
    LinearMap.neg_comp, neg_neg, LinearMap.comp_assoc]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

end
