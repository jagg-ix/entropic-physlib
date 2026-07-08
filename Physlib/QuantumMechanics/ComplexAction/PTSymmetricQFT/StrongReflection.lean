/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

/-!
# Greaves–Thomas §6: strong reflection and CPT invariance for tensors

Formalizes §6 (with §4.2/§4.4) of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674): the
**strong reflection** `S`, the **strong-reflection invariance theorem** (Theorem 2), the Hermitian
conjugation `†_$ = S ∘ C_$`, and the **general PT/CPT theorem** (Theorem 3) with its four
`$`-specializations (classical PT / quantum CPT / classical CPT / quantum PT).

The **strong reflection** `S` (§6) is the anti-automorphism of `K^form = TensorAlgebra ℂ U` that is the
identity on field symbols and reverses the order of products:

  `S(Φ^λ) = Φ^λ`,   `S(X + Y) = S(X) + S(Y)`,   `S(XY) = S(Y)S(X)`.

It is realized as `unop ∘ Sᵒᵖ`, where `Sᵒᵖ : K^form →ₐ (K^form)ᵐᵒᵖ` is the `TensorAlgebra.lift` of
`s ↦ op (Φ^s)` into the opposite algebra. `S² = id` (`strongReflection_involutive`).

* **§A — the strong reflection `S`** (`strongReflection`, `strongReflection_ι`, `strongReflection_antihom`,
  `strongReflection_involutive`, `strongReflection_comm_pair`). The last shows `S` fixes a *commuting*
  product `Φ^λ Φ^μ` — the mechanism behind "`S` is the identity on the commutative quotient `K^{c,form}`",
  i.e. **half of spin-statistics**: tensor fields commute, so a commutative theory is `S`-invariant.
* **§B — Theorem 2 (SR invariance) and the abstract Theorem 3 engine** (`strongReflection_invariance`,
  `dagger_invariance_iff`, `classicalPT_via_strongReflection`). Theorem 2: an `S`-invariant (commutative)
  theory that is `[ρ'ω'](L↓₊)`-invariant is invariant under `S ∘ [ρ'ω'](L↓₊)`. The set-theoretic engine
  `dagger_invariance_iff`: when `† ∘ g` preserves `D` and `†` is an involution, `g`-invariance ⟺
  `†`-invariance. With `† = S` (the `$ = id` case) this is the classical PT theorem.
* **§C — Hermiticity `†_$` and Theorem 3** (`daggerConj`, `daggerConj_ι`, `daggerConj_antihom`,
  `daggerConj_involutive`, `generalPTCPT`). `†_$ = S ∘ C_$` is the anti-automorphism acting as `C_$`
  (Eq. 14) on symbols but reversing products; `D` is `$`-Hermitian iff `†_$`-invariant. **Theorem 3**: a
  commutative `L↑₊`-invariant `D` is `C_$ ∘ [ρ'ω'](L↓₊)`-invariant **iff** it is `$`-Hermitian. Taking
  `$ = id` gives classical PT; `$ = ∗` gives **quantum CPT** (`[ρ'ω']_q(L↓₊)`-invariant iff `∗`-Hermitian);
  `$ = #` gives classical CPT.

**§4.2 (Quantum CPT Theorem for Tensors)** is the `$ = ∗` reading of Theorem 3 (Part 1) together with its
charge-grading face (Part 2): if `L↑₊` is charge-preserving then `L↓₊` is charge-*conjugating* under the
quantum action, because `[ρ'ω']_q = C_∗ ∘ [ρ'ω']` and `C_∗` is charge-conjugating while `[ρ'ω'](L↓₊)` is
charge-preserving (Theorem 1) — exactly `PTSymmetricQFT.ChargeConjugation.chargeConjugating_comp_chargePreserving`.
**§5/Theorem 1** (the universal extension `[ρ'ω']` via complexification, proved in Appendix C) supplies the
`[ρ'ω'](L↓₊)`-invariance taken here as the hypothesis `(S ∘ τ) '' D = D`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §4.2, §4.4, §5 (Theorem 1), §6 (strong
  reflection `S`, Theorems 2–3, the four `$`-interpretations).
* Repo dependencies: `PTSymmetricQFT.ChargeConjugation` (`chargeConjugation`, `chargeConjugation_ι`,
  `chargeConjugation_involutive`, `chargeConjugating_comp_chargePreserving`); `TensorAlgebra.lift` /
  `MulOpposite`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.StrongReflection

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — the strong reflection `S` -/

/-- The algebra hom `K^form →ₐ (K^form)ᵐᵒᵖ` extending `s ↦ op (Φ^s)` — the opposite-algebra packaging of
the order-reversing strong reflection. -/
noncomputable def Sop : KForm U →ₐ[ℂ] (KForm U)ᵐᵒᵖ :=
  TensorAlgebra.lift ℂ ((MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ TensorAlgebra.ι ℂ)

/-- **[Greaves–Thomas §6] The strong reflection `S`** — the anti-automorphism of `K^form` that is the
identity on field symbols and reverses the order of products. -/
noncomputable def strongReflection (X : KForm U) : KForm U := MulOpposite.unop (Sop X)

/-- **`S` is the identity on field symbols** `S(Φ^λ) = Φ^λ`. -/
@[simp] theorem strongReflection_ι (s : U) :
    strongReflection (TensorAlgebra.ι ℂ s) = TensorAlgebra.ι ℂ s := by
  simp [strongReflection, Sop, TensorAlgebra.lift_ι_apply]

/-- **`S` reverses products** `S(XY) = S(Y)S(X)` — `S` is an anti-automorphism of algebras. -/
theorem strongReflection_antihom (X Y : KForm U) :
    strongReflection (X * Y) = strongReflection Y * strongReflection X := by
  simp [strongReflection, Sop, MulOpposite.unop_mul]

/-- **`S` is additive** `S(X + Y) = S(X) + S(Y)`. -/
theorem strongReflection_add (X Y : KForm U) :
    strongReflection (X + Y) = strongReflection X + strongReflection Y := by
  simp [strongReflection, Sop]

/-- **`S` fixes scalars** `S(r·1) = r·1`. -/
@[simp] theorem strongReflection_algebraMap (r : ℂ) :
    strongReflection (algebraMap ℂ (KForm U) r) = algebraMap ℂ (KForm U) r := by
  simp [strongReflection, Sop]

/-- **`S` is an involution** `S ∘ S = id` — applying `S` twice restores the original order. -/
theorem strongReflection_involutive : Function.Involutive (strongReflection : KForm U → KForm U) := by
  intro X
  induction X using TensorAlgebra.induction with
  | algebraMap r => rw [strongReflection_algebraMap, strongReflection_algebraMap]
  | ι s => rw [strongReflection_ι, strongReflection_ι]
  | mul X Y hX hY => rw [strongReflection_antihom, strongReflection_antihom, hX, hY]
  | add X Y hX hY => rw [strongReflection_add, strongReflection_add, hX, hY]

/-- **[Spin-statistics mechanism] `S` fixes a commuting product** `S(Φ^λ Φ^μ) = Φ^λ Φ^μ` when the symbols
commute. This is why `S` is the identity on the commutative quotient `K^{c,form}`: a *commutative* formal
field theory (the tensor-field half of the spin-statistics connection) is `S`-invariant. -/
theorem strongReflection_comm_pair (s t : U)
    (hc : TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t = TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s) :
    strongReflection (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t)
      = TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t := by
  rw [strongReflection_antihom, strongReflection_ι, strongReflection_ι]; exact hc.symm

/-! ## §B — Theorem 2 (SR invariance) and the Theorem 3 engine -/

/-- **[Greaves–Thomas Theorem 2 — SR invariance for tensors]** A commutative (hence `S`-invariant) formal
field theory that is `[ρ'ω'](L↓₊)`-invariant is invariant under the **strong reflection**
`S ∘ [ρ'ω'](L↓₊)`. (`τ` is the classical PT automorphism `[ρ'ω'](L↓₊)` of Theorem 1.) -/
theorem strongReflection_invariance (D : Set (KForm U)) (τ : KForm U → KForm U)
    (hS : strongReflection '' D = D) (hτ : τ '' D = D) :
    (strongReflection ∘ τ) '' D = D := by
  rw [Set.image_comp, hτ, hS]

/-- **[Theorem 3 engine] `g`-invariance ⟺ `†`-invariance, given `† ∘ g` preserves `D` and `†` is an
involution.** Both implications follow from `(† ∘ g) '' D = D` and `† ∘ † = id`. This is the set-theoretic
core of the general PT/CPT theorem (with `† = †_$`, `g = C_$ ∘ [ρ'ω'](L↓₊)`). -/
theorem dagger_invariance_iff {α : Type*} (D : Set α) (dag g : α → α)
    (hdag : Function.Involutive dag) (hcombo : (dag ∘ g) '' D = D) :
    g '' D = D ↔ dag '' D = D := by
  rw [Set.image_comp] at hcombo
  refine ⟨fun hg => by rw [hg] at hcombo; exact hcombo, fun hd => ?_⟩
  have h2 : dag '' (dag '' (g '' D)) = D := by rw [hcombo, hd]
  rw [← Set.image_comp, hdag.comp_self, Set.image_id] at h2
  exact h2

/-- **[Theorem 3, `$ = id`: a classical PT theorem]** For the strong-reflection combination `S ∘ τ`
preserving `D`, the classical PT transformation `τ = [ρ'ω'](L↓₊)` preserves `D` **iff** `D` is `S`-invariant
(`†_id = S`). A commutative theory is automatically `S`-invariant, so it is `[ρ'ω'](L↓₊)`-invariant — the
classical PT theorem (a slight weakening of Theorem 1, now assuming commutativity). -/
theorem classicalPT_via_strongReflection (D : Set (KForm U)) (τ : KForm U → KForm U)
    (hcombo : (strongReflection ∘ τ) '' D = D) :
    τ '' D = D ↔ strongReflection '' D = D :=
  dagger_invariance_iff D strongReflection τ strongReflection_involutive hcombo

/-! ## §C — Hermiticity `†_$` and Theorem 3 (general PT/CPT) -/

/-- **[Greaves–Thomas §6] The Hermitian-conjugation anti-automorphism** `†_$ = S ∘ C_$` — it acts as the
charge conjugation `C_$` (Eq. 14) on field symbols but reverses the order of products. `D` is **`$`-Hermitian**
iff it is `†_$`-invariant. For `$ = ∗`, `†_∗` is exactly Hermitian conjugation of QFT operators (Example 8). -/
noncomputable def daggerConj (c : U ≃ₗ[ℂ] U) (X : KForm U) : KForm U :=
  strongReflection (chargeConjugation c X)

/-- **`†_$` acts as `C_$` on field symbols** `†_$(Φ^λ) = Φ^{$λ}`. -/
theorem daggerConj_ι (c : U ≃ₗ[ℂ] U) (s : U) :
    daggerConj c (TensorAlgebra.ι ℂ s) = TensorAlgebra.ι ℂ (c s) := by
  unfold daggerConj; rw [chargeConjugation_ι, strongReflection_ι]

/-- **`†_$` reverses products** `†_$(XY) = †_$(Y) †_$(X)` — like `S`, it is an anti-automorphism. -/
theorem daggerConj_antihom (c : U ≃ₗ[ℂ] U) (X Y : KForm U) :
    daggerConj c (X * Y) = daggerConj c Y * daggerConj c X := by
  unfold daggerConj; rw [map_mul, strongReflection_antihom]

/-- **`†_$` is additive**. -/
theorem daggerConj_add (c : U ≃ₗ[ℂ] U) (X Y : KForm U) :
    daggerConj c (X + Y) = daggerConj c X + daggerConj c Y := by
  unfold daggerConj; rw [map_add, strongReflection_add]

/-- **`†_$` fixes scalars**. -/
theorem daggerConj_algebraMap (c : U ≃ₗ[ℂ] U) (r : ℂ) :
    daggerConj c (algebraMap ℂ (KForm U) r) = algebraMap ℂ (KForm U) r := by
  unfold daggerConj; rw [AlgEquiv.commutes, strongReflection_algebraMap]

/-- **`†_$` is an involution** when `$` is (`$ ∘ $ = id`) — since `S` and `C_$` are both involutions. -/
theorem daggerConj_involutive (c : U ≃ₗ[ℂ] U) (hc : ∀ s, c (c s) = s) :
    Function.Involutive (daggerConj c : KForm U → KForm U) := by
  intro X
  induction X using TensorAlgebra.induction with
  | algebraMap r => rw [daggerConj_algebraMap, daggerConj_algebraMap]
  | ι s => rw [daggerConj_ι, daggerConj_ι, hc]
  | mul X Y hX hY => rw [daggerConj_antihom, daggerConj_antihom, hX, hY]
  | add X Y hX hY => rw [daggerConj_add, daggerConj_add, hX, hY]

/-- **`†_$ ∘ C_$ = S`** on `K^form` (when `$` is an involution): `†_$ = S ∘ C_$` and `C_$ ∘ C_$ = id`. -/
theorem daggerConj_chargeConjugation (c : U ≃ₗ[ℂ] U) (hc : ∀ s, c (c s) = s) (Y : KForm U) :
    daggerConj c (chargeConjugation c Y) = strongReflection Y := by
  unfold daggerConj; rw [chargeConjugation_involutive c hc]

/-- **[Greaves–Thomas Theorem 3 — general PT/CPT theorem for tensors]** A commutative `L↑₊`-invariant
formal field theory `D` (so that the strong-reflection combination `S ∘ τ = †_$ ∘ (C_$ ∘ τ)` preserves `D`,
by Theorem 2) is invariant under the charge-conjugated PT transformation `C_$ ∘ [ρ'ω'](L↓₊)` **if and only
if** it is `$`-Hermitian (`†_$`-invariant). Specializing `$`: `id` ⟹ classical PT, `∗` ⟹ **quantum CPT**
(`[ρ'ω']_q(L↓₊)`-invariance ⟺ `∗`-Hermiticity), `#` ⟹ classical CPT. -/
theorem generalPTCPT (c : U ≃ₗ[ℂ] U) (hc : ∀ s, c (c s) = s) (D : Set (KForm U))
    (τ : KForm U → KForm U) (hcombo : (strongReflection ∘ τ) '' D = D) :
    ((chargeConjugation c : KForm U → KForm U) ∘ τ) '' D = D ↔ (daggerConj c) '' D = D := by
  apply dagger_invariance_iff D (daggerConj c) ((chargeConjugation c : KForm U → KForm U) ∘ τ)
    (daggerConj_involutive c hc)
  have hfun : daggerConj c ∘ ((chargeConjugation c : KForm U → KForm U) ∘ τ)
      = strongReflection ∘ τ := by
    funext x; simp only [Function.comp_apply]; exact daggerConj_chargeConjugation c hc (τ x)
  rw [hfun]; exact hcombo

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.StrongReflection

end
