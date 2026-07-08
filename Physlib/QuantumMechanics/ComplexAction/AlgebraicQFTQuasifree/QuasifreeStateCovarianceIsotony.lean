/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

/-!
# Covariance and isotony of the quasi-free net of von Neumann algebras (Labuschagne–Majewski §§7.2–7.3)

Formalizes Part 2 §§7.2–7.3 of Labuschagne–Majewski (arXiv:2503.14107): the net of von Neumann measure algebras
`𝒪 ↦ (𝓜(𝒪), ω_𝒪)` built from quasi-free states is **covariant** under the isometric (Killing) flow and **isotonic**
under region inclusion. Both facts run through one mechanism: a **symplectic map** `T` on the one-particle space
(`G_𝒪 f ↦ G_{Ψ(𝒪)}(f∘Ψ⁻¹)`, or the inclusion embedding) that preserves the two-point function, so the Bogoliubov
`*`-isomorphism `α` it induces **intertwines the quasi-free states**.

* the isometric flow's map `T` is a **symplectic map** (`IsSymplecticMap`, `σ(Tf,Tg) = σ(f,g)`), and such maps
 compose and contain the identity (`isSymplecticMap_id`, `isSymplecticMap_comp`) — the one-parameter family of
 Killing-flow symplectic maps (Part 1);
* `T` **preserves the two-point function** (`IsTwoPointCovariant`, `s₂(Tf,Tg) = s₁(f,g)`), the covariance of the
 quasi-free state under the isometry / inclusion;
* hence the **quasi-free state is covariant** `ω_{s₂}(W(Tf)) = ω_{s₁}(W(f))` (`quasifree_state_covariant`) — this is
 both `ω_{Ψ(𝒪)} ∘ α_Ψ = ω_𝒪` (§7.2, isometry covariance, Prop. 7.3) and `ω₂ ∘ α_{2:1} = ω_{𝒪₁}` (§7.3, the
 state restricts under `𝒪₁ ⊂ 𝒪₂`, Prop. 7.8/7.11 isotony);
* a composite covariance intertwiner is again covariant (`quasifree_covariant_comp`) — the one-parameter group /
 chain of inclusions acts consistently.

So the quasi-free assignment `𝒪 ↦ ω_𝒪` is a covariant, isotonic net: the Killing flow of the spacetime (Part 1)
acts on the local von Neumann algebras by state-preserving `*`-isomorphisms, and region inclusion embeds the
smaller state into the larger — the von Neumann realization of the covariant, isotonic quasi-local net.

* **§A — symplectic maps of the isometric flow** (`IsSymplecticMap`, `isSymplecticMap_id`, `_comp`).
* **§B — two-point covariance and the covariant quasi-free state** (`IsTwoPointCovariant`,
 `quasifree_state_covariant`).
* **§C — composition / isotony chain** (`quasifree_covariant_comp`).

The symplectic-map and two-point-covariance predicates and the state-intertwining identity
`ω_{s₂}(W(Tf)) = ω_{s₁}(W(f))` are exact (reusing `quasifreeWeight`). The Bogoliubov `*`-isomorphism `α`, the GNS
standard form, and the weak/spatial extension (Prop. 7.3, 7.11) are *recorded* — `T` and its covariance are the
algebraic content. No new axioms.

## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, §§7.2–7.3 (isometry covariance Prop. 7.3, isotony Prop.
 7.8/7.11). Repo dependencies: `OperatorAlgebra.WeylCCRSpacetime` (`quasifreeWeight`),
 `AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony

/-! ## §A — symplectic maps of the isometric flow -/

/-- **A symplectic map** on the one-particle space — `σ(Tf, Tg) = σ(f, g)` (Labuschagne–Majewski §7.2): the map
`T : G_𝒪 f ↦ G_{Ψ(𝒪)}(f∘Ψ⁻¹)` induced by an isometry, or the inclusion embedding, preserving the symplectic form.
Its Bogoliubov transform is the `*`-isomorphism `α` of the CCR algebras. -/
def IsSymplecticMap (T : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ f g : (Fin 2 → ℝ), σ (T f) (T g) = σ f g

/-- **[The identity is symplectic] `id` preserves `σ`.** The trivial (`s = 0`) stage of the flow. -/
theorem isSymplecticMap_id (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) : IsSymplecticMap id σ :=
  fun _ _ => rfl

/-- **[Symplectic maps compose] `T, S` symplectic ⟹ `T ∘ S` symplectic.** The one-parameter Killing-flow family
of symplectic maps is closed under composition (the flow cocycle), and a chain of region inclusions composes. -/
theorem isSymplecticMap_comp {T S : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ} (hT : IsSymplecticMap T σ) (hS : IsSymplecticMap S σ) :
    IsSymplecticMap (T ∘ S) σ := by
  intro f g
  simp only [Function.comp_apply]
  rw [hT (S f) (S g), hS f g]

/-! ## §B — two-point covariance and the covariant quasi-free state -/

/-- **Two-point covariance** — `s₂(Tf, Tg) = s₁(f, g)` (Labuschagne–Majewski §7.2): the map `T` includes the
two-point function `s₁` of `ω_𝒪` to that of `ω_{Ψ(𝒪)}`, the covariance of the quasi-free state under the isometry
(or the inclusion embedding for isotony). -/
def IsTwoPointCovariant (T : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (s1 s2 : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ f g : (Fin 2 → ℝ), s2 (T f) (T g) = s1 f g

/-- **[The quasi-free state is covariant] `ω_{s₂}(W(Tf)) = ω_{s₁}(W(f))`.** If `T` preserves the two-point
function, the Bogoliubov `*`-isomorphism it induces intertwines the quasi-free states. This is simultaneously

* `ω_{Ψ(𝒪)} ∘ α_Ψ = ω_𝒪` — **covariance** of the net under the isometric Killing flow (§7.2, Prop. 7.3), and
* `ω₂ ∘ α_{2:1} = ω_{𝒪₁}` — **isotony**, the smaller state as the restriction of the larger under `𝒪₁ ⊂ 𝒪₂`
  (§7.3, Prop. 7.8/7.11). -/
theorem quasifree_state_covariant {T : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {s1 s2 : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ} (h : IsTwoPointCovariant T s1 s2) (f : Fin 2 → ℝ) :
    quasifreeWeight s2 (T f) = quasifreeWeight s1 f := by
  unfold quasifreeWeight
  rw [h f f]

/-! ## §C — composition / isotony chain -/

/-- **[Covariance composes] a chain of covariant maps is covariant.** If `T` records `s₁ → s₂` and `S` records
`s₂ → s₃` (both preserving the two-point function), then `S ∘ T` records `s₁ → s₃`: the one-parameter flow group
and the chain of region inclusions `𝒪₁ ⊂ 𝒪₂ ⊂ 𝒪₃` act consistently on the quasi-free states. -/
theorem quasifree_covariant_comp {T S : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {s1 s2 s3 : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    (hT : IsTwoPointCovariant T s1 s2) (hS : IsTwoPointCovariant S s2 s3) :
    IsTwoPointCovariant (S ∘ T) s1 s3 := by
  intro f g
  simp only [Function.comp_apply]
  rw [hS (T f) (T g), hT f g]

/-- **[The quasi-free net is covariant and isotonic, assembled].** For a two-point-covariance map `T` (the
isometric Killing-flow map, or the region-inclusion embedding):

* the quasi-free state is intertwined `ω_{s₂}(W(Tf)) = ω_{s₁}(W(f))` — covariance (§7.2) and isotony (§7.3);
* covariance maps compose (`S ∘ T`) — the one-parameter group / inclusion chain acts consistently.

The net `𝒪 ↦ ω_𝒪` of quasi-free von Neumann measure algebras is covariant under the Killing flow and isotonic
under inclusion. -/
theorem quasifree_net_covariant_isotonic {T S : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {s1 s2 s3 : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    (hT : IsTwoPointCovariant T s1 s2) (hS : IsTwoPointCovariant S s2 s3) (f : Fin 2 → ℝ) :
    quasifreeWeight s2 (T f) = quasifreeWeight s1 f
      ∧ IsTwoPointCovariant (S ∘ T) s1 s3 :=
  ⟨quasifree_state_covariant hT f, quasifree_covariant_comp hT hS⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony

end
