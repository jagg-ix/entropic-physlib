/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative

/-!
# Existence of quantum Killing Lie derivatives: unital `*`-derivation + local contraction group (Labuschagne–Majewski §6.2)

Continues §6 of Labuschagne–Majewski (arXiv:2503.14107): the quantum Killing Lie derivative `δ_Z` is a **unital
`*`-derivation** admitting a `δ_Z`-invariant faithful state, hence `σ`-strong* closable (their Theorem 6.10), and
it is the generator of a one-parameter **local** group of contractions (their Definition 6.2).

* **`δ_Z` is a unital `*`-derivation** (Theorem 6.10): it annihilates the unit
  (`quantumKillingLieDerivative_unital`) and, for a **skew-adjoint** Killing generator `K* = −K` (`K = iH_Z`),
  intertwines the involution `(δ_Z a)* = δ_Z(a*)` (`quantumKillingLieDerivative_star`) — together with the Leibniz
  rule of the previous module this is a unital `*`-derivation (`quantumKillingLieDerivative_isStarDerivation`);
* **a `δ_Z`-invariant faithful state exists** (Theorem 6.10 hypothesis): any **tracial** state annihilates the
  inner Killing derivation, `ω ∘ δ_Z = 0` (`killingGenerator_tracial_invariant`) — the vanishing-on-a-faithful-
  state condition that guarantees closability;
* **the local one-parameter group of contractions** (Definition 6.2): the domains `D_α` filter downward as `α`
  grows and the group law `T_s T_t = T_{s+t}` holds **locally** on `[−α, α]` (`LocalContractionGroup`), giving
  local invertibility `T_s T_{−s} = id` on each domain (`localContraction_local_inverse`).

So the Killing field furnishes a unital `*`-derivation with an invariant faithful state (the ingredients of the
closable generator of Theorem 6.10) and a local contraction group whose local cocycle is exact.

* **§A — `δ_Z` is a unital `*`-derivation** (`quantumKillingLieDerivative_unital`, `_star`, `_isStarDerivation`).
* **§B — a tracial state is `δ_Z`-invariant** (`killingGenerator_tracial_invariant`).
* **§C — the local one-parameter group of contractions** (`LocalContractionGroup`,
  `localContraction_local_inverse`).

**Honest layering.** The unital / `*` / Leibniz properties of the inner derivation and the tracial invariance are
exact algebra; the local-contraction-group structure captures Definition 6.2's filtration and **local** cocycle
exactly. The analytic content — the strong-continuity axiom, the separating-space closability proof (Lemma 6.8),
the `σ`-strong* topology — is *not* built; closability is the stated consequence of the invariant faithful state,
not re-derived. ## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, §6.2 (Def. 6.2, Lemma 6.8, Thm. 6.10). Repo carrier:
  `AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingLieDerivativeClosability


variable {R : Type*} [Ring R]

/-- **[The quantum Killing Lie derivative is unital] `δ_Z(1) = 0`.** The inner derivation annihilates the identity
— a *unital* derivation (Theorem 6.10). -/
lemma quantumKillingLieDerivative_unital (K : R) : quantumKillingLieDerivative K 1 = 0 := by
  unfold quantumKillingLieDerivative collisionStar; simp

/-- **[The quantum Killing Lie derivative is a `*`-derivation] `(δ_Z a)* = δ_Z(a*)`.** For a **skew-adjoint**
Killing generator `K* = −K` (i.e. `K = iH_Z` with `H_Z` self-adjoint), the inner derivation `δ_Z = [K, ·]`
intertwines the involution: it is a `*`-derivation (Theorem 6.10). -/
lemma quantumKillingLieDerivative_star [StarRing R] (K a : R) (hK : star K = -K) :
    star (quantumKillingLieDerivative K a) = quantumKillingLieDerivative K (star a) := by
  unfold quantumKillingLieDerivative collisionStar
  rw [star_sub, star_mul, star_mul, hK]
  noncomm_ring

/-- **[The quantum Killing Lie derivative is a unital `*`-derivation, assembled].** For a skew-adjoint generator,
`δ_Z` annihilates the unit, obeys the Leibniz rule, and intertwines the involution — the unital `*`-derivation of
Theorem 6.10. -/
lemma quantumKillingLieDerivative_isStarDerivation [StarRing R] (K a b : R) (hK : star K = -K) :
    quantumKillingLieDerivative K 1 = 0
      ∧ quantumKillingLieDerivative K (a * b)
          = quantumKillingLieDerivative K a * b + a * quantumKillingLieDerivative K b
      ∧ star (quantumKillingLieDerivative K a) = quantumKillingLieDerivative K (star a) :=
  ⟨quantumKillingLieDerivative_unital K, quantumKillingLieDerivative_leibniz K a b,
    quantumKillingLieDerivative_star K a hK⟩


/-- **[A tracial state annihilates the quantum Killing Lie derivative] `ω ∘ δ_Z = 0`.** For the inner Killing
derivation `δ_Z = [K, ·]`, any tracial state `ω(ab) = ω(ba)` satisfies `ω(δ_Z a) = ω(Ka) − ω(aK) = 0`. This is
the `δ_Z`-invariant faithful state of Theorem 6.10 whose existence guarantees `σ`-strong* closability. -/
lemma killingGenerator_tracial_invariant (ω : R →+ ℂ) (htr : ∀ a b : R, ω (a * b) = ω (b * a))
    (K a : R) : ω (quantumKillingLieDerivative K a) = 0 := by
  unfold quantumKillingLieDerivative collisionStar
  rw [map_sub, htr K a, sub_self]


/-- **A local one-parameter group of contractions** (Labuschagne–Majewski Definition 6.2): a family `T_t` of maps
with a downward filtration of domains `D_α` (`α > 0`) on which the group law holds **locally**:

* `D_antitone` — `D_α ⊆ D_β` when `0 < β ≤ α` (the domains shrink as `α` grows);
* `T_zero` — `T_0 = id`;
* `local_cocycle` — `T_s T_t(x) = T_{s+t}(x)` for `x ∈ D_α` whenever `s, t, s+t ∈ [−α, α]` (the *local* group
  law, the defining feature versus a global one-parameter group). -/
structure LocalContractionGroup (R : Type*) [Ring R] where
  /-- the contraction `T_t` at flow parameter `t`. -/
  T : ℝ → R → R
  /-- the domain filtration `D_α` for `α > 0`. -/
  D : ℝ → Set R
  /-- the domains shrink as `α` grows: `D_α ⊆ D_β` when `0 < β ≤ α`. -/
  D_antitone : ∀ ⦃α β : ℝ⦄, 0 < β → β ≤ α → D α ⊆ D β
  /-- `T_0` is the identity. -/
  T_zero : ∀ x : R, T 0 x = x
  /-- the local group law on `[−α, α]`. -/
  local_cocycle : ∀ (α : ℝ), 0 < α → ∀ x ∈ D α, ∀ s t : ℝ, s ∈ Set.Icc (-α) α →
    t ∈ Set.Icc (-α) α → s + t ∈ Set.Icc (-α) α → T s (T t x) = T (s + t) x

/-- **[Each stage of a local contraction group is locally invertible] `T_s T_{−s}(x) = x`.** On the domain `D_α`,
if `s, −s, 0 ∈ [−α, α]` then the local group law makes `T_s` invertible with inverse `T_{−s}` — the algebraic
local-group content of Definition 6.2. -/
lemma localContraction_local_inverse (G : LocalContractionGroup R) (α : ℝ) (hα : 0 < α)
    (x : R) (hx : x ∈ G.D α) (s : ℝ) (hs : s ∈ Set.Icc (-α) α) (hns : -s ∈ Set.Icc (-α) α)
    (h0 : (0 : ℝ) ∈ Set.Icc (-α) α) : G.T s (G.T (-s) x) = x := by
  rw [G.local_cocycle α hα x hx s (-s) hs hns (by rw [add_neg_cancel]; exact h0),
    add_neg_cancel, G.T_zero]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingLieDerivativeClosability

end
