/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame

/-!
# The tetrahedral flavor group A₄ and the three-generation standard representation

The tetrahedral rotation group is `A₄ = alternatingGroup (Fin 4)` (order 12), acting by even permutations of
the four tetrahedron vertices. It is the quotient of the binary tetrahedral group `2T` (order 24,
`TetrahedralLorentzFrame.binaryTetraCoordinates`) by its center `{±1}` — the local-Lorentz spin cover
`2T ⊂ SU(2) ⊂ SL(2,ℂ)` sitting over `A₄ ⊂ SO(3)`. In flavor models `A₄` organizes the **three fermion
generations** through its 3-dimensional irreducible representation. This file records the exact,
representation-theory-light content of that structure.

* **§A — the group and its spin double cover.** `card_A4` (`|A₄| = 12`) and
  `binaryTetra_double_covers_A4` (`|2T| = 24 = 2·|A₄|`, the two-to-one spin cover).
* **§B — the three-generation standard representation.** `sumForm` is the sum functional `∑ᵢ vᵢ` on the
  four-vertex space `Fin 4 → ℝ`; `generationSpace = ker sumForm` is the standard (traceless) subspace,
  complementary to the trivial "centroid" direction. `generation_count` proves `dim = 3` — the three
  generations as the standard representation carried by the four tetrahedral vertices, `4 = 1 ⊕ 3`.
  `generationSpace_perm_invariant` shows this subspace is invariant under the full permutation action (hence
  under `A₄`): the standard representation is well-defined as an `A₄`-representation.
  `generationSpace_no_fixed_vector` is a partial irreducibility fact: the standard representation contains no
  trivial sub-representation (its only permutation-fixed vector is `0`).

**Honest layering.** Proven exactly: the group order and its double-cover relation to `2T`, the standard
representation as the `dim = 3` kernel of the sum functional (rank–nullity), its permutation invariance, and
the absence of a trivial sub-representation (no nonzero fixed vector). *Interpretive* (not formalized here):
full irreducibility of this 3-dimensional representation and the A₄ character table (`irrep dims 1,1,1,3`,
`1²+1²+1²+3² = 12`), and the identification of the three basis directions with the physical generations
`e, μ, τ` (`Particles.ChargedLeptonGenerations`). No mass or mixing dynamics is asserted; the content is the
group and the standard-representation dimension.

## References

* Tetrahedral flavor symmetry: A₄ models of three generations (e.g. Ma–Rajasekaran; Altarelli–Feruglio,
  tribimaximal mixing). Binary polyhedral groups / McKay: `2T = E₆`. Companion to `TetrahedralLorentzFrame`
  (`2T`) and `Particles.ChargedLeptonGenerations` (the three charged-lepton generations).


-/

set_option autoImplicit false

open scoped BigOperators

open Equiv (Perm)

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.A4FlavorGenerations

open Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame


/-- **The tetrahedral group has order 12** `|A₄| = |alternatingGroup (Fin 4)| = 4!/2 = 12`. -/
lemma card_A4 : Fintype.card (alternatingGroup (Fin 4)) = 12 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- **`2T` is the two-to-one spin double cover of `A₄`** `|2T| = 24 = 2·|A₄|`: the binary tetrahedral group
(`TetrahedralLorentzFrame.binaryTetraCoordinates`, the 24-cell / unit Hurwitz quaternions in `SU(2)`) covers
the tetrahedral rotation group `A₄ ⊂ SO(3)` two-to-one, via `SU(2) → SO(3)`. -/
lemma binaryTetra_double_covers_A4 :
    binaryTetraCoordinates.card = 2 * Fintype.card (alternatingGroup (Fin 4)) := by
  rw [binaryTetraCoordinates_card, card_A4]


/-- The **sum functional** `∑ᵢ vᵢ` on the four-vertex space `Fin 4 → ℝ` — the projection onto the trivial
(centroid) direction. -/
def sumForm : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

@[simp] lemma sumForm_apply (v : Fin 4 → ℝ) : sumForm v = ∑ i, v i := rfl

lemma sumForm_surjective : Function.Surjective sumForm := fun r =>
  ⟨fun i => if i = 0 then r else 0, by rw [sumForm_apply]; simp⟩

/-- The **three-generation standard representation space** `{v : Fin 4 → ℝ | ∑ᵢ vᵢ = 0}` — the traceless
subspace of the four tetrahedron-vertex directions, complementary to the trivial centroid direction. -/
def generationSpace : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker sumForm

/-- **The standard representation is three-dimensional** `dim {∑ᵢ vᵢ = 0} = 3`: the four tetrahedral vertices
carry `4 = 1 ⊕ 3`, the trivial direction plus the three-dimensional standard representation — the three
generations. (Rank–nullity: `4 − 1 = 3`.) -/
lemma generation_count : Module.finrank ℝ generationSpace = 3 := by
  have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hrange : Module.finrank ℝ (LinearMap.range sumForm) = 1 := by
    rw [LinearMap.range_eq_top.mpr sumForm_surjective, finrank_top, Module.finrank_self]
  have hrn := sumForm.finrank_range_add_finrank_ker
  rw [hrange, hdom] at hrn
  have hker : Module.finrank ℝ generationSpace = Module.finrank ℝ (LinearMap.ker sumForm) := rfl
  rw [hker]; omega

/-- **The sum functional is permutation-invariant** `∑ᵢ v(σ i) = ∑ᵢ vᵢ` — reindexing by a permutation. -/
lemma sumForm_perm_invariant (σ : Perm (Fin 4)) (v : Fin 4 → ℝ) :
    sumForm (v ∘ σ) = sumForm v := by
  simp only [sumForm_apply, Function.comp_apply]
  exact Equiv.sum_comp σ v

/-- **The generation space is invariant under the permutation (hence `A₄`) action**: if `∑ᵢ vᵢ = 0` then
`∑ᵢ v(σ i) = 0`, so the standard representation is a well-defined `A₄`-representation on the three
generations. -/
lemma generationSpace_perm_invariant (σ : Perm (Fin 4)) (v : Fin 4 → ℝ)
    (hv : v ∈ generationSpace) : (v ∘ σ) ∈ generationSpace := by
  simp only [generationSpace, LinearMap.mem_ker] at hv ⊢
  rw [sumForm_perm_invariant]
  simpa using hv

/-- **The standard representation contains no trivial sub-representation** — a partial irreducibility fact:
the only permutation-fixed vector in the generation space is `0`. A vector fixed by every permutation is
constant, and a constant with `∑ᵢ vᵢ = 0` must vanish. So the three generations carry no invariant
(generation-blind) direction — the trivial representation does not appear. -/
lemma generationSpace_no_fixed_vector (v : Fin 4 → ℝ)
    (hv : v ∈ generationSpace) (hfix : ∀ σ : Perm (Fin 4), v ∘ σ = v) : v = 0 := by
  have hconst : ∀ i, v i = v 0 := fun i => by
    have h := congrFun (hfix (Equiv.swap i 0)) i
    simpa [Function.comp, Equiv.swap_apply_left] using h.symm
  have hsum : ∑ i, v i = 0 := by
    simpa only [generationSpace, LinearMap.mem_ker, sumForm_apply] using hv
  have h4 : (4 : ℝ) * v 0 = 0 := by
    have hrw : ∑ i, v i = ∑ _i : Fin 4, v 0 := Finset.sum_congr rfl (fun i _ => hconst i)
    rw [hrw, Finset.sum_const] at hsum
    simpa using hsum
  funext i
  simp only [Pi.zero_apply]
  rw [hconst i]; linarith [h4]

end Physlib.QuantumMechanics.ComplexAction.A4FlavorGenerations
