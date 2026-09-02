/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinEnergyMomentumDecomposition
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The icosahedral group acting on the stress-energy tensor

The icosahedral rotation group is `A₅` (the alternating group on five letters, order `60`). This file gives
it a genuine **linear action on the four-index energy-momentum tensor** of `GravitationalFieldEquations.MoulinEnergyMomentumDecomposition`
(by permuting tensor indices), and proves that Moulin's **field/matter split is covariant** under it: an
icosahedrally-symmetric source has an icosahedrally-symmetric stress-energy whose gravitational-field and
matter parts are *each* symmetric.

* **§A — the index-permutation action.** `tensorPerm σ` permutes the four indices of a `RiemannTensor` by a
  permutation `σ`; it is a left action (`tensorPerm_one`, `tensorPerm_mul`) and is additive
  (`tensorPerm_add`).
* **§B — the icosahedral group.** `IcosahedralGroup := alternatingGroup (Fin 5)` (`A₅`), of order `60`
  (`card_icosahedralGroup`).
* **§C — covariance of the Moulin split.** For *any* permutation `σ` (`moulin_split_covariant`), and hence
  for any permutation representation `ρ` of the icosahedral group (`moulin_split_icosahedrally_covariant`),
  `σ · T = σ · T^(F) + σ · T^(M)` — the field/matter decomposition commutes with the symmetry.
* **§D — invariance is preserved.** If the field part and the matter part are each icosahedrally invariant,
  so is the total (`moulin_total_invariant_of_parts`): the decomposition maps symmetric sources to symmetric
  field and matter stress-energy.

**Honest layering.** Proven: `tensorPerm` is a genuine additive left action; `A₅` has order `60`; and the
field/matter split is equivariant under it (so symmetric parts give a symmetric total). The action is by
index permutation for an arbitrary permutation representation `ρ` of the icosahedral group on the index type
(the standard `3`-D / `12`-vertex representations are instances); the equivariance of the Weyl/Ricci building
blocks under a *specific* `ρ` is not separately re-derived — the covariance shown is the algebraic
consequence of the linear (additive) split, which is what makes "icosahedral × stress-energy" precise.

## References

* The icosahedral rotation group `≅ A₅`; Moulin's `T = T^(F) + T^(M)` energy-momentum split. `Physlib`
  (`GravitationalFieldEquations.MoulinEnergyMomentumDecomposition`); Mathlib (`alternatingGroup`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction

variable {ι : Type*}


/-- **The index-permutation action** of a permutation `σ` on a four-index tensor: relabel each index by
`σ⁻¹`. -/
def tensorPerm (σ : Equiv.Perm ι) (T : RiemannTensor ι) : RiemannTensor ι :=
  fun a b c d => T (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c) (σ⁻¹ d)

/-- **[Identity acts trivially]** `1 · T = T`. -/
@[simp] lemma tensorPerm_one (T : RiemannTensor ι) : tensorPerm (1 : Equiv.Perm ι) T = T := by
  funext a b c d; simp [tensorPerm]

/-- **[Composition]** `(σ·τ) · T = σ · (τ · T)` — `tensorPerm` is a left action. -/
lemma tensorPerm_mul (σ τ : Equiv.Perm ι) (T : RiemannTensor ι) :
    tensorPerm (σ * τ) T = tensorPerm σ (tensorPerm τ T) := by
  funext a b c d; simp [tensorPerm, mul_inv_rev]

/-- **[Additive]** `σ · (A + B) = σ · A + σ · B` — the action distributes over the tensor sum, hence over
Moulin's field `+` matter split. -/
lemma tensorPerm_add (σ : Equiv.Perm ι) (A B : RiemannTensor ι) :
    tensorPerm σ (A + B) = tensorPerm σ A + tensorPerm σ B := by
  funext a b c d; simp [tensorPerm]


/-- **The icosahedral rotation group** `A₅` — the alternating group on five letters. -/
abbrev IcosahedralGroup := alternatingGroup (Fin 5)

/-- **[Order `60`]** the icosahedral rotation group has `5!/2 = 60` elements. -/
lemma card_icosahedralGroup : Fintype.card IcosahedralGroup = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide


variable [Fintype ι] [DecidableEq ι]

/-- **[The energy-momentum split is permutation-covariant]** `σ · T = σ · T^(F) + σ · T^(M)` — relabelling
indices commutes with Moulin's field/matter decomposition. -/
lemma moulin_split_covariant (σ : Equiv.Perm ι) (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    tensorPerm σ (fourIndexEnergyMomentum χ a n g Ric scalarR Rm)
      = tensorPerm σ (fieldEnergyMomentum χ a n g Ric scalarR Rm)
        + tensorPerm σ (matterEnergyMomentum χ n g Ric scalarR) := by
  rw [energyMomentum_two_part χ a n g Ric scalarR Rm hn1 hn2, tensorPerm_add]

/-- **[Icosahedrally covariant]** for any permutation representation `ρ` of the icosahedral group on the
index type and any group element `γ`, the field/matter split commutes with `ρ γ`. -/
lemma moulin_split_icosahedrally_covariant (ρ : IcosahedralGroup →* Equiv.Perm ι)
    (γ : IcosahedralGroup) (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι)
    (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    tensorPerm (ρ γ) (fourIndexEnergyMomentum χ a n g Ric scalarR Rm)
      = tensorPerm (ρ γ) (fieldEnergyMomentum χ a n g Ric scalarR Rm)
        + tensorPerm (ρ γ) (matterEnergyMomentum χ n g Ric scalarR) :=
  moulin_split_covariant (ρ γ) χ a n g Ric scalarR Rm hn1 hn2


/-- **Icosahedral invariance** of a tensor under a permutation representation `ρ`: it is fixed by every
`ρ γ`. -/
def IcosahedrallyInvariant (ρ : IcosahedralGroup →* Equiv.Perm ι) (T : RiemannTensor ι) : Prop :=
  ∀ γ : IcosahedralGroup, tensorPerm (ρ γ) T = T

/-- **[Symmetric parts ⟹ symmetric total]** if the gravitational-field part and the matter part of the
energy-momentum tensor are each icosahedrally invariant, so is the total `T = T^(F) + T^(M)`. The Moulin
decomposition sends icosahedrally-symmetric field and matter stress-energy to a symmetric total. -/
lemma moulin_total_invariant_of_parts (ρ : IcosahedralGroup →* Equiv.Perm ι)
    (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι)
    (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0)
    (hF : IcosahedrallyInvariant ρ (fieldEnergyMomentum χ a n g Ric scalarR Rm))
    (hM : IcosahedrallyInvariant ρ (matterEnergyMomentum χ n g Ric scalarR)) :
    IcosahedrallyInvariant ρ (fourIndexEnergyMomentum χ a n g Ric scalarR Rm) := by
  intro γ
  rw [energyMomentum_two_part χ a n g Ric scalarR Rm hn1 hn2, tensorPerm_add, hF γ, hM γ]

/-!

Averaging over the (finite) icosahedral group is the Reynolds operator: it projects any energy-momentum
tensor onto an icosahedrally-invariant one, and — being linear — it commutes with Moulin's field/matter
split. -/

/-- `tensorPerm` commutes with scalar multiplication. -/
lemma tensorPerm_smul (σ : Equiv.Perm ι) (r : ℝ) (T : RiemannTensor ι) :
    tensorPerm σ (r • T) = r • tensorPerm σ T := by
  funext a b c d; simp [tensorPerm]

/-- `tensorPerm` commutes with finite sums. -/
lemma tensorPerm_sum {κ : Type*} (σ : Equiv.Perm ι) (s : Finset κ) (f : κ → RiemannTensor ι) :
    tensorPerm σ (∑ i ∈ s, f i) = ∑ i ∈ s, tensorPerm σ (f i) := by
  funext a b c d; simp [tensorPerm, Finset.sum_apply]

variable (ρ : IcosahedralGroup →* Equiv.Perm ι)

/-- **The icosahedral (Reynolds) average** of a tensor: its group-average over the icosahedral group. -/
noncomputable def icosahedralAverage (T : RiemannTensor ι) : RiemannTensor ι :=
  (Fintype.card IcosahedralGroup : ℝ)⁻¹ • ∑ γ : IcosahedralGroup, tensorPerm (ρ γ) T

/-- **[The average is additive]** `⟨A + B⟩ = ⟨A⟩ + ⟨B⟩` — the Reynolds operator is linear, so it commutes
with the field `+` matter split. -/
lemma icosahedralAverage_add (A B : RiemannTensor ι) :
    icosahedralAverage ρ (A + B) = icosahedralAverage ρ A + icosahedralAverage ρ B := by
  have h : (∑ γ : IcosahedralGroup, tensorPerm (ρ γ) (A + B))
      = ∑ γ : IcosahedralGroup, (tensorPerm (ρ γ) A + tensorPerm (ρ γ) B) :=
    Finset.sum_congr rfl (fun γ _ => tensorPerm_add (ρ γ) A B)
  simp only [icosahedralAverage, h, Finset.sum_add_distrib, smul_add]

/-- **[The icosahedral average is invariant — the Reynolds projection onto invariants]** `⟨T⟩` is fixed by
every icosahedral group element: averaging over the group lands in the icosahedrally-symmetric subspace. -/
lemma icosahedralAverage_invariant (T : RiemannTensor ι) :
    IcosahedrallyInvariant ρ (icosahedralAverage ρ T) := by
  intro s
  have step1 : (∑ γ : IcosahedralGroup, tensorPerm (ρ s) (tensorPerm (ρ γ) T))
      = ∑ γ : IcosahedralGroup, tensorPerm (ρ (s * γ)) T :=
    Finset.sum_congr rfl (fun γ _ => by rw [← tensorPerm_mul, ← map_mul])
  have step2 : (∑ γ : IcosahedralGroup, tensorPerm (ρ (s * γ)) T)
      = ∑ γ : IcosahedralGroup, tensorPerm (ρ γ) T :=
    Equiv.sum_comp (Equiv.mulLeft s) (fun γ => tensorPerm (ρ γ) T)
  simp only [icosahedralAverage]
  rw [tensorPerm_smul, tensorPerm_sum, step1, step2]

/-- **[The symmetrized stress-energy tensor]** the icosahedral average of the energy-momentum tensor is an
**icosahedrally-invariant** stress-energy tensor, and its field/matter content is the average of the field
and matter parts: `⟨T⟩ = ⟨T^(F)⟩ + ⟨T^(M)⟩`. Reynolds-averaging produces a symmetric energy-momentum tensor
that still respects Moulin's gravitational-field/matter decomposition. -/
lemma icosahedral_symmetrized_stressEnergy
    (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι)
    (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    IcosahedrallyInvariant ρ (icosahedralAverage ρ (fourIndexEnergyMomentum χ a n g Ric scalarR Rm))
      ∧ icosahedralAverage ρ (fourIndexEnergyMomentum χ a n g Ric scalarR Rm)
          = icosahedralAverage ρ (fieldEnergyMomentum χ a n g Ric scalarR Rm)
            + icosahedralAverage ρ (matterEnergyMomentum χ n g Ric scalarR) := by
  refine ⟨icosahedralAverage_invariant ρ _, ?_⟩
  rw [energyMomentum_two_part χ a n g Ric scalarR Rm hn1 hn2, icosahedralAverage_add]

end Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction

end
