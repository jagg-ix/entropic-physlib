/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4

/-!
# The icosahedral group is the rotation subgroup of Sorkin's `su(5)` net symmetry

The icosahedral stress-energy development (`IcosahedralStressEnergyAction`) builds its Reynolds
(group-averaging) projector on the icosahedral rotation group `IcosahedralGroup = alternatingGroup
(Fin 5) = A₅`. Sorkin's `R⁴` simplectic net (`LeviCivita.SorkinSimplecticNetR4`) has isotropy the
`su(5)` Weyl group `Su5WeylGroup = Equiv.Perm (Fin 5) = S₅` (coordinate permutations), extended by a
charge-conjugation `Z₂`. These are **the same five letters**: `A₅` is exactly the index-`2` (even,
rotation) subgroup of `S₅`. So the group the stress-energy Reynolds operator averages over is the
rotation half of the discrete symmetry of the `R⁴` spacetime net.

This module makes that link precise, reusing the symbols of both files:

* `icosahedralInclusion` — the subgroup inclusion `A₅ ↪ S₅` (`IcosahedralGroup →* Su5WeylGroup`);
* `icosahedralGroup_index_two_in_su5Weyl` — `|S₅| = 2·|A₅|` (`120 = 2·60`): the icosahedral group is
  the index-`2` rotation subgroup of the net's Weyl isotropy;
* `icosahedral_preserves_affineWeight` / `icosahedral_permutes_affineWeightBasis` — `A₅` acts on the
  `su(5)` weight system, i.e. it permutes the vertices of Sorkin's `R⁴` net (reusing
  `weyl_permutes_affineWeightBasis`);
* `icosahedral_commutes_weightConjugation` — the charge-conjugation `Z₂` (`weightConjugation`,
  `5 ↔ 5̄`) commutes with the icosahedral permutations, so it is an independent factor, *not* the
  even/odd `Z₂ = S₅/A₅` parity;
* `weylInvariant_imp_icosahedralInvariant` — a stress-energy tensor invariant under the full net Weyl
  group `S₅` is a fortiori icosahedrally invariant: the Reynolds projector of
  `IcosahedralStressEnergyAction` targets a subspace *containing* the net-Weyl-invariant tensors.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], Sec. III A (the isotropic group `S₅` with an overall sign `Z₂`). Reuses
  `IcosahedralStressEnergyAction` (`IcosahedralGroup`, `tensorPerm`, `IcosahedrallyInvariant`,
  `icosahedralAverage`) and `LeviCivita.SorkinSimplecticNetR4` (`Su5WeylGroup`, `IsAffineWeight`,
  `affineWeightBasis`, `weyl_permutes_affineWeightBasis`, `weightConjugation`). Mathlib
  (`alternatingGroup`, `Subgroup.subtype`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry

open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

/-! ## `A₅` is the index-2 rotation subgroup of the `su(5)` Weyl isotropy `S₅` -/

/-- **The inclusion `A₅ ↪ S₅`** of the icosahedral rotation group into Sorkin's `su(5)` Weyl group
(the isotropy of the `R⁴` net): the alternating subgroup's inclusion into the full permutation group. -/
def icosahedralInclusion : IcosahedralGroup →* Su5WeylGroup := (alternatingGroup (Fin 5)).subtype

/-- **The icosahedral group is index `2` in the net's Weyl group**: `|S₅| = 2·|A₅|`, i.e. `120 = 2·60`.
The icosahedral rotation group `A₅` is the even (rotation) half of Sorkin's coordinate-permutation
isotropy `S₅`; the odd half is the reflection coset. -/
lemma icosahedralGroup_index_two_in_su5Weyl :
    Fintype.card Su5WeylGroup = 2 * Fintype.card IcosahedralGroup := by
  rw [su5WeylGroup_card, card_icosahedralGroup]

/-! ## `A₅` acts on the `su(5)` weight system — it permutes the `R⁴`-net vertices -/

/-- **The icosahedral group preserves the affine-weight (traceless) condition**: permuting a weight
vector's components by an even permutation keeps it summing to zero — `A₅` acts on the `su(5)` weight
system underlying Sorkin's affine coordinates. -/
lemma icosahedral_preserves_affineWeight (g : IcosahedralGroup) (v : Fin 5 → ℝ)
    (h : IsAffineWeight v) : IsAffineWeight (fun i => v ((g : Equiv.Perm (Fin 5)) i)) := by
  unfold IsAffineWeight at *
  rw [Equiv.sum_comp (g : Equiv.Perm (Fin 5)) v]; exact h

/-- **The icosahedral group permutes the `su(5)` weight basis** (the `R⁴`-net vertices): `g · e_j =
e_{g j}`, restricting `weyl_permutes_affineWeightBasis` to the even permutations. -/
lemma icosahedral_permutes_affineWeightBasis (g : IcosahedralGroup) (j : Fin 5) :
    (fun i => affineWeightBasis 5 j ((g : Equiv.Perm (Fin 5)).symm i))
      = affineWeightBasis 5 ((g : Equiv.Perm (Fin 5)) j) :=
  weyl_permutes_affineWeightBasis (g : Equiv.Perm (Fin 5)) j

/-- **The charge-conjugation `Z₂` is independent of the icosahedral permutations**: weight negation
`5 ↔ 5̄` (`weightConjugation`) commutes with reindexing by any `g ∈ A₅`. So Sorkin's overall-sign `Z₂`
is a separate factor, distinct from the even/odd parity `Z₂ = S₅/A₅` of the permutation group. -/
lemma icosahedral_commutes_weightConjugation (g : IcosahedralGroup) (v : Fin 5 → ℝ) :
    (fun i => weightConjugation v ((g : Equiv.Perm (Fin 5)) i))
      = weightConjugation (fun i => v ((g : Equiv.Perm (Fin 5)) i)) := by
  funext i; simp [weightConjugation]

/-! ## The Reynolds subspace contains the net-Weyl-invariant tensors -/

/-- **Full net-Weyl invariance implies icosahedral invariance.** A stress-energy tensor fixed by the
whole `su(5)` Weyl isotropy `S₅` of the `R⁴` net (under a representation `ρ`) is a fortiori fixed by
the icosahedral subgroup `A₅` — so the icosahedrally-invariant subspace that the Reynolds projector
`icosahedralAverage` lands in *contains* the fully net-symmetric tensors. -/
lemma weylInvariant_imp_icosahedralInvariant {ι : Type*}
    (ρ : Su5WeylGroup →* Equiv.Perm ι) (T : RiemannTensor ι)
    (h : ∀ σ : Su5WeylGroup, tensorPerm (ρ σ) T = T) :
    IcosahedrallyInvariant (ρ.comp icosahedralInclusion) T :=
  fun γ => h (icosahedralInclusion γ)

end Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry
