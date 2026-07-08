/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-!
# Local nets, Haag-duality, local primarity & definiteness (Verch 1996, Chapter 3)

Formalizes the **algebraic structure of Hadamard vacuum representations** (R. Verch, arXiv:funct-an/9609004,
Chapter 3): the axioms of a *local net of observable algebras* (isotony + locality, Eqs 3.1–3.2) and the
structural properties of Theorem 3.6 — **local definiteness** (c), **regularity** (e), **Haag-duality** (f),
**local primarity** (g) — expressed in the commutant language of `AlgebraicQFT.GNSVonNeumannHadamard` /
`ThermoFieldDynamics.KazamaTomitaTakesakiModular`.

The *deep* content of Theorem 3.6 — that the Klein–Gordon Hadamard GNS net actually *satisfies* these
properties — rests on the one-particle Hilbert-space structure, the Bosonic Fock realization, Araki's results
and the §2 continuity theorem: that is the operator-analytic layer. What is purely *structural* — the net
axioms, the property definitions, and the relations between them that hold for **any** local net from the
commutant calculus — is formalized here.

* **§A — the local net** (`LocalNet`, `locality_self`, `alg_compl_subset_commutant`). Isotony (3.1) and
  locality (3.2) in commutant form `R(O₁) ⊆ R(O₂)'`; the two easy inclusions `R(O) ⊆ R(O^⊥)'` and
  `R(O^⊥) ⊆ R(O)'`.
* **§B — Haag-duality** (`HaagDuality`, `haagDuality_imp_isVonNeumann`, `haagDuality_maximal`,
  `haagDuality_iff`). `R(O^⊥)' = R(O)` (Thm 3.6(f)): it forces `R(O)` to be a von Neumann algebra, expresses
  the **maximality** of `R(O)` (no observable can be added without breaking locality), and is exactly the
  saturation of the locality inclusion.
* **§C — local primarity & definiteness** (`LocalPrimarity`, `primarity_center`, `LocalDefiniteness`,
  `scalars_subset_iInter`). Primarity = *factor* `R(O) ∩ R(O)' = ℂ·1` (Thm 3.6(g), `vnCentre` trivial);
  definiteness `⋂_{O∋p} R(O) = ℂ·1` (Thm 3.6(c)) with its easy `ℂ·1 ⊆ ⋂` direction.
* **§D — regularity** (`alg_subset_iInter_outer`, `iUnion_inner_subset`). The easy inclusions of inner/outer
  regularity (Thm 3.6(e)) `R(O) ⊆ ⋂_{O₁⊃O} R(O₁)` and `⋃_{O₁⊂O} R(O₁) ⊆ R(O)`.

The split property (Thm 3.6(d), a type I∞ factor `R(O) ⊂ N ⊂ R(O₁)`) and the determination of `R(O)` as the
**unique hyperfinite type III₁ factor** (Thm 3.6(g)) are beyond the algebraic skeleton — type III₁ has no trace
(cf. `ThermoFieldDynamics.KazamaTomitaTakesakiModular`'s trace/factor contrast, where types I_n/II₁ have a finite trace and type
III none) and its construction needs the full Hadamard/Fock analysis.

## References

* R. Verch, arXiv:funct-an/9609004, Chapter 3, Theorem 3.6 (local definiteness, regularity, Haag-duality,
  local primarity, type III₁); Haag–Narnhofer–Stein, *principle of local definiteness*.
* Repo dependencies: `AlgebraicQFT.GNSVonNeumannHadamard` (`commutant`, `IsVonNeumann`, `vnCentre`, `commutant_isVonNeumann`),
  `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (factor/centre, the trace contrast for the type classification).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

/-! ## §A — the local net of observable algebras (Eqs 3.1–3.2) -/

/-- **[Eqs 3.1–3.2] A local net of observable algebras** `O ↦ R(O)` over an indexing poset of regions, with a
causal-complement map `O ↦ O^⊥`: **isotony** `O₁ ≤ O₂ ⟹ R(O₁) ⊆ R(O₂)`, the causal-completion order
`O ≤ O^⊥⊥`, and **locality** `O₁ ≤ O₂^⊥ ⟹ R(O₁) ⊆ R(O₂)'` (the algebras of causally disjoint regions
commute). -/
structure LocalNet (A : Type*) [Monoid A] (ι : Type*) [Preorder ι] where
  /-- The local von Neumann algebra `R(O)`. -/
  alg : ι → Set A
  /-- The causal complement `O ↦ O^⊥`. -/
  compl : ι → ι
  /-- **Isotony** (3.1). -/
  isotony : ∀ ⦃O₁ O₂ : ι⦄, O₁ ≤ O₂ → alg O₁ ⊆ alg O₂
  /-- Causal completion `O ≤ O^⊥⊥`. -/
  le_compl_compl : ∀ O : ι, O ≤ compl (compl O)
  /-- **Locality** (3.2): causally disjoint algebras commute, `R(O₁) ⊆ R(O₂)'`. -/
  locality : ∀ ⦃O₁ O₂ : ι⦄, O₁ ≤ compl O₂ → alg O₁ ⊆ commutant (alg O₂)

variable {A : Type*} [Monoid A] {ι : Type*} [Preorder ι] (N : LocalNet A ι)

/-- **[Easy Haag inclusion] `R(O) ⊆ R(O^⊥)'`** — every local observable commutes with those of the causal
complement (locality applied to `O ≤ O^⊥⊥`). One half of Haag-duality, true for any net. -/
theorem locality_self (O : ι) : N.alg O ⊆ commutant (N.alg (N.compl O)) :=
  N.locality (N.le_compl_compl O)

/-- **[Dual locality] `R(O^⊥) ⊆ R(O)'`** — the causal-complement algebra commutes with `R(O)` (locality at
`O^⊥ ≤ O^⊥`). -/
theorem alg_compl_subset_commutant (O : ι) : N.alg (N.compl O) ⊆ commutant (N.alg O) :=
  N.locality (le_refl (N.compl O))

/-! ## §B — Haag-duality (Theorem 3.6(f)) -/

/-- **[Theorem 3.6(f)] Haag-duality** `R(O^⊥)' = R(O)` — the local algebra is exactly the commutant of the
causal complement (for pure/Hadamard-vacuum states, on regular diamonds). -/
def HaagDuality (O : ι) : Prop := commutant (N.alg (N.compl O)) = N.alg O

/-- **Haag-duality makes `R(O)` a von Neumann algebra** — being a commutant, `R(O^⊥)'` is its own double
commutant (`commutant_isVonNeumann`), and Haag-duality identifies it with `R(O)`. -/
theorem haagDuality_imp_isVonNeumann {O : ι} (h : HaagDuality N O) :
    IsVonNeumann (N.alg O) := h ▸ commutant_isVonNeumann _

/-- **[Maximality of the local algebra] Haag-duality ⟹ `R(O)` is maximal.** Any set `S` of operators that
still commutes with the causal complement (`S ⊆ R(O^⊥)'`) is already contained in `R(O)`: no observable can be
added without violating locality. -/
theorem haagDuality_maximal {O : ι} (h : HaagDuality N O) {S : Set A}
    (hS : S ⊆ commutant (N.alg (N.compl O))) : S ⊆ N.alg O := by rw [← h]; exact hS

/-- **[Haag-duality = saturated locality] `R(O^⊥)' = R(O) ⟺ R(O^⊥)' ⊆ R(O)`.** The inclusion `R(O) ⊆ R(O^⊥)'`
holds for every net (`locality_self`), so Haag-duality is exactly the reverse inclusion. -/
theorem haagDuality_iff {O : ι} :
    HaagDuality N O ↔ commutant (N.alg (N.compl O)) ⊆ N.alg O :=
  ⟨fun h => h.le, fun hsub => le_antisymm hsub (locality_self N O)⟩

/-! ## §C — local primarity (factor) and local definiteness -/

/-- **[Theorem 3.6(g)] Local primarity = factor** — `R(O)` is a *factor*, `R(O) ∩ R(O)' = ℂ·1` (`vnCentre`
trivial), with `Z` the scalars `ℂ·1`. Physically: no local macroscopic observables / superselection rules. -/
def LocalPrimarity (Z : Set A) (O : ι) : Prop := vnCentre (N.alg O) = Z

/-- **A factor's centre is the scalars** `R(O) ∩ R(O)' = ℂ·1` — unfolding local primarity. -/
theorem primarity_center {Z : Set A} {O : ι} (h : LocalPrimarity N Z O) :
    N.alg O ∩ commutant (N.alg O) = Z := h

/-- **[Theorem 3.6(c)] Local definiteness** `⋂_{O∋p} R(O) = ℂ·1` — the intersection of all local algebras
shrinking to a point is trivial (`contains O` meaning `p ∈ O`). -/
def LocalDefiniteness (Z : Set A) (contains : ι → Prop) : Prop :=
  (⋂ O, ⋂ _ : contains O, N.alg O) = Z

/-- **[Easy direction of definiteness] `ℂ·1 ⊆ ⋂_{O∋p} R(O)`** — the scalars sit inside every local algebra,
hence in their intersection (the reverse inclusion is the deep Hadamard content). -/
theorem scalars_subset_iInter (Z : Set A) (contains : ι → Prop)
    (hZ : ∀ O, contains O → Z ⊆ N.alg O) :
    Z ⊆ ⋂ O, ⋂ _ : contains O, N.alg O :=
  Set.subset_iInter fun O => Set.subset_iInter fun h => hZ O h

/-! ## §D — inner / outer regularity (Theorem 3.6(e)) -/

/-- **[Outer regularity, easy inclusion] `R(O) ⊆ ⋂_{O₁ ⊃ O} R(O₁)`** — by isotony `R(O)` sits inside every
larger algebra (the reverse, `=`, is the deep regularity statement). -/
theorem alg_subset_iInter_outer (O : ι) :
    N.alg O ⊆ ⋂ O₁, ⋂ _ : O ≤ O₁, N.alg O₁ :=
  Set.subset_iInter fun _O₁ => Set.subset_iInter fun h => N.isotony h

/-- **[Inner regularity, easy inclusion] `⋃_{O₁ ⊂ O} R(O₁) ⊆ R(O)`** — by isotony every smaller algebra sits
inside `R(O)`; the deep statement is that its von Neumann closure (double commutant) equals `R(O)`. -/
theorem iUnion_inner_subset (O : ι) :
    (⋃ O₁, ⋃ _ : O₁ ≤ O, N.alg O₁) ⊆ N.alg O :=
  Set.iUnion_subset fun _O₁ => Set.iUnion_subset fun h => N.isotony h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

end
