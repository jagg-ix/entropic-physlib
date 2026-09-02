/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.GroupTheory.Subsemigroup.Centralizer
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

/-!
# Star-algebra GNS-form and commutant identities

This module contains elementary algebraic lemmas: the form `gnsForm ω a b = ω (star a * b)`, cyclic
reproduction from the unit element, conjugate symmetry and real diagonal under a hermitian-functional
hypothesis, centralizer/commutant identities, and the equivalence between commuting with a single
Hamiltonian and vanishing of `collisionStar H X`.

It does not construct a GNS Hilbert space, quotient by null vectors, complete a pre-Hilbert space, define
bicommutant-closed sets as weakly closed operator algebras, or prove quasifree-state results.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant


section GNS
variable {A : Type*} [Ring A] [StarRing A]

/-- **The GNS pre-inner-product** `⟨a,b⟩_ω = ω(a*·b)` induced by a state `ω` — the sesquilinear form whose
is the algebraic form used before any quotient/completion `ℋ_ω`. -/
def gnsForm (ω : A → ℂ) (a b : A) : ℂ := ω (star a * b)

/-- **[Cyclic reproduction] `ω(a) = ⟨Ω,π(a)Ω⟩`** with `Ω = [1]` — `ω(a) = ⟨1,a⟩_ω`, the defining property of
the GNS cyclic vector. -/
lemma gns_cyclic (ω : A → ℂ) (a : A) : ω a = gnsForm ω 1 a := by
  rw [gnsForm, star_one, one_mul]

/-- **[Conjugate symmetry] `⟨a,b⟩_ω = conj⟨b,a⟩_ω`** — for a hermitian state `ω(a*) = conj ω(a)`. -/
lemma gns_conj_symm (ω : A → ℂ) (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a b : A) :
    gnsForm ω a b = starRingEnd ℂ (gnsForm ω b a) := by
  rw [gnsForm, gnsForm, ← herm, star_mul, star_star]

/-- **[Diagonal is real] `ω(a*·a) ∈ ℝ`** — the GNS norm-square is real (the seed of the state positivity
`ω(a*a) ≥ 0` that makes `⟨·,·⟩_ω` a pre-inner-product). -/
lemma gns_self_real (ω : A → ℂ) (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a : A) :
    (gnsForm ω a a).im = 0 := by
  have h := gns_conj_symm ω herm a a
  have him : (gnsForm ω a a).im = -(gnsForm ω a a).im := by
    conv_lhs => rw [h]; simp [Complex.conj_im]
  linarith

end GNS


section Commutant
variable {A : Type*} [Monoid A]

/-- **The commutant `𝓐'`** of a set of operators — `Set.centralizer S`, the algebra of operators commuting
with all of `S`. -/
def commutant (S : Set A) : Set A := Set.centralizer S

/-- **[`𝓐 ⊆ 𝓐''`] A set is contained in its double commutant.** -/
lemma bicommutant_subset (S : Set A) : S ⊆ commutant (commutant S) := by
  intro a ha c hc; exact (hc a ha).symm

/-- **The commutant is anti-monotone** `S ⊆ T ⟹ T' ⊆ S'`. -/
lemma commutant_antitone {S T : Set A} (h : S ⊆ T) : commutant T ⊆ commutant S :=
  Set.centralizer_subset h

/-- **[`𝓐''' = 𝓐'`] The triple commutant collapses** — the defining identity behind the bicommutant
bicommutant theorem. -/
lemma commutant_triple (S : Set A) : commutant (commutant (commutant S)) = commutant S :=
  le_antisymm (commutant_antitone (bicommutant_subset S)) (bicommutant_subset (commutant S))

/-- **A bicommutant-closed set**: a set equal to its own double commutant `S'' = S`. -/
def IsBicommutantClosed (S : Set A) : Prop := commutant (commutant S) = S

/-- **[the algebraic §3.2 structural fact] The commutant of any set is a bicommutant-closed set** `(𝓐')'' = 𝓐'` — so
`π_ω(𝓐)''` and `π_ω(𝓐)'` are bicommutant-closed sets, the objects whose centre (primarity) and triviality
(purity/irreducibility) the algebraic analyses. -/
lemma commutant_isBicommutantClosed (S : Set A) : IsBicommutantClosed (commutant S) :=
  commutant_triple S

/-- **The centre of a bicommutant-closed set** `Z(M) = M ∩ M'` — trivial iff `M` is a factor (the state is
primary). -/
def commutantCentre (S : Set A) : Set A := S ∩ commutant S

end Commutant


section Liouvillian
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
variable {A : Type*} [Ring A]

/-- **[Commutant = `ker ad_H`] `X ∈ {H}' ⟺ collisionStar H X = 0`.** The bicommutant commutant of `{H}` is the
kernel of the Liouville/adjoint generator `ad_H = collisionStar H = [H,·]` — the Saveliev `ad` superoperator,
i.e. the TFD `hatHamiltonian` / `emFieldAdjoint`. The observables commuting with `H` are exactly those the
Liouvillian annihilates. -/
lemma mem_commutant_iff_collisionStar_zero (H X : A) :
    X ∈ commutant ({H} : Set A) ↔ collisionStar H X = 0 := by
  rw [commutant, Set.mem_centralizer_iff, collisionStar, sub_eq_zero]
  constructor
  · intro h; exact h H rfl
  · intro h m hm
    rw [Set.mem_singleton_iff] at hm
    subst hm
    simpa using h

/-- **The Hamiltonian lies in its own commutant** `H ∈ {H}'` — `[H,H] = 0` (`collisionStar_self`), the
conserved/stationary observable (the equilibrium of the Liouville flow). -/
lemma hamiltonian_mem_own_commutant (H : A) : H ∈ commutant ({H} : Set A) :=
  (mem_commutant_iff_collisionStar_zero H H).mpr (collisionStar_self H)

end Liouvillian

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant

end
