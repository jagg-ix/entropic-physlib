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
# The GNS representation and the von Neumann commutant (Verch 1996, §3.1–3.2)

Formalizes the algebraic kernel of the **GNS construction** and the **von Neumann (commutant) structure** that
Verch (arXiv:funct-an/9609004) uses to read off local definiteness, local primarity and Haag-duality of the
Hadamard-state representations of the Klein–Gordon field. To a state `ω` on a `*`-algebra `𝓐` the GNS theorem
attaches a triple `(ℋ_ω, π_ω, Ω_ω)` with `ω(B) = ⟨Ω_ω, π_ω(B)Ω_ω⟩`; the induced von Neumann algebra is the
double commutant `π_ω(𝓐)''`, and the state is **primary** iff the centre `π_ω(𝓐)'' ∩ π_ω(𝓐)'` is trivial,
**pure** iff `π_ω(𝓐)'` is trivial (irreducible). The Hilbert-completion/microlocal-Hadamard analysis is the
operator-analytic layer (Mathlib includes the full GNS as `PositiveLinearMap.gnsStarAlgHom`); the **algebraic
seed** is formalized here.

* **§A — the GNS pre-inner-product** (`gnsForm`, `gns_cyclic`, `gns_conj_symm`, `gns_self_real`). The form
  `⟨a,b⟩_ω = ω(a*b)`, the cyclic reproduction `ω(a) = ⟨1,a⟩_ω`, conjugate symmetry, and the reality of the
  diagonal `ω(a*a) ∈ ℝ` (the seed of positivity).
* **§B — the von Neumann commutant / bicommutant** (`commutant`, `bicommutant_subset`, `commutant_antitone`,
  `commutant_triple`, `IsVonNeumann`, `commutant_isVonNeumann`). `𝓐 ⊆ 𝓐''`, `𝓐''' = 𝓐'`, and *the commutant
  is always a von Neumann algebra* — the structural fact behind primary/pure and Haag-duality.
* **§C — the commutant is the kernel of the Liouvillian** (`mem_commutant_iff_collisionStar_zero`,
  `hamiltonian_mem_own_commutant`). `X ∈ {H}' ⟺ collisionStar H X = 0` — the von Neumann commutant of `{H}` is
  exactly the kernel of the adjoint/Liouville generator `ad_H = collisionStar H` (the Saveliev `ad` = the TFD
  hat-Hamiltonian = `emFieldAdjoint`); the Hamiltonian lies in its own commutant (`[H,H]=0`).

The Verch characterizations close the loop with the symplectic side: **primary** `⟺ R_μ` injective and **pure**
`⟺ R_μ² = −1` (the complex structure `AlgebraicQFT.SymplecticAdjointHadamard.sympForm_sq`), i.e. the von Neumann factor /
irreducibility conditions are the polarizator conditions of the quasifree (Hadamard) state.

## References

* R. Verch, arXiv:funct-an/9609004 (§3.1–3.2; the GNS triple, primary/pure, local von Neumann algebras,
  Haag-duality, type III).
* Mathlib `PositiveLinearMap.gnsStarAlgHom` (the full GNS construction), `Set.centralizer` (the commutant).
* Repo structure: `AlgebraicQFT.SymplecticAdjointHadamard.sympForm_sq` (the pure-state polarizator `R² = −1`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

/-! ## §A — the GNS pre-inner-product -/

section GNS
variable {A : Type*} [Ring A] [StarRing A]

/-- **The GNS pre-inner-product** `⟨a,b⟩_ω = ω(a*·b)` induced by a state `ω` — the sesquilinear form whose
completion is the GNS Hilbert space `ℋ_ω`. -/
def gnsForm (ω : A → ℂ) (a b : A) : ℂ := ω (star a * b)

/-- **[Cyclic reproduction] `ω(a) = ⟨Ω,π(a)Ω⟩`** with `Ω = [1]` — `ω(a) = ⟨1,a⟩_ω`, the defining property of
the GNS cyclic vector. -/
theorem gns_cyclic (ω : A → ℂ) (a : A) : ω a = gnsForm ω 1 a := by
  rw [gnsForm, star_one, one_mul]

/-- **[Conjugate symmetry] `⟨a,b⟩_ω = conj⟨b,a⟩_ω`** — for a hermitian state `ω(a*) = conj ω(a)`. -/
theorem gns_conj_symm (ω : A → ℂ) (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a b : A) :
    gnsForm ω a b = starRingEnd ℂ (gnsForm ω b a) := by
  rw [gnsForm, gnsForm, ← herm, star_mul, star_star]

/-- **[Diagonal is real] `ω(a*·a) ∈ ℝ`** — the GNS norm-square is real (the seed of the state positivity
`ω(a*a) ≥ 0` that makes `⟨·,·⟩_ω` a pre-inner-product). -/
theorem gns_self_real (ω : A → ℂ) (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a : A) :
    (gnsForm ω a a).im = 0 := by
  have h := gns_conj_symm ω herm a a
  have him : (gnsForm ω a a).im = -(gnsForm ω a a).im := by
    conv_lhs => rw [h]; simp [Complex.conj_im]
  linarith

end GNS

/-! ## §B — the von Neumann commutant / bicommutant -/

section Commutant
variable {A : Type*} [Monoid A]

/-- **The commutant `𝓐'`** of a set of operators — `Set.centralizer S`, the algebra of operators commuting
with all of `S`. -/
def commutant (S : Set A) : Set A := Set.centralizer S

/-- **[`𝓐 ⊆ 𝓐''`] A set is contained in its double commutant.** -/
theorem bicommutant_subset (S : Set A) : S ⊆ commutant (commutant S) := by
  intro a ha c hc; exact (hc a ha).symm

/-- **The commutant is anti-monotone** `S ⊆ T ⟹ T' ⊆ S'`. -/
theorem commutant_antitone {S T : Set A} (h : S ⊆ T) : commutant T ⊆ commutant S :=
  Set.centralizer_subset h

/-- **[`𝓐''' = 𝓐'`] The triple commutant collapses** — the defining identity behind the von Neumann
bicommutant theorem. -/
theorem commutant_triple (S : Set A) : commutant (commutant (commutant S)) = commutant S :=
  le_antisymm (commutant_antitone (bicommutant_subset S)) (bicommutant_subset (commutant S))

/-- **A von Neumann algebra**: a set equal to its own double commutant `S'' = S`. -/
def IsVonNeumann (S : Set A) : Prop := commutant (commutant S) = S

/-- **[Verch §3.2 structural fact] The commutant of any set is a von Neumann algebra** `(𝓐')'' = 𝓐'` — so
`π_ω(𝓐)''` and `π_ω(𝓐)'` are von Neumann algebras, the objects whose centre (primarity) and triviality
(purity/irreducibility) Verch analyses. -/
theorem commutant_isVonNeumann (S : Set A) : IsVonNeumann (commutant S) :=
  commutant_triple S

/-- **The centre of a von Neumann algebra** `Z(M) = M ∩ M'` — trivial iff `M` is a factor (the state is
primary). -/
def vnCentre (S : Set A) : Set A := S ∩ commutant S

end Commutant

/-! ## §C — the commutant is the kernel of the Liouvillian -/

section Liouvillian
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
variable {A : Type*} [Ring A]

/-- **[Commutant = `ker ad_H`] `X ∈ {H}' ⟺ collisionStar H X = 0`.** The von Neumann commutant of `{H}` is the
kernel of the Liouville/adjoint generator `ad_H = collisionStar H = [H,·]` — the Saveliev `ad` superoperator,
i.e. the TFD `hatHamiltonian` / `emFieldAdjoint`. The observables commuting with `H` are exactly those the
Liouvillian annihilates. -/
theorem mem_commutant_iff_collisionStar_zero (H X : A) :
    X ∈ commutant ({H} : Set A) ↔ collisionStar H X = 0 := by
  rw [commutant, Set.mem_centralizer_iff, collisionStar, sub_eq_zero]
  constructor
  · intro h; exact h H rfl
  · intro h m hm; rw [Set.mem_singleton_iff] at hm; subst hm; exact h

/-- **The Hamiltonian lies in its own commutant** `H ∈ {H}'` — `[H,H] = 0` (`collisionStar_self`), the
conserved/stationary observable (the equilibrium of the Liouville flow). -/
theorem hamiltonian_mem_own_commutant (H : A) : H ∈ commutant ({H} : Set A) :=
  (mem_commutant_iff_collisionStar_zero H H).mpr (collisionStar_self H)

end Liouvillian

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

end
