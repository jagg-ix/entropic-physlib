/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SelfAdjoint
meta import Zil

/-!
# Type-III local nets and affiliated unbounded generators

This module supplies the operator-algebraic carrier needed to move the continuum entropic-time and
AQFT constructions beyond finite matrices.  It uses Mathlib's concrete von Neumann algebras on a
Hilbert space and defines Murray--von Neumann equivalence, infinite projections, factors, and type-III
factors without invoking a matrix trace.

## A. Projection classification

Type III is expressed by the standard projection criterion: a factor is type III when every nonzero
projection in it is infinite.  This is deliberately weaker than a classification as the unique
hyperfinite type `III₁` factor, which additionally requires hyperfiniteness and Connes-spectrum data.

## B. Concrete local nets

A concrete net has von Neumann algebras as fibres.  Forgetting the bundles recovers the repository's
set-based Hadamard local net exactly, while a type-III net proves local primarity automatically.

## C. Affiliated unbounded observables

An unbounded partial linear operator is affiliated with a von Neumann algebra when every unitary in
the commutant preserves its domain and commutes with its action.  This is the bridge by which
self-adjoint continuum Schrödinger generators belong to local type-III observable algebras without
pretending that they are bounded algebra elements.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open VonNeumannAlgebra
open LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev BoundedOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →L[ℂ] H

/-! ## A. Factors and type-III projections -/

/-- Scalar multiples of the identity operator. -/
def scalarOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Set (BoundedOperator H) :=
  Set.range fun z : ℂ => z • (1 : BoundedOperator H)

/-- The centre `M ∩ M'` of a concrete von Neumann algebra. -/
def factorCentre (M : VonNeumannAlgebra H) : Set (BoundedOperator H) :=
  (M : Set (BoundedOperator H)) ∩ (M.commutant : Set (BoundedOperator H))

/-- A concrete von Neumann algebra is a factor when its centre consists exactly of scalars. -/
def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  factorCentre M = scalarOperators H

/-- Murray--von Neumann equivalence *inside `M`*, witnessed by a partial isometry belonging to `M`. -/
def MurrayVonNeumannEquivalentIn (M : VonNeumannAlgebra H)
    (p q : BoundedOperator H) : Prop :=
  ∃ v : BoundedOperator H, v ∈ M ∧ star v * v = p ∧ v * star v = q

/-- Every star projection is Murray--von Neumann equivalent to itself. -/
lemma murrayVonNeumannEquivalentIn_refl {M : VonNeumannAlgebra H} {p : BoundedOperator H}
    (hpM : p ∈ M) (hp : IsStarProjection p) : MurrayVonNeumannEquivalentIn M p p := by
  refine ⟨p, hpM, ?_, ?_⟩
  · rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-- Murray--von Neumann equivalence is symmetric. -/
lemma murrayVonNeumannEquivalentIn_symm {M : VonNeumannAlgebra H}
    {p q : BoundedOperator H} (h : MurrayVonNeumannEquivalentIn M p q) :
    MurrayVonNeumannEquivalentIn M q p := by
  obtain ⟨v, hvM, hvp, hvq⟩ := h
  refine ⟨star v, star_mem hvM, ?_, ?_⟩
  · simpa only [star_star] using hvq
  · simpa only [star_star] using hvp

/-- `q` is a star subprojection of `p`. -/
def IsSubprojection (q p : BoundedOperator H) : Prop :=
  IsStarProjection q ∧ IsStarProjection p ∧ q * p = q ∧ p * q = q

/-- A projection in `M` is infinite when it is equivalent *within `M`* to a proper subprojection. -/
def IsInfiniteProjection (M : VonNeumannAlgebra H) (p : BoundedOperator H) : Prop :=
  p ∈ M ∧ IsStarProjection p ∧
    ∃ q : BoundedOperator H,
      q ∈ M ∧ IsSubprojection q p ∧ q ≠ p ∧ MurrayVonNeumannEquivalentIn M p q

/-- A finite projection is a star projection which is not infinite. -/
def IsFiniteProjection (M : VonNeumannAlgebra H) (p : BoundedOperator H) : Prop :=
  p ∈ M ∧ IsStarProjection p ∧ ¬ IsInfiniteProjection M p

/-- A type-III factor: every nonzero projection in the factor is infinite. -/
def IsTypeIII (M : VonNeumannAlgebra H) : Prop :=
  IsFactor M ∧
    ∀ p : BoundedOperator H, p ∈ M → p ≠ 0 → IsStarProjection p → IsInfiniteProjection M p

/-- A type-III algebra is a factor. -/
lemma IsTypeIII.isFactor {M : VonNeumannAlgebra H} (hM : IsTypeIII M) : IsFactor M :=
  hM.1

/-- Every nonzero projection in a type-III algebra is infinite. -/
lemma IsTypeIII.infinite_of_mem {M : VonNeumannAlgebra H} (hM : IsTypeIII M)
    {p : BoundedOperator H} (hpM : p ∈ M) (hp0 : p ≠ 0) (hp : IsStarProjection p) :
    IsInfiniteProjection M p :=
  hM.2 p hpM hp0 hp

/-- Type-III factors contain no nonzero finite projections. -/
theorem IsTypeIII.no_nonzero_finite_projection {M : VonNeumannAlgebra H} (hM : IsTypeIII M)
    {p : BoundedOperator H} (hpM : p ∈ M) (hp0 : p ≠ 0) :
    ¬ IsFiniteProjection M p := by
  intro hpFinite
  exact hpFinite.2.2 (hM.infinite_of_mem hpM hp0 hpFinite.2.1)

/-! ## B. Concrete type-III local nets -/

/-- A local net whose fibres are bundled concrete von Neumann algebras. -/
structure ConcreteLocalNet (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) [Preorder ι] where
  /-- The von Neumann algebra associated with a region. -/
  alg : ι → VonNeumannAlgebra H
  /-- Causal complement of a region. -/
  compl : ι → ι
  /-- Isotony of the bundled algebras. -/
  isotony : ∀ ⦃O₁ O₂ : ι⦄, O₁ ≤ O₂ → alg O₁ ≤ alg O₂
  /-- Every region lies below its double causal complement. -/
  le_compl_compl : ∀ O : ι, O ≤ compl (compl O)
  /-- Locality in bundled commutant form. -/
  locality : ∀ ⦃O₁ O₂ : ι⦄, O₁ ≤ compl O₂ → alg O₁ ≤ (alg O₂).commutant

variable {ι : Type*} [Preorder ι]

/-- Forgetting the von Neumann bundles gives the existing set-based local-net structure. -/
def ConcreteLocalNet.toLocalNet (N : ConcreteLocalNet H ι) :
    LocalNet (BoundedOperator H) ι where
  alg O := N.alg O
  compl := N.compl
  isotony := by
    intro O₁ O₂ h a ha
    exact N.isotony h ha
  le_compl_compl := N.le_compl_compl
  locality := by
    intro O₁ O₂ h
    intro a ha
    have ha' : a ∈ (N.alg O₂).commutant := N.locality h ha
    rw [VonNeumannAlgebra.mem_commutant_iff] at ha'
    intro g hg
    exact ha' g hg

/-- A concrete local net all of whose local algebras are type-III factors. -/
structure ConcreteTypeIIINet (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) [Preorder ι] extends ConcreteLocalNet H ι where
  /-- Type-III classification of every local algebra. -/
  typeIII : ∀ O : ι, IsTypeIII (alg O)

/-- A type-III local net is locally primary: every local centre is exactly the scalars. -/
theorem ConcreteTypeIIINet.localPrimarity (N : ConcreteTypeIIINet H ι) (O : ι) :
    LocalPrimarity N.toConcreteLocalNet.toLocalNet (scalarOperators H) O := by
  change ((N.alg O : Set (BoundedOperator H)) ∩
    Set.centralizer (N.alg O : Set (BoundedOperator H))) = scalarOperators H
  simpa only [IsFactor, factorCentre,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant,
    VonNeumannAlgebra.coe_commutant] using
    (N.typeIII O).isFactor

/-- No local type-III algebra contains a nonzero finite projection. -/
theorem ConcreteTypeIIINet.no_local_nonzero_finite_projection (N : ConcreteTypeIIINet H ι)
    (O : ι) {p : BoundedOperator H} (hp : p ∈ N.alg O) (hp0 : p ≠ 0) :
    ¬ IsFiniteProjection (N.alg O) p :=
  (N.typeIII O).no_nonzero_finite_projection hp hp0

/-! ## C. Affiliated unbounded generators -/

/-- An unbounded operator is affiliated with `M` when commutant unitaries preserve its domain and
intertwine its action.  This is the correct membership notion for unbounded observables. -/
def IsAffiliated (T : H →ₗ.[ℂ] H) (M : VonNeumannAlgebra H) : Prop :=
  ∀ (U : BoundedOperator H), U ∈ M.commutant → U ∈ unitary (BoundedOperator H) →
    ∀ (x : H) (hx : x ∈ T.domain),
      ∃ hxU : U x ∈ T.domain, T ⟨U x, hxU⟩ = U (T ⟨x, hx⟩)

/-- Affiliation is monotone under enlargement of the observable algebra. -/
lemma IsAffiliated.mono {T : H →ₗ.[ℂ] H} {M N : VonNeumannAlgebra H}
    (hT : IsAffiliated T M) (hMN : M ≤ N) : IsAffiliated T N := by
  intro U hUN hU x hx
  apply hT U ?_ hU x hx
  rw [VonNeumannAlgebra.mem_commutant_iff] at hUN ⊢
  intro g hg
  exact hUN g (hMN hg)

/-- A local type-III net equipped with self-adjoint, affiliated, genuinely unbounded generators.
This packages the continuum dynamics without coercing unbounded generators into bounded fibres. -/
structure TypeIIIUnboundedDynamics (N : ConcreteTypeIIINet H ι) where
  /-- The unbounded generator localized in each region. -/
  generator : ι → H →ₗ.[ℂ] H
  /-- Each generator is densely defined and closable. -/
  isUnbounded : ∀ O : ι, (generator O).IsUnbounded
  /-- Each regional generator is self-adjoint. -/
  isSelfAdjoint : ∀ O : ι, IsSelfAdjoint (generator O)
  /-- Each regional generator is affiliated with its local type-III algebra. -/
  affiliated : ∀ O : ι, IsAffiliated (generator O) (N.alg O)

/-- The dynamics carrier supplies a real spectrum for every regional generator. -/
theorem TypeIIIUnboundedDynamics.spectrum_real {N : ConcreteTypeIIINet H ι}
    (D : TypeIIIUnboundedDynamics N) (O : ι) :
    σ (D.generator O) ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real (D.isSelfAdjoint O)

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.IsTypeIII.no_nonzero_finite_projection where
  formalizes @ "claim:a-type-iii-factor-has-no-nonzero-finite-projection",
  supported_by @ "definition:murray-von-neumann-type-iii-factor",
  epistemic_status @ risky

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.ConcreteTypeIIINet.localPrimarity where
  formalizes @ "claim:type-iii-local-algebras-are-factors-and-therefore-locally-primary",
  requires @ "claim:each-local-algebra-is-type-iii",
  caveat @ "claim:does-not-prove-that-a-particular-hadamard-or-araki-woods-net-is-type-iii"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.TypeIIIUnboundedDynamics.spectrum_real where
  supported_by @ "lean:ContinuousLinearMap.adjoint",
  formalizes @ "claim:self-adjoint-unbounded-generators-affiliated-with-local-type-iii-algebras-have-real-spectrum",
  caveat @ "claim:affiliation-and-self-adjointness-are-explicit-data-not-consequences-of-type-iii-alone"

zil_file_contract physlib.typeIIIUnboundedLocalDynamics where
  promises "Concrete local von Neumann algebras can be classified as type III by their projections, recover the existing Hadamard local-net API, and carry self-adjoint unbounded generators through affiliation with each local algebra."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:VonNeumannAlgebra", "lean:LinearPMap.IsSelfAdjoint.spectrum_real"]
  forbids_substitutes ["finite matrix traces used as type-III modular data",
    "unbounded generators coerced into bounded local-algebra elements",
    "a concrete hyperfinite III1 classification inferred from the abstract type-III carrier"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.IsTypeIII.no_nonzero_finite_projection,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.ConcreteTypeIIINet.localPrimarity,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.TypeIIIUnboundedDynamics.spectrum_real]

/- ZIL-END -/
