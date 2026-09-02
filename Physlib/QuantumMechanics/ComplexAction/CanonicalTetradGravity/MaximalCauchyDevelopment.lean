/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GeodesicCompleteness
public import Mathlib.Order.Zorn
meta import Zil

/-!
# Chain gluing and maximal Cauchy developments

This file begins the set-theoretic core of the Choquet--Bruhat--Geroch
maximal-development construction.  It does not replace spacetime gluing by a
bare invocation of Zorn's lemma:

1. developments are open regions in one ambient carrier obtained after the
   local-uniqueness identifications;
2. extension is literal inclusion fixing the common Cauchy embedding;
3. a nonempty chain is glued by the actual union of its regions;
4. the Einstein equation is inherited pointwise;
5. causal convexity and compact causal diamonds are proved for the union;
6. only then is Zorn applied to obtain a maximal development.

The fixed ambient presentation is the standard second half of Wald's gluing
argument: local uniqueness first identifies equal initial-data developments
on their common domains, after which their images can be treated as compatible
open subregions of a common carrier.  The quotient/atlas construction which
produces that presentation from arbitrary manifold carriers remains a separate
geometric layer; it is not smuggled into the Zorn step here.

`IsGloballyHyperbolicRegion` uses the causal-compact characterization:
causal convexity together with compact ambient causal diamonds.  Causality
itself is stored globally as reflexivity, transitivity, and antisymmetry of the
ambient causal relation.  On regular time-oriented Lorentzian manifolds this
is the causal-order formulation used by the maximal-development argument.

## References

* R. M. Wald, *General Relativity*, pp. 263--264, Theorem 10.2.2.
* Y. Choquet-Bruhat and R. Geroch, *Global aspects of the Cauchy
  problem in general relativity*, Commun. Math. Phys. 14 (1969).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Set

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.MaximalCauchyDevelopment

universe u v

/-- Ambient data shared after local-uniqueness identifications.  `EinsteinAt`
may be instantiated by the repository's real or complex Einstein field
equation on the selected geometric carrier. -/
structure CausalEinsteinAmbient (Ω : Type u) (S : Type v)
    [TopologicalSpace Ω] where
  /-- The causal relation `p ≤_c q`. -/
  causal : Ω → Ω → Prop
  causal_refl : ∀ p, causal p p
  causal_trans : ∀ {p q r}, causal p q → causal q r → causal p r
  causal_antisymm : ∀ {p q}, causal p q → causal q p → p = q
  /-- The fixed initial-data hypersurface in the ambient carrier. -/
  cauchyEmbedding : S → Ω
  cauchyEmbedding_injective : Function.Injective cauchyEmbedding
  /-- The (possibly complex) Einstein equation at one spacetime point. -/
  EinsteinAt : Ω → Prop

namespace CausalEinsteinAmbient

variable {Ω : Type u} {S : Type v} [TopologicalSpace Ω]

/-- The ambient causal diamond `J⁺(p) ∩ J⁻(q)`. -/
def causalDiamond (T : CausalEinsteinAmbient Ω S) (p q : Ω) : Set Ω :=
  {r | T.causal p r ∧ T.causal r q}

/-- A region is causally convex when every ambient causal segment with
endpoints in the region remains in the region. -/
def IsCausallyConvex (T : CausalEinsteinAmbient Ω S) (s : Set Ω) : Prop :=
  ∀ ⦃p q⦄, p ∈ s → q ∈ s → ∀ ⦃r⦄,
    T.causal p r → T.causal r q → r ∈ s

/-- Causal-compact global hyperbolicity for an ambient open region:
causal convexity plus compact causal diamonds for all of its endpoints. -/
def IsGloballyHyperbolicRegion
    (T : CausalEinsteinAmbient Ω S) (s : Set Ω) : Prop :=
  T.IsCausallyConvex s ∧
    ∀ p ∈ s, ∀ q ∈ s, IsCompact (T.causalDiamond p q)

/-- An Einstein Cauchy development represented as a compatible open region
of the common ambient spacetime. -/
@[ext]
structure Development (T : CausalEinsteinAmbient Ω S) where
  region : Set Ω
  isOpen_region : IsOpen region
  cauchy_mem : ∀ σ, T.cauchyEmbedding σ ∈ region
  einstein_on : ∀ p ∈ region, T.EinsteinAt p
  globallyHyperbolic : T.IsGloballyHyperbolicRegion region

namespace Development

variable {T : CausalEinsteinAmbient Ω S}

instance : PartialOrder (Development T) where
  le A B := A.region ⊆ B.region
  le_refl _ := Set.Subset.rfl
  le_trans A B C hAB hBC := Set.Subset.trans hAB hBC
  le_antisymm A B hAB hBA := by
    ext p
    exact ⟨fun hp => hAB hp, fun hp => hBA hp⟩

lemma le_def {A B : Development T} :
    A ≤ B ↔ A.region ⊆ B.region :=
  Iff.rfl

/-- The literal union of two compatible canonical developments.  All local
Einstein and openness data glue automatically; admissibility asks only for
the genuinely global causal-compact property of the union. -/
def union (A B : Development T)
    (hGH : T.IsGloballyHyperbolicRegion (A.region ∪ B.region)) :
    Development T where
  region := A.region ∪ B.region
  isOpen_region := A.isOpen_region.union B.isOpen_region
  cauchy_mem σ := Or.inl (A.cauchy_mem σ)
  einstein_on p hp := hp.elim (A.einstein_on p) (B.einstein_on p)
  globallyHyperbolic := hGH

@[simp]
lemma region_union (A B : Development T)
    (hGH : T.IsGloballyHyperbolicRegion (A.region ∪ B.region)) :
    (A.union B hGH).region = A.region ∪ B.region :=
  rfl

lemma le_union_left (A B : Development T)
    (hGH : T.IsGloballyHyperbolicRegion (A.region ∪ B.region)) :
    A ≤ A.union B hGH :=
  Set.subset_union_left

lemma le_union_right (A B : Development T)
    (hGH : T.IsGloballyHyperbolicRegion (A.region ∪ B.region)) :
    B ≤ A.union B hGH :=
  Set.subset_union_right

/-- The region of the direct union of a chain. -/
def chainUnionRegion (c : Set (Development T)) : Set Ω :=
  ⋃ A : c, A.1.region

lemma mem_chainUnionRegion_iff {c : Set (Development T)} {p : Ω} :
    p ∈ chainUnionRegion c ↔ ∃ A ∈ c, p ∈ A.region := by
  simp [chainUnionRegion]

/-- Two points lying in a chain union already lie together in one member of
the chain.  This is the key directedness fact behind both the causal-convex
and compact-diamond proofs. -/
lemma exists_chain_member_of_two_points
    {c : Set (Development T)} (hc : IsChain (· ≤ ·) c)
    {p q : Ω} (hp : p ∈ chainUnionRegion c)
    (hq : q ∈ chainUnionRegion c) :
    ∃ A ∈ c, p ∈ A.region ∧ q ∈ A.region := by
  rw [mem_chainUnionRegion_iff] at hp hq
  obtain ⟨A, hAc, hpA⟩ := hp
  obtain ⟨B, hBc, hqB⟩ := hq
  rcases hc.total hAc hBc with hAB | hBA
  · exact ⟨B, hBc, hAB hpA, hqB⟩
  · exact ⟨A, hAc, hpA, hBA hqB⟩

/-- A nonempty chain union contains the fixed Cauchy embedding. -/
lemma cauchy_mem_chainUnionRegion
    {c : Set (Development T)} (hne : c.Nonempty) (σ : S) :
    T.cauchyEmbedding σ ∈ chainUnionRegion c := by
  obtain ⟨A, hAc⟩ := hne
  rw [mem_chainUnionRegion_iff]
  exact ⟨A, hAc, A.cauchy_mem σ⟩

/-- The pointwise Einstein equation is inherited by the chain union. -/
lemma einstein_on_chainUnionRegion
    {c : Set (Development T)} {p : Ω}
    (hp : p ∈ chainUnionRegion c) :
    T.EinsteinAt p := by
  rw [mem_chainUnionRegion_iff] at hp
  obtain ⟨A, _, hpA⟩ := hp
  exact A.einstein_on p hpA

/-- The chain union is open. -/
lemma isOpen_chainUnionRegion (c : Set (Development T)) :
    IsOpen (chainUnionRegion c) := by
  unfold chainUnionRegion
  exact isOpen_iUnion fun A => A.1.isOpen_region

/-- Causal convexity survives the direct union of a chain. -/
lemma isCausallyConvex_chainUnionRegion
    {c : Set (Development T)} (hc : IsChain (· ≤ ·) c) :
    T.IsCausallyConvex (chainUnionRegion c) := by
  intro p q hp hq r hpr hrq
  obtain ⟨A, hAc, hpA, hqA⟩ :=
    exists_chain_member_of_two_points hc hp hq
  rw [mem_chainUnionRegion_iff]
  exact ⟨A, hAc, A.globallyHyperbolic.1 hpA hqA hpr hrq⟩

/-- Compact causal diamonds survive the direct union of a chain.  Once the
two endpoints are placed in a common member, causal convexity says its
ambient diamond is already the union's diamond; compactness is exactly the
member's stored global-hyperbolicity theorem. -/
lemma causalDiamond_isCompact_chainUnionRegion
    {c : Set (Development T)} (hc : IsChain (· ≤ ·) c)
    (p : Ω) (hp : p ∈ chainUnionRegion c)
    (q : Ω) (hq : q ∈ chainUnionRegion c) :
    IsCompact (T.causalDiamond p q) := by
  obtain ⟨A, _, hpA, hqA⟩ :=
    exists_chain_member_of_two_points hc hp hq
  exact A.globallyHyperbolic.2 p hpA q hqA

/-- **Global hyperbolicity is preserved by chain gluing.** -/
@[zil_level physical_theorem]
theorem globallyHyperbolic_chainUnionRegion
    {c : Set (Development T)} (hc : IsChain (· ≤ ·) c) :
    T.IsGloballyHyperbolicRegion (chainUnionRegion c) := by
  exact ⟨isCausallyConvex_chainUnionRegion hc,
    causalDiamond_isCompact_chainUnionRegion hc⟩

/-- The actual glued development associated with a nonempty chain. -/
noncomputable def chainUnion
    (c : Set (Development T)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : Development T where
  region := chainUnionRegion c
  isOpen_region := isOpen_chainUnionRegion c
  cauchy_mem := cauchy_mem_chainUnionRegion hne
  einstein_on := fun p hp => einstein_on_chainUnionRegion hp
  globallyHyperbolic := globallyHyperbolic_chainUnionRegion hc

/-- Every member embeds into the glued chain union. -/
@[zil_level physical_theorem]
theorem le_chainUnion
    (c : Set (Development T)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {A : Development T} (hAc : A ∈ c) :
    A ≤ chainUnion c hc hne := by
  intro p hp
  change p ∈ chainUnionRegion c
  rw [mem_chainUnionRegion_iff]
  exact ⟨A, hAc, hp⟩

/-- Every nonempty chain of Cauchy developments has the explicitly
constructed chain union as an upper bound. -/
theorem nonempty_chain_bddAbove
    (c : Set (Development T)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) :
    BddAbove c := by
  refine ⟨chainUnion c hc hne, ?_⟩
  intro A hAc
  exact le_chainUnion c hc hne hAc

/-- **Existence of a maximal globally hyperbolic Einstein Cauchy
development.** Zorn is applied only after the explicit chain-union upper
bound has been constructed and its global hyperbolicity proved. -/
@[zil_level physical_theorem]
theorem exists_maximal (base : Development T) :
    ∃ M : Development T, IsMax M := by
  letI : Nonempty (Development T) := ⟨base⟩
  apply zorn_le_nonempty
  intro c hc hne
  exact nonempty_chain_bddAbove c hc hne

/-- A maximal development admits no proper compatible extension. -/
theorem eq_of_maximal_extension {M N : Development T}
    (hM : IsMax M) (hMN : M ≤ N) :
    N = M :=
  le_antisymm (hM hMN) hMN

/-- An admissible binary union is a common extension.  This isolates the
local-uniqueness patching obligation needed for uniqueness of maximal
developments from the already-completed chain-gluing/Zorn existence proof. -/
theorem exists_joint_extension_of_union
    (A B : Development T)
    (hGH : T.IsGloballyHyperbolicRegion (A.region ∪ B.region)) :
    ∃ C : Development T, A ≤ C ∧ B ≤ C :=
  ⟨A.union B hGH, A.le_union_left B hGH, A.le_union_right B hGH⟩

/-- Maximal developments are unique once local uniqueness supplies a common
extension for every pair.  In the arbitrary-carrier formulation this equality
is read as uniqueness up to the fixed-Cauchy isometry used to put both
developments in the common ambient presentation. -/
@[zil_level physical_theorem]
theorem maximal_unique_of_joint_extension
    (hjoint : ∀ A B : Development T,
      ∃ C : Development T, A ≤ C ∧ B ≤ C)
    {M N : Development T} (hM : IsMax M) (hN : IsMax N) :
    M = N := by
  obtain ⟨C, hMC, hNC⟩ := hjoint M N
  have hCM : C ≤ M := hM hMC
  have hCN : C ≤ N := hN hNC
  exact le_antisymm (hMC.trans hCN) (hNC.trans hCM)

/- ZIL-BEGIN -/

zil attach globallyHyperbolic_chainUnionRegion where
  formalizes @ "claim:the-literal-union-of-a-chain-of-causally-convex-globally-hyperbolic-development-regions-is-causally-convex-and-has-compact-causal-diamonds",
  epistemic_status @ "risky",
  supported_by @ "book:Wald-General-Relativity-Theorem-10.2.2-chain-union-step",
  caveat @ "scope:the-development-regions-have-already-been-placed-in-one-common-ambient-carrier-by-the-local-uniqueness-identifications"

zil attach le_chainUnion where
  formalizes @ "claim:every-development-in-a-nonempty-extension-chain-embeds-by-inclusion-into-the-explicitly-glued-chain-union",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Set.mem_iUnion",
  caveat @ "scope:canonical-common-ambient-representatives"

zil attach exists_maximal where
  formalizes @ "claim:if-one-globally-hyperbolic-einstein-cauchy-development-exists-then-an-explicit-chain-gluing-construction-and-zorns-lemma-produce-a-maximal-one",
  epistemic_status @ "risky",
  supported_by @ "lean:zorn_le_nonempty",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.MaximalCauchyDevelopment.CausalEinsteinAmbient.Development.globallyHyperbolic_chainUnionRegion",
  caveat @ "scope:maximality-is-among-compatible-open-regions-in-the-common-ambient-presentation-the-prior-arbitrary-manifold-quotient-gluing-layer-is-separate"

zil attach maximal_unique_of_joint_extension where
  formalizes @ "claim:any-two-maximal-cauchy-developments-are-equal-in-the-common-ambient-presentation-once-local-uniqueness-patching-gives-every-pair-a-joint-extension",
  epistemic_status @ "risky",
  supported_by @ "book:Wald-General-Relativity-Theorem-10.2.2-uniqueness-patching-step",
  caveat @ "remaining-premise:construct-the-joint-extension-from-arbitrary-carrier-developments-and-the-repositorys-local-einstein-uniqueness-up-to-isometry"

zil_file_contract physlib.maximalCauchyDevelopmentChainGluing where
  promises "The public spine represents locally identified Einstein Cauchy developments as open regions in a common causal ambient carrier. It constructs the direct union of every nonempty extension chain, proves openness, fixed-Cauchy containment, pointwise Einstein inheritance, causal convexity, and compact causal diamonds, and only then applies Zorn to produce a maximal development. A separate theorem proves uniqueness of maximal representatives from the exact remaining joint-extension patching statement."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:zorn_le_nonempty",
    "lean:IsCompact",
    "lean:IsChain.total"
  ]
  forbids_substitutes [
    "invoking-zorn-without-constructing-chain-upper-bounds",
    "declaring-global-hyperbolicity-of-the-chain-union-as-an-unproved-field",
    "calling-the-adm-phase-space-flow-itself-a-maximal-globally-hyperbolic-spacetime",
    "claiming-uniqueness-without-the-joint-extension-local-isometry-patching-obligation"
  ]
  witnessed_by [
    globallyHyperbolic_chainUnionRegion,
    le_chainUnion,
    exists_maximal,
    maximal_unique_of_joint_extension
  ]

#zil_formalization_lint physlib.maximalCauchyDevelopmentChainGluing

/- ZIL-END -/

end Development

end CausalEinsteinAmbient

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.MaximalCauchyDevelopment

end
