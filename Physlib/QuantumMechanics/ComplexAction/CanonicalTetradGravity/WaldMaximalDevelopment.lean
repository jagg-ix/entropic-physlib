/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.DevelopmentDirectLimit
meta import Zil

/-!
# Wald maximal development on varying spacetime carriers

This file packages the set-theoretic maximal-development argument above the
arbitrary-carrier direct limit.

`SpacetimeDevelopment S` is a whole globally hyperbolic Einstein development
of fixed initial data `S`.  The preorder `A ≤ B` means that there exists an
injective, continuous, fixed-Cauchy causal--Einstein embedding of `A` into
`B`, with causally convex image.  A `CoherentChain` is the actual local
uniqueness output needed by Wald's proof: for every comparable pair in the
chain it selects one such embedding, and the selections commute under
identity and composition.

The coherent chain becomes a `DirectedDevelopmentSystem`.  The preceding
file then constructs its quotient carrier and proves that the quotient is
again a globally hyperbolic Einstein Cauchy development.  This gives the
chain an explicit upper bound.  Only after that construction does
`exists_maximal` invoke Zorn.

The remaining distinction from the full Choquet--Bruhat--Geroch theorem is
visible in the premise of `exists_maximal`: the repository's PDE-local
uniqueness theorem must be upgraded from uniqueness of phase trajectories to
fixed-Cauchy local spacetime isometries satisfying the coherence laws below.
No theorem in the current tree proves that upgrade, so it is not silently
assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Set

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity

namespace WaldMaximalDevelopment

open DevelopmentDirectLimit

universe u v

/-- A globally hyperbolic Einstein development of the fixed Cauchy data
carrier `S`.  All topology is stored explicitly so developments with
different point types can coexist in one Lean type. -/
structure SpacetimeDevelopment (S : Type v) where
  Point : Type u
  topology : TopologicalSpace Point
  causal : Point → Point → Prop
  causal_refl : ∀ p, causal p p
  causal_trans : ∀ {p q r}, causal p q → causal q r → causal p r
  causal_antisymm : ∀ {p q}, causal p q → causal q p → p = q
  EinsteinAt : Point → Prop
  einstein_on : ∀ p, EinsteinAt p
  cauchyEmbedding : S → Point
  cauchyEmbedding_injective : Function.Injective cauchyEmbedding
  diamond_compact : ∀ p q,
    @IsCompact Point topology {r | causal p r ∧ causal r q}

namespace SpacetimeDevelopment

variable {S : Type v}

/-- A fixed-Cauchy causal--Einstein extension embedding.  In a smooth
Lorentzian instantiation `toEmbedding` is supplied by the underlying local
isometry.  The fields retained here are exactly those consumed by the
topological causal gluing theorem. -/
structure ExtensionEmbedding
    (A B : SpacetimeDevelopment S) where
  toEmbedding : A.Point ↪ B.Point
  continuous :
    @Continuous A.Point B.Point A.topology B.topology toEmbedding
  cauchy_commutes : ∀ σ,
    toEmbedding (A.cauchyEmbedding σ) = B.cauchyEmbedding σ
  causal_map : ∀ p q,
    B.causal (toEmbedding p) (toEmbedding q) ↔ A.causal p q
  einstein_map : ∀ p,
    B.EinsteinAt (toEmbedding p) ↔ A.EinsteinAt p
  causalConvex : ∀ p q r,
    B.causal (toEmbedding p) r →
    B.causal r (toEmbedding q) →
    ∃ r₀, toEmbedding r₀ = r

namespace ExtensionEmbedding

variable {A B C : SpacetimeDevelopment S}

instance : CoeFun (ExtensionEmbedding A B) (fun _ => A.Point → B.Point) :=
  ⟨fun f => f.toEmbedding⟩

@[ext]
theorem ext {f g : ExtensionEmbedding A B}
    (h : ∀ p, f p = g p) : f = g := by
  cases f
  cases g
  simp_all only
  congr
  ext p
  exact h p

/-- Identity fixed-Cauchy extension. -/
def refl (A : SpacetimeDevelopment S) : ExtensionEmbedding A A where
  toEmbedding := Function.Embedding.refl _
  continuous := by
    letI : TopologicalSpace A.Point := A.topology
    exact continuous_id
  cauchy_commutes := fun _ => rfl
  causal_map := fun _ _ => Iff.rfl
  einstein_map := fun _ => Iff.rfl
  causalConvex := fun _ _ r _ _ => ⟨r, rfl⟩

/-- Composition of fixed-Cauchy extensions. -/
def comp (g : ExtensionEmbedding B C) (f : ExtensionEmbedding A B) :
    ExtensionEmbedding A C where
  toEmbedding := f.toEmbedding.trans g.toEmbedding
  continuous := by
    letI : TopologicalSpace A.Point := A.topology
    letI : TopologicalSpace B.Point := B.topology
    letI : TopologicalSpace C.Point := C.topology
    exact g.continuous.comp f.continuous
  cauchy_commutes σ := by
    change g (f (A.cauchyEmbedding σ)) = C.cauchyEmbedding σ
    rw [f.cauchy_commutes, g.cauchy_commutes]
  causal_map p q := by
    exact (g.causal_map (f p) (f q)).trans (f.causal_map p q)
  einstein_map p := by
    exact (g.einstein_map (f p)).trans (f.einstein_map p)
  causalConvex p q r hpr hrq := by
    obtain ⟨b, hb⟩ := g.causalConvex (f p) (f q) r hpr hrq
    have hpfb : B.causal (f p) b := by
      apply (g.causal_map (f p) b).1
      simpa [hb] using hpr
    have hbq : B.causal b (f q) := by
      apply (g.causal_map b (f q)).1
      simpa [hb] using hrq
    obtain ⟨a, ha⟩ := f.causalConvex p q b hpfb hbq
    refine ⟨a, ?_⟩
    change g (f a) = r
    rw [ha, hb]

@[simp]
theorem refl_apply (A : SpacetimeDevelopment S) (p : A.Point) :
    ExtensionEmbedding.refl A p = p :=
  rfl

@[simp]
theorem comp_apply (g : ExtensionEmbedding B C)
    (f : ExtensionEmbedding A B) (p : A.Point) :
    g.comp f p = g (f p) :=
  rfl

end ExtensionEmbedding

/-- A fixed-Cauchy equivalence of the topological causal--Einstein carriers.
For smooth Lorentzian developments, local uniqueness should construct this
from a metric-preserving diffeomorphism.  Keeping this carrier-level notion
separate prevents a homeomorphism from being mislabeled as a Lorentzian
isometry before atlas and metric preservation have been proved. -/
structure FixedCauchyEquiv
    (A B : SpacetimeDevelopment S) where
  toEquiv : A.Point ≃ B.Point
  continuous_toFun :
    @Continuous A.Point B.Point A.topology B.topology toEquiv
  continuous_invFun :
    @Continuous B.Point A.Point B.topology A.topology toEquiv.symm
  cauchy_commutes : ∀ σ,
    toEquiv (A.cauchyEmbedding σ) = B.cauchyEmbedding σ
  causal_map : ∀ p q,
    B.causal (toEquiv p) (toEquiv q) ↔ A.causal p q
  einstein_map : ∀ p,
    B.EinsteinAt (toEquiv p) ↔ A.EinsteinAt p

namespace FixedCauchyEquiv

variable {A B : SpacetimeDevelopment S}

instance : CoeFun (FixedCauchyEquiv A B) (fun _ => A.Point → B.Point) :=
  ⟨fun e => e.toEquiv⟩

/-- A fixed-Cauchy equivalence gives an extension embedding in the forward
direction; causal convexity follows from surjectivity. -/
def toExtensionEmbedding (e : FixedCauchyEquiv A B) :
    ExtensionEmbedding A B where
  toEmbedding := e.toEquiv.toEmbedding
  continuous := e.continuous_toFun
  cauchy_commutes := e.cauchy_commutes
  causal_map := e.causal_map
  einstein_map := e.einstein_map
  causalConvex _ _ r _ _ :=
    ⟨e.toEquiv.symm r, e.toEquiv.apply_symm_apply r⟩

end FixedCauchyEquiv

/-- Development extension is existence of a fixed-Cauchy
causal--Einstein embedding.  It is a preorder: distinct but isometric
presentations may extend each other. -/
instance : Preorder (SpacetimeDevelopment S) where
  le A B := Nonempty (ExtensionEmbedding A B)
  le_refl := fun A => ⟨ExtensionEmbedding.refl A⟩
  le_trans := fun _ _ _ hAB hBC =>
    ⟨(Classical.choice hBC).comp (Classical.choice hAB)⟩

lemma le_iff_nonempty_extension {A B : SpacetimeDevelopment S} :
    A ≤ B ↔ Nonempty (ExtensionEmbedding A B) :=
  Iff.rfl

/-- A selected coherent extension system on a chain.  The identity and
composition equations are exactly the compatibility required for the
direct-limit equivalence relation and are the mathematical content supplied
by local Einstein uniqueness up to fixed-Cauchy isometry. -/
structure CoherentChain
    (c : Set (SpacetimeDevelopment S)) where
  map : ∀ A B : c, A.1 ≤ B.1 → ExtensionEmbedding A.1 B.1
  map_self : ∀ A p, map A A le_rfl p = p
  map_map : ∀ A B C (hAB : A.1 ≤ B.1) (hBC : B.1 ≤ C.1) p,
    map B C hBC (map A B hAB p) =
      map A C (hAB.trans hBC) p

/-- A nonempty extension chain is a directed index type. -/
@[reducible] def chainIsDirectedOrder
    {c : Set (SpacetimeDevelopment S)}
    (hc : IsChain (· ≤ ·) c) :
    IsDirectedOrder c where
  directed A B := by
    rcases hc.total A.2 B.2 with hAB | hBA
    · exact ⟨B, hAB, le_rfl⟩
    · exact ⟨A, le_rfl, hBA⟩

@[reducible] def chainNonempty
    {c : Set (SpacetimeDevelopment S)}
    (hne : c.Nonempty) : Nonempty c :=
  ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩⟩

/-- Turn a coherent chain of different spacetime carriers into the directed
system consumed by the genuine quotient-gluing construction. -/
def CoherentChain.toDirectedSystem
    {c : Set (SpacetimeDevelopment S)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (C : CoherentChain c) :
    letI : IsDirectedOrder c := chainIsDirectedOrder hc
    letI : Nonempty c := chainNonempty hne
    DirectedDevelopmentSystem c S := by
  letI : IsDirectedOrder c := chainIsDirectedOrder hc
  letI : Nonempty c := chainNonempty hne
  exact
    { Point := fun A => A.1.Point
      topology := fun A => A.1.topology
      map := fun A B hAB => (C.map A B hAB).toEmbedding
      map_self := C.map_self
      map_map := C.map_map
      map_continuous := fun A B hAB => (C.map A B hAB).continuous
      causal := fun A => A.1.causal
      causal_refl := fun A => A.1.causal_refl
      causal_trans := fun A => A.1.causal_trans
      causal_antisymm := fun A => A.1.causal_antisymm
      causal_map := fun A B hAB => (C.map A B hAB).causal_map
      EinsteinAt := fun A => A.1.EinsteinAt
      einstein_on := fun A => A.1.einstein_on
      einstein_map := fun A B hAB => (C.map A B hAB).einstein_map
      cauchyEmbedding := fun A => A.1.cauchyEmbedding
      cauchyEmbedding_injective := fun A => A.1.cauchyEmbedding_injective
      cauchy_map := fun A B hAB => (C.map A B hAB).cauchy_commutes
      diamond_compact := fun A => A.1.diamond_compact
      causalConvex_map := fun A B hAB => (C.map A B hAB).causalConvex }

end SpacetimeDevelopment

open DevelopmentDirectLimit.DirectedDevelopmentSystem

variable {S : Type v}
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- Regard one component of a raw directed system as a standalone spacetime
development. -/
def component (D : DirectedDevelopmentSystem ι S) (i : ι) :
    SpacetimeDevelopment S where
  Point := D.Point i
  topology := D.topology i
  causal := D.causal i
  causal_refl := D.causal_refl i
  causal_trans := D.causal_trans i
  causal_antisymm := D.causal_antisymm i
  EinsteinAt := D.EinsteinAt i
  einstein_on := D.einstein_on i
  cauchyEmbedding := D.cauchyEmbedding i
  cauchyEmbedding_injective := D.cauchyEmbedding_injective i
  diamond_compact := D.diamond_compact i

/-- Regard the constructed direct limit as a standalone spacetime
development. -/
def gluedObject (D : DirectedDevelopmentSystem ι S) :
    SpacetimeDevelopment S where
  Point := D.GluedCarrier
  topology := D.instTopologicalSpaceGluedCarrier
  causal := D.gluedCausal
  causal_refl := D.gluedCausal_refl
  causal_trans := D.gluedCausal_trans
  causal_antisymm := D.gluedCausal_antisymm
  EinsteinAt := D.gluedEinsteinAt
  einstein_on := D.gluedEinstein_on
  cauchyEmbedding := D.gluedCauchyEmbedding
  cauchyEmbedding_injective := D.gluedCauchyEmbedding_injective
  diamond_compact := D.gluedCausalDiamond_isCompact

/-- Every component has its canonical fixed-Cauchy extension into the
constructed quotient development. -/
def componentExtension (D : DirectedDevelopmentSystem ι S) (i : ι) :
    SpacetimeDevelopment.ExtensionEmbedding
      (component D i) (gluedObject D) where
  toEmbedding := D.of i
  continuous := D.continuous_of i
  cauchy_commutes σ := (D.gluedCauchyEmbedding_eq_of i σ).symm
  causal_map := D.gluedCausal_of i
  einstein_map := D.gluedEinsteinAt_of i
  causalConvex p q r hpr hrq := by
    have hr :
        r ∈ D.of i '' {z : D.Point i |
          D.causal i p z ∧ D.causal i z q} := by
      rw [← D.gluedCausalDiamond_eq_image i p q]
      exact ⟨hpr, hrq⟩
    obtain ⟨r₀, _, hr₀⟩ := hr
    exact ⟨r₀, hr₀⟩

theorem component_le_glued
    (D : DirectedDevelopmentSystem ι S) (i : ι) :
    component D i ≤ gluedObject D :=
  ⟨componentExtension D i⟩

section SmallDevelopmentClass

variable {Dev : Type u} [Preorder Dev]

/-- Coherent fixed-Cauchy extension maps on a chain in a small selected class
of developments.  Keeping the index class and its point carriers in one
universe is the explicit Lean form of Wald's standard set-theoretic size
convention. -/
structure IndexedCoherentChain
    (F : Dev → SpacetimeDevelopment S) (c : Set Dev) where
  map : ∀ A B : c, A.1 ≤ B.1 →
    SpacetimeDevelopment.ExtensionEmbedding (F A.1) (F B.1)
  map_self : ∀ A p, map A A le_rfl p = p
  map_map : ∀ A B C (hAB : A.1 ≤ B.1) (hBC : B.1 ≤ C.1) p,
    map B C hBC (map A B hAB p) =
      map A C (hAB.trans hBC) p

@[reducible] def smallChainIsDirectedOrder
    {c : Set Dev} (hc : IsChain (· ≤ ·) c) :
    IsDirectedOrder c where
  directed A B := by
    rcases hc.total A.2 B.2 with hAB | hBA
    · exact ⟨B, hAB, le_rfl⟩
    · exact ⟨A, le_rfl, hBA⟩

@[reducible] def smallChainNonempty
    {c : Set Dev} (hne : c.Nonempty) : Nonempty c :=
  ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩⟩

/-- The raw directed system underlying a coherent chain in the selected
small class. -/
def IndexedCoherentChain.toDirectedSystem
    {F : Dev → SpacetimeDevelopment S} {c : Set Dev}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (C : IndexedCoherentChain F c) :
    letI : IsDirectedOrder c := smallChainIsDirectedOrder hc
    letI : Nonempty c := smallChainNonempty hne
    DirectedDevelopmentSystem c S := by
  letI : IsDirectedOrder c := smallChainIsDirectedOrder hc
  letI : Nonempty c := smallChainNonempty hne
  exact
    { Point := fun A => (F A.1).Point
      topology := fun A => (F A.1).topology
      map := fun A B hAB => (C.map A B hAB).toEmbedding
      map_self := C.map_self
      map_map := C.map_map
      map_continuous := fun A B hAB => (C.map A B hAB).continuous
      causal := fun A => (F A.1).causal
      causal_refl := fun A => (F A.1).causal_refl
      causal_trans := fun A => (F A.1).causal_trans
      causal_antisymm := fun A => (F A.1).causal_antisymm
      causal_map := fun A B hAB => (C.map A B hAB).causal_map
      EinsteinAt := fun A => (F A.1).EinsteinAt
      einstein_on := fun A => (F A.1).einstein_on
      einstein_map := fun A B hAB => (C.map A B hAB).einstein_map
      cauchyEmbedding := fun A => (F A.1).cauchyEmbedding
      cauchyEmbedding_injective := fun A =>
        (F A.1).cauchyEmbedding_injective
      cauchy_map := fun A B hAB => (C.map A B hAB).cauchy_commutes
      diamond_compact := fun A => (F A.1).diamond_compact
      causalConvex_map := fun A B hAB => (C.map A B hAB).causalConvex }

/-- **Wald maximal-development existence, with all three non-Zorn premises
exposed.**

* `extension_iff` says the selected preorder really is fixed-Cauchy
  spacetime extension;
* `coherent` is local uniqueness up to isometry, strengthened to commuting
  transition maps on every chain;
* `closed` is the set-theoretic size/closure convention: the explicitly
  constructed quotient development has a representative in `Dev`.

The direct limit discharges chain gluing and preservation of global
hyperbolicity.  Zorn is invoked only after those steps. -/
@[zil_level physical_theorem]
theorem exists_maximal
    (base : Dev)
    (F : Dev → SpacetimeDevelopment S)
    (extension_iff : ∀ A B,
      A ≤ B ↔ Nonempty
        (SpacetimeDevelopment.ExtensionEmbedding (F A) (F B)))
    (coherent :
      ∀ (c : Set Dev),
        IsChain (· ≤ ·) c → c.Nonempty →
        Nonempty (IndexedCoherentChain F c))
    (closed :
      ∀ (c : Set Dev) (hc : IsChain (· ≤ ·) c)
        (hne : c.Nonempty),
        letI : IsDirectedOrder c := smallChainIsDirectedOrder hc
        letI : Nonempty c := smallChainNonempty hne
        ∀ C : IndexedCoherentChain F c,
          ∃ upper : Dev,
            Nonempty
              (SpacetimeDevelopment.ExtensionEmbedding
                (gluedObject (C.toDirectedSystem hc hne)) (F upper))) :
    ∃ M : Dev, IsMax M := by
  refine @zorn_le_nonempty Dev inferInstance ⟨base⟩ ?_
  intro c hc hne
  letI : IsDirectedOrder c :=
    smallChainIsDirectedOrder hc
  letI : Nonempty c :=
    smallChainNonempty hne
  let C : IndexedCoherentChain F c :=
    Classical.choice (coherent c hc hne)
  let D : DirectedDevelopmentSystem c S :=
    C.toDirectedSystem hc hne
  obtain ⟨upper, hUpper⟩ := closed c hc hne C
  let eUpper :
      SpacetimeDevelopment.ExtensionEmbedding (gluedObject D) (F upper) :=
    Classical.choice hUpper
  refine ⟨upper, ?_⟩
  intro A hAc
  let i : c := ⟨A, hAc⟩
  let eMember :
      SpacetimeDevelopment.ExtensionEmbedding (F A) (gluedObject D) :=
    { toEmbedding := D.of i
      continuous := D.continuous_of i
      cauchy_commutes := fun σ =>
        (D.gluedCauchyEmbedding_eq_of i σ).symm
      causal_map := D.gluedCausal_of i
      einstein_map := D.gluedEinsteinAt_of i
      causalConvex := fun p q r hpr hrq => by
        have hr :
            r ∈ D.of i '' {z : D.Point i |
              D.causal i p z ∧ D.causal i z q} := by
          rw [← D.gluedCausalDiamond_eq_image i p q]
          exact ⟨hpr, hrq⟩
        obtain ⟨r₀, _, hr₀⟩ := hr
        exact ⟨r₀, hr₀⟩ }
  exact (extension_iff A upper).2 ⟨eUpper.comp eMember⟩

/-- Two maximal elements mutually extend once every pair admits a common
extension.  This is Wald's uniqueness-patching argument at the preorder
level. -/
@[zil_level physical_theorem]
theorem maximal_mutually_extends_of_joint_extension
    (joint : ∀ A B : Dev, ∃ C : Dev, A ≤ C ∧ B ≤ C)
    {M N : Dev} (hM : IsMax M) (hN : IsMax N) :
    M ≤ N ∧ N ≤ M := by
  obtain ⟨C, hMC, hNC⟩ := joint M N
  have hCM : C ≤ M := hM hMC
  have hCN : C ≤ N := hN hNC
  exact ⟨hMC.trans hCN, hNC.trans hCM⟩

/-- **Uniqueness up to fixed-Cauchy carrier equivalence.**  The first premise
is the joint-extension gluing theorem; the second is the precise
local-uniqueness adapter turning mutual extensions into a fixed-Cauchy
causal--Einstein homeomorphism.  In the final Lorentzian instantiation that
adapter must additionally be proved metric-preserving. -/
@[zil_level physical_theorem]
theorem maximal_unique_up_to_fixedCauchyEquiv
    (F : Dev → SpacetimeDevelopment S)
    (joint : ∀ A B : Dev, ∃ C : Dev, A ≤ C ∧ B ≤ C)
    (localUniqueness : ∀ A B : Dev,
      A ≤ B → B ≤ A →
      Nonempty (SpacetimeDevelopment.FixedCauchyEquiv (F A) (F B)))
    {M N : Dev} (hM : IsMax M) (hN : IsMax N) :
    Nonempty (SpacetimeDevelopment.FixedCauchyEquiv (F M) (F N)) := by
  obtain ⟨hMN, hNM⟩ :=
    maximal_mutually_extends_of_joint_extension joint hM hN
  exact localUniqueness M N hMN hNM

end SmallDevelopmentClass

/- ZIL-BEGIN -/

zil attach exists_maximal where
  formalizes @ "claim:inside-a-small-class-closed-under-directed-quotient-gluing-one-base-development-and-coherent-fixed-cauchy-local-isometry-maps-on-every-extension-chain-produce-a-maximal-globally-hyperbolic-development",
  epistemic_status @ "risky",
  supported_by @ "book:Wald-General-Relativity-Theorem-10.2.2",
  supported_by @ "lean:DirectLimit",
  supported_by @ "lean:zorn_le_nonempty",
  caveat @ "strong-visible-premise:local-einstein-uniqueness-must-produce-fixed-cauchy-causal-einstein-embeddings-that-are-continuous-causally-convex-and-coherent-under-identity-and-composition",
  caveat @ "size-premise:the-selected-small-development-class-must-contain-a-representative-receiving-an-extension-from-each-explicitly-constructed-direct-limit-development",
  caveat @ "remaining-smooth-geometry:the-current-theorem-glues-topological-causal-einstein-carriers-and-does-not-yet-construct-the-quotient-smooth-lorentzian-atlas"

zil attach maximal_mutually_extends_of_joint_extension where
  formalizes @ "claim:any-two-maximal-developments-mutually-extend-when-the-fixed-cauchy-local-uniqueness-patching-construction-gives-every-pair-a-common-extension",
  epistemic_status @ "risky",
  supported_by @ "book:Wald-General-Relativity-Theorem-10.2.2-uniqueness-step",
  caveat @ "premise:the-joint-extension-must-be-constructed-by-gluing-the-maximal-common-fixed-cauchy-isometric-region"

zil attach maximal_unique_up_to_fixedCauchyEquiv where
  formalizes @ "claim:maximal-developments-are-unique-up-to-a-fixed-cauchy-causal-einstein-homeomorphism-once-local-uniqueness-turns-mutual-extensions-into-that-equivalence",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.WaldMaximalDevelopment.maximal_mutually_extends_of_joint_extension",
  caveat @ "remaining-lorentzian-strengthening:prove-the-equivalence-is-a-smooth-metric-preserving-diffeomorphism-before-calling-it-an-isometry"

zil_file_contract physlib.waldMaximalDevelopmentExistence where
  promises "The public spine defines globally hyperbolic Einstein Cauchy developments on genuinely varying point carriers, orders a selected small class by fixed-Cauchy causal-Einstein extension embeddings, expresses local uniqueness as a coherent selection of chain embeddings, constructs each chain upper development using the arbitrary-carrier direct-limit quotient, requires the standard size convention that this quotient has a representative in the selected class, and only then applies Zorn to produce a maximal development."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:DirectLimit",
    "lean:zorn_le_nonempty",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.DevelopmentDirectLimit.DirectedDevelopmentSystem.gluedCausalDiamond_isCompact"
  ]
  forbids_substitutes [
    "taking-a-literal-set-union-of-different-spacetime-carrier-types",
    "quantifying-over-all-carriers-in-one-universe-while-pretending-their-type-of-developments-remains-in-that-universe",
    "invoking-zorn-before-constructing-chain-upper-developments",
    "deriving-spacetime-local-isometry-coherence-from-phase-trajectory-uniqueness",
    "calling-the-topological-causal-quotient-a-smooth-lorentzian-manifold-without-atlas-descent"
  ]
  witnessed_by [
    exists_maximal,
    maximal_mutually_extends_of_joint_extension,
    maximal_unique_up_to_fixedCauchyEquiv
  ]

#zil_formalization_lint physlib.waldMaximalDevelopmentExistence

/- ZIL-END -/

end WaldMaximalDevelopment

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity

end
