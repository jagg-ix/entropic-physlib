/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity
meta import Zil

/-!
# Local nets, Haag-duality, local primarity & definiteness (Verch 1996, Chapter 3)

Formalizes the **algebraic structure of Hadamard vacuum representations** (R. Verch, arXiv:funct-an/9609004,
Chapter 3): the axioms of a *local net of observable algebras* (isotony + locality, Eqs 3.1–3.2) and the
structural properties of Theorem 3.6 — **local definiteness** (c), **regularity** (e), **Haag-duality** (f),
**local primarity** (g) — expressed in the commutant language of `AlgebraicQFT.StarAlgebraGNSFormCommutant` /
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
  `scalars_subset_iInter`). Primarity = *factor* `R(O) ∩ R(O)' = ℂ·1` (Thm 3.6(g), `commutantCentre` trivial);
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
* Repo carriers: `AlgebraicQFT.StarAlgebraGNSFormCommutant` (`commutant`, `IsBicommutantClosed`, `commutantCentre`, `commutant_isBicommutantClosed`),
  `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (factor/centre, the trace contrast for the type classification).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant


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
lemma locality_self (O : ι) : N.alg O ⊆ commutant (N.alg (N.compl O)) :=
  N.locality (N.le_compl_compl O)

/-- **[Dual locality] `R(O^⊥) ⊆ R(O)'`** — the causal-complement algebra commutes with `R(O)` (locality at
`O^⊥ ≤ O^⊥`). -/
lemma alg_compl_subset_commutant (O : ι) : N.alg (N.compl O) ⊆ commutant (N.alg O) :=
  N.locality (le_refl (N.compl O))

/-! ## §A.1 Weak locality in a state versus Einstein locality

Buchholz–Florig–Summers (2000) obtain first a **weak**, vacuum-matrix-element form of
opposite-wedge locality.  This is logically weaker than the operator commutation required by
Haag–Kastler locality.  The distinction matters: modular theory alone gives the weak statement,
whereas promotion to Einstein causality requires an additional condition (or a special
commutator class).
-/

section WeakLocality

variable [StarMul A]

/-- **Weak opposite-wedge locality without assuming a local net.**
This carrier needs only an algebra family and an opposite-region map, so it can state the
Buchholz conclusion before Einstein locality has been established. -/
def WeakOppositeWedgeLocalityInState
    (alg : ι → Set A) (opposite : ι → ι) (ω : A → ℂ) (O : ι) : Prop :=
  ∀ ⦃a : A⦄, a ∈ alg (opposite O) →
    ∀ ⦃b : A⦄, b ∈ alg O → ω (star a * b) = ω (b * star a)

/-- **Weak opposite-region locality in a state** `ω`:
`ω(a* b) = ω(b a*)` for `a ∈ R(O^⊥)` and `b ∈ R(O)`.

This is the scalar vacuum-correlation identity isolated in Buchholz–Florig–Summers (2000);
it is deliberately not identified with the operator equation `a*b = b*a`. -/
def WeakLocalityInState (ω : A → ℂ) (O : ι) : Prop :=
  WeakOppositeWedgeLocalityInState N.alg N.compl ω O

/-- **Einstein locality implies weak vacuum locality.** If each local algebra is closed under
`star`, the operator commutation supplied by `LocalNet.locality` immediately gives the
Buchholz vacuum matrix-element identity for every state functional `ω`. -/
theorem locality_implies_weakLocalityInState
    (ω : A → ℂ)
    (hstar : ∀ (O : ι) ⦃a : A⦄, a ∈ N.alg O → star a ∈ N.alg O)
    (O : ι) :
    WeakLocalityInState N ω O := by
  intro a ha b hb
  have hsa : star a ∈ N.alg (N.compl O) := hstar (N.compl O) ha
  have hcentral : star a ∈ commutant (N.alg O) :=
    alg_compl_subset_commutant N O hsa
  have hcomm : b * star a = star a * b :=
    Set.mem_centralizer_iff.mp hcentral b hb
  exact congrArg ω hcomm.symm

end WeakLocality

section TomitaBoundary

variable {B : Type*} [Ring B] [StarRing B]

/-- **The GNS boundary identity produced by the Buchholz modular-conjugation calculation.**
For an opposite-wedge observable `a` and a wedge observable `b`, the two GNS matrix
elements related by the Tomita boundary value agree.  This is the analytic output of the
paper's `J`, KMS, and opposite-wedge rotation argument; it is kept separate from operator
commutation. -/
def HasOppositeWedgeTomitaBoundary
    (alg : ι → Set B) (opposite : ι → ι) (ω : B → ℂ) (O : ι) : Prop :=
  ∀ ⦃a : B⦄, a ∈ alg (opposite O) →
    ∀ ⦃b : B⦄, b ∈ alg O →
      gnsForm ω a b = gnsForm ω (star b) (star a)

/-- **[Buchholz modular boundary ⇒ weak locality].**
The paper's Tomita/KMS boundary equality is exactly the scalar opposite-wedge
weak-locality statement after expanding the existing GNS form.  No operator commutation is
inferred here. -/
theorem weakLocalityInState_of_tomitaBoundary
    (alg : ι → Set B) (opposite : ι → ι) (ω : B → ℂ) (O : ι)
    (hboundary : HasOppositeWedgeTomitaBoundary alg opposite ω O) :
    WeakOppositeWedgeLocalityInState alg opposite ω O := by
  intro a ha b hb
  simpa [gnsForm] using hboundary ha hb

end TomitaBoundary

section ContinuumKMSTomita

open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity

variable {B : Type*} [Ring B] [StarRing B]
variable {X : Type*} [MeasurableSpace X]

/-- **A continuum spectral realization of the opposite-wedge GNS matrix elements.**
The lower and upper complex-time boundaries are identified with the two GNS orderings;
the KMS equality between them is proved from the continuum spectral integral rather than
stored as a separate boundary axiom. -/
structure ContinuumKMSGNSRealization
    (alg : ι → Set B) (opposite : ι → ι) (ω : B → ℂ) (O : ι)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) where
  spectralWeight : B → B → X → ℂ
  regular :
    ∀ a ∈ alg (opposite O), ∀ b ∈ alg O,
      ∀ᵐ x ∂μ, Real.exp (β * frequency x) - 1 ≠ 0
  lowerBoundary :
    ∀ a ∈ alg (opposite O), ∀ b ∈ alg O,
      continuumThermalWightman μ β frequency (spectralWeight a b) 0 =
        gnsForm ω a b
  upperBoundary :
    ∀ a ∈ alg (opposite O), ∀ b ∈ alg O,
      continuumThermalWightman μ β frequency (spectralWeight a b)
          (-Complex.I * (β : ℂ)) =
        gnsForm ω (star b) (star a)

/-- **[Continuum spectral KMS ⇒ Tomita boundary].**
At `t=0`, the proved continuum KMS identity equates the lower and upper spectral
boundaries; the supplied spectral realization then identifies those values with the two
opposite-wedge GNS orderings. -/
theorem tomitaBoundary_of_continuumKMS
    (alg : ι → Set B) (opposite : ι → ι) (ω : B → ℂ) (O : ι)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ)
    (R : ContinuumKMSGNSRealization alg opposite ω O μ β frequency) :
    HasOppositeWedgeTomitaBoundary alg opposite ω O := by
  intro a ha b hb
  have hkms :=
    continuumThermalWightman_kms μ β frequency (R.spectralWeight a b) 0
      (R.regular a ha b hb)
  calc
    gnsForm ω a b =
        continuumThermalWightman μ β frequency (R.spectralWeight a b) 0 :=
      (R.lowerBoundary a ha b hb).symm
    _ = continuumThermalWightman μ β frequency (R.spectralWeight a b)
          (-Complex.I * (β : ℂ)) := by
      simpa using hkms.symm
    _ = gnsForm ω (star b) (star a) := R.upperBoundary a ha b hb

/-- **[Continuum spectral KMS ⇒ weak opposite-wedge locality].**
This closes the analytic chain: pointwise entire modes, Bochner spectral integration,
the continuum KMS boundary equality, the Tomita GNS boundary, and finally weak locality. -/
theorem weakLocality_of_continuumKMS
    (alg : ι → Set B) (opposite : ι → ι) (ω : B → ℂ) (O : ι)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ)
    (R : ContinuumKMSGNSRealization alg opposite ω O μ β frequency) :
    WeakOppositeWedgeLocalityInState alg opposite ω O :=
  weakLocalityInState_of_tomitaBoundary alg opposite ω O
    (tomitaBoundary_of_continuumKMS alg opposite ω O μ β frequency R)

end ContinuumKMSTomita

section CNumberUpgrade

variable {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]

/-- **A c-number commutator upgrades weak locality to operator locality.**

If the weak-locality commutator is known independently to be a scalar,
`a*b - b*a = z·1`, then any normalized complex-linear state detects its coefficient:
the weak identity forces `z = 0`.  This is the precise special case singled out in
Buchholz–Florig–Summers: weak locality suffices for fields with c-number commutators,
but not for a general interacting net. -/
theorem weakLocality_cnumber_commutator_zero
    (ω : B →ₗ[ℂ] ℂ) (hω : ω 1 = 1)
    {a b : B} (hweak : ω (star a * b) = ω (b * star a))
    {z : ℂ} (hcnumber : star a * b - b * star a = z • (1 : B)) :
    z = 0 := by
  have hvanish : ω (star a * b - b * star a) = 0 := by
    rw [map_sub, hweak, sub_self]
  rw [hcnumber, map_smul, hω, smul_eq_mul, mul_one] at hvanish
  exact hvanish

/-- **C-number weak locality gives actual commutation.** Under the same hypotheses,
`a*b = b*a`; no such upgrade is claimed for general operator-valued commutators. -/
theorem weakLocality_cnumber_implies_commutation
    (ω : B →ₗ[ℂ] ℂ) (hω : ω 1 = 1)
    {a b : B} (hweak : ω (star a * b) = ω (b * star a))
    {z : ℂ} (hcnumber : star a * b - b * star a = z • (1 : B)) :
    star a * b = b * star a := by
  have hz : z = 0 :=
    weakLocality_cnumber_commutator_zero ω hω hweak hcnumber
  rw [hz, zero_smul] at hcnumber
  exact sub_eq_zero.mp hcnumber

end CNumberUpgrade


/-- **[Theorem 3.6(f)] Haag-duality** `R(O^⊥)' = R(O)` — the local algebra is exactly the commutant of the
causal complement (for pure/Hadamard-vacuum states, on regular diamonds). -/
def HaagDuality (O : ι) : Prop := commutant (N.alg (N.compl O)) = N.alg O

/-- **Haag-duality makes `R(O)` a von Neumann algebra** — being a commutant, `R(O^⊥)'` is its own double
commutant (`commutant_isBicommutantClosed`), and Haag-duality identifies it with `R(O)`. -/
lemma haagDuality_imp_isVonNeumann {O : ι} (h : HaagDuality N O) :
    IsBicommutantClosed (N.alg O) := h ▸ commutant_isBicommutantClosed _

/-- **[Maximality of the local algebra] Haag-duality ⟹ `R(O)` is maximal.** Any set `S` of operators that
still commutes with the causal complement (`S ⊆ R(O^⊥)'`) is already contained in `R(O)`: no observable can be
added without violating locality. -/
lemma haagDuality_maximal {O : ι} (h : HaagDuality N O) {S : Set A}
    (hS : S ⊆ commutant (N.alg (N.compl O))) : S ⊆ N.alg O := by
  rw [← h]
  simpa using hS

/-- **[Haag-duality = saturated locality] `R(O^⊥)' = R(O) ⟺ R(O^⊥)' ⊆ R(O)`.** The inclusion `R(O) ⊆ R(O^⊥)'`
holds for every net (`locality_self`), so Haag-duality is exactly the reverse inclusion. -/
lemma haagDuality_iff {O : ι} :
    HaagDuality N O ↔ commutant (N.alg (N.compl O)) ⊆ N.alg O :=
  ⟨fun h => h.le, fun hsub => le_antisymm hsub (locality_self N O)⟩

/-! ## §B.1 Tomita commutant action versus geometric TCP action

Buchholz–Florig–Summers distinguish two actions of the modular conjugation on a wedge:
Tomita theory identifies its image with the wedge commutant, whereas geometric TCP would
identify it with the opposite wedge.  Consequently geometric action is not a consequence of
weak locality: it is equivalent to the additional opposite-wedge duality equality.
-/

/-- **Tomita action on a wedge algebra:** the adjoint action `j` maps `R(O)` onto `R(O)'`.
No locality axiom is built into this predicate. -/
def TomitaCommutantAction (alg : ι → Set A) (j : A → A) (O : ι) : Prop :=
  j '' alg O = commutant (alg O)

/-- **Geometric TCP action on a wedge algebra:** `j` maps `R(O)` onto `R(Oᶜ)`.
It is likewise stated before assuming Einstein locality. -/
def GeometricOppositeWedgeAction
    (alg : ι → Set A) (opposite : ι → ι) (j : A → A) (O : ι) : Prop :=
  j '' alg O = alg (opposite O)

/-- **[Geometric modular action ↔ opposite-wedge duality].**
Once Tomita's commutant action is supplied, saying that the same conjugation acts
geometrically is exactly the equality `R(O)' = R(Oᶜ)`. -/
theorem geometricOppositeWedgeAction_iff_duality
    (alg : ι → Set A) (opposite : ι → ι) (j : A → A) (O : ι)
    (hTomita : TomitaCommutantAction alg j O) :
    GeometricOppositeWedgeAction alg opposite j O ↔
      commutant (alg O) = alg (opposite O) := by
  rw [GeometricOppositeWedgeAction, hTomita]

/-- **Haag duality on the complementary wedge supplies opposite-wedge duality.**
The only geometric input is involutivity of the region complement. -/
theorem oppositeWedgeDuality_of_haagDuality_complement
    (O : ι) (hcompl : N.compl (N.compl O) = O)
    (hdual : HaagDuality N (N.compl O)) :
    commutant (N.alg O) = N.alg (N.compl O) := by
  simpa [HaagDuality, hcompl] using hdual

/-- **[Haag duality + Tomita ⇒ geometric TCP action].**
This is the precise strong-locality hypothesis under which the Buchholz modular conjugation
acts as the spacetime reflection on observables. -/
theorem geometricOppositeWedgeAction_of_haagDuality
    (j : A → A) (O : ι)
    (hTomita : TomitaCommutantAction N.alg j O)
    (hcompl : N.compl (N.compl O) = O)
    (hdual : HaagDuality N (N.compl O)) :
    GeometricOppositeWedgeAction N.alg N.compl j O :=
  (geometricOppositeWedgeAction_iff_duality N.alg N.compl j O hTomita).2
    (oppositeWedgeDuality_of_haagDuality_complement N O hcompl hdual)

/-- **Geometric TCP action implies strong opposite-wedge locality.**
Together with the Tomita commutant action it gives equality, hence in particular the
operator-commutation inclusion `R(Oᶜ) ⊆ R(O)'`.  Crucially this theorem is stated for an
arbitrary algebra family, not for `LocalNet`, so the conclusion is not assumed in advance. -/
theorem geometricOppositeWedgeAction_implies_strongLocality
    (alg : ι → Set A) (opposite : ι → ι) (j : A → A) (O : ι)
    (hTomita : TomitaCommutantAction alg j O)
    (hgeom : GeometricOppositeWedgeAction alg opposite j O) :
    alg (opposite O) ⊆ commutant (alg O) := by
  have hEq : commutant (alg O) = alg (opposite O) :=
    (geometricOppositeWedgeAction_iff_duality alg opposite j O hTomita).1 hgeom
  exact hEq.symm.le


/-- **[Theorem 3.6(g)] Local primarity = factor** — `R(O)` is a *factor*, `R(O) ∩ R(O)' = ℂ·1` (`commutantCentre`
trivial), with `Z` the scalars `ℂ·1`. Physically: no local macroscopic observables / superselection rules. -/
def LocalPrimarity (Z : Set A) (O : ι) : Prop := commutantCentre (N.alg O) = Z

/-- **A factor's centre is the scalars** `R(O) ∩ R(O)' = ℂ·1` — unfolding local primarity. -/
lemma primarity_center {Z : Set A} {O : ι} (h : LocalPrimarity N Z O) :
    N.alg O ∩ commutant (N.alg O) = Z := h

/-- **[Theorem 3.6(c)] Local definiteness** `⋂_{O∋p} R(O) = ℂ·1` — the intersection of all local algebras
shrinking to a point is trivial (`contains O` meaning `p ∈ O`). -/
def LocalDefiniteness (Z : Set A) (contains : ι → Prop) : Prop :=
  (⋂ O, ⋂ _ : contains O, N.alg O) = Z

/-- **[Easy direction of definiteness] `ℂ·1 ⊆ ⋂_{O∋p} R(O)`** — the scalars sit inside every local algebra,
hence in their intersection (the reverse inclusion is the deep Hadamard content). -/
lemma scalars_subset_iInter (Z : Set A) (contains : ι → Prop)
    (hZ : ∀ O, contains O → Z ⊆ N.alg O) :
    Z ⊆ ⋂ O, ⋂ _ : contains O, N.alg O :=
  Set.subset_iInter fun O => Set.subset_iInter fun h => hZ O h


/-- **[Outer regularity, easy inclusion] `R(O) ⊆ ⋂_{O₁ ⊃ O} R(O₁)`** — by isotony `R(O)` sits inside every
larger algebra (the reverse, `=`, is the deep regularity statement). -/
lemma alg_subset_iInter_outer (O : ι) :
    N.alg O ⊆ ⋂ O₁, ⋂ _ : O ≤ O₁, N.alg O₁ :=
  Set.subset_iInter fun _O₁ => Set.subset_iInter fun h => N.isotony h

/-- **[Inner regularity, easy inclusion] `⋃_{O₁ ⊂ O} R(O₁) ⊆ R(O)`** — by isotony every smaller algebra sits
inside `R(O)`; the deep statement is that its von Neumann closure (double commutant) equals `R(O)`. -/
lemma iUnion_inner_subset (O : ι) :
    (⋃ O₁, ⋃ _ : O₁ ≤ O, N.alg O₁) ⊆ N.alg O :=
  Set.iUnion_subset fun _O₁ => Set.iUnion_subset fun h => N.isotony h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_self where
  formalizes @ "claim:locality-the-local-algebra-of-a-region-is-contained-in-the-commutant-of-the-algebra-of-its-causal-complement-einstein-causality-of-the-local-net",
  supported_by @ "paper:verch-1996-funct-an-9609004-algebraic-structure-of-hadamard-vacuum-representations-chapter-3"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.haagDuality_imp_isVonNeumann where
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:haag-duality-makes-the-local-algebra-a-von-neumann-algebra-being-the-commutant-of-the-causal-complement-it-is-its-own-double-commutant"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.haagDuality_iff where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_self",
  formalizes @ "claim:haag-duality-is-saturated-locality-since-the-inclusion-of-the-local-algebra-in-the-commutant-of-the-causal-complement-holds-for-every-net-haag-duality-is-exactly-the-reverse-inclusion",
  requires @ "claim:locality-the-local-algebra-of-a-region-is-contained-in-the-commutant-of-the-algebra-of-its-causal-complement-einstein-causality-of-the-local-net"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.primarity_center where
  formalizes @ "claim:local-primarity-theorem-3-6-g-the-local-algebra-is-a-factor-its-intersection-with-its-commutant-is-the-scalars-so-there-are-no-local-macroscopic-observables-or-superselection-rules"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_implies_weakLocalityInState where
  formalizes @ "claim:einstein-locality-implies-buchholz-opposite-wedge-weak-locality-in-every-state",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-converse-is-not-valid-for-a-general-interacting-local-net"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocalityInState_of_tomitaBoundary where
  formalizes @ "claim:buchholz-tomita-kms-opposite-wedge-boundary-identity-implies-vacuum-weak-locality",
  requires @ "claim:the-continuum-tomita-kms-boundary-identity-on-the-opposite-wedge-gns-domain",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-analytic-continuation-producing-the-boundary-identity-is-an-explicit-premise-and-the-conclusion-is-only-a-state-matrix-element-equality"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.tomitaBoundary_of_continuumKMS where
  formalizes @ "claim:the-continuum-kay-wald-spectral-kms-identity-constructs-the-opposite-wedge-tomita-gns-boundary-equality",
  requires @ "claim:the-lower-and-upper-spectral-boundaries-realize-the-two-gns-orderings",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  supported_by @ "paper:kay-wald-1991-kms-analyticity-on-a-bifurcate-killing-horizon",
  caveat @ "claim:the-spectral-representation-of-the-two-gns-boundaries-remains-visible-while-the-kms-equality-between-them-is-proved"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_of_continuumKMS where
  formalizes @ "claim:continuum-spectral-kms-analyticity-implies-opposite-wedge-vacuum-weak-locality",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  requires @ "claim:the-continuum-spectral-gns-realization-at-both-kms-boundaries"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_cnumber_implies_commutation where
  formalizes @ "claim:buchholz-weak-locality-upgrades-to-operator-locality-for-c-number-commutators",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-c-number-commutator-hypothesis-is-load-bearing-and-excludes-general-operator-valued-interacting-commutators"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_iff_duality where
  formalizes @ "claim:buchholz-geometric-tcp-action-is-equivalent-to-opposite-wedge-duality-once-tomita-commutant-action-is-supplied",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:weak-locality-alone-does-not-produce-the-operator-algebra-equality"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_of_haagDuality where
  formalizes @ "claim:haag-duality-on-the-complementary-wedge-and-tomita-commutant-action-produce-geometric-tcp-action",
  requires @ "claim:the-causal-complement-is-involutive-on-the-chosen-wedge",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_implies_strongLocality where
  formalizes @ "claim:geometric-tcp-action-together-with-tomita-commutant-action-implies-strong-opposite-wedge-operator-locality",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads"

zil_file_contract physlib.hadamardLocalNet where
  promises "The algebraic structure of Hadamard vacuum representations (Verch, arXiv:funct-an/9609004, Chapter 3): the Haag-Kastler axioms of a local net of observable algebras (isotony + locality) and the structural properties of Theorem 3.6. Locality is Einstein causality -- the local algebra of a region lies in the commutant of its causal-complement algebra (locality_self). Haag-duality R(O-complement)-prime = R(O) makes the local algebra a von Neumann algebra (haagDuality_imp_isVonNeumann) and is exactly saturated locality, the reverse of the always-valid locality inclusion (haagDuality_iff). Local primarity makes the local algebra a factor -- its centre is the scalars -- so there are no local superselection rules (primarity_center). The Buchholz-Florig-Summers distinction is explicit: the Tomita/KMS GNS boundary identity produces weak opposite-wedge locality; the new continuum spectral route proves that boundary identity from the Kay-Wald pointwise and Bochner-integrated KMS theorem once the two spectral boundary values are identified with the GNS orderings; strong Einstein locality implies weak locality in every state; the reverse upgrade is proved only for c-number commutators; and geometric TCP action is equivalent to opposite-wedge duality once Tomita's commutant action is supplied."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.HaagDuality",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.LocalPrimarity"]
  forbids_substitutes ["the deep Hadamard-state content -- local definiteness and the reverse inclusions that require the microlocal spectrum condition -- which is the cited curved-spacetime infrastructure, only the commutant-algebra structural identities are carried",
    "any construction of the local net on a concrete spacetime, only the abstract von-Neumann-algebra relations are carried",
    "a general derivation of Einstein causality from modular weak locality; the proved reverse implication requires a c-number commutator",
    "deriving the continuum Tomita-KMS boundary value or Tomita commutant theorem from finite matrices"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_self,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.haagDuality_imp_isVonNeumann,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.haagDuality_iff,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.primarity_center,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_implies_weakLocalityInState,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocalityInState_of_tomitaBoundary,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.tomitaBoundary_of_continuumKMS,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_of_continuumKMS,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.weakLocality_cnumber_implies_commutation,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_iff_duality,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_of_haagDuality,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.geometricOppositeWedgeAction_implies_strongLocality]

/- ZIL-END -/
