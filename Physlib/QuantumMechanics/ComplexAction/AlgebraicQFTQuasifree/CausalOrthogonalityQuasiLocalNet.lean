/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

/-!
# The causal orthogonality relation and the quasi-local algebra (Labuschagne–Majewski)

Formalizes the central AQFT structure of Labuschagne–Majewski (*A von Neumann algebraic approach to Quantum
Theory on curved spacetime*, arXiv:2503.14107): a **quasi-local algebra** is a net of local algebras indexed by a
**directed set with an orthogonality relation** `⊥` (causal independence). On a globally hyperbolic spacetime the
class `𝒦(M,g)` of relatively-compact causally-convex regions is exactly such a directed set (their Prop. 4.6).

The repository already has a Haag–Kastler net (`HadamardLocalNet.LocalNet`) whose causal complement is a *function*
`O ↦ O^⊥`. This module supplies the paper's more primitive object — the abstract **orthogonality relation**
`α ⊥ β` on the index poset (their axioms (1)–(4) on the index set) — and the quasi-local algebra built on it, then
shows the existing `LocalNet` realizes it.

* **the orthogonality relation** (`CausalOrthogonality`): a symmetric relation `orth` on a preorder with the
 paper's axioms — directedness, existence of an orthogonal element, **heredity** (`α ≤ β ∧ β ⊥ γ ⟹ α ⊥ γ`), and
 common upper bound of two elements orthogonal to a third; subregions inherit spacelike separation on both sides
 (`orth_mono`);
* **the quasi-local algebra** (`QuasiLocalNet`): isotony plus **causal independence** — orthogonal regions have
 commuting observables, `α ⊥ β ⟹ 𝒜_α ⊆ 𝒜_β'` (`commutant`), the Einstein-causality / microcausality axiom;
* **microcausality is symmetric** (`commutant_symm`, `causalIndependence_symm`) — spacelike observables *mutually*
 commute, reusing the repository's `commutant`;
* **the existing `LocalNet` realizes the relation** (`localNetOrth`, `localNet_causal_independence`,
 `localNet_orth_heredity`): `α ⊥ β := α ≤ compl β` satisfies heredity, and `LocalNet.locality` *is* the causal
 independence.

* **§A — the orthogonality relation** (`CausalOrthogonality`, `orth_mono`).
* **§B — the quasi-local algebra** (`QuasiLocalNet`).
* **§C — microcausality is symmetric** (`commutant_symm`, `causalIndependence_symm`).
* **§D — the Haag–Kastler net realizes it** (`localNet_causal_independence`, `localNet_orth_heredity`).

This is the exact order-theoretic / algebraic skeleton of the quasi-local axioms: the
orthogonality relation and its consequences are exact, and causal independence reuses the repository's
`commutant`. The geometric instance (`orth` = causal disjointness on `𝒦(M,g)`), the modular theory, and the
crossed-product / type classification are *not* built here. No new axioms.

## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, quasi-local algebra + orthogonality relation (§2, Prop. 4.6).
 Repo dependencies: `AlgebraicQFTQuasifree.HadamardLocalNet` (`LocalNet`), `AlgebraicQFT.GNSVonNeumannHadamard`
 (`commutant`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet

/-! ## §A — the causal orthogonality relation -/

/-- **The causal orthogonality relation on a region index set** (Labuschagne–Majewski §2, Prop. 4.6). A
symmetric relation `orth` (`α ⊥ β`, causal independence) on a preorder `ι`, with the paper's axioms:

* `directed` — any two regions have a common upper bound (a region containing both);
* `exists_orth` — every region has a region orthogonal to it (there is spacelike-separated room);
* `heredity` — if `α ≤ β` and `β ⊥ γ` then `α ⊥ γ` (a subregion of a spacelike region is spacelike);
* `refine_orth` — two regions orthogonal to `α` have a common upper bound still orthogonal to `α`. -/
structure CausalOrthogonality (ι : Type*) [Preorder ι] where
  /-- the orthogonality (causal independence) relation `α ⊥ β`. -/
  orth : ι → ι → Prop
  /-- causal independence is symmetric. -/
  symm : ∀ ⦃α β⦄, orth α β → orth β α
  /-- the index set is directed: any two regions sit inside a common region. -/
  directed : ∀ α β : ι, ∃ γ : ι, α ≤ γ ∧ β ≤ γ
  /-- every region has an orthogonal (spacelike-separated) region. -/
  exists_orth : ∀ α, ∃ β, orth β α
  /-- heredity: a subregion of a region orthogonal to `γ` is itself orthogonal to `γ`. -/
  heredity : ∀ ⦃α β γ⦄, α ≤ β → orth β γ → orth α γ
  /-- two regions orthogonal to `α` have a common upper bound still orthogonal to `α`. -/
  refine_orth : ∀ ⦃α β γ⦄, orth α β → orth α γ → ∃ d, β ≤ d ∧ γ ≤ d ∧ orth α d

variable {A : Type*} [Monoid A] {ι : Type*} [Preorder ι]

/-- **[Subregions inherit spacelike separation on both sides] `α' ≤ α, β' ≤ β, α ⊥ β ⟹ α' ⊥ β'`.** If two
regions are causally independent, so is any pair of subregions — heredity applied on both arguments (via
symmetry). -/
theorem orth_mono (C : CausalOrthogonality ι) {α α' β β' : ι} (hα : α' ≤ α) (hβ : β' ≤ β)
    (h : C.orth α β) : C.orth α' β' :=
  C.symm (C.heredity hβ (C.symm (C.heredity hα h)))

/-! ## §B — the quasi-local algebra -/

/-- **A quasi-local algebra** (Labuschagne–Majewski §2): a net `alg : ι → Set A` of local algebras over a
directed index set with an orthogonality relation, satisfying

* `isotony` — `α ≤ β ⟹ 𝒜_α ⊆ 𝒜_β` (larger regions have more observables);
* `causalIndependence` — `α ⊥ β ⟹ 𝒜_α ⊆ 𝒜_β'` (`commutant`): observables of causally-independent regions
  commute (Einstein causality / microcausality). -/
structure QuasiLocalNet (A : Type*) [Monoid A] (ι : Type*) [Preorder ι] where
  /-- the causal orthogonality structure on the index set. -/
  causal : CausalOrthogonality ι
  /-- the net of local algebras. -/
  alg : ι → Set A
  /-- isotony: larger regions encode more observables. -/
  isotony : ∀ ⦃α β⦄, α ≤ β → alg α ⊆ alg β
  /-- causal independence: orthogonal regions have commuting observables. -/
  causalIndependence : ∀ ⦃α β⦄, causal.orth α β → alg α ⊆ commutant (alg β)

/-! ## §C — microcausality is symmetric -/

/-- **[The commutation of two sets is symmetric] `S ⊆ T' ⟹ T ⊆ S'`.** If every operator of `S` commutes with
every operator of `T`, then symmetrically every operator of `T` commutes with every operator of `S`. -/
theorem commutant_symm {S T : Set A} (h : S ⊆ commutant T) : T ⊆ commutant S := by
  intro t ht s hs
  exact (h hs t ht).symm

/-- **[Microcausality is symmetric] `α ⊥ β ⟹ 𝒜_β ⊆ 𝒜_α'`.** Observables of causally-independent regions
*mutually* commute: the causal independence of a quasi-local net holds in both directions. -/
theorem causalIndependence_symm (Q : QuasiLocalNet A ι) {α β : ι} (h : Q.causal.orth α β) :
    Q.alg β ⊆ commutant (Q.alg α) :=
  commutant_symm (Q.causalIndependence h)

/-! ## §D — the Haag–Kastler net realizes the orthogonality relation -/

/-- **The orthogonality relation induced by a Haag–Kastler net** `α ⊥ β := α ≤ β^⊥`. The existing `LocalNet`'s
causal-complement function gives the paper's causal orthogonality relation. -/
def localNetOrth (N : LocalNet A ι) (α β : ι) : Prop := α ≤ N.compl β

/-- **[The net's locality is the causal independence] `α ≤ β^⊥ ⟹ 𝒜_α ⊆ 𝒜_β'`.** `LocalNet.locality` is exactly
the quasi-local causal-independence axiom for the induced orthogonality relation. -/
theorem localNet_causal_independence (N : LocalNet A ι) {α β : ι} (h : localNetOrth N α β) :
    N.alg α ⊆ commutant (N.alg β) :=
  N.locality h

/-- **[The induced relation satisfies heredity] `α ≤ β, β ⊥ γ ⟹ α ⊥ γ`.** A subregion of a region spacelike to
`γ` is itself spacelike to `γ` — the Haag–Kastler net satisfies the paper's heredity axiom. -/
theorem localNet_orth_heredity (N : LocalNet A ι) {α β γ : ι} (hab : α ≤ β)
    (h : localNetOrth N β γ) : localNetOrth N α γ :=
  le_trans hab h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet

end
