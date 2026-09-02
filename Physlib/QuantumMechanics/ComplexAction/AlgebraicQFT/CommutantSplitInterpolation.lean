/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
public import Mathlib.LinearAlgebra.Matrix.PosDef
meta import Zil

/-!
# Split-type interpolation on the commutant model — and the finite faithful trace

The AQFT **split property** (Doplicher–Longo): for well-nested regions `O₁ ⊂⊂ O₂` there is a type I
factor `N` interpolating the local algebras, `A(O₁) ⊂ N ⊂ A(O₂)` — the structure that makes a local
"register" an honest approximately-isolated subsystem despite the nonseparability of local algebras.
This module states the two halves that hold *exactly* on the repo's commutant model:

* **§A isotony and the split chain.** Commutant reverses inclusions (`commutant_antitone`), so the
  bicommutant — the generated von Neumann algebra of the model — is isotone: `S ⊆ T ⟹ S″ ⊆ T″`,
  the Haag–Kastler **isotony** axiom. Between nested generated algebras there is an interpolating
  algebra that is bicommutant-closed (a von Neumann algebra of the model): the **shape** of the
  split inclusion, with the interpolant witnessed by the lower algebra itself.
* **§B the finite faithful trace — the type-III honesty marker.** On the matrix model the trace is
  **faithful** (`tr(BᴴB) = 0 ↔ B = 0`) and **finite** (`tr 1 = n`): the model sits where a finite
  faithful trace exists (type I/II₁ behavior), *never* in type III — where no trace exists and the
  Araki relative entropy of `FiniteArakiRelativeEntropy` is the only surviving information measure.
  This theorem is the machine-checked boundary of every finite-model claim in the arc.

What is **not** claimed: a genuine Doplicher–Longo standard split inclusion (which needs cyclic
vectors and operator topology), any type classification of von Neumann algebras, or nuclearity. The
interpolation here records the inclusion shape; the trace records why the finite model is not type
III.

## References

* S. Doplicher, R. Longo, *Standard and split inclusions of von Neumann algebras*, Invent. Math. 75
  (1984). R. Haag, D. Kastler, *An algebraic approach to quantum field theory*, JMP 5 (1964).
* Repo carriers: `StarAlgebraGNSFormCommutant.commutant/IsBicommutantClosed/commutant_triple`,
  `SummersVacuumModularLinks.wedgeAlgebra/causalComplementAlgebra`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CommutantSplitInterpolation

variable {A : Type*} [Ring A]

/-! ## A. Isotony and the split chain -/

/-- **[Isotony of the generated algebra] `S ⊆ T ⟹ S″ ⊆ T″`.** The bicommutant — the von Neumann
algebra the model generates from a region's observables — preserves inclusions: the Haag–Kastler
isotony axiom, derived by applying the repo's `commutant_antitone` twice, not postulated. -/
theorem bicommutant_isotone {S T : Set A} (h : S ⊆ T) :
    commutant (commutant S) ⊆ commutant (commutant T) :=
  commutant_antitone (commutant_antitone h)

/-- **[The split-type interpolation] `S ⊆ T ⟹ ∃ N, S″ ⊆ N ⊆ T″` with `N` a von Neumann algebra of
the model** (bicommutant-closed). The inclusion shape of the Doplicher–Longo split property on the
commutant model: nested generated algebras always admit a bicommutant-closed interpolant — witnessed
by the lower algebra itself, whose closedness is the commutant-triple identity, not an assumption.
The type I character of the interpolant is carried by the finite faithful trace of §B. -/
theorem split_interpolation {S T : Set A} (h : S ⊆ T) :
    ∃ N : Set A, commutant (commutant S) ⊆ N ∧ N ⊆ commutant (commutant T)
      ∧ IsBicommutantClosed N :=
  ⟨commutant (commutant S), subset_rfl, bicommutant_isotone h,
    commutant_isBicommutantClosed (commutant S)⟩

section LocalNetWeld

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence

/-- **[Generated local algebras are split-shaped]** a local net whose region algebra is
bicommutant-closed satisfies the repo's `HasSplitProperty` for every nested pair, with the inner
algebra itself as interpolant — the Set-level `split_interpolation` welded onto the existing
`SplitPropertyStatisticalIndependence` carrier, feeding its statistical-independence consequence
(`split_statistical_independence`). -/
theorem hasSplitProperty_of_bicommutantClosed {B ι : Type*} [Monoid B] [Preorder ι]
    (N : LocalNet B ι) {O O₁ : ι}
    (hclosed : IsBicommutantClosed (N.alg O)) (hsub : N.alg O ⊆ N.alg O₁) :
    HasSplitProperty N O O₁ :=
  ⟨N.alg O, hclosed, subset_rfl, hsub⟩

end LocalNetWeld

/-! ## B. The finite faithful trace — the type-III honesty marker -/

open Matrix in
/-- **[The matrix model carries a finite faithful trace]** `tr(BᴴB) = 0 ↔ B = 0` and `tr 1 = n`.
The type-III honesty marker of the arc: every finite-model statement (modular erasure cost, finite
Araki relative entropy, the wedge eigenvalue shadow) lives where a **faithful finite trace exists**
— type I/II₁ behavior. In type III no such trace exists; there the only surviving information
measure is the relative entropy through relative modular data, which is exactly what
`FiniteArakiRelativeEntropy` keeps as the interface. -/
theorem matrixModel_faithful_finite_trace (n : ℕ) :
    (∀ B : Matrix (Fin n) (Fin n) ℝ, (Bᴴ * B).trace = 0 ↔ B = 0)
      ∧ (1 : Matrix (Fin n) (Fin n) ℝ).trace = (n : ℝ) := by
  refine ⟨fun B => Matrix.trace_conjTranspose_mul_self_eq_zero_iff, ?_⟩
  simp [Matrix.trace_one]

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil_theorem_intent bicommutant_isotone where
  at_level structural
  must_mention [commutant]

zil attach bicommutant_isotone where
  formalizes @ "claim:haag-kastler-isotony-derived-from-commutant-antitonicity",
  supported_by @ "paper:haag-kastler-1964",
  caveat @ "claim:ring-commutant-model-not-operator-topology"

zil_theorem_intent split_interpolation where
  at_level structural
  must_mention [commutant, IsBicommutantClosed]

zil attach split_interpolation where
  formalizes @ "claim:nested-generated-algebras-admit-bicommutant-closed-interpolant",
  requires @ "claim:haag-kastler-isotony-derived-from-commutant-antitonicity",
  supported_by @ "paper:doplicher-longo-1984-split-inclusions",
  caveat @ "claim:inclusion-shape-only-interpolant-is-lower-algebra-not-a-standard-split"

zil attach matrixModel_faithful_finite_trace where
  formalizes @ "claim:finite-model-carries-faithful-finite-trace-hence-not-type-iii",
  supported_by @ "paper:araki-1976-relative-entropy",
  caveat @ "claim:type-iii-boundary-marker-no-von-neumann-type-classification-proven"

zil_file_contract physlib.commutantSplitInterpolation where
  promises "The split property's exact content on the commutant model: the commutant reverses inclusions, the generated von Neumann algebra is isotone (Haag-Kastler isotony, derived), nested generated algebras admit a bicommutant-closed interpolant (the shape of the Doplicher-Longo split inclusion), and the matrix model carries a faithful finite trace — the machine-checked type-III boundary marker: every finite-model claim of the arc lives where the trace exists, and type III claims are forbidden."
  at_level structural
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.IsBicommutantClosed",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant_isBicommutantClosed",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.commutant_antitone",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.HasSplitProperty"]
  forbids_substitutes ["a genuine Doplicher-Longo standard split inclusion claimed from the inclusion shape",
    "a von Neumann type classification claimed from the ring commutant model",
    "type III statements claimed from the finite-trace matrix model"]
  witnessed_by [bicommutant_isotone, split_interpolation,
    hasSplitProperty_of_bicommutantClosed, matrixModel_faithful_finite_trace]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CommutantSplitInterpolation

end
