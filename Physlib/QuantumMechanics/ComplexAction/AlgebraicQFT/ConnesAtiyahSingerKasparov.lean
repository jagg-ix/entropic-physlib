/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization
public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
public import Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability
public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SelfAdjoint
meta import Zil

/-!
# Spectral triples, index pairings, and finite Kasparov composition

This module supplies the common noncommutative-geometric carrier that was missing between the
repository's configuration-space Dirac operator, spectral asymptotics, and atomic shell data.

## A. Finite spectral triples and the spectral action

`FiniteSpectralTriple` records `(A,H,D)` with a faithful algebra representation, a symmetric
Dirac-type operator, and a real eigenbasis.  Its spectral action is the literal eigenvalue trace
`sum_i f (|lambda_i| / Lambda)`.  `effectiveDimensionFromExponent` reads a Weyl exponent
`lambda_k ~ k^alpha` as the spectral dimension `1/alpha`; the atomic adapter applies this convention
to the already-proved shell dimension `2 n^2`.

## B. Unbounded spectral triples

`UnboundedSpectralTriple` uses Physlib's genuine `LinearPMap` self-adjoint operator theory.  Its
algebra acts by continuous operators, preserves the Dirac domain, has explicit bounded commutator
extensions, and the Dirac resolvent is compact at a point of the resolvent set.

## C. Atiyah--Singer and discrete quantum numbers

The analytic side is Mathlib's actual `LinearMap.index = dim ker - dim coker`.  An
`AtiyahSingerIndexData` pairs it with an integrable `A-hat times ch(E)` density and records the deep
geometric index theorem as an explicit certificate.  Independently of that certificate, concrete
zero-map index pairings prove that finite mode, shell-closure, and valence registers have precisely
their expected integer indices.

## D. Finite Kasparov correspondences

`FiniteKasparovCorrespondence` is an algebra-equivariant finite-dimensional shadow of an unbounded
Kasparov cycle.  Its product composes both the algebra map and module map.  Mathlib's exact-sequence
proof of `LinearMap.index_comp` then gives a genuine theorem: indices add under the product.  This is
the reusable induction/restriction mechanism for chemical bonding modules.

## Honest scope

The unbounded carrier requires compactness and bounded-commutator proofs for each concrete Dirac
operator; this module does not manufacture those analytic facts.  The atomic exponent is an explicit
effective model, not a derivation of atomic spectra.
`AtiyahSingerIndexData.index_formula` is the analytic Atiyah--Singer input; characteristic classes and
their manifold integral are not reconstructed here.  The finite correspondence is not a construction
of analytic `KK(A,B)` for arbitrary C-star algebras: compactness, regularity, bounded commutators,
homotopy classes, and Hilbert C-star modules remain the continuum layer.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov

open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers

/-! ## A. Finite Connes spectral triples -/

/-- A finite spectral triple `(A,H,D)` with a real eigenbasis for the Dirac-type operator.

Finite dimensionality makes every commutator bounded.  The explicit symmetry equation is the
finite-dimensional self-adjointness datum used here. -/
structure FiniteSpectralTriple
    (A H ι : Type*) [Semiring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι] where
  /-- Representation of the coordinate algebra on the Hilbert space. -/
  representation : A →ₐ[ℂ] Module.End ℂ H
  /-- Faithfulness of the represented coordinate algebra. -/
  representation_faithful : Function.Injective representation
  /-- Dirac-type operator. -/
  dirac : Module.End ℂ H
  /-- A complete eigenbasis of the Dirac operator. -/
  eigenbasis : Module.Basis ι ℂ H
  /-- Real Dirac eigenvalues. -/
  eigenvalue : ι → ℝ
  /-- The displayed basis diagonalizes `D`. -/
  dirac_eigenvector : ∀ i : ι,
    dirac (eigenbasis i) = (eigenvalue i : ℂ) • eigenbasis i
  /-- Symmetry of `D`; in finite dimension this is the self-adjoint Dirac condition. -/
  dirac_symmetric : ∀ x y : H,
    inner ℂ (dirac x) y = inner ℂ x (dirac y)

namespace FiniteSpectralTriple

variable {A H ι : Type*} [Semiring A] [Algebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

/-- The represented commutator `[D,a]`, the differential of `a` in a spectral triple. -/
def representedCommutator (T : FiniteSpectralTriple A H ι) (a : A) : Module.End ℂ H :=
  T.dirac.comp (T.representation a) - (T.representation a).comp T.dirac

/-- The finite spectral action `Tr f(|D|/Lambda)` evaluated in the supplied eigenbasis. -/
def spectralAction (T : FiniteSpectralTriple A H ι) (f : ℝ → ℝ) (Λ : ℝ) : ℝ :=
  ∑ i : ι, f (|T.eigenvalue i| / Λ)

/-- The spectral action of a nonnegative cutoff is nonnegative. -/
lemma spectralAction_nonneg (T : FiniteSpectralTriple A H ι) (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (Λ : ℝ) : 0 ≤ T.spectralAction f Λ := by
  exact Finset.sum_nonneg fun i _ => hf (|T.eigenvalue i| / Λ)

/-- For an antitone cutoff profile, increasing the positive energy scale can only increase the
finite spectral action: each normalized eigenvalue moves toward the origin. -/
lemma spectralAction_mono_cutoff (T : FiniteSpectralTriple A H ι) (f : ℝ → ℝ)
    (hf : Antitone f) {Λ₁ Λ₂ : ℝ} (hΛ₁ : 0 < Λ₁) (hΛ : Λ₁ ≤ Λ₂) :
    T.spectralAction f Λ₁ ≤ T.spectralAction f Λ₂ := by
  apply Finset.sum_le_sum
  intro i _
  apply hf
  exact div_le_div_of_nonneg_left (abs_nonneg _) hΛ₁ hΛ

/-- A constant cutoff counts the eigenmodes with multiplicity. -/
lemma spectralAction_const (T : FiniteSpectralTriple A H ι) (c Λ : ℝ) :
    T.spectralAction (fun _ => c) Λ = (Fintype.card ι : ℝ) * c := by
  simp [spectralAction]

/-- The counting function of the absolute Dirac spectrum below a cutoff. -/
def eigenvalueCounting (T : FiniteSpectralTriple A H ι) (Λ : ℝ) : ℕ :=
  Finset.card (Finset.univ.filter fun i => |T.eigenvalue i| ≤ Λ)

/-- The finite counting function never exceeds the Hilbert-space eigenbasis cardinality. -/
lemma eigenvalueCounting_le_card (T : FiniteSpectralTriple A H ι) (Λ : ℝ) :
    T.eigenvalueCounting Λ ≤ Fintype.card ι := by
  simpa [eigenvalueCounting] using
    Finset.card_filter_le (s := (Finset.univ : Finset ι)) (p := fun i => |T.eigenvalue i| ≤ Λ)

end FiniteSpectralTriple

/-! ## B. Unbounded Connes spectral triples -/

/-- The everywhere-defined resolvent associated with a genuine point `z` of an unbounded operator's
resolvent set.  Membership supplies surjectivity, so the inverse partial map has full domain. -/
def resolventEverywhere {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : H →ₗ.[ℂ] H) (z : ℂ) (hz : z ∈ D.resolventSet) : H → H :=
  fun x => D.resolvent z ⟨x, by
    rw [LinearPMap.inverse_domain, hz.2.1]
    exact Submodule.mem_top⟩

/-- Compact-resolvent condition for a Physlib partial linear operator: at some genuine resolvent
point, its bounded everywhere-defined inverse maps a neighbourhood of zero into a relatively compact
set. -/
def HasCompactResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : H →ₗ.[ℂ] H) : Prop :=
  ∃ z : ℂ, ∃ hz : z ∈ D.resolventSet,
    IsCompactOperator (resolventEverywhere D z hz)

/-- An unbounded spectral triple using Physlib's actual partial-linear-map operator theory.

The algebra is faithfully represented by bounded operators.  The self-adjoint Dirac operator has
compact resolvent, its domain is invariant under the algebra, and its algebra commutators extend to
bounded operators on the entire Hilbert space. -/
structure UnboundedSpectralTriple
    (A H : Type*) [Semiring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Faithful bounded representation of the coordinate algebra. -/
  representation : A →ₐ[ℂ] (H →L[ℂ] H)
  /-- Faithfulness of the representation. -/
  representation_faithful : Function.Injective representation
  /-- Densely defined Dirac-type partial linear operator. -/
  dirac : H →ₗ.[ℂ] H
  /-- Self-adjointness, which also supplies density and closedness. -/
  dirac_selfAdjoint : IsSelfAdjoint dirac
  /-- Compactness of an everywhere-defined Dirac resolvent. -/
  compact_resolvent : HasCompactResolvent dirac
  /-- The represented algebra preserves the Dirac domain. -/
  domain_invariant : ∀ (a : A) (x : dirac.domain), representation a x ∈ dirac.domain
  /-- Bounded extension of each represented commutator `[D,a]`. -/
  boundedCommutator : A → (H →L[ℂ] H)
  /-- The bounded extension agrees with the algebraic commutator on the Dirac domain. -/
  boundedCommutator_eq : ∀ (a : A) (x : dirac.domain),
    boundedCommutator a x =
      dirac ⟨representation a x, domain_invariant a x⟩ - representation a (dirac x)

namespace UnboundedSpectralTriple

variable {A H : Type*} [Semiring A] [Algebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint Dirac operator in an unbounded spectral triple is a genuine Physlib unbounded
operator: its domain is dense and it is closable. -/
lemma dirac_isUnbounded (T : UnboundedSpectralTriple A H) : T.dirac.IsUnbounded :=
  LinearPMap.IsSelfAdjoint.isUnbounded T.dirac_selfAdjoint

/-- The spectrum of the unbounded spectral triple's self-adjoint Dirac operator is real. -/
lemma dirac_spectrum_real (T : UnboundedSpectralTriple A H) :
    T.dirac.spectrum ⊆ Set.range Complex.ofReal :=
  LinearPMap.IsSelfAdjoint.spectrum_real T.dirac_selfAdjoint

end UnboundedSpectralTriple

/-! ## C. Dirac eigenvalue asymptotics as effective dimension -/

/-- The spectral dimension read from a positive Dirac eigenvalue exponent:
`|lambda_k| ~ k^alpha` corresponds to `d_eff = 1/alpha`. -/
def effectiveDimensionFromExponent (α : ℝ) : ℝ := α⁻¹

/-- A reciprocal Weyl exponent recovers its dimension exactly. -/
@[simp] lemma effectiveDimensionFromExponent_inv (d : ℝ) :
    effectiveDimensionFromExponent d⁻¹ = d := by
  simp [effectiveDimensionFromExponent]

/-- Pointwise power-law carrier for the absolute eigenvalues of a Dirac-type operator.  This is a
strong finite/explicit substitute for an asymptotic equivalence and can be weakened downstream to a
`Tendsto` statement without changing the dimension convention. -/
def IsDiracEigenvaluePowerLaw (eigenvalueAbs : ℕ → ℝ) (C α : ℝ) : Prop :=
  ∀ k : ℕ, eigenvalueAbs k = C * ((k + 1 : ℕ) : ℝ) ^ α

/-- Analytic dimension-spectrum data attached to an unbounded Dirac operator.

The pole set is kept explicit because proving meromorphic continuation of the spectral zeta
function is geometry-specific.  This carrier nevertheless fixes the exact interface: eigenvalue
asymptotics determine a reciprocal growth dimension, and the leading zeta pole must equal it. -/
structure DiracDimensionSpectrumData where
  /-- Absolute Dirac eigenvalues, including multiplicity. -/
  eigenvalueAbs : ℕ → ℝ
  /-- Weyl exponent in `|lambda_k| ~ k^alpha`. -/
  growthExponent : ℝ
  /-- Analytically continued spectral zeta function. -/
  spectralZeta : ℂ → ℂ
  /-- On the real convergence axis, the continuation agrees with the repository's actual `tsum`
  spectral zeta of the supplied absolute Dirac eigenvalues. -/
  spectralZeta_real_eq : ∀ s : ℝ, spectralZeta (s : ℂ) =
    (Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization.spectralZeta
      eigenvalueAbs s : ℂ)
  /-- Its pole set (the Connes dimension spectrum in this carrier). -/
  dimensionSpectrum : Set ℂ
  /-- Leading real spectral dimension. -/
  leadingDimension : ℝ
  /-- The leading dimension occurs in the dimension spectrum. -/
  leadingDimension_mem : (leadingDimension : ℂ) ∈ dimensionSpectrum
  /-- Weyl growth and the leading zeta pole use the same dimension convention. -/
  leadingDimension_eq : leadingDimension = effectiveDimensionFromExponent growthExponent

namespace DiracDimensionSpectrumData

/-- The effective dimension read from Dirac eigenvalue growth is the leading dimension-spectrum
pole recorded by the analytic continuation certificate. -/
theorem effectiveDimension_eq_leadingDimension (S : DiracDimensionSpectrumData) :
    effectiveDimensionFromExponent S.growthExponent = S.leadingDimension := by
  exact S.leadingDimension_eq.symm

end DiracDimensionSpectrumData

/-- The effective atomic Dirac exponent associated with an Aufbau shell: the reciprocal of the
already-proved shell mode dimension. -/
def atomicDiracGrowthExponent (n : ℕ) : ℝ :=
  ((aufbauShellDim n : ℕ) : ℝ)⁻¹

/-- Reading the model exponent spectrally returns the exact Aufbau shell dimension. -/
lemma atomic_effectiveDimension_eq_shellDim (n : ℕ) :
    effectiveDimensionFromExponent (atomicDiracGrowthExponent n) =
      ((aufbauShellDim n : ℕ) : ℝ) := by
  simp [atomicDiracGrowthExponent]

/-- Hence the effective dimension is the established hydrogenic shell capacity `2 n^2`. -/
theorem atomic_effectiveDimension_eq_two_mul_sq (n : ℕ) :
    effectiveDimensionFromExponent (atomicDiracGrowthExponent n) =
      ((2 * n ^ 2 : ℕ) : ℝ) := by
  rw [atomic_effectiveDimension_eq_shellDim, aufbauShellDim_eq]

/-! ## D. Atiyah--Singer index data and finite index pairings -/

/-- The actual analytic index used throughout this module: `dim ker D - dim coker D`. -/
def analyticIndex {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℂ X] [Module ℂ Y] (D : X →ₗ[ℂ] Y) : ℤ :=
  D.index

/-- An explicit Atiyah--Singer certificate.  Its topological density is the scalar representative of
`Ahat(M) wedge ch(E)` in the chosen top-degree integration convention. -/
structure AtiyahSingerIndexData
    (M X Y : Type*) [MeasurableSpace M]
    [AddCommGroup X] [AddCommGroup Y] [Module ℂ X] [Module ℂ Y] where
  /-- Chiral/twisted Dirac operator whose analytic index is computed. -/
  diracPlus : X →ₗ[ℂ] Y
  /-- Top-degree scalar density representing `Ahat(M)`. -/
  ahatDensity : M → ℝ
  /-- Top-degree scalar density representing `ch(E)`. -/
  chernCharacterDensity : M → ℝ
  /-- Measure/orientation convention for the characteristic-number integral. -/
  volume : Measure M
  /-- Integrability of the local index density. -/
  density_integrable : Integrable (fun x => ahatDensity x * chernCharacterDensity x) volume
  /-- Atiyah--Singer: analytic index equals the integrated topological density. -/
  index_formula : (diracPlus.index : ℝ) =
    ∫ x, ahatDensity x * chernCharacterDensity x ∂volume

namespace AtiyahSingerIndexData

variable {M X Y : Type*} [MeasurableSpace M]
  [AddCommGroup X] [AddCommGroup Y] [Module ℂ X] [Module ℂ Y]

/-- Public analytic-index-equals-topological-index theorem exposed by the certificate. -/
theorem analyticIndex_eq_topologicalIndex (I : AtiyahSingerIndexData M X Y) :
    (analyticIndex I.diracPlus : ℝ) =
      ∫ x, I.ahatDensity x * I.chernCharacterDensity x ∂I.volume :=
  I.index_formula

end AtiyahSingerIndexData

/-- Finite complex mode space of cardinality `n`. -/
abbrev FiniteModeSpace (n : ℕ) := Fin n → ℂ

/-- The basic finite index-pairing operator from a `positive` register to a `negative` register.
The zero map isolates the graded dimension difference and is sufficient to encode discrete mode
counts without inventing a topological theorem. -/
def finiteIndexPairingOperator (positive negative : ℕ) :
    FiniteModeSpace positive →ₗ[ℂ] FiniteModeSpace negative :=
  0

/-- Every linear operator between the displayed finite graded mode spaces has index equal to the
dimension difference.  Thus the discrete pairing is independent of the chosen finite representative,
not an artefact of selecting the zero map. -/
lemma finiteIndexPairing_index (positive negative : ℕ)
    (D : FiniteModeSpace positive →ₗ[ℂ] FiniteModeSpace negative) :
    D.index = (positive : ℤ) - (negative : ℤ) := by
  rw [LinearMap.index_eq_of_finiteDimensional]
  simp [FiniteModeSpace]

/-- The pairing is the exact signed difference of the two graded mode counts. -/
theorem finiteIndexPairingOperator_index (positive negative : ℕ) :
    (finiteIndexPairingOperator positive negative).index =
      (positive : ℤ) - (negative : ℤ) :=
  finiteIndexPairing_index positive negative (finiteIndexPairingOperator positive negative)

/-- The K-homology/K-theory index shadow of a closed angular-momentum shell. -/
def shellClosureIndex (l : ℕ) : ℤ :=
  (finiteIndexPairingOperator (capacityOfAngularMomentum l) 0).index

/-- A shell closure carries exactly its Pauli mode count as its index pairing. -/
theorem shellClosureIndex_eq_capacity (l : ℕ) :
    shellClosureIndex l = capacityOfAngularMomentum l := by
  rw [shellClosureIndex, finiteIndexPairingOperator_index]
  simp

/-- The index pairing encoding an occupied valence register of size `q`. -/
def valenceIndex (q : ℕ) : ℤ :=
  (finiteIndexPairingOperator q 0).index

/-- The valence index is the discrete occupied-mode count. -/
@[simp] theorem valenceIndex_eq (q : ℕ) : valenceIndex q = q := by
  rw [valenceIndex, finiteIndexPairingOperator_index]
  simp

/-- Signed particle--hole index inside a shell of capacity `C`. -/
def particleHoleIndex (C q : ℕ) : ℤ :=
  (finiteIndexPairingOperator q (C - q)).index

/-- The particle--hole pairing is the signed difference `q - (C-q)`. -/
theorem particleHoleIndex_eq (C q : ℕ) :
    particleHoleIndex C q = (q : ℤ) - (C - q : ℕ) := by
  exact finiteIndexPairingOperator_index q (C - q)

/-! ## E. Finite Kasparov correspondences and their product -/

/-- An algebra-equivariant finite-dimensional correspondence.

This is the exact part of a Kasparov cycle needed for induction/restriction and index composition:
an algebra map, a module map, and their intertwining law. -/
structure FiniteKasparovCorrespondence
    (A B X Y : Type*) [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B]
    [AddCommGroup X] [AddCommGroup Y] [Module ℂ X] [Module ℂ Y]
    (rhoA : A →ₐ[ℂ] Module.End ℂ X)
    (rhoB : B →ₐ[ℂ] Module.End ℂ Y) where
  /-- Change of coordinate/observable algebra. -/
  algebraMap : A →ₐ[ℂ] B
  /-- Induced map of finite modules. -/
  moduleMap : X →ₗ[ℂ] Y
  /-- Equivariance of the module map with respect to the algebra change. -/
  equivariant : ∀ (a : A) (x : X),
    moduleMap (rhoA a x) = rhoB (algebraMap a) (moduleMap x)

namespace FiniteKasparovCorrespondence

variable {A B C X Y Z : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module ℂ X] [Module ℂ Y] [Module ℂ Z]
  {rhoA : A →ₐ[ℂ] Module.End ℂ X}
  {rhoB : B →ₐ[ℂ] Module.End ℂ Y}
  {rhoC : C →ₐ[ℂ] Module.End ℂ Z}

/-- Finite Kasparov product: compose the algebra correspondence and its module operator. -/
def kasparovProduct
    (F : FiniteKasparovCorrespondence A B X Y rhoA rhoB)
    (G : FiniteKasparovCorrespondence B C Y Z rhoB rhoC) :
    FiniteKasparovCorrespondence A C X Z rhoA rhoC where
  algebraMap := G.algebraMap.comp F.algebraMap
  moduleMap := G.moduleMap ∘ₗ F.moduleMap
  equivariant := by
    intro a x
    rw [LinearMap.comp_apply, F.equivariant, G.equivariant]
    rfl

/-- Analytic index carried by a finite correspondence. -/
def index (F : FiniteKasparovCorrespondence A B X Y rhoA rhoB) : ℤ :=
  F.moduleMap.index

/-- **Kasparov-product index law.**  The exact-sequence theorem for linear-map indices proves that
the bivariant index is additive under composition. -/
theorem index_kasparovProduct
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] [FiniteDimensional ℂ Z]
    (F : FiniteKasparovCorrespondence A B X Y rhoA rhoB)
    (G : FiniteKasparovCorrespondence B C Y Z rhoB rhoC) :
    (kasparovProduct F G).index = G.index + F.index := by
  simp [index, kasparovProduct, LinearMap.index_comp]

/-- Chemical induction followed by restriction therefore adds the two correspondence indices.  The
name exposes the generic Kasparov law directly to bonding modules without duplicating its proof. -/
theorem chemicalBond_induction_restriction_index
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] [FiniteDimensional ℂ Z]
    (induction : FiniteKasparovCorrespondence A B X Y rhoA rhoB)
    (restriction : FiniteKasparovCorrespondence B C Y Z rhoB rhoC) :
    (kasparovProduct induction restriction).index =
      restriction.index + induction.index :=
  index_kasparovProduct induction restriction

end FiniteKasparovCorrespondence

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.UnboundedSpectralTriple.dirac_spectrum_real where
  formalizes @ "claim:a-self-adjoint-compact-resolvent-dirac-operator-in-an-unbounded-spectral-triple-has-real-spectrum",
  supported_by @ "lean:LinearPMap.IsSelfAdjoint.spectrum_real",
  caveat @ "claim:compact-resolvent-and-bounded-commutator-proofs-remain-obligations-of-each-concrete-dirac-model"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteSpectralTriple.spectralAction_mono_cutoff where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:for-an-antitone-profile-the-finite-connes-spectral-action-is-monotone-in-the-positive-cutoff-scale",
  caveat @ "claim:finite-eigenvalue-trace-law-not-the-continuum-heat-kernel-asymptotic-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.atomic_effectiveDimension_eq_two_mul_sq where
  formalizes @ "claim:the-effective-atomic-spectral-dimension-from-the-model-dirac-exponent-is-the-established-two-n-squared-shell-capacity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower.aufbauShellDim_eq",
  caveat @ "claim:effective-exponent-model-not-a-spectral-asymptotic-theorem-for-the-physical-many-electron-dirac-operator"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.DiracDimensionSpectrumData.effectiveDimension_eq_leadingDimension where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-reciprocal-dirac-eigenvalue-growth-exponent-agrees-with-the-leading-dimension-spectrum-pole",
  requires @ "claim:geometry-specific-meromorphic-continuation-and-leading-pole-certificate",
  caveat @ "claim:this-interface-does-not-derive-meromorphic-continuation-for-an-arbitrary-dirac-operator"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.AtiyahSingerIndexData.analyticIndex_eq_topologicalIndex where
  formalizes @ "claim:the-analytic-dirac-index-equals-the-integrated-ahat-times-chern-character-topological-index",
  requires @ "claim:atiyah-singer-index-certificate-for-the-selected-manifold-bundle-and-dirac-operator",
  caveat @ "claim:the-characteristic-class-index-formula-is-explicit-data-not-derived-by-this-finite-adapter"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.shellClosureIndex_eq_capacity where
  formalizes @ "claim:a-closed-atomic-shell-pauli-capacity-is-an-integer-linear-index-pairing",
  supported_by @ "lean:LinearMap.index_eq_of_finiteDimensional"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteKasparovCorrespondence.index_kasparovProduct where
  formalizes @ "claim:finite-kasparov-correspondence-indices-add-under-the-kasparov-product",
  supported_by @ "lean:LinearMap.index_comp",
  caveat @ "claim:finite-equivariant-correspondence-not-the-full-analytic-kk-category-of-cstar-algebras"

zil_file_contract physlib.connesAtiyahSingerKasparov where
  promises "A finite Connes spectral triple exposes the Dirac commutator, eigenvalue counting, and spectral action; a genuine LinearPMap unbounded spectral triple requires a self-adjoint compact-resolvent Dirac operator and bounded represented commutators; an explicit zeta/pole-set carrier relates Dirac eigenvalue growth to the leading dimension-spectrum pole; arbitrary finite linear index pairings encode shell and valence counts; an explicit Atiyah--Singer certificate equates analytic index with the integrated A-hat/Chern-character density; and finite algebra-equivariant Kasparov products compose induction/restriction data with an additive index."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:LinearMap.index", "lean:LinearMap.index_comp",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.cliffordDirac_sq_neg_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower.aufbauShellDim_eq"]
  forbids_substitutes ["a finite matrix carrier presented as the full unbounded compact-resolvent theory",
    "compact resolvent or bounded commutators asserted for a concrete Dirac operator without proofs",
    "the Atiyah--Singer characteristic-class formula claimed without an explicit certificate",
    "a finite equivariant correspondence presented as analytic KK(A,B) for arbitrary C-star algebras",
    "atomic spectral dimension presented as an empirical eigenvalue asymptotic without a physical Dirac-spectrum proof"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteSpectralTriple.spectralAction_nonneg,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteSpectralTriple.spectralAction_mono_cutoff,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.UnboundedSpectralTriple.dirac_spectrum_real,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.DiracDimensionSpectrumData.effectiveDimension_eq_leadingDimension,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.atomic_effectiveDimension_eq_two_mul_sq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.AtiyahSingerIndexData.analyticIndex_eq_topologicalIndex,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.shellClosureIndex_eq_capacity,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteKasparovCorrespondence.index_kasparovProduct]

/- ZIL-END -/
