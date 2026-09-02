/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems
public import Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge
public import Mathlib.Tactic

/-!
# Higher Berry curvature from Schmidt decomposition and MPS

Lean-checkable core of

* O. E. Sommer, X. Wen, A. Vishwanath,
  *Higher Berry Curvature from the Wave Function I: Schmidt Decomposition
  and Matrix Product States*, arXiv:2405.05316v1.

The paper's analytic claims involve smooth families of infinite MPS, transfer
matrix resolvents, and gerbe connective structures.  This file formalizes the
parts that can be made into repo-facing checked algebra without hiding those
analytic hypotheses:

* the degree shift: in spatial dimension `d`, higher Berry curvature is a
  `(d+2)`-form;
* the Schmidt-decomposition formula, Eq. (1), as a finite sum of Schmidt-weight
  derivatives times Berry-curvature terms;
* the local Berry-curvature flow/descent bookkeeping, Eq. (2)-(4);
* the MPS cut formula and the uniform-MPS gauge correction, Eq. (6) and
  Eq. (9)-(11);
* the gerbe descent equations, Eq. (17)-(19), as a connection interface with
  patch-independence consequences;
* the exactly solvable pump integral behind Eq. (15), including the normalized
  value `1`;
* a bridge to the existing TKNN/Integer-QH layer: when the HBC period equals a
  TKNN Berry-curvature period, the integer invariants are equal.

No global smoothness, convergence, iDMRG numerics, or gerbe quantization theorem
is asserted for free.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.HigherBerryCurvatureMPS

open Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems
open Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge


/-- Higher Berry curvature in spatial dimension `d` is a `(d+2)`-form. -/
def higherBerryFormDegree (spatialDimension : ℕ) : ℕ :=
  spatialDimension + 2

/-- In the paper's main `d = 1` case, the higher Berry curvature is a 3-form. -/
lemma higherBerryFormDegree_one_dimensional :
    higherBerryFormDegree 1 = 3 := rfl

/-- Finite Schmidt data for Eq. (1).  `weightDerivative α` represents
`d(c_α^2)`, while `berryCurvatureA α` represents the real 2-form
`Im ⟨dα|dα⟩_[A]` promoted into the target form carrier. -/
structure SchmidtHigherBerryData (Idx Form : Type*) [AddCommGroup Form]
    [Module ℝ Form] where
  weightDerivative : Idx → ℝ
  berryCurvatureA : Idx → Form

/-- Eq. (1): the higher Berry curvature across the cut from a Schmidt
decomposition is the finite sum
`Σ_α d(c_α^2) · Im⟨dα|dα⟩_[A]`. -/
def schmidtHigherBerryCurvature {Idx Form : Type*} [Fintype Idx]
    [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtHigherBerryData Idx Form) : Form :=
  ∑ α : Idx, S.weightDerivative α • S.berryCurvatureA α

/-- If all Schmidt weights are locally constant, Eq. (1) gives zero higher
Berry curvature. -/
lemma schmidtHigherBerryCurvature_zero_weights {Idx Form : Type*}
    [Fintype Idx] [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtHigherBerryData Idx Form)
    (hzero : ∀ α : Idx, S.weightDerivative α = 0) :
    schmidtHigherBerryCurvature S = 0 := by
  unfold schmidtHigherBerryCurvature
  simp [hzero]

/-- Eq. (1) is invariant under replacing the data by pointwise equal Schmidt
weight derivatives and curvature terms. -/
lemma schmidtHigherBerryCurvature_congr {Idx Form : Type*}
    [Fintype Idx] [AddCommGroup Form] [Module ℝ Form]
    (S T : SchmidtHigherBerryData Idx Form)
    (hw : ∀ α : Idx, S.weightDerivative α = T.weightDerivative α)
    (hF : ∀ α : Idx, S.berryCurvatureA α = T.berryCurvatureA α) :
    schmidtHigherBerryCurvature S = schmidtHigherBerryCurvature T := by
  unfold schmidtHigherBerryCurvature
  exact Finset.sum_congr rfl fun α _ => by rw [hw α, hF α]


/-- The sector-trace form of Eq. (1): in a degenerate Schmidt sector, the
ordinary Berry curvature term is replaced by the trace of the non-Abelian
curvature of that sector. -/
structure SchmidtSectorHigherBerryData (Sector Form : Type*) [AddCommGroup Form]
    [Module ℝ Form] where
  sectorWeightDerivative : Sector → ℝ
  sectorCurvatureTrace : Sector → Form

/-- Sector version of the Schmidt HBC formula:
`Σ_s d(c_s^2) Tr F_s`. -/
def schmidtSectorHigherBerryCurvature {Sector Form : Type*} [Fintype Sector]
    [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtSectorHigherBerryData Sector Form) : Form :=
  ∑ s : Sector, S.sectorWeightDerivative s • S.sectorCurvatureTrace s

/-- The ordinary Schmidt formula is the special case where every Schmidt
label is its own sector. -/
def schmidtDataAsSectorData {Idx Form : Type*} [AddCommGroup Form]
    [Module ℝ Form] (S : SchmidtHigherBerryData Idx Form) :
    SchmidtSectorHigherBerryData Idx Form where
  sectorWeightDerivative := S.weightDerivative
  sectorCurvatureTrace := S.berryCurvatureA

/-- With singleton sectors, the non-Abelian sector-trace formula reduces
definitionally to Eq. (1). -/
lemma schmidtSector_singleton_eq_schmidt {Idx Form : Type*}
    [Fintype Idx] [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtHigherBerryData Idx Form) :
    schmidtSectorHigherBerryCurvature (schmidtDataAsSectorData S) =
      schmidtHigherBerryCurvature S := rfl

/-- If all sector Schmidt weights are locally constant, the sector-trace
higher Berry curvature vanishes. -/
lemma schmidtSectorHigherBerryCurvature_zero_weights {Sector Form : Type*}
    [Fintype Sector] [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtSectorHigherBerryData Sector Form)
    (hzero : ∀ s : Sector, S.sectorWeightDerivative s = 0) :
    schmidtSectorHigherBerryCurvature S = 0 := by
  unfold schmidtSectorHigherBerryCurvature
  simp [hzero]


/-- Local Berry-flow data.  `flow p q` is the 3-form `F_{pq}^{(3)}` and
`exteriorLocalCurvature q` is `dF_q^{(2)}`. -/
structure LocalBerryFlowData (Site Form2 Form3 : Type*) [Fintype Site]
    [AddCommGroup Form3] where
  localCurvature : Site → Form2
  flow : Site → Site → Form3
  exteriorLocalCurvature : Site → Form3
  descent : ∀ q : Site, (∑ p : Site, flow p q) = exteriorLocalCurvature q
  antisymmetric : ∀ p q : Site, flow p q = -flow q p

/-- Net higher Berry curvature flow across a cut: Eq. (4),
`Ω^(3)=Σ_{p<a<q}F_{pq}^{(3)}`. -/
def netHigherBerryFlow {Site Form2 Form3 : Type*} [Fintype Site]
    [AddCommGroup Form3] (D : LocalBerryFlowData Site Form2 Form3)
    (left right : Site → Prop) [DecidablePred left] [DecidablePred right] :
    Form3 :=
  Finset.sum (Finset.univ.filter left) fun p =>
    Finset.sum (Finset.univ.filter right) fun q => D.flow p q

/-- The local descent equation, Eq. (2), as a reusable theorem. -/
lemma localBerryFlow_descent {Site Form2 Form3 : Type*} [Fintype Site]
    [AddCommGroup Form3] (D : LocalBerryFlowData Site Form2 Form3) (q : Site) :
    (∑ p : Site, D.flow p q) = D.exteriorLocalCurvature q :=
  D.descent q

/-- The immediate solution `F_{pq}^{(3)} = d_p d_q A` is antisymmetric when the
site-local second derivative is supplied as antisymmetric. -/
lemma localBerryFlow_antisymmetric {Site Form2 Form3 : Type*} [Fintype Site]
    [AddCommGroup Form3] (D : LocalBerryFlowData Site Form2 Form3) (p q : Site) :
    D.flow p q = -D.flow q p :=
  D.antisymmetric p q

/-- Reversing the cut reverses the sign of every pair contribution. -/
lemma localBerryFlow_reverse_pair {Site Form2 Form3 : Type*} [Fintype Site]
    [AddCommGroup Form3] (D : LocalBerryFlowData Site Form2 Form3) (p q : Site) :
    D.flow q p = -D.flow p q := by
  rw [D.antisymmetric q p]


/-- Eq. (6) finite-cut carrier:
`Ω^(3) = -Im Σ_{p<a} (...)`.  The contraction value for each site is already
the real form contribution after applying `Im`. -/
def mpsLeftCanonicalCutCurvature {Site Form : Type*} [Fintype Site]
    [AddCommGroup Form] (leftOfCut : Site → Prop) [DecidablePred leftOfCut]
    (siteContribution : Site → Form) : Form :=
  -Finset.sum (Finset.univ.filter leftOfCut) fun p => siteContribution p

/-- If every left-of-cut contribution vanishes, the MPS cut curvature vanishes. -/
lemma mpsLeftCanonicalCutCurvature_zero {Site Form : Type*} [Fintype Site]
    [AddCommGroup Form] (leftOfCut : Site → Prop) [DecidablePred leftOfCut]
    (siteContribution : Site → Form)
    (hzero : ∀ p : Site, leftOfCut p → siteContribution p = 0) :
    mpsLeftCanonicalCutCurvature leftOfCut siteContribution = 0 := by
  unfold mpsLeftCanonicalCutCurvature
  have hsum :
      Finset.sum (Finset.univ.filter leftOfCut) (fun p => siteContribution p) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    exact hzero p (by simpa using hp)
  rw [hsum, neg_zero]

/-- Uniform-MPS contractions appearing in Eq. (9)-(11).  The two fields are
the already-contracted form values:

* `tangentResolventRight`: `Im(l|E_{dA}^{dA}(1-E_A^A)^{-1}|dr)`;
* `gaugeCorrection`: `Im(l|E_A^{dA}(1-E_A^A)^{-1}dE_A^A(1-E_A^A)^{-1}|dr)`.
-/
structure UniformMPSHBCContractions (Form : Type*) where
  tangentResolventRight : Form
  gaugeCorrection : Form

/-- Eq. (9)/(10): uniform-MPS HBC in left tangent-space gauge. -/
def uniformMPSHigherBerryLeftGauge {Form : Type*} [Neg Form]
    (C : UniformMPSHBCContractions Form) : Form :=
  -C.tangentResolventRight

/-- Eq. (11): the extra term present away from left tangent-space gauge. -/
def uniformMPSHigherBerryWithGaugeCorrection {Form : Type*} [Sub Form] [Neg Form]
    (C : UniformMPSHBCContractions Form) : Form :=
  -C.tangentResolventRight - C.gaugeCorrection

/-- If the non-left-gauge correction vanishes, the gauge-corrected expression
reduces to the left-gauge expression. -/
lemma uniformMPSHigherBerryWithGaugeCorrection_eq_leftGauge
    {Form : Type*} [AddCommGroup Form]
    (C : UniformMPSHBCContractions Form) (hzero : C.gaugeCorrection = 0) :
    uniformMPSHigherBerryWithGaugeCorrection C =
      uniformMPSHigherBerryLeftGauge C := by
  simp [uniformMPSHigherBerryWithGaugeCorrection,
    uniformMPSHigherBerryLeftGauge, hzero]

/-- The paper's HBC construction uses the MPS line of the existing tensor-network
taxonomy: one-dimensional, constant-entanglement scaling, finite correlation
length, and canonical form available for open/infinite MPS. -/
lemma higherBerryMPS_uses_existing_tensorNetworkProfile :
    (tensorNetworkProfile .MPS).spatialDimension = 1
      ∧ (tensorNetworkProfile .MPS).entropyScaling = .constant
      ∧ (tensorNetworkProfile .MPS).correlationLength = .finite
      ∧ (tensorNetworkProfile .MPS).canonicalForm = .openBoundaryOrInfiniteOnly := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-- Finite transfer-product carrier for Appendix A, Eq. (A3):
`E(b -> a) = Π E_p`.  This is only the finite algebraic product; the
infinite/uMPS resolvent remains an analytic input. -/
def finiteMPSTransferProduct {N : ℕ} {M : Type*} [CommMonoid M]
    (E : Fin N → M) : M :=
  ∏ p : Fin N, E p

lemma finiteMPSTransferProduct_const_one {N : ℕ} {M : Type*} [CommMonoid M] :
    finiteMPSTransferProduct (N := N) (fun _ : Fin N => (1 : M)) = 1 := by
  unfold finiteMPSTransferProduct
  simp

lemma finiteMPSTransferProduct_mul {N : ℕ} {M : Type*} [CommMonoid M]
    (E F : Fin N → M) :
    finiteMPSTransferProduct (fun p => E p * F p) =
      finiteMPSTransferProduct E * finiteMPSTransferProduct F := by
  unfold finiteMPSTransferProduct
  rw [Finset.prod_mul_distrib]

/-- Appendix A canonical MPS cut data: the left environment is identity and
the right environment is diagonal with the squared Schmidt coefficients. -/
structure CanonicalMPSCutData (Idx Env : Type*) [Fintype Idx] [One Env] where
  schmidtWeightSq : Idx → ℝ
  leftEnvironment : Env
  rightEnvironmentWeight : Idx → ℝ
  normalizedWeights : (∑ α : Idx, schmidtWeightSq α) = 1
  leftEnvironment_eq_one : leftEnvironment = 1
  rightEnvironment_diagonal :
    ∀ α : Idx, rightEnvironmentWeight α = schmidtWeightSq α

lemma canonicalMPS_leftEnvironment_eq_one {Idx Env : Type*} [Fintype Idx] [One Env]
    (C : CanonicalMPSCutData Idx Env) :
    C.leftEnvironment = 1 :=
  C.leftEnvironment_eq_one

lemma canonicalMPS_rightEnvironmentWeight_eq_schmidt {Idx Env : Type*}
    [Fintype Idx] [One Env] (C : CanonicalMPSCutData Idx Env) (α : Idx) :
    C.rightEnvironmentWeight α = C.schmidtWeightSq α :=
  C.rightEnvironment_diagonal α

lemma canonicalMPS_weights_normalized {Idx Env : Type*}
    [Fintype Idx] [One Env] (C : CanonicalMPSCutData Idx Env) :
    (∑ α : Idx, C.schmidtWeightSq α) = 1 :=
  C.normalizedWeights


/-- A finite, real-valued Schmidt decomposition of a bipartite state.

The carrier records the actual decomposition data:

* nonnegative Schmidt coefficients `coeff α`;
* left and right Schmidt vectors;
* orthonormality of both Schmidt families;
* the amplitude expansion
  `ψ(a,b) = Σ_α c_α ⟨a|α_L⟩ ⟨b|α_R⟩`;
* normalization `Σ_α c_α² = 1`.

This is intentionally finite: it is the algebraic layer needed by the paper's
Schmidt formula and by the existing tensor-network/SVD infrastructure. -/
structure FiniteSchmidtDecomposition (Idx Left Right : Type*) [Fintype Idx] where
  coeff : Idx → ℝ
  leftVector : Idx → Left
  rightVector : Idx → Right
  leftInner : Left → Left → ℝ
  rightInner : Right → Right → ℝ
  amplitude : Left → Right → ℝ
  coeff_nonneg : ∀ α : Idx, 0 ≤ coeff α
  normalized : (∑ α : Idx, coeff α ^ 2) = 1
  left_norm_one : ∀ α : Idx, leftInner (leftVector α) (leftVector α) = 1
  right_norm_one : ∀ α : Idx, rightInner (rightVector α) (rightVector α) = 1
  left_orthogonal :
    ∀ {α β : Idx}, α ≠ β → leftInner (leftVector α) (leftVector β) = 0
  right_orthogonal :
    ∀ {α β : Idx}, α ≠ β → rightInner (rightVector α) (rightVector β) = 0
  amplitude_eq_sum :
    ∀ a : Left, ∀ b : Right,
      amplitude a b =
        ∑ α : Idx,
          coeff α * leftInner a (leftVector α) * rightInner b (rightVector α)

/-- The squared Schmidt coefficient `c_α²`, i.e. the probability/eigenvalue
appearing in both reduced density matrices. -/
def finiteSchmidtWeightSq {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) : ℝ :=
  D.coeff α ^ 2

lemma finiteSchmidtCoefficient_nonneg {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    0 ≤ D.coeff α :=
  D.coeff_nonneg α

lemma finiteSchmidtWeightSq_nonneg {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    0 ≤ finiteSchmidtWeightSq D α := by
  unfold finiteSchmidtWeightSq
  exact sq_nonneg (D.coeff α)

lemma finiteSchmidtWeightSq_sum_eq_one {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) :
    (∑ α : Idx, finiteSchmidtWeightSq D α) = 1 := by
  simpa [finiteSchmidtWeightSq] using D.normalized

lemma finiteSchmidt_left_orthonormal {Idx Left Right : Type*} [Fintype Idx]
    [DecidableEq Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α β : Idx) :
    D.leftInner (D.leftVector α) (D.leftVector β) =
      if α = β then 1 else 0 :=
  by
    by_cases h : α = β
    · subst β
      rw [if_pos rfl]
      exact D.left_norm_one α
    · rw [if_neg h]
      exact D.left_orthogonal h

lemma finiteSchmidt_right_orthonormal {Idx Left Right : Type*} [Fintype Idx]
    [DecidableEq Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α β : Idx) :
    D.rightInner (D.rightVector α) (D.rightVector β) =
      if α = β then 1 else 0 :=
  by
    by_cases h : α = β
    · subst β
      rw [if_pos rfl]
      exact D.right_norm_one α
    · rw [if_neg h]
      exact D.right_orthogonal h

lemma finiteSchmidt_left_norm_one {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    D.leftInner (D.leftVector α) (D.leftVector α) = 1 :=
  D.left_norm_one α

lemma finiteSchmidt_right_norm_one {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    D.rightInner (D.rightVector α) (D.rightVector α) = 1 :=
  D.right_norm_one α

lemma finiteSchmidt_left_offDiagonal_zero {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) {α β : Idx}
    (h : α ≠ β) :
    D.leftInner (D.leftVector α) (D.leftVector β) = 0 :=
  D.left_orthogonal h

lemma finiteSchmidt_right_offDiagonal_zero {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) {α β : Idx}
    (h : α ≠ β) :
    D.rightInner (D.rightVector α) (D.rightVector β) = 0 :=
  D.right_orthogonal h

/-- The Schmidt expansion of the bipartite amplitude. -/
lemma finiteSchmidt_amplitude_expansion {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (a : Left) (b : Right) :
    D.amplitude a b =
      ∑ α : Idx,
        D.coeff α * D.leftInner a (D.leftVector α) *
          D.rightInner b (D.rightVector α) :=
  D.amplitude_eq_sum a b

/-- The algebraic Schmidt rank of this finite decomposition. -/
def finiteSchmidtRank {Idx Left Right : Type*} [Fintype Idx]
    (_D : FiniteSchmidtDecomposition Idx Left Right) : ℕ :=
  Fintype.card Idx

/-- Left reduced-density eigenvalues are the squared Schmidt coefficients. -/
def leftReducedDensityEigenvalue {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) : ℝ :=
  finiteSchmidtWeightSq D α

/-- Right reduced-density eigenvalues are the same squared Schmidt
coefficients. -/
def rightReducedDensityEigenvalue {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) : ℝ :=
  finiteSchmidtWeightSq D α

lemma leftReducedDensityEigenvalue_nonneg {Idx Left Right : Type*}
    [Fintype Idx] (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    0 ≤ leftReducedDensityEigenvalue D α := by
  simpa [leftReducedDensityEigenvalue] using finiteSchmidtWeightSq_nonneg D α

lemma rightReducedDensityEigenvalue_nonneg {Idx Left Right : Type*}
    [Fintype Idx] (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    0 ≤ rightReducedDensityEigenvalue D α := by
  simpa [rightReducedDensityEigenvalue] using finiteSchmidtWeightSq_nonneg D α

lemma leftReducedDensity_trace_one {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) :
    (∑ α : Idx, leftReducedDensityEigenvalue D α) = 1 := by
  simpa [leftReducedDensityEigenvalue] using finiteSchmidtWeightSq_sum_eq_one D

lemma rightReducedDensity_trace_one {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) :
    (∑ α : Idx, rightReducedDensityEigenvalue D α) = 1 := by
  simpa [rightReducedDensityEigenvalue] using finiteSchmidtWeightSq_sum_eq_one D

/-- The two reduced density matrices have the same nonzero Schmidt spectrum. -/
lemma left_right_reducedDensity_spectra_eq {Idx Left Right : Type*}
    [Fintype Idx] (D : FiniteSchmidtDecomposition Idx Left Right) (α : Idx) :
    leftReducedDensityEigenvalue D α = rightReducedDensityEigenvalue D α := rfl

/-- A finite Schmidt decomposition supplies the existing tensor-network
`SchmidtSVDData`: the Schmidt rank is exactly the number of singular values. -/
def finiteSchmidtSVDData {Idx Left Right : Type*} [Fintype Idx]
    (_D : FiniteSchmidtDecomposition Idx Left Right) : SchmidtSVDData where
  schmidtRank := Fintype.card Idx
  singularValueCount := Fintype.card Idx
  rank_eq_singularValueCount := rfl

lemma finiteSchmidt_rank_eq_singularValueCount {Idx Left Right : Type*}
    [Fintype Idx] (D : FiniteSchmidtDecomposition Idx Left Right) :
    (finiteSchmidtSVDData D).schmidtRank =
      (finiteSchmidtSVDData D).singularValueCount :=
  schmidtRank_eq_singularValueCount (finiteSchmidtSVDData D)

/-- A finite Schmidt decomposition supplies the canonical MPS cut data:
the canonical weights are `c_α²`, the left environment is `1`, and the right
environment is diagonal in the Schmidt basis. -/
def canonicalMPSCutDataOfFiniteSchmidt {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) :
    CanonicalMPSCutData Idx Unit where
  schmidtWeightSq := finiteSchmidtWeightSq D
  leftEnvironment := ()
  rightEnvironmentWeight := finiteSchmidtWeightSq D
  normalizedWeights := finiteSchmidtWeightSq_sum_eq_one D
  leftEnvironment_eq_one := rfl
  rightEnvironment_diagonal := fun _ => rfl

lemma canonicalMPSCutDataOfFiniteSchmidt_weights_normalized
    {Idx Left Right : Type*} [Fintype Idx]
    (D : FiniteSchmidtDecomposition Idx Left Right) :
    (∑ α : Idx,
      (canonicalMPSCutDataOfFiniteSchmidt D).schmidtWeightSq α) = 1 :=
  canonicalMPS_weights_normalized (canonicalMPSCutDataOfFiniteSchmidt D)

/-- The explicit finite Schmidt decomposition feeds Eq. (1) by providing the
same Schmidt labels and squared-weight channel used by the HBC formula. -/
def finiteSchmidtHigherBerryData {Idx Left Right Form : Type*} [Fintype Idx]
    [AddCommGroup Form] [Module ℝ Form]
    (_D : FiniteSchmidtDecomposition Idx Left Right)
    (weightDerivative : Idx → ℝ) (berryCurvatureA : Idx → Form) :
    SchmidtHigherBerryData Idx Form where
  weightDerivative := weightDerivative
  berryCurvatureA := berryCurvatureA

lemma finiteSchmidtHigherBerryCurvature_eq_sum
    {Idx Left Right Form : Type*} [Fintype Idx]
    [AddCommGroup Form] [Module ℝ Form]
    (D : FiniteSchmidtDecomposition Idx Left Right)
    (weightDerivative : Idx → ℝ) (berryCurvatureA : Idx → Form) :
    schmidtHigherBerryCurvature
      (finiteSchmidtHigherBerryData D weightDerivative berryCurvatureA)
      = ∑ α : Idx, weightDerivative α • berryCurvatureA α := rfl


/-- De Rahm-Cech descent data for the uMPS gerbe connection.  This records the
paper's Eq. (17)-(19) as explicit fields and lets downstream modules use the
patch-independence consequences without assuming a hidden global theorem. -/
structure UMPSGerbeDescentData (Patch Form1 Form2 Form3 : Type*)
    [AddCommGroup Form1] [AddCommGroup Form2] where
  cInvdc : Patch → Patch → Patch → Form1
  oneConnection : Patch → Patch → Form1
  twoConnection : Patch → Form2
  curvature3 : Form3
  d1 : Form1 → Form2
  d2 : Form2 → Form3
  descent17 :
    ∀ α β γ : Patch,
      oneConnection α β + oneConnection β γ + oneConnection γ α =
        -cInvdc α β γ
  descent18 :
    ∀ α β : Patch,
      twoConnection α - twoConnection β = d1 (oneConnection α β)
  descent19 :
    ∀ α : Patch,
      curvature3 = d2 (twoConnection α)

/-- Eq. (19) makes the 3-curvature independent of the chosen patch. -/
lemma gerbe_curvature_patch_independent
    {Patch Form1 Form2 Form3 : Type*} [AddCommGroup Form1] [AddCommGroup Form2]
    (G : UMPSGerbeDescentData Patch Form1 Form2 Form3) (α β : Patch) :
    G.d2 (G.twoConnection α) = G.d2 (G.twoConnection β) := by
  rw [← G.descent19 α, ← G.descent19 β]

/-- The two-connection differences telescope around a triple overlap. -/
lemma gerbe_twoConnection_cyclic_telescope
    {Patch Form1 Form2 Form3 : Type*} [AddCommGroup Form1] [AddCommGroup Form2]
    (G : UMPSGerbeDescentData Patch Form1 Form2 Form3) (α β γ : Patch) :
    (G.twoConnection α - G.twoConnection β)
      + (G.twoConnection β - G.twoConnection γ)
      + (G.twoConnection γ - G.twoConnection α) = 0 := by
  abel

/-- Combining Eq. (18) on a triple overlap gives the cyclic sum of the
one-connection differentials. -/
lemma gerbe_descent18_cyclic_sum
    {Patch Form1 Form2 Form3 : Type*} [AddCommGroup Form1] [AddCommGroup Form2]
    (G : UMPSGerbeDescentData Patch Form1 Form2 Form3) (α β γ : Patch) :
    G.d1 (G.oneConnection α β)
      + G.d1 (G.oneConnection β γ)
      + G.d1 (G.oneConnection γ α) = 0 := by
  rw [← G.descent18 α β, ← G.descent18 β γ, ← G.descent18 γ α]
  abel


/-- Heaviside factor `θ(α-π/2)` used in Eq. (15). -/
def hbcHeavisideAfterEquator (alpha : ℝ) : ℝ :=
  if Real.pi / 2 ≤ alpha then 1 else 0

/-- Eq. (15) density coefficient:
`-θ(α-π/2) * (1/2) * cos α * sin θ`. -/
def exactSolvableHBCDensity (alpha theta : ℝ) : ℝ :=
  -hbcHeavisideAfterEquator alpha * (1 / 2) * Real.cos alpha * Real.sin theta

lemma exactSolvableHBCDensity_before_equator
    {alpha theta : ℝ} (h : ¬ Real.pi / 2 ≤ alpha) :
    exactSolvableHBCDensity alpha theta = 0 := by
  simp [exactSolvableHBCDensity, hbcHeavisideAfterEquator, h]

lemma exactSolvableHBCDensity_after_equator
    {alpha theta : ℝ} (h : Real.pi / 2 ≤ alpha) :
    exactSolvableHBCDensity alpha theta =
      -(1 / 2) * Real.cos alpha * Real.sin theta := by
  simp [exactSolvableHBCDensity, hbcHeavisideAfterEquator, h]

/-- Antiderivative contribution from the `α ∈ [π/2,π]` part of Eq. (15). -/
def exactSolvableAlphaContribution : ℝ :=
  -(1 / 2) * (Real.sin Real.pi - Real.sin (Real.pi / 2))

/-- Angular `θ` contribution from integrating `sin θ` over `[0,π]`. -/
def exactSolvableThetaContribution : ℝ :=
  -Real.cos Real.pi + Real.cos 0

/-- Azimuthal `φ` contribution over `[0,2π]`. -/
def exactSolvablePhiContribution : ℝ :=
  2 * Real.pi

lemma exactSolvableAlphaContribution_eq_half :
    exactSolvableAlphaContribution = 1 / 2 := by
  unfold exactSolvableAlphaContribution
  simp [Real.sin_pi, Real.sin_pi_div_two]

lemma exactSolvableThetaContribution_eq_two :
    exactSolvableThetaContribution = 2 := by
  unfold exactSolvableThetaContribution
  simp [Real.cos_pi]
  norm_num

/-- The separated elementary integral of Eq. (15). -/
def exactSolvableHBCIntegral : ℝ :=
  exactSolvableAlphaContribution
    * exactSolvableThetaContribution
    * exactSolvablePhiContribution

/-- Eq. (15): the exactly solvable model has total HBC period `2π`. -/
lemma exactSolvableHBCIntegral_eq_two_pi :
    exactSolvableHBCIntegral = 2 * Real.pi := by
  unfold exactSolvableHBCIntegral exactSolvablePhiContribution
  rw [exactSolvableAlphaContribution_eq_half,
    exactSolvableThetaContribution_eq_two]
  ring


/-- Appendix B, Eq. (B7): the equator two-cell carries one unit of curvature
period, represented by the period `2π`. -/
def twoPatchEquatorCurvaturePeriod : ℝ :=
  2 * Real.pi

/-- Appendix B, Eq. (B8): the equator two-cell has Chern number one. -/
lemma twoPatchEquatorChernNumber_eq_one :
    (1 / (2 * Real.pi)) * twoPatchEquatorCurvaturePeriod = 1 := by
  unfold twoPatchEquatorCurvaturePeriod
  field_simp [Real.pi_ne_zero]

/-- The two-patch gerbe boundary calculation and the bulk HBC calculation
give the same period in the exactly solvable model. -/
lemma twoPatchEquatorCurvaturePeriod_eq_exactSolvableHBCIntegral :
    twoPatchEquatorCurvaturePeriod = exactSolvableHBCIntegral := by
  rw [exactSolvableHBCIntegral_eq_two_pi]
  rfl


/-- Appendix C, Eq. (C4): in the two-site calculation, the Berry-curvature flow
from `A` to `B` is the same Schmidt HBC expression as Eq. (1). -/
def twoSiteBerryFlow {Idx Form : Type*} [Fintype Idx]
    [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtHigherBerryData Idx Form) : Form :=
  schmidtHigherBerryCurvature S

lemma twoSiteBerryFlow_eq_schmidtHigherBerryCurvature {Idx Form : Type*}
    [Fintype Idx] [AddCommGroup Form] [Module ℝ Form]
    (S : SchmidtHigherBerryData Idx Form) :
    twoSiteBerryFlow S = schmidtHigherBerryCurvature S := rfl

/-- Appendix C, Eq. (C6): nested Schmidt data for a three-region/d=2 flow.
`outerWeightDerivative β` represents `d(c_β^2)`, and
`innerWeightDerivative β α` represents `d(c_{α;β}^2)`. -/
structure NestedSchmidtHigherFlowData
    (Outer : Type*) (Inner : Outer → Type*) (Form : Type*)
    [AddCommGroup Form] [Module ℝ Form] where
  outerWeightDerivative : Outer → ℝ
  innerWeightDerivative : ∀ β : Outer, Inner β → ℝ
  berryCurvatureA : ∀ β : Outer, Inner β → Form

/-- Appendix C, Eq. (C6): `Σ_{β,α} dc_β² dc_{α;β}² F_{α;β}`. -/
def nestedSchmidtHigherFlow {Outer : Type*} {Inner : Outer → Type*}
    {Form : Type*} [Fintype Outer] [∀ β : Outer, Fintype (Inner β)]
    [AddCommGroup Form] [Module ℝ Form]
    (S : NestedSchmidtHigherFlowData Outer Inner Form) : Form :=
  ∑ β : Outer, ∑ α : Inner β,
    (S.outerWeightDerivative β * S.innerWeightDerivative β α)
      • S.berryCurvatureA β α

/-- If the outer Schmidt weights are locally constant, the nested flow
vanishes. -/
lemma nestedSchmidtHigherFlow_zero_outer {Outer : Type*}
    {Inner : Outer → Type*} {Form : Type*}
    [Fintype Outer] [∀ β : Outer, Fintype (Inner β)]
    [AddCommGroup Form] [Module ℝ Form]
    (S : NestedSchmidtHigherFlowData Outer Inner Form)
    (hzero : ∀ β : Outer, S.outerWeightDerivative β = 0) :
    nestedSchmidtHigherFlow S = 0 := by
  unfold nestedSchmidtHigherFlow
  simp [hzero]

/-- If the inner Schmidt weights are locally constant in every sector, the
nested flow vanishes. -/
lemma nestedSchmidtHigherFlow_zero_inner {Outer : Type*}
    {Inner : Outer → Type*} {Form : Type*}
    [Fintype Outer] [∀ β : Outer, Fintype (Inner β)]
    [AddCommGroup Form] [Module ℝ Form]
    (S : NestedSchmidtHigherFlowData Outer Inner Form)
    (hzero : ∀ β : Outer, ∀ α : Inner β, S.innerWeightDerivative β α = 0) :
    nestedSchmidtHigherFlow S = 0 := by
  unfold nestedSchmidtHigherFlow
  simp [hzero]

/-- The three-region Appendix-C construction is the `d=2` case, hence a
4-form in the higher-Berry degree convention. -/
lemma nestedSchmidtHigherFlow_degree_two_dimensional :
    higherBerryFormDegree 2 = 4 := rfl


/-- A higher-Berry period witness: the normalized period is an integer.  This
is the HBC analog of the TKNN normalized Berry-curvature integral. -/
structure HigherBerryPeriodWitness where
  period : ℝ
  invariant : ℤ
  invariant_eq_normalized_period :
    (invariant : ℝ) = (1 / (2 * Real.pi)) * period

/-- The exactly solvable Sommer-Wen-Vishwanath pump has invariant `1`. -/
def exactSolvableHigherBerryWitness : HigherBerryPeriodWitness where
  period := exactSolvableHBCIntegral
  invariant := 1
  invariant_eq_normalized_period := by
    rw [exactSolvableHBCIntegral_eq_two_pi]
    field_simp [Real.pi_ne_zero]
    norm_num

/-- Normalized form of the exactly solvable quantization statement:
`(1/2π)∫Ω^(3)=1`. -/
lemma exactSolvableHBC_normalizedPeriod_eq_one :
    (1 / (2 * Real.pi)) * exactSolvableHBCIntegral = 1 := by
  rw [exactSolvableHBCIntegral_eq_two_pi]
  field_simp [Real.pi_ne_zero]

/-- Bridge to the existing TKNN layer: if a higher-Berry period is the same
period as a TKNN Berry-curvature integral, the HBC integer equals the TKNN
Chern number. -/
lemma higherBerryInvariant_eq_tknn_chern_of_same_period
    {MBZ : Type*} [MeasurableSpace MBZ]
    (H : HigherBerryPeriodWitness) (T : TKNNBerryCurvatureWitness MBZ)
    (hperiod : H.period = ∫ k, T.berryCurvature k ∂ T.μ) :
    H.invariant = T.chernNumber := by
  have hcast : (H.invariant : ℝ) = (T.chernNumber : ℝ) := by
    calc
      (H.invariant : ℝ)
          = (1 / (2 * Real.pi)) * H.period :=
            H.invariant_eq_normalized_period
      _ = (1 / (2 * Real.pi)) * ∫ k, T.berryCurvature k ∂ T.μ := by
            rw [hperiod]
      _ = (T.chernNumber : ℝ) :=
            T.chern_eq_normalized_integral.symm
  exact Int.cast_injective hcast

end Physlib.QuantumMechanics.ComplexAction.HigherBerryCurvatureMPS

end
