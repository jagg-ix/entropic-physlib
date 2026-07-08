/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiLusanna
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.CrossSphere
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly
public import Physlib.Relativity.Special.HyperbolicBoost

/-!
# Two metric invariants: the Levi-Civita area defect and the Lusanna tetrad proper separation

Links the Levi-Civita cross-sphere area defect (`LeviCivita.CrossSphere`, `crossSphereDefect =
‖ξ × η‖²`) to the Lusanna tetrad proper separation (`CanonicalTetradGravity.ComptonVacuumBell`,
`properSeparationSq = xᵀ g x`, `g = EᵀηE`) — the two **metric-gauge-invariant quadratic-form scalars** of
the geometry.

Both are scalars built from the metric that are invariant under the metric-preserving gauge group:

* the **Lusanna proper separation** `xᵀ g x` is invariant under the local Lorentz gauge `E ↦ ΛE`,
  `Λ ∈ SO(1,3)` (`properSeparationSq_lorentz_gauge`) — the `𝔰𝔬(1,3)` frame freedom is pure inertial gauge;
* the **Levi-Civita cross-sphere defect** `‖ξ × η‖² = ‖ξ‖²‖η‖² − ⟨ξ,η⟩²` (the Lagrange/Binet–Cauchy form,
  `crossProduct_normSq_lagrange`) is invariant under any inner-product-preserving (orthogonal / rotation)
  map `R` (`crossSphereDefect_inner_invariant`) — the spatial-rotation `SO(3) ⊂ SO(1,3)` face of the same
  metric invariance, because the defect is built from the inner product `⟨·,·⟩` that `R` preserves.

So the Levi-Civita area defect and the tetrad proper length are both gauge-invariant geometric scalars:
the area under spatial rotations, the length under the full Lorentz gauge
(`leviCivita_tetrad_gauge_invariants`).

**General-covariance reading (§C).** The proper separation is the flat Minkowski interval *referred to
arbitrary co-ordinates*: `xᵀ g x = xᵀ (coordCongruence E η) x` (`properSeparationSq_eq_coordCongruence`,
`LeviCivita.ArbitraryCoordinates`), the cotetrad `E` playing the coordinate Jacobian taking the local
Minkowski frame to the arbitrary one. Its Lorentz-gauge invariance is then the statement that the metric is
a **fixed point of the Lorentz congruence** `coordCongruence (ΛE) η = coordCongruence E η`
(`properSeparation_coordCongruence_lorentz_invariant`): the `𝔰𝔬(1,3)` frame freedom is the Lorentz subgroup
of arbitrary coordinate changes that leaves the flat metric `η` fixed.

**Fermion-double-copy reading (§D).** The de la Cruz fermion double-copy sector supplies gravity-only matter
states whose computational QCD amplitudes enter through the BCJ/KLT kernel, but whose physical structure has
no gauge interaction. This file links that sector to the tetrad-invariant geometry: the KLT pole-cancellation
identities and the four-spin nonrelativistic cross-section factor can be transported alongside the
Levi-Civita/Lusanna metric invariants without changing the Lorentz-gauge-invariant proper separation.

* **§A — the cross-sphere defect is an inner-product (rotation) invariant**
  (`crossSphereDefect_inner_invariant`).
* **§B — the assembly** (`leviCivita_tetrad_gauge_invariants`).
* **§C — the proper separation as the flat interval in arbitrary co-ordinates**
  (`properSeparationSq_eq_coordCongruence`, `properSeparation_coordCongruence_lorentz_invariant`,
  `leviCivita_tetrad_gauge_invariants_coordCongruence`).
* **§D — de la Cruz fermion double copies inside the tetrad-invariant gravity sector**
  (`deLaCruz_KLT_pole_cancellations_with_tetrad_invariance`,
  `deLaCruz_fermionDoubleCopy_tetrad_invariant_link`).

## References

* structures: `LeviCivita.CrossSphere` (`crossSphereDefect`, `crossProduct_normSq_lagrange`),
  `Hopf.DualSphereFiberDecomposition` (`crossSphereDefect_lagrange`, `sphereInner`, `sphereNormSq`),
  `CanonicalTetradGravity.ComptonVacuumBell` (`properSeparationSq`, `properSeparationSq_lorentz_gauge`),
  `LeviCivita.ArbitraryCoordinates` (`coordCongruence`, `tetradMetric_eq_coordCongruence`),
  `BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly` (`oneFermionPair_kernel_cancels_double_poles`,
  `twoFermionPair_kernel_cancels_double_pole`, `gravityOnlyMatterFromAmplitude_noGauge`,
  `deLaCruz_nonrel_crossSection_eq_four_rutherford`).

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiLusanna
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DeLaCruzFermionDoubleCopyGravityOnly
open Physlib.Relativity.Special
open Matrix

/-! ## §Regge — finite Regge action and tetrad/connection structures

**Reference.** R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385
(1975) [`Sorkin:1975ah`]. The Sorkin material in this file:

* **Sec. II A** (the metric thatch) — `FourSimplexMetricNet` (`localLengthSq`, `cellMetric`,
  `cellMetricFromThatch_reconstructs_lengths`/`_unique`, the `−+++` signature, interface gluing);
* **Sec. II B** (the defect of a bone) — the bone circulator, holding the bone's `2`-plane fixed
  (**Fig. 1**, parallel transport around a bone; the three cases of **Fig. 2**): `planeRotation` /
  `boneRotationCirculator` (timelike, rotation `θ`), `planeBoost` / `boneBoostCirculator`
  (spacelike, boost `η`), `nullRotation` (null, `Λ(λ)=1+λV+½λ²V²`, Appendix A);
  `regularTetrahedronVertexDefect`;
* **Sec. II C** (the action) — the smoothed-cusp curvature density `R√(−g)=2(e^λ)''`
  (`hasDerivAt_expLambda_second`), `cuspActionPerArea_eq_defect` (`−½∫∫R√(−g)=θ`),
  `cuspAction_total` (`S=θA`), and Eq. (1) `sorkinReggeAction = Σ_b η(b)A(b)`;
* **Sec. II D** (the thatch equations) — the Schläfli reduction `δS=Σ η δA`
  (`fullFirstVariation_eq_reduced_of_schlaefli`), the area derivative
  `∂A/∂l_ij²=(l²−l²−l²)/(16A)` (`hasDerivAt_sorkinBoneArea`, Eq. (2)→(3)), Eq. (2)
  `G(ij)=∂S_ℓ/∂l_ij²` (`hasDerivAt_reggeAction_leg`), and the equations Eq. (3)/(4)
  (`sorkinEinsteinThatch`, `VacuumThatchEquations`, `SourcedThatchEquations`);
* **Sec. II E** (dimensional examples) — 3D `G(ij)=η(ij)` (`sorkinEinsteinThatch_threeDim`) and
  the vacuum-iff-flat criterion; 2D `G≡0` (`sorkinEinsteinThatch_twoDim_vanishes`) with the action
  topological (`hasDerivAt_reggeAction_twoDim`, Gauss–Bonnet);
* **Sec. II F** (source term) — energy-momentum concentrated in the legs
  (`sourced_matter_supported_on_incident_legs`, `G(ij)=0` outside the `1`-simplices);
* **Sec. II G** (coordinate invariance) — gauge freedom only in the flat-space limit
  (`flatSpace_vacuum_gauge_freedom`; **Fig. 3**, the soap-film uniqueness argument).
-/

/-- Regge action data on a finite set of bones: a bone measure and a deficit angle. -/
structure ReggeActionData (Bone : Type*) where
  measure : Bone -> ℝ
  deficit : Bone -> ℝ

/-- The Regge action `S_R = sum_bone measure(bone) * deficit(bone)`. -/
noncomputable def reggeAction {Bone : Type*} [Fintype Bone]
    (D : ReggeActionData Bone) : ℝ :=
  ∑ bone : Bone, D.measure bone * D.deficit bone

@[simp] theorem reggeAction_empty {Bone : Type*} [Fintype Bone] [IsEmpty Bone]
    (D : ReggeActionData Bone) :
    reggeAction D = 0 := by
  simp [reggeAction]

@[simp] theorem reggeAction_zero_deficit {Bone : Type*} [Fintype Bone]
    (measure : Bone -> ℝ) :
    reggeAction ({ measure := measure, deficit := fun _ => 0 } : ReggeActionData Bone) = 0 := by
  simp [reggeAction]

@[simp] theorem reggeAction_unit (D : ReggeActionData PUnit) :
    reggeAction D = D.measure PUnit.unit * D.deficit PUnit.unit := by
  simp [reggeAction]

/-- If the tetrad/connection deficit angles agree bonewise with the Regge deficits,
the two finite Regge action sums agree. -/
theorem reggeAction_eq_of_deficit_agreement {Bone : Type*} [Fintype Bone]
    (measure : Bone -> ℝ) (deficit tetradDeficit : Bone -> ℝ)
    (h : ∀ bone : Bone, tetradDeficit bone = deficit bone) :
    reggeAction ({ measure := measure, deficit := tetradDeficit } : ReggeActionData Bone)
      = reggeAction ({ measure := measure, deficit := deficit } : ReggeActionData Bone) := by
  simp [reggeAction, h]

/-- A discrete tetrad assignment: every link has a vector in each local simplex frame,
and one simplex is selected as the link's referred/simplex-local representative. -/
structure DiscreteTetrad (Simplex Link : Type*) where
  linkVector : Link -> Simplex -> Fin 4 -> ℝ
  referredSimplex : Link -> Simplex

/-- The vector of a link in its selected simplex frame. -/
def DiscreteTetrad.referredVector {Simplex Link : Type*}
    (T : DiscreteTetrad Simplex Link) (link : Link) : Fin 4 -> ℝ :=
  T.linkVector link (T.referredSimplex link)

/-- The bivector generated by two link vectors, `u ^ v`, represented as the
antisymmetric matrix `u_a v_b - u_b v_a`. -/
def linkBivector (u v : Fin 4 -> ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun a b => u a * v b - u b * v a)

/-- The bivector of a pair of links inside a chosen simplex frame. -/
def DiscreteTetrad.bivectorIn {Simplex Link : Type*}
    (T : DiscreteTetrad Simplex Link) (sigma : Simplex) (linkA linkB : Link) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  linkBivector (T.linkVector linkA sigma) (T.linkVector linkB sigma)

/-- A link-pair bivector is antisymmetric. -/
theorem linkBivector_antisymm (u v : Fin 4 -> ℝ) :
    (linkBivector u v)ᵀ = -(linkBivector u v) := by
  ext a b
  simp [linkBivector]

/-- Swapping the two generating link vectors reverses the bivector orientation. -/
theorem linkBivector_swap (u v : Fin 4 -> ℝ) :
    linkBivector v u = - linkBivector u v := by
  ext a b
  simp [linkBivector]
  ring

@[simp] theorem linkBivector_self (u : Fin 4 -> ℝ) :
    linkBivector u u = 0 := by
  ext a b
  simp [linkBivector]
  ring

/-- Closure of the oriented edge vectors around a triangle. -/
def EdgeVectorClosure {Edge : Type*} [Fintype Edge] (edgeVector : Edge -> Fin 4 -> ℝ) : Prop :=
  ∑ edge : Edge, edgeVector edge = 0

/-- Closure of oriented bivectors over the boundary of a tetrahedron. -/
def BivectorClosure {Face : Type*} [Fintype Face]
    (faceBivector : Face -> Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∑ face : Face, faceBivector face = 0

/-- A pair of opposite edge vectors closes. -/
theorem edgeVectorClosure_pair (u : Fin 4 -> ℝ) :
    EdgeVectorClosure (fun i : Fin 2 => if i = 0 then u else -u) := by
  ext a
  simp [Fin.sum_univ_two]

/-- A pair of opposite bivectors closes. -/
theorem bivectorClosure_pair (B : Matrix (Fin 4) (Fin 4) ℝ) :
    BivectorClosure (fun i : Fin 2 => if i = 0 then B else -B) := by
  ext a b
  simp [Fin.sum_univ_two]

/-- Orientation of a face in a curvature product. -/
inductive OrientationSign where
  | forward
  | backward
deriving DecidableEq, Repr

namespace OrientationSign

/-- Convert an orientation sign to the exponent `+1` or `-1`. -/
def exponent : OrientationSign -> ℤ
  | forward => 1
  | backward => -1

@[simp] theorem exponent_forward : exponent forward = 1 := rfl
@[simp] theorem exponent_backward : exponent backward = -1 := rfl

end OrientationSign

/-- The oriented connection factor: `Omega` for forward orientation and
`Omega^{-1}` for backward orientation. -/
def orientedFactor {G : Type*} [Group G] : OrientationSign -> G -> G
  | OrientationSign.forward, g => g
  | OrientationSign.backward, g => g⁻¹

@[simp] theorem orientedFactor_forward {G : Type*} [Group G] (g : G) :
    orientedFactor OrientationSign.forward g = g := rfl

@[simp] theorem orientedFactor_backward {G : Type*} [Group G] (g : G) :
    orientedFactor OrientationSign.backward g = g⁻¹ := rfl

/-- Curvature around a bone: ordered product of oriented connection factors. -/
def curvatureProduct {G : Type*} [Group G] (path : List (OrientationSign × G)) : G :=
  path.foldr (fun entry acc => orientedFactor entry.1 entry.2 * acc) 1

@[simp] theorem curvatureProduct_nil {G : Type*} [Group G] :
    curvatureProduct ([] : List (OrientationSign × G)) = 1 := rfl

@[simp] theorem curvatureProduct_cons {G : Type*} [Group G]
    (entry : OrientationSign × G) (path : List (OrientationSign × G)) :
    curvatureProduct (entry :: path) = orientedFactor entry.1 entry.2 * curvatureProduct path := rfl

@[simp] theorem curvatureProduct_single_forward {G : Type*} [Group G] (g : G) :
    curvatureProduct [(OrientationSign.forward, g)] = g := by
  simp [curvatureProduct]

@[simp] theorem curvatureProduct_single_backward {G : Type*} [Group G] (g : G) :
    curvatureProduct [(OrientationSign.backward, g)] = g⁻¹ := by
  simp [curvatureProduct]

/-- A four-dimensional discrete connection encoded in oriented tetrahedral faces,
with every transport matrix orthogonal in the Euclidean frame. -/
structure ReggeConnection4 (Face : Type*) where
  Omega : Face -> Matrix (Fin 4) (Fin 4) ℝ
  orthogonal : ∀ face : Face, (Omega face)ᵀ * Omega face = 1

/-- A connection matrix transports one local link vector to another. -/
def TransportsVector (Omega : Matrix (Fin 4) (Fin 4) ℝ) (source target : Fin 4 -> ℝ) : Prop :=
  Omega *ᵥ source = target

/-- Curvature fixes an edge vector, the `n=3` condition `(R-1)T = 0`. -/
def CurvatureFixesVector (R : Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 -> ℝ) : Prop :=
  R *ᵥ T = T

/-- Curvature fixes a bivector, the `n=4` condition that the bone bivector is
not rotated by the curvature. -/
def CurvatureFixesBivector (R V : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  R * V * Rᵀ = V

@[simp] theorem identity_fixes_vector (T : Fin 4 -> ℝ) :
    CurvatureFixesVector 1 T := by
  simp [CurvatureFixesVector]

@[simp] theorem identity_fixes_bivector (V : Matrix (Fin 4) (Fin 4) ℝ) :
    CurvatureFixesBivector 1 V := by
  simp [CurvatureFixesBivector]

/-- A Hodge-star structure on a real vector space of bivectors, with `star^2 = 1`. -/
structure HodgeInvolution (Biv : Type*) [AddCommGroup Biv] [Module ℝ Biv] where
  star : Biv -> Biv
  map_add : ∀ A B : Biv, star (A + B) = star A + star B
  map_smul : ∀ (c : ℝ) (B : Biv), star (c • B) = c • star B
  involutive : ∀ B : Biv, star (star B) = B

variable {Biv : Type*} [AddCommGroup Biv] [Module ℝ Biv]

namespace HodgeInvolution

theorem map_neg (H : HodgeInvolution Biv) (B : Biv) :
    H.star (-B) = -H.star B := by
  simpa using H.map_smul (-1 : ℝ) B

theorem map_sub (H : HodgeInvolution Biv) (A B : Biv) :
    H.star (A - B) = H.star A - H.star B := by
  rw [sub_eq_add_neg, H.map_add, H.map_neg, sub_eq_add_neg]

end HodgeInvolution

/-- The self-dual projection `B_+ = (B + *B)/2`. -/
noncomputable def selfDualPart (H : HodgeInvolution Biv) (B : Biv) : Biv :=
  (1 / 2 : ℝ) • (B + H.star B)

/-- The anti-self-dual projection `B_- = (B - *B)/2`. -/
noncomputable def antiSelfDualPart (H : HodgeInvolution Biv) (B : Biv) : Biv :=
  (1 / 2 : ℝ) • (B - H.star B)

/-- The self-dual projection is fixed by the Hodge star. -/
theorem star_selfDualPart (H : HodgeInvolution Biv) (B : Biv) :
    H.star (selfDualPart H B) = selfDualPart H B := by
  unfold selfDualPart
  rw [H.map_smul, H.map_add, H.involutive, add_comm]

/-- The anti-self-dual projection changes sign under the Hodge star. -/
theorem star_antiSelfDualPart (H : HodgeInvolution Biv) (B : Biv) :
    H.star (antiSelfDualPart H B) = - antiSelfDualPart H B := by
  unfold antiSelfDualPart
  rw [H.map_smul, HodgeInvolution.map_sub, H.involutive]
  module

/-- The two projections reconstruct the original bivector. -/
theorem selfDualPart_add_antiSelfDualPart (H : HodgeInvolution Biv) (B : Biv) :
    selfDualPart H B + antiSelfDualPart H B = B := by
  rw [selfDualPart, antiSelfDualPart]
  module

/-- The self-dual action-half statement, isolated as the exact algebraic
consequence of the hypothesis `S_+ = S/2`. -/
structure SelfDualReggeAction where
  fullAction : ℝ
  selfDualAction : ℝ
  action_half : selfDualAction = fullAction / 2

/-- If the self-dual action is half the full Regge action, twice it is the full action. -/
theorem twice_selfDualAction_eq_full (A : SelfDualReggeAction) :
    2 * A.selfDualAction = A.fullAction := by
  rw [A.action_half]
  ring

/-- The tetrad/connection Regge representation is equivalent to ordinary Regge
calculus on a finite bone set when the finite actions agree and the deficits
agree bonewise. -/
structure ReggeTetradEquivalence (Bone : Type*) [Fintype Bone] where
  ordinary : ReggeActionData Bone
  tetrad : ReggeActionData Bone
  deficits_agree : ∀ bone : Bone, tetrad.deficit bone = ordinary.deficit bone
  actions_agree : reggeAction tetrad = reggeAction ordinary

/-- Build the equivalence package when the two formulations use the same bone
measures and have equal deficits. -/
noncomputable def reggeTetradEquivalence_of_deficits {Bone : Type*} [Fintype Bone]
    (measure : Bone -> ℝ) (ordinaryDeficit tetradDeficit : Bone -> ℝ)
    (h : ∀ bone : Bone, tetradDeficit bone = ordinaryDeficit bone) :
    ReggeTetradEquivalence Bone where
  ordinary := { measure := measure, deficit := ordinaryDeficit }
  tetrad := { measure := measure, deficit := tetradDeficit }
  deficits_agree := h
  actions_agree := reggeAction_eq_of_deficit_agreement measure ordinaryDeficit tetradDeficit h

/-- The tetrad connection lives in the same Lorentz algebra structure already used
by the repo's Jacobi-Ricci-Bianchi/Lusanna tetrad bridge. -/
theorem regge_tetrad_connection_lorentz_link {d : ℕ}
    (T : TetradConnection (Fin 1 ⊕ Fin d)) (c : Fin 1 ⊕ Fin d)
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    (connMatrix T c)ᵀ = -(connMatrix T c)
      ∧ IsLorentzAlg (minkowskiMatrix * connMatrix T c)
      ∧ Eᵀ * ((minkowskiMatrix * connMatrix T c)ᵀ * minkowskiMatrix
            + minkowskiMatrix * (minkowskiMatrix * connMatrix T c)) * E = 0 :=
  tetrad_connection_lorentz_valued T c E

/-- Backwards-compatible theorem name for the Khatsymovsky paper bridge, now
owned by the Levi-Civita/tetrad invariant module instead of a standalone file. -/
theorem khatsymovsky_tetrad_connection_lorentz_link {d : ℕ}
    (T : TetradConnection (Fin 1 ⊕ Fin d)) (c : Fin 1 ⊕ Fin d)
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    (connMatrix T c)ᵀ = -(connMatrix T c)
      ∧ IsLorentzAlg (minkowskiMatrix * connMatrix T c)
      ∧ Eᵀ * ((minkowskiMatrix * connMatrix T c)ᵀ * minkowskiMatrix
            + minkowskiMatrix * (minkowskiMatrix * connMatrix T c)) * E = 0 :=
  regge_tetrad_connection_lorentz_link T c E

/-! ## §Sorkin-Regge — metric thatches, variations, and finite equations -/

/-- Sorkin's causal classification of a two-simplex bone. -/
inductive BoneCausalType where
  | timelike
  | spacelike
  | null
deriving DecidableEq, Repr

/-- The local action contribution of one bone: `A * theta`, `A * eta`, or `0`. -/
def boneActionContribution : BoneCausalType -> ℝ -> ℝ -> ℝ
  | BoneCausalType.timelike, area, parameter => area * parameter
  | BoneCausalType.spacelike, area, parameter => area * parameter
  | BoneCausalType.null, _, _ => 0

@[simp] theorem boneActionContribution_null (area parameter : ℝ) :
    boneActionContribution BoneCausalType.null area parameter = 0 := rfl

@[simp] theorem boneActionContribution_timelike (area theta : ℝ) :
    boneActionContribution BoneCausalType.timelike area theta = area * theta := rfl

@[simp] theorem boneActionContribution_spacelike (area eta : ℝ) :
    boneActionContribution BoneCausalType.spacelike area eta = area * eta := rfl

/-- A metric net in Sorkin's terminology: squared leg lengths are the metric thatch.

This is the minimal incidence structure used by the Regge action and thatch equations below. The
four-simplex reconstruction of the cell metric from the squared leg lengths is packaged in
`FourSimplexMetricNet`. -/
structure MetricNetData (Leg Bone Cell : Type*) where
  lengthSq : Leg -> ℝ
  legInBone : Leg -> Bone -> Prop
  boneInCell : Bone -> Cell -> Prop
  lorentzSignature : Cell -> Prop

/-! ### Sorkin Section II.A — metric nets and the metric thatch -/

/-- Local vertices of a 4-simplex, written as one base vertex plus four affine basis vertices.
This gives a concrete representative for Sorkin's cell `σ = [01234]`. -/
abbrev Simplex4Vertex := Option (Fin 4)

/-- Index type for the ten independent symmetric metric components of a constant
cell metric in four dimensions. -/
abbrev Simplex4MetricComponent := Fin 10

/-- The ten independent components of a symmetric four-dimensional metric tensor. -/
theorem simplex4MetricComponent_card : Fintype.card Simplex4MetricComponent = 10 := by
  rfl

/-- The local squared-length function on a cell is symmetric. -/
def LocalLengthSymmetric (length : Simplex4Vertex -> Simplex4Vertex -> ℝ) : Prop :=
  ∀ p q : Simplex4Vertex, length p q = length q p

/-- The local squared-length function vanishes on repeated vertices. -/
def LocalLengthZeroDiagonal (length : Simplex4Vertex -> Simplex4Vertex -> ℝ) : Prop :=
  ∀ p : Simplex4Vertex, length p p = 0

/-- The constant metric on a 4-cell reconstructed from the ten squared leg lengths.

With the base vertex at the origin and the four other vertices as affine basis vectors,
`g_ab = (l_0a^2 + l_0b^2 - l_ab^2)/2`. This is the algebraic content of Sorkin's statement that
the ten `l_ij^2` determine the ten independent components of `g_μν` in the cell. -/
noncomputable def cellMetricFromThatch
    (length : Simplex4Vertex -> Simplex4Vertex -> ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b =>
    (length none (some a) + length none (some b) - length (some a) (some b)) / 2

/-- Squared separation induced by a reconstructed cell metric on the five local vertices. -/
def cellMetricLengthSq (G : Matrix (Fin 4) (Fin 4) ℝ) :
    Simplex4Vertex -> Simplex4Vertex -> ℝ
  | none, none => 0
  | none, some a => G a a
  | some a, none => G a a
  | some a, some b => G a a + G b b - 2 * G a b

/-- The metric reconstructed from a symmetric zero-diagonal squared-length thatch reproduces
all ten squared lengths of the 4-simplex. -/
theorem cellMetricFromThatch_reconstructs_lengths
    (length : Simplex4Vertex -> Simplex4Vertex -> ℝ)
    (hsym : LocalLengthSymmetric length) (hdiag : LocalLengthZeroDiagonal length) :
    ∀ p q : Simplex4Vertex,
      cellMetricLengthSq (cellMetricFromThatch length) p q = length p q := by
  intro p q
  cases p with
  | none =>
      cases q with
      | none =>
          simpa [cellMetricLengthSq] using (hdiag none).symm
      | some a =>
          have hdiagA : length (some a) (some a) = 0 := hdiag (some a)
          simp [cellMetricLengthSq, cellMetricFromThatch, hdiagA]
  | some a =>
      cases q with
      | none =>
          have hdiagA : length (some a) (some a) = 0 := hdiag (some a)
          rw [← hsym none (some a)]
          simp [cellMetricLengthSq, cellMetricFromThatch, hdiagA]
      | some b =>
          have hdiagA : length (some a) (some a) = 0 := hdiag (some a)
          have hdiagB : length (some b) (some b) = 0 := hdiag (some b)
          simp [cellMetricLengthSq, cellMetricFromThatch, hdiagA, hdiagB]
          ring

/-- Uniqueness half of Sorkin's Section II.A reconstruction: any constant cell metric inducing
the same squared separations on the five simplex vertices is exactly the metric reconstructed
by `cellMetricFromThatch`. -/
theorem cellMetricFromThatch_unique
    (length : Simplex4Vertex -> Simplex4Vertex -> ℝ) (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hsep : ∀ p q : Simplex4Vertex, cellMetricLengthSq G p q = length p q) :
    G = cellMetricFromThatch length := by
  ext a b
  have ha : G a a = length none (some a) := by
    simpa [cellMetricLengthSq] using hsep none (some a)
  have hb : G b b = length none (some b) := by
    simpa [cellMetricLengthSq] using hsep none (some b)
  have hab : G a a + G b b - 2 * G a b = length (some a) (some b) := by
    simpa [cellMetricLengthSq] using hsep (some a) (some b)
  simp [cellMetricFromThatch]
  nlinarith

/-- A Section II metric net specialized to four-dimensional Regge cells.

Each 4-cell supplies its five local vertices and the local leg with each squared distance.
The diagonal entries are harmless placeholders set to squared length zero; genuine legs are the
off-diagonal pairs. The `cellLorentzSignature` field is Sorkin's requirement that each reconstructed
cell metric pass the `-+++` signature check. -/
structure FourSimplexMetricNet (Vertex Leg Bone Cell : Type*) extends MetricNetData Leg Bone Cell where
  cellVertex : Cell -> Simplex4Vertex -> Vertex
  cellLeg : Cell -> Simplex4Vertex -> Simplex4Vertex -> Leg
  cellLeg_symm : ∀ cell p q, cellLeg cell p q = cellLeg cell q p
  cellLeg_diag_zero : ∀ cell p, lengthSq (cellLeg cell p p) = 0
  cellLorentzSignature : ∀ cell, lorentzSignature cell

namespace FourSimplexMetricNet

/-- The local squared-length thatch of a cell. -/
def localLengthSq {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) :
    Simplex4Vertex -> Simplex4Vertex -> ℝ :=
  fun p q => N.lengthSq (N.cellLeg cell p q)

theorem localLengthSq_symmetric {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) :
    LocalLengthSymmetric (N.localLengthSq cell) := by
  intro p q
  exact congrArg N.lengthSq (N.cellLeg_symm cell p q)

theorem localLengthSq_zero_diagonal {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) :
    LocalLengthZeroDiagonal (N.localLengthSq cell) := by
  intro p
  exact N.cellLeg_diag_zero cell p

/-- The constant metric reconstructed in one 4-cell from its metric thatch. -/
noncomputable def cellMetric {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) : Matrix (Fin 4) (Fin 4) ℝ :=
  cellMetricFromThatch (N.localLengthSq cell)

/-- In every 4-cell, the reconstructed metric gives back the squared lengths assigned to the
local legs of the metric thatch. -/
theorem cellMetric_reconstructs_lengths {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) :
    ∀ p q : Simplex4Vertex,
      cellMetricLengthSq (N.cellMetric cell) p q = N.localLengthSq cell p q :=
  cellMetricFromThatch_reconstructs_lengths (N.localLengthSq cell)
    (N.localLengthSq_symmetric cell) (N.localLengthSq_zero_diagonal cell)

/-- The reconstructed cell metric satisfies the Lorentz-signature check encoded in the net. -/
theorem cellMetric_lorentzSignature {Vertex Leg Bone Cell : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cell : Cell) :
    N.lorentzSignature cell :=
  N.cellLorentzSignature cell

/-- Two adjacent cells glue metrically along an interface when their metric thatches agree on
the squared lengths of all interface vertex pairs. -/
def SharedInterfaceLengthsAgree {Vertex Leg Bone Cell I : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cellA cellB : Cell)
    (embedA embedB : I -> Simplex4Vertex) : Prop :=
  ∀ i j : I,
    N.localLengthSq cellA (embedA i) (embedA j)
      = N.localLengthSq cellB (embedB i) (embedB j)

/-- Section II gluing theorem: if the squared lengths agree on a shared interface, then the
constant metrics reconstructed in the two cells induce the same squared separations on that
interface. -/
theorem cellMetric_restriction_agree_of_shared_lengths {Vertex Leg Bone Cell I : Type*}
    (N : FourSimplexMetricNet Vertex Leg Bone Cell) (cellA cellB : Cell)
    (embedA embedB : I -> Simplex4Vertex)
    (h : N.SharedInterfaceLengthsAgree cellA cellB embedA embedB) :
    ∀ i j : I,
      cellMetricLengthSq (N.cellMetric cellA) (embedA i) (embedA j)
        = cellMetricLengthSq (N.cellMetric cellB) (embedB i) (embedB j) := by
  intro i j
  rw [N.cellMetric_reconstructs_lengths cellA, N.cellMetric_reconstructs_lengths cellB]
  exact h i j

end FourSimplexMetricNet

/-- Sorkin's finite Regge action is the finite Regge action structure with
`measure = area` and `deficit = defect`. -/
noncomputable def sorkinReggeAction {Bone : Type*} [Fintype Bone]
    (area defect : Bone -> ℝ) : ℝ :=
  reggeAction ({ measure := area, deficit := defect } : ReggeActionData Bone)

theorem sorkinReggeAction_eq_reggeAction {Bone : Type*} [Fintype Bone]
    (area defect : Bone -> ℝ) :
    sorkinReggeAction area defect
      = reggeAction ({ measure := area, deficit := defect } : ReggeActionData Bone) := rfl

@[simp] theorem sorkinReggeAction_zero_defect {Bone : Type*} [Fintype Bone]
    (area : Bone -> ℝ) :
    sorkinReggeAction area (fun _ => 0) = 0 := by
  simp [sorkinReggeAction]

/-- The quadratic Heron kernel printed by Sorkin for a bone `[ijk]`. -/
def triangleAreaKernel (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - 2 * (x * y + y * z + z * x)

/-- Numerator of Sorkin's displayed derivative of the triangle area with respect
to the squared leg length `x = l_ij^2`. -/
def triangleAreaDerivativeNumerator (x y z : ℝ) : ℝ :=
  x - y - z

/-- One finite term in the thatch equation `G(ij)`. -/
noncomputable def sorkinAreaDerivativeTerm (epsilon defect area x y z : ℝ) : ℝ :=
  epsilon * defect * (triangleAreaDerivativeNumerator x y z / (8 * area))

@[simp] theorem sorkinAreaDerivativeTerm_zero_defect
    (epsilon area x y z : ℝ) :
    sorkinAreaDerivativeTerm epsilon 0 area x y z = 0 := by
  simp [sorkinAreaDerivativeTerm]

@[simp] theorem sorkinAreaDerivativeTerm_zero_orientation
    (defect area x y z : ℝ) :
    sorkinAreaDerivativeTerm 0 defect area x y z = 0 := by
  simp [sorkinAreaDerivativeTerm]

/-- Data for the first variation of the Regge action along one leg. -/
structure ReggeFirstVariationData (Bone Leg : Type*) [Fintype Bone] where
  area : Bone -> ℝ
  defect : Bone -> ℝ
  dArea : Leg -> Bone -> ℝ
  dDefect : Leg -> Bone -> ℝ

/-- The unreduced first variation `sum_b (dA_b * eta_b + A_b * deta_b)`. -/
noncomputable def fullFirstVariation {Bone Leg : Type*} [Fintype Bone]
    (V : ReggeFirstVariationData Bone Leg) (leg : Leg) : ℝ :=
  Finset.univ.sum (fun bone : Bone =>
    (V.dArea leg bone * V.defect bone) + (V.area bone * V.dDefect leg bone)
  )

/-- The reduced first variation after the Schlaefli identity removes
the `sum A_b * deta_b` term. -/
noncomputable def reducedFirstVariation {Bone Leg : Type*} [Fintype Bone]
    (V : ReggeFirstVariationData Bone Leg) (leg : Leg) : ℝ :=
  Finset.univ.sum (fun bone : Bone => V.dArea leg bone * V.defect bone)

/-- The discrete Schlaefli identity in the form used by Sorkin Appendix B. -/
def SchlaefliIdentityForLeg {Bone Leg : Type*} [Fintype Bone]
    (V : ReggeFirstVariationData Bone Leg) (leg : Leg) : Prop :=
  Finset.univ.sum (fun bone : Bone => V.area bone * V.dDefect leg bone) = 0

/-- Under the Schlaefli identity, the Regge first variation contains only the
area-variation terms. -/
theorem fullFirstVariation_eq_reduced_of_schlaefli {Bone Leg : Type*} [Fintype Bone]
    (V : ReggeFirstVariationData Bone Leg) (leg : Leg)
    (h : SchlaefliIdentityForLeg V leg) :
    fullFirstVariation V leg = reducedFirstVariation V leg := by
  unfold SchlaefliIdentityForLeg at h
  unfold fullFirstVariation reducedFirstVariation
  rw [Finset.sum_add_distrib, h, add_zero]

/-- Finite data for Sorkin's leg equation `G(ij)`. -/
structure ThatchEquationData (Leg Bone : Type*) [Fintype Bone] where
  orientation : Bone -> ℝ
  defect : Bone -> ℝ
  incidence : Leg -> Bone -> Bool
  dArea_dLengthSq : Leg -> Bone -> ℝ

/-- Sorkin's `G(ij)`: finite sum over incident bones. -/
noncomputable def sorkinEinsteinThatch {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (leg : Leg) : ℝ :=
  ∑ bone : Bone,
    if D.incidence leg bone then
      D.orientation bone * D.defect bone * D.dArea_dLengthSq leg bone
    else 0

/-- Vacuum Regge equations: `G(ij) = 0` for every leg. -/
def VacuumThatchEquations {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) : Prop :=
  ∀ leg : Leg, sorkinEinsteinThatch D leg = 0

/-- Sourced Regge equations: `G(ij) = T(ij)`. -/
def SourcedThatchEquations {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (source : Leg -> ℝ) : Prop :=
  ∀ leg : Leg, sorkinEinsteinThatch D leg = source leg

theorem vacuumThatchEquations_iff_sourced_zero {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) :
    VacuumThatchEquations D ↔ SourcedThatchEquations D (fun _ => 0) := by
  rfl

theorem sorkinEinsteinThatch_eq_zero_of_no_incidence {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (leg : Leg)
    (h : ∀ bone : Bone, D.incidence leg bone = false) :
    sorkinEinsteinThatch D leg = 0 := by
  simp [sorkinEinsteinThatch, h]

/-- Sorkin's finite Regge action and tetrad/connection Regge action use the same
checked finite sum once their bone areas and deficits are identified. -/
theorem sorkin_regge_action_same_carrier {Bone : Type*} [Fintype Bone]
    (area defect : Bone -> ℝ) :
    sorkinReggeAction area defect
      = reggeAction ({ measure := area, deficit := defect } : ReggeActionData Bone) :=
  sorkinReggeAction_eq_reggeAction area defect

/-- Backwards-compatible theorem name for the paper-specific bridge. -/
theorem sorkin_khatsymovsky_action_same_carrier {Bone : Type*} [Fintype Bone]
    (area defect : Bone -> ℝ) :
    sorkinReggeAction area defect
      = reggeAction ({ measure := area, deficit := defect } : ReggeActionData Bone) :=
  sorkin_regge_action_same_carrier area defect

/-! ## §A — the cross-sphere defect is an inner-product (rotation) invariant -/

/-- **[The Levi-Civita area defect is a rotation invariant] `‖Rξ × Rη‖² = ‖ξ × η‖²`.** Any
inner-product-preserving (orthogonal) map `R` leaves the cross-sphere defect invariant, because the
Lagrange identity expresses it entirely through the inner product `⟨·,·⟩` that `R` preserves — the
spatial-rotation face of metric invariance. -/
theorem crossSphereDefect_inner_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (ξ η : Fin 3 → ℝ)
    (hR : ∀ a b : Fin 3 → ℝ, sphereInner (R *ᵥ a) (R *ᵥ b) = sphereInner a b) :
    crossSphereDefect (R *ᵥ ξ) (R *ᵥ η) = crossSphereDefect ξ η := by
  rw [crossSphereDefect_lagrange, crossSphereDefect_lagrange]
  simp only [sphereNormSq]
  rw [hR ξ ξ, hR η η, hR ξ η]

/-! ## §B — the two metric invariants assembled -/

/-- **[The Levi-Civita area defect and the tetrad proper length are gauge-invariant metric scalars].** For
a Lorentz frame `Λ ∈ SO(1,3)`, a cotetrad `E`, and an inner-product-preserving spatial map `R`:

* the Levi-Civita cross-sphere defect `‖ξ × η‖²` is invariant under `R` (rotations);
* the Lusanna tetrad proper separation `xᵀ g x` is invariant under the Lorentz gauge `E ↦ ΛE`.

The Levi-Civita area defect and the tetrad proper length are both gauge-invariant geometric scalars — the
area under spatial rotations `SO(3)`, the length under the full Lorentz gauge `SO(1,3)`. -/
theorem leviCivita_tetrad_gauge_invariants {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (ξ η : Fin 3 → ℝ)
    (hR : ∀ a b : Fin 3 → ℝ, sphereInner (R *ᵥ a) (R *ᵥ b) = sphereInner a b) :
    crossSphereDefect (R *ᵥ ξ) (R *ᵥ η) = crossSphereDefect ξ η
      ∧ properSeparationSq (Λ * E) x = properSeparationSq E x :=
  ⟨crossSphereDefect_inner_invariant R ξ η hR, properSeparationSq_lorentz_gauge hΛ x⟩

/-! ## §C — the proper separation as the flat interval in arbitrary co-ordinates -/

/-- **[The proper separation is the flat interval in arbitrary co-ordinates] `xᵀ g x = xᵀ (coordCongruence E η) x`.**
The Lusanna tetrad proper separation is the flat Minkowski interval `η` referred to arbitrary co-ordinates
by the cotetrad congruence `g = coordCongruence E η = EᵀηE` (`tetradMetric_eq_coordCongruence`,
`LeviCivita.ArbitraryCoordinates`) — the cotetrad `E` is the coordinate Jacobian taking the local Minkowski
frame to the arbitrary one. -/
theorem properSeparationSq_eq_coordCongruence {d : ℕ}
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq E x = x ⬝ᵥ (coordCongruence E minkowskiMatrix *ᵥ x) := by
  unfold properSeparationSq
  rw [tetradMetric_eq_coordCongruence]

/-- **[Reconstructed metric uniqueness]** If two cotetrads reconstruct the same
coordinate-congruence metric, then they determine the same proper-separation
quadratic scalar at every displacement. -/
theorem properSeparation_unique_of_reconstructed_metric {d : ℕ}
    (E E' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x : (Fin 1 ⊕ Fin d) → ℝ)
    (hmetric : coordCongruence E minkowskiMatrix = coordCongruence E' minkowskiMatrix) :
    properSeparationSq E x = properSeparationSq E' x := by
  rw [properSeparationSq_eq_coordCongruence, properSeparationSq_eq_coordCongruence, hmetric]

/-- **[The metric is a fixed point of the Lorentz congruence] `xᵀ (coordCongruence (ΛE) η) x = xᵀ (coordCongruence E η) x`.**
Read through Levi-Civita's congruence `JᵀMJ`, the proper-separation invariance under the local Lorentz gauge
`E ↦ ΛE` (`Λ ∈ SO(1,3)`) is the statement that the flat interval referred to arbitrary co-ordinates is
unchanged by the Lorentz subgroup of coordinate changes — the metric is a fixed point of the Lorentz
congruence. -/
theorem properSeparation_coordCongruence_lorentz_invariant {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) :
    x ⬝ᵥ (coordCongruence (Λ * E) minkowskiMatrix *ᵥ x)
      = x ⬝ᵥ (coordCongruence E minkowskiMatrix *ᵥ x) := by
  rw [← properSeparationSq_eq_coordCongruence, ← properSeparationSq_eq_coordCongruence]
  exact properSeparationSq_lorentz_gauge hΛ x

/-- **[The three metric invariants, assembled].** For a Lorentz frame `Λ ∈ SO(1,3)`, a cotetrad `E`, and an
inner-product-preserving spatial map `R`:

* the Levi-Civita cross-sphere defect `‖ξ × η‖²` is invariant under spatial rotations `R` (`SO(3)`);
* the tetrad proper separation `xᵀ g x` is invariant under the Lorentz gauge `E ↦ ΛE` (`SO(1,3)`);
* and that proper separation is the flat interval in arbitrary co-ordinates,
  `xᵀ (coordCongruence (ΛE) η) x = xᵀ (coordCongruence E η) x` — the metric as a fixed point of the Lorentz
  congruence (general covariance).

The Levi-Civita area defect and the tetrad proper length are gauge-invariant geometric scalars, the proper
length being the flat Minkowski interval referred to arbitrary co-ordinates by the cotetrad congruence. -/
theorem leviCivita_tetrad_gauge_invariants_coordCongruence {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (ξ η : Fin 3 → ℝ)
    (hR : ∀ a b : Fin 3 → ℝ, sphereInner (R *ᵥ a) (R *ᵥ b) = sphereInner a b) :
    crossSphereDefect (R *ᵥ ξ) (R *ᵥ η) = crossSphereDefect ξ η
      ∧ properSeparationSq (Λ * E) x = properSeparationSq E x
      ∧ x ⬝ᵥ (coordCongruence (Λ * E) minkowskiMatrix *ᵥ x)
          = x ⬝ᵥ (coordCongruence E minkowskiMatrix *ᵥ x) :=
  ⟨crossSphereDefect_inner_invariant R ξ η hR, properSeparationSq_lorentz_gauge hΛ x,
    properSeparation_coordCongruence_lorentz_invariant Λ E hΛ x⟩

/-! ## §D — de la Cruz fermion double copies inside the tetrad-invariant gravity sector -/

/-- **[KLT pole cancellation is compatible with tetrad-gauge invariance].** The de la Cruz four-point KLT
kernel identities live on the amplitude side, while the Lusanna/Levi-Civita tetrad equation lives on the
geometric side. This bridge packages them together: Lorentz-gauge changes of the cotetrad preserve the
proper separation, and the one-pair/two-pair generalized-KLT kernels simultaneously cancel one copy of the
squared gauge pole. -/
theorem deLaCruz_KLT_pole_cancellations_with_tetrad_invariance {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (s12 s23 s13 P R Rtilde : ℂ) :
    properSeparationSq (Λ * E) x = properSeparationSq E x
      ∧ (s12 * s23 / s13) * (R / (s12 * s23)) * (Rtilde / (s12 * s23))
          = R * Rtilde / (s13 * s12 * s23)
      ∧ P * (R / P) * (Rtilde / P) = R * Rtilde / P :=
  ⟨properSeparationSq_lorentz_gauge hΛ x,
    oneFermionPair_kernel_cancels_double_poles s12 s23 s13 R Rtilde,
    twoFermionPair_kernel_cancels_double_pole P R Rtilde⟩

/-- **[Fermion double-copy matter is a tetrad-invariant, gravity-only source].** This assembles the new
de la Cruz formalization with the Levi-Civita/Lusanna invariant layer:

* the cross-sphere defect is invariant under spatial inner-product symmetries;
* the tetrad proper separation and its coordinate-congruence form are invariant under local Lorentz gauge;
* the double-copied fermion matter has zero physical gauge amplitude;
* the double-copy fermion spin labels have cardinality four;
* the all-spin nonrelativistic cross section is four times the gravitational Rutherford value.

This is the formal repo link saying that the new fermion double-copy matter structure can be used as a
gravity-only source in the already-existing tetrad-invariant geometric sector. -/
theorem deLaCruz_fermionDoubleCopy_tetrad_invariant_link {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) (Rmat : Matrix (Fin 3) (Fin 3) ℝ) (ξ η : Fin 3 → ℝ)
    (hR : ∀ a b : Fin 3 → ℝ, sphereInner (Rmat *ᵥ a) (Rmat *ᵥ b) = sphereInner a b)
    (A Atilde M : ℂ) (GN m mPrime Ekin z : ℝ) (hEkin : Ekin ≠ 0) (hz : z + 1 ≠ 0) :
    crossSphereDefect (Rmat *ᵥ ξ) (Rmat *ᵥ η) = crossSphereDefect ξ η
      ∧ properSeparationSq (Λ * E) x = properSeparationSq E x
      ∧ x ⬝ᵥ (coordCongruence (Λ * E) minkowskiMatrix *ᵥ x)
          = x ⬝ᵥ (coordCongruence E minkowskiMatrix *ᵥ x)
      ∧ (gravityOnlyMatterFromAmplitude A Atilde M).physicalGaugeAmplitude = 0
      ∧ Fintype.card FermionDoubleCopySpinState = 4
      ∧ deLaCruzNonrelCrossSection GN m mPrime Ekin z
          = 4 * gravitationalRutherfordCrossSection GN m mPrime Ekin z :=
  ⟨crossSphereDefect_inner_invariant Rmat ξ η hR, properSeparationSq_lorentz_gauge hΛ x,
    properSeparation_coordCongruence_lorentz_invariant Λ E hΛ x,
    gravityOnlyMatterFromAmplitude_noGauge A Atilde M, fermionDoubleCopy_spinState_card,
    deLaCruz_nonrel_crossSection_eq_four_rutherford GN m mPrime Ekin z hEkin hz⟩

/-! ## §S — Sorkin (1975), Phys. Rev. D **12**, 385: analytic content of the thatch equations

The algebraic skeleton (`reggeAction`, `triangleAreaKernel = [[ijk]]`, the Schläfli
identity `SchlaefliIdentityForLeg`, and the leg equation `sorkinEinsteinThatch = G(ij)`)
is developed above. Here we add the analytic content of the paper: the bone area as the
square root of the Heron kernel (Sec. II D), its derivative with respect to a squared leg
length (the step from Eq. (2) to Eq. (3)), the two- and three-dimensional reductions
(Sec. II E), and the null-bone circulator `Λ(λ) = 1 + λV + ½λ²V²` (Appendix A). -/

/-- **Sorkin's bone area** `A(ijk) = ¼ [[ijk]]^{1/2}` (Sec. II D), in the squared leg
lengths `x = l_ij²`, `y = l_jk²`, `z = l_ki²`. -/
noncomputable def sorkinBoneArea (x y z : ℝ) : ℝ := Real.sqrt (triangleAreaKernel x y z) / 4

/-- `16 A² = [[ijk]]`: the bone area squares to the Heron kernel (Heron's formula in
squared-length variables), for a bone with `[[ijk]] ≥ 0` (a spacelike bone). -/
theorem sorkinBoneArea_sq {x y z : ℝ} (h : 0 ≤ triangleAreaKernel x y z) :
    16 * sorkinBoneArea x y z ^ 2 = triangleAreaKernel x y z := by
  unfold sorkinBoneArea; rw [div_pow, Real.sq_sqrt h]; ring

/-- A bone with strictly positive Heron kernel has strictly positive area. -/
theorem sorkinBoneArea_pos {x y z : ℝ} (h : 0 < triangleAreaKernel x y z) :
    0 < sorkinBoneArea x y z :=
  div_pos (Real.sqrt_pos.mpr h) (by norm_num)

/-- The Heron kernel `[[ijk]]` is a quadratic in the squared leg length `x = l_ij²` with
derivative `∂[[ijk]]/∂l_ij² = 2 (l_ij² − l_ik² − l_jk²)`. -/
theorem hasDerivAt_triangleAreaKernel (x y z : ℝ) :
    HasDerivAt (fun t => triangleAreaKernel t y z) (2 * (x - y - z)) x := by
  have hfun : (fun t => triangleAreaKernel t y z)
      = (fun t : ℝ => t ^ 2 - (2 * (y + z)) * t + (y ^ 2 + z ^ 2 - 2 * (y * z))) := by
    funext t; unfold triangleAreaKernel; ring
  rw [hfun]
  have h := (((hasDerivAt_pow 2 x).sub
      ((hasDerivAt_id x).const_mul (2 * (y + z)))).add_const (y ^ 2 + z ^ 2 - 2 * (y * z)))
  exact h.congr_deriv (by norm_num; ring)

/-- **Sorkin Eq. (2) → Eq. (3): the area derivative** `∂A/∂l_ij² = (l_ij² − l_ik² − l_jk²)/(16A)`.
Combined with `δS = Σ_b η(b) δA(b)` (the Schläfli reduction above), this is exactly the
per-bone term of the leg equation `G(ij)`. The displayed numerator is
`triangleAreaDerivativeNumerator = l_ij² − l_ik² − l_jk²`. -/
theorem hasDerivAt_sorkinBoneArea {x y z : ℝ} (h : 0 < triangleAreaKernel x y z) :
    HasDerivAt (fun t => sorkinBoneArea t y z)
      (triangleAreaDerivativeNumerator x y z / (16 * sorkinBoneArea x y z)) x := by
  have hK := hasDerivAt_triangleAreaKernel x y z
  have hsqrt := hK.sqrt (ne_of_gt h)
  have hdiv := hsqrt.div_const 4
  have hsq : Real.sqrt (triangleAreaKernel x y z) ≠ 0 := by
    simp [Real.sqrt_eq_zero', not_le.mpr h]
  exact hdiv.congr_deriv (by unfold sorkinBoneArea triangleAreaDerivativeNumerator; field_simp; ring)

/-! ### §II D — the thatch equations `G(ij) = ∂S_ℓ/∂l_ij²`

Sorkin's Sec. II D: with the Schläfli identity (`fullFirstVariation_eq_reduced_of_schlaefli`)
the variation is `δS_ℓ = Σ_b η(b) δA(b)`, so the leg equation is the derivative of the finite
Regge action with respect to one squared leg length, `G(ij) = ∂S_ℓ/∂l_ij² = Σ_b η(b) ∂A(b)/∂l_ij²`
(Eq. (2)), each bone term being `η(b) · (l_ij² − l_ik² − l_jk²)/(16 A(b))` (Eq. (3), from
`hasDerivAt_sorkinBoneArea`). This is the analytic content behind `sorkinEinsteinThatch`. -/

/-- **Sorkin Eq. (2), one bone**: the derivative of a bone's action contribution `η A` with respect
to a squared leg length is `η ∂A/∂l_ij² = η (l_ij² − l_ik² − l_jk²)/(16 A)` — reusing the proven area
derivative `hasDerivAt_sorkinBoneArea`. -/
theorem hasDerivAt_boneAction (defectVal : ℝ) {x y z : ℝ} (h : 0 < triangleAreaKernel x y z) :
    HasDerivAt (fun t => defectVal * sorkinBoneArea t y z)
      (defectVal * (triangleAreaDerivativeNumerator x y z / (16 * sorkinBoneArea x y z))) x :=
  (hasDerivAt_sorkinBoneArea h).const_mul defectVal

/-- **Sorkin Eq. (2): the thatch equation is the derivative of the Regge action along one leg**,
`G(ij) = ∂S_ℓ/∂l_ij² = Σ_b η(b) ∂A(b)/∂l_ij²`. For a finite family of bones whose areas
`A(b)` vary with the squared leg length, the derivative of `S_ℓ = Σ_b η(b) A(b)` is the bone-sum of
`η(b) ∂A(b)/∂l_ij²` — the reduced first variation, i.e. `sorkinEinsteinThatch`. -/
theorem hasDerivAt_reggeAction_leg {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℝ) (boneArea : Bone → ℝ → ℝ) (dArea : Bone → ℝ) (t : ℝ)
    (h : ∀ b, HasDerivAt (boneArea b) (dArea b) t) :
    HasDerivAt (fun s => ∑ b : Bone, defect b * boneArea b s)
      (∑ b : Bone, defect b * dArea b) t := by
  have hfun : (fun s => ∑ b : Bone, defect b * boneArea b s)
      = ∑ b : Bone, (fun s => defect b * boneArea b s) := by
    funext s; rw [Finset.sum_apply]
  rw [hfun]
  exact HasDerivAt.sum (fun b _ => (h b).const_mul (defect b))

/-- **Sorkin Sec. II E, three dimensions**: bones coincide with legs, and the leg equation
reduces to the defect itself, `G(ij) = η(ij)`. Here each leg is incident to exactly its own
bone with unit orientation and unit area-derivative. -/
theorem sorkinEinsteinThatch_threeDim {Leg : Type*} [Fintype Leg] [DecidableEq Leg]
    (D : ThatchEquationData Leg Leg)
    (hinc : ∀ l b, D.incidence l b = decide (l = b))
    (hor : ∀ b, D.orientation b = 1) (hdA : ∀ l, D.dArea_dLengthSq l l = 1) (leg : Leg) :
    sorkinEinsteinThatch D leg = D.defect leg := by
  unfold sorkinEinsteinThatch
  rw [Finset.sum_eq_single leg]
  · rw [hinc]; simp [hor, hdA]
  · intro b _ hb; rw [hinc]; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ leg) h

/-- **Sorkin Sec. II E**: in three dimensions the vacuum equations `G(ij) = 0` hold iff every
defect vanishes — i.e. iff space is flat (Einstein's equations have only trivial solutions in
three dimensions). -/
theorem vacuum_threeDim_iff_all_defect_zero {Leg : Type*} [Fintype Leg] [DecidableEq Leg]
    (D : ThatchEquationData Leg Leg)
    (hinc : ∀ l b, D.incidence l b = decide (l = b))
    (hor : ∀ b, D.orientation b = 1) (hdA : ∀ l, D.dArea_dLengthSq l l = 1) :
    VacuumThatchEquations D ↔ ∀ leg, D.defect leg = 0 := by
  unfold VacuumThatchEquations
  refine ⟨fun hV leg => ?_, fun hd leg => ?_⟩
  · rw [← sorkinEinsteinThatch_threeDim D hinc hor hdA leg]; exact hV leg
  · rw [sorkinEinsteinThatch_threeDim D hinc hor hdA leg]; exact hd leg

/-- **Sorkin Sec. II E, two dimensions**: the bones are `0`-dimensional (vertices) whose
"volume" never changes, so every area-variation vanishes and `G(ij) ≡ 0` identically
(the discrete Gauss–Bonnet statement that `S_ℓ` is topological). -/
theorem sorkinEinsteinThatch_twoDim_vanishes {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (h : ∀ l b, D.dArea_dLengthSq l b = 0) (leg : Leg) :
    sorkinEinsteinThatch D leg = 0 := by
  unfold sorkinEinsteinThatch
  apply Finset.sum_eq_zero; intro b _; split <;> simp [h]

/-- In two dimensions the vacuum equations hold identically. -/
theorem vacuum_twoDim {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (h : ∀ l b, D.dArea_dLengthSq l b = 0) :
    VacuumThatchEquations D :=
  fun leg => sorkinEinsteinThatch_twoDim_vanishes D h leg

/-- **Sorkin Sec. II E, two dimensions: the action is topological.** In two dimensions the bones are
`0`-dimensional (points) whose "volume" never changes, so every area-variation vanishes and the
Regge action is **independent of the metric thatch** — its derivative along any squared leg length
is zero. This is the discrete Gauss–Bonnet statement that `S_ℓ` depends only on the topology. -/
theorem hasDerivAt_reggeAction_twoDim {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℝ) (boneArea : Bone → ℝ → ℝ) (t : ℝ)
    (h : ∀ b, HasDerivAt (boneArea b) 0 t) :
    HasDerivAt (fun s => ∑ b : Bone, defect b * boneArea b s) 0 t := by
  have := hasDerivAt_reggeAction_leg defect boneArea (fun _ => 0) t h
  simpa using this

/-! ### §II F — the thatch equations with source term -/

/-- **Sorkin Sec. II F: energy-momentum is concentrated in the legs.** With a source term the leg
equation is `G(ij) = T(ij)` (`SourcedThatchEquations`, Eq. (4)). Since `G(ij)` vanishes outside the
`1`-simplices (where no bone is incident, `sorkinEinsteinThatch_eq_zero_of_no_incidence`), the matter
source `T(ij)` must vanish there too: energy-momentum lives on the legs even though curvature is
diffused over the bones. -/
theorem sourced_matter_supported_on_incident_legs {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (source : Leg → ℝ)
    (hS : SourcedThatchEquations D source) (leg : Leg)
    (h : ∀ b, D.incidence leg b = false) : source leg = 0 := by
  rw [← hS leg]; exact sorkinEinsteinThatch_eq_zero_of_no_incidence D leg h

/-! ### §II G — coordinate invariance: gauge freedom only in the flat-space limit

Sorkin's Sec. II G: the simplectic empty-space problem is like fitting a soap film by a polyhedron
(**Fig. 3**) — for given face connectivity the minimizing vertices are unique, so unlike the
continuum there is no coordinate-invariance ambiguity in a curved thatch solution. The one exception
is flat space, where the empty-space equations become underdetermining. -/

/-- **Sorkin Sec. II G: gauge freedom in the flat-space limit.** In flat space (all defects vanish)
the vacuum thatch equations hold for *any* metric thatch — the empty-space equations do not fix the
leg lengths, the discrete analog of coordinate/gauge freedom, which appears only in the flat-space
limit. -/
theorem flatSpace_vacuum_gauge_freedom {Leg Bone : Type*} [Fintype Bone]
    (D : ThatchEquationData Leg Bone) (h : ∀ b, D.defect b = 0) :
    VacuumThatchEquations D := by
  intro leg
  unfold sorkinEinsteinThatch
  apply Finset.sum_eq_zero
  intro b _; split <;> simp [h b]

/-- **Sorkin Appendix A: the null-bone circulator** `Λ(λ) = 1 + λV + ½λ²V²`, the general
Lorentz transformation fixing a null `2`-plane, with `V` the nilpotent generator (`V³ = 0`). -/
noncomputable def nullRotation {n : Type*} [Fintype n] [DecidableEq n]
    (lam : ℝ) (V : Matrix n n ℝ) : Matrix n n ℝ :=
  1 + lam • V + (lam ^ 2 / 2) • (V * V)

@[simp] theorem nullRotation_zero {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) : nullRotation 0 V = 1 := by simp [nullRotation]

/-- **The null circulators form a one-parameter group**, `Λ(a) Λ(b) = Λ(a+b)` (Appendix A):
here `λ` plays the role of the null "angle". The `V³` and `V⁴` cross terms drop out because
the generator is nilpotent (`V³ = 0`), leaving `½a² + ab + ½b² = ½(a+b)²` on the `V²` term. -/
theorem nullRotation_mul {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (hV : V * V * V = 0) (a b : ℝ) :
    nullRotation a V * nullRotation b V = nullRotation (a + b) V := by
  simp only [nullRotation, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, ← Matrix.mul_assoc]
  simp only [hV, Matrix.zero_mul, smul_zero, add_zero]
  match_scalars <;> ring

/-! ## §BC — Sorkin Sec. II B (the "defect" of a bone) and Sec. II C (the action)

**Sec. II B.** The defect of a bone is measured by its *circulator*: parallel transport
around a loop that links the bone once is a Lorentz transformation holding the bone's
`2`-plane fixed. Three cases arise by the character of the bone: a timelike bone gives a
**rotation** through an angle `θ` in the transverse plane, a spacelike bone a **boost** with
rapidity `η`, and a null bone the nilpotent `nullRotation` of §S. The defect is the
parameter (`θ` or `η`) of this circulator. The regular-tetrahedron cone example has vertex
defect `2π − 3(π/3) = π`.

**Sec. II C.** Smoothing the conical cusp with `g_rr = 1`, `g_φφ = e^{2λ(r)}`, the only
nonvanishing curvature gives `R = 2[λ'' + (λ')²]` and `(−g)^{1/2} = e^λ`, so the curvature
density is `R(−g)^{1/2} = 2(e^λ)''`. Integrating, `−½ ∫∫ R(−g)^{1/2} dr dφ = θ` independently
of the smoothing, and over the whole bone the action is `S = θ A`, i.e. defect × area — the
per-bone summand of `reggeAction`. -/

/-- Sorkin Sec. II B: the regular-tetrahedron cone has vertex defect `2π − 3(π/3) = π`. -/
theorem regularTetrahedronVertexDefect : 2 * Real.pi - 3 * (Real.pi / 3) = Real.pi := by ring

/-- **Timelike-bone circulator** (Sec. II B): a rotation through the defect angle `θ` in the
`2`-plane transverse to the bone, fixing the bone's plane. -/
noncomputable def planeRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

@[simp] theorem planeRotation_zero : planeRotation 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [planeRotation]

/-- The timelike circulators form a one-parameter group `R(a) R(b) = R(a+b)`. -/
theorem planeRotation_mul (a b : ℝ) : planeRotation a * planeRotation b = planeRotation (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [planeRotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/-- A bone rotation preserves the transverse Euclidean norm `x² + y²` (it is orthogonal). -/
theorem planeRotation_preserves_normSq (θ : ℝ) (v : Fin 2 → ℝ) :
    (planeRotation θ *ᵥ v) 0 ^ 2 + (planeRotation θ *ᵥ v) 1 ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [planeRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val']
  nlinarith [h, sq_nonneg (v 0), sq_nonneg (v 1)]

/-- **Spacelike-bone circulator** (Sec. II B): a boost with rapidity `η` in the `2`-plane
transverse to the bone. -/
noncomputable def planeBoost (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh η, -Real.sinh η; -Real.sinh η, Real.cosh η]

@[simp] theorem planeBoost_zero : planeBoost 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [planeBoost]

/-- The spacelike circulators form a one-parameter group `B(a) B(b) = B(a+b)`. -/
theorem planeBoost_mul (a b : ℝ) : planeBoost a * planeBoost b = planeBoost (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [planeBoost, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_add, Real.sinh_add] <;> ring

/-- **Sorkin's spacelike-bone circulator acts by the repository's rapidity boost**: its components
are `boostX` / `boostT` (`Physlib.Relativity.Special`), identifying the bone defect `η` with a
relativistic rapidity. -/
theorem planeBoost_apply_zero (η : ℝ) (v : Fin 2 → ℝ) :
    (planeBoost η *ᵥ v) 0 = boostX η (v 0) (v 1) := by
  simp [planeBoost, boostX, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val']; ring

theorem planeBoost_apply_one (η : ℝ) (v : Fin 2 → ℝ) :
    (planeBoost η *ᵥ v) 1 = boostT η (v 0) (v 1) := by
  simp [planeBoost, boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val']; ring

/-- A bone boost preserves the transverse Minkowski form `t² − z²` — reusing the rapidity boost's
`RapidityBoost.preserves_minkowski` rather than re-proving it. -/
theorem planeBoost_preserves_minkowski (η : ℝ) (v : Fin 2 → ℝ) :
    (planeBoost η *ᵥ v) 0 ^ 2 - (planeBoost η *ᵥ v) 1 ^ 2 = v 0 ^ 2 - v 1 ^ 2 := by
  rw [planeBoost_apply_zero, planeBoost_apply_one]
  exact RapidityBoost.preserves_minkowski ⟨η⟩ (v 0) (v 1)

/-! The circulator of a bone (Sorkin Sec. II B) is a `4`-dimensional Lorentz transformation that
**holds the bone's `2`-plane fixed** and acts on the transverse `2`-plane by the `planeRotation` /
`planeBoost` above: "a vector parallel to the bone remains unchanged." Coordinates are
`(t, x, y, z) = (0, 1, 2, 3)` with Minkowski form `−t² + x² + y² + z²`. -/

/-- **Timelike-bone circulator in spacetime** (Sorkin Sec. II B): the identity on the bone's `t–z`
plane (coords `0, 3`) and the rotation `R(θ)` on the transverse `x–y` plane (coords `1, 2`). -/
noncomputable def boneRotationCirculator (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, Real.cos θ, -Real.sin θ, 0; 0, Real.sin θ, Real.cos θ, 0; 0, 0, 0, 1]

@[simp] theorem boneRotationCirculator_zero : boneRotationCirculator 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [boneRotationCirculator]

/-- The timelike circulators form a one-parameter group `R(a) R(b) = R(a+b)`. -/
theorem boneRotationCirculator_mul (a b : ℝ) :
    boneRotationCirculator a * boneRotationCirculator b = boneRotationCirculator (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boneRotationCirculator, Matrix.mul_apply, Fin.sum_univ_four, Real.cos_add, Real.sin_add] <;>
    ring

/-- **A vector parallel to the (timelike) bone is unchanged**: the circulator fixes the bone's
`t–z` plane (`x = y = 0`). -/
theorem boneRotationCirculator_fixes_bone (θ : ℝ) (v : Fin 4 → ℝ) (h1 : v 1 = 0) (h2 : v 2 = 0) :
    boneRotationCirculator θ *ᵥ v = v := by
  funext i; fin_cases i <;>
    simp [boneRotationCirculator, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h1, h2]

/-- The timelike-bone circulator is a Lorentz transformation: it preserves the Minkowski form
`−t² + x² + y² + z²`. -/
theorem boneRotationCirculator_preserves_minkowski (θ : ℝ) (v : Fin 4 → ℝ) :
    -(boneRotationCirculator θ *ᵥ v) 0 ^ 2 + (boneRotationCirculator θ *ᵥ v) 1 ^ 2
        + (boneRotationCirculator θ *ᵥ v) 2 ^ 2 + (boneRotationCirculator θ *ᵥ v) 3 ^ 2
      = -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [boneRotationCirculator, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.of_apply, Matrix.cons_val']
  nlinarith [h, sq_nonneg (v 1), sq_nonneg (v 2)]

/-- **Spacelike-bone circulator in spacetime** (Sorkin Sec. II B): the identity on the bone's `x–y`
plane (coords `1, 2`) and the boost `B(η)` on the transverse `t–z` plane (coords `0, 3`). -/
noncomputable def boneBoostCirculator (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cosh η, 0, 0, -Real.sinh η; 0, 1, 0, 0; 0, 0, 1, 0; -Real.sinh η, 0, 0, Real.cosh η]

@[simp] theorem boneBoostCirculator_zero : boneBoostCirculator 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [boneBoostCirculator]

/-- The spacelike circulators form a one-parameter group `B(a) B(b) = B(a+b)`. -/
theorem boneBoostCirculator_mul (a b : ℝ) :
    boneBoostCirculator a * boneBoostCirculator b = boneBoostCirculator (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boneBoostCirculator, Matrix.mul_apply, Fin.sum_univ_four, Real.cosh_add, Real.sinh_add] <;>
    ring

/-- **A vector parallel to the (spacelike) bone is unchanged**: the circulator fixes the bone's
`x–y` plane (`t = z = 0`). -/
theorem boneBoostCirculator_fixes_bone (η : ℝ) (v : Fin 4 → ℝ) (h0 : v 0 = 0) (h3 : v 3 = 0) :
    boneBoostCirculator η *ᵥ v = v := by
  funext i; fin_cases i <;>
    simp [boneBoostCirculator, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h3]

/-- The spacetime spacelike-bone circulator acts on its transverse `t–z` plane by the repository's
rapidity boost `boostX` / `boostT`. -/
theorem boneBoostCirculator_apply_zero (η : ℝ) (v : Fin 4 → ℝ) :
    (boneBoostCirculator η *ᵥ v) 0 = boostX η (v 0) (v 3) := by
  simp [boneBoostCirculator, boostX, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.of_apply, Matrix.cons_val']; ring

theorem boneBoostCirculator_apply_three (η : ℝ) (v : Fin 4 → ℝ) :
    (boneBoostCirculator η *ᵥ v) 3 = boostT η (v 0) (v 3) := by
  simp [boneBoostCirculator, boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.of_apply, Matrix.cons_val']; ring

/-- The spacelike-bone circulator is a Lorentz transformation: it preserves the Minkowski form
`−t² + x² + y² + z²` — reusing the rapidity boost's `preserves_minkowski` on the transverse plane. -/
theorem boneBoostCirculator_preserves_minkowski (η : ℝ) (v : Fin 4 → ℝ) :
    -(boneBoostCirculator η *ᵥ v) 0 ^ 2 + (boneBoostCirculator η *ᵥ v) 1 ^ 2
        + (boneBoostCirculator η *ᵥ v) 2 ^ 2 + (boneBoostCirculator η *ᵥ v) 3 ^ 2
      = -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  have h1 : (boneBoostCirculator η *ᵥ v) 1 = v 1 := by
    simp [boneBoostCirculator, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.of_apply, Matrix.cons_val']
  have h2 : (boneBoostCirculator η *ᵥ v) 2 = v 2 := by
    simp [boneBoostCirculator, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.of_apply, Matrix.cons_val']
  rw [boneBoostCirculator_apply_zero, boneBoostCirculator_apply_three, h1, h2]
  nlinarith [RapidityBoost.preserves_minkowski (⟨η⟩ : RapidityBoost) (v 0) (v 3)]

/-- **Sorkin Sec. II C**: for the smoothed cusp metric `g_φφ = e^{2λ}`, the curvature density
factor is `(e^λ)'' = (λ'' + (λ')²) e^λ`, whence `R(−g)^{1/2} = 2(e^λ)''`. Here `lamP = λ'`
(a function) and `a2 = λ''` at the point `r`. -/
theorem hasDerivAt_expLambda_second (lam lamP : ℝ → ℝ) (r a2 : ℝ)
    (h1 : ∀ s, HasDerivAt lam (lamP s) s) (h2 : HasDerivAt lamP a2 r) :
    HasDerivAt (fun s => lamP s * Real.exp (lam s)) ((a2 + lamP r ^ 2) * Real.exp (lam r)) r := by
  have hexp : HasDerivAt (fun s => Real.exp (lam s)) (Real.exp (lam r) * lamP r) r := (h1 r).exp
  have hp := h2.mul hexp
  exact hp.congr_deriv (by ring)

/-- **Sorkin Sec. II C: the action per unit bone area equals the defect**,
`−½ ∫₀^{2π} ∫₀^∞ R(−g)^{1/2} dr dφ = −2π[(1 − θ/2π) − 1] = θ`, the boundary values of
`(e^λ)'` being `1` at `r = 0` and `1 − θ/2π` at `r = ∞`. -/
noncomputable def cuspActionPerArea (θ : ℝ) : ℝ := -2 * Real.pi * ((1 - θ / (2 * Real.pi)) - 1)

theorem cuspActionPerArea_eq_defect (θ : ℝ) : cuspActionPerArea θ = θ := by
  unfold cuspActionPerArea
  have : (2 * Real.pi) ≠ 0 := by positivity
  field_simp
  ring

/-- **Sorkin Sec. II C: the bone action is `S = θ A`** (defect × area), obtained by extending
the per-area result over the bone; this is the per-bone summand of `reggeAction`. -/
theorem cuspAction_total (θ A : ℝ) : cuspActionPerArea θ * A = θ * A := by
  rw [cuspActionPerArea_eq_defect]

/-- **Sec. II C ⟶ Eq. (1): the finite Regge action is the sum of the per-bone continuum
actions.** `S_ℓ = Σ_b A(b) η(b)` is exactly `Σ_b (−½∫∫R√(−g) over bone b)·A(b) = Σ_b θ(b) A(b)`:
each bone contributes its Sec. II C action `cuspActionPerArea(η_b)·A_b`, which by
`cuspActionPerArea_eq_defect` equals `η_b A_b`, the summand of `sorkinReggeAction`. -/
theorem sorkinReggeAction_eq_sum_cuspAction {Bone : Type*} [Fintype Bone]
    (area defect : Bone → ℝ) :
    sorkinReggeAction area defect = ∑ b : Bone, cuspActionPerArea (defect b) * area b := by
  simp only [sorkinReggeAction, reggeAction]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [cuspActionPerArea_eq_defect]; ring

/-- The same link for the abstract `reggeAction`: each bone's contribution is its Sec. II C
continuum action `cuspActionPerArea(deficit b)·measure b`. -/
theorem reggeAction_eq_sum_cuspAction {Bone : Type*} [Fintype Bone]
    (D : ReggeActionData Bone) :
    reggeAction D = ∑ b : Bone, cuspActionPerArea (D.deficit b) * D.measure b := by
  simp only [reggeAction]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [cuspActionPerArea_eq_defect]; ring

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

end
