/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry
public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
public import Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection
meta import Mathlib.Algebra.Quaternion
meta import Mathlib.Algebra.QuadraticAlgebra.Basic
public meta import Mathlib.Algebra.Lie.OfAssociative
public meta import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Clifford spinors and root-system induction

This file extracts the formal part of Pierre-Philippe Dechant's
*Clifford spinors and root system induction: H4 and the Grand Antiprism*
(arXiv:2103.07817v2) that can be connected to the present repo without
pretending that the full analytic/reflection-root-system development is already
available.  The final section does construct exact finite `H₃`/`H₄`
coordinates and the binary icosahedral group `2I` as unit quaternions over
`Q(sqrt 5)`.

The paper's reusable mathematical spine is:

* root reflections are represented by Clifford/Pin versors;
* `α` and `-α` induce the same reflection, the elementary double-cover
  quotient behind spinor geometry;
* a rank-3 root system can induce a rank-4 root system by reading its
  even Clifford spinors as `4` real coordinates;
* the `H₃ -> H₄` case is the binary-icosahedral/600-cell instance, and its
  rotation shadow is the already-formalized `A₅` icosahedral subgroup of the
  `SU(5)`/Sorkin Weyl net.

What is proved here:

* `euclideanReflect_neg`: the reflection defined by a root is unchanged by
  changing the Clifford representative's sign;
* `FiniteEuclideanRootSystem`: a concrete finite-root-system predicate with
  nonzero roots, reflection closure, and the reduced-root condition;
* the induced rank-4 system inherits reflection closure and sign quotient
  from an explicit Clifford-spinor induction certificate;
* `H3H4CliffordInductionCertificate` records the exact data still needed for
  the paper's full reflection-root-system `H₃ -> H₄` theorem: `30` roots in
  `H₃`, `120` in `H₄`, and the spinor/coordinate identification;
* `h3h4_certificate_links_to_existing_icosahedral_su5_infrastructure` links
  that certificate to the repo's existing `A₅ ⊂ S₅` and `SU(5)` Cartan
  invariance theorems.
* concrete exact coordinates over `Q(sqrt 5)` for the `30` H3 points and
  `120` H4 / binary-icosahedral unit quaternions;
* `BinaryIcosahedralGroup`, a Lean `Group` subtype closed under quaternion
  multiplication with inverse given by quaternion conjugation.

The remaining heavy construction is deliberately exposed as a
certificate, not hidden: the analytic Euclidean embedding and full
reflection-root-system proof for the Dechant `H₃ -> H₄` theorem still need to
be discharged from the concrete coordinates.
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Quaternion

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover
open PauliMatrix

/-! ## Euclidean reflection layer -/

/-- The coordinate vector carrier used for finite Euclidean root systems. -/
abbrev EuclideanVector (n : ℕ) := Fin n → ℝ

/-- The standard Euclidean dot product on `Fin n -> ℝ`. -/
def euclideanDot {n : ℕ} (x y : EuclideanVector n) : ℝ := ∑ i, x i * y i

@[simp] lemma euclideanDot_neg_right {n : ℕ} (x y : EuclideanVector n) :
    euclideanDot x (-y) = - euclideanDot x y := by
  simp [euclideanDot]

@[simp] lemma euclideanDot_neg_left {n : ℕ} (x y : EuclideanVector n) :
    euclideanDot (-x) y = - euclideanDot x y := by
  simp [euclideanDot]

@[simp] lemma euclideanDot_neg_neg {n : ℕ} (x y : EuclideanVector n) :
    euclideanDot (-x) (-y) = euclideanDot x y := by
  simp [euclideanDot]

/-- Reflection in the hyperplane orthogonal to `alpha`:
`s_alpha(x) = x - 2 (x,alpha)/(alpha,alpha) alpha`. -/
noncomputable def euclideanReflect {n : ℕ} (alpha x : EuclideanVector n) : EuclideanVector n :=
  x - (2 * euclideanDot x alpha / euclideanDot alpha alpha) • alpha

/-- Dechant Prop. 2.3 in coordinate form: the two Clifford representatives
`alpha` and `-alpha` define the same root reflection. -/
lemma euclideanReflect_neg {n : ℕ} (alpha x : EuclideanVector n) :
    euclideanReflect (-alpha) x = euclideanReflect alpha x := by
  funext i
  simp [euclideanReflect]
  ring

/-- A finite reduced Euclidean root system, stated only with the operations
needed by the Clifford-spinor induction bridge: finite roots, nonzero norm,
closure under all root reflections, and no nontrivial scalar multiples beyond
`±alpha`. -/
structure FiniteEuclideanRootSystem (n : ℕ) where
  roots : Finset (EuclideanVector n)
  root_nonzero : ∀ {alpha : EuclideanVector n}, alpha ∈ roots → euclideanDot alpha alpha ≠ 0
  neg_mem : ∀ {alpha : EuclideanVector n}, alpha ∈ roots → -alpha ∈ roots
  reflect_mem :
    ∀ {alpha beta : EuclideanVector n}, alpha ∈ roots → beta ∈ roots →
      euclideanReflect alpha beta ∈ roots
  reduced :
    ∀ {alpha beta : EuclideanVector n} {r : ℝ},
      alpha ∈ roots → beta ∈ roots → beta = r • alpha → beta = alpha ∨ beta = -alpha

namespace FiniteEuclideanRootSystem

variable {n : ℕ} (R : FiniteEuclideanRootSystem n)

/-- Root reflections remain in a finite root system. This is the concrete
closure property used by the rank-3-to-rank-4 induction theorem. -/
lemma reflection_closed {alpha beta : EuclideanVector n}
    (ha : alpha ∈ R.roots) (hb : beta ∈ R.roots) :
    euclideanReflect alpha beta ∈ R.roots :=
  R.reflect_mem ha hb

/-- The reflection associated to `-alpha` is the same reflection as the one
associated to `alpha`, so the root-sign ambiguity is a double-cover quotient,
not a new Weyl operation. -/
lemma reflection_sign_quotient {alpha beta : EuclideanVector n} :
    euclideanReflect (-alpha) beta = euclideanReflect alpha beta :=
  euclideanReflect_neg alpha beta

/-- If `alpha` is a root, so is `-alpha`. -/
lemma neg_root {alpha : EuclideanVector n} (ha : alpha ∈ R.roots) : -alpha ∈ R.roots :=
  R.neg_mem ha

end FiniteEuclideanRootSystem

/-! ## Clifford-spinor induction certificates -/

/-- The explicit data needed to turn a rank-3 finite root system into a rank-4
finite root system by the Dechant/Clifford-spinor mechanism.

`spinorRoots` is the `4`-coordinate image of the even Clifford spinors in
`Cl(3)`. The proof that those coordinates form a rank-4 root system is kept
as a field, because this repo does not yet contain the H3 coordinates,
quaternionic multiplication table, or binary icosahedral group needed to
instantiate the paper's main H3/H4 example. -/
structure RankThreeCliffordSpinorInduction (R3 : FiniteEuclideanRootSystem 3) where
  spinorRoots : Finset (EuclideanVector 4)
  induced : FiniteEuclideanRootSystem 4
  induced_roots_eq : induced.roots = spinorRoots
  even_spinor_coordinate_image : Prop
  even_spinor_coordinate_image_holds : even_spinor_coordinate_image

namespace RankThreeCliffordSpinorInduction

variable {R3 : FiniteEuclideanRootSystem 3} (D : RankThreeCliffordSpinorInduction R3)

/-- The rank-4 root system induced by the even-spinor coordinate image. -/
def inducedRankFourRootSystem : FiniteEuclideanRootSystem 4 := D.induced

/-- The induced `4`-D root system is exactly the recorded spinor-coordinate
image. -/
lemma induced_roots_are_spinor_roots :
    D.inducedRankFourRootSystem.roots = D.spinorRoots :=
  D.induced_roots_eq

/-- The induced spinor roots are reflection-closed. This is the checkable
rank-4 conclusion of the induction layer. -/
lemma induced_reflection_closed {alpha beta : EuclideanVector 4}
    (ha : alpha ∈ D.spinorRoots) (hb : beta ∈ D.spinorRoots) :
    euclideanReflect alpha beta ∈ D.spinorRoots := by
  rw [← D.induced_roots_eq] at ha hb ⊢
  exact D.induced.reflect_mem ha hb

/-- The induced spinor root system identifies the two Clifford signs:
`alpha` and `-alpha` induce the same rank-4 root reflection. -/
lemma induced_reflection_sign_quotient (alpha beta : EuclideanVector 4) :
    euclideanReflect (-alpha) beta = euclideanReflect alpha beta :=
  euclideanReflect_neg alpha beta

/-- The even-spinor coordinate-image obligation has been supplied by the
certificate. This theorem names the obligation so future concrete H3/H4 files
can discharge it once coordinates are available. -/
lemma even_spinor_coordinate_image_supplied :
    D.even_spinor_coordinate_image :=
  D.even_spinor_coordinate_image_holds

end RankThreeCliffordSpinorInduction

/-! ## The H3/H4 target as an explicit, non-hidden obligation -/

/-- A full certificate for the H3 -> H4 instance of the paper: H3 has `30`
roots, the induced H4 system has `120` roots, and the induced roots are the
even-spinor coordinate image. This is intentionally not an unconditional
existence theorem; the missing coordinate construction is exposed. -/
structure H3H4CliffordInductionCertificate where
  H3 : FiniteEuclideanRootSystem 3
  induction : RankThreeCliffordSpinorInduction H3
  h3_card : H3.roots.card = 30
  h4_card : induction.induced.roots.card = 120
  binary_icosahedral_lift : Prop
  binary_icosahedral_lift_holds : binary_icosahedral_lift
  h4_is_six_hundred_cell_roots : Prop
  h4_is_six_hundred_cell_roots_holds : h4_is_six_hundred_cell_roots

namespace H3H4CliffordInductionCertificate

variable (C : H3H4CliffordInductionCertificate)

/-- The induced H4 root system in the H3/H4 certificate. -/
def H4 : FiniteEuclideanRootSystem 4 := C.induction.induced

/-- The H3 root count from the certificate: `|H3| = 30`. -/
lemma h3_root_count : C.H3.roots.card = 30 :=
  C.h3_card

/-- The H4 root count from the certificate: `|H4| = 120`, the 600-cell root
count in Dechant's H3/H4 instance. -/
lemma h4_root_count : C.H4.roots.card = 120 :=
  C.h4_card

/-- The H4 roots are exactly the even-spinor coordinate image supplied by the
rank-3 Clifford induction data. -/
lemma h4_roots_are_spinor_coordinate_image :
    C.H4.roots = C.induction.spinorRoots :=
  C.induction.induced_roots_eq

/-- The induced H4 root system is reflection-closed. -/
lemma h4_reflection_closed {alpha beta : EuclideanVector 4}
    (ha : alpha ∈ C.H4.roots) (hb : beta ∈ C.H4.roots) :
    euclideanReflect alpha beta ∈ C.H4.roots :=
  C.H4.reflect_mem ha hb

/-- The spinor-sign ambiguity in the H3/H4 certificate is invisible to the
induced H4 reflection. -/
lemma h4_spinor_sign_quotient (alpha beta : EuclideanVector 4) :
    euclideanReflect (-alpha) beta = euclideanReflect alpha beta :=
  euclideanReflect_neg alpha beta

/-- The binary-icosahedral lift obligation has been supplied by the
certificate. This is where a future explicit `2I` construction should plug in. -/
lemma binary_icosahedral_lift_supplied :
    C.binary_icosahedral_lift :=
  C.binary_icosahedral_lift_holds

/-- The 600-cell/H4 identification obligation has been supplied by the
certificate. This keeps the current file honest about what is and is not yet
constructed. -/
lemma h4_is_six_hundred_cell_roots_supplied :
    C.h4_is_six_hundred_cell_roots :=
  C.h4_is_six_hundred_cell_roots_holds

end H3H4CliffordInductionCertificate

/-! ## Links to existing icosahedral, SU(5), and spinor infrastructure -/

/-- The Dechant spinor sign quotient and the repo's spin-half double cover are
the same double-cover pattern: the sign is visible on spinors but cancels in
the physical/reflection action. -/
lemma clifford_sign_quotient_matches_spin_half_double_cover
    (alpha beta : EuclideanVector 4) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    euclideanReflect (-alpha) beta = euclideanReflect alpha beta
      ∧ spinHalfRotation (2 * Real.pi) = -1
      ∧ spinHalfRotation (4 * Real.pi) = 1
      ∧ spinHalfRotation (2 * Real.pi) * X * spinHalfRotation (2 * Real.pi)
          = spinHalfRotation 0 * X * spinHalfRotation 0 := by
  refine ⟨euclideanReflect_neg alpha beta, ?_, ?_, ?_⟩
  · exact spinHalfRotation_two_pi
  · exact spinHalfRotation_four_pi
  · unfold spinHalfRotation
    simpa only [zero_add] using spinRotation_conj_two_pi (σ (Sum.inr 1)) X 0

/-- Existing `SU(5)` Cartan invariance is automatically icosahedral
invariance along the inclusion `A5 -> S5` formalized in
`IcosahedralWeylNetSymmetry`. This is the repo-level hook for the paper's
icosahedral rotation shadow: it reuses `icosahedralInclusion` and the Cartan
metric theorem instead of redefining either. -/
lemma su5_cartan_metric_invariant_under_clifford_icosahedral_shadow
    (g : IcosahedralGroup) (i j : Fin 5) :
    su5CartanMetric ((icosahedralInclusion g) i) ((icosahedralInclusion g) j)
      = su5CartanMetric i j :=
  su5CartanMetric_icosahedral_invariant g i j

/-- A complete H3/H4 certificate connects to the repo's existing icosahedral
and `SU(5)` infrastructure: H3 has `30` roots, induced H4 has `120` roots,
the sign quotient holds, `A5` sits in the `SU(5)` Weyl group with index `2`,
and the `SU(5)` Cartan metric is invariant under that icosahedral shadow. -/
lemma h3h4_certificate_links_to_existing_icosahedral_su5_infrastructure
    (C : H3H4CliffordInductionCertificate) (g : IcosahedralGroup)
    (alpha beta : EuclideanVector 4) (i j : Fin 5) :
    C.H3.roots.card = 30
      ∧ C.H4.roots.card = 120
      ∧ euclideanReflect (-alpha) beta = euclideanReflect alpha beta
      ∧ Fintype.card Su5WeylGroup = 2 * Fintype.card IcosahedralGroup
      ∧ su5CartanMetric ((icosahedralInclusion g) i) ((icosahedralInclusion g) j)
          = su5CartanMetric i j := by
  exact ⟨C.h3_card, C.h4_card, euclideanReflect_neg alpha beta,
    icosahedralGroup_index_two_in_su5Weyl,
    su5_cartan_metric_invariant_under_clifford_icosahedral_shadow g i j⟩

/-! ## Concrete H3/H4 coordinates and the binary icosahedral coordinate set

The coordinate model below supplies the paper's concrete coordinates.
Coordinates live in the exact quadratic algebra
`Q(sqrt 5)` rather than in floating-point `Real`s, so Lean can decide equality
and finite membership exactly.

`Quad5` represents `a + b sqrt(5)`.  The golden-ratio pieces used by the H3/H4
coordinates are encoded as exact pairs:

* `1/2`;
* `phi/2 = (1 + sqrt(5))/4`;
* `phi^{-1}/2 = (sqrt(5) - 1)/4`.

The H3 root coordinates have `6 + 24 = 30` points.  The H4 coordinates have
`8 + 16 + 96 = 120` points and are exactly the standard unit-quaternion
coordinates for the binary icosahedral group `2I`: permutations of
`(±1,0,0,0)`, all half-sign vectors, and even permutations of
`(0, ±1/2, ±phi/2, ±phi^{-1}/2)`.
-/

/-- Exact quadratic-coordinate scalars `a + b sqrt(5)`. -/
abbrev Quad5 := QuadraticAlgebra ℚ 5 0

/-- The quaternion algebra over `Q(sqrt 5)`, used as exact 600-cell / `2I`
coordinates. -/
abbrev H4Quaternion := ℍ[Quad5]

instance instDecidableEqQuad5 : DecidableEq Quad5 := fun x y =>
  if hre : x.re = y.re then
    if him : x.im = y.im then
      isTrue (by ext <;> assumption)
    else
      isFalse (fun h => him (congrArg QuadraticAlgebra.im h))
  else
    isFalse (fun h => hre (congrArg QuadraticAlgebra.re h))

instance instDecidableEqH4Quaternion : DecidableEq H4Quaternion := fun x y =>
  if hre : x.re = y.re then
    if hi : x.imI = y.imI then
      if hj : x.imJ = y.imJ then
        if hk : x.imK = y.imK then
          isTrue (QuaternionAlgebra.ext hre hi hj hk)
        else
          isFalse (fun h => hk (congrArg QuaternionAlgebra.imK h))
      else
        isFalse (fun h => hj (congrArg QuaternionAlgebra.imJ h))
    else
      isFalse (fun h => hi (congrArg QuaternionAlgebra.imI h))
  else
    isFalse (fun h => hre (congrArg QuaternionAlgebra.re h))

/-- Exact scalar constructor `a + b sqrt(5)`. -/
def q5 (a b : ℚ) : Quad5 := ⟨a, b⟩

/-- The exact quadratic scalar `0`. -/
def q5Zero : Quad5 := q5 0 0

/-- The exact quadratic scalar `1`. -/
def q5One : Quad5 := q5 1 0

/-- The exact quadratic scalar `1 / 2`. -/
def q5Half : Quad5 := q5 (1 / 2) 0

/-- The exact quadratic scalar `(1 + sqrt(5)) / 4`. -/
def q5PhiHalf : Quad5 := q5 (1 / 4) (1 / 4)

/-- The exact quadratic scalar `(-1 + sqrt(5)) / 4`. -/
def q5PhiInvHalf : Quad5 := q5 (-(1 / 4)) (1 / 4)

/-- Apply a Boolean sign to an exact quadratic scalar.  `true` means `+`,
`false` means `-`. -/
def signedQ5 (positive : Bool) (x : Quad5) : Quad5 :=
  if positive then x else -x

/-- Turn four exact coordinates into a quaternion. -/
def quatOfVec4 (v : Fin 4 → Quad5) : H4Quaternion :=
  ⟨v 0, v 1, v 2, v 3⟩

/-- H3 axis-root labels: `±e_i`, `i = 0,1,2`. -/
abbrev H3AxisLabel := Fin 3 × Bool

/-- The three even coordinate permutations of `Fin 3`, written explicitly to
keep coordinate enumeration computationally transparent. -/
def evenPerm3 (k : Fin 3) : Equiv.Perm (Fin 3) :=
  match k with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => Equiv.swap 0 1 * Equiv.swap 1 2
  | ⟨_, _⟩ => Equiv.swap 1 2 * Equiv.swap 0 1

/-- H3 golden-root labels: even permutations of
`(±1/2, ±phi/2, ±phi^{-1}/2)`. -/
abbrev H3GoldenLabel := Fin 3 × (Fin 3 → Bool)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete H3 coordinate labels, with `6 + 24 = 30` cases. -/
inductive H3CoordinateLabel where
  | axis : H3AxisLabel → H3CoordinateLabel
  | golden : H3GoldenLabel → H3CoordinateLabel
deriving DecidableEq, Fintype

/-- Exact H3 axis coordinates before embedding into rational real coordinates. -/
def h3AxisVecQ5 (label : H3AxisLabel) : Fin 3 → Quad5 :=
  fun j => if j = label.1 then signedQ5 label.2 q5One else q5Zero

/-- The base H3 golden coordinate tuple
`(±1/2, ±phi/2, ±phi^{-1}/2)`. -/
def h3GoldenBaseQ5 (eps : Fin 3 → Bool) (j : Fin 3) : Quad5 :=
  if j = 0 then signedQ5 (eps 0) q5Half
  else if j = 1 then signedQ5 (eps 1) q5PhiHalf
  else signedQ5 (eps 2) q5PhiInvHalf

/-- H3 golden coordinates: even coordinate permutations of the base tuple. -/
def h3GoldenVecQ5 (label : H3GoldenLabel) : Fin 3 → Quad5 :=
  fun j => h3GoldenBaseQ5 label.2 ((evenPerm3 label.1).symm j)

/-- The concrete H3 coordinate map over `Q(sqrt 5)`. -/
def h3CoordinatePointQ5 : H3CoordinateLabel → (Fin 3 → Quad5)
  | .axis label => h3AxisVecQ5 label
  | .golden label => h3GoldenVecQ5 label

/-- The concrete H3 coordinate set. -/
def h3CoordinateSetQ5 : Finset (Fin 3 → Quad5) :=
  Finset.univ.image h3CoordinatePointQ5

/-- The H3 coordinate labels have exactly `30` cases. -/
lemma h3CoordinateLabel_card : Fintype.card H3CoordinateLabel = 30 := by
  native_decide

/-- The H3 coordinate map has no duplicate coordinates. -/
lemma h3CoordinatePointQ5_injective : Function.Injective h3CoordinatePointQ5 := by
  native_decide

/-- The concrete H3 coordinate set has the expected `30` roots. -/
lemma h3CoordinateSetQ5_card : h3CoordinateSetQ5.card = 30 := by
  simp [h3CoordinateSetQ5, Finset.card_image_of_injective _ h3CoordinatePointQ5_injective,
    h3CoordinateLabel_card]

/-- H4 axis labels: the `8` points `(±1,0,0,0)` and coordinate permutations. -/
abbrev H4AxisLabel := Fin 4 × Bool

/-- H4 half-sign labels: the `16` points
`(±1/2, ±1/2, ±1/2, ±1/2)`. -/
abbrev H4HalfLabel := Fin 4 → Bool

/-- The twelve even coordinate permutations of `Fin 4`, written explicitly as
the identity, the eight 3-cycles, and the three double transpositions. -/
def evenPerm4 (k : Fin 12) : Equiv.Perm (Fin 4) :=
  match k with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => Equiv.swap 0 1 * Equiv.swap 1 2
  | ⟨2, _⟩ => Equiv.swap 1 2 * Equiv.swap 0 1
  | ⟨3, _⟩ => Equiv.swap 0 1 * Equiv.swap 1 3
  | ⟨4, _⟩ => Equiv.swap 1 3 * Equiv.swap 0 1
  | ⟨5, _⟩ => Equiv.swap 0 2 * Equiv.swap 2 3
  | ⟨6, _⟩ => Equiv.swap 2 3 * Equiv.swap 0 2
  | ⟨7, _⟩ => Equiv.swap 1 2 * Equiv.swap 2 3
  | ⟨8, _⟩ => Equiv.swap 2 3 * Equiv.swap 1 2
  | ⟨9, _⟩ => Equiv.swap 0 1 * Equiv.swap 2 3
  | ⟨10, _⟩ => Equiv.swap 0 2 * Equiv.swap 1 3
  | ⟨_, _⟩ => Equiv.swap 0 3 * Equiv.swap 1 2

/-- H4 golden labels: `12` even coordinate permutations times `8` signs. -/
abbrev H4GoldenLabel := Fin 12 × (Fin 3 → Bool)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete H4 / binary-icosahedral coordinate labels, with
`8 + 16 + 96 = 120` cases. -/
inductive BinaryIcosahedralLabel where
  | axis : H4AxisLabel → BinaryIcosahedralLabel
  | half : H4HalfLabel → BinaryIcosahedralLabel
  | golden : H4GoldenLabel → BinaryIcosahedralLabel
deriving DecidableEq, Fintype

/-- H4 axis coordinates `±e_i`. -/
def h4AxisVecQ5 (label : H4AxisLabel) : Fin 4 → Quad5 :=
  fun j => if j = label.1 then signedQ5 label.2 q5One else q5Zero

/-- H4 half-sign coordinates. -/
def h4HalfVecQ5 (eps : H4HalfLabel) : Fin 4 → Quad5 :=
  fun j => signedQ5 (eps j) q5Half

/-- The base H4 golden tuple
`(0, ±1/2, ±phi/2, ±phi^{-1}/2)`. -/
def h4GoldenBaseQ5 (eps : Fin 3 → Bool) (j : Fin 4) : Quad5 :=
  if j = 0 then q5Zero
  else if j = 1 then signedQ5 (eps 0) q5Half
  else if j = 2 then signedQ5 (eps 1) q5PhiHalf
  else signedQ5 (eps 2) q5PhiInvHalf

/-- H4 golden coordinates: even coordinate permutations of the base tuple. -/
def h4GoldenVecQ5 (label : H4GoldenLabel) : Fin 4 → Quad5 :=
  fun j => h4GoldenBaseQ5 label.2 ((evenPerm4 label.1).symm j)

/-- The concrete H4 / `2I` coordinate map into exact quaternions. -/
def binaryIcosahedralPoint : BinaryIcosahedralLabel → H4Quaternion
  | .axis label => quatOfVec4 (h4AxisVecQ5 label)
  | .half eps => quatOfVec4 (h4HalfVecQ5 eps)
  | .golden label => quatOfVec4 (h4GoldenVecQ5 label)

/-- The concrete binary icosahedral coordinate set in the unit quaternions. -/
def binaryIcosahedralCoordinates : Finset H4Quaternion :=
  Finset.univ.image binaryIcosahedralPoint

/-- The label type has exactly `120` cases. -/
lemma binaryIcosahedralLabel_card : Fintype.card BinaryIcosahedralLabel = 120 := by
  native_decide

/-- The coordinate map has no duplicate quaternion coordinates. -/
lemma binaryIcosahedralPoint_injective : Function.Injective binaryIcosahedralPoint := by
  native_decide

/-- The concrete binary-icosahedral coordinate set has cardinality `120`. -/
lemma binaryIcosahedralCoordinates_card : binaryIcosahedralCoordinates.card = 120 := by
  simp [binaryIcosahedralCoordinates,
    Finset.card_image_of_injective _ binaryIcosahedralPoint_injective,
    binaryIcosahedralLabel_card]

/-- Every labeled `2I` coordinate belongs to the coordinate set. -/
lemma binaryIcosahedralPoint_mem (label : BinaryIcosahedralLabel) :
    binaryIcosahedralPoint label ∈ binaryIcosahedralCoordinates := by
  simp [binaryIcosahedralCoordinates]

/-- Every concrete `2I` coordinate has quaternion norm-square `1`. -/
lemma binaryIcosahedralPoint_normSq_all :
    ∀ label : BinaryIcosahedralLabel,
      Quaternion.normSq (binaryIcosahedralPoint label) = (1 : Quad5) := by
  native_decide

/-- Membership form of the norm-one theorem. -/
lemma binaryIcosahedralCoordinates_normSq_one {q : H4Quaternion}
    (hq : q ∈ binaryIcosahedralCoordinates) :
    Quaternion.normSq q = (1 : Quad5) := by
  rcases Finset.mem_image.mp hq with ⟨label, _, rfl⟩
  exact binaryIcosahedralPoint_normSq_all label

/-- The identity quaternion is one of the concrete `2I` coordinates. -/
lemma binaryIcosahedralPoint_axis_zero_pos_eq_one :
    binaryIcosahedralPoint (.axis (0, true)) = (1 : H4Quaternion) := by
  native_decide

/-- The concrete `2I` coordinate set contains `1`. -/
lemma one_mem_binaryIcosahedralCoordinates :
    (1 : H4Quaternion) ∈ binaryIcosahedralCoordinates := by
  rw [← binaryIcosahedralPoint_axis_zero_pos_eq_one]
  exact binaryIcosahedralPoint_mem (.axis (0, true))

/-- The concrete `2I` coordinate set is closed under quaternion multiplication. -/
lemma binaryIcosahedral_mul_mem_all :
    ∀ a b : BinaryIcosahedralLabel,
      binaryIcosahedralPoint a * binaryIcosahedralPoint b ∈ binaryIcosahedralCoordinates := by
  native_decide

/-- Membership form of multiplication closure. -/
lemma binaryIcosahedralCoordinates_mul_mem {q r : H4Quaternion}
    (hq : q ∈ binaryIcosahedralCoordinates) (hr : r ∈ binaryIcosahedralCoordinates) :
    q * r ∈ binaryIcosahedralCoordinates := by
  rcases Finset.mem_image.mp hq with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hr with ⟨b, _, rfl⟩
  exact binaryIcosahedral_mul_mem_all a b

/-- The concrete `2I` coordinate set is closed under quaternion conjugation;
for norm-one quaternions this is inverse closure. -/
lemma binaryIcosahedral_star_mem_all :
    ∀ a : BinaryIcosahedralLabel,
      star (binaryIcosahedralPoint a) ∈ binaryIcosahedralCoordinates := by
  native_decide

/-- Membership form of conjugation/inverse closure. -/
lemma binaryIcosahedralCoordinates_star_mem {q : H4Quaternion}
    (hq : q ∈ binaryIcosahedralCoordinates) :
    star q ∈ binaryIcosahedralCoordinates := by
  rcases Finset.mem_image.mp hq with ⟨a, _, rfl⟩
  exact binaryIcosahedral_star_mem_all a

/-- The concrete `2I` coordinate set is closed under the central sign
`q ↦ -q`, the kernel element of the spin double cover. -/
lemma binaryIcosahedral_neg_mem_all :
    ∀ a : BinaryIcosahedralLabel,
      - binaryIcosahedralPoint a ∈ binaryIcosahedralCoordinates := by
  native_decide

/-- Membership form of central-sign closure. -/
lemma binaryIcosahedralCoordinates_neg_mem {q : H4Quaternion}
    (hq : q ∈ binaryIcosahedralCoordinates) :
    -q ∈ binaryIcosahedralCoordinates := by
  rcases Finset.mem_image.mp hq with ⟨a, _, rfl⟩
  exact binaryIcosahedral_neg_mem_all a

/-- The concrete binary icosahedral group `2I`, realized as the exact finite
coordinate subtype of unit quaternions over `Q(sqrt 5)`. -/
abbrev BinaryIcosahedralGroup := {q : H4Quaternion // q ∈ binaryIcosahedralCoordinates}

namespace BinaryIcosahedralGroup

instance instOne : One BinaryIcosahedralGroup :=
  ⟨⟨1, one_mem_binaryIcosahedralCoordinates⟩⟩

instance instMul : Mul BinaryIcosahedralGroup :=
  ⟨fun q r => ⟨q.1 * r.1, binaryIcosahedralCoordinates_mul_mem q.2 r.2⟩⟩

instance instInv : Inv BinaryIcosahedralGroup :=
  ⟨fun q => ⟨star q.1, binaryIcosahedralCoordinates_star_mem q.2⟩⟩

instance instNeg : Neg BinaryIcosahedralGroup :=
  ⟨fun q => ⟨-q.1, binaryIcosahedralCoordinates_neg_mem q.2⟩⟩

instance instDiv : Div BinaryIcosahedralGroup :=
  ⟨fun q r => q * r⁻¹⟩

@[simp] lemma coe_one : ((1 : BinaryIcosahedralGroup) : H4Quaternion) = 1 := rfl

@[simp] lemma coe_mul (q r : BinaryIcosahedralGroup) :
    ((q * r : BinaryIcosahedralGroup) : H4Quaternion) = q.1 * r.1 := rfl

@[simp] lemma coe_inv (q : BinaryIcosahedralGroup) :
    ((q⁻¹ : BinaryIcosahedralGroup) : H4Quaternion) = star q.1 := rfl

@[simp] lemma coe_neg (q : BinaryIcosahedralGroup) :
    ((-q : BinaryIcosahedralGroup) : H4Quaternion) = -q.1 := rfl

@[simp] lemma coe_div (q r : BinaryIcosahedralGroup) :
    ((q / r : BinaryIcosahedralGroup) : H4Quaternion) = q.1 * star r.1 := rfl

/-- Norm-one `2I` coordinates have quaternion conjugate as a right inverse. -/
lemma mul_star_self {q : H4Quaternion} (hq : q ∈ binaryIcosahedralCoordinates) :
    q * star q = (1 : H4Quaternion) := by
  simpa [binaryIcosahedralCoordinates_normSq_one hq] using Quaternion.self_mul_star q

/-- Norm-one `2I` coordinates have quaternion conjugate as a left inverse. -/
lemma star_mul_self {q : H4Quaternion} (hq : q ∈ binaryIcosahedralCoordinates) :
    star q * q = (1 : H4Quaternion) := by
  simpa [binaryIcosahedralCoordinates_normSq_one hq] using Quaternion.star_mul_self q

instance instGroup : Group BinaryIcosahedralGroup where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  div := (· / ·)
  mul_assoc q r s := Subtype.ext (mul_assoc q.1 r.1 s.1)
  one_mul q := Subtype.ext (one_mul q.1)
  mul_one q := Subtype.ext (mul_one q.1)
  inv_mul_cancel q := Subtype.ext (star_mul_self q.2)

/-- The concrete binary icosahedral group has `120` elements as a coordinate
set. -/
lemma coordinate_card : binaryIcosahedralCoordinates.card = 120 :=
  binaryIcosahedralCoordinates_card

/-- The central sign has order two on the concrete quaternion coordinates. -/
lemma centralSign_involutive (q : BinaryIcosahedralGroup) : -(-q) = q := by
  ext <;> simp

end BinaryIcosahedralGroup

/-! ## Embedding the exact `2I` coordinates into the repo's Hopf/SO(4) layer -/

/-- The `Q(sqrt 5)` scalar embedding into `ℝ`, sending the quadratic generator
to the positive real square root of `5`. -/
noncomputable def quad5ToRealAlgHom : Quad5 →ₐ[ℚ] ℝ :=
  (QuadraticAlgebra.lift (R := ℚ) (A := ℝ) (a := 5) (b := 0)
    ⟨Real.sqrt 5, by
      rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num⟩)

/-- Coordinatewise scalar extension from exact `Q(sqrt 5)` quaternions to real
quaternions. -/
noncomputable def h4QuaternionToReal (q : H4Quaternion) : ℍ[ℝ] :=
  ⟨quad5ToRealAlgHom q.re, quad5ToRealAlgHom q.imI,
    quad5ToRealAlgHom q.imJ, quad5ToRealAlgHom q.imK⟩

@[simp] lemma h4QuaternionToReal_one :
    h4QuaternionToReal (1 : H4Quaternion) = (1 : ℍ[ℝ]) := by
  ext <;> simp [h4QuaternionToReal]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma h4QuaternionToReal_mul (q r : H4Quaternion) :
    h4QuaternionToReal (q * r) = h4QuaternionToReal q * h4QuaternionToReal r := by
  ext <;> simp [h4QuaternionToReal, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma h4QuaternionToReal_star (q : H4Quaternion) :
    h4QuaternionToReal (star q) = star (h4QuaternionToReal q) := by
  ext <;> simp [h4QuaternionToReal]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma h4QuaternionToReal_neg (q : H4Quaternion) :
    h4QuaternionToReal (-q) = -h4QuaternionToReal q := by
  ext <;> simp [h4QuaternionToReal]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma h4QuaternionToReal_normSq (q : H4Quaternion) :
    Quaternion.normSq (h4QuaternionToReal q) = quad5ToRealAlgHom (Quaternion.normSq q) := by
  simp [h4QuaternionToReal, Quaternion.normSq_def']

/-- Every exact `2I` coordinate maps to a real unit quaternion, so it lies on
the real `S³` carrier used by `Hopf.QuaternionIsoclinicHopfFibration`. -/
lemma binaryIcosahedral_toReal_normSq_one {q : H4Quaternion}
    (hq : q ∈ binaryIcosahedralCoordinates) :
    Quaternion.normSq (h4QuaternionToReal q) = (1 : ℝ) := by
  rw [h4QuaternionToReal_normSq, binaryIcosahedralCoordinates_normSq_one hq]
  simp

/-- A concrete `2I` element acts by a left isoclinic rotation on real
quaternions, reusing the repo's Hopf/SO(4) norm-preservation theorem. -/
lemma binaryIcosahedralGroup_toReal_leftMul_normSq
    (g : BinaryIcosahedralGroup) (x : ℍ[ℝ]) :
    Quaternion.normSq (h4QuaternionToReal g.1 * x) = Quaternion.normSq x :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.leftMul_normSq
    (h4QuaternionToReal g.1) x (binaryIcosahedral_toReal_normSq_one g.2)

/-- A concrete `2I` element acts by a right isoclinic rotation on real
quaternions, reusing the repo's Hopf/SO(4) norm-preservation theorem. -/
lemma binaryIcosahedralGroup_toReal_rightMul_normSq
    (g : BinaryIcosahedralGroup) (x : ℍ[ℝ]) :
    Quaternion.normSq (x * h4QuaternionToReal g.1) = Quaternion.normSq x :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.rightMul_normSq
    (h4QuaternionToReal g.1) x (binaryIcosahedral_toReal_normSq_one g.2)

/-- Two concrete `2I` elements define an `SO(4)` two-sided quaternion action
`x ↦ p*x*star q`; norm preservation is exactly the existing Hopf/SO(4)
`so4Map_normSq` theorem after scalar extension from `Q(sqrt 5)` to `ℝ`. -/
lemma binaryIcosahedralGroup_toReal_so4Map_normSq
    (p q : BinaryIcosahedralGroup) (x : ℍ[ℝ]) :
    Quaternion.normSq
        (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map
          (h4QuaternionToReal p.1) (h4QuaternionToReal q.1) x)
      = Quaternion.normSq x :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map_normSq
    (h4QuaternionToReal p.1) (h4QuaternionToReal q.1) x
    (binaryIcosahedral_toReal_normSq_one p.2)
    (binaryIcosahedral_toReal_normSq_one q.2)

/-- The Hopf image of any concrete `2I` element lies on the real unit `S²`.
This links the finite 600-cell coordinates to the repo's quaternion Hopf map. -/
lemma binaryIcosahedralGroup_toReal_hopf_normSq
    (g : BinaryIcosahedralGroup) :
    Quaternion.normSq
        (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf
          (h4QuaternionToReal g.1))
      = 1 :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf_normSq
    (h4QuaternionToReal g.1) (binaryIcosahedral_toReal_normSq_one g.2)

/-- The Hopf image of any concrete `2I` element is purely imaginary, hence is
on the `S²` base rather than in the full real quaternion algebra. -/
lemma binaryIcosahedralGroup_toReal_hopf_re_zero
    (g : BinaryIcosahedralGroup) :
    (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf
      (h4QuaternionToReal g.1)).re = 0 :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf_re_zero
    (h4QuaternionToReal g.1)

/-- The real Hopf frame generated by any concrete `2I` element is a rigid
orthonormal dual-sphere frame, reusing `QuaternionHopfDualSphere`. -/
lemma binaryIcosahedralGroup_toReal_hopf_frame_orthonormal
    (g : BinaryIcosahedralGroup) :
    Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition.crossSphereDefect
        (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere.frameVec
          (h4QuaternionToReal g.1)
          Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.imagUnit)
        (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere.frameVec
          (h4QuaternionToReal g.1)
          Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere.jUnit)
      = 1 :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere.hopf_frame_orthonormal
    (h4QuaternionToReal g.1) (binaryIcosahedral_toReal_normSq_one g.2)

/-! ## The finite `2I × 2I` isoclinic action -/

/-- The finite left/right binary-icosahedral pair acting on real quaternions. -/
abbrev BinaryIcosahedralSO4Pair := BinaryIcosahedralGroup × BinaryIcosahedralGroup

/-- The concrete finite `2I × 2I` action on `ℍ[ℝ]` obtained by scalar-extending
exact `Q(sqrt 5)` coordinates and applying the existing two-sided
quaternionic `SO(4)` map. -/
noncomputable def binaryIcosahedralSO4Action
    (g : BinaryIcosahedralSO4Pair) (x : ℍ[ℝ]) : ℍ[ℝ] :=
  Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map
    (h4QuaternionToReal g.1.1) (h4QuaternionToReal g.2.1) x

/-- The identity pair acts as the identity rotation. -/
lemma binaryIcosahedralSO4Action_one (x : ℍ[ℝ]) :
    binaryIcosahedralSO4Action (1, 1) x = x := by
  simpa [binaryIcosahedralSO4Action]
    using Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map_one x

/-- Composition of concrete `2I × 2I` actions is the multiplication law
inherited from the existing `SO(4)` two-sided quaternion map. -/
lemma binaryIcosahedralSO4Action_comp
    (g h : BinaryIcosahedralSO4Pair) (x : ℍ[ℝ]) :
    binaryIcosahedralSO4Action h (binaryIcosahedralSO4Action g x)
      = binaryIcosahedralSO4Action (h.1 * g.1, h.2 * g.2) x := by
  simpa [binaryIcosahedralSO4Action, h4QuaternionToReal_mul]
    using
      Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map_comp
        (h4QuaternionToReal g.1.1) (h4QuaternionToReal g.2.1)
        (h4QuaternionToReal h.1.1) (h4QuaternionToReal h.2.1) x

/-- Every concrete `2I × 2I` action preserves the real quaternion norm-square. -/
lemma binaryIcosahedralSO4Action_normSq
    (g : BinaryIcosahedralSO4Pair) (x : ℍ[ℝ]) :
    Quaternion.normSq (binaryIcosahedralSO4Action g x) = Quaternion.normSq x :=
  binaryIcosahedralGroup_toReal_so4Map_normSq g.1 g.2 x

/-- The central sign pair belongs to the kernel of the concrete double cover:
`(p,q)` and `(-p,-q)` act by the same `SO(4)` rotation. -/
lemma binaryIcosahedralSO4Action_neg_neg
    (p q : BinaryIcosahedralGroup) (x : ℍ[ℝ]) :
    binaryIcosahedralSO4Action (-p, -q) x
      = binaryIcosahedralSO4Action (p, q) x := by
  simpa [binaryIcosahedralSO4Action]
    using
      Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map_neg_neg
        (h4QuaternionToReal p.1) (h4QuaternionToReal q.1) x

/-- The finite Hopf orbit obtained from the concrete `2I` coordinates.  It is
defined as a finite image of the exact coordinate set after real scalar
extension and the quaternion Hopf map. -/
noncomputable def binaryIcosahedralHopfOrbit : Finset (ℍ[ℝ]) := by
  classical
  exact binaryIcosahedralCoordinates.image fun q =>
    Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf
      (h4QuaternionToReal q)

/-- Every concrete `2I` group element contributes its Hopf image to the finite
orbit. -/
lemma binaryIcosahedralHopfOrbit_mem (g : BinaryIcosahedralGroup) :
    Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf
        (h4QuaternionToReal g.1)
      ∈ binaryIcosahedralHopfOrbit := by
  classical
  exact Finset.mem_image.mpr ⟨g.1, g.2, rfl⟩

/-- Every point in the finite `2I` Hopf orbit lies on the unit `S²`. -/
lemma binaryIcosahedralHopfOrbit_normSq_one {y : ℍ[ℝ]}
    (hy : y ∈ binaryIcosahedralHopfOrbit) :
    Quaternion.normSq y = 1 := by
  classical
  rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
  exact
    Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf_normSq
      (h4QuaternionToReal q) (binaryIcosahedral_toReal_normSq_one hq)

/-- Every point in the finite `2I` Hopf orbit is purely imaginary, so the orbit
really lands in the `S²` base of the Hopf fibration. -/
lemma binaryIcosahedralHopfOrbit_re_zero {y : ℍ[ℝ]}
    (hy : y ∈ binaryIcosahedralHopfOrbit) :
    y.re = 0 := by
  classical
  rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
  exact
    Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.hopf_re_zero
      (h4QuaternionToReal q)

/-- Coordinate/cardinality bridge to the existing `A₅ ⊂ S₅ = SU(5)` Weyl-net
infrastructure: `|2I| = 120 = |S₅| = 2|A₅|`. -/
lemma binaryIcosahedral_card_matches_su5Weyl_and_icosahedral :
    binaryIcosahedralCoordinates.card = Fintype.card Su5WeylGroup
      ∧ binaryIcosahedralCoordinates.card = 2 * Fintype.card IcosahedralGroup := by
  constructor
  · rw [binaryIcosahedralCoordinates_card,
      Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.su5WeylGroup_card]
  · rw [binaryIcosahedralCoordinates_card, card_icosahedralGroup]

/-! ## Connection to Sorkin §III.A Weyl chambers and the open `R4` net -/

/-- The concrete `2I/H4` coordinate count is the same `120` count as Sorkin's
`A4 = su(5)` Weyl-chamber tiling of the `R4` simplectic net. This is a
cardinality bridge, not a claim that the quaternion coordinates and affine
five-coordinate chambers are definitionally the same object. -/
lemma binaryIcosahedralCoordinates_card_eq_sorkinWeylChambers :
    binaryIcosahedralCoordinates.card = Fintype.card Su5WeylGroup := by
  rw [binaryIcosahedralCoordinates_card,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weylChambers_card]

/-- The checked counts line up with the Sorkin §III.A count package:
`H3` has `30` coordinates, the concrete `2I/H4` set has the same `120` count
as the Sorkin Weyl chambers, and Sorkin's isotropic group has twice that size
because it adds the independent `Z2` sign/charge-conjugation factor. -/
lemma h3_h4_counts_match_sorkin_sectionIIIA_counts :
    h3CoordinateSetQ5.card = 30
      ∧ binaryIcosahedralCoordinates.card = Fintype.card Su5WeylGroup
      ∧ Fintype.card Su5WeylGroup = 120
      ∧ Fintype.card IsotropicGroupR4 = 2 * binaryIcosahedralCoordinates.card := by
  refine ⟨h3CoordinateSetQ5_card,
    binaryIcosahedralCoordinates_card_eq_sorkinWeylChambers,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weylChambers_card,
    ?_⟩
  rw [Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.isotropicGroupR4_eq_su5weyl_times_two,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weylChambers_card,
    binaryIcosahedralCoordinates_card]

/-- Bridge to Sorkin §III.A's reasoning, not just its numerical data.

The quaternion side says that any two concrete `2I` elements define a
norm-preserving real `SO(4)` two-sided action. The Sorkin side contributes:
homogeneity of the leg relation under translation, Weyl-chamber cover
(`no gaps`), scale covariance of the open `R4` leg relation, and refinability
at every positive scale. These are kept as separate conjuncts because no
canonical coordinate map from the exact `2I` quaternions to Sorkin affine
five-tuples is asserted here. -/
lemma binaryIcosahedral_so4_action_links_to_sorkin_openR4_reasoning
    (p q : BinaryIcosahedralGroup) (x : ℍ[ℝ])
    (y u v t : Fin 5 → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    Quaternion.normSq
        (Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration.so4Map
          (h4QuaternionToReal p.1) (h4QuaternionToReal q.1) x)
      = Quaternion.normSq x
      ∧ (∃ sigma : Su5WeylGroup, InWeylChamber sigma y)
      ∧ (IsLegVector (fun i => u i + t i) (fun i => v i + t i) ↔ IsLegVector u v)
      ∧ (IsLegVectorAtScale lam u v
          ↔ IsLegVectorAtScale 1 (fun i => lam⁻¹ * u i) (fun i => lam⁻¹ * v i))
      ∧ RefinableAtEveryScale (fun lam => 0 < lam) := by
  exact ⟨binaryIcosahedralGroup_toReal_so4Map_normSq p q x,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weylChambers_cover y,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.isLegVector_translation_invariant u v t,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.isLegVector_scale_covariant lam hlam u v,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.openR4Net_refinable⟩

/-- Full finite-action synthesis for the concrete `2I` construction.

This theorem is the repo-facing bridge: exact `Q(sqrt 5)` coordinates form a
finite binary-icosahedral group; after scalar extension, `2I × 2I` acts on
real quaternions by the already-formalized two-sided `SO(4)` map, with identity,
composition, norm preservation, and the central `±1` double-cover kernel.  The
same group elements also have Hopf images that land on the `S²` base.  The
Sorkin side is included only through the already-proved open-`R4` facts:
Weyl-chamber cover, translation homogeneity, scale covariance, and refinability.
No canonical coordinate identification between the quaternion model and
Sorkin's affine five-coordinate net is asserted. -/
lemma binaryIcosahedral_action_hopf_sorkin_synthesis
    (g h : BinaryIcosahedralSO4Pair) (x : ℍ[ℝ])
    (y u v t : Fin 5 → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    binaryIcosahedralSO4Action (1, 1) x = x
      ∧ binaryIcosahedralSO4Action h (binaryIcosahedralSO4Action g x)
          = binaryIcosahedralSO4Action (h.1 * g.1, h.2 * g.2) x
      ∧ Quaternion.normSq (binaryIcosahedralSO4Action g x) = Quaternion.normSq x
      ∧ binaryIcosahedralSO4Action (-g.1, -g.2) x = binaryIcosahedralSO4Action g x
      ∧ (∀ z ∈ binaryIcosahedralHopfOrbit, Quaternion.normSq z = 1 ∧ z.re = 0)
      ∧ (∃ sigma : Su5WeylGroup, InWeylChamber sigma y)
      ∧ (IsLegVector (fun i => u i + t i) (fun i => v i + t i) ↔ IsLegVector u v)
      ∧ (IsLegVectorAtScale lam u v
          ↔ IsLegVectorAtScale 1 (fun i => lam⁻¹ * u i) (fun i => lam⁻¹ * v i))
      ∧ RefinableAtEveryScale (fun lam => 0 < lam) := by
  refine ⟨binaryIcosahedralSO4Action_one x,
    binaryIcosahedralSO4Action_comp g h x,
    binaryIcosahedralSO4Action_normSq g x,
    binaryIcosahedralSO4Action_neg_neg g.1 g.2 x,
    ?_,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weylChambers_cover y,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.isLegVector_translation_invariant u v t,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.isLegVector_scale_covariant lam hlam u v,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.openR4Net_refinable⟩
  exact fun z hz => ⟨binaryIcosahedralHopfOrbit_normSq_one hz,
    binaryIcosahedralHopfOrbit_re_zero hz⟩

/-- Concrete coordinate synthesis: the H3 coordinate system has `30` roots,
the H4/binary-icosahedral coordinate system has `120` unit quaternions, and
the latter is closed under multiplication and conjugation. -/
lemma concrete_h3_h4_and_binary_icosahedral_coordinates :
    h3CoordinateSetQ5.card = 30
      ∧ binaryIcosahedralCoordinates.card = 120
      ∧ (∀ q ∈ binaryIcosahedralCoordinates, Quaternion.normSq q = (1 : Quad5))
      ∧ (1 : H4Quaternion) ∈ binaryIcosahedralCoordinates
      ∧ (∀ q ∈ binaryIcosahedralCoordinates, ∀ r ∈ binaryIcosahedralCoordinates,
          q * r ∈ binaryIcosahedralCoordinates)
      ∧ (∀ q ∈ binaryIcosahedralCoordinates, star q ∈ binaryIcosahedralCoordinates) := by
  exact ⟨h3CoordinateSetQ5_card, binaryIcosahedralCoordinates_card,
    fun q hq => binaryIcosahedralCoordinates_normSq_one hq,
    one_mem_binaryIcosahedralCoordinates,
    fun q hq r hr => binaryIcosahedralCoordinates_mul_mem hq hr,
    fun q hq => binaryIcosahedralCoordinates_star_mem hq⟩

end Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

end
