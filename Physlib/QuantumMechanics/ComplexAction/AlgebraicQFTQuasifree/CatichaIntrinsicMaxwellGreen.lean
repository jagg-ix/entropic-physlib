/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
public import Physlib.Mathematics.Distribution.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A common continuum carrier for Caticha evolution and global curved Maxwell fields

The repository already has two independent, fully typed analytic interfaces:

* `ContinuumCatichaKGData` carries Caticha's functional generator, a complex
  Klein--Gordon operator, retarded/advanced Green operators, and Hadamard data;
* `PseudoRiemannianMetric.IntrinsicMaxwellGreenData` carries the global
  Ricci-coupled Maxwell operator and its real retarded/advanced Green operators.

This file joins them without identifying unlike carriers definitionally.  The
only new premise is `ContinuumCatichaIntrinsicMaxwellAdapter`: explicit additive
maps from the real Maxwell source/field carriers to their complex Caticha
counterparts, together with compatibility of the differential operators and
the two Green pairs.  From that premise the existing lemmas give twelve integration
capstones:

1. retarded evolution solves both equations on the common carrier;
2. the Pauli--Jordan causal propagators agree after complexification;
3. the shared causal field is simultaneously a global homogeneous Maxwell
   solution, stable under Caticha evolution, and equipped with the pulled-back
   CCR-compatible positive Hermitian microlocal/Hadamard carrier.
4. arbitrary homogeneous Maxwell fields map to homogeneous KG fields;
5. retarded-sector uniqueness agrees on both carriers;
6. the causal Caticha--Hadamard--Maxwell chain is independent of the compatible
   local Levi--Civita atlas used to construct the global connection.
7. Caticha functional evolution of an advanced KG field descends to the same
   declared source evolution as its retarded counterpart;
8. advanced Maxwell and KG solutions agree on the common carrier;
9. retarded and advanced sourced evolution are jointly independent of the
   compatible local Levi--Civita atlas.
10. an optional advanced support sector makes the advanced solution unique;
11. that advanced uniqueness is respected by the Caticha/KG carrier map;
12. localized Caticha sources map to commuting AQFT observables in causally
    disjoint regions while retaining the pulled-back Hadamard properties.

No claim is made that an arbitrary pseudo-Riemannian manifold supplies Green
operators, a Hadamard state, or a canonical real-to-complex carrier map.  Those
remain explicit analytic/geometric data.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Module
open scoped Manifold SchwartzMap

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open PseudoRiemannianMetric

universe uFc uSc uFr uSr uXi v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

variable {𝒯c : Type uFc} {𝒾c : Type uSc}
variable [AddCommGroup 𝒯c] [Module ℂ 𝒯c]
variable [AddCommGroup 𝒾c] [Module ℂ 𝒾c]
variable {𝒯fr : Type uFr} {𝒬er : Type uSr}
variable [AddCommGroup 𝒯fr] [Module ℝ 𝒯fr]
variable [AddCommGroup 𝒬er] [Module ℝ 𝒬er]

variable {d : ℕ}
variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

/-! # A. Advanced Caticha source evolution -/

namespace ContinuumCatichaKGData

/-- Caticha functional evolution of an advanced field is carried by the KG
operator to the declared source evolution.  This is the advanced counterpart
of `caticha_retarded_intertwines_source`. -/
lemma caticha_advanced_intertwines_source
    (D : ContinuumCatichaKGData 𝒯c 𝒾c) (source : 𝒾c) :
    D.kleinGordon
        (continuumSmearedSchrodingerGenerator D.lapse D.shift
          D.Hperp D.Hi (D.advanced source)) =
      D.sourceGenerator source := by
  rw [D.intertwines, D.kleinGordon_advanced source]

end ContinuumCatichaKGData

/-! # B. Common-carrier data -/

/-- Explicit common-carrier data between a global real Maxwell Green system
and a complex Caticha--Klein--Gordon Green system.  Additive maps are the
minimal structure needed to compare retarded-minus-advanced propagators; no
canonical complexification or equality of unlike differential operators is
silently assumed. -/
structure ContinuumCatichaIntrinsicMaxwellAdapter
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr) where
  /-- Complexification/encoding of a real Maxwell source. -/
  sourceMap : 𝒬er →+ 𝒾c
  /-- Complexification/encoding of a real Maxwell field. -/
  fieldMap : 𝒯fr →+ 𝒯c
  /-- The complex KG operator is the encoded global Maxwell wave operator on
  every field in the selected analytic carrier. -/
  waveOperator_compat : ∀ field,
    sourceMap (G.waveOperator field) = D.kleinGordon (fieldMap field)
  /-- The retarded Green evolutions agree on the encoded source. -/
  retarded_compat : ∀ source,
    fieldMap (G.retarded source) = D.retarded (sourceMap source)
  /-- The advanced Green evolutions agree on the encoded source. -/
  advanced_compat : ∀ source,
    fieldMap (G.advanced source) = D.advanced (sourceMap source)

namespace ContinuumCatichaIntrinsicMaxwellAdapter

/-! # B.1. Canonical adapter on a shared real/complex carrier -/

/-- **Canonical shared-carrier adapter.**  When the Maxwell and Caticha
descriptions use the same source and field types, no independently chosen
encoding maps are needed: the identity additive maps supply the adapter.
Only the three meaningful compatibility equations remain.

The real and complex module structures are both retained because the
intrinsic Maxwell operator is real-linear while the Caticha/KG operator is
complex-linear.  No equality between those scalar actions is assumed or
needed for the additive common-carrier statement. -/
def ofSameCarrier
    {𝒯 𝒮 : Type*}
    [AddCommGroup 𝒯] [Module ℝ 𝒯] [Module ℂ 𝒯]
    [AddCommGroup 𝒮] [Module ℝ 𝒮] [Module ℂ 𝒮]
    (D : ContinuumCatichaKGData 𝒯 𝒮)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒮 𝒯)
    (hwave : ∀ field, G.waveOperator field = D.kleinGordon field)
    (hretarded : ∀ source, G.retarded source = D.retarded source)
    (hadvanced : ∀ source, G.advanced source = D.advanced source) :
    ContinuumCatichaIntrinsicMaxwellAdapter I D G where
  sourceMap := AddMonoidHom.id 𝒮
  fieldMap := AddMonoidHom.id 𝒯
  waveOperator_compat field := by simpa using hwave field
  retarded_compat source := by simpa using hretarded source
  advanced_compat source := by simpa using hadvanced source

/-- The canonical shared-carrier adapter acts identically on sources. -/
@[simp]
lemma ofSameCarrier_sourceMap_apply
    {𝒯 𝒮 : Type*}
    [AddCommGroup 𝒯] [Module ℝ 𝒯] [Module ℂ 𝒯]
    [AddCommGroup 𝒮] [Module ℝ 𝒮] [Module ℂ 𝒮]
    (D : ContinuumCatichaKGData 𝒯 𝒮)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒮 𝒯)
    (hwave : ∀ field, G.waveOperator field = D.kleinGordon field)
    (hretarded : ∀ source, G.retarded source = D.retarded source)
    (hadvanced : ∀ source, G.advanced source = D.advanced source)
    (source : 𝒮) :
    (ofSameCarrier I D G hwave hretarded hadvanced).sourceMap source = source := rfl

/-- The canonical shared-carrier adapter acts identically on fields. -/
@[simp]
lemma ofSameCarrier_fieldMap_apply
    {𝒯 𝒮 : Type*}
    [AddCommGroup 𝒯] [Module ℝ 𝒯] [Module ℂ 𝒯]
    [AddCommGroup 𝒮] [Module ℝ 𝒮] [Module ℂ 𝒮]
    (D : ContinuumCatichaKGData 𝒯 𝒮)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒮 𝒯)
    (hwave : ∀ field, G.waveOperator field = D.kleinGordon field)
    (hretarded : ∀ source, G.retarded source = D.retarded source)
    (hadvanced : ∀ source, G.advanced source = D.advanced source)
    (field : 𝒯) :
    (ofSameCarrier I D G hwave hretarded hadvanced).fieldMap field = field := rfl

/-! # B.2. Concrete complex-linear Maxwell/Caticha Green carrier -/

/-- Promote a real-linear map on a real/complex analytic carrier to a
complex-linear map once its complex scalar compatibility has been proved.
The underlying function is unchanged. -/
def complexLinearOfRealLinear
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [AddCommGroup W] [Module ℝ W] [Module ℂ W]
    (f : V →ₗ[ℝ] W)
    (hsmul : ∀ c : ℂ, ∀ x, f (c • x) = c • f x) :
    V →ₗ[ℂ] W where
  toFun := f
  map_add' := f.map_add
  map_smul' := hsmul

/-- Complex-linearity certificate for an intrinsic Maxwell Green system on
one analytic carrier.  This is the exact domain condition needed to use the
same wave, retarded, and advanced maps as Caticha/Klein--Gordon operators;
it is strictly stronger than merely putting unrelated real and complex
module structures on the carrier. -/
structure ComplexLinearIntrinsicMaxwellCarrier
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒜 𝒜) : Prop where
  wave_smul : ∀ c : ℂ, ∀ field,
    G.waveOperator (c • field) = c • G.waveOperator field
  retarded_smul : ∀ c : ℂ, ∀ source,
    G.retarded (c • source) = c • G.retarded source
  advanced_smul : ∀ c : ℂ, ∀ source,
    G.advanced (c • source) = c • G.advanced source

namespace ComplexLinearIntrinsicMaxwellCarrier

variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
variable (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
  I g cov sign frame 𝒜 𝒜)

/-- The intrinsic Maxwell wave operator on its proved complex domain. -/
def waveOperator (C : ComplexLinearIntrinsicMaxwellCarrier I G) : 𝒜 →ₗ[ℂ] 𝒜 :=
  complexLinearOfRealLinear G.waveOperator C.wave_smul

/-- The intrinsic retarded Green operator on its proved complex domain. -/
def retarded (C : ComplexLinearIntrinsicMaxwellCarrier I G) : 𝒜 →ₗ[ℂ] 𝒜 :=
  complexLinearOfRealLinear G.retarded C.retarded_smul

/-- The intrinsic advanced Green operator on its proved complex domain. -/
def advanced (C : ComplexLinearIntrinsicMaxwellCarrier I G) : 𝒜 →ₗ[ℂ] 𝒜 :=
  complexLinearOfRealLinear G.advanced C.advanced_smul

/-- **Concrete Caticha/KG realization of an intrinsic Maxwell Green
system.**  The normal Caticha Hamiltonian and the KG/source operators are the
same complex-linear intrinsic Maxwell wave operator; lapse is one and shift
is zero.  The existing Maxwell Green maps become the retarded and advanced KG
maps.  Consequently Green inversion and the Caticha intertwining law are
proved from the supplied Maxwell datum rather than repeated as new premises. -/
def toContinuumCatichaKGData
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) :
    ContinuumCatichaKGData 𝒜 𝒜 where
  Hperp := C.waveOperator I G
  Hi := 0
  lapse := 1
  shift := 0
  kleinGordon := C.waveOperator I G
  sourceGenerator := C.waveOperator I G
  retarded := C.retarded I G
  advanced := C.advanced I G
  kleinGordon_retarded source := G.wave_retarded source
  kleinGordon_advanced source := G.wave_advanced source
  intertwines field := by
    simp [continuumSmearedSchrodingerGenerator]

@[simp]
lemma toContinuumCatichaKGData_kleinGordon_apply
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) (field : 𝒜) :
    (C.toContinuumCatichaKGData I G).kleinGordon field =
      G.waveOperator field := rfl

@[simp]
lemma toContinuumCatichaKGData_retarded_apply
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) (source : 𝒜) :
    (C.toContinuumCatichaKGData I G).retarded source = G.retarded source := rfl

@[simp]
lemma toContinuumCatichaKGData_advanced_apply
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) (source : 𝒜) :
    (C.toContinuumCatichaKGData I G).advanced source = G.advanced source := rfl

/-- The promised operator-identification theorem: on the selected complex
analytic carrier, Caticha's KG operator is pointwise exactly the intrinsic
Ricci-coupled Maxwell wave operator. -/
lemma catichaKG_eq_intrinsicMaxwell
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) :
    ∀ field : 𝒜,
      (C.toContinuumCatichaKGData I G).kleinGordon field =
        G.waveOperator field :=
  C.toContinuumCatichaKGData_kleinGordon_apply I G

/-- The concrete realization supplies the common-carrier adapter without any
additional wave or Green compatibility equations. -/
def toCatichaIntrinsicMaxwellAdapter
    (C : ComplexLinearIntrinsicMaxwellCarrier I G) :
    ContinuumCatichaIntrinsicMaxwellAdapter I
      (C.toContinuumCatichaKGData I G) G :=
  ofSameCarrier I (C.toContinuumCatichaKGData I G) G
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end ComplexLinearIntrinsicMaxwellCarrier

/-- **Globally-hyperbolic Cauchy-to-Caticha--Maxwell chain.**  Once a causal
Cauchy theorem supplies existence, support-sector membership, and uniqueness,
the retarded/advanced selectors become linear Green operators.  On a proved
complex-linear common domain, those derived operators construct the Caticha
KG datum.  Both Green fields then solve the KG and intrinsic Ricci-coupled
Maxwell equations, and the KG operator is the analytic intrinsic Maxwell
operator on every field.

The theorem does not assume retarded/advanced linear maps independently: they
are constructed by `WellPosedIntrinsicMaxwellCauchyData.toIntrinsicMaxwellGreenData`. -/
lemma wellPosedCauchy_catichaKG_intrinsicMaxwell_chain
    {𝒜 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    (D : PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData
      I g cov sign frame 𝒜 𝒜)
    (C : ComplexLinearIntrinsicMaxwellCarrier I
      D.toIntrinsicMaxwellGreenData)
    (source : 𝒜) :
    let G := D.toIntrinsicMaxwellGreenData
    let K := C.toContinuumCatichaKGData I G
    K.kleinGordon (K.retarded source) = source ∧
      K.kleinGordon (K.advanced source) = source ∧
      PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      ∀ field : 𝒜, K.kleinGordon field = G.waveOperator field := by
  dsimp only
  refine ⟨D.wave_retarded source, D.wave_advanced source, ?_, ?_, fun _ ↦ rfl⟩
  · exact PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves
      I D.toIntrinsicMaxwellGreenData source
  · exact PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves
      I D.toIntrinsicMaxwellGreenData source

/-! # B.3. Correct sesquilinear Hadamard carrier -/

/-- Hermiticity for a genuine complex sesquilinear two-point functional. -/
def IsHermitianSesquilinearTwoPoint
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℂ 𝒜]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ψ, W φ ψ = starRingEnd ℂ (W ψ φ)

/-- Positivity for a genuine complex sesquilinear two-point functional. -/
def IsPositiveSesquilinearTwoPoint
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℂ 𝒜]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ, 0 ≤ (W φ φ).re

/-- CCR compatibility on the underlying real test-field carrier. -/
def IsCCRSesquilinearTwoPoint
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ) : Prop :=
  ∀ φ ψ, W φ ψ - W ψ φ = Complex.I * (symp φ ψ : ℂ)

/-- Corrected continuum Hadamard carrier.  Unlike the legacy bilinear
carrier, its first slot is conjugate-linear and its CCR form is real
bilinear, matching the standard quasifree-field convention. -/
structure ContinuumSesquilinearHadamardTwoPoint
    (𝒜 Ξ : Type*) [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜] where
  twoPoint : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ
  symplecticForm : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ
  wavefront : Set Ξ
  positiveFrequencyCone : Set Ξ
  hermitian : IsHermitianSesquilinearTwoPoint twoPoint
  positive : IsPositiveSesquilinearTwoPoint twoPoint
  ccr : IsCCRSesquilinearTwoPoint twoPoint symplecticForm
  microlocal : MicrolocalSpectrumCondition wavefront positiveFrequencyCone

/-- Distributional data realizing a sesquilinear two-point functional.

Unlike the former certificate carrier, this structure contains no theorem
asserting its own Hadamard property.  The wavefront equality must be proved
from localized Fourier regularity off the proposed cone and singularity on
the cone; see `DistributionalHadamardData.wavefront_eq_iff`. -/
structure DistributionalHadamardData
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ} where
  /-- The spacetime two-point distribution. -/
  distribution : V →d[ℂ] ℂ
  /-- Schwartz smearing associated with a pair of abstract test fields. -/
  smearing : 𝒜 → 𝒜 → 𝓢(V, ℂ)
  /-- The distributional pairing realizes the abstract two-point form. -/
  represents : ∀ φ ψ, W φ ψ = distribution (smearing φ ψ)
  /-- Local chart/cutoff/conic-frequency probes for the distribution. -/
  probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ
  /-- The positive-frequency Hadamard cone in the chosen cotangent carrier. -/
  hadamardCone : Set (X × Ξ)

/-- The analytic regularity half of the Hadamard condition: every nonzero
covector outside the proposed cone has rapid localized-Fourier decay. -/
def DistributionalHadamardData.IsRegularOutsideCone
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) : Prop :=
  ∀ x ξ, ξ ≠ 0 → (x, ξ) ∉ D.hadamardCone →
    Physlib.Distribution.IsMicrolocallyRegularAt D.distribution D.probe x ξ

/-- The analytic singularity half of the Hadamard condition: every covector
in the proposed cone is nonzero and fails rapid localized-Fourier decay. -/
def DistributionalHadamardData.IsSingularOnCone
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) : Prop :=
  ∀ x ξ, (x, ξ) ∈ D.hadamardCone →
    ξ ≠ 0 ∧
      ¬ Physlib.Distribution.IsMicrolocallyRegularAt D.distribution D.probe x ξ

/-- Exact Hadamard wavefront equality is equivalent to the two genuine
localized-Fourier estimates: regularity off the cone and singularity on it. -/
lemma DistributionalHadamardData.wavefront_eq_iff
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) :
    Physlib.Distribution.distributionalWavefrontSet D.distribution D.probe =
        D.hadamardCone ↔
      D.IsRegularOutsideCone ∧ D.IsSingularOnCone := by
  constructor
  · intro h
    constructor
    · intro x ξ hξ houtside
      by_contra hirregular
      have hwf : (x, ξ) ∈ Physlib.Distribution.distributionalWavefrontSet
          D.distribution D.probe := ⟨hξ, hirregular⟩
      exact houtside (h ▸ hwf)
    · intro x ξ hcone
      have hwf : (x, ξ) ∈ Physlib.Distribution.distributionalWavefrontSet
          D.distribution D.probe := h.symm ▸ hcone
      exact hwf
  · rintro ⟨hregular, hsingular⟩
    ext xξ
    constructor
    · intro hwf
      by_contra houtside
      exact hwf.2 (hregular xξ.1 xξ.2 hwf.1 houtside)
    · intro hcone
      exact hsingular xξ.1 xξ.2 hcone

/-- Derive exact Hadamard wavefront equality from the two model-specific
microlocal theorems, without storing the conclusion in a certificate. -/
lemma DistributionalHadamardData.wavefront_eq
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (hregular : D.IsRegularOutsideCone)
    (hsingular : D.IsSingularOnCone) :
    Physlib.Distribution.distributionalWavefrontSet D.distribution D.probe =
      D.hadamardCone :=
  D.wavefront_eq_iff.mpr ⟨hregular, hsingular⟩

/-! ### Quantitative Fourier criteria for the two Hadamard halves -/

/-- Nonzero covectors outside a proposed Hadamard cone. -/
def DistributionalHadamardData.OffConeCovector
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) :=
  {xξ : X × Ξ // xξ.2 ≠ 0 ∧ xξ ∉ D.hadamardCone}

/-- Quantitative localized-Fourier upper bounds away from the proposed
Hadamard cone.

For every nonzero off-cone covector this carrier selects an actual localized
probe and supplies an explicit nonnegative bound at every polynomial order.
It contains no microlocal-regularity or wavefront-set conclusion. -/
structure DistributionalHadamardData.OffConeRapidDecayBounds
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) where
  probeIndex : D.OffConeCovector → D.probe.Index
  base_mem : ∀ q, q.1.1 ∈ D.probe.baseRegion (probeIndex q)
  frequency_mem : ∀ q, q.1.2 ∈ D.probe.coneRegion (probeIndex q)
  bound : D.OffConeCovector → ℕ → ℝ
  bound_nonneg : ∀ q N, 0 ≤ bound q N
  weighted_amplitude_le : ∀ q N η,
    η ∈ D.probe.coneRegion (probeIndex q) →
      (1 + ‖η‖) ^ N *
          ‖D.distribution (D.probe.test (probeIndex q) η)‖ ≤
        bound q N

/-- Explicit upper bounds at every polynomial order prove microlocal
regularity at every nonzero off-cone covector. -/
@[zil_level physical_theorem]
lemma DistributionalHadamardData.OffConeRapidDecayBounds.isRegularOutsideCone
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (B : D.OffConeRapidDecayBounds) :
    D.IsRegularOutsideCone := by
  intro x ξ hξ houtside
  let q : D.OffConeCovector := ⟨(x, ξ), hξ, houtside⟩
  refine ⟨B.probeIndex q, B.base_mem q, B.frequency_mem q, ?_⟩
  intro N
  exact ⟨B.bound q N, B.bound_nonneg q N,
    fun η hη => B.weighted_amplitude_le q N η hη⟩

/-- Covectors on a proposed Hadamard cone. -/
def DistributionalHadamardData.OnConeCovector
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) :=
  {xξ : X × Ξ // xξ ∈ D.hadamardCone}

/-- Quantitative localized-Fourier lower growth on the proposed Hadamard
cone.

For every on-cone covector and every probe that could witness regularity,
one polynomially weighted amplitude escapes every nonnegative bound.  This
is an analytic singularity premise, not a stored `¬ regular` certificate. -/
structure DistributionalHadamardData.OnConeLowerEscapeBounds
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) where
  frequency_ne_zero : ∀ q : D.OnConeCovector, q.1.2 ≠ 0
  lower_escape : ∀ (q : D.OnConeCovector) (i : D.probe.Index),
    q.1.1 ∈ D.probe.baseRegion i →
    q.1.2 ∈ D.probe.coneRegion i →
      Physlib.Distribution.HasPolynomialLowerEscapeOn
        (fun η ↦ D.distribution (D.probe.test i η))
        (D.probe.coneRegion i)

/-- Explicit lower growth on every candidate localized probe proves
singularity at every covector of the proposed cone. -/
@[zil_level physical_theorem]
lemma DistributionalHadamardData.OnConeLowerEscapeBounds.isSingularOnCone
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (B : D.OnConeLowerEscapeBounds) :
    D.IsSingularOnCone := by
  intro x ξ hcone
  let q : D.OnConeCovector := ⟨(x, ξ), hcone⟩
  refine ⟨B.frequency_ne_zero q, ?_⟩
  rintro ⟨i, hx, hξ, hrapid⟩
  exact
    (Physlib.Distribution.not_hasRapidFourierDecayOn_of_hasPolynomialLowerEscapeOn
      (B.lower_escape q i hx hξ)) hrapid

/-- Quantitative upper and lower Fourier estimates derive the exact
distributional Hadamard wavefront set, without either Hadamard half being
supplied as a proposition-valued certificate. -/
@[zil_level physical_theorem]
lemma DistributionalHadamardData.wavefront_eq_of_fourierBounds
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (offCone : D.OffConeRapidDecayBounds)
    (onCone : D.OnConeLowerEscapeBounds) :
    Physlib.Distribution.distributionalWavefrontSet D.distribution D.probe =
      D.hadamardCone :=
  D.wavefront_eq offCone.isRegularOutsideCone onCone.isSingularOnCone

/-- Complete bidirectional transport between two distribution/probe pairs.
The distributions may have different Schwartz test spaces and the probes may
have unrelated index types.  The coverage fields identify base and conic
regions, while the pairing fields identify the localized Fourier amplitudes
seen by the two distributions. -/
structure DistributionalProbeTransport
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    (distribution : V →d[ℂ] ℂ)
    (probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ)
    (distribution' : V' →d[ℂ] ℂ)
    (probe' : Physlib.Distribution.MicrolocalFourierProbe V' X Ξ) where
  forward : probe.Index → probe'.Index
  backward : probe'.Index → probe.Index
  forward_base : ∀ i, probe'.baseRegion (forward i) = probe.baseRegion i
  forward_cone : ∀ i, probe'.coneRegion (forward i) = probe.coneRegion i
  backward_base : ∀ j, probe.baseRegion (backward j) = probe'.baseRegion j
  backward_cone : ∀ j, probe.coneRegion (backward j) = probe'.coneRegion j
  forward_pairing : ∀ i η,
    distribution (probe.test i η) =
      distribution' (probe'.test (forward i) η)
  backward_pairing : ∀ j η,
    distribution' (probe'.test j η) =
      distribution (probe.test (backward j) η)

/-- Bidirectional distribution/probe transport preserves microlocal
regularity at every base point and covector. -/
lemma DistributionalProbeTransport.regularAt_iff
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {distribution : V →d[ℂ] ℂ}
    {probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ}
    {distribution' : V' →d[ℂ] ℂ}
    {probe' : Physlib.Distribution.MicrolocalFourierProbe V' X Ξ}
    (T : DistributionalProbeTransport distribution probe distribution' probe')
    (x : X) (ξ : Ξ) :
    Physlib.Distribution.IsMicrolocallyRegularAt distribution probe x ξ ↔
      Physlib.Distribution.IsMicrolocallyRegularAt distribution' probe' x ξ := by
  constructor
  · rintro ⟨i, hx, hξ, hdecay⟩
    refine ⟨T.forward i, ?_, ?_, ?_⟩
    · rw [T.forward_base i]
      exact hx
    · rw [T.forward_cone i]
      exact hξ
    · rw [T.forward_cone i]
      exact (Physlib.Distribution.hasRapidFourierDecayOn_congr
        (fun η _ => T.forward_pairing i η)).mp hdecay
  · rintro ⟨j, hx, hξ, hdecay⟩
    refine ⟨T.backward j, ?_, ?_, ?_⟩
    · rw [T.backward_base j]
      exact hx
    · rw [T.backward_cone j]
      exact hξ
    · rw [T.backward_cone j]
      exact (Physlib.Distribution.hasRapidFourierDecayOn_congr
        (fun η _ => T.backward_pairing j η)).mp hdecay

/-- The computed localized-Fourier wavefront set is invariant under complete
bidirectional distribution/probe transport. -/
lemma DistributionalProbeTransport.wavefront_eq
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {distribution : V →d[ℂ] ℂ}
    {probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ}
    {distribution' : V' →d[ℂ] ℂ}
    {probe' : Physlib.Distribution.MicrolocalFourierProbe V' X Ξ}
    (T : DistributionalProbeTransport distribution probe distribution' probe') :
    Physlib.Distribution.distributionalWavefrontSet distribution probe =
      Physlib.Distribution.distributionalWavefrontSet distribution' probe' := by
  ext xξ
  simp only [Physlib.Distribution.distributionalWavefrontSet, Set.mem_setOf_eq]
  rw [T.regularAt_iff]

/-- Reflexive probe transport when only the representing distribution
changes and all evaluated pairings agree on the common probe family. -/
def DistributionalProbeTransport.ofSameProbePairing
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    (distribution distribution' : V →d[ℂ] ℂ)
    (probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ)
    (hprobe : ∀ i η,
      distribution (probe.test i η) = distribution' (probe.test i η)) :
    DistributionalProbeTransport distribution probe distribution' probe where
  forward := id
  backward := id
  forward_base := fun _ => rfl
  forward_cone := fun _ => rfl
  backward_base := fun _ => rfl
  backward_cone := fun _ => rfl
  forward_pairing := hprobe
  backward_pairing := fun i η => (hprobe i η).symm

/-- Reverse a complete distribution/probe transport. -/
def DistributionalProbeTransport.symm
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {distribution : V →d[ℂ] ℂ}
    {probe : Physlib.Distribution.MicrolocalFourierProbe V X Ξ}
    {distribution' : V' →d[ℂ] ℂ}
    {probe' : Physlib.Distribution.MicrolocalFourierProbe V' X Ξ}
    (T : DistributionalProbeTransport distribution probe distribution' probe') :
    DistributionalProbeTransport distribution' probe' distribution probe where
  forward := T.backward
  backward := T.forward
  forward_base := T.backward_base
  forward_cone := T.backward_cone
  backward_base := T.forward_base
  backward_cone := T.forward_cone
  forward_pairing := T.backward_pairing
  backward_pairing := T.forward_pairing

/-- Compose complete distribution/probe transports.  This permits Hadamard
theorems to move through several carrier changes without collapsing all
intermediate test spaces or probe index types definitionally. -/
def DistributionalProbeTransport.trans
    {V₀ V₁ V₂ : Type} {X Ξ : Type*}
    [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup Ξ]
    {distribution₀ : V₀ →d[ℂ] ℂ}
    {probe₀ : Physlib.Distribution.MicrolocalFourierProbe V₀ X Ξ}
    {distribution₁ : V₁ →d[ℂ] ℂ}
    {probe₁ : Physlib.Distribution.MicrolocalFourierProbe V₁ X Ξ}
    {distribution₂ : V₂ →d[ℂ] ℂ}
    {probe₂ : Physlib.Distribution.MicrolocalFourierProbe V₂ X Ξ}
    (T₀₁ : DistributionalProbeTransport
      distribution₀ probe₀ distribution₁ probe₁)
    (T₁₂ : DistributionalProbeTransport
      distribution₁ probe₁ distribution₂ probe₂) :
    DistributionalProbeTransport
      distribution₀ probe₀ distribution₂ probe₂ where
  forward := fun i => T₁₂.forward (T₀₁.forward i)
  backward := fun k => T₀₁.backward (T₁₂.backward k)
  forward_base := fun i =>
    (T₁₂.forward_base (T₀₁.forward i)).trans (T₀₁.forward_base i)
  forward_cone := fun i =>
    (T₁₂.forward_cone (T₀₁.forward i)).trans (T₀₁.forward_cone i)
  backward_base := fun k =>
    (T₀₁.backward_base (T₁₂.backward k)).trans (T₁₂.backward_base k)
  backward_cone := fun k =>
    (T₀₁.backward_cone (T₁₂.backward k)).trans (T₁₂.backward_cone k)
  forward_pairing := fun i η =>
    (T₀₁.forward_pairing i η).trans
      (T₁₂.forward_pairing (T₀₁.forward i) η)
  backward_pairing := fun k η =>
    (T₁₂.backward_pairing k η).trans
      (T₀₁.backward_pairing (T₁₂.backward k) η)

/-- Analytic transport data between distributional Hadamard realizations.

Unlike the former same-probe helper, source and target distributions may live
on different Schwartz test spaces and the target may carry an independently
constructed chart/cutoff probe family with a different index type.  The two
coverage maps certify that the probe families see the same base and conic
regions.  The two pairing fields then identify the localized Fourier
amplitudes in both directions.  These are precisely the hypotheses needed to
derive equality of computed wavefront sets; no cone is copied as metadata. -/
structure DistributionalHadamardData.Transport
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) where
  /-- Distribution representing the target two-point functional. -/
  distribution : V' →d[ℂ] ℂ
  /-- Target Schwartz smearing map. -/
  smearing : 𝒟 → 𝒟 → SchwartzMap V' ℂ
  /-- Exact realization of the target two-point functional. -/
  represents : ∀ φ ψ, W' φ ψ = distribution (smearing φ ψ)
  /-- Independently selected target localized-Fourier probes. -/
  probe : Physlib.Distribution.MicrolocalFourierProbe V' X Ξ
  /-- Full bidirectional coverage and distributional pairing transport. -/
  probeTransport : DistributionalProbeTransport
    D.distribution D.probe distribution probe

/-- Extract the target distributional data from complete analytic transport.
No Hadamard conclusion is stored in the result. -/
def DistributionalHadamardData.Transport.toData
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (T : D.Transport (𝒟 := 𝒟) (V' := V') (W' := W')) :
    DistributionalHadamardData
      (𝒜 := 𝒟) (V := V') (X := X) (Ξ := Ξ) (W := W') where
  distribution := T.distribution
  smearing := T.smearing
  represents := T.represents
  probe := T.probe
  hadamardCone := D.hadamardCone

/-- Complete probe transport preserves the analytic regularity theorem off
the Hadamard cone. -/
lemma DistributionalHadamardData.Transport.isRegularOutsideCone
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (T : D.Transport (𝒟 := 𝒟) (V' := V') (W' := W'))
    (hregular : D.IsRegularOutsideCone) :
    T.toData.IsRegularOutsideCone := by
  intro x ξ hξ houtside
  exact (T.probeTransport.regularAt_iff x ξ).mp
    (hregular x ξ hξ houtside)

/-- Complete probe transport preserves the analytic singularity theorem on
the Hadamard cone. -/
lemma DistributionalHadamardData.Transport.isSingularOnCone
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (T : D.Transport (𝒟 := 𝒟) (V' := V') (W' := W'))
    (hsingular : D.IsSingularOnCone) :
    T.toData.IsSingularOnCone := by
  intro x ξ hcone
  have hsource := hsingular x ξ hcone
  refine ⟨hsource.1, ?_⟩
  intro htarget
  exact hsource.2 ((T.probeTransport.regularAt_iff x ξ).mpr htarget)

/-- Complete analytic transport carries a proved source wavefront theorem to
the target distribution; the result follows from localized-Fourier pairing
invariance rather than from a copied certificate field. -/
lemma DistributionalHadamardData.Transport.wavefront_eq
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (T : D.Transport (𝒟 := 𝒟) (V' := V') (W' := W'))
    (hregular : D.IsRegularOutsideCone)
    (hsingular : D.IsSingularOnCone) :
    Physlib.Distribution.distributionalWavefrontSet T.distribution T.probe =
      D.hadamardCone :=
  T.toData.wavefront_eq (T.isRegularOutsideCone hregular)
    (T.isSingularOnCone hsingular)

/-- Construct transport data when source and target genuinely use the same
probe family.  This convenience constructor is now an explicit reflexive
specialization of the general transport carrier. -/
def DistributionalHadamardData.Transport.ofSameProbePairing
    {𝒜 𝒟 : Type*}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (distribution : V →d[ℂ] ℂ)
    (smearing : 𝒟 → 𝒟 → SchwartzMap V ℂ)
    (represents : ∀ φ ψ, W' φ ψ = distribution (smearing φ ψ))
    (hprobe : ∀ (i : D.probe.Index) (η : Ξ),
      D.distribution (D.probe.test i η) =
        distribution (D.probe.test i η)) :
    D.Transport (𝒟 := 𝒟) (V' := V) (W' := W') where
  distribution := distribution
  smearing := smearing
  represents := represents
  probe := D.probe
  probeTransport := DistributionalProbeTransport.ofSameProbePairing
    D.distribution distribution D.probe hprobe

/-- Construct the corrected continuum Hadamard carrier from a spacetime
distribution and an exact localized-Fourier wavefront theorem.  In contrast
to `ofInnerProduct`, this constructor cannot manufacture microlocal support by
assigning the same arbitrary set to both fields. -/
def ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (hHermitian : IsHermitianSesquilinearTwoPoint W)
    (hPositive : IsPositiveSesquilinearTwoPoint W)
    (hCCR : IsCCRSesquilinearTwoPoint W symp)
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (hregular : D.IsRegularOutsideCone)
    (hsingular : D.IsSingularOnCone) :
    ContinuumSesquilinearHadamardTwoPoint 𝒜 (X × Ξ) where
  twoPoint := W
  symplecticForm := symp
  wavefront := Physlib.Distribution.distributionalWavefrontSet D.distribution D.probe
  positiveFrequencyCone := D.hadamardCone
  hermitian := hHermitian
  positive := hPositive
  ccr := hCCR
  microlocal :=
    Physlib.Distribution.distributionalWavefrontSet_subset_of_eq
      D.distribution D.probe D.hadamardCone (D.wavefront_eq hregular hsingular)

/-- The carrier built from distributional microlocal theorems exposes the
proved exact equality between its computed wavefront set and the Hadamard cone. -/
lemma ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (hHermitian : IsHermitianSesquilinearTwoPoint W)
    (hPositive : IsPositiveSesquilinearTwoPoint W)
    (hCCR : IsCCRSesquilinearTwoPoint W symp)
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (hregular : D.IsRegularOutsideCone)
    (hsingular : D.IsSingularOnCone) :
    (ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems
      W symp hHermitian hPositive hCCR D hregular hsingular).wavefront =
        D.hadamardCone :=
  D.wavefront_eq hregular hsingular

/-- Every element of the computed wavefront set of a proved Hadamard
carrier has a nonzero covector. -/
lemma ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_covector_ne_zero
    {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    {V : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Ξ]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (hHermitian : IsHermitianSesquilinearTwoPoint W)
    (hPositive : IsPositiveSesquilinearTwoPoint W)
    (hCCR : IsCCRSesquilinearTwoPoint W symp)
    (D : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W))
    (hregular : D.IsRegularOutsideCone)
    (hsingular : D.IsSingularOnCone)
    {xξ : X × Ξ}
    (hxξ : xξ ∈ (ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems
      W symp hHermitian hPositive hCCR D hregular hsingular).wavefront) :
    xξ.2 ≠ 0 :=
  Physlib.Distribution.distributionalWavefrontSet_covector_ne_zero
    D.distribution D.probe hxξ

/-! ## B.4. Sesquilinear causal pullback -/

/-- Pull a genuine sesquilinear two-point functional back along a
complex-linear field map.  This is the conjugate-linear analogue of the
older `pullbackTwoPoint`; defining it once here avoids rebuilding the same
algebra for Klein--Gordon, Maxwell, and Dirac causal propagators. -/
def pullbackSesquilinearTwoPoint
    {𝒟 𝒜 : Type*}
    [AddCommGroup 𝒟] [Module ℂ 𝒟]
    [AddCommGroup 𝒜] [Module ℂ 𝒜]
    (U : 𝒟 →ₗ[ℂ] 𝒜) (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ) :
    𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ where
  toFun φ :=
    { toFun := fun ψ => W (U φ) (U ψ)
      map_add' := by intro ψ χ; simp
      map_smul' := by intro c ψ; simp }
  map_add' φ ψ := by ext χ; simp
  map_smul' c φ := by ext χ; simp

/-- A complex-linear pullback preserves Hermiticity of a sesquilinear
two-point functional. -/
lemma pullbackSesquilinearTwoPoint_isHermitian
    {𝒟 𝒜 : Type*}
    [AddCommGroup 𝒟] [Module ℂ 𝒟]
    [AddCommGroup 𝒜] [Module ℂ 𝒜]
    (U : 𝒟 →ₗ[ℂ] 𝒜) (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (hW : IsHermitianSesquilinearTwoPoint W) :
    IsHermitianSesquilinearTwoPoint (pullbackSesquilinearTwoPoint U W) := by
  intro φ ψ
  simpa [pullbackSesquilinearTwoPoint] using hW (U φ) (U ψ)

/-- A complex-linear pullback preserves positivity of a sesquilinear
two-point functional. -/
lemma pullbackSesquilinearTwoPoint_isPositive
    {𝒟 𝒜 : Type*}
    [AddCommGroup 𝒟] [Module ℂ 𝒟]
    [AddCommGroup 𝒜] [Module ℂ 𝒜]
    (U : 𝒟 →ₗ[ℂ] 𝒜) (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (hW : IsPositiveSesquilinearTwoPoint W) :
    IsPositiveSesquilinearTwoPoint (pullbackSesquilinearTwoPoint U W) := by
  intro φ
  simpa [pullbackSesquilinearTwoPoint] using hW (U φ)

/-- Pull a corrected sesquilinear Hadamard carrier through a linear field
evolution.  Hermiticity and positivity are derived.  The real symplectic
pullback identity and positive-cone transport are explicit analytic inputs;
they respectively derive CCR compatibility and microlocal support.

If `H` came from `ofDistributionalTheorems`, its starting wavefront was
computed by localized Fourier decay.  This construction transports that
proved carrier; it does not claim a new propagation-of-singularities theorem
without the supplied `transport` and `hcone`. -/
noncomputable def ContinuumSesquilinearHadamardTwoPoint.pullback
    {𝒟 𝒜 Ξ : Type*}
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    (H : ContinuumSesquilinearHadamardTwoPoint 𝒜 Ξ)
    (U : 𝒟 →ₗ[ℂ] 𝒜)
    (symp : 𝒟 →ₗ[ℝ] 𝒟 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ φ ψ,
      symp φ ψ = H.symplecticForm (U φ) (U ψ))
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport H.positiveFrequencyCone
      H.positiveFrequencyCone) :
    ContinuumSesquilinearHadamardTwoPoint 𝒟 Ξ where
  twoPoint := pullbackSesquilinearTwoPoint U H.twoPoint
  symplecticForm := symp
  wavefront := transport '' H.wavefront
  positiveFrequencyCone := H.positiveFrequencyCone
  hermitian :=
    pullbackSesquilinearTwoPoint_isHermitian U H.twoPoint H.hermitian
  positive :=
    pullbackSesquilinearTwoPoint_isPositive U H.twoPoint H.positive
  ccr := by
    intro φ ψ
    change
      H.twoPoint (U φ) (U ψ) - H.twoPoint (U ψ) (U φ) =
        Complex.I * (symp φ ψ : ℂ)
    rw [symp_pullback]
    exact H.ccr (U φ) (U ψ)
  microlocal :=
    microlocalSpectrumCondition_image transport H.microlocal hcone

/-- The sesquilinear pullback exposes all four inherited quasifree/Hadamard
laws together. -/
lemma ContinuumSesquilinearHadamardTwoPoint.pullback_properties
    {𝒟 𝒜 Ξ : Type*}
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    (H : ContinuumSesquilinearHadamardTwoPoint 𝒜 Ξ)
    (U : 𝒟 →ₗ[ℂ] 𝒜)
    (symp : 𝒟 →ₗ[ℝ] 𝒟 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ φ ψ,
      symp φ ψ = H.symplecticForm (U φ) (U ψ))
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport H.positiveFrequencyCone
      H.positiveFrequencyCone) :
    IsHermitianSesquilinearTwoPoint
        (H.pullback U symp symp_pullback transport hcone).twoPoint ∧
      IsPositiveSesquilinearTwoPoint
        (H.pullback U symp symp_pullback transport hcone).twoPoint ∧
      IsCCRSesquilinearTwoPoint
        (H.pullback U symp symp_pullback transport hcone).twoPoint
        (H.pullback U symp symp_pullback transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (H.pullback U symp symp_pullback transport hcone).wavefront
        (H.pullback U symp symp_pullback transport hcone).positiveFrequencyCone :=
  ⟨(H.pullback U symp symp_pullback transport hcone).hermitian,
    (H.pullback U symp symp_pullback transport hcone).positive,
    (H.pullback U symp symp_pullback transport hcone).ccr,
    (H.pullback U symp symp_pullback transport hcone).microlocal⟩

/-- The real symplectic form `2 Im ⟪φ,ψ⟫` associated with a complex Hilbert
carrier. -/
def innerSymplecticForm
    {𝒜 : Type*} [NormedAddCommGroup 𝒜] [InnerProductSpace ℂ 𝒜] :
    𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ where
  toFun φ :=
    { toFun := fun ψ => 2 * (inner ℂ φ ψ).im
      map_add' := by intro ψ χ; simp [inner_add_right, mul_add]
      map_smul' := by
        intro r ψ
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right]
        simp [RCLike.real_smul_eq_coe_mul]
        ring }
  map_add' := by
    intro φ χ
    ext ψ
    simp [inner_add_left, mul_add]
  map_smul' := by
    intro r φ
    ext ψ
    change 2 * (inner ℂ ((r : ℂ) • φ) ψ).im =
      r * (2 * (inner ℂ φ ψ).im)
    rw [inner_smul_left]
    simp
    ring

/-- A concrete nonzero-capable quasifree/Hadamard carrier supplied by the
Hilbert inner product.  The wavefront cone remains explicit: choosing `cone`
records the analytic microlocal certificate at the carrier boundary instead
of pretending it follows from Hilbert positivity. -/
noncomputable def ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct
    {𝒜 Ξ : Type*} [NormedAddCommGroup 𝒜] [InnerProductSpace ℂ 𝒜]
    (cone : Set Ξ) : ContinuumSesquilinearHadamardTwoPoint 𝒜 Ξ where
  twoPoint := innerₛₗ ℂ (E := 𝒜)
  symplecticForm := innerSymplecticForm
  wavefront := cone
  positiveFrequencyCone := cone
  hermitian := by
    intro φ ψ
    change inner ℂ φ ψ = starRingEnd ℂ (inner ℂ ψ φ)
    exact (inner_conj_symm (𝕜 := ℂ) φ ψ).symm
  positive := by
    intro φ
    change 0 ≤ (inner ℂ φ φ).re
    exact inner_self_nonneg (𝕜 := ℂ) (x := φ)
  ccr := by
    intro φ ψ
    simp only [innerₛₗ_apply_apply]
    change inner ℂ φ ψ - inner ℂ ψ φ =
      Complex.I * ((2 * (inner ℂ φ ψ).im : ℝ) : ℂ)
    rw [← inner_conj_symm (𝕜 := ℂ) ψ φ]
    simpa only [mul_comm] using Complex.sub_conj (inner ℂ φ ψ)
  microlocal := Set.Subset.rfl

@[simp]
lemma ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_twoPoint
    {𝒜 Ξ : Type*} [NormedAddCommGroup 𝒜] [InnerProductSpace ℂ 𝒜]
    (cone : Set Ξ) (φ ψ : 𝒜) :
    (ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct cone).twoPoint φ ψ =
      inner ℂ φ ψ := by
  rfl

/-- The corrected Hilbert-space two-point carrier is genuinely nonzero on
every nonzero field.  This distinguishes it from the only universally safe
constructor available for the legacy complex-bilinear interface. -/
lemma ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_self_ne_zero
    {𝒜 Ξ : Type*} [NormedAddCommGroup 𝒜] [InnerProductSpace ℂ 𝒜]
    (cone : Set Ξ) {φ : 𝒜} (hφ : φ ≠ 0) :
    (ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct cone).twoPoint φ φ ≠ 0 := by
  rw [ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_twoPoint]
  exact (inner_self_ne_zero (𝕜 := ℂ)).2 hφ

/-! # C. Retarded, advanced, and causal compatibility -/

/-- **Shared retarded evolution.**  A Maxwell source propagated by the global
intrinsic Green operator solves the Ricci-coupled Maxwell equation; its image
on the complex carrier is exactly the Caticha/KG retarded solution and hence
solves the encoded Klein--Gordon source equation. -/
lemma retarded_common_carrier
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      D.kleinGordon (D.retarded (A.sourceMap source)) = A.sourceMap source ∧
      A.fieldMap (G.retarded source) = D.retarded (A.sourceMap source) :=
  ⟨PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves I G source,
    D.kleinGordon_retarded_apply (A.sourceMap source), A.retarded_compat source⟩

/-- **Shared advanced evolution.**  A Maxwell source propagated by the global
advanced Green operator solves the intrinsic curved Maxwell equation; its
image on the complex carrier is the advanced Caticha/KG solution, which solves
the encoded source equation and whose Caticha evolution descends to the
declared source generator. -/
lemma advanced_common_carrier
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      D.kleinGordon (D.advanced (A.sourceMap source)) = A.sourceMap source ∧
      A.fieldMap (G.advanced source) = D.advanced (A.sourceMap source) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.advanced (A.sourceMap source))) =
        D.sourceGenerator (A.sourceMap source) :=
  ⟨PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves I G source,
    D.kleinGordon_advanced (A.sourceMap source), A.advanced_compat source,
    D.caticha_advanced_intertwines_source (A.sourceMap source)⟩

/-- **Shared Pauli--Jordan propagator.**  Compatibility of the retarded and
advanced Green maps implies compatibility of their difference.  This is the
actual common-carrier equation between the global Maxwell causal field and
the continuum Caticha/KG causal field. -/
lemma causalPropagator_compat
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er) :
    A.fieldMap
        (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
          I G source) =
      D.causalPropagator (A.sourceMap source) := by
  rw [PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator,
    ContinuumCatichaKGData.causalPropagator, LinearMap.sub_apply,
    LinearMap.sub_apply, map_sub,
    A.retarded_compat source, A.advanced_compat source]

/-- **Caticha--AQFT--global-Maxwell causal capstone.**  On the explicit common
carrier, one causal Green field is (i) a global homogeneous curved Maxwell
solution, (ii) mapped to the Caticha/KG causal field, (iii) preserved by the
Caticha functional generator inside the homogeneous KG solution space, and
(iv) accompanied by the pulled-back positive, Hermitian, CCR-compatible
microlocal two-point carrier. -/
lemma causal_hadamard_globalMaxwell_chain
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er)
    {Ξ : Type uXi} (Q : ContinuumHadamardTwoPoint 𝒯c Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport Q.positiveFrequencyCone
      Q.positiveFrequencyCone) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source)) 0 ∧
      A.fieldMap
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source) =
        D.causalPropagator (A.sourceMap source) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.causalPropagator (A.sourceMap source))) = 0 ∧
      IsHermitianTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsPositiveTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint
          (D.causalHadamardCarrier Q transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
          (D.causalHadamardCarrier Q transport hcone).wavefront
          (D.causalHadamardCarrier Q transport hcone).positiveFrequencyCone := by
  have hQ := D.causalHadamardCarrier_properties Q transport hcone
  exact
    ⟨PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator_solves_homogeneous
        I G source,
      causalPropagator_compat I D G A source,
      D.caticha_causalPropagator_is_homogeneous (A.sourceMap source),
      hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩

/-! # C.1. Direct same-carrier consequences -/

/-- **The Maxwell and Caticha Pauli--Jordan propagators coincide on a shared
carrier.**  The identity adapter is constructed internally, so the statement
requires only equality of the wave and Green operators rather than a separate
adapter object. -/
lemma causalPropagator_eq_of_sameCarrier
    {𝒯 𝒮 : Type*}
    [AddCommGroup 𝒯] [Module ℝ 𝒯] [Module ℂ 𝒯]
    [AddCommGroup 𝒮] [Module ℝ 𝒮] [Module ℂ 𝒮]
    (D : ContinuumCatichaKGData 𝒯 𝒮)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒮 𝒯)
    (hwave : ∀ field, G.waveOperator field = D.kleinGordon field)
    (hretarded : ∀ source, G.retarded source = D.retarded source)
    (hadvanced : ∀ source, G.advanced source = D.advanced source)
    (source : 𝒮) :
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator I G source =
      D.causalPropagator source := by
  simpa using causalPropagator_compat I D G
    (ofSameCarrier I D G hwave hretarded hadvanced) source

/-- **Same-carrier Caticha--Hadamard--global-Maxwell capstone.**  If the real
Maxwell and complex Caticha descriptions already share their analytic source
and field carriers, their operator compatibility directly yields: the global
homogeneous intrinsic Maxwell equation, equality of their Pauli--Jordan
fields, preservation by Caticha functional evolution, and the positive,
Hermitian, CCR-compatible microlocal two-point carrier.

This removes the adapter-existence premise.  It deliberately retains the
Green data, Hadamard data, and covector-cone preservation as explicit analytic
inputs. -/
lemma causal_hadamard_globalMaxwell_sameCarrier_chain
    {𝒯 𝒮 : Type*}
    [AddCommGroup 𝒯] [Module ℝ 𝒯] [Module ℂ 𝒯]
    [AddCommGroup 𝒮] [Module ℝ 𝒮] [Module ℂ 𝒮]
    (D : ContinuumCatichaKGData 𝒯 𝒮)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒮 𝒯)
    (hwave : ∀ field, G.waveOperator field = D.kleinGordon field)
    (hretarded : ∀ source, G.retarded source = D.retarded source)
    (hadvanced : ∀ source, G.advanced source = D.advanced source)
    (source : 𝒮)
    {Ξ : Type uXi} (Q : ContinuumHadamardTwoPoint 𝒯 Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport Q.positiveFrequencyCone
      Q.positiveFrequencyCone) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source)) 0 ∧
      PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
          I G source = D.causalPropagator source ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.causalPropagator source)) = 0 ∧
      IsHermitianTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsPositiveTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint
          (D.causalHadamardCarrier Q transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
          (D.causalHadamardCarrier Q transport hcone).wavefront
          (D.causalHadamardCarrier Q transport hcone).positiveFrequencyCone := by
  simpa using causal_hadamard_globalMaxwell_chain I D G
    (ofSameCarrier I D G hwave hretarded hadvanced) source Q transport hcone

/-! # D. Operator transport and retarded uniqueness -/

/-- **Homogeneous equations survive the common-carrier map.**  Any field in
the kernel of the global Maxwell wave operator maps to a field in the kernel
of the complex Klein--Gordon operator.  Unlike Green-output compatibility,
this statement applies to an arbitrary field of the selected carrier. -/
lemma homogeneous_solution_compat
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (field : 𝒯fr) (hfield : G.waveOperator field = 0) :
    D.kleinGordon (A.fieldMap field) = 0 := by
  rw [← A.waveOperator_compat field, hfield, map_zero]

/-- **Retarded uniqueness agrees on both carriers.**  A global Maxwell field
in the declared retarded sector that solves the intrinsic sourced equation is
the Maxwell retarded Green field.  Its encoded field is consequently the
Caticha/KG retarded solution and solves the encoded source equation. -/
lemma unique_retarded_common_carrier
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (field : 𝒯fr) (source : 𝒬er) (hfield : field ∈ G.retardedSector)
    (hsolves : PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
      I g cov sign frame (G.realizeField field) (G.realizeSource source)) :
    field = G.retarded source ∧
      A.fieldMap field = D.retarded (A.sourceMap source) ∧
      D.kleinGordon (A.fieldMap field) = A.sourceMap source := by
  have hunique :=
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves
      I G field source hfield hsolves
  subst field
  exact ⟨rfl, A.retarded_compat source,
    A.waveOperator_compat (G.retarded source) ▸ congrArg A.sourceMap (G.wave_retarded source)⟩

/-! # E. Atlas-independent causal AQFT evolution -/

/-- **Atlas-independent Caticha--AQFT--Maxwell causal capstone.**  The shared
causal field constructed with the global connection selected by one compatible
local Levi--Civita atlas solves the intrinsic Maxwell equation for the global
connection selected by any other such atlas.  Its Caticha/KG and Hadamard
properties are unchanged.  Green existence, regularity, the common-carrier
adapter, and microlocal data remain explicit premises. -/
lemma causal_hadamard_localAtlas_chain
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {α β : Type*}
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (L : PseudoRiemannianMetric.LocalLeviCivitaAtlasData I g α)
    (L' : PseudoRiemannianMetric.LocalLeviCivitaAtlasData I g β)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData I g
      (L'.covariantDerivative (I := I)) sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er)
    (hfield : ∀ x, MDiffAt
      (T% (G.realizeField
        (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
          I G source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (PseudoRiemannianMetric.firstCovariantSection I
        (L'.covariantDerivative (I := I)) (frame i)
        (G.realizeField
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x)
    {Ξ : Type uXi} (Q : ContinuumHadamardTwoPoint 𝒯c Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport Q.positiveFrequencyCone
      Q.positiveFrequencyCone) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g
        (L.covariantDerivative (I := I)) sign frame
        (G.realizeField
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source)) 0 ∧
      A.fieldMap
          (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator
            I G source) =
        D.causalPropagator (A.sourceMap source) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.causalPropagator (A.sourceMap source))) = 0 ∧
      IsHermitianTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsPositiveTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
          (D.causalHadamardCarrier Q transport hcone).twoPoint
          (D.causalHadamardCarrier Q transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
          (D.causalHadamardCarrier Q transport hcone).wavefront
          (D.causalHadamardCarrier Q transport hcone).positiveFrequencyCone := by
  have hQ := D.causalHadamardCarrier_properties Q transport hcone
  exact
    ⟨IntrinsicMaxwellGreenData.causalPropagator_solves_homogeneous_for_localLeviCivitaAtlas
        I L L' G source hfield hframe hNablaFrame hbracket,
      causalPropagator_compat I D G A source,
      D.caticha_causalPropagator_is_homogeneous (A.sourceMap source),
      hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩

/-! # F. Two-sided sourced evolution across compatible atlases -/

/-- **Atlas-independent retarded/advanced common carrier.**  The retarded and
advanced fields constructed using one globally selected local Levi--Civita
atlas solve the sourced intrinsic Maxwell equation for any other compatible
atlas.  Both fields map to their Caticha/KG Green solutions, and Caticha
evolution of each descends to the same encoded source generator.

The Green operators and the regularity of both realized fields remain explicit
analytic premises. -/
lemma retarded_advanced_localAtlas_common_carrier
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {α β : Type*}
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (L : PseudoRiemannianMetric.LocalLeviCivitaAtlasData I g α)
    (L' : PseudoRiemannianMetric.LocalLeviCivitaAtlasData I g β)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData I g
      (L'.covariantDerivative (I := I)) sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (source : 𝒬er)
    (hRetField : ∀ x, MDiffAt (T% (G.realizeField (G.retarded source))) x)
    (hAdvField : ∀ x, MDiffAt (T% (G.realizeField (G.advanced source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hRetNablaFrame : ∀ i x, MDiffAt
      (T% (PseudoRiemannianMetric.firstCovariantSection I
        (L'.covariantDerivative (I := I)) (frame i)
        (G.realizeField (G.retarded source)))) x)
    (hAdvNablaFrame : ∀ i x, MDiffAt
      (T% (PseudoRiemannianMetric.firstCovariantSection I
        (L'.covariantDerivative (I := I)) (frame i)
        (G.realizeField (G.advanced source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g
        (L.covariantDerivative (I := I)) sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g
        (L.covariantDerivative (I := I)) sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      A.fieldMap (G.retarded source) = D.retarded (A.sourceMap source) ∧
      A.fieldMap (G.advanced source) = D.advanced (A.sourceMap source) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.retarded (A.sourceMap source))) =
        D.sourceGenerator (A.sourceMap source) ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (D.advanced (A.sourceMap source))) =
        D.sourceGenerator (A.sourceMap source) := by
  have hret :=
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_localLeviCivitaAtlas
      I L L' G source hRetField hframe hRetNablaFrame hbracket
  have hadv : PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn I g
      (L.covariantDerivative (I := I)) sign frame
      (G.realizeField (G.advanced source)) (G.realizeSource source) :=
    (PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff
      I g L L' sign frame (G.realizeField (G.advanced source))
      (G.realizeSource source) hAdvField hframe hAdvNablaFrame hbracket).mpr
        (PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves I G source)
  exact ⟨hret, hadv, A.retarded_compat source, A.advanced_compat source,
    D.caticha_retarded_intertwines_source (A.sourceMap source),
    D.caticha_advanced_intertwines_source (A.sourceMap source)⟩

end ContinuumCatichaIntrinsicMaxwellAdapter

/-! # G. Optional advanced uniqueness -/

/-- Additional analytic data selecting an advanced support/boundary-condition
sector.  It is kept separate from `IntrinsicMaxwellGreenData`, so existing
retarded-only Green constructions need no stronger hypotheses. -/
structure AdvancedUniqueIntrinsicMaxwellData
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr) where
  /-- The subspace carrying the advanced support or boundary condition. -/
  advancedSector : Submodule ℝ 𝒯fr
  /-- Advanced Green solutions lie in the selected advanced sector. -/
  advanced_mem : ∀ source, G.advanced source ∈ advancedSector
  /-- The wave operator is injective after imposing the advanced condition. -/
  wave_injectiveOn_advanced : Set.InjOn G.waveOperator advancedSector

namespace AdvancedUniqueIntrinsicMaxwellData

/-- Within an explicitly selected advanced sector, the advanced Green field is
the unique solution of the intrinsic sourced Maxwell equation. -/
lemma eq_advanced_of_solves
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (U : AdvancedUniqueIntrinsicMaxwellData I G)
    (field : 𝒯fr) (source : 𝒬er) (hfield : field ∈ U.advancedSector)
    (hsolves : PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
      I g cov sign frame (G.realizeField field) (G.realizeSource source)) :
    field = G.advanced source := by
  have hop :
      PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOperator
          I g cov sign frame (G.realizeField field) = G.realizeSource source :=
    (PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq
      I g cov sign frame (G.realizeField field) (G.realizeSource source)).mp hsolves
  have hWave : G.waveOperator field = source := G.realizeSource_injective <| by
    rw [G.realizes_wave]
    exact hop
  exact U.wave_injectiveOn_advanced hfield (U.advanced_mem source) <| by
    rw [hWave, G.wave_advanced source]

/-- **Advanced uniqueness agrees on both carriers.**  Once an explicit
advanced sector is supplied, every advanced-sector Maxwell solution equals
the advanced Green field; its image is consequently the Caticha/KG advanced
solution and its functional evolution yields the encoded source generator. -/
lemma unique_advanced_common_carrier
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    (G : PseudoRiemannianMetric.IntrinsicMaxwellGreenData
      I g cov sign frame 𝒬er 𝒯fr)
    (A : ContinuumCatichaIntrinsicMaxwellAdapter I D G)
    (U : AdvancedUniqueIntrinsicMaxwellData I G)
    (field : 𝒯fr) (source : 𝒬er) (hfield : field ∈ U.advancedSector)
    (hsolves : PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
      I g cov sign frame (G.realizeField field) (G.realizeSource source)) :
    field = G.advanced source ∧
      A.fieldMap field = D.advanced (A.sourceMap source) ∧
      D.kleinGordon (A.fieldMap field) = A.sourceMap source ∧
      D.kleinGordon
          (continuumSmearedSchrodingerGenerator D.lapse D.shift
            D.Hperp D.Hi (A.fieldMap field)) =
        D.sourceGenerator (A.sourceMap source) := by
  have hunique := U.eq_advanced_of_solves I G field source hfield hsolves
  subst field
  rw [A.advanced_compat source]
  exact ⟨rfl, rfl, D.kleinGordon_advanced (A.sourceMap source),
    D.caticha_advanced_intertwines_source (A.sourceMap source)⟩

end AdvancedUniqueIntrinsicMaxwellData

/-! # H. Local AQFT observables on the continuum source carrier -/

/-- Explicit localization of continuum Caticha/KG sources in a supplied AQFT
local net.  The observable map need not be inferred from a two-point function:
localization and algebra membership are recorded as independent data. -/
structure ContinuumSourceLocalNetAdapter
    {A : Type*} [Monoid A] {region : Type*} [Preorder region]
    (N : LocalNet A region) where
  /-- Sources localized in each spacetime region. -/
  localizedSource : region → Submodule ℂ 𝒾c
  /-- The observable associated with a continuum source. -/
  sourceObservable : 𝒾c → A
  /-- Source localization is isotone. -/
  localized_isotony : ∀ {O₁ O₂ : region},
    O₁ ≤ O₂ → localizedSource O₁ ≤ localizedSource O₂
  /-- A localized source produces an observable in the corresponding algebra. -/
  observable_mem : ∀ {O : region} {source : 𝒾c},
    source ∈ localizedSource O → sourceObservable source ∈ N.alg O

namespace ContinuumSourceLocalNetAdapter

/-- Isotony is respected simultaneously by source localization and by the
local observable net. -/
lemma localized_source_observable_isotony
    {A : Type*} [Monoid A] {region : Type*} [Preorder region]
    (N : LocalNet A region) (L : ContinuumSourceLocalNetAdapter N)
    {O₁ O₂ : region} (hO : O₁ ≤ O₂) {source : 𝒾c}
    (hsource : source ∈ L.localizedSource O₁) :
    source ∈ L.localizedSource O₂ ∧ L.sourceObservable source ∈ N.alg O₂ :=
  ⟨L.localized_isotony hO hsource,
    N.isotony hO (L.observable_mem hsource)⟩

/-- **Caticha--Hadamard--local-net bridge.**  The pulled-back continuum
Hadamard carrier retains its Hermitian, positive, CCR, and microlocal
properties, while observables associated with sources localized in causally
disjoint regions commute by the supplied local net's locality axiom.

This theorem does not construct a Haag--Kastler net from a two-point function;
the localization/observable adapter and local net remain explicit premises. -/
lemma causalHadamard_localNet_properties
    {A : Type*} [Monoid A] {region : Type*} [Preorder region]
    (D : ContinuumCatichaKGData 𝒯c 𝒾c)
    {Ξ : Type uXi} (Q : ContinuumHadamardTwoPoint 𝒯c Ξ)
    (transport : Ξ → Ξ)
    (hcone : Set.MapsTo transport Q.positiveFrequencyCone
      Q.positiveFrequencyCone)
    (N : LocalNet A region) (L : ContinuumSourceLocalNetAdapter N)
    {O₁ O₂ : region} (hcausal : O₁ ≤ N.compl O₂)
    {φ ψ : 𝒾c} (hφ : φ ∈ L.localizedSource O₁)
    (hψ : ψ ∈ L.localizedSource O₂) :
    IsHermitianTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsPositiveTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint ∧
      IsCCRCompatibleTwoPoint
        (D.causalHadamardCarrier Q transport hcone).twoPoint
        (D.causalHadamardCarrier Q transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (D.causalHadamardCarrier Q transport hcone).wavefront
        (D.causalHadamardCarrier Q transport hcone).positiveFrequencyCone ∧
      L.sourceObservable φ * L.sourceObservable ψ =
        L.sourceObservable ψ * L.sourceObservable φ := by
  have hQ := D.causalHadamardCarrier_properties Q transport hcone
  have hcomm := N.locality hcausal (L.observable_mem hφ)
    (L.sourceObservable ψ) (L.observable_mem hψ)
  exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2, hcomm.symm⟩

end ContinuumSourceLocalNetAdapter

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram

end
