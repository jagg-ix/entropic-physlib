/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SmoothLorentzianDirectLimit
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaIntrinsicMaxwellGreen
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality
public import
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure
public import
  Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
meta import Zil

/-!
# Energy construction of causal Maxwell Green operators and Hadamard propagation

The intrinsic Maxwell layer already proves the geometric operator identity,
and `WellPosedIntrinsicMaxwellCauchyData` proves linearity once causal
solution selectors and uniqueness are available.  This module moves the
analytic boundary one step earlier.

`MaxwellEnergyCauchyData` contains no retarded or advanced solution map.
Instead it records the standard output of a globally-hyperbolic energy
argument:

* existence in the retarded and advanced support subspaces; and
* an a priori estimate on each support subspace.

The estimate proves uniqueness.  Classical choice then selects solutions,
and the existing uniqueness argument proves that both selectors are linear.
Thus the retarded/advanced Green operators are constructed, rather than
stored as structure fields.

The final theorem composes those constructed operators with the repository's
localized-Fourier transport.  Exact equality with the positive-frequency
Hadamard cone is therefore derived from regularity off the cone, singularity
on it, and transported Fourier pairings.  It is not copied into a
certificate.

This is the correct division of labour.  The smooth direct-limit module
constructs the Lorentzian manifold and metric.  A concrete normally
hyperbolic PDE proof may establish the two existence and two energy-estimate
fields directly, or supply the closed causal Sobolev sectors and coercive
weak forms of `MaxwellLaxMilgramGraphData`.  In the latter route,
Lax--Milgram constructs existence and the graph-norm estimates.  Global
hyperbolicity as a topological predicate alone still cannot do that.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle FiberBundle Module
open scoped InnerProductSpace Manifold SchwartzMap

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity

namespace GloballyHyperbolicGreenHadamard

open PseudoRiemannianMetric
open
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter
open
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
open
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality
open
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

universe uS uT uA uD v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

variable {d : ℕ}
variable {g : PseudoRiemannianMetric E H M n I}
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {sign : Fin d → ℝ}
variable {frame : Fin d → ∀ x : M, TangentSpace I x}

/-! ## A. Energy estimates construct the Green operators -/

/-- Analytic output of a globally-hyperbolic Maxwell Cauchy theorem.

There are deliberately no Green maps in this structure.  The causal
solutions are obtained from existence, while the energy estimates force
uniqueness on the two causal support sectors. -/
structure MaxwellEnergyCauchyData
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝒮 : Type uS) (𝒯 : Type uT)
    [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
    [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯] where
  realizeField : 𝒯 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource : 𝒮 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource_injective : Function.Injective realizeSource
  waveOperator : 𝒯 →L[ℝ] 𝒮
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  retardedSector : Submodule ℝ 𝒯
  advancedSector : Submodule ℝ 𝒯
  retarded_exists :
    ∀ source, ∃ u : 𝒯, u ∈ retardedSector ∧ waveOperator u = source
  advanced_exists :
    ∀ source, ∃ u : 𝒯, u ∈ advancedSector ∧ waveOperator u = source
  retardedEnergyConstant : ℝ
  advancedEnergyConstant : ℝ
  retarded_energy_estimate :
    ∀ u ∈ retardedSector,
      ‖u‖ ≤ retardedEnergyConstant * ‖waveOperator u‖
  advanced_energy_estimate :
    ∀ u ∈ advancedSector,
      ‖u‖ ≤ advancedEnergyConstant * ‖waveOperator u‖

/-! ## A.1. Time reversal reduces two-sided Cauchy theory to one side -/

/-- The retarded half of a globally-hyperbolic Maxwell energy theorem.

For a time-reversal-invariant wave equation this is the only independent
analytic Cauchy theorem: the advanced half is obtained by conjugating the
retarded solution with time reversal.  Keeping this carrier separate makes
that reduction visible instead of storing two duplicated PDE assumptions. -/
structure RetardedMaxwellEnergyCauchyData
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝒮 : Type uS) (𝒯 : Type uT)
    [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
    [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯] where
  realizeField : 𝒯 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource : 𝒮 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource_injective : Function.Injective realizeSource
  waveOperator : 𝒯 →L[ℝ] 𝒮
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  retardedSector : Submodule ℝ 𝒯
  retarded_exists :
    ∀ source, ∃ u : 𝒯, u ∈ retardedSector ∧ waveOperator u = source
  retardedEnergyConstant : ℝ
  retarded_energy_estimate :
    ∀ u ∈ retardedSector,
      ‖u‖ ≤ retardedEnergyConstant * ‖waveOperator u‖

/-- Isometric time-reversal covariance of a retarded Maxwell energy problem.

The two involutions act on sources and fields, intertwine the wave operator,
and exchange the retarded and advanced support sectors.  Isometry is the
analytic input that transports the retarded energy estimate with the same
constant. -/
structure MaxwellTimeReversalData
    {𝒮 : Type uS} {𝒯 : Type uT}
    [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
    [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) where
  sourceTimeReversal : 𝒮 ≃ₗᵢ[ℝ] 𝒮
  fieldTimeReversal : 𝒯 ≃ₗᵢ[ℝ] 𝒯
  source_involutive :
    ∀ source, sourceTimeReversal (sourceTimeReversal source) = source
  field_involutive :
    ∀ field, fieldTimeReversal (fieldTimeReversal field) = field
  wave_intertwines :
    ∀ field,
      D.waveOperator (fieldTimeReversal field) =
        sourceTimeReversal (D.waveOperator field)
  advancedSector : Submodule ℝ 𝒯
  retarded_to_advanced :
    ∀ field, field ∈ D.retardedSector →
      fieldTimeReversal field ∈ advancedSector
  advanced_to_retarded :
    ∀ field, field ∈ advancedSector →
      fieldTimeReversal field ∈ D.retardedSector

/-- Complex covariance required only on the retarded half of the Maxwell
Cauchy problem.  Advanced-sector complex stability will be derived from
conjugate-linear time reversal. -/
structure RetardedMaxwellComplexDomain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜) : Prop where
  wave_smul : ∀ c : ℂ, ∀ field,
    D.waveOperator (c • field) = c • D.waveOperator field
  retardedSector_smul : ∀ c : ℂ, ∀ field,
    field ∈ D.retardedSector → c • field ∈ D.retardedSector

/-- Wigner conjugate-linearity of time reversal on the common complex
source/field carrier.  The underlying maps remain real-linear isometries,
as recorded by `MaxwellTimeReversalData`. -/
structure MaxwellComplexTimeReversalData
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (T : MaxwellTimeReversalData I D) : Prop where
  source_smul : ∀ c : ℂ, ∀ source,
    T.sourceTimeReversal (c • source) =
      (star c) • T.sourceTimeReversal source
  field_smul : ∀ c : ℂ, ∀ field,
    T.fieldTimeReversal (c • field) =
      (star c) • T.fieldTimeReversal field

/-- Complex-domain compatibility for an energy-constructed Maxwell Cauchy
problem on a common source/field carrier.

Only the differential operator's complex covariance and stability of the
two causal sectors under complex scalars are recorded.  Complex-linearity of
the selected retarded and advanced solutions is derived from causal
uniqueness below. -/
structure MaxwellEnergyComplexDomain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜) : Prop where
  wave_smul : ∀ c : ℂ, ∀ field,
    D.waveOperator (c • field) = c • D.waveOperator field
  retardedSector_smul : ∀ c : ℂ, ∀ field,
    field ∈ D.retardedSector → c • field ∈ D.retardedSector
  advancedSector_smul : ∀ c : ℂ, ∀ field,
    field ∈ D.advancedSector → c • field ∈ D.advancedSector

/-! ## A.2. Coercive sector equivalences discharge the energy fields -/

/-- A concrete coercive realization of the two causal Cauchy problems.

The continuous linear equivalences are the standard endpoint of a
normally-hyperbolic existence, uniqueness, and open-mapping argument: the
wave operator restricted to either causal support sector is an isomorphism
onto the source space.  Unlike `MaxwellEnergyCauchyData`, this structure does
not store existence or estimates.  Both are derived from the inverse
operators and their operator norms. -/
structure MaxwellCoerciveSectorData
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝒮 : Type uS) (𝒯 : Type uT)
    [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
    [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯] where
  realizeField : 𝒯 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource : 𝒮 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource_injective : Function.Injective realizeSource
  waveOperator : 𝒯 →L[ℝ] 𝒮
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  retardedSector : Submodule ℝ 𝒯
  advancedSector : Submodule ℝ 𝒯
  retardedWaveEquiv : retardedSector ≃L[ℝ] 𝒮
  advancedWaveEquiv : advancedSector ≃L[ℝ] 𝒮
  retardedWaveEquiv_apply :
    ∀ u, retardedWaveEquiv u = waveOperator u.1
  advancedWaveEquiv_apply :
    ∀ u, advancedWaveEquiv u = waveOperator u.1

/-! ## A.3. Closed Sobolev graph domains and Lax--Milgram construction -/

/-- The complete continuum `H¹(ℝ³; ℂ⁴)` Cauchy-slice carrier used below.

Each component is the repository's Bessel-potential `H¹` Hilbert carrier,
not a finite-mode approximation.  A curved chart or global bundle
realization is supplied separately by `realizeField`. -/
abbrev MaxwellHOneFour : Type :=
  PiLp 2 fun _ : Fin 4 =>
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree

/-- The Riesz coordinate for `H⁻¹(ℝ³; ℂ⁴)` sources.

The underlying Hilbert type agrees with `MaxwellHOneFour`; its interpretation
as the dual source coordinate is fixed by the source Riesz equivalences in
`MaxwellLaxMilgramGraphData`. -/
abbrev MaxwellHMinusOneFour : Type := MaxwellHOneFour

/-- Closed causal Sobolev sectors equipped with the weak gauge-fixed Maxwell
forms needed by Lax--Milgram.

This structure does **not** store Green operators, causal existence, or
energy estimates.  It stores the analytic hypotheses that a concrete
globally-hyperbolic Maxwell PDE proof has to establish:

* closed retarded and advanced subspaces of the Hilbert field carrier;
* bounded weak Maxwell forms and explicit positive energy lower bounds on
  those subspaces;
* Riesz coordinates for the source duals; and
* identification of those weak forms with the intrinsic Ricci-coupled
  Maxwell operator.

Lax--Milgram constructs both restricted wave equivalences below.  The
existing coercive-sector layer then derives causal solutions, uniqueness,
continuous Green operators, and quantitative energy estimates. -/
structure MaxwellLaxMilgramGraphData
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x)
    (𝒮 : Type uS) (𝒯 : Type uT)
    [NormedAddCommGroup 𝒮] [InnerProductSpace ℝ 𝒮]
    [NormedAddCommGroup 𝒯] [InnerProductSpace ℝ 𝒯]
    [CompleteSpace 𝒯] where
  realizeField : 𝒯 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource : 𝒮 →ₗ[ℝ] (∀ x : M, TangentSpace I x)
  realizeSource_injective : Function.Injective realizeSource
  waveOperator : 𝒯 →L[ℝ] 𝒮
  realizes_wave : ∀ u,
    realizeSource (waveOperator u) =
      intrinsicRicciCoupledMaxwellOperator I g cov sign frame (realizeField u)
  retardedSector : Submodule ℝ 𝒯
  advancedSector : Submodule ℝ 𝒯
  retardedSector_closed : IsClosed (retardedSector : Set 𝒯)
  advancedSector_closed : IsClosed (advancedSector : Set 𝒯)
  retardedSourceRiesz : 𝒮 ≃L[ℝ] retardedSector
  advancedSourceRiesz : 𝒮 ≃L[ℝ] advancedSector
  retardedForm :
    retardedSector →L[ℝ] retardedSector →L[ℝ] ℝ
  advancedForm :
    advancedSector →L[ℝ] advancedSector →L[ℝ] ℝ
  retardedCoercivityConstant : ℝ
  retardedCoercivityConstant_pos : 0 < retardedCoercivityConstant
  retarded_energy_lower : ∀ u,
    retardedCoercivityConstant * ‖u‖ * ‖u‖ ≤ retardedForm u u
  advancedCoercivityConstant : ℝ
  advancedCoercivityConstant_pos : 0 < advancedCoercivityConstant
  advanced_energy_lower : ∀ u,
    advancedCoercivityConstant * ‖u‖ * ‖u‖ ≤ advancedForm u u
  retarded_weak_operator :
    ∀ (u : retardedSector) (v : retardedSector),
      ⟪retardedSourceRiesz (waveOperator u.1), v⟫_ℝ =
        retardedForm u v
  advanced_weak_operator :
    ∀ (u : advancedSector) (v : advancedSector),
      ⟪advancedSourceRiesz (waveOperator u.1), v⟫_ℝ =
        advancedForm u v

/-- The graph-domain carrier specialized to the repository's genuine
continuum `H¹(ℝ³; ℂ⁴)` Cauchy data and Rieszized `H⁻¹` sources. -/
abbrev CurvedMaxwellHOneGraphData
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (sign : Fin d → ℝ)
    (frame : Fin d → ∀ x : M, TangentSpace I x) :=
  MaxwellLaxMilgramGraphData I g cov sign frame
    MaxwellHMinusOneFour MaxwellHOneFour

namespace MaxwellLaxMilgramGraphData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [InnerProductSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [InnerProductSpace ℝ 𝒯]
variable [CompleteSpace 𝒯]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The retarded Lax--Milgram coercivity proposition is derived from the
explicit positive energy constant and lower estimate stored in the analytic
Maxwell datum. -/
lemma retardedCoercive
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    IsCoercive D.retardedForm :=
  ⟨D.retardedCoercivityConstant, D.retardedCoercivityConstant_pos,
    D.retarded_energy_lower⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The advanced Lax--Milgram coercivity proposition is likewise derived
from its quantitative energy estimate. -/
lemma advancedCoercive
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    IsCoercive D.advancedForm :=
  ⟨D.advancedCoercivityConstant, D.advancedCoercivityConstant_pos,
    D.advanced_energy_lower⟩

/-- The retarded weak Maxwell operator is a continuous linear equivalence.
Surjectivity, injectivity, and bounded inverse are Lax--Milgram conclusions,
not certificate fields. -/
noncomputable def retardedWaveEquiv
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    D.retardedSector ≃L[ℝ] 𝒮 := by
  letI : CompleteSpace D.retardedSector :=
    D.retardedSector_closed.completeSpace_coe
  exact D.retardedCoercive.continuousLinearEquivOfBilin.trans
    D.retardedSourceRiesz.symm

/-- The advanced weak Maxwell operator is a continuous linear equivalence,
again constructed by Lax--Milgram. -/
noncomputable def advancedWaveEquiv
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    D.advancedSector ≃L[ℝ] 𝒮 := by
  letI : CompleteSpace D.advancedSector :=
    D.advancedSector_closed.completeSpace_coe
  exact D.advancedCoercive.continuousLinearEquivOfBilin.trans
    D.advancedSourceRiesz.symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma retardedWaveEquiv_apply
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (u : D.retardedSector) :
    D.retardedWaveEquiv I u = D.waveOperator u.1 := by
  letI : CompleteSpace D.retardedSector :=
    D.retardedSector_closed.completeSpace_coe
  have hweak :
      D.retardedSourceRiesz (D.waveOperator u.1) =
        D.retardedCoercive.continuousLinearEquivOfBilin u :=
    D.retardedCoercive.unique_continuousLinearEquivOfBilin
      (D.retarded_weak_operator u)
  apply D.retardedSourceRiesz.injective
  simpa [retardedWaveEquiv] using hweak.symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma advancedWaveEquiv_apply
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (u : D.advancedSector) :
    D.advancedWaveEquiv I u = D.waveOperator u.1 := by
  letI : CompleteSpace D.advancedSector :=
    D.advancedSector_closed.completeSpace_coe
  have hweak :
      D.advancedSourceRiesz (D.waveOperator u.1) =
        D.advancedCoercive.continuousLinearEquivOfBilin u :=
    D.advancedCoercive.unique_continuousLinearEquivOfBilin
      (D.advanced_weak_operator u)
  apply D.advancedSourceRiesz.injective
  simpa [advancedWaveEquiv] using hweak.symm

/-- Lax--Milgram discharges the two restricted wave-isomorphism fields of
the existing coercive causal Maxwell carrier. -/
@[zil_level physical_theorem]
noncomputable def toCoerciveSectorData
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator
  realizes_wave := D.realizes_wave
  retardedSector := D.retardedSector
  advancedSector := D.advancedSector
  retardedWaveEquiv := D.retardedWaveEquiv I
  advancedWaveEquiv := D.advancedWaveEquiv I
  retardedWaveEquiv_apply := D.retardedWaveEquiv_apply I
  advancedWaveEquiv_apply := D.advancedWaveEquiv_apply I

/-- The `H¹`/`H⁻¹` graph norm of a field for the intrinsic Maxwell wave
operator.  On a concrete Sobolev carrier this is the standard sum norm on
the operator graph. -/
def graphNorm
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (u : 𝒯) : ℝ :=
  ‖u‖ + ‖D.waveOperator u‖

/-- Retarded causal existence together with the quantitative Maxwell graph
norm estimate.  The solution and the constant are constructed from the
Lax--Milgram inverse. -/
@[zil_level physical_theorem]
theorem retarded_exists_graphNorm_estimate
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ∃ u : 𝒯,
      u ∈ D.retardedSector ∧
      D.waveOperator u = source ∧
      D.graphNorm I u ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField u) (D.realizeSource source) := by
  let us : D.retardedSector := (D.retardedWaveEquiv I).symm source
  have hwave : D.waveOperator us.1 = source := by
    rw [← D.retardedWaveEquiv_apply I us]
    exact (D.retardedWaveEquiv I).apply_symm_apply source
  have hnorm :=
    (D.retardedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  refine ⟨us.1, us.2, hwave, ?_, ?_⟩
  · rw [graphNorm, hwave]
    calc
      ‖us.1‖ + ‖source‖ = ‖us‖ + ‖source‖ := rfl
      _ ≤
          ‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ *
              ‖source‖ + ‖source‖ :=
        add_le_add hnorm le_rfl
      _ =
          (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ := by ring
  · rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
    simpa only [hwave] using (D.realizes_wave us.1).symm

/-- Advanced causal existence and the matching graph-norm energy estimate. -/
@[zil_level physical_theorem]
theorem advanced_exists_graphNorm_estimate
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ∃ u : 𝒯,
      u ∈ D.advancedSector ∧
      D.waveOperator u = source ∧
      D.graphNorm I u ≤
        (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField u) (D.realizeSource source) := by
  let us : D.advancedSector := (D.advancedWaveEquiv I).symm source
  have hwave : D.waveOperator us.1 = source := by
    rw [← D.advancedWaveEquiv_apply I us]
    exact (D.advancedWaveEquiv I).apply_symm_apply source
  have hnorm :=
    (D.advancedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  refine ⟨us.1, us.2, hwave, ?_, ?_⟩
  · rw [graphNorm, hwave]
    calc
      ‖us.1‖ + ‖source‖ = ‖us‖ + ‖source‖ := rfl
      _ ≤
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ *
              ‖source‖ + ‖source‖ :=
        add_le_add hnorm le_rfl
      _ =
          (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ := by ring
  · rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
    simpa only [hwave] using (D.realizes_wave us.1).symm

/-- The concrete curved Sobolev/graph-norm Maxwell theorem.

Closed causal Sobolev sectors, coercive weak forms, and their intrinsic
geometric identification construct both causal solutions, their graph-norm
energy estimates, and the repository's global Green carrier. -/
@[zil_level physical_theorem]
theorem curvedSobolevGraphMaxwell_causal_exists_energy
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (∃ u : 𝒯,
        u ∈ D.retardedSector ∧
        D.waveOperator u = source ∧
        D.graphNorm I u ≤
          (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ ∧
        IntrinsicRicciCoupledMaxwellOn I g cov sign frame
          (D.realizeField u) (D.realizeSource source)) ∧
    (∃ u : 𝒯,
        u ∈ D.advancedSector ∧
        D.waveOperator u = source ∧
        D.graphNorm I u ≤
          (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ ∧
        IntrinsicRicciCoupledMaxwellOn I g cov sign frame
          (D.realizeField u) (D.realizeSource source)) :=
  ⟨D.retarded_exists_graphNorm_estimate I source,
    D.advanced_exists_graphNorm_estimate I source⟩

/-- Concrete specialization of the curved graph-domain theorem to
`H¹(ℝ³; ℂ⁴) → H⁻¹(ℝ³; ℂ⁴)`.

The theorem is infinite-dimensional and pointwise-continuum through the
Bessel-potential carrier.  The curved field/source realization, causal
support closure, coercivity, and weak-operator identity remain explicit in
`D`. -/
@[zil_level physical_theorem]
theorem curvedHOneFourMaxwell_causal_exists_energy
    (D : CurvedMaxwellHOneGraphData I g cov sign frame)
    (source : MaxwellHMinusOneFour) :
    (∃ u : MaxwellHOneFour,
        u ∈ D.retardedSector ∧
        D.waveOperator u = source ∧
        D.graphNorm I u ≤
          (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ ∧
        IntrinsicRicciCoupledMaxwellOn I g cov sign frame
          (D.realizeField u) (D.realizeSource source)) ∧
    (∃ u : MaxwellHOneFour,
        u ∈ D.advancedSector ∧
        D.waveOperator u = source ∧
        D.graphNorm I u ≤
          (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
            ‖source‖ ∧
        IntrinsicRicciCoupledMaxwellOn I g cov sign frame
          (D.realizeField u) (D.realizeSource source)) :=
  D.curvedSobolevGraphMaxwell_causal_exists_energy I source

end MaxwellLaxMilgramGraphData

namespace RetardedMaxwellEnergyCauchyData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]

/-- A chosen retarded solution.  Its linearity is not assumed; it follows
after the energy estimate supplies causal uniqueness. -/
noncomputable def retardedSolution
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) : 𝒯 :=
  Classical.choose (D.retarded_exists source)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma retardedSolution_mem
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.retardedSolution I source ∈ D.retardedSector :=
  (Classical.choose_spec (D.retarded_exists source)).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_retardedSolution
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.retardedSolution I source) = source :=
  (Classical.choose_spec (D.retarded_exists source)).2

end RetardedMaxwellEnergyCauchyData

namespace MaxwellTimeReversalData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]

/-- The advanced solution obtained by time-reversing the retarded solution
of the time-reversed source. -/
noncomputable def advancedSolution
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D)
    (source : 𝒮) : 𝒯 :=
  T.fieldTimeReversal
    (D.retardedSolution I (T.sourceTimeReversal source))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma advancedSolution_mem
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D)
    (source : 𝒮) :
    T.advancedSolution I D source ∈ T.advancedSector :=
  T.retarded_to_advanced _
    (D.retardedSolution_mem I (T.sourceTimeReversal source))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_advancedSolution
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D)
    (source : 𝒮) :
    D.waveOperator (T.advancedSolution I D source) = source := by
  rw [advancedSolution, T.wave_intertwines,
    D.wave_retardedSolution I, T.source_involutive]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Time reversal transports retarded existence to advanced existence. -/
lemma advanced_exists
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D)
    (source : 𝒮) :
    ∃ u : 𝒯, u ∈ T.advancedSector ∧ D.waveOperator u = source :=
  ⟨T.advancedSolution I D source, T.advancedSolution_mem I D source,
    T.wave_advancedSolution I D source⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The advanced estimate has exactly the retarded constant because both
time-reversal maps are isometries. -/
lemma advanced_energy_estimate
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D)
    (field : 𝒯) (hfield : field ∈ T.advancedSector) :
    ‖field‖ ≤
      D.retardedEnergyConstant * ‖D.waveOperator field‖ := by
  have h := D.retarded_energy_estimate
    (T.fieldTimeReversal field) (T.advanced_to_retarded field hfield)
  simpa only [T.fieldTimeReversal.norm_map, T.wave_intertwines,
    T.sourceTimeReversal.norm_map] using h

/-- A retarded energy theorem and isometric involutive time reversal produce
the full two-sided Maxwell energy Cauchy problem.  In particular, advanced
existence and its estimate are conclusions rather than duplicate analytic
premises. -/
@[zil_level physical_theorem]
noncomputable def toEnergyCauchyData
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (T : MaxwellTimeReversalData I D) :
    MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator
  realizes_wave := D.realizes_wave
  retardedSector := D.retardedSector
  advancedSector := T.advancedSector
  retarded_exists := D.retarded_exists
  advanced_exists := T.advanced_exists I D
  retardedEnergyConstant := D.retardedEnergyConstant
  advancedEnergyConstant := D.retardedEnergyConstant
  retarded_energy_estimate := D.retarded_energy_estimate
  advanced_energy_estimate := T.advanced_energy_estimate I D

variable {𝒜 : Type uS}
variable [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Conjugate-linear time reversal transports complex stability of the
retarded support sector to the advanced support sector. -/
lemma advancedSector_smul
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (T : MaxwellTimeReversalData I D)
    (C : RetardedMaxwellComplexDomain I D)
    (A : MaxwellComplexTimeReversalData I D T)
    (c : ℂ) (field : 𝒜) (hfield : field ∈ T.advancedSector) :
    c • field ∈ T.advancedSector := by
  have hretarded :
      T.fieldTimeReversal (c • field) ∈ D.retardedSector := by
    rw [A.field_smul]
    exact C.retardedSector_smul (star c) _
      (T.advanced_to_retarded field hfield)
  have hadvanced :=
    T.retarded_to_advanced
      (T.fieldTimeReversal (c • field)) hretarded
  simpa only [T.field_involutive] using hadvanced

/-- Retarded complex covariance and Wigner conjugate-linear time reversal
construct the full complex domain required by the Caticha--Maxwell carrier.
No independent advanced complex-stability premise remains. -/
@[zil_level physical_theorem]
noncomputable def toEnergyComplexDomain
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (T : MaxwellTimeReversalData I D)
    (C : RetardedMaxwellComplexDomain I D)
    (A : MaxwellComplexTimeReversalData I D T) :
    MaxwellEnergyComplexDomain I (T.toEnergyCauchyData I D) where
  wave_smul := C.wave_smul
  retardedSector_smul := C.retardedSector_smul
  advancedSector_smul :=
    MaxwellTimeReversalData.advancedSector_smul I D T C A

end MaxwellTimeReversalData

namespace MaxwellCoerciveSectorData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]

/-- A causal wave-operator isomorphism automatically supplies existence and
the sharp operator-norm energy estimates required by
`MaxwellEnergyCauchyData`. -/
@[zil_level physical_theorem]
noncomputable def toEnergyCauchyData
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯) :
    MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator
  realizes_wave := D.realizes_wave
  retardedSector := D.retardedSector
  advancedSector := D.advancedSector
  retarded_exists := by
    intro source
    refine ⟨(D.retardedWaveEquiv.symm source).1,
      (D.retardedWaveEquiv.symm source).2, ?_⟩
    calc
      D.waveOperator (D.retardedWaveEquiv.symm source).1 =
          D.retardedWaveEquiv (D.retardedWaveEquiv.symm source) :=
        (D.retardedWaveEquiv_apply _).symm
      _ = source := D.retardedWaveEquiv.apply_symm_apply source
  advanced_exists := by
    intro source
    refine ⟨(D.advancedWaveEquiv.symm source).1,
      (D.advancedWaveEquiv.symm source).2, ?_⟩
    calc
      D.waveOperator (D.advancedWaveEquiv.symm source).1 =
          D.advancedWaveEquiv (D.advancedWaveEquiv.symm source) :=
        (D.advancedWaveEquiv_apply _).symm
      _ = source := D.advancedWaveEquiv.apply_symm_apply source
  retardedEnergyConstant :=
    ‖D.retardedWaveEquiv.symm.toContinuousLinearMap‖
  advancedEnergyConstant :=
    ‖D.advancedWaveEquiv.symm.toContinuousLinearMap‖
  retarded_energy_estimate := by
    intro u hu
    let us : D.retardedSector := ⟨u, hu⟩
    have hle :=
      D.retardedWaveEquiv.symm.toContinuousLinearMap.le_opNorm
        (D.retardedWaveEquiv us)
    calc
      ‖u‖ = ‖us‖ := rfl
      _ = ‖D.retardedWaveEquiv.symm (D.retardedWaveEquiv us)‖ := by
        rw [D.retardedWaveEquiv.symm_apply_apply]
      _ ≤ ‖D.retardedWaveEquiv.symm.toContinuousLinearMap‖ *
          ‖D.retardedWaveEquiv us‖ := hle
      _ = ‖D.retardedWaveEquiv.symm.toContinuousLinearMap‖ *
          ‖D.waveOperator u‖ := by rw [D.retardedWaveEquiv_apply]
  advanced_energy_estimate := by
    intro u hu
    let us : D.advancedSector := ⟨u, hu⟩
    have hle :=
      D.advancedWaveEquiv.symm.toContinuousLinearMap.le_opNorm
        (D.advancedWaveEquiv us)
    calc
      ‖u‖ = ‖us‖ := rfl
      _ = ‖D.advancedWaveEquiv.symm (D.advancedWaveEquiv us)‖ := by
        rw [D.advancedWaveEquiv.symm_apply_apply]
      _ ≤ ‖D.advancedWaveEquiv.symm.toContinuousLinearMap‖ *
          ‖D.advancedWaveEquiv us‖ := hle
      _ = ‖D.advancedWaveEquiv.symm.toContinuousLinearMap‖ *
          ‖D.waveOperator u‖ := by rw [D.advancedWaveEquiv_apply]

end MaxwellCoerciveSectorData

namespace MaxwellEnergyCauchyData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]

/-- The retarded solution selected from the PDE existence theorem. -/
noncomputable def retardedSolution
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) : 𝒯 :=
  Classical.choose (D.retarded_exists source)

/-- The advanced solution selected from the PDE existence theorem. -/
noncomputable def advancedSolution
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) : 𝒯 :=
  Classical.choose (D.advanced_exists source)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma retardedSolution_mem
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.retardedSolution I source ∈ D.retardedSector :=
  (Classical.choose_spec (D.retarded_exists source)).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_retardedSolution
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.retardedSolution I source) = source :=
  (Classical.choose_spec (D.retarded_exists source)).2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma advancedSolution_mem
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.advancedSolution I source ∈ D.advancedSector :=
  (Classical.choose_spec (D.advanced_exists source)).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_advancedSolution
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.advancedSolution I source) = source :=
  (Classical.choose_spec (D.advanced_exists source)).2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The retarded energy estimate proves uniqueness in the retarded support
sector. -/
lemma wave_injectiveOn_retarded
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Set.InjOn D.waveOperator D.retardedSector := by
  intro u hu v hv huv
  have hmem : u - v ∈ D.retardedSector := D.retardedSector.sub_mem hu hv
  have hwave : D.waveOperator (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hle := D.retarded_energy_estimate (u - v) hmem
  rw [hwave, norm_zero, mul_zero] at hle
  have hnorm : ‖u - v‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The advanced energy estimate proves uniqueness in the advanced support
sector. -/
lemma wave_injectiveOn_advanced
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Set.InjOn D.waveOperator D.advancedSector := by
  intro u hu v hv huv
  have hmem : u - v ∈ D.advancedSector := D.advancedSector.sub_mem hu hv
  have hwave : D.waveOperator (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hle := D.advanced_energy_estimate (u - v) hmem
  rw [hwave, norm_zero, mul_zero] at hle
  have hnorm : ‖u - v‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Package the existence theorem and the uniqueness derived from the energy
estimate into the repository's causal Cauchy interface. -/
@[zil_level physical_theorem]
noncomputable def toWellPosedCauchyData
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    WellPosedIntrinsicMaxwellCauchyData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator.toLinearMap
  retardedSolution := D.retardedSolution I
  advancedSolution := D.advancedSolution I
  realizes_wave := D.realizes_wave
  wave_retarded := D.wave_retardedSolution I
  wave_advanced := D.wave_advancedSolution I
  retardedSector := D.retardedSector
  advancedSector := D.advancedSector
  retarded_mem := D.retardedSolution_mem I
  advanced_mem := D.advancedSolution_mem I
  wave_injectiveOn_retarded := D.wave_injectiveOn_retarded I
  wave_injectiveOn_advanced := D.wave_injectiveOn_advanced I

/-- The actual pair of linear Green operators constructed from energy
well-posedness. -/
@[zil_level physical_theorem]
noncomputable def toGreenData
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    IntrinsicMaxwellGreenData I g cov sign frame 𝒮 𝒯 :=
  (D.toWellPosedCauchyData I).toIntrinsicMaxwellGreenData

@[simp]
lemma toGreenData_retarded_apply
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).retarded source = D.retardedSolution I source := rfl

@[simp]
lemma toGreenData_advanced_apply
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).advanced source = D.advancedSolution I source := rfl

/-! ## A.3. Energy estimates produce continuous causal isomorphisms -/

/-- The wave operator restricted to the retarded support sector. -/
noncomputable def waveOnRetarded
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    D.retardedSector →L[ℝ] 𝒮 :=
  D.waveOperator.comp D.retardedSector.subtypeL

/-- The wave operator restricted to the advanced support sector. -/
noncomputable def waveOnAdvanced
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    D.advancedSector →L[ℝ] 𝒮 :=
  D.waveOperator.comp D.advancedSector.subtypeL

/-- The retarded solution selector as a linear map into its causal support
sector.  Linearity is derived from uniqueness, not assumed. -/
noncomputable def retardedSectorSolutionLinear
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →ₗ[ℝ] D.retardedSector where
  toFun := fun source =>
    ⟨D.retardedSolution I source, D.retardedSolution_mem I source⟩
  map_add' := fun source₁ source₂ => by
    apply Subtype.ext
    exact (D.toWellPosedCauchyData I).retardedSolution_add I source₁ source₂
  map_smul' := fun r source => by
    apply Subtype.ext
    exact (D.toWellPosedCauchyData I).retardedSolution_smul I r source

/-- The advanced solution selector as a linear map into its causal support
sector.  Linearity is derived from uniqueness, not assumed. -/
noncomputable def advancedSectorSolutionLinear
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →ₗ[ℝ] D.advancedSector where
  toFun := fun source =>
    ⟨D.advancedSolution I source, D.advancedSolution_mem I source⟩
  map_add' := fun source₁ source₂ => by
    apply Subtype.ext
    exact (D.toWellPosedCauchyData I).advancedSolution_add I source₁ source₂
  map_smul' := fun r source => by
    apply Subtype.ext
    exact (D.toWellPosedCauchyData I).advancedSolution_smul I r source

/-- The retarded energy estimate upgrades the uniqueness-constructed
solution selector to a bounded continuous linear map. -/
noncomputable def retardedSectorSolutionContinuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] D.retardedSector :=
  (D.retardedSectorSolutionLinear I).mkContinuous
    D.retardedEnergyConstant (by
      intro source
      have h := D.retarded_energy_estimate
        (D.retardedSolution I source) (D.retardedSolution_mem I source)
      change ‖D.retardedSolution I source‖ ≤
        D.retardedEnergyConstant * ‖source‖
      simpa only [D.wave_retardedSolution I source] using h)

/-- The advanced energy estimate upgrades the uniqueness-constructed
solution selector to a bounded continuous linear map. -/
noncomputable def advancedSectorSolutionContinuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] D.advancedSector :=
  (D.advancedSectorSolutionLinear I).mkContinuous
    D.advancedEnergyConstant (by
      intro source
      have h := D.advanced_energy_estimate
        (D.advancedSolution I source) (D.advancedSolution_mem I source)
      change ‖D.advancedSolution I source‖ ≤
        D.advancedEnergyConstant * ‖source‖
      simpa only [D.wave_advancedSolution I source] using h)

/-- The energy-constructed retarded Green operator as a continuous linear
map into the ambient field carrier. -/
noncomputable def retardedContinuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  D.retardedSector.subtypeL.comp
    (D.retardedSectorSolutionContinuous I)

/-- The energy-constructed advanced Green operator as a continuous linear
map into the ambient field carrier. -/
noncomputable def advancedContinuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  D.advancedSector.subtypeL.comp
    (D.advancedSectorSolutionContinuous I)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma retardedContinuous_apply
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.retardedContinuous I source = D.retardedSolution I source := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma advancedContinuous_apply
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.advancedContinuous I source = D.advancedSolution I source := rfl

/-- The linear retarded Green map constructed through causal uniqueness is
extensionally the bounded operator constructed from the energy estimate. -/
lemma toGreenData_retarded_eq_continuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    (D.toGreenData I).retarded = D.retardedContinuous I := by
  ext source
  rfl

/-- The linear advanced Green map constructed through causal uniqueness is
extensionally the bounded operator constructed from the energy estimate. -/
lemma toGreenData_advanced_eq_continuous
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    (D.toGreenData I).advanced = D.advancedContinuous I := by
  ext source
  rfl

/-- Direct retarded Green bound supplied by the causal energy estimate. -/
lemma norm_retardedContinuous_le
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ‖D.retardedContinuous I source‖ ≤
      D.retardedEnergyConstant * ‖source‖ := by
  rw [D.retardedContinuous_apply I source]
  simpa only [D.wave_retardedSolution I source] using
    D.retarded_energy_estimate
      (D.retardedSolution I source) (D.retardedSolution_mem I source)

/-- Direct advanced Green bound supplied by the causal energy estimate. -/
lemma norm_advancedContinuous_le
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ‖D.advancedContinuous I source‖ ≤
      D.advancedEnergyConstant * ‖source‖ := by
  rw [D.advancedContinuous_apply I source]
  simpa only [D.wave_advancedSolution I source] using
    D.advanced_energy_estimate
      (D.advancedSolution I source) (D.advancedSolution_mem I source)

/-- The retarded solution map is a left inverse to the restricted wave
operator because the energy estimate gives retarded-sector uniqueness. -/
lemma retardedSectorSolution_leftInverse
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Function.LeftInverse
      (D.retardedSectorSolutionContinuous I) (D.waveOnRetarded I) := by
  intro u
  apply Subtype.ext
  change D.retardedSolution I (D.waveOperator u.1) = u.1
  apply D.wave_injectiveOn_retarded I
  · exact D.retardedSolution_mem I _
  · exact u.2
  · exact D.wave_retardedSolution I (D.waveOperator u.1)

/-- The retarded solution map is a right inverse to the restricted wave
operator by causal source existence. -/
lemma retardedSectorSolution_rightInverse
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Function.RightInverse
      (D.retardedSectorSolutionContinuous I) (D.waveOnRetarded I) := by
  intro source
  change D.waveOperator (D.retardedSolution I source) = source
  exact D.wave_retardedSolution I source

/-- The advanced solution map is a left inverse to the restricted wave
operator because the energy estimate gives advanced-sector uniqueness. -/
lemma advancedSectorSolution_leftInverse
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Function.LeftInverse
      (D.advancedSectorSolutionContinuous I) (D.waveOnAdvanced I) := by
  intro u
  apply Subtype.ext
  change D.advancedSolution I (D.waveOperator u.1) = u.1
  apply D.wave_injectiveOn_advanced I
  · exact D.advancedSolution_mem I _
  · exact u.2
  · exact D.wave_advancedSolution I (D.waveOperator u.1)

/-- The advanced solution map is a right inverse to the restricted wave
operator by causal source existence. -/
lemma advancedSectorSolution_rightInverse
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    Function.RightInverse
      (D.advancedSectorSolutionContinuous I) (D.waveOnAdvanced I) := by
  intro source
  change D.waveOperator (D.advancedSolution I source) = source
  exact D.wave_advancedSolution I source

/-- Causal existence and the retarded energy estimate prove that the
retarded wave restriction is a continuous linear equivalence. -/
noncomputable def retardedWaveEquiv
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    D.retardedSector ≃L[ℝ] 𝒮 :=
  ContinuousLinearEquiv.equivOfInverse
    (D.waveOnRetarded I) (D.retardedSectorSolutionContinuous I)
    (D.retardedSectorSolution_leftInverse I)
    (D.retardedSectorSolution_rightInverse I)

/-- Causal existence and the advanced energy estimate prove that the
advanced wave restriction is a continuous linear equivalence. -/
noncomputable def advancedWaveEquiv
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    D.advancedSector ≃L[ℝ] 𝒮 :=
  ContinuousLinearEquiv.equivOfInverse
    (D.waveOnAdvanced I) (D.advancedSectorSolutionContinuous I)
    (D.advancedSectorSolution_leftInverse I)
    (D.advancedSectorSolution_rightInverse I)

/-- The energy-Cauchy formulation and the coercive-sector formulation are
not independent analytic assumptions: continuity of the wave map, causal
existence, and the two energy estimates construct the coercive
isomorphisms. -/
@[zil_level physical_theorem]
noncomputable def toCoerciveSectorData
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯) :
    MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯 where
  realizeField := D.realizeField
  realizeSource := D.realizeSource
  realizeSource_injective := D.realizeSource_injective
  waveOperator := D.waveOperator
  realizes_wave := D.realizes_wave
  retardedSector := D.retardedSector
  advancedSector := D.advancedSector
  retardedWaveEquiv := D.retardedWaveEquiv I
  advancedWaveEquiv := D.advancedWaveEquiv I
  retardedWaveEquiv_apply := fun u => by
    rfl
  advancedWaveEquiv_apply := fun u => by
    rfl

/-- Both energy-constructed Green fields solve the global intrinsic
Ricci-coupled Maxwell equation. -/
lemma retarded_advanced_solve_intrinsicMaxwell
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        ((D.toGreenData I).realizeField ((D.toGreenData I).retarded source))
        ((D.toGreenData I).realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        ((D.toGreenData I).realizeField ((D.toGreenData I).advanced source))
        ((D.toGreenData I).realizeSource source) :=
  ⟨IntrinsicMaxwellGreenData.retarded_solves I (D.toGreenData I) source,
    IntrinsicMaxwellGreenData.advanced_solves I (D.toGreenData I) source⟩

end MaxwellEnergyCauchyData

/-! ## A.4. Complex covariance is inherited by the Green operators -/

namespace MaxwellEnergyComplexDomain

variable {𝒜 : Type uS}
variable [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]

/-- Retarded-sector uniqueness promotes complex covariance of the wave
operator to complex covariance of the selected retarded solution. -/
lemma retardedSolution_smul
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (C : MaxwellEnergyComplexDomain I D)
    (c : ℂ) (source : 𝒜) :
    D.retardedSolution I (c • source) =
      c • D.retardedSolution I source := by
  apply D.wave_injectiveOn_retarded I
  · exact D.retardedSolution_mem I _
  · exact C.retardedSector_smul c _
      (D.retardedSolution_mem I source)
  · rw [D.wave_retardedSolution I, C.wave_smul,
      D.wave_retardedSolution I]

/-- Advanced-sector uniqueness promotes complex covariance of the wave
operator to complex covariance of the selected advanced solution. -/
lemma advancedSolution_smul
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (C : MaxwellEnergyComplexDomain I D)
    (c : ℂ) (source : 𝒜) :
    D.advancedSolution I (c • source) =
      c • D.advancedSolution I source := by
  apply D.wave_injectiveOn_advanced I
  · exact D.advancedSolution_mem I _
  · exact C.advancedSector_smul c _
      (D.advancedSolution_mem I source)
  · rw [D.wave_advancedSolution I, C.wave_smul,
      D.wave_advancedSolution I]

/-- The complex Caticha/Maxwell carrier is a theorem of wave covariance and
causal uniqueness; retarded and advanced complex-linearity are not separate
certificate fields at this layer. -/
@[zil_level physical_theorem]
noncomputable def toComplexLinearIntrinsicMaxwellCarrier
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (C : MaxwellEnergyComplexDomain I D) :
    ComplexLinearIntrinsicMaxwellCarrier I (D.toGreenData I) where
  wave_smul := C.wave_smul
  retarded_smul := C.retardedSolution_smul I D
  advanced_smul := C.advancedSolution_smul I D

/-- Energy well-posedness plus complex covariance constructs the complete
Caticha/Klein--Gordon/intrinsic-Maxwell chain without separately supplying
Green maps or a complex-linear Green certificate. -/
@[zil_level physical_theorem]
lemma catichaKG_intrinsicMaxwell_chain
    (D : MaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (C : MaxwellEnergyComplexDomain I D)
    (source : 𝒜) :
    let G := D.toGreenData I
    let K :=
      (C.toComplexLinearIntrinsicMaxwellCarrier I D).toContinuumCatichaKGData I G
    K.kleinGordon (K.retarded source) = source ∧
      K.kleinGordon (K.advanced source) = source ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      ∀ field : 𝒜, K.kleinGordon field = G.waveOperator field :=
  wellPosedCauchy_catichaKG_intrinsicMaxwell_chain I
    (D.toWellPosedCauchyData I)
    (C.toComplexLinearIntrinsicMaxwellCarrier I D) source

end MaxwellEnergyComplexDomain

namespace MaxwellTimeReversalData

variable {𝒜 : Type uS}
variable [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]

/-- One-sided retarded well-posedness, retarded complex covariance, and
Wigner time reversal construct the common Caticha/Klein--Gordon/intrinsic
Maxwell evolution.  Both the advanced PDE theorem and advanced complex
stability are derived inside the chain. -/
@[zil_level physical_theorem]
lemma catichaKG_intrinsicMaxwell_chain
    (D : RetardedMaxwellEnergyCauchyData I g cov sign frame 𝒜 𝒜)
    (T : MaxwellTimeReversalData I D)
    (C : RetardedMaxwellComplexDomain I D)
    (A : MaxwellComplexTimeReversalData I D T)
    (source : 𝒜) :
    let E := T.toEnergyCauchyData I D
    let G := E.toGreenData I
    let Cfull :=
      MaxwellTimeReversalData.toEnergyComplexDomain I D T C A
    let K :=
      (MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier
        I E Cfull).toContinuumCatichaKGData I G
    K.kleinGordon (K.retarded source) = source ∧
      K.kleinGordon (K.advanced source) = source ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      ∀ field : 𝒜, K.kleinGordon field = G.waveOperator field :=
  MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain I
    (T.toEnergyCauchyData I D)
    (MaxwellTimeReversalData.toEnergyComplexDomain I D T C A) source

end MaxwellTimeReversalData

namespace MaxwellCoerciveSectorData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [NormedSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [NormedSpace ℝ 𝒯]

/-- The retarded inverse as a genuine continuous linear operator into the
ambient field space. -/
noncomputable def retardedContinuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  D.retardedSector.subtypeL.comp
    D.retardedWaveEquiv.symm.toContinuousLinearMap

/-- The advanced inverse as a genuine continuous linear operator into the
ambient field space. -/
noncomputable def advancedContinuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  D.advancedSector.subtypeL.comp
    D.advancedWaveEquiv.symm.toContinuousLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma retardedContinuous_apply
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.retardedContinuous I source =
      (D.retardedWaveEquiv.symm source).1 := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma advancedContinuous_apply
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.advancedContinuous I source =
      (D.advancedWaveEquiv.symm source).1 := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The continuous retarded inverse is a right inverse of the intrinsic
analytic wave operator. -/
lemma wave_retardedContinuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.retardedContinuous I source) = source := by
  change D.waveOperator (D.retardedWaveEquiv.symm source).1 = source
  rw [← D.retardedWaveEquiv_apply]
  exact D.retardedWaveEquiv.apply_symm_apply source

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The continuous advanced inverse is a right inverse of the intrinsic
analytic wave operator. -/
lemma wave_advancedContinuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.advancedContinuous I source) = source := by
  change D.waveOperator (D.advancedWaveEquiv.symm source).1 = source
  rw [← D.advancedWaveEquiv_apply]
  exact D.advancedWaveEquiv.apply_symm_apply source

/-- Coercive causal sector isomorphisms therefore construct the intrinsic
retarded and advanced Maxwell Green operators without separately supplying
solution maps, uniqueness proofs, or energy constants. -/
@[zil_level physical_theorem]
noncomputable def toGreenData
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯) :
    IntrinsicMaxwellGreenData I g cov sign frame 𝒮 𝒯 :=
  (D.toEnergyCauchyData I).toGreenData I

/-- The abstractly derived retarded Green map is exactly the continuous
inverse of the retarded wave-operator restriction. -/
lemma toGreenData_retarded_eq_continuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).retarded source = D.retardedContinuous I source := by
  apply (D.toEnergyCauchyData I).wave_injectiveOn_retarded I
  · exact (D.toGreenData I).retarded_mem source
  · exact (D.retardedWaveEquiv.symm source).2
  · calc
      (D.toEnergyCauchyData I).waveOperator
          ((D.toGreenData I).retarded source) = source :=
        (D.toGreenData I).wave_retarded source
      _ = (D.toEnergyCauchyData I).waveOperator
          (D.retardedContinuous I source) :=
        (D.wave_retardedContinuous I source).symm

/-- The abstractly derived advanced Green map is exactly the continuous
inverse of the advanced wave-operator restriction. -/
lemma toGreenData_advanced_eq_continuous
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).advanced source = D.advancedContinuous I source := by
  apply (D.toEnergyCauchyData I).wave_injectiveOn_advanced I
  · exact (D.toEnergyCauchyData I).advancedSolution_mem I source
  · exact (D.advancedWaveEquiv.symm source).2
  · calc
      (D.toEnergyCauchyData I).waveOperator
          ((D.toGreenData I).advanced source) = source :=
        (D.toGreenData I).wave_advanced source
      _ = (D.toEnergyCauchyData I).waveOperator
          (D.advancedContinuous I source) :=
        (D.wave_advancedContinuous I source).symm

/-- Quantitative retarded Green bound inherited from the inverse operator
norm. -/
lemma norm_retarded_le
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ‖(D.toGreenData I).retarded source‖ ≤
      ‖D.retardedWaveEquiv.symm.toContinuousLinearMap‖ * ‖source‖ := by
  rw [D.toGreenData_retarded_eq_continuous I source,
    D.retardedContinuous_apply I source]
  exact D.retardedWaveEquiv.symm.toContinuousLinearMap.le_opNorm source

/-- Quantitative advanced Green bound inherited from the inverse operator
norm. -/
lemma norm_advanced_le
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ‖(D.toGreenData I).advanced source‖ ≤
      ‖D.advancedWaveEquiv.symm.toContinuousLinearMap‖ * ‖source‖ := by
  rw [D.toGreenData_advanced_eq_continuous I source,
    D.advancedContinuous_apply I source]
  exact D.advancedWaveEquiv.symm.toContinuousLinearMap.le_opNorm source

/-- The coercive-sector construction immediately yields both global sourced
intrinsic Maxwell equations. -/
lemma retarded_advanced_solve_intrinsicMaxwell
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        ((D.toGreenData I).realizeField ((D.toGreenData I).retarded source))
        ((D.toGreenData I).realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        ((D.toGreenData I).realizeField ((D.toGreenData I).advanced source))
        ((D.toGreenData I).realizeSource source) :=
  (D.toEnergyCauchyData I).retarded_advanced_solve_intrinsicMaxwell I source

/-- On a complex-linear common carrier, the coercive causal wave
isomorphisms construct the complete Caticha/Klein--Gordon--intrinsic-Maxwell
chain.  In particular, neither the Caticha Green maps nor the Maxwell Green
maps are additional premises: both are the continuous causal inverses
constructed above. -/
@[zil_level physical_theorem]
lemma catichaKG_intrinsicMaxwell_chain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]
    (D : MaxwellCoerciveSectorData I g cov sign frame 𝒜 𝒜)
    (C : ComplexLinearIntrinsicMaxwellCarrier I (D.toGreenData I))
    (source : 𝒜) :
    let G := D.toGreenData I
    let K := C.toContinuumCatichaKGData I G
    K.kleinGordon (K.retarded source) = source ∧
      K.kleinGordon (K.advanced source) = source ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      ∀ field : 𝒜, K.kleinGordon field = G.waveOperator field :=
  wellPosedCauchy_catichaKG_intrinsicMaxwell_chain I
    ((D.toEnergyCauchyData I).toWellPosedCauchyData I) C source

/-- The coercive construction discharges the formerly supplied Green-data
leg of the Caticha--Hadamard--Maxwell microcausality capstone.

The remaining assumptions have their original, distinct roles: `hatlas` and
the differentiability hypotheses transport the homogeneous Maxwell equation
between Levi--Civita representatives, while `hW` controls the independent
Hermitian-kernel decomposition. -/
@[zil_level bridge_theorem]
lemma caticha_hadamard_maxwell_microcausality_of_coercive
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [NormedSpace ℝ 𝒜] [Module ℂ 𝒜]
    {α : Type*} (W : α → α → ℂ) (hW : IsHermitianKernel W)
    {ι : Type*}
    (covAtlas : ι →
      CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g covAtlas)
    (a b : ι)
    (D : MaxwellCoerciveSectorData I g (covAtlas a) sign frame 𝒜 𝒜)
    (C : ComplexLinearIntrinsicMaxwellCarrier I (D.toGreenData I))
    (source : 𝒜)
    (hV : ∀ x, MDiffAt
      (T% ((D.toGreenData I).realizeField
        (IntrinsicMaxwellGreenData.causalPropagator
          I (D.toGreenData I) source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (covAtlas b) (frame i)
        ((D.toGreenData I).realizeField
          (IntrinsicMaxwellGreenData.causalPropagator
            I (D.toGreenData I) source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    let G := D.toGreenData I
    let K := C.toContinuumCatichaKGData I G
    (K.kleinGordon
        (continuumSmearedSchrodingerGenerator K.lapse K.shift K.Hperp K.Hi
          (K.causalPropagator source)) = 0) ∧
      (Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightmanTwoPoint
        (hadamardPart W) (pauliJordanPart W) = W) ∧
      IsPauliJordan (pauliJordanPart W) ∧
      (∀ x y,
        W x y - W y x =
          Complex.I * ((pauliJordanPart W x y : ℝ) : ℂ)) ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas a) sign frame
        (G.realizeField
          (IntrinsicMaxwellGreenData.causalPropagator I G source)) 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas b) sign frame
        (G.realizeField
          (IntrinsicMaxwellGreenData.causalPropagator I G source)) 0 := by
  dsimp only
  exact
    caticha_hadamard_maxwell_microcausality
      I (C.toContinuumCatichaKGData I (D.toGreenData I)) source
      W hW g covAtlas hatlas a b sign frame (D.toGreenData I) source
      hV hframe hNablaFrame hbracket

end MaxwellCoerciveSectorData

/-! ## A.4. Lax--Milgram Green operators on the Sobolev graph domain -/

namespace MaxwellLaxMilgramGraphData

variable {𝒮 : Type uS} {𝒯 : Type uT}
variable [NormedAddCommGroup 𝒮] [InnerProductSpace ℝ 𝒮]
variable [NormedAddCommGroup 𝒯] [InnerProductSpace ℝ 𝒯]
variable [CompleteSpace 𝒯]

/-- The retarded Green inverse as a genuine continuous linear map, constructed
from the coercive weak form by Lax--Milgram. -/
noncomputable def retardedGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  (D.toCoerciveSectorData I).retardedContinuous I

/-- The advanced Green inverse as a genuine continuous linear map. -/
noncomputable def advancedGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  (D.toCoerciveSectorData I).advancedContinuous I

/-- The intrinsic global Maxwell Green carrier constructed from the two
Lax--Milgram causal inverses. -/
@[zil_level physical_theorem]
noncomputable def toGreenData
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    IntrinsicMaxwellGreenData I g cov sign frame 𝒮 𝒯 :=
  (D.toCoerciveSectorData I).toGreenData I

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_retardedGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.retardedGreen I source) = source :=
  (D.toCoerciveSectorData I).wave_retardedContinuous I source

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_advancedGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.advancedGreen I source) = source :=
  (D.toCoerciveSectorData I).wave_advancedContinuous I source

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma retardedGreen_mem
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.retardedGreen I source ∈ D.retardedSector :=
  (D.retardedWaveEquiv I).symm source |>.2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma advancedGreen_mem
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.advancedGreen I source ∈ D.advancedSector :=
  (D.advancedWaveEquiv I).symm source |>.2

@[simp]
lemma toGreenData_retarded_apply
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).retarded source = D.retardedGreen I source :=
  (D.toCoerciveSectorData I).toGreenData_retarded_eq_continuous I source

@[simp]
lemma toGreenData_advanced_apply
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    (D.toGreenData I).advanced source = D.advancedGreen I source :=
  (D.toCoerciveSectorData I).toGreenData_advanced_eq_continuous I source

/-- The constructed retarded Green map satisfies the quantitative
`H¹ + H⁻¹` operator-graph estimate. -/
@[zil_level physical_theorem]
lemma graphNorm_retardedGreen_le
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.graphNorm I (D.retardedGreen I source) ≤
      (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
        ‖source‖ := by
  have hnorm :=
    (D.retardedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  rw [graphNorm, D.wave_retardedGreen I source]
  calc
    ‖D.retardedGreen I source‖ + ‖source‖ =
        ‖(D.retardedWaveEquiv I).symm source‖ + ‖source‖ := rfl
    _ ≤
        ‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ *
            ‖source‖ + ‖source‖ :=
      add_le_add hnorm le_rfl
    _ =
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ := by ring

/-- The constructed advanced Green map satisfies the matching graph bound. -/
@[zil_level physical_theorem]
lemma graphNorm_advancedGreen_le
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.graphNorm I (D.advancedGreen I source) ≤
      (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
        ‖source‖ := by
  have hnorm :=
    (D.advancedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  rw [graphNorm, D.wave_advancedGreen I source]
  calc
    ‖D.advancedGreen I source‖ + ‖source‖ =
        ‖(D.advancedWaveEquiv I).symm source‖ + ‖source‖ := rfl
    _ ≤
        ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ *
            ‖source‖ + ‖source‖ :=
      add_le_add hnorm le_rfl
    _ =
        (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ := by ring

/-- The continuous causal propagator `G⁻ - G⁺` constructed from the two
Lax--Milgram inverses. -/
noncomputable def causalGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    𝒮 →L[ℝ] 𝒯 :=
  D.retardedGreen I - D.advancedGreen I

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
lemma wave_causalGreen
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.waveOperator (D.causalGreen I source) = 0 := by
  rw [causalGreen, sub_apply, map_sub,
    D.wave_retardedGreen I source, D.wave_advancedGreen I source, sub_self]

/-- Operator-norm control of the homogeneous causal propagator. -/
lemma norm_causalGreen_le
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    ‖D.causalGreen I source‖ ≤
      (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
        ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
        ‖source‖ := by
  have hret :=
    (D.retardedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  have hadv :=
    (D.advancedWaveEquiv I).symm.toContinuousLinearMap.le_opNorm source
  rw [causalGreen, sub_apply]
  calc
    ‖D.retardedGreen I source - D.advancedGreen I source‖ ≤
        ‖D.retardedGreen I source‖ + ‖D.advancedGreen I source‖ :=
      norm_sub_le _ _
    _ =
        ‖(D.retardedWaveEquiv I).symm source‖ +
          ‖(D.advancedWaveEquiv I).symm source‖ := rfl
    _ ≤
        ‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ * ‖source‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ * ‖source‖ :=
      add_le_add hret hadv
    _ =
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ := by ring

/-! ## A.4.1. Exact Green complex and the physical source quotient -/

/-- Fields belonging to both causal Sobolev sectors.  On compactly supported
test fields this is the analytic domain on which both Green inverses act as
left inverses of the wave operator. -/
def causalCore
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    Submodule ℝ 𝒯 :=
  D.retardedSector ⊓ D.advancedSector

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The constructed retarded Green operator is a left inverse of the wave
operator on the retarded causal sector. -/
lemma retardedGreen_wave_of_mem
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (field : 𝒯) (hfield : field ∈ D.retardedSector) :
    D.retardedGreen I (D.waveOperator field) = field := by
  change
    ((D.retardedWaveEquiv I).symm (D.waveOperator field)).1 = field
  have h :=
    (D.retardedWaveEquiv I).symm_apply_apply
      (⟨field, hfield⟩ : D.retardedSector)
  rw [D.retardedWaveEquiv_apply I] at h
  exact congrArg Subtype.val h

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The constructed advanced Green operator is a left inverse of the wave
operator on the advanced causal sector. -/
lemma advancedGreen_wave_of_mem
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (field : 𝒯) (hfield : field ∈ D.advancedSector) :
    D.advancedGreen I (D.waveOperator field) = field := by
  change
    ((D.advancedWaveEquiv I).symm (D.waveOperator field)).1 = field
  have h :=
    (D.advancedWaveEquiv I).symm_apply_apply
      (⟨field, hfield⟩ : D.advancedSector)
  rw [D.advancedWaveEquiv_apply I] at h
  exact congrArg Subtype.val h

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The causal propagator kills wave images of fields lying in the common
retarded/advanced core.  This is the second composition in the standard
Green complex; `wave_causalGreen` is the first. -/
@[simp]
lemma causalGreen_wave_of_mem_causalCore
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (field : 𝒯) (hfield : field ∈ D.causalCore I) :
    D.causalGreen I (D.waveOperator field) = 0 := by
  rw [causalGreen, sub_apply,
    D.retardedGreen_wave_of_mem I field hfield.1,
    D.advancedGreen_wave_of_mem I field hfield.2, sub_self]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Pointwise exactness of the causal Green complex.  A source is annihilated
by `G⁻ - G⁺` exactly when it is the wave image of a field belonging to both
causal sectors. -/
@[zil_level physical_theorem]
theorem causalGreen_eq_zero_iff_exists_causalCore
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    D.causalGreen I source = 0 ↔
      ∃ field : 𝒯,
        field ∈ D.causalCore I ∧ D.waveOperator field = source := by
  constructor
  · intro hzero
    have hEq :
        D.retardedGreen I source = D.advancedGreen I source := by
      exact sub_eq_zero.mp (by
        simpa only [causalGreen, sub_apply] using hzero)
    refine ⟨D.retardedGreen I source, ?_, D.wave_retardedGreen I source⟩
    exact
      ⟨D.retardedGreen_mem I source,
        hEq ▸ D.advancedGreen_mem I source⟩
  · rintro ⟨field, hfield, rfl⟩
    exact D.causalGreen_wave_of_mem_causalCore I field hfield

/-- Wave images of the common causal core.  Exactness below identifies this
submodule with the complete kernel of the Pauli--Jordan propagator. -/
def causalWaveImage
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    Submodule ℝ 𝒮 :=
  (D.causalCore I).map D.waveOperator.toLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Exact Green-complex theorem.**  The kernel of the constructed causal
propagator is precisely the wave image of the common causal Sobolev core. -/
@[zil_level physical_theorem]
theorem ker_causalGreen_eq_causalWaveImage
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    LinearMap.ker (D.causalGreen I).toLinearMap =
      D.causalWaveImage I := by
  ext source
  constructor
  · intro hsource
    have hzero : D.causalGreen I source = 0 :=
      (LinearMap.mem_ker.mp hsource)
    obtain ⟨field, hfield, hwave⟩ :=
      (D.causalGreen_eq_zero_iff_exists_causalCore I source).mp hzero
    exact ⟨field, hfield, hwave⟩
  · rintro ⟨field, hfield, rfl⟩
    exact LinearMap.mem_ker.mpr
      (D.causalGreen_wave_of_mem_causalCore I field hfield)

/-- The homogeneous Maxwell solution subspace on the analytic carrier. -/
def homogeneousMaxwellSpace
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    Submodule ℝ 𝒯 :=
  LinearMap.ker D.waveOperator.toLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Every field in the causal Green range is a homogeneous intrinsic
Maxwell solution. -/
lemma causalGreen_range_le_homogeneousMaxwellSpace
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    LinearMap.range (D.causalGreen I).toLinearMap ≤
      D.homogeneousMaxwellSpace I := by
  rintro field ⟨source, rfl⟩
  exact LinearMap.mem_ker.mpr (D.wave_causalGreen I source)

/-- Sources modulo wave-exact common-core sources.  The kernel theorem proves
that this definition is the standard causal test-function quotient, rather
than an independently supplied gauge relation. -/
abbrev CausalSourceQuotient
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :=
  𝒮 ⧸ LinearMap.ker (D.causalGreen I).toLinearMap

/-- The first-isomorphism-theorem realization of the physical source
quotient as the actual range of the constructed causal propagator. -/
noncomputable def causalSourceQuotientEquivRange
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    D.CausalSourceQuotient I ≃ₗ[ℝ]
      LinearMap.range (D.causalGreen I).toLinearMap :=
  (D.causalGreen I).toLinearMap.quotKerEquivRange

/-- The causal quotient embeds into the homogeneous Maxwell solution space.
Injectivity follows from the first isomorphism theorem; homogeneity follows
from the derived identity `P(G⁻ - G⁺) = 0`. -/
noncomputable def causalSourceQuotientToHomogeneous
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    D.CausalSourceQuotient I →ₗ[ℝ] D.homogeneousMaxwellSpace I :=
  (Submodule.inclusion
      (D.causalGreen_range_le_homogeneousMaxwellSpace I)).comp
    (D.causalSourceQuotientEquivRange I).toLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Physical causal phase-space theorem.**  Quotienting sources by the
wave image of the common causal core gives a faithful linear realization in
the homogeneous Maxwell solution space. -/
@[zil_level physical_theorem]
theorem causalSourceQuotientToHomogeneous_injective
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯) :
    Function.Injective (D.causalSourceQuotientToHomogeneous I) :=
  (Submodule.inclusion_injective
      (D.causalGreen_range_le_homogeneousMaxwellSpace I)).comp
    (D.causalSourceQuotientEquivRange I).injective

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Every class in the physical source quotient is represented faithfully by
a global homogeneous intrinsic Ricci-coupled Maxwell field. -/
@[zil_level physical_theorem]
theorem causalSourceQuotient_intrinsic_homogeneous
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (q : D.CausalSourceQuotient I) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
      (D.realizeField (D.causalSourceQuotientToHomogeneous I q).1) 0 := by
  rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
  have hkernel :
      D.waveOperator (D.causalSourceQuotientToHomogeneous I q).1 = 0 :=
    LinearMap.mem_ker.mp
      (D.causalSourceQuotientToHomogeneous I q).2
  simpa only [hkernel, map_zero] using
    (D.realizes_wave (D.causalSourceQuotientToHomogeneous I q).1).symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Concrete continuum causal phase space.**  On the repository's
`H¹(ℝ³; ℂ⁴)` field and `H⁻¹(ℝ³; ℂ⁴)` source carrier, the quotient by
wave-exact common-core sources embeds faithfully into global homogeneous
intrinsic Maxwell solutions. -/
@[zil_level physical_theorem]
theorem curvedHOneFour_causalSourceQuotient_phaseSpace
    (D : CurvedMaxwellHOneGraphData I g cov sign frame) :
    Function.Injective (D.causalSourceQuotientToHomogeneous I) ∧
      ∀ q : D.CausalSourceQuotient I,
        IntrinsicRicciCoupledMaxwellOn I g cov sign frame
          (D.realizeField (D.causalSourceQuotientToHomogeneous I q).1) 0 :=
  ⟨D.causalSourceQuotientToHomogeneous_injective I,
    D.causalSourceQuotient_intrinsic_homogeneous I⟩

/-- The Lax--Milgram causal propagator is a bounded homogeneous solution of
the intrinsic Ricci-coupled Maxwell equation. -/
@[zil_level physical_theorem]
theorem causalGreen_intrinsic_homogeneous_energy
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ := by
  constructor
  · rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
    simpa only [D.wave_causalGreen I source, map_zero] using
      (D.realizes_wave (D.causalGreen I source)).symm
  · exact D.norm_causalGreen_le I source

/-- Constructed causal Green evolution for the intrinsic curved Maxwell
operator, including both graph-energy bounds. -/
@[zil_level physical_theorem]
theorem curvedMaxwellGreen_intrinsic_graphEnergy
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒮 𝒯)
    (source : 𝒮) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.retardedGreen I source))
        (D.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.advancedGreen I source))
        (D.realizeSource source) ∧
      D.retardedGreen I source ∈ D.retardedSector ∧
      D.advancedGreen I source ∈ D.advancedSector ∧
      D.graphNorm I (D.retardedGreen I source) ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ ∧
      D.graphNorm I (D.advancedGreen I source) ≤
        (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ := by
  have hRetarded :
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.retardedGreen I source))
        (D.realizeSource source) := by
    rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
    simpa only [D.wave_retardedGreen I source] using
      (D.realizes_wave (D.retardedGreen I source)).symm
  have hAdvanced :
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.advancedGreen I source))
        (D.realizeSource source) := by
    rw [intrinsicRicciCoupledMaxwellOn_iff_operator_eq]
    simpa only [D.wave_advancedGreen I source] using
      (D.realizes_wave (D.advancedGreen I source)).symm
  exact
    ⟨hRetarded, hAdvanced,
      D.retardedGreen_mem I source, D.advancedGreen_mem I source,
      D.graphNorm_retardedGreen_le I source,
      D.graphNorm_advancedGreen_le I source⟩

/-- The preceding Green theorem on the repository's explicit
`H¹(ℝ³; ℂ⁴) → H⁻¹(ℝ³; ℂ⁴)` carrier. -/
@[zil_level physical_theorem]
theorem curvedHOneFourMaxwellGreen_intrinsic_graphEnergy
    (D : CurvedMaxwellHOneGraphData I g cov sign frame)
    (source : MaxwellHMinusOneFour) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.retardedGreen I source))
        (D.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.advancedGreen I source))
        (D.realizeSource source) ∧
      D.retardedGreen I source ∈ D.retardedSector ∧
      D.advancedGreen I source ∈ D.advancedSector ∧
      D.graphNorm I (D.retardedGreen I source) ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ ∧
      D.graphNorm I (D.advancedGreen I source) ≤
        (‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖ + 1) *
          ‖source‖ :=
  D.curvedMaxwellGreen_intrinsic_graphEnergy I source

/-- Concrete `H¹(ℝ³; ℂ⁴)` specialization of the homogeneous causal
propagator and its energy bound. -/
@[zil_level physical_theorem]
theorem curvedHOneFour_causalGreen_intrinsic_homogeneous_energy
    (D : CurvedMaxwellHOneGraphData I g cov sign frame)
    (source : MaxwellHMinusOneFour) :
    IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ :=
  D.causalGreen_intrinsic_homogeneous_energy I source

/-! ## A.5. Complex-linear Lax--Milgram Green and Caticha evolution -/

/-- Complex covariance of the Lax--Milgram graph domain.

This is an abbreviation of the already established energy-domain interface:
it adds no second copy of the wave or causal-sector hypotheses.  Lax--Milgram
first constructs the causal inverses, and causal uniqueness then proves that
those inverses commute with complex scalars. -/
abbrev ComplexDomain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜) : Prop :=
  MaxwellEnergyComplexDomain I
    ((D.toCoerciveSectorData I).toEnergyCauchyData I)

/-- The Lax--Milgram construction and complex-domain covariance derive the
complex-linear intrinsic Maxwell carrier.  In particular, complex
linearity of the retarded and advanced Green maps is not assumed. -/
@[zil_level physical_theorem]
noncomputable def toComplexLinearIntrinsicMaxwellCarrier
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) :
    ComplexLinearIntrinsicMaxwellCarrier I (D.toGreenData I) :=
  MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier I
    ((D.toCoerciveSectorData I).toEnergyCauchyData I) C

/-- The constructed retarded Lax--Milgram Green operator is complex-linear
on the selected complex Sobolev graph domain. -/
lemma retardedGreen_smul
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (c : ℂ) (source : 𝒜) :
    D.retardedGreen I (c • source) = c • D.retardedGreen I source := by
  simpa only [D.toGreenData_retarded_apply I] using
    (D.toComplexLinearIntrinsicMaxwellCarrier I C).retarded_smul c source

/-- The constructed advanced Lax--Milgram Green operator is complex-linear
on the selected complex Sobolev graph domain. -/
lemma advancedGreen_smul
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (c : ℂ) (source : 𝒜) :
    D.advancedGreen I (c • source) = c • D.advancedGreen I source := by
  simpa only [D.toGreenData_advanced_apply I] using
    (D.toComplexLinearIntrinsicMaxwellCarrier I C).advanced_smul c source

/-- The continuous Pauli--Jordan operator constructed by Lax--Milgram
therefore commutes with complex scalars. -/
lemma causalGreen_smul
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (c : ℂ) (source : 𝒜) :
    D.causalGreen I (c • source) = c • D.causalGreen I source := by
  rw [causalGreen, sub_apply, sub_apply, D.retardedGreen_smul I C,
    D.advancedGreen_smul I C, smul_sub]

/-- The same Lax--Milgram causal inverses now construct the continuum Caticha
functional/Klein--Gordon datum; its differential operator is definitionally
the intrinsic Ricci-coupled Maxwell operator on the common complex carrier. -/
@[zil_level physical_theorem]
lemma catichaKG_intrinsicMaxwell_chain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (source : 𝒜) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.kleinGordon (K.retarded source) = source ∧
      K.kleinGordon (K.advanced source) = source ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.retarded source)) (G.realizeSource source) ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (G.realizeField (G.advanced source)) (G.realizeSource source) ∧
      ∀ field : 𝒜, K.kleinGordon field = G.waveOperator field :=
  MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain I
    ((D.toCoerciveSectorData I).toEnergyCauchyData I) C source

/-- The Caticha/Klein--Gordon Pauli--Jordan field is exactly the continuous
Lax--Milgram causal Green field on the common complex carrier. -/
lemma caticha_causalPropagator_eq_causalGreen
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (source : 𝒜) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.causalPropagator source = D.causalGreen I source := by
  dsimp only
  rw [ContinuumCatichaKGData.causalPropagator, LinearMap.sub_apply,
    causalGreen, sub_apply]
  change
    (D.toGreenData I).retarded source -
        (D.toGreenData I).advanced source =
      D.retardedGreen I source - D.advancedGreen I source
  rw [D.toGreenData_retarded_apply I, D.toGreenData_advanced_apply I]

/-- The Pauli--Jordan operator as a complex-linear map.  Its underlying
function is the continuous real Lax--Milgram causal Green operator. -/
noncomputable def causalGreenComplexLinear
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) :
    𝒜 →ₗ[ℂ] 𝒜 :=
  ((D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
    I (D.toGreenData I)).causalPropagator

@[simp]
lemma causalGreenComplexLinear_apply
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (source : 𝒜) :
    D.causalGreenComplexLinear I C source = D.causalGreen I source :=
  D.caticha_causalPropagator_eq_causalGreen I C source

/-- **Genuine complex continuous causal propagator.**  Complex covariance
upgrades the Caticha/Maxwell Pauli--Jordan map to a complex-linear operator,
while the Lax--Milgram inverse estimates prove its continuity with the same
sum-of-inverse-norms bound. -/
@[zil_level physical_theorem]
noncomputable def causalGreenComplex
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) :
    𝒜 →L[ℂ] 𝒜 :=
  (D.causalGreenComplexLinear I C).mkContinuous
    (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
      ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖)
    (fun source => by
      rw [D.causalGreenComplexLinear_apply I C]
      exact D.norm_causalGreen_le I source)

@[simp]
lemma causalGreenComplex_apply
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (source : 𝒜) :
    D.causalGreenComplex I C source = D.causalGreen I source := by
  rw [causalGreenComplex, LinearMap.mkContinuous_apply,
    D.causalGreenComplexLinear_apply I C]

/-- **Complex continuum Caticha--Maxwell causal capstone.**  The constructed
Pauli--Jordan field is simultaneously the Caticha/Klein--Gordon causal
field, a homogeneous intrinsic curved Maxwell solution, stable under the
Caticha functional generator, and controlled by the causal Green energy
bound. -/
@[zil_level physical_theorem]
theorem caticha_causalGreen_intrinsic_homogeneous_energy
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I) (source : 𝒜) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.causalPropagator source = D.causalGreen I source ∧
      K.kleinGordon (K.causalPropagator source) = 0 ∧
      K.kleinGordon
        (continuumSmearedSchrodingerGenerator K.lapse K.shift
          K.Hperp K.Hi (K.causalPropagator source)) = 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ := by
  dsimp only
  refine ⟨D.caticha_causalPropagator_eq_causalGreen I C source, ?_, ?_,
    (D.causalGreen_intrinsic_homogeneous_energy I source).1,
    (D.causalGreen_intrinsic_homogeneous_energy I source).2⟩
  · exact
      ((D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
        I (D.toGreenData I)).kleinGordon_causalPropagator_eq_zero source
  · exact
      ((D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
        I (D.toGreenData I)).caticha_causalPropagator_is_homogeneous source

/-- Concrete `H¹(ℝ³; ℂ⁴)` specialization of the complete complex
Caticha/Klein--Gordon/intrinsic-Maxwell causal evolution. -/
@[zil_level physical_theorem]
theorem curvedHOneFour_caticha_causalGreen_intrinsic_homogeneous_energy
    (D : CurvedMaxwellHOneGraphData I g cov sign frame)
    (C : D.ComplexDomain I) (source : MaxwellHMinusOneFour) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.causalPropagator source = D.causalGreen I source ∧
      K.kleinGordon (K.causalPropagator source) = 0 ∧
      K.kleinGordon
        (continuumSmearedSchrodingerGenerator K.lapse K.shift
          K.Hperp K.Hi (K.causalPropagator source)) = 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ :=
  D.caticha_causalGreen_intrinsic_homogeneous_energy I C source

/-- Pull a corrected sesquilinear Hadamard carrier through the *constructed*
complex-continuous Maxwell causal propagator.  Hermiticity, positivity, CCR
compatibility, and microlocal support are inherited from the generic AQFT
pullback theorem; only the symplectic identity and cone transport remain
analytic inputs. -/
noncomputable def causalSesquilinearHadamardCarrier
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {Xi : Type*}
    (H2 : ContinuumSesquilinearHadamardTwoPoint 𝒜 Xi)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      symp phi psi =
        H2.symplecticForm
          (D.causalGreenComplex I C phi) (D.causalGreenComplex I C psi))
    (transport : Xi → Xi)
    (hcone : Set.MapsTo transport H2.positiveFrequencyCone
      H2.positiveFrequencyCone) :
    ContinuumSesquilinearHadamardTwoPoint 𝒜 Xi :=
  H2.pullback (D.causalGreenComplex I C).toLinearMap symp
    symp_pullback transport hcone

/-- All corrected quasifree/Hadamard laws inherited by the Lax--Milgram
Maxwell causal pullback. -/
lemma causalSesquilinearHadamardCarrier_properties
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {Xi : Type*}
    (H2 : ContinuumSesquilinearHadamardTwoPoint 𝒜 Xi)
    (symp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      symp phi psi =
        H2.symplecticForm
          (D.causalGreenComplex I C phi) (D.causalGreenComplex I C psi))
    (transport : Xi → Xi)
    (hcone : Set.MapsTo transport H2.positiveFrequencyCone
      H2.positiveFrequencyCone) :
    IsHermitianSesquilinearTwoPoint
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsPositiveSesquilinearTwoPoint
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).twoPoint ∧
      IsCCRSesquilinearTwoPoint
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).twoPoint
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).symplecticForm ∧
      MicrolocalSpectrumCondition
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).wavefront
        (D.causalSesquilinearHadamardCarrier I C H2 symp
          symp_pullback transport hcone).positiveFrequencyCone :=
  H2.pullback_properties (D.causalGreenComplex I C).toLinearMap symp
    symp_pullback transport hcone

/-- Package a distributional realization of the source two-point function
obtained by pulling a field two-point distribution through the constructed
Maxwell causal propagator.  The target distribution and localized-Fourier
probes may live on a different Schwartz carrier. -/
def causalDistributionalHadamardTransport
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    Dhad.Transport (𝒟 := 𝒜) (V' := V')
      (W' := pullbackSesquilinearTwoPoint
        (D.causalGreenComplex I C).toLinearMap W) where
  distribution := sourceDistribution
  smearing := sourceSmearing
  represents := represents
  probe := sourceProbe
  probeTransport := probeTransport

/-- The target distributional Hadamard datum constructed from the causal
Maxwell pullback.  It stores no wavefront theorem. -/
def causalDistributionalHadamardData
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    DistributionalHadamardData
      (𝒜 := 𝒜) (V := V') (X := X) (Ξ := Xi)
      (W := pullbackSesquilinearTwoPoint
        (D.causalGreenComplex I C).toLinearMap W) :=
  (D.causalDistributionalHadamardTransport I C W Dhad
    sourceDistribution sourceSmearing represents sourceProbe
    probeTransport).toData

/-! ### A.4.4. Explicit radial Pauli--Jordan target distribution -/

/-- Specialize the general Caticha--Maxwell distributional transport to the
actual Coulomb-weighted retarded-minus-advanced Dirac distribution of the
radial light-cone model.

This definition deliberately keeps the representation and bidirectional
localized-Fourier transport as arguments.  Supplying an explicit target
distribution is not, by itself, a proof that its wavefront set is the
four-dimensional Hadamard cone. -/
def radialCausalDistributionalHadamardTransport
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {V : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (t r c : ℝ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap ℝ ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        causalKernelDistribution t r c (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe ℝ X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe
        (causalKernelDistribution t r c) sourceProbe) :
    Dhad.Transport (𝒟 := 𝒜) (V' := ℝ)
      (W' := pullbackSesquilinearTwoPoint
        (D.causalGreenComplex I C).toLinearMap W) :=
  D.causalDistributionalHadamardTransport I C W Dhad
    (causalKernelDistribution t r c) sourceSmearing represents
    sourceProbe probeTransport

/-- The concrete radial Pauli--Jordan target has the transported Hadamard
wavefront cone once the source upper/lower Fourier estimates and the
bidirectional localized-probe pairing are proved.

The conclusion is now about `causalKernelDistribution` itself, rather than
an opaque target distribution field. -/
@[zil_level physical_theorem]
lemma radialCausalDistributionalHadamard_wavefront_eq
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    {V : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (offCone : Dhad.OffConeRapidDecayBounds)
    (onCone : Dhad.OnConeLowerEscapeBounds)
    (t r c : ℝ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap ℝ ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        causalKernelDistribution t r c (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe ℝ X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe
        (causalKernelDistribution t r c) sourceProbe) :
    Physlib.Distribution.distributionalWavefrontSet
        (causalKernelDistribution t r c) sourceProbe =
      Dhad.hadamardCone :=
  (D.radialCausalDistributionalHadamardTransport I C W Dhad t r c
    sourceSmearing represents sourceProbe probeTransport).wavefront_eq
      offCone.isRegularOutsideCone onCone.isSingularOnCone

/-- **Lax--Milgram Caticha--Maxwell distributional Hadamard propagation.**
The same complex-continuous Pauli--Jordan map is the Caticha/KG causal field,
a bounded homogeneous intrinsic curved Maxwell field, and the map defining
the source-space two-point pullback.  Complete bidirectional localized
Fourier transport then proves the exact target wavefront cone. -/
@[zil_level physical_theorem]
lemma caticha_maxwell_causal_distributional_hadamard_propagation
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    (D : MaxwellLaxMilgramGraphData I g cov sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    (source : 𝒜)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (hregular : Dhad.IsRegularOutsideCone)
    (hsingular : Dhad.IsSingularOnCone)
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.causalPropagator source = D.causalGreen I source ∧
      K.kleinGordon (K.causalPropagator source) = 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ ∧
      Physlib.Distribution.distributionalWavefrontSet
          sourceDistribution sourceProbe = Dhad.hadamardCone := by
  dsimp only
  refine ⟨D.caticha_causalPropagator_eq_causalGreen I C source,
    ((D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
      I (D.toGreenData I)).kleinGordon_causalPropagator_eq_zero source,
    (D.causalGreen_intrinsic_homogeneous_energy I source).1,
    (D.causalGreen_intrinsic_homogeneous_energy I source).2, ?_⟩
  exact
    (D.causalDistributionalHadamardTransport I C W Dhad
      sourceDistribution sourceSmearing represents sourceProbe
      probeTransport).wavefront_eq hregular hsingular

/-- Concrete `H¹(ℝ³; ℂ⁴)` specialization of the distributional
Caticha--Maxwell causal propagation theorem. -/
@[zil_level physical_theorem]
lemma curvedHOneFour_caticha_maxwell_causal_distributional_hadamard_propagation
    (D : CurvedMaxwellHOneGraphData I g cov sign frame)
    (C : D.ComplexDomain I)
    (source : MaxwellHMinusOneFour)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : MaxwellHOneFour →ₗ⋆[ℂ] MaxwellHOneFour →ₗ[ℂ] ℂ)
    (Dhad : DistributionalHadamardData
      (𝒜 := MaxwellHOneFour) (V := V) (X := X) (Ξ := Xi) (W := W))
    (hregular : Dhad.IsRegularOutsideCone)
    (hsingular : Dhad.IsSingularOnCone)
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing :
      MaxwellHMinusOneFour → MaxwellHMinusOneFour → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    K.causalPropagator source = D.causalGreen I source ∧
      K.kleinGordon (K.causalPropagator source) = 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g cov sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ ∧
      Physlib.Distribution.distributionalWavefrontSet
          sourceDistribution sourceProbe = Dhad.hadamardCone :=
  D.caticha_maxwell_causal_distributional_hadamard_propagation
    I C source W Dhad hregular hsingular sourceDistribution
    sourceSmearing represents sourceProbe probeTransport

/-- **Corrected distributional Caticha--AQFT--Maxwell atlas capstone.**
The two-point functional is genuinely sesquilinear and is pulled back through
the exact complex-continuous causal propagator.  Its Hermiticity, positivity,
and CCR law are derived from the field functional.  Bidirectional
localized-Fourier transport proves the target distribution's exact Hadamard
wavefront set.  Independently, the same energy-bounded causal field solves
the intrinsic Maxwell equation for two representatives of a compatible
Levi--Civita atlas.

This theorem supersedes conjunctions with an unrelated bilinear kernel.  It
does not infer the microlocal estimates, symplectic pullback, or smooth atlas
transport from Lax--Milgram coercivity; those remain explicit inputs. -/
@[zil_level bridge_theorem]
lemma caticha_maxwell_causal_distributional_hadamard_atlas_chain
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    {ι : Type*}
    (covAtlas : ι →
      CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g covAtlas)
    (a b : ι)
    (D : MaxwellLaxMilgramGraphData I g (covAtlas a) sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    (source : 𝒜)
    (hV : ∀ x, MDiffAt
      (T% (D.realizeField (D.causalGreen I source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (covAtlas b) (frame i)
        (D.realizeField (D.causalGreen I source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x)
    {V V' : Type} {X Xi : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Xi]
    (W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ)
    (fieldSymp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (hHermitian : IsHermitianSesquilinearTwoPoint W)
    (hPositive : IsPositiveSesquilinearTwoPoint W)
    (hCCR : IsCCRSesquilinearTwoPoint W fieldSymp)
    (sourceSymp : 𝒜 →ₗ[ℝ] 𝒜 →ₗ[ℝ] ℝ)
    (symp_pullback : ∀ phi psi,
      sourceSymp phi psi =
        fieldSymp
          (D.causalGreenComplex I C phi) (D.causalGreenComplex I C psi))
    (Dhad : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Xi) (W := W))
    (hregular : Dhad.IsRegularOutsideCone)
    (hsingular : Dhad.IsSingularOnCone)
    (sourceDistribution : V' →d[ℂ] ℂ)
    (sourceSmearing : 𝒜 → 𝒜 → SchwartzMap V' ℂ)
    (represents : ∀ phi psi,
      pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W phi psi =
        sourceDistribution (sourceSmearing phi psi))
    (sourceProbe : Physlib.Distribution.MicrolocalFourierProbe V' X Xi)
    (probeTransport : DistributionalProbeTransport
      Dhad.distribution Dhad.probe sourceDistribution sourceProbe) :
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
        I (D.toGreenData I)
    K.kleinGordon
        (continuumSmearedSchrodingerGenerator K.lapse K.shift
          K.Hperp K.Hi (K.causalPropagator source)) = 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas a) sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas b) sign frame
        (D.realizeField (D.causalGreen I source)) 0 ∧
      ‖D.causalGreen I source‖ ≤
        (‖(D.retardedWaveEquiv I).symm.toContinuousLinearMap‖ +
          ‖(D.advancedWaveEquiv I).symm.toContinuousLinearMap‖) *
          ‖source‖ ∧
      IsHermitianSesquilinearTwoPoint
        (pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W) ∧
      IsPositiveSesquilinearTwoPoint
        (pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W) ∧
      IsCCRSesquilinearTwoPoint
        (pullbackSesquilinearTwoPoint
          (D.causalGreenComplex I C).toLinearMap W) sourceSymp ∧
      Physlib.Distribution.distributionalWavefrontSet
          sourceDistribution sourceProbe = Dhad.hadamardCone := by
  dsimp only
  have hA :=
    (D.causalGreen_intrinsic_homogeneous_energy I source).1
  have hB :
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas b) sign frame
        (D.realizeField (D.causalGreen I source)) 0 :=
    (intrinsicRicciCoupledMaxwellOn_atlas_iff I g covAtlas hatlas a b sign
      frame (D.realizeField (D.causalGreen I source)) 0
      hV hframe hNablaFrame hbracket).mp hA
  refine
    ⟨((D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData
        I (D.toGreenData I)).caticha_causalPropagator_is_homogeneous source,
      hA, hB, (D.causalGreen_intrinsic_homogeneous_energy I source).2,
      pullbackSesquilinearTwoPoint_isHermitian
        (D.causalGreenComplex I C).toLinearMap W hHermitian,
      pullbackSesquilinearTwoPoint_isPositive
        (D.causalGreenComplex I C).toLinearMap W hPositive, ?_, ?_⟩
  · intro phi psi
    change
      W (D.causalGreenComplex I C phi) (D.causalGreenComplex I C psi) -
          W (D.causalGreenComplex I C psi) (D.causalGreenComplex I C phi) =
        Complex.I * (sourceSymp phi psi : ℂ)
    rw [symp_pullback]
    exact hCCR
      (D.causalGreenComplex I C phi) (D.causalGreenComplex I C psi)
  · exact
      (D.causalDistributionalHadamardTransport I C W Dhad
        sourceDistribution sourceSmearing represents sourceProbe
        probeTransport).wavefront_eq hregular hsingular

/-- **Lax--Milgram Caticha--Hadamard--AQFT capstone.**  Closed coercive
causal Sobolev forms construct the Green operators, complex covariance and
uniqueness construct their complex-linear Caticha/KG realization, and the
existing Hermitian-kernel and atlas transport theorem supplies the
microcausal/Hadamard and coordinate-independent Maxwell conclusions.

No Green map or complex-linear Green certificate is supplied independently.
The Hermitian kernel and the smooth compatible Levi--Civita atlas remain
visible because they are logically separate from causal PDE well-posedness. -/
@[zil_level bridge_theorem]
lemma caticha_hadamard_maxwell_microcausality_of_laxMilgram
    {𝒜 : Type uS}
    [NormedAddCommGroup 𝒜] [InnerProductSpace ℝ 𝒜]
    [CompleteSpace 𝒜] [Module ℂ 𝒜]
    {α : Type*} (W : α → α → ℂ) (hW : IsHermitianKernel W)
    {ι : Type*}
    (covAtlas : ι →
      CovariantDerivative I E (TangentSpace I : M → Type _))
    (hatlas : IsLeviCivitaAtlas I g covAtlas)
    (a b : ι)
    (D : MaxwellLaxMilgramGraphData I g (covAtlas a) sign frame 𝒜 𝒜)
    (C : D.ComplexDomain I)
    (source : 𝒜)
    (hV : ∀ x, MDiffAt
      (T% ((D.toGreenData I).realizeField
        (IntrinsicMaxwellGreenData.causalPropagator
          I (D.toGreenData I) source))) x)
    (hframe : ∀ i x, MDiffAt (T% (frame i)) x)
    (hNablaFrame : ∀ i x, MDiffAt
      (T% (firstCovariantSection I (covAtlas b) (frame i)
        ((D.toGreenData I).realizeField
          (IntrinsicMaxwellGreenData.causalPropagator
            I (D.toGreenData I) source)))) x)
    (hbracket : ∀ i j x,
      MDiffAt (T% (VectorField.mlieBracket I (frame i) (frame j))) x) :
    let G := D.toGreenData I
    let K :=
      (D.toComplexLinearIntrinsicMaxwellCarrier I C).toContinuumCatichaKGData I G
    (K.kleinGordon
        (continuumSmearedSchrodingerGenerator K.lapse K.shift K.Hperp K.Hi
          (K.causalPropagator source)) = 0) ∧
      (Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightmanTwoPoint
        (hadamardPart W) (pauliJordanPart W) = W) ∧
      IsPauliJordan (pauliJordanPart W) ∧
      (∀ x y,
        W x y - W y x =
          Complex.I * ((pauliJordanPart W x y : ℝ) : ℂ)) ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas a) sign frame
        (G.realizeField
          (IntrinsicMaxwellGreenData.causalPropagator I G source)) 0 ∧
      IntrinsicRicciCoupledMaxwellOn I g (covAtlas b) sign frame
        (G.realizeField
          (IntrinsicMaxwellGreenData.causalPropagator I G source)) 0 :=
  (D.toCoerciveSectorData I).caticha_hadamard_maxwell_microcausality_of_coercive
    I W hW covAtlas hatlas a b
    (D.toComplexLinearIntrinsicMaxwellCarrier I C) source
    hV hframe hNablaFrame hbracket

end MaxwellLaxMilgramGraphData

/-! ## B. Propagation of the distributional Hadamard condition -/

/-- A Green-evolved Hadamard realization.  Its analytic content is a
bidirectional transport between independently indexed localized-Fourier
probe families, explicit rapid-decay upper bounds off the source cone, and
explicit polynomial lower escape on the source cone.  No regularity,
singularity, or wavefront equality is a field. -/
structure GreenHadamardPropagation
    {𝒜 : Type uA} {𝒟 : Type uD}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    (source : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)) where
  transport :
    source.Transport (𝒟 := 𝒟) (V' := V') (W' := W')
  source_offConeBounds : source.OffConeRapidDecayBounds
  source_onConeBounds : source.OnConeLowerEscapeBounds

namespace GreenHadamardPropagation

/-- The propagated two-point distribution has exactly the transported
positive-frequency Hadamard wavefront cone. -/
@[zil_level physical_theorem]
lemma wavefront_eq
    {𝒜 : Type uA} {𝒟 : Type uD}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {source : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (P : GreenHadamardPropagation (𝒟 := 𝒟) (V' := V') (W' := W') source) :
    Physlib.Distribution.distributionalWavefrontSet
        P.transport.distribution P.transport.probe =
      source.hadamardCone :=
  P.transport.wavefront_eq
    P.source_offConeBounds.isRegularOutsideCone
    P.source_onConeBounds.isSingularOnCone

/-- Analytic Hadamard regularity off the cone propagates to the Green-evolved
distribution. -/
lemma regularOutsideCone
    {𝒜 : Type uA} {𝒟 : Type uD}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {source : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (P : GreenHadamardPropagation (𝒟 := 𝒟) (V' := V') (W' := W') source) :
    P.transport.toData.IsRegularOutsideCone :=
  P.transport.isRegularOutsideCone
    P.source_offConeBounds.isRegularOutsideCone

/-- Analytic singularity on every positive-frequency null covector also
propagates to the Green-evolved distribution. -/
lemma singularOnCone
    {𝒜 : Type uA} {𝒟 : Type uD}
    [AddCommGroup 𝒜] [Module ℝ 𝒜] [Module ℂ 𝒜]
    [AddCommGroup 𝒟] [Module ℝ 𝒟] [Module ℂ 𝒟]
    {V V' : Type} {X Ξ : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [NormedAddCommGroup Ξ]
    {W : 𝒜 →ₗ⋆[ℂ] 𝒜 →ₗ[ℂ] ℂ}
    {W' : 𝒟 →ₗ⋆[ℂ] 𝒟 →ₗ[ℂ] ℂ}
    {source : DistributionalHadamardData
      (𝒜 := 𝒜) (V := V) (X := X) (Ξ := Ξ) (W := W)}
    (P : GreenHadamardPropagation (𝒟 := 𝒟) (V' := V') (W' := W') source) :
    P.transport.toData.IsSingularOnCone :=
  P.transport.isSingularOnCone
    P.source_onConeBounds.isSingularOnCone

end GreenHadamardPropagation

/- ZIL-BEGIN -/

zil attach MaxwellTimeReversalData.toEnergyCauchyData where
  formalizes @ "claim:a-retarded-maxwell-existence-and-energy-theorem-plus-isometric-involutive-time-reversal-derives-advanced-existence-and-the-same-energy-estimate",
  epistemic_status @ "risky",
  supported_by @ "lean:LinearIsometryEquiv.norm_map",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellTimeReversalData.wave_advancedSolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellTimeReversalData.advanced_energy_estimate",
  caveat @ "premise:the-model-specific-pde-proof-must-still-supply-retarded-existence-and-its-energy-estimate-on-the-selected-continuum-carrier",
  caveat @ "premise:time-reversal-must-be-proved-an-isometric-involution-intertwining-the-wave-operator-and-exchanging-the-two-causal-support-sectors",
  caveat @ "claim:advanced-cauchy-theory-is-derived-and-is-not-a-second-independent-pde-certificate"

zil attach MaxwellTimeReversalData.toEnergyComplexDomain where
  formalizes @ "claim:retarded-sector-complex-stability-plus-wigner-conjugate-linear-time-reversal-derives-complex-stability-of-the-advanced-sector",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellTimeReversalData.advancedSector_smul",
  supported_by @ "lean:starRingEnd",
  caveat @ "premise:the-wave-operator-and-retarded-sector-must-be-complex-covariant-on-the-selected-continuum-domain",
  caveat @ "premise:the-source-and-field-time-reversal-isometries-must-satisfy-the-wigner-conjugate-linearity-law",
  caveat @ "claim:advanced-complex-stability-is-derived-and-is-not-an-independent-domain-certificate"

zil attach MaxwellTimeReversalData.catichaKG_intrinsicMaxwell_chain where
  formalizes @ "claim:one-sided-retarded-maxwell-energy-well-posedness-plus-wigner-time-reversal-constructs-the-two-sided-complex-caticha-klein-gordon-intrinsic-maxwell-evolution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellTimeReversalData.toEnergyCauchyData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellTimeReversalData.toEnergyComplexDomain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain",
  caveat @ "premise:retarded-existence-retarded-energy-wave-complex-covariance-and-isometric-conjugate-linear-time-reversal-remain-the-visible-model-specific-inputs",
  caveat @ "claim:no-independent-advanced-existence-energy-or-complex-stability-certificate-is-used"

zil attach MaxwellEnergyCauchyData.toCoerciveSectorData where
  formalizes @ "claim:a-continuous-maxwell-wave-map-with-causal-source-existence-and-retarded-advanced-energy-estimates-derives-bounded-solution-maps-and-continuous-linear-wave-isomorphisms-on-both-causal-sectors",
  epistemic_status @ "risky",
  supported_by @ "lean:LinearMap.mkContinuous",
  supported_by @ "lean:ContinuousLinearEquiv.equivOfInverse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.wave_injectiveOn_retarded",
  caveat @ "premise:the-model-specific-continuum-pde-proof-must-supply-causal-existence-and-the-two-energy-estimates-on-the-chosen-sobolev-or-graph-norm-carrier",
  caveat @ "claim:the-continuous-equivalences-are-conclusions-and-no-longer-independent-pde-premises"

zil attach MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier where
  formalizes @ "claim:complex-covariance-of-the-maxwell-wave-operator-and-complex-stability-of-both-causal-sectors-force-the-energy-constructed-retarded-and-advanced-green-maps-to-be-complex-linear",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.wave_injectiveOn_retarded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.wave_injectiveOn_advanced",
  caveat @ "premise:complex-covariance-of-the-differential-operator-and-complex-scalar-closure-of-the-selected-support-sectors-must-be-proved-on-the-model-specific-domain",
  caveat @ "claim:complex-linearity-of-the-green-maps-is-a-uniqueness-conclusion-not-an-independent-certificate"

zil attach MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain where
  formalizes @ "claim:energy-cauchy-well-posedness-plus-complex-wave-covariance-constructs-the-common-caticha-klein-gordon-intrinsic-maxwell-evolution-without-supplied-green-maps-or-a-supplied-complex-green-certificate",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.wellPosedCauchy_catichaKG_intrinsicMaxwell_chain",
  caveat @ "premise:causal-existence-energy-estimates-wave-complex-covariance-and-sector-stability-remain-the-visible-model-specific-analytic-inputs"

zil attach MaxwellCoerciveSectorData.toEnergyCauchyData where
  formalizes @ "claim:continuous-wave-operator-isomorphisms-on-retarded-and-advanced-support-sectors-derive-causal-existence-and-energy-estimates-with-the-norms-of-the-inverse-operators",
  epistemic_status @ "risky",
  supported_by @ "lean:ContinuousLinearMap.le_opNorm",
  supported_by @ "lean:ContinuousLinearEquiv.apply_symm_apply",
  caveat @ "premise:the-model-specific-normally-hyperbolic-pde-theorem-must-prove-that-the-two-restricted-wave-operators-are-continuous-linear-equivalences"

zil attach MaxwellLaxMilgramGraphData.retardedCoercive where
  formalizes @ "claim:a-positive-retarded-energy-constant-and-its-quadratic-lower-bound-derive-the-lax-milgram-coercivity-proposition",
  epistemic_status @ "risky",
  supported_by @ "lean:IsCoercive",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.retarded_energy_lower",
  caveat @ "premise:the-concrete-gauge-fixed-maxwell-pde-analysis-must-prove-the-positive-constant-and-lower-energy-inequality-on-the-selected-retarded-sobolev-sector",
  caveat @ "claim:coercivity-is-derived-and-is-no-longer-a-proposition-valued-field"

zil attach MaxwellLaxMilgramGraphData.advancedCoercive where
  formalizes @ "claim:a-positive-advanced-energy-constant-and-its-quadratic-lower-bound-derive-the-lax-milgram-coercivity-proposition",
  epistemic_status @ "risky",
  supported_by @ "lean:IsCoercive",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.advanced_energy_lower",
  caveat @ "premise:the-concrete-gauge-fixed-maxwell-pde-analysis-must-prove-the-positive-constant-and-lower-energy-inequality-on-the-selected-advanced-sobolev-sector",
  caveat @ "claim:coercivity-is-derived-and-is-no-longer-a-proposition-valued-field"

zil attach MaxwellLaxMilgramGraphData.toCoerciveSectorData where
  formalizes @ "claim:closed-retarded-and-advanced-sobolev-sectors-with-bounded-weak-maxwell-forms-explicit-positive-energy-lower-bounds-and-riesz-source-coordinates-construct-the-causal-wave-isomorphisms",
  epistemic_status @ "risky",
  supported_by @ "lean:IsCoercive.continuousLinearEquivOfBilin",
  supported_by @ "lean:IsClosed.completeSpace_coe",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.retardedCoercive",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.advancedCoercive",
  caveat @ "premise:closedness-positive-energy-lower-bounds-and-identification-of-the-weak-form-with-the-intrinsic-ricci-coupled-maxwell-operator-must-be-proved-for-the-selected-curved-sobolev-carrier",
  caveat @ "claim:causal-wave-isomorphisms-are-lax-milgram-conclusions-and-not-supplied-green-or-existence-certificates"

zil attach MaxwellLaxMilgramGraphData.retarded_exists_graphNorm_estimate where
  formalizes @ "claim:the-lax-milgram-retarded-inverse-produces-a-causally-supported-maxwell-solution-with-an-explicit-h-one-h-minus-one-graph-norm-bound",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.retardedWaveEquiv_apply",
  supported_by @ "lean:ContinuousLinearMap.le_opNorm",
  caveat @ "premise:the-retarded-sector-is-a-closed-causal-sobolev-subspace-and-the-weak-maxwell-form-is-bounded-coercive"

zil attach MaxwellLaxMilgramGraphData.advanced_exists_graphNorm_estimate where
  formalizes @ "claim:the-lax-milgram-advanced-inverse-produces-a-causally-supported-maxwell-solution-with-an-explicit-h-one-h-minus-one-graph-norm-bound",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.advancedWaveEquiv_apply",
  supported_by @ "lean:ContinuousLinearMap.le_opNorm",
  caveat @ "premise:the-advanced-sector-is-a-closed-causal-sobolev-subspace-and-the-weak-maxwell-form-is-bounded-coercive"

zil attach MaxwellLaxMilgramGraphData.curvedSobolevGraphMaxwell_causal_exists_energy where
  formalizes @ "claim:coercive-weak-intrinsic-maxwell-forms-on-closed-causal-continuum-sobolev-domains-supply-both-retarded-and-advanced-existence-and-quantitative-graph-energy-estimates",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.retarded_exists_graphNorm_estimate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.advanced_exists_graphNorm_estimate",
  caveat @ "premise:this-is-a-genuine-continuum-hilbert-space-theorem-but-model-specific-global-hyperbolicity-support-closedness-coercivity-and-geometric-operator-identification-remain-visible-inputs",
  caveat @ "claim:the-theorem-does-not-infer-hyperbolic-coercivity-from-the-metric-signature-alone"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFourMaxwell_causal_exists_energy where
  formalizes @ "claim:on-the-explicit-infinite-dimensional-bessel-potential-h-one-c-four-carrier-the-curved-intrinsic-maxwell-equation-has-retarded-and-advanced-causal-solutions-with-h-one-h-minus-one-graph-energy-bounds",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.curvedSobolevGraphMaxwell_causal_exists_energy",
  caveat @ "premise:the-concrete-curved-realization-causal-support-closedness-coercivity-and-weak-intrinsic-maxwell-identity-are-fields-of-the-specialized-data",
  caveat @ "scope:this-is-a-cauchy-slice-h-one-c-four-carrier-with-rieszized-h-minus-one-sources-not-a-claim-that-every-lorentzian-manifold-automatically-supplies-the-data"

zil attach MaxwellLaxMilgramGraphData.toGreenData where
  formalizes @ "claim:the-lax-milgram-causal-wave-equivalences-construct-the-global-intrinsic-retarded-and-advanced-maxwell-green-carrier",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toCoerciveSectorData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellCoerciveSectorData.toGreenData",
  caveat @ "claim:no-green-map-is-supplied-independently-both-are-the-continuous-inverses-of-the-lax-milgram-wave-equivalences"

zil attach MaxwellLaxMilgramGraphData.curvedMaxwellGreen_intrinsic_graphEnergy where
  formalizes @ "claim:the-constructed-continuous-retarded-and-advanced-green-maps-have-the-required-causal-support-solve-the-global-intrinsic-curved-maxwell-equations-and-obey-explicit-graph-energy-bounds",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toGreenData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.graphNorm_retardedGreen_le",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.graphNorm_advancedGreen_le",
  caveat @ "premise:causal-sector-closedness-coercivity-riesz-source-coordinates-and-the-weak-to-intrinsic-maxwell-identification-remain-the-model-specific-pde-inputs"

zil attach MaxwellLaxMilgramGraphData.causalGreen_intrinsic_homogeneous_energy where
  formalizes @ "claim:the-difference-of-the-lax-milgram-retarded-and-advanced-green-inverses-is-a-continuous-homogeneous-intrinsic-maxwell-causal-propagator-bounded-by-the-sum-of-the-inverse-norms",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.wave_retardedGreen",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.wave_advancedGreen",
  supported_by @ "lean:ContinuousLinearMap.le_opNorm",
  caveat @ "claim:homogeneity-is-derived-by-subtracting-two-right-inverses-of-the-same-source-not-stored-as-a-causal-propagator-certificate"

zil attach MaxwellLaxMilgramGraphData.causalGreen_eq_zero_iff_exists_causalCore where
  formalizes @ "claim:a-source-is-annihilated-by-the-constructed-pauli-jordan-propagator-exactly-when-it-is-the-wave-image-of-a-field-in-the-common-retarded-advanced-causal-core",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.retardedGreen_wave_of_mem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.advancedGreen_wave_of_mem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.wave_retardedGreen",
  caveat @ "claim:this-is-exactness-on-the-declared-closed-causal-sobolev-sectors-not-a-claim-that-arbitrary-test-function-support-theory-is-automatic"

zil attach MaxwellLaxMilgramGraphData.ker_causalGreen_eq_causalWaveImage where
  formalizes @ "claim:the-kernel-submodule-of-the-constructed-causal-green-map-is-exactly-the-wave-operator-image-of-the-common-causal-core",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreen_eq_zero_iff_exists_causalCore",
  supported_by @ "lean:LinearMap.mem_ker",
  caveat @ "claim:the-gauge-null-relation-is-derived-from-the-green-complex-and-is-not-stored-as-an-independent-equivalence-certificate"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFour_causalSourceQuotient_phaseSpace where
  formalizes @ "claim:on-the-continuum-h-one-r-three-c-four-carrier-sources-modulo-wave-exact-common-core-sources-embed-faithfully-into-global-homogeneous-intrinsic-maxwell-solutions",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.ker_causalGreen_eq_causalWaveImage",
  supported_by @ "lean:LinearMap.quotKerEquivRange",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalSourceQuotient_intrinsic_homogeneous",
  caveat @ "scope:this-constructs-the-linear-causal-phase-space-on-the-selected-continuum-sobolev-carrier-and-does-not-assert-asymptotic-completeness-or-interacting-qed"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFourMaxwellGreen_intrinsic_graphEnergy where
  formalizes @ "claim:on-the-explicit-infinite-dimensional-h-one-c-four-carrier-the-continuous-lax-milgram-green-maps-solve-intrinsic-curved-maxwell-with-causal-support-and-graph-energy-control",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.curvedMaxwellGreen_intrinsic_graphEnergy",
  caveat @ "scope:the-carrier-is-concrete-but-the-curved-realization-and-coercive-causal-weak-form-remain-explicit-data"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFour_causalGreen_intrinsic_homogeneous_energy where
  formalizes @ "claim:on-h-one-r-three-c-four-the-retarded-minus-advanced-maxwell-green-map-is-a-bounded-homogeneous-intrinsic-causal-propagator",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreen_intrinsic_homogeneous_energy",
  caveat @ "scope:this-establishes-the-continuous-causal-propagator-on-the-selected-sobolev-data-not-an-automatic-green-hyperbolicity-theorem-for-every-lorentzian-manifold"

zil attach MaxwellLaxMilgramGraphData.toComplexLinearIntrinsicMaxwellCarrier where
  formalizes @ "claim:complex-covariance-of-the-wave-domain-and-causal-sector-stability-promote-the-lax-milgram-retarded-and-advanced-inverses-to-one-complex-linear-intrinsic-maxwell-carrier",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toGreenData",
  caveat @ "claim:complex-linearity-of-the-green-inverses-is-derived-from-wave-covariance-causal-sector-stability-and-uniqueness-not-added-as-an-independent-certificate",
  caveat @ "premise:complex-covariance-of-the-selected-wave-domain-remains-an-explicit-model-specific-analytic-input"

zil attach MaxwellLaxMilgramGraphData.catichaKG_intrinsicMaxwell_chain where
  formalizes @ "claim:the-complex-lax-milgram-causal-inverses-construct-caticha-functional-klein-gordon-and-intrinsic-curved-maxwell-evolution-as-one-continuum-operator-chain",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toComplexLinearIntrinsicMaxwellCarrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain",
  caveat @ "claim:the-caticha-klein-gordon-operator-is-the-same-complex-linear-intrinsic-maxwell-wave-operator-on-the-declared-common-carrier",
  caveat @ "scope:this-is-the-linear-functional-evolution-carrier-and-does-not-claim-interacting-curved-spacetime-qed"

zil attach MaxwellLaxMilgramGraphData.caticha_causalGreen_intrinsic_homogeneous_energy where
  formalizes @ "claim:the-continuous-lax-milgram-pauli-jordan-field-is-exactly-the-caticha-klein-gordon-causal-field-is-homogeneous-for-both-evolutions-and-obeys-the-curved-maxwell-energy-bound",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_causalPropagator_eq_causalGreen",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreen_intrinsic_homogeneous_energy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_causalPropagator_is_homogeneous",
  caveat @ "claim:one-derived-retarded-minus-advanced-field-carries-all-three-conclusions-no-independent-caticha-causal-solution-is-supplied"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFour_caticha_causalGreen_intrinsic_homogeneous_energy where
  formalizes @ "claim:on-the-infinite-dimensional-h-one-r-three-c-four-carrier-the-same-bounded-causal-field-realizes-caticha-functional-klein-gordon-and-global-intrinsic-curved-maxwell-evolution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_causalGreen_intrinsic_homogeneous_energy",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree",
  caveat @ "premise:the-curved-realization-coercive-causal-weak-form-and-complex-domain-covariance-are-visible-inputs-of-the-h-one-graph-datum",
  caveat @ "scope:this-is-a-genuine-continuum-sobolev-carrier-not-a-finite-mode-approximation"

zil attach MaxwellLaxMilgramGraphData.causalGreenComplex where
  formalizes @ "claim:the-lax-milgram-retarded-minus-advanced-propagator-is-a-genuine-complex-continuous-linear-map-with-the-sum-of-causal-inverse-norms-as-an-explicit-bound",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreen_smul",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.norm_causalGreen_le",
  supported_by @ "lean:LinearMap.mkContinuous",
  caveat @ "claim:complex-linearity-and-continuity-are-derived-for-the-already-constructed-causal-propagator-not-supplied-by-a-new-green-certificate"

zil attach MaxwellLaxMilgramGraphData.causalSesquilinearHadamardCarrier_properties where
  formalizes @ "claim:pullback-through-the-constructed-complex-continuous-maxwell-causal-propagator-preserves-hermiticity-positivity-ccr-compatibility-and-positive-frequency-microlocal-support",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.pullback_properties",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreenComplex",
  caveat @ "premise:the-field-hadamard-carrier-symplectic-pullback-identity-and-cone-preserving-covector-transport-remain-explicit-analytic-inputs"

zil attach MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_propagation where
  formalizes @ "claim:one-complex-continuous-pauli-jordan-map-is-the-caticha-klein-gordon-causal-field-the-bounded-homogeneous-intrinsic-maxwell-field-and-the-map-pulling-the-field-two-point-distribution-to-an-exactly-hadamard-source-distribution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalDistributionalHadamardTransport",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.wavefront_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_causalGreen_intrinsic_homogeneous_energy",
  caveat @ "premise:field-regularity-off-and-singularity-on-the-hadamard-cone-a-target-distributional-realization-and-bidirectional-localized-fourier-probe-transport-are-required",
  caveat @ "claim:the-target-wavefront-equality-is-derived-from-probe-pairing-transport-and-is-not-copied-into-data"

zil attach MaxwellLaxMilgramGraphData.radialCausalDistributionalHadamard_wavefront_eq where
  formalizes @ "claim:the-explicit-coulomb-weighted-retarded-minus-advanced-dirac-distribution-enters-the-caticha-maxwell-hadamard-spine-as-the-concrete-target-and-inherits-the-source-hadamard-cone-from-quantitative-fourier-bounds-and-bidirectional-probe-transport",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelDistribution_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.radialCausalDistributionalHadamardTransport",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.wavefront_eq",
  caveat @ "premise:the-representation-identity-bidirectional-localized-fourier-pairing-and-source-off-cone-upper-and-on-cone-lower-bounds-remain-explicit",
  caveat @ "scope:the-target-is-the-one-dimensional-fixed-radius-radial-pauli-jordan-distribution-and-is-not-relabeled-as-a-full-four-dimensional-maxwell-bivector-parametrix"

zil attach MaxwellLaxMilgramGraphData.curvedHOneFour_caticha_maxwell_causal_distributional_hadamard_propagation where
  formalizes @ "claim:on-the-infinite-dimensional-h-one-r-three-c-four-carrier-the-constructed-complex-continuous-maxwell-propagator-simultaneously-realizes-caticha-klein-gordon-evolution-energy-controlled-curved-maxwell-evolution-and-exact-distributional-hadamard-propagation",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_propagation",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree",
  caveat @ "scope:this-is-the-concrete-continuum-cauchy-slice-carrier-the-curved-realization-coercivity-complex-covariance-and-microlocal-probe-transport-remain-visible-inputs"

zil attach MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_atlas_chain where
  formalizes @ "claim:the-same-complex-continuous-causal-propagator-carries-caticha-functional-evolution-a-positive-hermitian-ccr-compatible-distributional-hadamard-pullback-energy-controlled-intrinsic-maxwell-evolution-and-coordinate-independence-across-a-levi-civita-atlas",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_propagation",
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.pullbackSesquilinearTwoPoint_isHermitian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.pullbackSesquilinearTwoPoint_isPositive",
  caveat @ "premise:the-field-two-point-laws-symplectic-pullback-microlocal-regularity-and-singularity-bidirectional-probe-transport-and-atlas-smoothness-remain-explicit",
  caveat @ "claim:this-replaces-the-older-unrelated-bilinear-kernel-conjunction-with-a-genuine-sesquilinear-distribution-pulled-back-through-the-constructed-causal-map",
  caveat @ "scope:the-theorem-instantiates-directly-on-curved-maxwell-h-one-graph-data-and-does-not-claim-that-every-lorentzian-manifold-supplies-the-analytic-inputs"

zil attach MaxwellLaxMilgramGraphData.caticha_hadamard_maxwell_microcausality_of_laxMilgram where
  formalizes @ "claim:coercive-causal-sobolev-forms-and-complex-domain-covariance-discharge-the-green-and-complex-linearity-legs-of-the-caticha-hadamard-aqft-atlas-independent-maxwell-chain",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toCoerciveSectorData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toComplexLinearIntrinsicMaxwellCarrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellCoerciveSectorData.caticha_hadamard_maxwell_microcausality_of_coercive",
  caveat @ "premise:the-hermitian-kernel-compatible-levi-civita-atlas-and-smoothness-conditions-remain-explicit-because-they-are-independent-of-lax-milgram-well-posedness",
  caveat @ "claim:no-independent-green-map-or-complex-linear-green-certificate-is-used"

zil attach MaxwellCoerciveSectorData.toGreenData where
  formalizes @ "claim:coercive-retarded-and-advanced-wave-operator-isomorphisms-construct-the-global-intrinsic-maxwell-green-system",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellCoerciveSectorData.toEnergyCauchyData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.toGreenData",
  caveat @ "claim:operator-isomorphism-to-green-construction-not-an-unconditional-proof-that-every-globally-hyperbolic-lorentzian-metric-supplies-the-required-isomorphisms"

zil attach MaxwellCoerciveSectorData.catichaKG_intrinsicMaxwell_chain where
  formalizes @ "claim:on-a-common-complex-linear-continuum-carrier-coercive-causal-wave-isomorphisms-construct-caticha-klein-gordon-and-intrinsic-maxwell-green-evolution-as-the-same-operator-chain",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.wellPosedCauchy_catichaKG_intrinsicMaxwell_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellCoerciveSectorData.toGreenData",
  caveat @ "premise:the-causal-wave-isomorphisms-and-complex-linearity-on-the-selected-continuum-domain-remain-model-specific-analytic-inputs"

zil attach MaxwellCoerciveSectorData.caticha_hadamard_maxwell_microcausality_of_coercive where
  formalizes @ "claim:coercive-causal-wave-isomorphisms-discharge-the-green-existence-leg-of-the-caticha-hadamard-aqft-atlas-independent-maxwell-microcausality-chain",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality.caticha_hadamard_maxwell_microcausality",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellCoerciveSectorData.toGreenData",
  caveat @ "premise:coercive-wave-isomorphisms-complex-linearity-atlas-smoothness-and-hermitian-kernel-data-remain-explicit",
  caveat @ "claim:this-removes-the-independent-green-map-premise-but-does-not-identify-a-hermitian-kernel-with-a-distributional-hadamard-state"

zil attach MaxwellEnergyCauchyData.toGreenData where
  formalizes @ "claim:globally-hyperbolic-causal-existence-plus-retarded-and-advanced-energy-estimates-construct-bounded-continuous-green-operators-for-the-intrinsic-ricci-coupled-maxwell-wave-operator",
  epistemic_status @ "risky",
  supported_by @ "lean:PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.toIntrinsicMaxwellGreenData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.wave_injectiveOn_retarded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.toGreenData_retarded_eq_continuous",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellEnergyCauchyData.toGreenData_advanced_eq_continuous",
  caveat @ "premise:the-selected-continuum-carrier-must-supply-causal-existence-and-the-two-energy-estimates-from-a-concrete-normally-hyperbolic-pde-theorem",
  caveat @ "global-hyperbolicity-of-the-spacetime-is-geometric-input-it-does-not-by-itself-prove-these-analytic-estimates"

zil attach DistributionalHadamardData.OffConeRapidDecayBounds.isRegularOutsideCone where
  formalizes @ "claim:explicit-all-order-localized-fourier-upper-bounds-at-every-nonzero-off-cone-covector-prove-distributional-microlocal-regularity-off-the-hadamard-cone",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Distribution.HasRapidFourierDecayOn",
  caveat @ "premise:the-model-specific-pseudodifferential-analysis-must-supply-a-probe-and-a-nonnegative-weighted-amplitude-bound-at-every-polynomial-order",
  caveat @ "claim:off-cone-regularity-is-derived-and-is-not-a-certificate-field"

zil attach DistributionalHadamardData.OnConeLowerEscapeBounds.isSingularOnCone where
  formalizes @ "claim:polynomial-lower-escape-for-every-localized-probe-at-every-on-cone-covector-proves-genuine-distributional-singularity-on-the-hadamard-cone",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Distribution.not_hasRapidFourierDecayOn_of_hasPolynomialLowerEscapeOn",
  caveat @ "premise:the-model-specific-parametrix-analysis-must-prove-nonzero-frequency-and-a-weighted-amplitude-that-escapes-every-bound-for-each-candidate-probe",
  caveat @ "claim:on-cone-singularity-is-derived-and-is-not-a-negated-regularity-certificate-field"

zil attach DistributionalHadamardData.wavefront_eq_of_fourierBounds where
  formalizes @ "claim:quantitative-off-cone-upper-bounds-and-on-cone-lower-escape-identify-the-computed-distributional-wavefront-set-exactly-with-the-positive-frequency-hadamard-cone",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.OffConeRapidDecayBounds.isRegularOutsideCone",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.OnConeLowerEscapeBounds.isSingularOnCone",
  caveat @ "claim:neither-half-of-the-wavefront-equality-is-stored-as-a-conclusion-shaped-certificate"

zil attach GreenHadamardPropagation.wavefront_eq where
  formalizes @ "claim:bidirectional-localized-fourier-transport-propagates-the-exact-positive-frequency-hadamard-wavefront-set-to-the-green-evolved-two-point-distribution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.wavefront_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_of_fourierBounds",
  caveat @ "premise:quantitative-off-cone-fourier-upper-bounds-on-cone-lower-escape-and-complete-bidirectional-probe-pairing-transport-are-the-model-specific-propagation-of-singularities-inputs"

zil_file_contract physlib.globallyHyperbolicGreenHadamard where
  promises "A retarded Maxwell existence and energy theorem, together with isometric involutive time reversal, derives the advanced theorem with the same energy constant and hence the full two-sided Cauchy carrier. Retarded complex covariance plus Wigner conjugate-linearity further derives advanced complex stability and constructs the Caticha/Klein-Gordon/intrinsic-Maxwell chain without independent advanced analytic or complex-domain certificates. More generally, a continuous wave operator, causal source existence, and quantitative retarded/advanced energy estimates derive causal-sector uniqueness, bounded solution selectors, and continuous linear wave isomorphisms on both support sectors; conversely those isomorphisms recover the existence and estimates with inverse-operator norms. A deeper continuum route starts from the repository's complete H1 C4 carrier, closed retarded and advanced Sobolev domains, bounded weak Maxwell forms, explicit positive quadratic energy lower bounds, and Riesz H-minus-one source coordinates. Those inequalities derive Lax-Milgram coercivity; Lax-Milgram then constructs the two causal wave equivalences and proves explicit H1/H-minus-one graph-norm existence and energy bounds. The resulting Green operators are exactly the continuous inverses, solve the global intrinsic curved Maxwell equations, retain causal-sector membership and satisfy explicit graph-norm bounds. Their difference is a continuous homogeneous causal propagator bounded by the sum of the two inverse norms. Both inverse laws then prove the exact Green complex: the causal kernel is the wave image of the common retarded/advanced core, so the source quotient is derived rather than postulated and embeds faithfully into homogeneous intrinsic Maxwell solutions on the explicit H1 C4 carrier. Complex covariance of the same graph domain derives a genuine complex continuous Pauli-Jordan operator and identifies it with the Caticha/Klein-Gordon causal field; the common field is homogeneous under Caticha functional evolution and intrinsic curved Maxwell evolution with the same quantitative energy bound. Pulling a corrected sesquilinear two-point function through that exact operator preserves Hermiticity, positivity and the CCR law. Explicit all-order localized-Fourier upper bounds derive regularity off the proposed cone, while polynomial lower escape at every candidate on-cone probe derives singularity on the cone. A complete bidirectional localized-Fourier transport carries those proved Hadamard halves to the pulled-back source distribution and derives exact equality with the positive-frequency Hadamard cone, including on the explicit H1 C4 carrier. The concrete fixed-radius Coulomb-weighted retarded-minus-advanced Dirac distribution is exposed as an explicit transport target, with its representation, probe pairing and quantitative microlocal obligations kept visible. The resulting corrected distributional field and the energy-bounded causal Maxwell solution are finally transported across compatible Levi-Civita representatives, closing the atlas-independent Caticha-AQFT-Maxwell chain without an unrelated bilinear kernel."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData",
    "lean:PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.toIntrinsicMaxwellGreenData",
    "lean:IsCoercive.continuousLinearEquivOfBilin",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree",
    "lean:Physlib.Distribution.HasPolynomialLowerEscapeOn",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelDistribution",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.wavefront_eq"
  ]
  forbids_substitutes [
    "supplying-an-independent-advanced-pde-certificate-when-isometric-time-reversal-covariance-is-available",
    "storing-retarded-and-advanced-linear-maps-without-deriving-linearity-from-existence-and-energy-uniqueness",
    "claiming-global-hyperbolicity-alone-proves-maxwell-cauchy-estimates",
    "storing-causal-existence-or-graph-energy-estimates-when-they-can-be-derived-from-closed-weak-sobolev-forms-with-positive-energy-lower-bounds",
    "storing-a-homogeneous-causal-propagator-when-it-can-be-derived-as-retarded-minus-advanced",
    "supplying-an-independent-gauge-null-relation-when-the-causal-green-kernel-can-be-derived-as-the-wave-image-of-the-common-causal-core",
    "quotienting-sources-by-an-unrelated-equivalence-instead-of-the-exact-kernel-of-the-constructed-causal-propagator",
    "storing-independent-complex-linear-green-certificates-when-wave-covariance-causal-sector-stability-and-uniqueness-derive-them",
    "introducing-a-second-caticha-causal-field-instead-of-identifying-the-existing-lax-milgram-pauli-jordan-propagator",
    "conjoining-an-unrelated-hadamard-certificate-instead-of-pulling-the-two-point-distribution-through-the-constructed-causal-propagator",
    "copying-a-target-hadamard-cone-without-bidirectional-localized-fourier-probe-pairing-transport",
    "claiming-atlas-independence-by-conjoining-two-local-equations-without-applying-the-levi-civita-atlas-equivalence",
    "claiming-that-lorentzian-signature-alone-implies-the-coercivity-needed-by-lax-milgram",
    "storing-lax-milgram-coercivity-as-a-proposition-field-instead-of-supplying-a-positive-energy-constant-and-its-quadratic-lower-bound",
    "storing-off-cone-regularity-or-on-cone-singularity-instead-of-supplying-localized-fourier-upper-and-lower-growth-estimates",
    "copying-the-proposed-hadamard-cone-into-a-wavefront-certificate-without-localized-fourier-regularity-and-singularity-theorems"
  ]
  witnessed_by [
    RetardedMaxwellEnergyCauchyData.retardedSolution_mem,
    RetardedMaxwellEnergyCauchyData.wave_retardedSolution,
    MaxwellTimeReversalData.advancedSolution_mem,
    MaxwellTimeReversalData.wave_advancedSolution,
    MaxwellTimeReversalData.advanced_exists,
    MaxwellTimeReversalData.advanced_energy_estimate,
    MaxwellTimeReversalData.toEnergyCauchyData,
    MaxwellTimeReversalData.advancedSector_smul,
    MaxwellTimeReversalData.toEnergyComplexDomain,
    MaxwellTimeReversalData.catichaKG_intrinsicMaxwell_chain,
    MaxwellEnergyCauchyData.retardedSectorSolutionContinuous,
    MaxwellEnergyCauchyData.advancedSectorSolutionContinuous,
    MaxwellEnergyCauchyData.retardedContinuous,
    MaxwellEnergyCauchyData.advancedContinuous,
    MaxwellEnergyCauchyData.toGreenData_retarded_eq_continuous,
    MaxwellEnergyCauchyData.toGreenData_advanced_eq_continuous,
    MaxwellEnergyCauchyData.norm_retardedContinuous_le,
    MaxwellEnergyCauchyData.norm_advancedContinuous_le,
    MaxwellEnergyCauchyData.retardedWaveEquiv,
    MaxwellEnergyCauchyData.advancedWaveEquiv,
    MaxwellEnergyCauchyData.toCoerciveSectorData,
    MaxwellEnergyComplexDomain.retardedSolution_smul,
    MaxwellEnergyComplexDomain.advancedSolution_smul,
    MaxwellEnergyComplexDomain.toComplexLinearIntrinsicMaxwellCarrier,
    MaxwellEnergyComplexDomain.catichaKG_intrinsicMaxwell_chain,
    MaxwellLaxMilgramGraphData.retardedCoercive,
    MaxwellLaxMilgramGraphData.advancedCoercive,
    MaxwellLaxMilgramGraphData.retardedWaveEquiv_apply,
    MaxwellLaxMilgramGraphData.advancedWaveEquiv_apply,
    MaxwellLaxMilgramGraphData.toCoerciveSectorData,
    MaxwellLaxMilgramGraphData.retarded_exists_graphNorm_estimate,
    MaxwellLaxMilgramGraphData.advanced_exists_graphNorm_estimate,
    MaxwellLaxMilgramGraphData.curvedSobolevGraphMaxwell_causal_exists_energy,
    MaxwellLaxMilgramGraphData.curvedHOneFourMaxwell_causal_exists_energy,
    MaxwellLaxMilgramGraphData.retardedGreen,
    MaxwellLaxMilgramGraphData.advancedGreen,
    MaxwellLaxMilgramGraphData.toGreenData,
    MaxwellLaxMilgramGraphData.wave_retardedGreen,
    MaxwellLaxMilgramGraphData.wave_advancedGreen,
    MaxwellLaxMilgramGraphData.graphNorm_retardedGreen_le,
    MaxwellLaxMilgramGraphData.graphNorm_advancedGreen_le,
    MaxwellLaxMilgramGraphData.wave_causalGreen,
    MaxwellLaxMilgramGraphData.norm_causalGreen_le,
    MaxwellLaxMilgramGraphData.retardedGreen_wave_of_mem,
    MaxwellLaxMilgramGraphData.advancedGreen_wave_of_mem,
    MaxwellLaxMilgramGraphData.causalGreen_wave_of_mem_causalCore,
    MaxwellLaxMilgramGraphData.causalGreen_eq_zero_iff_exists_causalCore,
    MaxwellLaxMilgramGraphData.ker_causalGreen_eq_causalWaveImage,
    MaxwellLaxMilgramGraphData.causalSourceQuotientEquivRange,
    MaxwellLaxMilgramGraphData.causalSourceQuotientToHomogeneous_injective,
    MaxwellLaxMilgramGraphData.causalSourceQuotient_intrinsic_homogeneous,
    MaxwellLaxMilgramGraphData.curvedHOneFour_causalSourceQuotient_phaseSpace,
    MaxwellLaxMilgramGraphData.causalGreen_intrinsic_homogeneous_energy,
    MaxwellLaxMilgramGraphData.curvedMaxwellGreen_intrinsic_graphEnergy,
    MaxwellLaxMilgramGraphData.curvedHOneFourMaxwellGreen_intrinsic_graphEnergy,
    MaxwellLaxMilgramGraphData.curvedHOneFour_causalGreen_intrinsic_homogeneous_energy,
    MaxwellLaxMilgramGraphData.toComplexLinearIntrinsicMaxwellCarrier,
    MaxwellLaxMilgramGraphData.retardedGreen_smul,
    MaxwellLaxMilgramGraphData.advancedGreen_smul,
    MaxwellLaxMilgramGraphData.causalGreen_smul,
    MaxwellLaxMilgramGraphData.catichaKG_intrinsicMaxwell_chain,
    MaxwellLaxMilgramGraphData.caticha_causalPropagator_eq_causalGreen,
    MaxwellLaxMilgramGraphData.causalGreenComplexLinear_apply,
    MaxwellLaxMilgramGraphData.causalGreenComplex,
    MaxwellLaxMilgramGraphData.causalGreenComplex_apply,
    MaxwellLaxMilgramGraphData.caticha_causalGreen_intrinsic_homogeneous_energy,
    MaxwellLaxMilgramGraphData.curvedHOneFour_caticha_causalGreen_intrinsic_homogeneous_energy,
    MaxwellLaxMilgramGraphData.causalSesquilinearHadamardCarrier_properties,
    MaxwellLaxMilgramGraphData.causalDistributionalHadamardTransport,
    MaxwellLaxMilgramGraphData.causalDistributionalHadamardData,
    MaxwellLaxMilgramGraphData.radialCausalDistributionalHadamardTransport,
    MaxwellLaxMilgramGraphData.radialCausalDistributionalHadamard_wavefront_eq,
    MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_propagation,
    MaxwellLaxMilgramGraphData.curvedHOneFour_caticha_maxwell_causal_distributional_hadamard_propagation,
    MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_atlas_chain,
    MaxwellLaxMilgramGraphData.caticha_hadamard_maxwell_microcausality_of_laxMilgram,
    MaxwellCoerciveSectorData.toEnergyCauchyData,
    MaxwellCoerciveSectorData.toGreenData,
    MaxwellCoerciveSectorData.toGreenData_retarded_eq_continuous,
    MaxwellCoerciveSectorData.toGreenData_advanced_eq_continuous,
    MaxwellCoerciveSectorData.norm_retarded_le,
    MaxwellCoerciveSectorData.norm_advanced_le,
    MaxwellCoerciveSectorData.retarded_advanced_solve_intrinsicMaxwell,
    MaxwellCoerciveSectorData.catichaKG_intrinsicMaxwell_chain,
    MaxwellCoerciveSectorData.caticha_hadamard_maxwell_microcausality_of_coercive,
    MaxwellEnergyCauchyData.wave_injectiveOn_retarded,
    MaxwellEnergyCauchyData.wave_injectiveOn_advanced,
    MaxwellEnergyCauchyData.toWellPosedCauchyData,
    MaxwellEnergyCauchyData.toGreenData,
    MaxwellEnergyCauchyData.retarded_advanced_solve_intrinsicMaxwell,
    DistributionalHadamardData.OffConeRapidDecayBounds.isRegularOutsideCone,
    DistributionalHadamardData.OnConeLowerEscapeBounds.isSingularOnCone,
    DistributionalHadamardData.wavefront_eq_of_fourierBounds,
    GreenHadamardPropagation.regularOutsideCone,
    GreenHadamardPropagation.singularOnCone,
    GreenHadamardPropagation.wavefront_eq
  ]

/- ZIL-END -/

end GloballyHyperbolicGreenHadamard

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity
