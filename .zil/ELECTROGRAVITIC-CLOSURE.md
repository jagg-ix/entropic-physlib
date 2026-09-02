# Electrogravitic closure ledger

This file is the ZIL-side documentation companion to
`docs/EntropicDynamicsClosure.md`. It records theorem boundaries and inspection
rules. It adds no Lean definitions, axioms, or proofs.

## Frozen scientific reference

The current classification is based on scientific commit
`fa19aa2505d4939cca423ead6fdfa64528cb7afe`
(`construct canonical Lorentzian measure and global Palatini action`).
Documentation commits after that point do not change the proof status.

## Strongest witnesses

```text
Physlib.QuantumMechanics.ComplexAction.ComplexEinstein
  .ElectroGravitationalFieldEquations
  .derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity

Physlib.Meta.EntropicDynamicsFullEinsteinSource
  .entropicDynamics_derives_physics_metricBuilt_variational

Physlib.QuantumMechanics.ComplexAction.Curvature
  .GlobalEinsteinHilbertAction.canonicalEinsteinHilbertAction

Physlib.QuantumMechanics.ComplexAction.Curvature
  .GlobalEinsteinHilbertAction
  .canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero
```

These witnesses establish metric-built and action-certified field-equation
closure, plus an atlas-independent global Einstein–Hilbert action with dominated
Palatini differentiation.

## Current claim graph

```text
metric field g
  -> canonical Lorentzian measure mu_g
  -> intrinsic scalar curvature R[g]
  -> global Einstein-Hilbert action integral
  -> dominated Palatini derivative
  -> global gravitational stationarity under explicit hypotheses

metric field g and inverse gInv
  -> Frechet metric jet
  -> Levi-Civita connection Gamma[g]
  -> connection jet
  -> Riemann[g]
  -> Ricci[g]
  -> scalar curvature R[g]
  -> Einstein tensor G[g]

Faraday field F = dA
  -> gauge-invariant Maxwell stress tensor T[F]

certified action derivative = coupled first variation
  + action stationarity
  -> coupled stationarity
  -> metric-built ElectroGravitationalFieldEquation
  -> complete complex source balance
  -> public entropic-dynamics capstone
```

## Action and derivative inventory

### Coupled action and certificate

```text
coupledElectrograviticFirstVariationLinear
linearizedCoupledElectrograviticActionGerm
linearizedCoupledElectrograviticActionGerm_hasFDerivAt
ElectrograviticActionDerivativeData
ElectrograviticActionDerivativeData.stationary_iff_coupled
derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity
```

### Sector and global actions

```text
Electromagnetism.ElectromagneticPotential.lagrangian
Electromagnetism.ElectromagneticPotential
  .lagrangian_hasVarGradientAt_gradLagrangian

Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
  .complexReggeAction
Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
  .hasDerivAt_complexReggeAction_leg

Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
  .canonicalEinsteinHilbertAction
Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
  .canonicalEinsteinHilbertActionPath_hasDerivAt_of_dominated
Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
  .canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero
```

### Einstein–Hilbert / Palatini / boundary variation

```text
hasDerivAt_det_affine_metric
hasDerivAt_inverseMatrix_affine
hasDerivAt_lorentzianVolumeDensity_affine
hasDerivAt_einsteinHilbertDensity_affine
riemannFromConnection_hasDerivAt_connectionVariation
ricciFromConnection_hasDerivAt_connectionVariation
scalarCurvatureFromConnection_hasDerivAt_palatini
einsteinHilbertDensity_hasDerivAt_palatini
ghy_cancels_fixedMetric_palatiniBoundary
integratedEinsteinHilbertPalatiniVariation_eq_bulk_of_boundary
```

The determinant, inverse, volume, Einstein–Hilbert density, Palatini curvature,
GHY boundary, and global gravitational integration layers are not open.

The remaining action target is one concrete global nonlinear
Einstein–Maxwell–entropic action whose derivative instantiates the existing
coupled certificate.

## Metric and curvature closure

The chartwise chain consumed by the public capstone is directly proved:

```text
IsFourMetricPair
metricBuiltConnectionField
metricBuiltConnectionField_isLeviCivita
metricBuiltConnectionJetAt
metricBuiltRiemannAt
metricBuiltRiemannAt_firstBianchi
metricBuiltRicciAt
metricBuiltScalarAt
metricBuiltEinsteinAt
metricBuiltStationary_iff_complexEinstein
derive_metricBuilt_electrogravitic_field_equation
```

The intrinsic layer proves atlas independence of Levi-Civita curvature, Ricci
contractions, raised Ricci, the Bochner wave operator, and scalar curvature.

Classification:

```text
metric_to_curvature_chartwise: directly_proved
intrinsic_curvature_atlas_independence: directly_proved
global_einstein_hilbert_action: directly_proved_with_explicit_scope
```

## Global curved-spacetime PDE closure

### Directly proved global equation layers

```text
PseudoRiemannianMetric.TensorRicciCoupledMaxwellOn
PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff
PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff
PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOperator
```

These define a global intrinsic Ricci-coupled Maxwell PDE at every manifold
point, prove its frame-free/operator form, and prove atlas independence.

The distributional electromagnetic subsystem separately proves sourced Maxwell
on every Schwartz test function.

### Conditional global causal solutions

```text
PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData
PseudoRiemannianMetric.IntrinsicMaxwellGreenData
PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData
  .toIntrinsicMaxwellGreenData
PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves
PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves
```

Causal existence and uniqueness data imply linear retarded and advanced Green
operators and global solutions. The well-posed Cauchy-data structure itself is
analytic input; it is not constructed from global hyperbolicity in the inspected
chain.

### Conditional local nonlinear Einstein evolution

```text
GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution
GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique
```

Picard–Lindelöf gives a local trajectory on an arbitrary complete Banach phase
space, and Lipschitz control gives uniqueness. The concrete gauge-reduced
Einstein vector field, its regularity, and `fieldEquation_propagates` remain
explicit inputs.

### Constraint infrastructure boundary

The canonical-gravity and Ipek–Caticha modules formalize constraint carriers,
Gauss–Codazzi identities, matter-sourced Hamiltonian constraints,
deformation-algebra consequences under decoupling, and metric-velocity /
extrinsic-curvature identities. They explicitly withhold:

```text
full field-dependent Dirac structure functions
full lapse-and-shift ADM evolution
momentum evolution with spatial Ricci
concrete Hamiltonian/momentum constraint propagation
```

The Regge initial-value layer proves combinatorial determination for selected
closed systems and records the open-space boundary obstruction.

### PDE status matrix

```text
global_einstein_hilbert_action: directly_proved
global_intrinsic_maxwell_equation: directly_proved
global_maxwell_atlas_independence: directly_proved
sourced_distributional_maxwell: directly_proved_on_separate_carrier
retarded_advanced_global_maxwell_solutions: conditional_on_cauchy_green_data
local_nonlinear_complex_einstein_evolution: conditional_on_vector_field_and_propagation_data
local_nonlinear_einstein_uniqueness: conditional_on_lipschitz_control
concrete_maxwell_cauchy_construction_from_global_hyperbolicity: not_closed_end_to_end
concrete_adm_constraint_propagation: not_closed_end_to_end
maximal_globally_hyperbolic_coupled_development: not_located
```

Forbidden simplifications:

- do not report the global PDE row as simply “No”;
- do not report conditional Green solutions as unconditional construction of
  Green-hyperbolicity;
- do not report a Banach-space Picard theorem as a concrete Einstein PDE
  reduction without the supplied vector-field and propagation data;
- do not call local existence global existence;
- do not call an equation imposed at every point a Cauchy well-posedness theorem.

## BCJ amplitude closure

```text
entropicJacobiBCJDuality
entropicJacobiBCJChannels
entropicJacobiBCJAmplitude_eq
entropicJacobiGaugeAmplitude_eq_sq
entropicJacobiDoubleCopy_sq_eq_gauge_product
ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude
```

Classification:

```text
explicit_entropic_three_channel_bcj_model: directly_proved
arbitrary_interacting_yang_mills_bcj_representation: not_claimed
```

## Corrected status policy

Use:

```text
directly_proved
proved_with_explicit_scope
conditional_on_explicit_analytic_data
not_closed_end_to_end
not_located
```

Do not replace scoped proofs by “missing”, or scoped model results by universal
claims.

## Remaining targets

1. Construct `WellPosedIntrinsicMaxwellCauchyData` from explicit global
   hyperbolicity, support, and energy estimates.
2. Instantiate `GFreeNonlinearEinsteinCauchyProblem` with the actual ADM/Sobolev
   phase space and prove constraint propagation.
3. Construct one concrete global coupled action derivative certificate.
4. Formalize continuation and maximal globally hyperbolic development without
   conflating local and global existence.

## Read-only graph export

```bash
lake exe zil-scan \
  Physlib.Meta.EntropicDynamicsFullEinsteinSource \
  /tmp/entropic-dynamics-full-source.zilevents.json \
  --no-cache --force
```

Lean theorem statements and `SpineAxiomAudit` remain authoritative.
