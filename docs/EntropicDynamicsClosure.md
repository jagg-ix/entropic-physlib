# Entropic-dynamics physical-theory closure

This document records the strongest currently justified end-to-end status of the
entropic-dynamics / complex-action program. It is a documentation and audit
surface; Lean remains the proof authority.

The scientific assessment is frozen at commit
`fa19aa2505d4939cca423ead6fdfa64528cb7afe`
(`construct canonical Lorentzian measure and global Palatini action`).
Documentation commits following that revision do not change the scientific
status.

## Status vocabulary

Broad physical claims are not classified with a bare yes/no. Each interface is
assigned one of:

- **directly proved** — a named Lean theorem proves the stated interface;
- **proved with explicit scope** — the theorem exists, but only for a declared
  carrier such as one coordinate chart, a linearized action germ, an abstract
  Banach phase space, or an explicit three-channel amplitude model;
- **conditional on explicit analytic data** — the mathematical consequence is
  proved, while existence, regularity, support, constraint propagation, or
  other analytic data remain structure fields;
- **not closed end-to-end** — relevant pieces exist, but no theorem constructs
  and connects the complete requested physical interface.

“Not globally well posed” does not mean “no global equation exists”, and
“conditional Green data” does not mean “no global propagator theorem exists”.
Conversely, a theorem accepting a well-posedness or propagation certificate must
not be reported as an unconditional construction of that certificate.

## Strongest current theorem surfaces

### Public entropic-dynamics capstone

```lean
Physlib.Meta.EntropicDynamicsFullEinsteinSource
  .entropicDynamics_derives_physics_metricBuilt_variational
```

This theorem replaces independent Ricci and scalar-curvature inputs by the
repository chain

```text
g -> g⁻¹ -> ∂g -> Γ[g] -> ∂Γ[g] -> Riemann[g]
  -> Ric[g] -> R[g] -> G[g]
```

and replaces three separate stationarity predicates by one direct-sum coupled
first-variation premise. It returns the quantum, reversible-limit, Newtonian,
weak-field, and complex-Einstein conclusions together with inverse-metric,
source-free Maxwell, homogeneous Maxwell, torsion-free, metric-compatible, and
first-Bianchi certificates.

### Strongest action-to-field-equation interface

```lean
Physlib.QuantumMechanics.ComplexAction.ComplexEinstein
  .ElectroGravitationalFieldEquations
  .derive_metricBuilt_electrogravitic_field_equation_from_action_stationarity
```

This theorem accepts an actual action through
`ElectrograviticActionDerivativeData`. Its load-bearing field is a
`HasFDerivAt` proof identifying the action derivative with the coupled
first-variation map. Stationarity of that derivative produces the metric-built
Einstein–Maxwell–entropic equations.

### Concrete coupled differentiated action

```lean
linearizedCoupledElectrograviticActionGerm
linearizedCoupledElectrograviticActionGerm_hasFDerivAt
linearizedCoupledElectrograviticActionGerm_fderiv_apply
```

This is one named coupled action with an actual Fréchet derivative. Its scope is
a linearized germ on the finite-dimensional variation carrier.

### Nonlinear Maxwell field-space action

```lean
MaxwellLocalFieldSpace
maxwellLocalFieldDensity
maxwellLocalFieldDensity_differentiableAt
maxwellLocalFieldDensity_fderiv_metricDirection
MaxwellFieldSpace
maxwellFieldAction
maxwellFieldDensityDerivative
maxwellFieldAction_hasFDerivAt
```

The Maxwell coordinate density is now differentiated on all 48 independent
local coordinates \((g_{\mu\nu},g^{\mu\nu},F_{\mu\nu})\), then lifted to the
supremum-norm Banach space of bounded continuous fields. The global derivative
is constructed by dominated integration rather than accepted as a derivative
certificate. Its evaluation on the inverse-compatible metric tangent
\((h,-g^{-1}hg^{-1},0)\) is proved equal to the Maxwell stress-energy pairing.

The scope is deliberately narrower than a coupled gravitational result: the
measure is a fixed coordinate measure and the three Maxwell field coordinates
are independent off the background. The theorem does not yet construct the
Einstein--Hilbert curvature-jet and boundary variation as a Fréchet derivative
on a manifold-metric field space.

### Global Einstein–Hilbert action

```lean
Physlib.QuantumMechanics.ComplexAction.Curvature
  .GlobalEinsteinHilbertAction.canonicalEinsteinHilbertAction
```

The gravitational action is integrated on the manifold against the
metric-built Lorentzian volume measure. Scalar curvature is expressed as the
basis-independent trace of raised Ricci; certified frame and Levi-Civita atlas
representatives compute the same scalar. The module also proves dominated
Palatini differentiation of an actual global action path and stationarity when
the bulk derivative vanishes almost everywhere.

This closes the former “atlas-independent action integration” gap for the
Einstein–Hilbert sector. It does not by itself construct the electromagnetic and
entropic terms as one global nonlinear coupled action, nor does action
stationarity alone prove Cauchy well-posedness.

## Corrected status table

| Question | Current classification | Evidence and boundary |
| --- | --- | --- |
| Is `ElectroGravitationalFieldEquation` supplied directly? | **directly proved: no in the strongest constructors** | Variational constructors derive the structure from stationarity. |
| Is the Einstein equation supplied directly? | **directly proved: no** | Metric stationarity yields the real Einstein equation with the Maxwell source. |
| Is the Maxwell stress tensor tied to `A`? | **directly proved: yes** | `maxwellStressEnergy` is constructed from `faraday k A`; gauge invariance is proved. |
| Is source-free Maxwell supplied directly? | **directly proved: no** | `electromagneticStationary_iff_sourceFree` derives it from arbitrary gauge variations. |
| Is homogeneous Maxwell proved? | **directly proved: yes** | `faraday_bianchi` supplies `d(dA)=0`. |
| Is the entropic split supplied directly? | **directly proved: no** | `bcjEntropicStationary_iff` derives `m_I c² = S₁ + S₂`. |
| Is there one underlying action functional? | **proved with explicit scope** | A coupled linearized action germ and a global nonlinear Einstein–Hilbert action exist. A single concrete global nonlinear Einstein–Maxwell–entropic action has not yet been instantiated as one derivative certificate. |
| Is its functional derivative formally calculated? | **directly proved with explicit scope** | Coupled-germ, nonlinear Maxwell bounded-field Fréchet, EM, Regge, determinant, inverse-metric, volume, Einstein–Hilbert, Palatini-curvature, GHY, and dominated global action-path derivatives are formalized. The Maxwell result is a genuine field-space derivative; the full Einstein–Maxwell–entropic manifold derivative remains uncomposed. |
| Is curvature constructed from the metric? | **directly proved chartwise and intrinsically represented globally** | The capstone uses the exact metric-built connection/Riemann/Ricci/scalar/Einstein chain; global scalar curvature is frame- and atlas-independent. |
| Is this a global curved-spacetime PDE? | **substantial global layers and a conditional maximal-development construction are proved; full coupled well-posedness is not closed end-to-end** | A global intrinsic Maxwell PDE and atlas independence are proved; causal solutions follow from explicit Cauchy/Green data; local nonlinear Einstein evolution follows from a supplied gauge-reduced vector field and constraint-propagation theorem. Arbitrary-carrier chain quotients now preserve the fixed Cauchy surface, Einstein equation, and causal-compact global hyperbolicity, and Zorn produces a maximal representative inside a small class closed under those quotients. Concrete local spacetime isometries, quotient Lorentzian atlas, and analytic Maxwell/Einstein data remain open. |
| Is full amplitude-level BCJ derived? | **proved for an explicit model realization** | Denominated Jacobi-compliant channels, gauge amplitudes, gravity amplitude, and gauge-product relation are proved; arbitrary Yang–Mills BCJ representations are not claimed. |
| Is the result kernel-audited? | **directly proved: yes** | Metric, action, Palatini, global-action, BCJ, and capstone witnesses are enrolled in `SpineAxiomAudit`. |

## Action and derivative closure

### Sector actions

The repository contains:

```lean
Electromagnetism.ElectromagneticPotential.lagrangian

Physlib.QuantumMechanics.ComplexAction.LeviCivita
  .ComplexReggeAction.complexReggeAction

Physlib.ClassicalMechanics.ActionPrinciple.EntropicAction.total

Physlib.QuantumMechanics.ComplexAction.Curvature
  .GlobalEinsteinHilbertAction.canonicalEinsteinHilbertAction
```

Electromagnetism has a `HasVarGradientAt` chain and a sourced distributional
Maxwell realization. Complex Regge gravity has an actual directional derivative
and a real/imaginary stationarity split. The global Einstein–Hilbert module
constructs the metric measure and integrates intrinsic scalar curvature on the
manifold.

### Coupled first variation and action certificate

```lean
CoupledElectrograviticVariation
coupledElectrograviticFirstVariation
coupledElectrograviticFirstVariationLinear
IsCoupledElectrograviticStationary
coupledElectrograviticStationary_iff
ElectrograviticActionDerivativeData
ElectrograviticActionDerivativeData.stationary_iff_coupled
```

The direct-sum stationarity theorem is an actual composition result. The action
certificate prevents an arbitrary action formula from entering the spine unless
a formal derivative theorem identifies its derivative with the coupled first
variation.

### Einstein–Hilbert, Palatini, and boundary variation

The repository formalizes:

```lean
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

The global action layer adds:

```lean
PseudoRiemannianMetric.lorentzianVolumeMeasure
canonicalEinsteinHilbertAction
canonicalFrameEinsteinHilbertAction_eq_intrinsic
globalAction_hasDerivAt_of_dominated
globalAction_hasDerivAt_zero_of_palatini_bulk_zero
canonicalEinsteinHilbertActionPath_hasDerivAt_of_dominated
canonicalEinsteinHilbertActionPath_stationary_of_palatini_zero
```

Thus the unresolved action boundary is no longer determinant calculus,
Maxwell coordinate-field Fréchet calculus, Palatini reduction, boundary
cancellation, or global gravitational integration. It is the final construction
of one concrete global nonlinear coupled Einstein–Maxwell–entropic action on a
common manifold field carrier, including the Einstein--Hilbert jet and boundary
Fréchet derivative, whose derivative instantiates
`ElectrograviticActionDerivativeData`.

## Metric and curvature closure

### Coordinate-chart capstone chain

```lean
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

### Intrinsic/global geometry

The pseudo-Riemannian geometry layer proves coordinate independence of the
Levi-Civita curvature action, frame Ricci contractions, raised Ricci action,
Bochner wave operator, and scalar trace. The global Einstein–Hilbert action then
integrates the intrinsic scalar against a canonical metric-built measure.

The metric-to-curvature row is therefore no longer pending. The remaining
question is evolution well-posedness, not construction or coordinate
independence of the geometric equation.

## Global curved-spacetime PDE inspection

A bare “No” is incorrect. The repository contains several distinct global PDE
layers.

### 1. Global intrinsic Maxwell equation — directly proved

The global manifold predicate is:

```lean
PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
```

with operator form:

```lean
PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOperator
PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq
```

It is imposed at every point of the manifold and is independent of the selected
Levi-Civita atlas representative:

```lean
intrinsicRicciCoupledMaxwellAt_atlas_iff
intrinsicRicciCoupledMaxwellOn_atlas_iff
localLeviCivitaAtlas_intrinsicMaxwellOn_iff
```

The frame equation is also related to a frame-free tensor equation and admits a
local-to-global theorem over an actual cover.

**Classification:** directly proved as a global geometric PDE identity.

### 2. Sourced distributional Maxwell — directly proved on its carrier

The electromagnetic Lagrangian has a genuine variational gradient and the
distributional module derives the sourced equation on every Schwartz test
function:

```lean
Electromagnetism.DistElectromagneticPotential
  .satisfiesDistributionalMaxwell_testFunction
```

**Classification:** directly proved on the distributional Minkowski carrier;
not yet the same theorem as the intrinsic curved-manifold Maxwell operator.

### 3. Global retarded and advanced Maxwell solutions — conditional on Cauchy data

The repository defines:

```lean
PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData
PseudoRiemannianMetric.IntrinsicMaxwellGreenData
```

From existence, causal-sector membership, and uniqueness fields,
`WellPosedIntrinsicMaxwellCauchyData` proves that retarded and advanced solution
selectors are linear and constructs `IntrinsicMaxwellGreenData`. The latter
proves that retarded and advanced fields solve the global intrinsic equation and
that the retarded solution is unique in its causal sector.

**Classification:** the solution consequences are directly proved, but the
well-posed Cauchy datum is explicit analytic input. No theorem found in this
inspection constructs it from global hyperbolicity, energy estimates, and a
specified Sobolev source/field pair.

### 4. Caticha/Klein–Gordon/Hadamard global causal carrier — conditional

`ContinuumCatichaKGData` accepts Klein–Gordon, retarded, and advanced operators
with right-inverse and intertwining proofs. It derives the causal propagator and
its homogeneous equation. The Caticha–Hadamard–global-Maxwell capstone proves
atlas-independent Maxwell microcausality on the shared causal carrier.

Its documentation correctly withholds Green-hyperbolicity, existence of the
Green operators, and spacelike-support properties when they are not supplied.

**Classification:** directly proved from explicit global Green/Hadamard data;
existence of that analytic data is not constructed by the capstone.

### 5. Nonlinear complex-Einstein Cauchy evolution — local generically, global in the Lipschitz ADM model

```lean
GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution
GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique
```

work on an arbitrary complete real Banach phase space, so the carrier may be a
continuum Sobolev space. Picard–Lindelöf yields a local trajectory for a `C¹`
gauge-reduced nonlinear vector field, and Lipschitz control yields uniqueness.
The full complex Einstein equation is preserved along the trajectory through the
explicit `fieldEquation_propagates` field.

`ADMConstraintPropagation` goes further on the completed continuum
metric--momentum--matter carrier.  It derives the trajectory-level subsidiary
system from the Fréchet derivative of the constraint map and pointwise
ADM/Bianchi tangency, constructs an additive all-time flow from global
Lipschitz control, proves invariance of the full weak constraint surface, and
establishes two-sided Grönwall stability and finite-time phase-norm bounds.

**Classification:** genuine evolution, uniqueness, constraint propagation,
and global continuation for the declared model, conditional on:

- construction of the gauge-reduced Einstein vector field;
- its global Lipschitz estimate;
- initial constraints;
- the pointwise Fréchet/Bianchi tangency identity for the weak constraint map.

The trajectory-level constraint law and its propagation are no longer supplied
premises.  What remains analytic input is the explicit nonlinear Einstein
vector field together with its global Lipschitz and pointwise tangency
certificates.

### 6. Global Einstein development — closed for the globally-Lipschitz ADM model

`ConcreteADMGFreeCauchyData.exists_global_constrained_evolution_with_no_finite_norm_blowup`
now constructs an all-real-time trajectory on the completed continuum
metric--momentum--matter phase carrier.  Along this trajectory:

- the complex Einstein equation holds;
- the weak Hamiltonian and all three momentum constraints propagate;
- every finite time slab has an explicit uniform phase-norm bound obtained
  from the genuine Grönwall estimate.

This is a global development and finite-time norm-control theorem for the
declared globally Lipschitz gauge-reduced ADM model.  It does not prove that
arbitrary geometric Einstein data generate such a globally Lipschitz vector
field, nor does its phase-norm estimate imply curvature-singularity avoidance
or geodesic completeness.  Separately,
`metricLeviCivita_coordinateGeodesicallyComplete` proves all-real-time
coordinate geodesics when the full Levi--Civita spray is globally Lipschitz on
a global chart.  That strong spray premise is not derived from bounded ADM
phase norm.

No theorem yet instantiates the following entire chain from concrete
geometric initial data:

```text
actual gauge-reduced Einstein–Maxwell–entropic PDE
  -> Sobolev estimates and local well-posedness
  -> Hamiltonian and momentum constraint propagation
  -> coherent fixed-Cauchy local isometries and continuation
  -> atlas-independent globally hyperbolic spacetime solution
```

The new ADM theorem supplies global-in-time existence and finite-slab
phase-norm control for its declared globally-Lipschitz model.
`DevelopmentDirectLimit` constructs the quotient of arbitrary chain carriers
using Mathlib's generic `DirectLimit` and proves that compact causal diamonds
survive. `WaldMaximalDevelopment.exists_maximal` uses that quotient to prove
maximal existence, conditional on coherent fixed-Cauchy extension maps and the
standard small-class closure convention. Its uniqueness theorem is
conditional on the joint-extension patch and on turning mutual extensions
into a fixed-Cauchy causal--Einstein equivalence.  The smooth
metric-preserving atlas instantiation, curvature singularity control, and
geodesic completeness without the global-Lipschitz-spray premise remain
unproved. The Regge initial-value module also records that open space requires
boundary conditions at spatial infinity.

### PDE closure matrix

| PDE layer | Status |
| --- | --- |
| Global Einstein–Hilbert action integral | **directly proved** |
| Atlas-independent intrinsic scalar and curvature contractions | **directly proved** |
| Global intrinsic curved Maxwell equation | **directly proved** |
| Sourced distributional Maxwell equation | **directly proved on a separate distributional carrier** |
| Retarded/advanced global Maxwell solutions | **proved conditional on well-posed Cauchy/Green data** |
| Atlas-independent Maxwell causal solution | **proved conditional on Green data** |
| Local nonlinear complex-Einstein trajectory | **proved conditional on a concrete gauge-reduced vector field and propagation data** |
| Local uniqueness | **proved conditional on Lipschitz control** |
| Concrete ADM constraint propagation for that trajectory | **proved on the completed continuum carrier from pointwise Fréchet/Bianchi tangency and ODE uniqueness** |
| Concrete construction of Maxwell Cauchy data from global hyperbolicity | **not closed end-to-end** |
| Maximal globally hyperbolic coupled development | **arbitrary-carrier gluing and Zorn existence proved conditionally; concrete Lorentzian/PDE instantiation remains open** |
| Global-in-time existence or singularity control | **global existence and finite-slab phase-norm control proved for the globally-Lipschitz ADM model; arbitrary-GR curvature/geodesic singularity control remains open** |

## BCJ amplitude closure

The repository separates scalar entropy splitting, damping factorization,
Bianchi/Jacobi analogies, and an explicit denominated amplitude realization.
The explicit model uses:

```lean
entropicJacobiBCJDuality
entropicJacobiBCJChannels
entropicJacobiBCJAmplitude_eq
entropicJacobiGaugeAmplitude_eq_sq
entropicJacobiDoubleCopy_sq_eq_gauge_product
ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude
```

This is a genuine model-level BCJ amplitude result. It is not a universal theorem
that arbitrary interacting Yang–Mills amplitudes admit such numerators.

## Current strongest defensible closure claim

> The repository provides a kernel-checked, metric-built,
> action-certified Einstein–Maxwell–entropic field-equation closure; an
> atlas-independent global Einstein–Hilbert action with dominated Palatini
> differentiation; a global intrinsic curved-Maxwell PDE with atlas-independent
> geometric and conditional causal-solution layers; and an all-real-time
> nonlinear complex-Einstein ADM evolution with constraint preservation,
> reversible flow, perturbation stability, and finite-slab norm control on its
> declared globally-Lipschitz continuum Banach phase model; and an explicit
> arbitrary-carrier chain quotient yielding conditional Wald maximal
> development existence.

It does **not yet** instantiate the maximal-development construction with a
concrete coupled Einstein--Maxwell--entropic PDE, smooth metric-preserving
fixed-Cauchy local isometries, and the quotient Lorentzian atlas.

## Remaining focused targets

The remaining integration work is now sharply localized:

1. construct `WellPosedIntrinsicMaxwellCauchyData` from explicit globally
   hyperbolic assumptions and analytic estimates;
2. construct the explicit nonlinear Einstein vector field on the existing
   metric/momentum/matter phase space and prove its global Lipschitz and
   pointwise Fréchet/Bianchi tangency certificates;
3. connect the global Einstein–Hilbert action and electromagnetic/entropic
   action sectors to one concrete global `ElectrograviticActionDerivativeData`;
4. derive coherent fixed-Cauchy spacetime local isometries from the concrete
   Einstein PDE uniqueness theorem, descend the smooth Lorentzian atlas and
   metric through `DevelopmentDirectLimit`, and discharge the small-class
   closure and joint-extension premises of `WaldMaximalDevelopment`.

## Read-only validation commands

```bash
lake build Physlib.Meta.EntropicDynamicsFullEinsteinSource
lake build Physlib.Meta.SpineAxiomAudit
lake build Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction

lake exe zil-scan \
  Physlib.Meta.EntropicDynamicsFullEinsteinSource \
  /tmp/entropic-dynamics-full-source.zilevents.json \
  --no-cache --force
```

No CI workflow is required for this documentation classification.
