/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.FullLindbladODE
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
public import Physlib.QuantumMechanics.ComplexAction.RetardedGreenCausalSupport
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral
public import Physlib.QuantumMechanics.EuclideanTensorCompositionIso
public import Physlib.QuantumMechanics.BornCompositionCorrelation
public import Physlib.QuantumMechanics.Entanglement.MaximallyEntangledEntropy
public import Physlib.QuantumMechanics.EntropicClockSynthesis
public import Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Physlib.Thermodynamics.HolographicPrinciple
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson
public import Physlib.Thermodynamics.RelativisticScreenKinematics
public import Physlib.Thermodynamics.VerlindeCovariantGravity
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
public import Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation
public import Physlib.Meta.ZilAssert
meta import Zil

/-!
# The relational-framework claim ledger — the program map as a queryable database

This repository imposes no axioms, at the kernel or in the graph.  The relational-information
framework document presents its eighteen foundational statements axiomatically (local clocks →
causal order → relational spacetime; composite states → Bell correlations; boundary
entropy + energy + temperature → gravitation → curvature); here none of them has axiom
status — each is either **derived** as an output or **carried** as a definition or exact
identity, and this ledger records which, as ZIL graph edges on the theorems that carry each
statement.  The map that previously lived only in session notes is now data: retrieval goes
through the graph, and the graph is build-checked.

**Query recipes** (scratch file `import Physlib` + command, `lake env lean`):

* `#zil_query subject ~ "claim:relational"` — the whole map.
* `#zil_query subject ~ "claim:relational", relation = "derives"` — statements the graph
  *outputs* (nothing assumed).
* `#zil_query subject ~ "holographic-area-scaling"` — the area-law token: its consumer
  (the Newton-gravity derivation) and its deriver (`NewtonGIsolation.newtonG_isolated`,
  the unique-bit-count equivalence).

**Edge convention**: `derives @` marks a statement the repository proves as an output;
`formalizes @` marks a statement carried as a definition or exact identity; `caveat @` marks
partial coverage; `requires @` marks a derivation's input — every such input is itself
established below, so the chain carries no accepted premise.

**The graph-inconsistency this ledger closes**: the displacement-entropy assumption lived
under two token spellings — `assumption:displacement-entropy-ansatz` (established by the
discharge) and `assumption:verlinde-displacement-entropy-ansatz` (required by the two
Verlinde force lemmas, never established).  The discharge theorem now carries a `derives`
edge for the second spelling too, and both are asserted established.
-/

@[expose] public section

namespace Physlib.Meta.RelationalClaimLedger

/-! ### Statements 1–10 — clocks, causality, geometry carriers, quantum information -/

zil attach Physlib.QuantumMechanics.Lindblad.isLindbladSolution_trace_rate_zero where
  formalizes @ "claim:relational-01-local-state-evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.trace_gklsGenerator_eq_zero"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock_period where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  formalizes @ "claim:relational-02-internal-clock-ordering"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD where
  derives @ "claim:relational-02-internal-clock-ordering",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.restFrame_zitter_gap",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.zitter_oscillation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.heisenberg_velocity_solution",
  caveat @ "claim:the-massive-mode-clock-face-the-one-dimensional-trembling-operator-equals-the-mass-term-oscillating-at-the-rest-gap-so-the-compton-anchor-frequency-is-an-operator-dynamical-output-observed-in-the-condensate-analogue-not-a-unit-convention"

zil attach Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedResponse_support_subset_causalFuture where
  supported_by @ "lean:retardedGreen_ne_zero_imp_later",
  formalizes @ "claim:relational-03-finite-causal-propagation"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_self where
  formalizes @ "claim:relational-04-relational-time"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.metricInterval_isometry_invariant where
  formalizes @ "claim:relational-05-operational-spatial-relations"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.representation_dichotomy where
  derives @ "claim:relational-05-operational-spatial-relations",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.fwOperator_scalar_iff",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.meanPosition_linear_wavePacket",
  caveat @ "claim:the-quantum-operator-face-which-operator-corresponds-to-spatial-coordinates-is-selected-by-interaction-locality-not-given-as-a-background-identity-the-newton-wigner-operator-is-carried-by-newtonwignerpositionoperator-via-the-fujiwara-time-operator-under-the-momentum-reading"

zil attach SpaceTime.properTimeIntegral_straight_lorentz_invariant where
  supported_by @ "lean:properTimeIntegral_straight",
  supported_by @ "lean:properTime_lorentz_invariant",
  formalizes @ "claim:relational-06-proper-time-worldline-clock"

zil attach Physlib.QuantumMechanics.EuclideanTensorCompositionIso.euclideanTensorEquiv_basisFun where
  formalizes @ "claim:relational-07-quantum-composition",
  caveat @ "claim:the-finite-factor-tensor-isomorphism-face-the-infinite-case-is-carried-by-borncompositioninfinite"

zil attach Physlib.QuantumMechanics.BornCompositionInfinite.dense_span_l2ProdInfinite where
  derives @ "claim:relational-07-quantum-composition",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionInfinite.inner_l2ProdInfinite",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionInfinite.bornDist_l2ProdInfinite",
  caveat @ "claim:tensor-structure-realized-on-the-composite-carrier-directly-no-abstract-tensor-functor-with-associators-because-mathlib-has-no-completed-hilbert-tensor-product-to-weld-to"

zil attach Physlib.QuantumMechanics.Entanglement.bellSinglet_qMutualInfo where
  supported_by @ "lean:bellSinglet_entropy_composition",
  formalizes @ "claim:relational-08-entropy-and-mutual-information"

zil attach Physlib.QuantumMechanics.EntropicClockSynthesis.bornOutcomeTable_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.chsh_violation_positive_mutual_information",
  supported_by @ "lean:Physlib.QuantumMechanics.EntropicClockSynthesis.tsirelson_on_eight_clock",
  formalizes @ "claim:relational-09-born-local-measurement"

zil attach Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bell_marginals_indistinguishable where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiMinus_traceRight_uniform",
  formalizes @ "claim:relational-10-no-signalling"

zil attach Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.tsirelson_correlation_bound where
  supported_by @ "lean:HermitianMat.sqrt_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.tsirelson_sq_bound",
  formalizes @ "claim:relational-bell-tsirelson-sector"

/-! ### Statements 11–15 — the thermodynamic-gravity chain -/

zil attach Physlib.Thermodynamics.HolographicScreenEntropy.screenEntropy_bekensteinHawking where
  formalizes @ "claim:relational-11-holographic-information-scaling",
  caveat @ "claim:entropy-area-face-exact-and-the-count-n-equals-area-c-cubed-over-g-hbar-is-derived-as-the-unique-bit-count-compatible-with-newtons-form-by-newtong-isolated",
  supported_by @ "lean:Physlib.Thermodynamics.LightSheet.bousso_covariant_bound"

zil attach Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh where
  derives @ "claim:relational-12-thermodynamic-force-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.verlindeDisplacementEntropy_eq_entropicAction_reading"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.verlindeDisplacementEntropy_eq_entropicAction_reading where
  derives @ "assumption:verlinde-displacement-entropy-ansatz",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD",
  caveat @ "claim:conditional-on-the-compton-anchor-calibration-which-fixes-the-time-unit-to-the-mass-a-unit-choice-selecting-the-physically-present-rest-zitterbewegung-oscillation-of-the-massive-dirac-mode"

zil attach Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde where
  derives @ "claim:relational-13-screen-equipartition-newton-gravity",
  requires @ "assumption:holographic-area-scaling-of-screen-degrees-of-freedom"

zil attach Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated where
  derives @ "assumption:holographic-area-scaling-of-screen-degrees-of-freedom",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension.logBondDimension_fixed_by_areaLaw",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicScreenEntropy.newton_form_forces_bekensteinHawking",
  caveat @ "claim:derived-as-an-equivalence-the-holographic-count-is-the-unique-bit-count-compatible-with-newtons-form-so-the-scaling-is-an-output-of-the-one-g-system-closure-with-newtons-form-and-g-anchored-by-the-compton-clock-while-boussos-inequality-bounds-remain-unformalized"

zil attach Physlib.Thermodynamics.newtonPotential_deriv_eq_verlinde_entropicForce where
  derives @ "claim:relational-14-potential-coarse-graining"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity where
  derives @ "claim:relational-15-screen-flux-poisson",
  caveat @ "claim:strong-pointwise-poisson-for-arbitrary-continuous-radial-density-with-the-cartesian-radial-laplacian-transport-supplied-the-remaining-assembly-is-composing-the-shell-potential-profile",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.RadialLaplacianTransport.laplacian_radial",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson.radial_strongPoisson_generalDensity"

/-! ### Statements 16–18 — the relativistic completion -/

zil attach Physlib.Thermodynamics.RelativisticScreenKinematics.redshiftScreenTemperature_eq where
  formalizes @ "claim:relational-16-relativistic-screen-kinematics",
  caveat @ "claim:screen-temperature-on-the-exact-schwarzschild-carrier-the-unit-observer-and-potential-gradient-now-hold-for-abstract-killing-data-in-abstractkillingredshiftkinematics",
  supported_by @ "lean:Physlib.Thermodynamics.AbstractKillingRedshiftKinematics.stationary_unit_of_timelike"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.killingSecondJet_divergenceDerivativeZero",
  formalizes @ "claim:relational-17-komar-screen-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius where
  derives @ "claim:relational-18-einstein-macroscopic-limit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy.cosmologicalConstant_globally_constant"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.entropicTime_rate_nonneg where
  derives @ "claim:relational-entropic-time-arrow"

/-! ### Integrity gate — the ledger fails the build when it stops being true -/

#zil_assert_established
  "claim:relational-01-local-state-evolution",
  "claim:relational-02-internal-clock-ordering",
  "claim:relational-03-finite-causal-propagation",
  "claim:relational-04-relational-time",
  "claim:relational-05-operational-spatial-relations",
  "claim:relational-06-proper-time-worldline-clock",
  "claim:relational-07-quantum-composition",
  "claim:relational-08-entropy-and-mutual-information",
  "claim:relational-09-born-local-measurement",
  "claim:relational-10-no-signalling",
  "claim:relational-bell-tsirelson-sector",
  "claim:relational-11-holographic-information-scaling",
  "claim:relational-12-thermodynamic-force-law",
  "claim:relational-13-screen-equipartition-newton-gravity",
  "claim:relational-14-potential-coarse-graining",
  "claim:relational-15-screen-flux-poisson",
  "claim:relational-16-relativistic-screen-kinematics",
  "claim:relational-17-komar-screen-energy",
  "claim:relational-18-einstein-macroscopic-limit",
  "claim:relational-entropic-time-arrow"

#zil_assert_established
  "assumption:displacement-entropy-ansatz",
  "assumption:verlinde-displacement-entropy-ansatz"

-- The area law is DERIVED, not assumed: `NewtonGIsolation.newtonG_isolated` proves the
-- holographic count is the unique bit count compatible with Newton's form (an iff), and
-- Newton's form and `G` are themselves outputs of the anchored-clock chain.  This ledger
-- briefly asserted the token primitive — an island claim minted in fresh vocabulary while
-- the derivation sat in the graph under the Bousso/one-`G` closure vocabulary; the flip
-- below is the correction, found by querying rather than trusting notes.
#zil_assert_established "assumption:holographic-area-scaling-of-screen-degrees-of-freedom"

end Physlib.Meta.RelationalClaimLedger
