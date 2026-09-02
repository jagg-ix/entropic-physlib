/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.EntropicSpine.Core
public import Physlib.QuantumMechanics.KoopmanQuantization
public import Physlib.QuantumMechanics.CyclicAutomatonSpectrum
public import Physlib.QuantumMechanics.UnitaryConjugacy
public import Physlib.QuantumMechanics.CyclicVectorRigidity
public import Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysicalData
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysicalDataDirac
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction
public import Physlib.QuantumMechanics.BornCompositionCorrelation
public import Physlib.QuantumMechanics.L2KetAdapter
public import Physlib.QuantumMechanics.L2StatePresentation
public import Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction
public import Physlib.Mathematics.LovelockRund
public import Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow
public import Physlib.Mathematics.DynamicalSystems.DerivativeCocycleHyperbolicity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticOrbitalStability
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticMildFlow
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.OVVEntropicClockBridge
public import Physlib.QuantumMechanics.ComplexAction.DiracCartan2ISecondQuantizedQCD
public import Physlib.QuantumMechanics.RelationalTime.ThreeClockClosure
public import Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics
public import Physlib.QuantumMechanics.RelationalTime.ThreeClockFunctoriality
public import Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumWeakCouplingReduction
public import Physlib.Meta.LindbladOneLevelOhmicMicroscopicRateAudit
public import Physlib.Meta.LindbladOneLevelSpectralGoldenRuleAudit
public import Physlib.Meta.LindbladOneLevelContinuumWeakCouplingAudit
public import Physlib.QuantumMechanics.PeriodicSchrodinger
public import Physlib.QuantumMechanics.RelationalTime.CausalEventHistory
public import Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier
public import Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach
public import Physlib.QuantumMechanics.RelationalTime.RadarLightConeEquivalencePrinciple
public import Physlib.QuantumMechanics.RelationalTime.PageWoottersMultitimeCorrelator
public import Physlib.QuantumMechanics.ComplexAction.RetardedGreenCausalSupport
public import Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLorentzReconstruction
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeAlexandrovZeeman
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalPreorder
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLightRayPreservation
public import Physlib.QuantumMechanics.Entanglement.MaximallyEntangledEntropy
public import Physlib.Thermodynamics.FiniteMarkovEntropyProductionStrict
public import Physlib.Meta.FiniteCausalPropagationAudit
public import Physlib.Meta.RadarDistanceOperationalAudit
public import Physlib.Meta.RadarLightConeEquivalencePrincipleAudit
public import Physlib.Meta.SpacelikeBoostNoSignalingAudit
public import Physlib.Meta.CausalConeLorentzReconstructionAudit
public import Physlib.Meta.CausalConeAlexandrovZeemanAudit
public import Physlib.Meta.CausalPreorderAudit
public import Physlib.Meta.CausalConeLightRayPreservationAudit
public import Physlib.Meta.ComptonClockMalamentProperTimeLinksAudit
public import Physlib.Meta.ComptonClockEntropicArrowAudit
public import Physlib.Meta.MetricIntervalIsometryInvarianceAudit
public import Physlib.Meta.MetricDilationGravityFormulationsAudit
public import Physlib.Meta.SecondBianchiDilationCartanQCDTQFTAudit
public import Physlib.Meta.MayrStiebergerDilatonTensorAudit
public import Physlib.Meta.EntanglementBraneModularTQFTAudit
public import Physlib.Meta.EinsteinEntanglementDynamicsAudit
public import Physlib.Meta.TimelikeEntanglementEntropyAudit
public import Physlib.Meta.VarlamovCliffordLorentzAudit
public import Physlib.Meta.CliffordFiberChristoffelContractionAudit
public import Physlib.Meta.PageWoottersMultitimeCorrelatorAudit
public import Physlib.Meta.FiniteMarkovEntropyProductionStrictAudit
public import Physlib.QFT.ScalarGreenFunctions
public import Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange
public import Physlib.Electromagnetism.Vacuum.HarmonicWaveCertificate
public import Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum
public import Physlib.Meta.M9CriterionReductionAudit
public import Physlib.Meta.CubicQuinticConstructedCertificatesAudit
public import Physlib.Meta.M9ChargeKleinOrbitalCriteriaAudit
public import Physlib.Meta.ZilEvidenceClosureRegistryAudit

/-!
# Entropic spine and executable-criterion theorem surfaces

The spine exports the entropic program's concrete carriers directly, on the
arbitrary-index Hilbert sum `lp (fun _ : Index => ℂ) 2`, with no universal model
structure.  The reversible deterministic dynamics is the Koopman quantization
`KoopmanQuantization.koopmanStateStep`; the finite cyclic clock is the automaton
spectrum of `CyclicAutomatonSpectrum.cyclicStateStep`, whose cyclic-vector
rigidity (`CyclicVectorRigidity`) makes any finite unitary with an orthonormal
cyclic orbit basis unitarily conjugate to the standard shift, and whose distinct
generator presentations are conjugate through `shiftStateStep_conjugate_cyclicStateStep`.
The cyclic age is `ZMod N`-valued and is not promoted to monotone real or proper
time; the norm-squared response is structural rather than gravitational.

Aggregate import preserving the existing entropic-spine implementation,
Lovelock--Rund continuum variational geometry, and the periodic Schrödinger
perturbation formalization with its complex-action spectral-selection bridge.
It also exports the continuum scalar Green-function hierarchy, the exact
Coulomb-gauge projector/propagator/Dyson algebra used by the gauge-field layer,
and the total-correlation entropic clock with its complex-action damping bridge.
Its relational-time surface now also exports deterministic causal-event
execution, invariance under explicitly certified independent swaps, and the
minimal/unique natural-valued clock fixed by causal predecessor depth.  This
discrete result does not identify causal depth with Lorentzian proper time or
derive continuum dynamics.
The aggregate also exports the maximally dissipative CAT/EPT damping semigroup,
the continuum kinetic Kolmogorov certificate, the unique gauge-covariant cubic
backreaction law, and its locally well-posed nonlinear continuum evolution. It
also exports the concrete positive-imaginary-energy complex-Einstein clock whose
derived action-rate calibration proves that its entropic reading equals physical
proper time. The Dirac--Cartan--binary-icosahedral bridge additionally exports
the concrete `2I` spinor action, algebraic axial-torsion elimination, the
Compton--Yukawa complex-mass assembly, and its exterior-algebra fermionic Fock
lift, where fixed occupation multiplies the Compton energy and QCD theta,
confinement, and Yukawa entropy feed one history amplitude and decoherence
functional.

The Wheeler–DeWitt/complex-Einstein surface additionally exports the finite
Ooguri–Vafa–Verlinde flux carrier. It proves additive flux-superpotential and
multiplicative wavefunction composition, the full semiclassical Eq. (3.8)
norm-square identity, the unique radial saddle `R = M/2` and entropy exponential
of Eq. (3.9), holomorphic/real-polarization probability agreement, and the
pointwise/integrated OSV norm-square identities on both the scalar and arbitrary
finite multi-flux carriers. It also packages the exact supersymmetric implication
`Q² = H` and `Qψ = 0` imply `Hψ = 0`. Its ZIL contract keeps the Calabi–Yau
periods, physical supercharge, and topological-string wavefunction explicit inputs
and does not promote those identities to an all-genus OSV/microscopic-index
theorem.

The OVV carrier is now connected to the IKKT/IIB matrix action and the
Compton--Zitterbewegung entropic clock through one typed bridge.  The exact
content is: the OVV insertion has a specified imaginary action in the common
`lorentzianKernel`; the proved IKKT coupling rescaling removes a positive
matrix coupling; and, under a visible normalized-action match, their weights
coincide.  IKKT central translations preserve this path weight, the match
specializes to the actual finite electric/magnetic OVV superpotential, and the
matched matrix weight has the same norm square as the holomorphic
topological-string wave.  A separate visible rest-energy calibration then
identifies that dimensionless entropic phase with `omega_C * tau`, equivalently
one half of the rest-frame Zitterbewegung phase.  For nonnegative proper time it
also selects `Im W <= 0` and hence a nonexpansive weight.  The bridge now replaces
the abstract clock argument by the Lorentzian inertial-worldline proper-time
integral, identifies the phase with the existing scalar entropic-proper-time and
Clausius readings, and composes the recent all-null-direction Jacobson theorem to
the Einstein equation.  The cosmological equation then embeds exactly into the
equilibrium complex-Einstein presentation by moving the cosmological term to the
effective real stress.  The Jacobson layer also now composes its pre-existing
contracted-Bianchi lemma, proving that the resulting cosmological scalar has
vanishing gradient under explicit conservation and metric-compatibility inputs.
Its matrix/flux, rest-energy, heat, and horizon-Clausius calibrations remain
explicit: it deliberately does not claim that IKKT derives the OVV
compactification, a nonzero imaginary Einstein source, or Einstein gravity, or
that flux data predicts a particle mass.  A further finite-rapidity continuation
uses the existing Schmidt carrier rather than inventing a new dissipation law:
under the visible calibration `S_I = hbar log K`, the OVV phase is `log K` and
its modulus is exactly `tanh eta = 1/K`.  Matching the Jacobson coupling to the
G-free inference coupling then lets the derived real equation seed the existing
`log K` complex-Einstein family, with imaginary curvature converging to zero.
The same action and phase identities now hold pointwise along matched IKKT/OVV
rapidity trajectories, and the OVV phase inherits the explicit
`4 exp(-2 eta)` reversible-limit bound.  With contracted real Bianchi and a
divergence-free reference entropic stress, every member of the resulting family
also satisfies complex Bianchi and conservation of both sources.  The reference
entropic stress tensor remains an explicit model input, so this does not claim a
unique irreversible law follows from equilibrium Clausius data.

The Clifford--Lorentz surface now uses the actual bundled
`SL(2,ℂ) → SO⁺(1,3)` homomorphism: the Pin sandwich is the geometric
Minkowski reflection, the kernel is exactly `{1,-1}`, and equal Lorentz images
are exactly the two central-sign-related spinors. This proves the two-sheet
fibers over the image; it does not promote that result to an unproved
surjectivity theorem for the entire restricted Lorentz group.

The public surface also exports the ZIL evidence-closure audit. That registry
separates named implementations from kernel verification, records rejected
omissions through structured counterexample edges, and keeps the genuinely
remaining analytic obligations queryable rather than buried in prose caveats.

The one-level LDDL bridge additionally exports the finite Caldeira--Leggett
Ohmic coupling inversion: the coupling law inverts exactly to select the
effective `γ`, the relaxation coefficient, the Lorentzian width, and the
coefficient entering decoherence, conditional on the stated
weak-coupling/Born--Markov/secular model identification. The same rate has an
exact on-shell spectral representation `γ = 2π g² J`, with fermionic thermal
detailed balance and exact agreement with `J_eff = shapeSum/(8 cutoff³)` for
the finite-Ohmic parameterization. A typed continuum reduction layer records
the one-sided bath-correlation transform, the additive Volterra-to-Markov
error, the exact resonant secular projection, and the composed error against
the LDDL vector field.

The public relational-time surface now additionally exports:

* exact finite Page--Wootters conditioning certificates over physical history states;
* transport of a direct one-step evolution law to conditioned system states;
* exact observable and predicate transport through conditioning;
* deterministic post-processing closure for conditioned/direct state pairs;
* the dynamical non-coincidence theorem separating entropy-preserving modular
  flow from strict entropy-producing flow;
* composable invertible Page--Wootters/modular/entropic calibration maps;
* conjugation of Page--Wootters endomorphisms through the entropic-clock
  calibration, preserving identity and composition; and
* complete Page--Wootters-to-proper-time calibration composition with strict
  temporal-order preservation when the pairwise maps are strictly monotone; and
* the unified constrained system--clock--bath carrier
  (`UnifiedRelationalDissipativeCarrier`) that bundles the Page--Wootters
  constraint, the conditional GKSL generator, and a faithful Gibbs equilibrium,
  and reduces from a single structure to both experimentally anchored limits:
  the reversible Page--Wootters conditional evolution at zero dissipation, and a
  unique Gibbs thermal steady state under strict relative-entropy contraction —
  now inhabited by a nonzero correlated history satisfying a nonzero
  clock--system constraint.  The Gaussian continuum collision bath selects its
  rate and closes the concrete unitary Davies-scale / `C₀` GKSL / linewidth /
  relaxation / exact-KL-derivative chain;
* finite causal propagation in support-over-sources form
  (`retardedIntegralResponse_support_subset_causalFuture`): both the finite
  causal-set sum and the Bochner integral over an arbitrary measure space are
  supported in the causal future of the source's support,
  `supp(G⁺f) ⊆ J⁺(supp f)`, upgrading the pointwise future-cone membership; and
* the operational signal-delay law `Δt = d/c + Δt_int`
  (`SignalDelayCausalReach`): its light-cone lower bound `d/c ≤ Δt`, additive
  relay composition, and the spacelike-no-signal consequence
  (`not_canSignalReach_of_spacelike`) — no synchronization without causal
  communication, grounding why distant simultaneity is convention-dependent;
* the operational reconstruction of spatial distance from round-trip signal time
  (`radarDistance_roundTripTime`): `d = c·T/2` recovers the true separation,
  strictly monotone in the clock reading and consistent with the flat null-leg
  interval `−c²(d/c)² + d² = 0` — spatial separation emerging from causal data;
* the link of that operational distance to the Einstein Equivalence Principle
  (`radarLightLeg_massless_boost_invariant`): the radar light leg is a massless
  mass-shell vector whose null character is boost-invariant — Local Lorentz
  Invariance, `boost = inertial gauge` — placing it on the Nagao–Nielsen
  convergence-cone boundary and grounding the frame-covariance of the
  reconstructed distance in the same Lorentz-invariant light cone the EEP asserts;
* the wiring of that boost-invariant light cone into the causal and Bell layers
  (`spacelike_chsh_noSignaling_frame_covariant`): the full CHSH/no-signaling
  contract holds at every boosted image of a spacelike point — Bell no-signaling is
  Lorentz-frame-covariant, *derived* from boost-invariance of the spacelike
  character, not merely conjoined with it; with the spacelike separation
  simultaneous in some frame (`spacelike_exists_simultaneity_frame`, why
  no-signaling is mandatory) and the timelike causal order frame-invariant
  (`boostBy_preserves_timelikeFuture`);
* the dimension-independent metric interval API (`metricInterval_isometry_invariant`): every
  matrix isometry `LᵀgL=g` preserves `v·gv`, while a constant Weyl rescaling scales the
  interval and leaves the metric-built Levi–Civita connection unchanged
  (`weylRescale_connection_invariant_interval_scales`);
* the flat Nagao–Nielsen complex-action specialization
  (`nnComplexAction_interval_flatLeviCivita`):
  `nnLorentzForm q = q.re² − q.im² = Re(q²)` is the `(1,1)` Minkowski interval on
  the real/imaginary-action plane (`nnLorentzForm_eq_metricInterval`); its boost matrix obeys
  `LᵀgL=g` (`nnActionBoostMatrix_isometry`), so the general theorem proves preservation of this interval,
  its convergence cone, and both descriptions of the invariant
  (`nnActionBoost_preserves_interval`, `nnActionBoost_preserves_real_square`,
  `nnActionBoost_converges_iff`).  Conversely, full boost invariance forces every real
  symmetric quadratic form on the action plane to be a scalar multiple of `nnLorentzForm`
  (`nnSymmetricForm_invariant_iff`), and unit timelike normalization removes that last scale
  (`nnLorentzForm_unique_normalized`).  Its constant metric derivative has exactly one
  torsion-free compatible connection, the flat zero Levi–Civita connection
  (`nnFlatLeviCivita_existsUnique`); `nnInvariantGeometry_unique` packages metric and
  connection uniqueness using the previously proved Koszul theorem rather than a new
  connection assumption.  This is the flat action plane, not a replacement for the
  repository's curved-spacetime connection;
* the electromagnetic/gravity realization of that action geometry: the real
  Einstein–Maxwell residual built from the gauge-invariant Faraday stress tensor and the
  imaginary entropic-Einstein residual form one complex coordinate
  (`electrograviticResidualCoordinate`).  Metric stationarity is exactly its componentwise
  vanishing (`metricStationary_iff_residualCoordinate_zero`); every internal action boost
  preserves its interval and its zero set (`electrograviticResidual_interval_invariant`,
  `metricStationary_iff_boostedResidual_zero`).  The same statement holds after the metric
  itself builds Levi–Civita, Riemann, Ricci, scalar curvature and Einstein tensors
  (`metricBuiltStationary_iff_boostedResidual_zero`).  This boost acts on the residual's
  real/imaginary action components; it is neither a spacetime coordinate boost nor electric–magnetic
  duality;
* the full orthochronous boost-invariance of the interior future light cone
  (`interiorFutureLightCone_smul_iff_of_orthochronous`), resting on the reverse
  Cauchy–Schwarz inequality `0 < ⟪u,v⟫ₘ` for future-timelike vectors
  (`minkowskiProduct_pos_of_futureTimelike`), with spacelike separation invariant
  under the full Lorentz group — and the Malament reconstruction up to a conformal
  factor (`conformalFactor_causalCharacter_invariant`): rescaling the metric by any
  positive `Ω²` leaves the causal order unchanged, so causal data fixes the metric
  only up to a conformal factor;
* the 3+1-dimensional Alexandrov–Zeeman affine reduction: the null cone determines any
  symmetric continuous bilinear form up to scale (`same_null_cone_proportional`), the
  open future timelike cone is the topological interior of the closed causal cone
  (`interior_futureCausalCone3_eq_futureTimelikeCone3`), and therefore an affine causal
  automorphism preserves null vectors without a separate premise and is exactly a
  translation followed by a positive dilation and Lorentz transformation
  (`affine_causalAutomorphism_eq_translation_dilation_lorentz`); an arbitrary nonlinear
  causal automorphism still requires the fundamental affine-geometry collineation step
  to produce the affine equivalence consumed by this theorem;
* the companion algebraic Alexandrov–Zeeman conclusion
  (`conformalLorentz_eq_smul_lorentz`): a conformal-linear map with positive factor `c`
  is exactly `√c` times a Lorentz transformation
  (`conformalLorentz_toMatrix_mem_lorentzGroup`), while a causal automorphism preserves
  Alexandrov intervals (`causalDiamond_image_of_isCausalAutomorphism`);
* the causal-order foundation the Alexandrov intervals rest on
  (`causallyFollows_trans`, `causalPreorder`): the Minkowski causal relation is a
  genuine preorder — reflexive, and transitive because the future causal cone is
  closed under addition (the closed-cone reverse Cauchy–Schwarz
  `minkowskiProduct_nonneg_of_futureCausal`) — with the causal diamond identified as
  the order interval `Set.Icc` (`causalDiamond_eq_Icc`);
* Zeeman light-ray preservation from causal order alone
  (`futureLightConeBoundary_image_of_causalAutomorphism`): in 3+1 dimensions a
  future-null Alexandrov interval is exactly a causally reachable interval that is a
  chain (`futureLightConeBoundary_iff_causalDiamond_isChain`); null intervals are chains
  and timelike intervals contain a spacelike-incomparable pair, so every bare causal
  automorphism maps complete future light cones to complete future light cones and maps
  chronological timelike reachability as well
  (`interiorFutureLightCone_mem_iff_of_causalAutomorphism`); the corresponding open
  chronological diamonds are Euclidean-open and mapped exactly to image diamonds
  (`isOpen_chronologicalDiamond3`, `chronologicalDiamond3_image_of_causalAutomorphism`).
  It also maps
  every individual nondegenerate future null affine ray exactly onto its corresponding
  image ray (`futureNullRay_image_of_causalAutomorphism`), with the two oriented halves
  assembled into exact preservation of the complete null affine line
  (`nullAffineLine_image_of_causalAutomorphism`).  The
  remaining nonlinear Alexandrov–Zeeman obligation is the standalone affine-geometry
  theorem promoting the resulting light-ray collineation to an affine equivalence;
* the operational Malament–Compton calibration closure: with nonzero physical clock
  parameters, accumulated Compton phase is injective in proper time
  (`comptonPhase_injective`); preserving one nonzero timelike clock reading removes the
  remaining affine causal dilation, fixes its positive conformal factor uniquely to one,
  and preserves every proper-time interval
  (`comptonCalibration_fixes_malamentScale`).  At fixed kinematic boost and nonzero clock
  interval, the nonnegative Schmidt rapidity is also uniquely identifiable from the
  entanglement-reparametrized phase (`entanglementRapidity_unique_of_phase`) and explicitly
  reconstructed by `arcosh` (`entanglementRapidity_eq_arcosh_phaseRatio`).  The calibrated
  affine causal map is therefore a Lorentz transformation followed by translation
  (`comptonCalibration_is_poincare`), and one nonzero calibrated interval determines the
  Compton mass parameter uniquely (`comptonMass_unique_of_phase`).  Proper time also has an
  explicit inverse reconstruction from its phase (`properTime_reconstruct_from_comptonPhase`),
  and global phase preservation is equivalent to global proper-time preservation
  (`globalComptonCalibration_iff_properTimeInvariant`).  These global calibrations contain
  identity and are closed under composition and inverse
  (`isGloballyComptonCalibrated_refl`, `IsGloballyComptonCalibrated.trans`,
  `IsGloballyComptonCalibrated.symm`); among affine causal automorphisms they are precisely
  the Poincaré transformations (`isGloballyComptonCalibrated_iff_poincare`).  The conditional
  holographic coupling `ħc/m²` is then reconstructed directly from a nonzero clock phase
  (`derivedNewtonG_eq_from_comptonPhase`), while calibration transports the Compton
  Sorkin–Johnston kernel across one or two independently selected intervals
  (`comptonClockKernel_invariant_of_calibration`,
  `comptonClockKernel_pair_invariant_of_calibration`) and preserves its Hadamard and
  Pauli–Jordan parts (`comptonClockSJ_parts_invariant_of_calibration`).  The capstone
  `calibratedComptonClock_poincare_sj_unitary_holographic` packages the Poincaré reduction,
  clock-frequency coupling, causal state, and reversible unitary flow.  This uses the proved
  affine causal classification and does not claim the separate nonlinear
  light-ray-collineation-to-affine step, an independently predicted numerical mass or
  coupling, or a new full distributional Hadamard wavefront-set theorem;
* the Compton-anchored entropic-time arrow (`comptonPhase_monotone` and
  `comptonPhase_strictMono`): `τ_ent = S_I/ħ = ω_C τ` is monotone in proper time and
  strictly increasing for positive mass.  This is the reversible constant-rate clock limit,
  not entropy production and not an identification of time with entropy;
* the strict entropy-production arrow for a general finite Markov chain
  (`markovEntropyProduction_pos_of_not_detailedBalance`): the Schnakenberg
  symmetrization gives `σ ≥ 0`, strict `σ > 0` unless detailed balance — the
  entropic arrow beyond the two-state binary carrier; and
* Page–Wootters two-time correlations (`twoTimeCorrelator_eq_phase_diff`):
  `C(τ₁,τ₂) = e^{iE_sys(τ₁−τ₂)/ℏ}·q` depends only on the clock-time difference,
  is time-translation invariant with stationary magnitude, and reduces to the
  one-time expectation at coincidence — the relational carrier extended from
  state trajectories to multitime observables.

The M9 criterion bridge surface additionally exposes:

* fermion exchange phase, two-state antisymmetry, and identical-state exclusion;
* a smooth source-free harmonic potential that is both a Maxwell solution and a
  plane wave;
* the exact finite spectral heat semigroup with zero-mode conservation and the
  zero-diffusivity limit;
* additive winding charge quantized in thirds, with conjugation, integer-sector
  divisibility, and Fock-space charge grading;
* finite spectral Klein--Gordon modes with exact massive dispersion and conserved
  quadratic mode energy; and
* the unscreened Coulomb/O(4) Gegenbauer harmonic sector with negative
  integer-labelled hydrogenic energy levels.

The constructed-certificate surface additionally exports the complete H1
carrier, the genuine free Schrödinger group, the cubic--quintic weak/mild
interfaces, the conservative minimizing-orbit stability theorem, and named
identified-branch constructors.

## Audit boundary

The public spine therefore already contains:

* the arbitrary-index `ℓ²` Koopman quantization and the exact finite cyclic
  automaton spectrum with a unitary coordinate shift, cyclic age covariance,
  reversible KL preservation, and cyclic-vector rigidity;
* uniqueness of the irreversible Born-density cubic backreaction inside the
  declared local gauge-covariant cubic class;
* a concrete complex-Einstein model deriving its action-rate calibration and
  identifying the resulting entropic clock with physical proper time;
* local Banach well-posedness of the full polynomial continuum generator and an
  exact global nonlinear semiflow for fixed continuous multiplication energy;
* maximal dissipativity and `C₀` semigroup generation for the homogeneous
  continuum CAT/EPT sector;
* an explicit free continuum kinetic Kolmogorov kernel with bracket generation,
  smooth positivity, and its kinetic PDE;
* exact finite conditioning, conditioned-dynamics transport, observable
  transport, calibrated-dynamics conjugation, and four-clock calibration
  interfaces;
* criterion-scoped algebraic/free-field/spectral certificates for fermionic
  exchange, Maxwell plane waves, and periodic heat flow;
* Lean-backed ZIL lifecycle invariants for the Hartree-continuity, no-loss,
  Born-normalization, minimizer, compact-orbit, and orbital-stability chain;
* a concrete norm-preserving binary-icosahedral spinor action with central-sign
  descent for bilinear observables, algebraic spin-sourced Cartan torsion
  elimination into an axial contact density, and a checked Dirac mass-shell and
  complex-energy assembly for a Compton-anchored Yukawa mass;
* the fermionic Fock lift of that `2I` action with creation intertwining and
  Pauli/CAR, and a second-quantized QCD history weight whose Born diagonal is
  fixed by confinement plus occupation-dependent Yukawa entropy action;
* an exact finite-Ohmic coupling-to-rate inversion selecting the effective rate
  and Lorentzian width inside the stated bath model;
* an on-shell spectral golden-rule/detailed-balance representation of the same
  rate;
* a typed continuum weak-coupling reduction layer composing the bath-correlation
  transform, the additive Volterra-to-Markov error, and the exact resonant
  secular projection against the LDDL vector field; and
* a concrete Gaussian continuum spectral bath whose norm-preserving unitary
  phase group produces the evaluated correlation transform, together with a
  Stinespring unitary collision-reservoir realization whose Davies-rescaled
  reduction converges to the bundled one-level CPTP `C₀` semigroup with the
  explicit loss/gain GKSL right generator.
* intrinsic manifold derivative cocycles for both one diffeomorphism and genuine
  smooth additive (`ℤ^d`-capable) diffeomorphism actions, with continuous
  hyperbolic tangent splittings, plus the finite Brown entropy--Lyapunov layer: coarse exponent
  classes have representative-independent hyperplanes, signs, and regular
  directions; weighted exponent entropy is bounded by Margulis--Ruelle capacity,
  globally subadditive and linear inside a common closed Weyl cone; zero signed
  growth balances stable/unstable capacities; saturation is componentwise rigid;
  and pairwise distinct root classes obey the fiber-resonance cardinal bound.
  This exports the
  algebraic consequence of supplied Lyapunov data, not Oseledets/SRB existence
  or full measure rigidity.

The concrete faces are the periodic reciprocal-mode Bloch phase evolution
(`BlochPhaseEvolution`, with the mode-wise Schrödinger generator law
`i ∂ₜ ψ_γ = E_γ ψ_γ`) and the Compton-anchored physical data
(`ComptonPhysicalData`, carrying the holographic area-per-bit Newton constant,
Newton's second law at the screen, and the four-spinor Yukawa Dirac mass shell).
Rigidity is the concrete unitary conjugacy of the finite cyclic family
(`shiftStateStep_conjugate_cyclicStateStep` and the cyclic-vector
`toStandardConjugacy`), not a stored certificate, and a composite face generates
subsystem correlation from a coupling permutation. The finite cyclic clock still
supplies no monotone real clock, proper-time calibration, Newtonian force, or
irreversible entropy production, and no equivalence between the cyclic, periodic,
and Compton faces is claimed.

The spine also exports the completed representation stack: the Born boundary of a
normalized state as an actual probability distribution, the proved equivalence of
the finite `ℓ²` carrier with the QuantumInfo `Ket` and density-operator carriers
(agreeing Born distributions, a natural bridge intertwining the dynamics), the
abstract `StatePresentation`/`StatePresentationBridge` layer with its proved
`ℓ²`–`Ket` natural bridge. A carrier is admitted through a proved bridge, not an
analogy. The semantic boundary is kept explicit: the
diagonal-measurement total correlation is classical correlation extracted from a
quantum state; it does not by itself prove quantum entanglement, which is
established separately and only for pure states.

Reversible and irreversible dynamics are one bundled `CPTPMap` layer on density
operators: a genuinely reversible (`CPTPMap.IsUnitary`) channel is
entropy-preserving — the necessary direction, not a characterization — the
replacement-to-maximally-mixed channel is not, and relative entropy contracts
under every channel by data processing, the shared irreversibility law with the
unitary channels the equality case and the Lindblad `oneLevelChannel` and Spohn
free-energy H-theorem the concrete GKLS realization. The framework's Koopman
permutation step is the unitary channel `CPTPMap.ofEquiv`, hence
entropy-preserving; generic non-permutation model steps are not covered.
Irreversible evolution is a separate channel sector, not forced into the
reversible model step.

These results do not construct a nonzero orbitally stable untrapped physical
particle, derive the fermionic assignment of a particular CAT/EPT excitation,
quantize photons, derive microscopic thermodynamics, select charged-lepton
Yukawa ratios, or calibrate particle masses, charges, and couplings from
independently fixed model parameters. The conditioning certificate still
requires a consumer-proved tensor/clock conditioning equality. The complete
clock chain requires externally justified invertible and, for order results,
strictly monotone pairwise maps. The general state-dependent spatial
differential generator, variable-coefficient nonlinear hypoellipticity,
unbounded nonlinear generation, and a smooth maximal globally hyperbolic
Einstein--matter development also remain stronger targets than the scoped
theorems exported here. A concrete nonlinear target flow still supplies its
explicit weak equation, admissibility, conservation laws, and model data;
physical particle identity, calibration, and external validation remain
separate. The M9 charge, Klein--Gordon, and orbital bridges support
criterion-scoped formal/executable closure; they do not identify a specific
measured elementary charge, derive an interacting scalar particle from the
complete CAT/EPT dynamics, or calibrate atomic phenomenology. The evidence
registry does not promote pending declarations to kernel-checked evidence; the
remaining target-specific obligations - localized strong `L^(6/5)` Born
convergence, recentered first-moment control, the concrete energy-critical
Duhamel/Strichartz flow, global mass/energy conservation, and analytic
identification of the numerical stationary branch with the minimizing orbit -
stay queryable in the registry. The finite-Ohmic result is a parameter-origin
theorem inside the stated bath model; it does not yet derive the
Born--Markov/secular reduction from the full continuum system--bath
Hamiltonian, calibrate the coupling/cutoff/shape in physical units, identify a
real transition and environment, or execute a frozen held-out test. The
spectral golden-rule result likewise still assumes that reduction; it does not
derive it from the full unitary continuum system--bath Hamiltonian. The
generic continuum reduction layer still accepts supplied analytic estimates,
but the Gaussian collision-reservoir specialization now constructs its
continuum spectral correlation, transform, truncation limit, unitary dilation,
CPTP Davies-scale limit, and GKSL generator. Its exact fresh-ancilla
Stinespring collisions are not a proof of the stronger thermodynamic Davies
limit for one persistent bath driven by a fixed Hamiltonian `H₀ + λV`.
-/
