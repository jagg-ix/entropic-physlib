/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass
public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.MuonG2
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.PairAnnihilationGravitationalWave
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation
public import Physlib.Thermodynamics.ModularErasureCost
public import Physlib.Thermodynamics.VerlindeEquipartitionDerivation
meta import Zil

/-!
# The epistemically typed derived-claims ledger

This module inventories kernel-clean theorems that rewrite, conditionally derive, or genuinely constrain a
physical constant or law. A ZIL `derives` edge records the theorem's advertised conclusion; **it does not by
itself assert an independent empirical prediction**. Every such edge therefore carries one enforced
`epistemic_status`:

* `inversion`: algebraically solves a premise or definition back for one of its inputs;
* `consistency-identity`: checks that definitions or established normalizations agree;
* `ansatz-loaded`: has empirical content only conditional on explicit physical/model premises; or
* `risky`: computes a result not inserted through the premise being tested and can independently fail.

Only the last class makes an independently risky prediction relative to its explicitly stated model and
premises. The others remain valuable as audited bookkeeping, cross-module coherence, or conditional model
consequences, but must not be advertised as parameter-free predictions.

* **the Weinberg angle** `sin²θ_W = 3/8` at unification — `WeinbergAngle.su5_sin2Weinberg_eq_three_eighths`.
  The SU(5) prediction, a *derived* value where the Standard Model takes `θ_W` as an input.
* **mass from geometry** `m² = 8·a·v₀²` — `GeometricOriginOfMass.geometric_origin_of_mass`. The vacuum mass
  as the curvature of the Landau potential at its minimum, not a free Yukawa parameter.
* **the muon magnetic anomaly** `a_μ = K² − 1` — `MuonG2.entropicDefect_eq_muon_g2` is a consistency
  identity between two definitions. The stronger `MuonG2.joint_anomaly_fractional_wMass_shift` relates it
  to a W-mass shift, but remains ansatz-loaded until `κ` and `c` are fixed without W-mass data.
* **Bekenstein–Hawking entropy** `S_BH = k_B·4πGM²/(ℏc)` — `SchwarzschildInteriorFoliationMetric.bhEntropy_eq_mass`.
  The horizon entropy from the Schwarzschild area, and its ER=EPR one-bit consequence.
* **the ER=EPR wormhole mass** `M = √(ℏc·ln2/(4πG))` — `SchwarzschildInteriorFoliationMetric.erEpr_wormholeMass`.
  Setting the bridge entropy to one entanglement bit *fixes* the mass — the quantitative tension the
  Dai–Minic–Stojkovic–Fu test exposes.
* **the cosmological constant in horizon-bit coordinates** `Λ = 12πc³/(ℏGN)` —
  `DeSitterCosmologicalConstantBits.cosmologicalConstant_bitForm` inverts the same `Λ`-dependent horizon-bit
  definition. It predicts `Λ` only if a microscopic `N` is supplied independently.
* **the icosahedral golden ratio** `2cos(π/5) = φ` —
  `IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio`. The exact five-fold geometric identity
  inventories the golden constant used by the program without promoting it to a dynamical prediction.
* **the fine-structure constant from Planck and screen data** —
  `EntanglementScreenArea.fineStructure_at_planckMass` rewrites `α` as the electromagnetic/gravitational
  force ratio at the Planck mass, while `EntanglementScreenArea.fineStructure_from_screenBits` eliminates
  `ℏc` in favor of charge-to-mass, entanglement nats, `G`, and the holographic screen-bit count.
* **the Unruh/Hawking modular normalization** `β = 2π` in natural units —
  `KayWaldHawkingKMSHorizon.wedgeModular_natural_is_unruhBeta`. The wedge modular eigenvalue has exactly
  the Unruh inverse-temperature exponent; this is an eigenvalue identity, not a detector-response theorem.
* **holographic Newton coupling through the Einstein chain** —
  `HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain`. The area
  per bit fixes `G` and `κ_G`, then connects the Compton/de Broglie clock, Nagao–Nielsen contour, and
  metric-derived Levi-Civita geometry to a conditional Einstein equation.
* **the `G`-free Gaussian-Fisher screen coupling** `G_info = ℏc σ₀⁴` —
  `ComptonCellNewtonConstant.gaussianFisherScreenCoupling_eq`. The Gaussian score integral proves
  `I = 1/σ₀²`, and the normalized screen area uniquely fixes the effective count through
  `N λ² = A`; no Newton constant occurs in either construction. The identification with measured
  Newton `G` is settled in `GaussianFisherPlanckCalibration`: it is *equivalent* to the
  one-bit-per-Planck-area postulate the holographic count always encoded
  (`identification_iff_planckDensity`), holds for exactly one width — the Planck width
  `σ_P = (G/ℏc)^{1/4}`, i.e. `inferenceMass = m_P` (`existsUnique_calibration`) — and is
  *refuted* for any per-system width by coupling injectivity
  (`distinct_widths_give_distinct_responses`). The one remaining physical question is the
  holographic Planck-density postulate itself; there is no second premise and no free constant.
* **the Zitterbewegung rest-frame beat** `ω_Z = 2mc²/ℏ` —
  `PairAnnihilationGravitationalWave.annihilation_phase_zitterbewegung`. The positive/negative-energy
  pair phase is exactly the Zitterbewegung phase at twice the Compton frequency.
* **the de Sitter bit-count synthesis** — `DeSitterCosmologicalConstantBits.deSitter_darkEnergy_bitCount`.
  A single horizon-bit identification jointly fixes `Λ`, horizon entropy, the contour-decoherence factor,
  and vacuum-energy density; it does not independently determine the bit count from observation.

Each attachment also carries `experimental_bound@`: a reference value where a direct measurement exists,
or an explicit `no-direct-measurement` marker otherwise, followed by the independent comparison that could
falsify the claimed identification. Values are provenance-tagged so an update does not masquerade as a
change to a kernel theorem.

Every entry is audited kernel-clean (`Physlib.Meta.SpineAxiomAudit` covers the spine; these are checked here).
The ledger asserts no new physics theorem. Its compile-time gate prevents future prose from collapsing
inversions, identities, conditional models, and independently risky results into one undifferentiated
“prediction” class. This module adds no aliases, axioms, or proof terms.
-/

@[expose] public section

namespace Physlib.Meta.DerivedPredictions

open Lean Elab Command

/-! ### The ledger — each `derives` edge carries an enforced epistemic status -/

zil attach Physlib.QuantumMechanics.ComplexAction.WeinbergAngle.su5_sin2Weinberg_eq_three_eighths where
  derives @ "constant:weinberg-angle-sin-squared-equals-three-eighths",
  epistemic_status @ "risky",
  prediction_class @ "derived-numerical-prediction",
  standard_physics_postulates @ "input:electroweak-mixing-angle-is-a-free-parameter",
  supported_by @ "paper:georgi-glashow-su5-1974",
  caveat @ "claim:tree-level-unification-value-not-the-running-low-energy-angle",
  experimental_bound @ "value:pdg-2025-msbar-sin2thetaW-at-MZ-0.23122-plusminus-0.00006;test:renormalization-group-running-must-reach-three-eighths-at-the-claimed-unification-scale"

zil attach Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass.geometric_origin_of_mass where
  derives @ "law:mass-squared-is-landau-potential-curvature-at-vacuum",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "model-specific-finite-carrier-result",
  standard_physics_postulates @ "input:fermion-and-boson-masses-are-free-yukawa-parameters",
  caveat @ "claim:landau-double-well-model-not-the-full-standard-model-higgs-sector",
  experimental_bound @ "value:no-universal-direct-measurement-for-model-parameters-a-and-v0;test:independently-fixed-a-and-v0-must-reproduce-the-corresponding-pole-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.MuonG2.entropicDefect_eq_muon_g2 where
  derives @ "law:muon-anomalous-moment-is-entanglement-schmidt-defect-k-squared-minus-one",
  epistemic_status @ "consistency-identity",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "measurement:muon-anomalous-magnetic-moment-is-an-experimentally-measured-input",
  supported_by @ "measurement:fermilab-muon-g-2-final-2025",
  supported_by @ "paper:muon-g-2-theory-initiative-update-2025",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.fermilabMagicGamma_determines_schmidtNumber",
  caveat @ "claim:operational-k-is-reconstructed-from-storage-ring-lorentz-factor-not-direct-qft-schmidt-tomography",
  caveat @ "claim:algebraic-change-of-variables-until-K-is-derived-from-a-state-before-using-a-mu",
  caveat @ "epistemic:k-squared-minus-one-occurs-on-both-sides-by-definition-so-this-theorem-alone-cannot-predict-a-mu",
  caveat @ "claim:2025-theory-update-finds-no-significant-sm-experiment-tension-so-anomaly-means-g-minus-two-not-unresolved-discrepancy",
  experimental_bound @ "value:fermilab-2025-a-mu-0.001165920705-stat-0.000000000114-syst-0.000000000091;test:measured-storage-ring-gamma-or-momentum-must-reconstruct-K-and-K-squared-minus-one-consistently-but-does-not-independently-predict-a-mu"

zil attach Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.MuonG2.joint_anomaly_fractional_wMass_shift where
  derives @ "law:fractional-w-mass-shift-equals-kappa-times-c-times-muon-anomaly",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "conditional-cross-observable-result",
  standard_physics_postulates @ "input:muon-magnetic-anomaly-and-w-boson-mass-are-independent-observables",
  supported_by @ "paper:endo-mishima-2022-w-mass-gf-shift",
  caveat @ "claim:cross-observable-form-and-sign-are-proved-but-no-parameter-free-w-mass-magnitude-is-derived",
  caveat @ "claim:kappa-and-especially-c-must-be-fixed-without-the-w-mass-datum-for-the-relation-to-be-predictive",
  caveat @ "claim:cdf-2022-w-mass-target-is-disputed-and-fitting-c-to-it-is-not-independent-verification",
  experimental_bound @ "value:cdf-2022-MW-80.4335-plusminus-0.0094-GeV;test:independently-fixed-kappa-and-c-must-map-the-measured-a-mu-to-an-independent-w-mass-measurement"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.fermilabMagicGamma_determines_schmidtNumber where
  formalizes @ "claim:storage-ring-gamma-29.3-fixes-operational-schmidt-number",
  epistemic_status @ "consistency-identity",
  supported_by @ "measurement:fermilab-bnl-magic-momentum-3.094-gev-over-c-and-gamma-29.3",
  supported_by @ "paper:muon-g-2-ricap-2024-operating-point-kinematics",
  caveat @ "claim:gamma-reconstruction-is-operational-not-entanglement-tomography",
  caveat @ "epistemic:magic-gamma-is-selected-through-the-anomaly-dependent-thomas-bmt-cancellation-so-it-is-not-an-independent-prediction-of-a-mu",
  experimental_bound @ "value:gamma-29.3-implies-1.0005-lt-K-lt-1.0006-and-0.001166-lt-K-squared-minus-one-lt-0.001167;test:updated-beam-momentum-distribution-must-preserve-the-operational-kinematic-bounds"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha.schmidtNumberFromAlpha_eq_schmidtNumberFromGamma where
  formalizes @ "claim:alpha-derived-and-storage-ring-gamma-derived-operational-schmidt-numbers-agree",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.schmidtNumberFromGamma_sq_sub_one",
  supported_by @ "measurement:fermilab-bnl-magic-momentum-3.094-gev-over-c-and-gamma-29.3",
  caveat @ "claim:exact-equality-assumes-the-two-reconstructed-anomalies-agree-and-does-not-constitute-independent-verification-or-qft-schmidt-tomography",
  experimental_bound @ "value:both-published-channels-place-K-between-1.0005-and-1.0006;test:precision-alpha-and-beam-kinematic-reconstructions-must-remain-compatible"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt.alpha_from_schmidt where
  formalizes @ "claim:alpha-is-two-pi-times-schmidt-defect-under-schwinger-anomaly-identification",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation.alpha_isolated",
  caveat @ "epistemic:the-theorem-assumes-schwingerAnomaly-alpha-equals-anomaly-of-rapidity-K-and-solves-that-premise-for-alpha"

zil attach Physlib.Thermodynamics.ModularErasureCost.neg_log_wedgeModularEigenvalue where
  supported_by @ "lean:HermitianMat.log_exp",
  formalizes @ "claim:negative-log-of-wedge-modular-eigenvalue-is-modular-hamiltonian-eigenvalue",
  epistemic_status @ "consistency-identity",
  caveat @ "epistemic:log-exp-cancellation-on-paired-definitions-not-an-independent-modular-spectrum-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.bhEntropy_eq_mass where
  derives @ "constant:bekenstein-hawking-entropy-from-schwarzschild-area",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:black-hole-entropy-is-a-semiclassical-assumption",
  supported_by @ "paper:bekenstein-1973-hawking-1975",
  experimental_bound @ "value:no-direct-black-hole-entropy-measurement;test:any-independent-horizon-microstate-count-must-equal-kB-times-area-over-four-planck-areas"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.erEpr_wormholeMass where
  derives @ "constant:er-epr-one-bit-wormhole-mass-root-hbar-c-ln2-over-four-pi-g",
  epistemic_status @ "inversion",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:er-epr-correspondence-is-a-conjecture",
  supported_by @ "paper:dai-minic-stojkovic-fu-2020",
  caveat @ "claim:value-identity-exposes-a-mass-scale-tension-not-a-resolution",
  experimental_bound @ "value:no-direct-one-bit-wormhole-mass-measurement;test:a-realized-one-bit-bridge-mass-must-equal-root-hbar-c-ln2-over-four-pi-G"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.cosmologicalConstant_bitForm where
  derives @ "constant:cosmological-constant-is-twelve-pi-c-cubed-over-hbar-g-n",
  epistemic_status @ "inversion",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:cosmological-constant-is-an-observed-free-parameter",
  supported_by @ "paper:gibbons-hawking-de-sitter-horizon-1977",
  caveat @ "claim:form-follows-conditionally-from-identifying-n-with-the-de-sitter-horizon-bit-count-not-from-fitting-the-observed-value",
  caveat @ "epistemic:n-is-defined-from-the-same-lambda-dependent-horizon-so-the-theorem-algebraically-inverts-its-premise",
  experimental_bound @ "value:planck-2018-flat-lcdm-H0-67.4-plusminus-0.5-km-s-Mpc-and-OmegaM-0.315-plusminus-0.007;test:the-independently-counted-horizon-N-must-reproduce-the-inferred-Lambda"

zil attach Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio where
  derives @ "constant:icosahedral-pentagon-cosine-equals-golden-ratio",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:golden-ratio-is-an-external-geometric-constant",
  supported_by @ "claim:icosahedral-five-fold-symmetry",
  caveat @ "claim:exact-geometric-identity-not-by-itself-a-dynamical-or-empirical-physics-prediction",
  experimental_bound @ "value:exact-geometric-identity-no-direct-physics-measurement;test:any-physical-use-requires-an-independently-observed-icosahedral-five-fold-structure"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.fineStructure_at_planckMass where
  derives @ "constant:fine-structure-is-electromagnetic-to-gravitational-force-ratio-at-planck-mass",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:fine-structure-constant-is-a-measured-independent-coupling",
  supported_by @ "definition:fine-structure-constant-and-planck-mass",
  caveat @ "claim:planck-mass-reparameterization-not-a-prediction-of-the-observed-alpha-value",
  experimental_bound @ "value:codata-2022-alpha-inverse-137.035999177(21);test:independently-determined-planck-mass-data-must-reproduce-alpha-within-codata-uncertainty"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.fineStructure_from_screenBits where
  derives @ "constant:fine-structure-is-charge-mass-entanglement-nats-over-holographic-screen-bits",
  epistemic_status @ "consistency-identity",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:fine-structure-constant-is-a-measured-independent-coupling",
  supported_by @ "definition:entanglement-screen-holographic-bit-count",
  caveat @ "claim:conditional-screen-identity-not-a-numerical-prediction-without-independent-physical-inputs",
  experimental_bound @ "value:codata-2022-alpha-inverse-137.035999177(21);test:independently-measured-charge-mass-eta-G-and-screen-N-must-reproduce-alpha-within-codata-uncertainty"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon.wedgeModular_natural_is_unruhBeta where
  derives @ "constant:unruh-inverse-temperature-beta-is-two-pi-in-natural-units",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:unruh-temperature-normalization-is-imposed-by-quantum-field-theory",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "definition:summers-unruh-inverse-temperature",
  caveat @ "claim:natural-units-eigenvalue-identity-not-detector-response-or-kms-state-uniqueness",
  experimental_bound @ "value:two-pi-is-the-exact-natural-units-qft-normalization-no-direct-unruh-detector-measurement;test:an-accelerated-detector-spectrum-must-have-the-corresponding-thermal-slope"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain where
  derives @ "law:holographic-area-per-bit-fixes-newton-coupling-and-conditional-einstein-chain",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:newton-constant-and-einstein-coupling-are-empirical-inputs",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  caveat @ "claim:complex-einstein-equation-is-an-explicit-premise-not-derived-by-the-clock-or-contour-identities",
  caveat @ "claim:exact-one-plus-one-einstein-tensor-forces-the-real-source-carrier-to-zero",
  caveat @ "claim:conditional-algebraic-chain-not-an-empirical-measurement-of-newtons-constant",
  experimental_bound @ "value:codata-2022-G-6.67430(15)e-11-m3-kg-1-s-2;test:independent-area-per-bit-data-must-reproduce-G-and-a-nonzero-source-requires-the-existing-three-plus-one-upgrade"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance where
  derives @ "constant:newton-coupling-is-hbar-c-times-inference-position-variance-to-the-fourth",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:newton-constant-is-an-empirically-measured-independent-coupling",
  supported_by @ "paper:caticha-cafaro-2007-information-geometric-newtonian-dynamics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
  caveat @ "claim:the-gaussian-score-integral-and-effective-area-count-are-now-\
constructed-but-identifying-the-resulting-information-screen-coupling-with-measured-\
newton-g-and-fixing-sigma0-remain-physical-inputs",
  experimental_bound @ "value:codata-2022-G-6.67430(15)e-11-m3-kg-1-s-2;test:an-independently-measured-inference-variance-sigma0-and-compton-screen-cell-count-must-reproduce-G-without-fitting-G"

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.PairAnnihilationGravitationalWave.annihilation_phase_zitterbewegung where
  derives @ "law:zitterbewegung-rest-frequency-is-two-times-compton-frequency",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:zitterbewegung-frequency-follows-from-positive-negative-dirac-branches",
  supported_by @ "paper:schrodinger-zitterbewegung-1930",
  caveat @ "claim:exact-phase-identity-not-a-direct-observation-of-free-particle-zitterbewegung",
  experimental_bound @ "value:no-direct-free-particle-rest-frame-zitterbewegung-frequency-measurement;test:an-interference-measurement-must-scale-as-two-m-c-squared-over-hbar"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits.deSitter_darkEnergy_bitCount where
  derives @ "law:one-de-sitter-horizon-bit-count-fixes-lambda-entropy-decoherence-and-vacuum-density",
  epistemic_status @ "inversion",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:dark-energy-density-horizon-entropy-and-decoherence-are-separate-model-inputs",
  supported_by @ "paper:gibbons-hawking-de-sitter-horizon-1977",
  caveat @ "claim:all-four-identities-are-conditional-on-the-same-holographic-horizon-bit-identification",
  caveat @ "claim:the-theorem-does-not-independently-measure-N-or-select-flat-lcdm",
  experimental_bound @ "value:planck-2018-flat-lcdm-H0-67.4-plusminus-0.5-km-s-Mpc-and-OmegaM-0.315-plusminus-0.007;test:one-independently-inferred-N-must-simultaneously-match-Lambda-vacuum-density-entropy-and-decoherence"

zil attach Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh where
  derives @ "law:newtons-second-law-from-entropic-force-at-unruh-temperature",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:newtons-second-law-is-an-axiom-of-classical-mechanics",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  caveat @ "claim:displacement-entropy-ansatz-is-verlinde-postulate-not-derived",
  experimental_bound @ "value:f-equals-m-a-holds-to-all-tested-precision-in-the-nonrelativistic-regime;test:any-unruh-temperature-deviation-would-shift-the-entropic-force-normalization"

-- Verlinde's screen equipartition is NOT a postulate: it is DERIVED here from the classical equipartition
-- theorem, so the gravity ledger entries below rest on it as a derived result, not an assumption.
zil attach Physlib.Thermodynamics.verlinde_equipartition_from_NDOF where
  formalizes @ "claim:screen-equipartition-derived-from-n-classical-quadratic-degrees-of-freedom",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.StatisticalMechanics.Equipartition.equipartition_quadraticDOF",
  supported_by @ "paper:verlinde-2011",
  caveat @ "claim:the-derivation-is-the-classical-high-temperature-quadratic-dof-limit-quantum-two-level-bits-acquire-corrections-at-low-temperature"

zil attach Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde where
  derives @ "law:newton-inverse-square-gravity-from-equipartition-on-holographic-bits",
  epistemic_status @ "ansatz-loaded",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:newtons-law-of-gravitation-is-an-empirical-law-with-measured-G",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  caveat @ "claim:equipartition-is-derived-verlinde-equipartition-from-ndof-the-remaining-inputs-are-the-displacement-entropy-ansatz-and-the-holographic-bit-count-through-which-G-enters",
  experimental_bound @ "value:codata-2022-G-6.67430(15)e-11-m3-kg-1-s-2;test:screen-bit-counting-must-reproduce-the-cavendish-value-of-G"

zil attach Physlib.Relativity.SemiClassical.verlindeTemperature_at_horizon_is_hawking where
  derives @ "law:horizon-screen-temperature-equals-hawking-temperature",
  epistemic_status @ "consistency-identity",
  prediction_class @ "model-specific-finite-carrier-result",
  standard_physics_postulates @ "input:hawking-temperature-is-a-separate-semiclassical-qft-result",
  supported_by @ "paper:verlinde-2010-emergent-gravity",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  caveat @ "claim:static-eigenvalue-identity-not-dynamical-hawking-radiation",
  experimental_bound @ "value:no-direct-black-hole-temperature-measurement-analogue-systems-only;test:an-analogue-horizon-spectrum-must-match-the-surface-gravity-slope"

zil attach Physlib.Thermodynamics.ModularErasureCost.horizon_bit_erasure_is_one_bit_entropy where
  derives @ "law:one-bit-erased-at-the-horizon-grows-horizon-entropy-by-exactly-kb-ln-two",
  epistemic_status @ "consistency-identity",
  prediction_class @ "conditional-screen-or-identification-result",
  standard_physics_postulates @ "input:landauer-principle-and-bekenstein-horizon-accounting-are-separate-postulates",
  supported_by @ "paper:landauer-1961",
  supported_by @ "paper:bekenstein-1973",
  caveat @ "claim:static-first-law-increment-not-a-dynamical-infall-process",
  caveat @ "epistemic:first-law-hawking-temperature-and-landauer-normalizations-force-the-cancellation-so-this-is-not-an-independent-prediction",
  experimental_bound @ "value:no-direct-horizon-bit-erasure-measurement;test:any-landauer-violating-erasure-would-break-the-generalized-second-law"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation.anomalyFrequency_gamma_independent where
  derives @ "law:anomaly-frequency-is-gamma-independent-g-times-qb-over-m",
  epistemic_status @ "risky",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:storage-ring-operating-point-imported-from-accelerator-practice",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:tbmt-force-law-taken-as-given-not-derived-from-qed",
  experimental_bound @ "value:fermilab-final-2025-omega-a-at-127-ppb;test:the-anomaly-frequency-must-be-energy-independent-across-the-beam-momentum-spread"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation.electricTermCoeff_vanishes_at_gamma where
  derives @ "law:magic-lorentz-factor-is-the-zero-of-the-tbmt-electric-term",
  epistemic_status @ "consistency-identity",
  prediction_class @ "exact-mathematical-identity",
  standard_physics_postulates @ "input:magic-momentum-3.094-gev-chosen-operationally-in-ring-design",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:upgrades-the-audited-change-of-variables-to-a-derived-cancellation-not-entanglement-evidence",
  experimental_bound @ "value:gamma-29.3-magic-momentum-3.094-gev-over-c;test:residual-electric-field-systematic-C-e-must-scale-with-the-off-magic-detuning"

zil_rule derivedPredictionLedger:
  ?constant # is_derived_by @ ?declaration IF
  ?declaration # derives @ ?constant

zil_rule derivedPredictionFalsifies:
  ?constant # contrasts_with @ ?fact IF
  ?declaration # derives @ ?constant AND
  ?declaration # standard_physics_postulates @ ?fact

zil_rule derivedPredictionExperimentalBound:
  ?constant # is_tested_against @ ?bound IF
  ?declaration # derives @ ?constant AND
  ?declaration # experimental_bound @ ?bound

zil_rule derivedPredictionClassification:
  ?constant # has_falsification_class @ ?category IF
  ?declaration # derives @ ?constant AND
  ?declaration # prediction_class @ ?category

zil_rule derivedPredictionEpistemicStatus:
  ?constant # has_epistemic_status @ ?status IF
  ?declaration # derives @ ?constant AND
  ?declaration # epistemic_status @ ?status

zil_rule riskyPredictionSurface:
  ?constant # is_risky_prediction_by @ ?declaration IF
  ?declaration # derives @ ?constant AND
  ?declaration # epistemic_status @ "risky"

zil_rule ansatzLoadedSurface:
  ?constant # is_ansatz_loaded_consequence_of @ ?declaration IF
  ?declaration # derives @ ?constant AND
  ?declaration # epistemic_status @ "ansatz-loaded"

zil_rule inversionSurface:
  ?constant # is_algebraically_inverted_by @ ?declaration IF
  ?declaration # derives @ ?constant AND
  ?declaration # epistemic_status @ "inversion"

zil_rule consistencySurface:
  ?constant # is_consistency_checked_by @ ?declaration IF
  ?declaration # derives @ ?constant AND
  ?declaration # epistemic_status @ "consistency-identity"

/-! ### Compile-time falsification-surface completeness

This gate is deliberately scoped to attachments owned by this module. Every declaration carrying a
`derives` relation must carry exactly one `experimental_bound`, exactly one `prediction_class`, and exactly
one `epistemic_status` from the closed vocabulary `{inversion, consistency-identity, ansatz-loaded, risky}`.
A future ledger entry with a missing, ambiguous, or misspelled field fails elaboration and reports its Lean
declaration name. -/

run_cmd
  let env ← getEnv
  let moduleName := `Physlib.Meta.DerivedPredictions
  let entries := Zil.declarationAttachments env
  let derived := entries.filter fun entry =>
    entry.module == moduleName && entry.atom.relation == "derives"
  let invalid := derived.filter fun entry =>
    let bounds := entries.filter fun candidate =>
      candidate.module == moduleName &&
        candidate.declaration == entry.declaration &&
        candidate.atom.relation == "experimental_bound"
    bounds.size != 1
  unless invalid.isEmpty do
    throwError
      "derived-predictions coverage failure: expected exactly one experimental_bound for {invalid.map (·.declaration)}"
  let invalidClass := derived.filter fun entry =>
    let classes := entries.filter fun candidate =>
      candidate.module == moduleName &&
        candidate.declaration == entry.declaration &&
        candidate.atom.relation == "prediction_class"
    classes.size != 1
  unless invalidClass.isEmpty do
    throwError
      "derived-predictions classification failure: expected exactly one prediction_class for {invalidClass.map (·.declaration)}"
  let invalidStatus := derived.filter fun entry =>
    let statuses := entries.filter fun candidate =>
      candidate.module == moduleName &&
        candidate.declaration == entry.declaration &&
        candidate.atom.relation == "epistemic_status"
    statuses.size != 1
  unless invalidStatus.isEmpty do
    throwError
      "derived-predictions epistemic-status failure: expected exactly one epistemic_status for {invalidStatus.map (·.declaration)}"
  let allowedStatus : Zil.Value → Bool
    | .symbol "inversion" => true
    | .symbol "consistency-identity" => true
    | .symbol "ansatz-loaded" => true
    | .symbol "risky" => true
    | _ => false
  let invalidStatusValue := derived.filter fun entry =>
    let statuses := entries.filter fun candidate =>
      candidate.module == moduleName &&
        candidate.declaration == entry.declaration &&
        candidate.atom.relation == "epistemic_status"
    statuses.any fun candidate => !allowedStatus candidate.atom.subject
  unless invalidStatusValue.isEmpty do
    throwError
      "derived-predictions epistemic-status failure: status must be inversion, consistency-identity, ansatz-loaded, or risky for {invalidStatusValue.map (·.declaration)}"
  logInfo m!"derived-predictions coverage: all {derived.size} ledger entries have exactly one experimental_bound, one prediction_class, and one valid epistemic_status"

end Physlib.Meta.DerivedPredictions
