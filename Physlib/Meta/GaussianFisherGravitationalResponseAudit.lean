/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential
public import Physlib.Thermodynamics.VerlindeWeakEquivalence
public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.Meta.DerivedPredictions
public import Physlib.Meta.ZilAssert

/-!
# A. Audit of the empirically anchored microscopic gravitational-response sector

The Compton–Fisher bit density is the inverse squared Compton wavelength of the inference
mass; the capstone's cell count is that density times the screen area; a screen at any
radius tiled at the density carries the holographic count at `ħcσ₀⁴`; the entropic force
of such screens is Newton's law at that coupling for every source, probe and radius; the
operational coupling is unique; and the full gravitational system (Newton, Einstein
coupling, Poisson dust source, Schwarzschild, complex EFE) runs at the constructed
coupling.

This audit also classifies the repository's external evidence instead of treating every
laboratory result as interchangeable support.  Atom-recoil metrology anchors the Compton
frequency interface, the condensate analogue realizes the zitterbewegung frequency, atom
interferometry excludes a dissipative Compton-rate reading, and Eötvös measurements test the
mass cancellation in the weak-equivalence interface.  Measured universality of the Newton
coupling then excludes a per-system inference width *within the screen model* and selects the
unique Planck width.

None of those measurements counts independent gravitational screen cells.  The physical
identification with measured Newton `G` therefore remains conditional on the Compton–Fisher
tiling and inference-mass interpretations.  The ZIL assertions below make both sides of this
assessment build-enforced: the empirical anchors may not disappear, and their evidence may
not silently discharge the microscopic tiling premise.
-/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse

#check @Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.comptonBitDensity
#check @Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.comptonBitDensity_eq_inv_cellArea,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.comptonCellBits_eq_density_mul_area,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledBits_eq_holographicBits,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse_couplingForm,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.operational_newtonG_eq_info,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.gaussianFisher_establishes_gravitationalSystem ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.operational_newtonG_eq_info ]

/-! ## A.1. Forward uniqueness of the `G`-free counted-cell coupling -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.candidateNewtonG_eq_countedNewtonG,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.candidateNewtonG_eq_hbar_c_mul_inferenceWidth_four,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.existsUnique_countedNewtonG ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.candidateNewtonG_eq_countedNewtonG,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.candidateNewtonG_eq_hbar_c_mul_inferenceWidth_four,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.existsUnique_countedNewtonG ]

/-! ## A.2. The Planck-calibration sector: the identification proved equivalent to the
Planck-density postulate, uniquely calibrated, and refuted per-system. -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_planckMass,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_planckArea,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_planckDensity,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_tilings_agree,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_at_planckWidth,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_calibration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.planckDensity_iff_eq_planckWidth,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_planckDensityCalibration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.coupling_injective,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.distinct_widths_give_distinct_responses,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.universality_forces_unique_width,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.quarticCoupling_exact_and_identification_iff_planckDensity ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_planckDensity,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_calibration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.planckDensity_iff_eq_planckWidth,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_planckDensityCalibration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.distinct_widths_give_distinct_responses,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.quarticCoupling_exact_and_identification_iff_planckDensity ]

/-! ## A.3. The horizon-consistency sector: the calibration survives the black-hole area
equations and the inverse-square law, exactly. -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledHorizonRadius,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiled_horizonCount_eq_bekenstein,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiled_horizonCount_closedForm,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledScreen_at_horizon_is_hawking,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiled_count_eq_areaEntropy_natural,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledScreen_inverseSquare,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledBits_areaScaling ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledScreen_at_horizon_is_hawking,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherHorizonConsistency.tiledScreen_inverseSquare ]

/-! ## A.4. The experimentally anchored interfaces and falsification-pruned readings -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.analogue_zitterbewegungFrequency_eq_coupling,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential.phaseLike_reading_blind_to_compton,
  Physlib.Thermodynamics.eotvos_null ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.analogue_zitterbewegungFrequency_eq_coupling,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential.phaseLike_reading_blind_to_compton,
  Physlib.Thermodynamics.eotvos_null ]

/-! ## A.5. Build-enforced evidence scope -/

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.GFreeComptonCellCalibration.existsUnique_countedNewtonG
  "epistemic_status" "mathematical-identity"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.gaussianFisherScreenCoupling_eq
  "epistemic_status" "mathematical-identity"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.quarticCoupling_exact_and_identification_iff_planckDensity
  "epistemic_status" "mathematical-identity"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.identification_iff_planckDensity
  "epistemic_status" "consistency-identity"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.existsUnique_planckDensityCalibration
  "epistemic_status" "consistency-identity"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse
  "epistemic_status" "ansatz-loaded"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy
  "experimental_bound"
  "atom-recoil-h-over-m-metrology-fixes-the-compton-frequency-m-c-squared-over-hbar-to-\
0-point-2-ppb-parker-2018-lan-muller-subharmonic-compton-clock-mass-time-metrology"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.analogue_zitterbewegungFrequency_eq_coupling
  "experimental_bound"
  "value:leblanc-2013-coupling-frequency-omega-over-two-pi-between-2.4-and-4.3-kilohertz-\
with-analogue-light-speed-11.6-millimetres-per-second-and-compton-wavelength-about-one-\
micrometre;test:the-fitted-trembling-frequency-must-track-twice-the-independently-set-\
raman-coupling-rest-energy-over-hbar-across-the-coupling-range"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential.visibility_deficit_depends_only_on_differential
  "experimental_bound"
  "value:atom-interferometers-recombine-coherently-over-milliseconds-while-the-compton-time-\
hbar-over-m-c-squared-is-about-8e-27-seconds-for-rubidium-87;test:the-surviving-reading-\
forbids-any-compton-scale-visibility-loss-common-to-both-arms-and-requires-a-deficit-exp-\
minus-half-delta-lambda-times-window-whenever-the-arms-differ-in-entropic-rate-so-an-\
independently-measured-delta-lambda-times-window-predicts-the-deficit-with-no-free-parameter"

#zil_assert_edge Physlib.Thermodynamics.eotvos_null "experimental_bound"
  "value:microscope-final-2022-eotvos-parameter-titanium-platinum-minus-one-point-five-\
plus-minus-two-point-seven-times-ten-to-the-minus-fifteen-and-eot-wash-torsion-balances-\
at-ten-to-the-minus-thirteen;test:the-framework-predicts-exactly-zero-with-no-parameter-\
to-absorb-a-violation-because-the-displacement-entropy-depends-on-the-mass-alone-so-any-\
nonzero-eotvos-ratio-at-any-precision-falsifies-the-displacement-entropy-postulate-outright"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherPlanckCalibration.distinct_widths_give_distinct_responses
  "experimental_bound"
  "value:codata-2022-G-6.67430(15)e-11-m3-kg-1-s-2;test:any-two-physical-screens-assigned-\
distinct-inference-widths-must-not-produce-distinct-newton-couplings-for-the-same-source-\
probe-and-radius"

#zil_assert_edge
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.GaussianFisherGravitationalResponse.tiledScreen_gravitationalResponse
  "requires" "assumption:compton-cell-screen-tiling-is-the-independent-bit-count"

#zil_assert_primitive "assumption:compton-cell-screen-tiling-is-the-independent-bit-count"

/-! ### The de Broglie leverage sector: dispersion theorems and the Compton scattering
anchor of the bit cell. -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.phaseVelocity_eq,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.hasDerivAt_phaseFrequency,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.hasDerivAt_phaseWavenumber,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.groupVelocity_eq_particleVelocity,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonFrequency_additive,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonShift_deBroglie_form,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonShift_right_angle,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonShift_backscatter,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.cellArea_eq_shift_sq,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonBitDensity_eq_inv_shift_sq ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.groupVelocity_eq_particleVelocity,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DeBroglieDispersionComptonAnchor.comptonBitDensity_eq_inv_shift_sq ]

/-! ### The uniqueness sector: the inverse-square law uniquely determines the holographic
stack — profile, coupling, width, EFE normalization, AdS/CFT modulus. -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.inverseSquare_forces_holographicProfile,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.holographicProfile_iff_inverseSquare,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.powerLaw_bitScaling_inverseSquare_iff,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.comptonFisher_inverseSquare_unique_coupling,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.einsteinCoupling_unique_from_poisson,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.existsUnique_d3CompactificationVolume,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.countedData_forces_response,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.stack_from_inverseSquare ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.inverseSquare_forces_holographicProfile,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.holographicProfile_iff_inverseSquare,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.powerLaw_bitScaling_inverseSquare_iff,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.UniqueInverseSquareHolographicCoupling.stack_from_inverseSquare ]

/-! ### The derived ansatz: Verlinde's displacement entropy as the unique entropy gradient
compatible with Unruh thermality and inertia. -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.existsUnique_displacementEntropy,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_eq_iff_unruh_inertial_response,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.verlindeEntropy_iff_inertial_response_law,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_a_independent,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.every_displacementEntropy_compatible_at_zero_acceleration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.not_existsUnique_displacementEntropy_at_zero_acceleration,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_eq_two_pi_nats_per_comptonCell,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_at_one_comptonWavelength ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.existsUnique_displacementEntropy,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_eq_iff_unruh_inertial_response,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.verlindeEntropy_iff_inertial_response_law,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.not_existsUnique_displacementEntropy_at_zero_acceleration ]
