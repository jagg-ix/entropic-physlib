/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# ZIL contracts for the Section 4 analytic interfaces

These contracts distinguish proved downstream consequences from the two deep
analytic existence mechanisms that remain explicit theorem premises.
-/

@[expose] public section

/- ZIL-BEGIN -/
open Zil
/- ZIL-END -/

namespace Physlib.Meta.MultiNormSection4PaperZil

/- ZIL-BEGIN -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.arbitraryMultiIndex_moment_derivative_decomposition
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.HadamardDecompositionMechanism,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.coordinateDerivative
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.arbitraryMultiIndex_moment_derivative_decomposition
    where
  formalizes @ "claim:lemma4.1-arbitrary-multi-index-derivative-decomposition-interface-with-support-control",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.1",
  requires @ "assumption:hadamard-decomposition-mechanism-from-order-m-moment-cancellation",
  caveat @ "claim:does-not-construct-the-hadamard-mechanism-from-moment-cancellation"

zil_file_contract physlib.entropicSpine.multiNormSection4MomentDerivative where
  promises "formalization:finite-exact-order-multi-index-derivative-decomposition-interface"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.exactMultiIndices",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.schwartzMoment",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.HasCancellationOrder",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.ComponentsNormalizedRelative",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.DerivativeDecomposition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.arbitraryMultiIndex_moment_derivative_decomposition"
  ]
  forbids_substitutes [
    "claiming unconditional existence of Hadamard decomposition components",
    "calling the decomposition premise a proof of moment-derivative equivalence",
    "replacing bundled Schwartz derivatives with an unrelated symbolic derivative"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.arbitraryMultiIndex_moment_derivative_decomposition
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.HasCancellationOrder,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full
    where
  formalizes @ "claim:lemma4.2-certified-dual-families-cancellation-support-partial-and-full-calderon-identities",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2",
  requires @ "assumption:dual-calderon-family-certificate-constructed-from-the-original-family",
  caveat @ "claim:does-not-construct-the-tilded-families-or-prove-their-relative-seminorm-bounds"

zil_file_contract physlib.entropicSpine.multiNormSection4DualCalderon where
  promises "formalization:paper-faithful-dual-family-certificate-and-all-certified-consequences"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.NormalizedRelative",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily.partial_identity",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full"
  ]
  forbids_substitutes [
    "calling a supplied certificate unconditional construction of the tilded families",
    "discarding Fourier or spatial support fields",
    "calling a finite partial identity an infinite distributional limit"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorApproximationKernel,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorDualApproximationKernel,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.HasCancellationOrder
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family
    where
  formalizes @ "claim:proposition4.3-finite-full-multi-index-tensor-calderon-identities",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-proposition4.3",
  requires @ "assumption:coordinate-dual-calderon-certificates",
  caveat @ "claim:finite-coordinatewise-box-identity-not-yet-the-infinite-distributional-sum-regrouped-by-paper-index-set-L"

zil_file_contract physlib.entropicSpine.multiNormSection4TensorCalderon where
  promises "formalization:actual-full-function-indexed-product-tensors-and-finite-partial-identities"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:SchwartzMap.productTensor",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorIndexBox",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorApproximation_eq_sum_details",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullTensorDualApproximation_eq_sum_details",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family"
  ]
  forbids_substitutes [
    "calling a finite coordinatewise box the full infinite distributional formula",
    "claiming the paper-specific L regrouping without an index partition theorem",
    "claiming unconditional tensor duality without coordinate certificates"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon.fullMultiIndex_tensorProduct_calderon_family
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkov_partial_kernel_identity
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualDetailConvolution,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualApproximationConvolution
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkov_partial_kernel_identity
    where
  formalizes @ "claim:lemma4.2-equations4.2-and4.3-constructed-tilded-kernels-and-finite-calderon-identity",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2",
  caveat @ "claim:relative-seminorm-cancellation-compact-spatial-support-and-final-approximation-limit-remain-in-rychkov-analytic-certificate"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovConstruction where
  promises "formalization:actual-rychkov-fourier-polynomial-kernels-and-proved-finite-convolution-telescope"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.sum_rychkovProductTerm",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkov_partial_kernel_identity"
  ]
  forbids_substitutes [
    "replacing the constructed Fourier factors with an existential family",
    "calling the finite telescope the full distributional limit",
    "claiming arbitrary cancellation without the analytic derivative estimate"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkov_partial_kernel_identity
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualApproximation_support
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovFourierApproximationCarrier
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualApproximation_support
    where
  formalizes @ "claim:lemma4.2e-constructed-rychkov-approximation-inherits-original-fourier-support",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2e"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovApproximationSupport where
  promises "formalization:constructed-rychkov-approximation-has-canonical-original-fourier-carrier"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovFourierApproximationCarrier",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualApproximation_support"
  ]
  forbids_substitutes [
    "supplying Fourier approximation support as an external certificate field",
    "using the whole frequency space as a vacuous support carrier"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualApproximation_support
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualDetail_support
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovFourierDetailCarrier
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualDetail_support
    where
  formalizes @ "claim:lemma4.2e-constructed-rychkov-detail-is-supported-in-adjacent-fourier-carriers",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2e"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovDetailSupport where
  promises "formalization:all-constructed-rychkov-detail-levels-have-canonical-adjacent-fourier-carriers"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovFourierDetailCarrier",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualDetail_succ_support",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualDetail_support"
  ]
  forbids_substitutes [
    "supplying Fourier detail support as an external certificate field",
    "discarding the level-zero low-frequency case"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.fourier_rychkovDualDetail_support
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.dualApproximationConvolution_eq_spatialPolynomial
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovApproximationSpatialPolynomial,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualApproximationConvolution
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.dualApproximationConvolution_eq_spatialPolynomial
    where
  formalizes @ "claim:lemma4.2-equation4.3-final-approximation-is-an-explicit-finite-spatial-convolution-polynomial",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2",
  caveat @ "claim:this-exact-finite-formula-does-not-by-itself-prove-the-final-approximation-limit"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovApproximationSpatialFormula where
  promises "formalization:constructed-final-approximation-convolution-equals-the-residual-convolution-polynomial"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.residualConvolutionApply",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovApproximationSpatialPolynomial",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.dualApproximationConvolution_eq_spatialPolynomial"
  ]
  forbids_substitutes [
    "replacing the spatial convolution polynomial by unsupported frequency metadata",
    "calling a finite exact identity an asymptotic delta-limit"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.dualApproximationConvolution_eq_spatialPolynomial
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetail_succ_eq_spatialPolynomial
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetailSuccSpatialPolynomial
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetail_succ_eq_spatialPolynomial
    where
  formalizes @ "claim:lemma4.2-equation4.2-tilded-details-are-explicit-finite-spatial-convolution-polynomials",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovDetailSpatialFormula where
  promises "formalization:constructed-positive-level-tilded-details-equal-two-residual-spatial-convolution-polynomials"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualApproximation_eq_spatialPolynomial",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetailSuccSpatialPolynomial",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetail_succ_eq_spatialPolynomial"
  ]
  forbids_substitutes [
    "supplying an unrelated existential tilded family",
    "discarding the level-zero approximation branch"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetail_succ_eq_spatialPolynomial
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkov_constructed_spatial_compactSupport
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualApproximationConvolution
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkov_constructed_spatial_compactSupport
    where
  formalizes @ "claim:lemma4.2f-constructed-tilded-kernels-and-final-approximation-have-compact-spatial-support",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2",
  caveat @ "claim:compactness-is-proved-but-the-paper-uniform-explicit-dilate-bound-remains-quantitative-work"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovSpatialCompactSupport where
  promises "formalization:compact-spatial-support-derived-for-all-constructed-rychkov-kernels"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.complexDyadicApproximationKernel_hasCompactSupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.schwartzConvolution_hasCompactSupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualApproximation_hasCompactSupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkovDualDetail_hasCompactSupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkov_constructed_spatial_compactSupport"
  ]
  forbids_substitutes [
    "retaining compact spatial support only as an external certificate field",
    "calling qualitative compactness the paper's uniform explicit support-dilate estimate"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial.rychkov_constructed_spatial_compactSupport
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.tendsto_rychkovDualCalderon_of_approximation
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderonPartialDistribution,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualApproximationDistribution,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.tendsto_rychkovDualCalderon_of_approximation
    where
  formalizes @ "claim:lemma4.2c-full-detail-calderon-limit-reduced-to-final-approximation-limit",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2c",
  requires @ "assumption:constructed-rychkov-final-approximation-converges-to-dirac",
  caveat @ "claim:the-detail-series-limit-is-derived-and-is-not-an-independent-certificate-field"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovLimitBridge where
  promises "formalization:constructed-finite-identity-transports-the-approximation-limit-to-the-full-detail-calderon-limit"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.dualCalderonPartialDistribution_rychkov_eq_approximation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.tendsto_rychkovDualCalderon_of_approximation"
  ]
  forbids_substitutes [
    "assuming the full detail-series limit independently of the proved finite identity",
    "calling approximation convergence proved when it remains the analytic premise"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.tendsto_rychkovDualCalderon_of_approximation
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualApproximation_delta
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualApproximationDistribution,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualApproximation_delta
    where
  formalizes @ "claim:lemma4.2c-constructed-final-rychkov-approximation-converges-to-dirac",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2c",
  caveat @ "claim:the-proof-uses-fourier-scaling-normalization-and-dominated-convergence-not-an-external-limit-certificate"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovApproximationLimit where
  promises "formalization:constructed-rychkov-final-approximation-converges-to-dirac-without-an-external-certificate"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.fourier_complexDyadicApproximationKernel_apply",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.norm_fourier_dualApproximationConvolution_rychkov_le",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualApproximation_delta"
  ]
  forbids_substitutes [
    "retaining the final approximation limit as a certificate field",
    "calling pointwise Fourier convergence distributional convergence without an integrable dominator"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualApproximation_delta
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualCalderon_delta
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderonPartialDistribution,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualCalderon_delta
    where
  formalizes @ "claim:lemma4.2c-full-constructed-rychkov-detail-calderon-limit",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2c",
  caveat @ "claim:the-full-limit-is-derived-from-the-exact-finite-telescope-and-the-proved-final-approximation-limit"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovFullLimit where
  promises "formalization:unconditional-full-constructed-rychkov-detail-series-limit"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.dualCalderonPartialDistribution_rychkov_eq_approximation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualApproximation_delta",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualCalderon_delta"
  ]
  forbids_substitutes [
    "assuming either the approximation limit or the full detail-series limit",
    "duplicating the repository's tempered-distribution embedding"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit.tendsto_rychkovDualCalderon_delta
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_cancellation_uniformSpatialSupport
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative.HasCancellationOrder,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport.rychkovSpatialCarrier
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_cancellation_uniformSpatialSupport
    where
  formalizes @ "claim:lemma4.2b-f-constructed-arbitrary-moment-cancellation-and-uniform-spatial-dilate",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2b-f",
  caveat @ "claim:paper-faithful-unscaled-normalization-is-proved-separately"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovCancellationSpatialDilate where
  promises "formalization:constructed-rychkov-arbitrary-cancellation-and-explicit-uniform-spatial-dilate"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovCancellation.rychkovDualDetail_hasCancellationOrder",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport.rychkovDualApproximation_tsupport_subset_spatialCarrier",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport.rychkovDualDetail_tsupport_subset_spatialCarrier",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_cancellation_uniformSpatialSupport"
  ]
  forbids_substitutes [
    "retaining moment cancellation as an external certificate field",
    "retaining qualitative compact support when a uniform dilate is required",
    "calling Fourier vanishing moment cancellation without proving the Fourier-derivative moment bridge"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_cancellation_uniformSpatialSupport
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_normalization_scaling
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.NormalizedRelative,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.unscaledDyadicFamily,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicDilation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualApproximation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual.rychkovDualDetail
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_normalization_scaling
    where
  formalizes @ "claim:lemma4.2a-paper-faithful-unscaled-dual-normalization-and-dyadic-scaling",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-lemma4.2a",
  caveat @ "claim:normalization-is-before-external-dilation-and-both-duals-use-the-approximation-family-as-reference"

zil_file_contract physlib.entropicSpine.multiNormSection4RychkovNormalization where
  promises "formalization:constructed-rychkov-paper-faithful-normalization-and-scaling"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicDilation_undilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.unscaled_complexDyadicApproximationKernel_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.unscaled_rychkovDualApproximation_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.unscaled_rychkovDualDetail_succ_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.rychkovDualApproximation_normalizedRelative",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.rychkovDualDetail_normalizedRelative",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDualCalderonFamily",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_normalization_scaling"
  ]
  forbids_substitutes [
    "comparing raw already-dilated kernels in Schwartz seminorms",
    "using the detail family instead of the approximation templates as the normalization reference",
    "retaining either normalization estimate as an external certificate premise"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates.constructedRychkovDual_normalization_scaling
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.existsUnique_paperTubeIndex
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.FullTubeIndex,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.paperTubeIndexSet
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.existsUnique_paperTubeIndex
    where
  formalizes @ "claim:proposition4.3-paper-index-set-L-partitions-the-full-natural-multi-index-lattice",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-proposition4.3",
  caveat @ "claim:this-is-the-index-partition-not-by-itself-convergence-of-the-tensor-series"

zil_file_contract physlib.entropicSpine.multiNormSection4PaperTubePartition where
  promises "formalization:exact-completed-maximal-tube-partition-of-full-tensor-indices"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.FullTubeIndex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.paperTubeIndexSet",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.existsUnique_paperTubeIndex"
  ]
  forbids_substitutes [
    "using an unrelated abstract partition instead of the Section 3 maximal tubes",
    "dropping the distinguished zero low block",
    "claiming a cover without uniqueness"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.existsUnique_paperTubeIndex
  ]

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.hasSum_paperGroupedDualDetailDistribution_delta
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.paperGroupedDualDetailDistribution,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.fullTensorDualDetailDistribution,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.hasSum_paperGroupedDualDetailDistribution_delta
    where
  formalizes @ "claim:proposition4.3-distributional-series-regrouping-by-the-paper-index-set-L",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-proposition4.3",
  requires @ "assumption:raw-full-index-tensor-series-has-dirac-as-unconditional-sum",
  caveat @ "claim:regrouping-is-proved-but-raw-tensor-series-convergence-remains-an-explicit-premise"

zil_file_contract physlib.entropicSpine.multiNormSection4DistributionRegrouping where
  promises "formalization:finite-fiber-tempered-distribution-regrouping-over-the-actual-paper-index"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.hasSum_regroup_by_finite_paperTubes",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.paperGroupedDualDetailDistribution",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.hasSum_paperGroupedDualDetailDistribution_delta"
  ]
  forbids_substitutes [
    "assuming the regrouped conclusion directly",
    "using completeness of tempered distributions that is not available",
    "claiming the raw tensor HasSum premise has been discharged"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping.hasSum_paperGroupedDualDetailDistribution_delta
  ]

#zil_formalization_lint_all

/- ZIL-END -/

end Physlib.Meta.MultiNormSection4PaperZil
