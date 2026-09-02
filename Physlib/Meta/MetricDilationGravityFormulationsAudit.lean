/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of dilation transport across gravity formulations
-/

open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations

#physlib_axiom_clean_all [
  tetradMetric_smul,
  properSeparationSq_eq_metricInterval,
  tetradDilationWeyl_properSeparation_invariant,
  axialCurrentNormSq_eq_metricInterval_one,
  hehlDattaContactDensity_dilation,
  cartanResidual_compensated_dilation,
  hehlDattaContactDensity_compensated_dilation_invariant,
  dadhichPons_projective_dilationWeyl_invariant,
  torsion_entropicConnection,
  projectiveConnection_injective,
  projectiveCovector_recovered_from_torsion_trace,
  entropicConnection_projective_torsion_trace,
  entropicConnection_projective_torsionTrace_zero_iff,
  dadhichPons_traceGauge_unique_representative,
  metricTrace_smul_left,
  traceReversedWithDenominator_constWeyl,
  constWeyl_inverseMetric_mul_metric,
  traceReversedMatter_constWeyl,
  matterAffineTensor_constWeyl,
  eddingtonMatterAffine_dilationWeyl_invariant,
  eddingtonFirstIntegral_constWeyl_covariant,
  lovelockTraceReversedMatter_constWeyl,
  lovelockAffineTensor_constWeyl,
  lovelockMatterAffine_dilationWeyl_invariant,
  lovelockFirstIntegral_constWeyl_covariant,
  eddingtonFirstIntegral_constWeyl_derives_einsteinLambda,
  metricTrace_constWeyl,
  lovelockFirstIntegral_constWeyl_derives_fieldEquation ]

#physlib_non_vacuous_all [
  tetradMetric_smul,
  tetradDilationWeyl_properSeparation_invariant,
  axialCurrentNormSq_eq_metricInterval_one,
  hehlDattaContactDensity_dilation,
  cartanResidual_compensated_dilation,
  hehlDattaContactDensity_compensated_dilation_invariant,
  dadhichPons_projective_dilationWeyl_invariant,
  torsion_entropicConnection,
  projectiveConnection_injective,
  projectiveCovector_recovered_from_torsion_trace,
  entropicConnection_projective_torsion_trace,
  entropicConnection_projective_torsionTrace_zero_iff,
  dadhichPons_traceGauge_unique_representative,
  metricTrace_smul_left,
  traceReversedWithDenominator_constWeyl,
  constWeyl_inverseMetric_mul_metric,
  traceReversedMatter_constWeyl,
  matterAffineTensor_constWeyl,
  eddingtonMatterAffine_dilationWeyl_invariant,
  eddingtonFirstIntegral_constWeyl_covariant,
  lovelockTraceReversedMatter_constWeyl,
  lovelockAffineTensor_constWeyl,
  lovelockMatterAffine_dilationWeyl_invariant,
  lovelockFirstIntegral_constWeyl_covariant,
  eddingtonFirstIntegral_constWeyl_derives_einsteinLambda,
  metricTrace_constWeyl,
  lovelockFirstIntegral_constWeyl_derives_fieldEquation ]
