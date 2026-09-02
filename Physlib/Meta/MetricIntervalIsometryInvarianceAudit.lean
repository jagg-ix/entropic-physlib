/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the metric-interval isometry invariance
-/

open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance

#physlib_axiom_clean_all [
  metricInterval_isometry_invariant,
  metricInterval_smul,
  weylRescale_connection_invariant_interval_scales,
  dilationGroup_apply,
  dilationMatrix_one,
  dilationMatrix_mul,
  dilationMatrix_mul_inv,
  dilationMatrix_mulVec,
  dilationGroup_apply_eq_dilationMatrix_mulVec,
  metricInterval_dilation,
  dilationMatrix_conformal,
  metricInterval_compensated_dilation,
  dilationWeyl_connection_invariant_interval_invariant ]

#physlib_non_vacuous_all [
  metricInterval_isometry_invariant,
  metricInterval_smul,
  weylRescale_connection_invariant_interval_scales,
  dilationMatrix_mul,
  dilationMatrix_mul_inv,
  dilationMatrix_mulVec,
  dilationGroup_apply_eq_dilationMatrix_mulVec,
  metricInterval_dilation,
  dilationMatrix_conformal,
  metricInterval_compensated_dilation,
  dilationWeyl_connection_invariant_interval_invariant ]
