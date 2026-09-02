/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of AffineProjectionTensorGeometry -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.mul_complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.complement_mul,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.transpose,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.mulVec_fixed ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.mul_complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.complement_mul,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.transpose,
  Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry.IsProjectionTensor.mulVec_fixed ]
