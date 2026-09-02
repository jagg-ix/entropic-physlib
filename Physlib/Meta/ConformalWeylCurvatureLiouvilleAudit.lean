/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the conformal Weyl-curvature transform and Liouville EOM
-/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.christoffelConformal_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalRiemann_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalGaussCurvature_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.liouville_eom_iff_constant_curvature,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_solves_liouville,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_gaussCurvature ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.christoffelConformal_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalRiemann_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.conformalGaussCurvature_eq,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.liouville_eom_iff_constant_curvature,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_solves_liouville,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalWeylCurvatureLiouville.poincareVacuum_gaussCurvature ]
