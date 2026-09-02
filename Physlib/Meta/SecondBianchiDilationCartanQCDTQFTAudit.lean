/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the second-Bianchi dilation/Cartan/QCD/TQFT bridge
-/

open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiDilationCartanQCDTQFT
open Physlib.Mathematics.LovelockRund

#physlib_axiom_clean_all [
  continuumWedgeAt_apply,
  continuumWedgeAt_add_left,
  continuumWedgeAt_smul_left,
  continuumWedgeAt_add_right,
  continuumWedgeAt_smul_right,
  continuumWedgeAt_compContinuousLinearMap,
  continuumWedgeAt_two_comm,
  continuumWedgeBilinear_apply,
  continuumWedge_smul_smul,
  continuumWedge_two_comm,
  pullbackForm_continuumWedge,
  dilateBianchiTensor_one,
  dilateBianchiTensor_mul,
  dilateBianchiTensor_inv_apply,
  secondBianchi_dilation_iff,
  dilateDifferentialForm_one,
  dilateDifferentialForm_mul,
  dilateDifferentialForm_inv_apply,
  greenSchwarzTensorFieldStrength_dilation,
  greenSchwarz_modifiedBianchi_dilation,
  stringScale_dilationGroup,
  secondBianchi_greenSchwarz_dilation,
  quadraticPontryagin_dilation,
  continuumPontryagin_eq_quadraticPontryagin,
  continuumPontryagin_dilation,
  continuumPontryagin_add,
  pullbackForm_continuumPontryagin,
  greenSchwarz_quadraticPontryagin_dilation,
  greenSchwarz_continuumPontryagin_dilation,
  secondBianchi_greenSchwarz_quadraticPontryagin_dilation,
  secondBianchi_greenSchwarz_continuumPontryagin_dilation,
  secondBianchi_greenSchwarz_dilation_conservation,
  secondBianchi_dilation_einsteinCartan,
  qcd_bcj_secondBianchi_conservation,
  secondBianchi_cartan_qcd_tqft_faces ]

#physlib_non_vacuous_all [
  continuumWedgeAt_apply,
  continuumWedgeAt_add_left,
  continuumWedgeAt_smul_left,
  continuumWedgeAt_add_right,
  continuumWedgeAt_smul_right,
  continuumWedgeAt_compContinuousLinearMap,
  continuumWedgeAt_two_comm,
  continuumWedge_smul_smul,
  continuumWedge_two_comm,
  pullbackForm_continuumWedge,
  dilateBianchiTensor_mul,
  dilateBianchiTensor_inv_apply,
  secondBianchi_dilation_iff,
  dilateDifferentialForm_mul,
  dilateDifferentialForm_inv_apply,
  greenSchwarzTensorFieldStrength_dilation,
  greenSchwarz_modifiedBianchi_dilation,
  stringScale_dilationGroup,
  secondBianchi_greenSchwarz_dilation,
  quadraticPontryagin_dilation,
  continuumPontryagin_dilation,
  continuumPontryagin_add,
  greenSchwarz_quadraticPontryagin_dilation,
  greenSchwarz_continuumPontryagin_dilation,
  secondBianchi_greenSchwarz_quadraticPontryagin_dilation,
  secondBianchi_greenSchwarz_continuumPontryagin_dilation,
  secondBianchi_greenSchwarz_dilation_conservation,
  secondBianchi_dilation_einsteinCartan,
  qcd_bcj_secondBianchi_conservation,
  secondBianchi_cartan_qcd_tqft_faces ]
