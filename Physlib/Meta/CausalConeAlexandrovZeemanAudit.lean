/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeAlexandrovZeeman
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Alexandrov–Zeeman converse

Gates the algebraic conclusion, the 3+1 same-null-cone metric-rigidity theorem, the
topological identification of the timelike cone as the interior of the causal cone, and
the null-incidence reconstruction of tangent hyperplanes, real affine-collineation
reconstruction, and post-collineation affine causal-automorphism classification.
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Physlib.Mathematics.AffineCollineation.exists_affineEquiv_of_affineLine_images,
  Lorentz.Vector.conformalLorentz_normalized_isLorentz,
  Lorentz.Vector.conformalLorentz_eq_smul_lorentz,
  Lorentz.Vector.conformalLorentz_toMatrix_mem_lorentzGroup,
  Lorentz.Vector.smul_lorentz_isConformalLorentz,
  Lorentz.Vector.translation_isCausalAutomorphism,
  Lorentz.Vector.causalDiamond_image_of_isCausalAutomorphism,
  Lorentz.Vector.nullSeparation_iff_of_causalAutomorphism,
  Lorentz.Vector.nullConeAt_image_of_causalAutomorphism,
  Lorentz.Vector.mem_nullOrthogonalHyperplane_iff_incidence,
  Lorentz.Vector.nullOrthogonalHyperplane_image_of_causalAutomorphism,
  Lorentz.Vector.same_null_cone_proportional,
  Lorentz.Vector.nullCone_preserving_linear_is_conformal,
  Lorentz.Vector.nullCone_preserving_linear_is_positive_conformal,
  Lorentz.Vector.nullCone_preserving_linear_eq_dilation_lorentz,
  Lorentz.Vector.affine_causal_null_preserver_eq_translation_dilation_lorentz,
  Lorentz.Vector.interior_futureCausalCone3_eq_futureTimelikeCone3,
  Lorentz.Vector.affine_causalAutomorphism_preserves_nullCone,
  Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz ]

#physlib_non_vacuous_all [
  Physlib.Mathematics.AffineCollineation.exists_affineEquiv_of_affineLine_images,
  Lorentz.Vector.conformalLorentz_normalized_isLorentz,
  Lorentz.Vector.conformalLorentz_eq_smul_lorentz,
  Lorentz.Vector.conformalLorentz_toMatrix_mem_lorentzGroup,
  Lorentz.Vector.smul_lorentz_isConformalLorentz,
  Lorentz.Vector.translation_isCausalAutomorphism,
  Lorentz.Vector.causalDiamond_image_of_isCausalAutomorphism,
  Lorentz.Vector.nullSeparation_iff_of_causalAutomorphism,
  Lorentz.Vector.nullConeAt_image_of_causalAutomorphism,
  Lorentz.Vector.mem_nullOrthogonalHyperplane_iff_incidence,
  Lorentz.Vector.nullOrthogonalHyperplane_image_of_causalAutomorphism,
  Lorentz.Vector.same_null_cone_proportional,
  Lorentz.Vector.nullCone_preserving_linear_is_conformal,
  Lorentz.Vector.nullCone_preserving_linear_is_positive_conformal,
  Lorentz.Vector.nullCone_preserving_linear_eq_dilation_lorentz,
  Lorentz.Vector.affine_causal_null_preserver_eq_translation_dilation_lorentz,
  Lorentz.Vector.interior_futureCausalCone3_eq_futureTimelikeCone3,
  Lorentz.Vector.affine_causalAutomorphism_preserves_nullCone,
  Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz ]
