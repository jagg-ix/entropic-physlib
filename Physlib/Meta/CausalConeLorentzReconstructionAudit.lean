/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLorentzReconstruction
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the causal-cone boost-invariance / Malament reconstruction

Gates the reverse Cauchy–Schwarz inequality, the orthochronous boost-invariance of the
interior future light cone, the full-Lorentz invariance of spacelike separation, and the
conformal-factor invariance of the causal character.
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Lorentz.Vector.minkowskiProduct_pos_of_futureTimelike,
  Lorentz.Vector.toVector_futureTimelike_of_orthochronous,
  Lorentz.Vector.interiorFutureLightCone_smul_of_orthochronous,
  Lorentz.Vector.interiorFutureLightCone_smul_iff_of_orthochronous,
  Lorentz.Vector.causallyUnrelated_smul,
  Lorentz.Vector.causalCharacterOfForm_smul_pos,
  Lorentz.Vector.conformalFactor_causalCharacter_invariant ]

#physlib_non_vacuous_all [
  Lorentz.Vector.minkowskiProduct_pos_of_futureTimelike,
  Lorentz.Vector.toVector_futureTimelike_of_orthochronous,
  Lorentz.Vector.interiorFutureLightCone_smul_of_orthochronous,
  Lorentz.Vector.interiorFutureLightCone_smul_iff_of_orthochronous,
  Lorentz.Vector.causallyUnrelated_smul,
  Lorentz.Vector.causalCharacterOfForm_smul_pos,
  Lorentz.Vector.conformalFactor_causalCharacter_invariant ]
