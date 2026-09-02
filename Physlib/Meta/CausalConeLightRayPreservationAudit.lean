/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLightRayPreservation
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of Zeeman light-ray preservation

Gates both null-cone definitions, the chain/non-chain geometry of null/timelike
Alexandrov intervals, and light-ray preservation under bare causal automorphisms.
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Lorentz.Vector.futureLightConeBoundary_iff,
  Lorentz.Vector.causalDiamond_isChain_of_futureNull,
  Lorentz.Vector.causalDiamond_not_isChain_of_futureTimelike,
  Lorentz.Vector.futureLightConeBoundary_iff_causalDiamond_isChain,
  Lorentz.Vector.interiorFutureLightCone_iff_causalDiamond_not_isChain,
  Lorentz.Vector.causalDiamondIsChain_iff_of_causalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism,
  Lorentz.Vector.interiorFutureLightCone_mem_iff_of_causalAutomorphism,
  Lorentz.Vector.isOpen_interiorFutureLightCone3,
  Lorentz.Vector.isOpen_chronologicalDiamond3,
  Lorentz.Vector.chronologicalDiamond3_image_of_causalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_image_of_causalAutomorphism,
  Lorentz.Vector.futureNullRay_image_of_causalAutomorphism,
  Lorentz.Vector.nullAffineLine_image_of_causalAutomorphism,
  Lorentz.Vector.IsCausalAutomorphism.toChronoCausalAutomorphism,
  Lorentz.Vector.translation_isChronoCausalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_mem_iff_of_chronoCausalAut,
  Lorentz.Vector.futureLightConeBoundary_image_of_chronoCausalAut ]

#physlib_non_vacuous_all [
  Lorentz.Vector.futureLightConeBoundary_iff,
  Lorentz.Vector.causalDiamond_isChain_of_futureNull,
  Lorentz.Vector.causalDiamond_not_isChain_of_futureTimelike,
  Lorentz.Vector.futureLightConeBoundary_iff_causalDiamond_isChain,
  Lorentz.Vector.interiorFutureLightCone_iff_causalDiamond_not_isChain,
  Lorentz.Vector.causalDiamondIsChain_iff_of_causalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism,
  Lorentz.Vector.interiorFutureLightCone_mem_iff_of_causalAutomorphism,
  Lorentz.Vector.isOpen_interiorFutureLightCone3,
  Lorentz.Vector.isOpen_chronologicalDiamond3,
  Lorentz.Vector.chronologicalDiamond3_image_of_causalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_image_of_causalAutomorphism,
  Lorentz.Vector.futureNullRay_image_of_causalAutomorphism,
  Lorentz.Vector.nullAffineLine_image_of_causalAutomorphism,
  Lorentz.Vector.IsCausalAutomorphism.toChronoCausalAutomorphism,
  Lorentz.Vector.translation_isChronoCausalAutomorphism,
  Lorentz.Vector.futureLightConeBoundary_mem_iff_of_chronoCausalAut,
  Lorentz.Vector.futureLightConeBoundary_image_of_chronoCausalAut ]
