/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Liouville-complexity AdS/CFT arc synthesis
-/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis.adSPoincareSlice_liouville_derived_curvature,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis.liouville_arc_synthesis ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis.adSPoincareSlice_liouville_derived_curvature,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleAdSArcSynthesis.liouville_arc_synthesis ]
