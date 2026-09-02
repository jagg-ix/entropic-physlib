/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of SchwarzschildDeSitterNariai -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.kottlerHorizonPoly_criticalPoint,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.kottlerHorizonPoly_nariai_value,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariai_double_root ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.kottlerHorizonPoly_criticalPoint,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.kottlerHorizonPoly_nariai_value,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariai_double_root ]
