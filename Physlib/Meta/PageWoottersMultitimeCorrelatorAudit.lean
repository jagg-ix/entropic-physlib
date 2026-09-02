/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWoottersMultitimeCorrelator
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Page–Wootters two-time correlator

Gates the difference-form correlator, its coincidence limit, stationary magnitude,
time-translation invariance, and the tie to the carrier's Schrödinger phase field.
-/

open Physlib.Thermodynamics.Landauer.PageWoottersBipartite

#physlib_axiom_clean_all [
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.evolvedPhase_at_carrier_time,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_eq_phase_diff,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_coincidence,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_norm,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_time_translation_invariant,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_depends_on_difference ]

#physlib_non_vacuous_all [
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.evolvedPhase_at_carrier_time,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_eq_phase_diff,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_coincidence,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_norm,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_time_translation_invariant,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator_depends_on_difference ]
