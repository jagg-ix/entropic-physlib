/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWoottersMultitimeCorrelator
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Page–Wootters Leggett–Garg violation
-/

open Physlib.Thermodynamics.Landauer.PageWoottersBipartite

#physlib_axiom_clean_all [
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgCorrelator_eq_re,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_equalSpacing,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.two_cos_sub_cos_two_le,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_le_luders,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_violation,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_exceeds_classical_bound ]

#physlib_non_vacuous_all [
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgCorrelator_eq_re,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_equalSpacing,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.two_cos_sub_cos_two_le,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_le_luders,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_violation,
  Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3_exceeds_classical_bound ]
