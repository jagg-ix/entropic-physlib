/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.RelativisticScreenKinematics
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the relativistic screen kinematics -/

open Physlib.Thermodynamics.RelativisticScreenKinematics

#physlib_axiom_clean_all [
  Physlib.Thermodynamics.RelativisticScreenKinematics.redshiftScreenTemperature_eq,
  Physlib.Thermodynamics.RelativisticScreenKinematics.stationaryFourVelocity_unit_timelike,
  Physlib.Thermodynamics.RelativisticScreenKinematics.properAcceleration_eq,
  Physlib.Thermodynamics.RelativisticScreenKinematics.redshiftScreenTemperature_eq_redshifted_unruh ]

#physlib_non_vacuous_all [
  Physlib.Thermodynamics.RelativisticScreenKinematics.redshiftScreenTemperature_eq,
  Physlib.Thermodynamics.RelativisticScreenKinematics.stationaryFourVelocity_unit_timelike,
  Physlib.Thermodynamics.RelativisticScreenKinematics.properAcceleration_eq,
  Physlib.Thermodynamics.RelativisticScreenKinematics.redshiftScreenTemperature_eq_redshifted_unruh ]
