/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysicalDataDirac
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Compton physical data and its identities

This leaf audit applies the repository axiom and non-vacuity gates to the
gravitational and Yukawa identities carried by `ComptonPhysicalData`: the
holographic area-per-bit Newton constant, the Verlinde/Newton force agreement,
the Einstein bit-form coupling, the Compton mass identity, Newton's second law
at the screen, and the four-spinor Dirac mass shell of the supplied Yukawa mass.
-/

#check @Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData
#check @Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.exampleComptonPhysicalData

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.screenRadius_pos,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.omegaC_pos,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.verlindeScreenForce_eq_newtonForceScale,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.einsteinCoupling_bitForm_at_comptonScreen,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.comptonMass_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.yukawaClock_restEnergy_at_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.yukawaComplexEnergy_im_at_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonG_holographic_area_per_bit,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonForce_at_screen,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonForce_at_screen_holographic_bitForm,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.diracHamiltonian4_sq_at_comptonOmega,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.isolatedYukawa_at_comptonOmega ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.verlindeScreenForce_eq_newtonForceScale,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.einsteinCoupling_bitForm_at_comptonScreen,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.comptonMass_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.yukawaClock_restEnergy_at_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.yukawaComplexEnergy_im_at_omegaC,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonG_holographic_area_per_bit,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonForce_at_screen,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonForce_at_screen_holographic_bitForm,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.diracHamiltonian4_sq_at_comptonOmega,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.isolatedYukawa_at_comptonOmega ]
