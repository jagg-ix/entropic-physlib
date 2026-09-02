/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysicalData
public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-!
# Dirac mass-shell projection of the Compton physical instance

The one-mode Compton state carrier is not itself the four-spinor
Dirac carrier.  This leaf bridge exposes the already-proved theorem that the
same supplied Yukawa/Compton mass appears in the actual four-spinor Dirac
Hamiltonian.  It therefore connects the Compton clock to the
existing spinor mass shell without identifying the two state spaces.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical

open Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-- The Yukawa mass attached to the Compton clock is the mass term of the
existing four-spinor Dirac Hamiltonian and obeys its exact mass shell. -/
@[zil_level physical_theorem]
theorem diracHamiltonian4_sq_at_comptonOmega
    (D : ComptonPhysicalData) (p1 p2 p3 : ℝ) :
    diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
        * diracHamiltonian4 p1 p2 p3 (yukawaMass D.y D.v)
      = ((p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (yukawaMass D.y D.v) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  diracHamiltonian4_sq_yukawaClock D.yukawaClockData p1 p2 p3

/-- The Yukawa coupling is isolated by the same Compton frequency used by the
Compton state phase. -/
@[zil_level bridge_theorem]
theorem isolatedYukawa_at_comptonOmega (D : ComptonPhysicalData) :
    D.y = Real.sqrt 2 * D.hbar * D.omegaC / (D.c ^ 2 * D.v) :=
  isolated_yukawa_from_compton_clock D.yukawaClockData

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical

zil attach diracHamiltonian4_sq_at_comptonOmega where
  formalizes @ "claim:the-compton-clock-yukawa-mass-is-the-mass-term-of-the-four-spinor-dirac-hamiltonian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.diracHamiltonian4_sq_yukawaClock",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-one-mode-l2-state-space-is-not-identified-with-the-four-spinor-dirac-space"

zil attach isolatedYukawa_at_comptonOmega where
  formalizes @ "claim:the-compton-clock-frequency-isolates-the-yukawa-coupling-at-the-supplied-mediator-vev",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.isolated_yukawa_from_compton_clock",
  epistemic_status @ "conditional-model",
  caveat @ "claim:this-is-an-isolation-identity-not-a-numerical-prediction-of-the-coupling"

/- ZIL-END -/
