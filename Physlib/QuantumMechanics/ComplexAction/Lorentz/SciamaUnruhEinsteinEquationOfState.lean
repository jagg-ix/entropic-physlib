/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein

/-!
# Einstein's equation from the microscopic Unruh state: closing the entropic-gravity chain

Jacobson's derivation of the Einstein field equation from the Clausius relation
(`ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius`) takes the **Unruh temperature**
`T_U = κ/2π` as a phenomenological input (`hUnruh`).  This module grounds that input in the *microscopic*
quantum state: the Unruh temperature `T_U = α/2π` is the **KMS temperature of the accelerated-detector power
spectrum** `SciamaUnruhPowerSpectrum.unruhPowerSpectrum` — the thermal spectrum whose detailed balance
`Π(ω)/Π(−ω) = e^{−2πω/α}` (`unruhPowerSpectrum_detailedBalance`) is precisely `e^{−ω/T_U}`.

* `sciamaUnruhTemperature` — `T_U = α/2π`, the KMS temperature of the Unruh detector spectrum.
* `sciamaUnruh_detailedBalance_kms` — the Unruh spectrum's detailed balance is `Π(ω)/Π(−ω) = e^{−ω/T_U}`: the
  microscopic accelerated-detector state *is* thermal at `T_U`, so `T_U` is not a postulate but the
  temperature of a quantum state.
* `einstein_from_sciamaUnruh` — **the Einstein field equation from the microscopic Unruh state**: feeding the
  Sciama Unruh temperature into Jacobson's Clausius chain, the all-null-direction Clausius balance at
  `T_U = sciamaUnruhTemperature κ` outputs `G_{ab} + Λ g_{ab} = 8πG T_{ab}` with `κ = 8πG` derived.

This closes the entropic-gravity program's chain end-to-end: the accelerated-detector thermal spectrum (a
quantum-field state) fixes the Unruh temperature, which — through horizon area-entropy and the Clausius
relation — outputs Einstein's equation.  Spacetime dynamics from the temperature of a quantum thermal state.

Honest scope: the identification of Jacobson's `T_U` with the Unruh-spectrum KMS temperature and the resulting
EFE output.  The Clausius balance itself (area-entropy + heat flux) is the labeled input carried by
`JacobsonClausiusEinstein`; here it is closed with the *microscopically-grounded* temperature.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhEinsteinEquationOfState

open Matrix minkowskiMatrix
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-- **The Unruh (KMS) temperature** `T_U = α/2π` of the accelerated-detector power spectrum. -/
def sciamaUnruhTemperature (α : ℝ) : ℝ := α / (2 * Real.pi)

/-- **[Unruh spectrum is KMS-thermal] `Π(ω)/Π(−ω) = e^{−ω/T_U}`.**  The accelerated-detector power spectrum
obeys detailed balance at the Unruh temperature `T_U = α/2π`, so `T_U` is the temperature of a genuine quantum
thermal state — not a postulate. -/
theorem sciamaUnruh_detailedBalance_kms (α ω : ℝ) (hα : 0 < α) (hω : ω ≠ 0) :
    unruhPowerSpectrum α ω / unruhPowerSpectrum α (-ω)
      = Real.exp (-(ω / sciamaUnruhTemperature α)) := by
  have hα' : α ≠ 0 := hα.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [unruhPowerSpectrum_detailedBalance α ω hα hω, sciamaUnruhTemperature]
  congr 1
  field_simp

/-- **[Einstein's equation from the microscopic Unruh state]** the Clausius balance at the Unruh-spectrum KMS
temperature `T_U = sciamaUnruhTemperature κ` outputs the Einstein field equation `G_{ab} + Λ g_{ab} = 8πG
T_{ab}`.  The Unruh temperature is the KMS temperature of the accelerated-detector spectrum
(`sciamaUnruh_detailedBalance_kms`), so this is spacetime dynamics from the temperature of a quantum thermal
state — the entropic-gravity chain closed end-to-end. -/
theorem einstein_from_sciamaUnruh {d : ℕ}
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (G κb : ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm) (hG : G ≠ 0) (hκb : κb ≠ 0)
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      κb * (k ⬝ᵥ (T *ᵥ k)) = sciamaUnruhTemperature κb * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G))) :
    ∃ Λ : ℝ, einsteinFieldEquationCosmological Ric (Matrix.trace (η * Ric)) η T Λ
      (8 * Real.pi * G) :=
  einstein_from_clausius Ric T G κb (sciamaUnruhTemperature κb) hRic hT hG hκb
    (by rw [sciamaUnruhTemperature]) hClausius

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhEinsteinEquationOfState

end
