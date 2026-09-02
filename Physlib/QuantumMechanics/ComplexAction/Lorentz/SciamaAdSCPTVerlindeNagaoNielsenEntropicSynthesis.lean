/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermionMagneticInverseSquareComplexEFE
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-!
# The entropic sector: Verlinde (inverse-square) and Nagao–Nielsen (decoherence)

The complex EFE (`SciamaAdSCPTFermionMagneticInverseSquareComplexEFE`) splits the fermion's field into a
matter/real sector and an **entropic/imaginary sector** (`Λ = κS`).  Both of the entropic sector's faces are
already formalized in the repo, and this module ties the synthesis to them.

* **Verlinde — the inverse-square law is the entropic force.**  The `1/r²` field
  (`newtonAcceleration = GM/r²`) that §1 matched to the MIW interworld term is the **Verlinde entropic force**:
  `T·ΔS/Δx` on the holographic screen equals `GMm/R²` (`Thermodynamics.VerlindeNewtonGravity`,
  `newton_law_of_gravity_from_verlinde`).  So the fermion's inverse-square self-field is entropic
  (`inverse_square_is_verlinde_entropic_force`), and — via §1 — scales as the MIW coupling.

* **Nagao–Nielsen — the decoherence visibility is the complex-action modulus.**  The interference visibility
  `v = exp(−Γt)` (`SciamaAdSCPTTransportDecoherenceInterference`) that damps the Aharonov–Bohm magnetic fringe
  is *exactly* the modulus of the **Nagao–Nielsen complex-action weight** `exp((i/ℏ)(S_R + iS_I))`
  (`PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsenComplexActionWeight`): `‖·‖ = exp(−S_I/ℏ)`
  (`master_modulus_is_kuiken`), with the decoherence exponent identified as the imaginary action per `ℏ`,
  `Γt = S_I/ℏ` (`decoherence_visibility_is_nagaoNielsen_modulus`).

* **The synthesis** (`verlinde_nagaoNielsen_entropic_synthesis`): the complex EFE's entropic sector carries both —
  Verlinde's screen entropy produces the inverse-square/gravitoelectric force, and Nagao–Nielsen's imaginary
  action `S_I` produces the decoherence that damps the magnetic/gravitomagnetic interference.  The inverse-square
  law and the decoherence are the two readings of the one entropic (imaginary-action) sector.

Honest scope: two exact reuses — the Verlinde entropic force `= GM/r²·m` (`newton_law_of_gravity_from_verlinde`)
and the Nagao–Nielsen weight modulus `= exp(−S_I/ℏ)` (`master_modulus_is_kuiken`) — under the physical
identifications (`newtonAcceleration` is the entropic-force field; `S_I/ℏ` is the decoherence exponent `Γt`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTVerlindeNagaoNielsenEntropicSynthesis

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.Thermodynamics

/-! ## §1. Verlinde — the inverse-square law is the entropic force -/

/-- **[The fermion's inverse-square field is the Verlinde entropic force]** `T·ΔS/Δx = (GM/r²)·m`.  The
holographic-screen entropic force at the Verlinde temperature and displacement entropy equals the inverse-square
Newton/Coulomb field `newtonAcceleration = GM/R²` times the test mass — the field §1 matched to the MIW
interworld term.  So the inverse-square law is entropic (Verlinde 2011). -/
theorem inverse_square_is_verlinde_entropic_force {M G ℏ c R kB m Δx : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx) :
    verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx
      = newtonAcceleration G M R * m := by
  rw [newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx]
  unfold newtonAcceleration
  ring

/-! ## §2. Nagao–Nielsen — the decoherence visibility is the complex-action modulus -/

/-- **[The decoherence visibility is the Nagao–Nielsen complex-action modulus]** `‖e^{(i/ℏ)(S_R+iS_I)}‖ =
exp(−S_I/ℏ) = exp(−Γt) = v`.  The interference visibility that damps the Aharonov–Bohm magnetic fringe is the
modulus of the Nagao–Nielsen complex-action weight, with the transport decoherence exponent `Γt` identified as
the imaginary action per `ℏ`, `S_I/ℏ = Γt`: decoherence is the imaginary-action (entropy-production) sector. -/
theorem decoherence_visibility_is_nagaoNielsen_modulus {prefactor t S_R S_I ℏ : ℝ} (X : NobleMetal)
    (hℏ : ℏ ≠ 0) (hSI : S_I / ℏ = sdScatteringRate prefactor X * t) :
    ‖nagaoNielsenComplexActionWeight S_R S_I ℏ‖ = interferenceVisibility prefactor t X := by
  rw [nagaoNielsen_eq_master S_R S_I ℏ hℏ, master_modulus_is_kuiken]
  unfold kuikenWeight interferenceVisibility
  rw [hSI]

/-! ## §3. The synthesis — one entropic sector, two faces -/

/-- **[Verlinde and Nagao–Nielsen are the two faces of the complex EFE's entropic sector]** — the screen entropy
gives the inverse-square/gravitoelectric force (`inverse_square_is_verlinde_entropic_force`), and the imaginary
action gives the decoherence that damps the magnetic/gravitomagnetic interference
(`decoherence_visibility_is_nagaoNielsen_modulus`).  The inverse-square law and the decoherence are two readings
of the one entropic (imaginary-action) sector of the complex EFE sourced by the fermion. -/
theorem verlinde_nagaoNielsen_entropic_synthesis {M G ℏ c R kB m Δx prefactor t S_R S_I : ℝ} (X : NobleMetal)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx)
    (hSI : S_I / ℏ = sdScatteringRate prefactor X * t) :
    verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = newtonAcceleration G M R * m
      ∧ ‖nagaoNielsenComplexActionWeight S_R S_I ℏ‖ = interferenceVisibility prefactor t X :=
  ⟨inverse_square_is_verlinde_entropic_force hℏ hkB hc hR hΔx,
    decoherence_visibility_is_nagaoNielsen_modulus X hℏ.ne' hSI⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTVerlindeNagaoNielsenEntropicSynthesis

end
