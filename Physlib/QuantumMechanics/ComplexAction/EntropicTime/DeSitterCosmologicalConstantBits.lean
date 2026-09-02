/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
public import Physlib.Cosmology.FLRW.MatterContent
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.Cosmology.FLRW.HorizonEntropyExpansion
meta import Zil

/-!
# The cosmological constant is the reciprocal of the de Sitter horizon bit count

The de Sitter horizon closes the arc. A cosmological constant `Λ > 0` gives a de Sitter horizon of
areal radius `L` with `L² = 3/Λ` (4-dimensional de Sitter, `Λ = 3/L²`), hence horizon area
`A = 4πL² = 12π/Λ`. The holographic bit count of that horizon is
`N = holographicBits A G ℏ c = A c³/(Gℏ) = 12π c³/(GℏΛ)`, and inverting gives the **cosmological
constant in bit form**

  `Λ = 12π c³/(ℏ G N) = 12π/(ℓ_P² N)`   (`ℓ_P² = Gℏ/c³`):

**dark energy is the reciprocal of the number of horizon bits.** The observed smallness of `Λ` is the
observed largeness of the de Sitter bit count. The de Sitter horizon's Bekenstein–Hawking entropy is
`S_dS = ℏ N/4` (`horizon_imaginaryAction_eq_quarter_bits`), its Nagao–Nielsen contour / decoherence
factor is `e^{−N/4}` (`horizon_nnContour_bitCount`), and the vacuum energy density
`ρ_Λ = Λc²/(8πG)` (`Cosmology.FLRW.MatterContent.vacuumEnergyDensity`) is `3c⁵/(2 G² ℏ N)`.

The same bit count `N` that set the Einstein coupling `κ = 8π(A/N)/(ℏc)`, the universal free-fall
acceleration, and the horizon decoherence now sets the cosmological constant — the entropic (imaginary)
curvature `Λ = κS` of `HorizonNagaoContourBitEinstein.entropic_einstein_bitForm` acquires a value.

* **§A** the de Sitter horizon area `A = 12π/Λ`.
* **§B** the cosmological constant in bit form `Λ = 12π c³/(ℏ G N)`.
* **§C** the de Sitter entropy `S_dS = ℏ N/4` and its decoherence factor `e^{−N/4}`.
* **§D** the vacuum energy density in bit form `ρ_Λ = 3c⁵/(2 G² ℏ N)`.
* **§E** dark energy from the bit count: the four faces together.

## References

* G. W. Gibbons, S. W. Hawking, Phys. Rev. D 15 (1977) 2738 — de Sitter horizon entropy `S = A/(4ℓ_P²)`.
* E. Verlinde, JHEP 04 (2011) 029; T. Padmanabhan — the holographic/emergent reading of `Λ`.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Cosmology.FLRW.MatterContent
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits

@[expose] public section

/-! ## A. The de Sitter horizon area -/

/-- **The de Sitter horizon area** `A = 4πL² = 12π/Λ`, the area of the 2-sphere at the de Sitter
radius `L` with `L² = 3/Λ` (`Λ = 3/L²`). -/
noncomputable def deSitterHorizonArea (Λ : ℝ) : ℝ := 4 * Real.pi * (3 / Λ)

/-- **[The de Sitter horizon area]** `A = 12π/Λ`. -/
lemma deSitterHorizonArea_eq (Λ : ℝ) : deSitterHorizonArea Λ = 12 * Real.pi / Λ := by
  unfold deSitterHorizonArea; ring

/-! ## B. The cosmological constant in bit form -/

/-- **[The cosmological constant is the reciprocal of the horizon bit count]**
`Λ = 12π c³/(ℏ G N)`. If `N` is *defined from the same* de Sitter horizon of cosmological constant `Λ`,
this is the algebraic inverse of that bit-count formula, not an independent prediction of `Λ`. It becomes
empirically restrictive only if `N` is supplied by an independent microscopic count. -/
theorem cosmologicalConstant_bitForm (Λ G ℏ c N : ℝ)
    (hΛ : Λ ≠ 0) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0)
    (hbits : N = holographicBits (deSitterHorizonArea Λ) G ℏ c) :
    Λ = 12 * Real.pi * c ^ 3 / (ℏ * G * N) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hbits]
  unfold holographicBits deSitterHorizonArea
  field_simp
  ring

/-! ## C. The de Sitter entropy and its decoherence factor -/

/-- **[The de Sitter horizon entropy is a quarter of the bit count]** `S_dS = ℏ N/4`. The
Bekenstein–Hawking entropy of the cosmological horizon is a quarter of the de Sitter bit count, the
imaginary action of its Nagao–Nielsen contour. -/
theorem deSitter_entropy_eq_quarter_bits (Λ G ℏ c N : ℝ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0)
    (hbits : N = holographicBits (deSitterHorizonArea Λ) G ℏ c) :
    horizonImaginaryAction G c (deSitterHorizonArea Λ) = ℏ * N / 4 := by
  rw [horizon_imaginaryAction_eq_quarter_bits G c (deSitterHorizonArea Λ) ℏ hG hℏ, ← hbits]

/-- **[The de Sitter horizon decoherence factor is `e^{−N/4}`]** the Nagao–Nielsen contour modulus of
the cosmological horizon is `e^{−N/4} = e^{−S_dS}`. A small `Λ` means a large `N`, so `e^{−N/4} → 0`:
the de Sitter universe is maximally decohered — classical. -/
theorem deSitter_decoherence_bitCount (S_R Λ G ℏ c N : ℝ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0)
    (hbits : N = holographicBits (deSitterHorizonArea Λ) G ℏ c) :
    ‖nnPathWeight S_R (horizonImaginaryAction G c (deSitterHorizonArea Λ)) ℏ‖
      = Real.exp (-(N / 4)) := by
  rw [horizon_nnContour_bitCount S_R G c (deSitterHorizonArea Λ) ℏ hG hℏ, ← hbits]

/-! ## D. The vacuum energy density in bit form -/

/-- **[The vacuum energy density in bit form]** `ρ_Λ = Λc²/(8πG) = 3c⁵/(2 G² ℏ N)`. Feeding the
bit-form cosmological constant into the vacuum energy density
`Cosmology.FLRW.MatterContent.vacuumEnergyDensity` gives the dark-energy density as an inverse bit
count, weighted by the squared Newton constant. -/
theorem vacuumEnergyDensity_bitForm (Λ G ℏ c N : ℝ)
    (hΛbit : Λ = 12 * Real.pi * c ^ 3 / (ℏ * G * N)) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hN : N ≠ 0) :
    vacuumEnergyDensity Λ G c = 3 * c ^ 5 / (2 * G ^ 2 * ℏ * N) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold vacuumEnergyDensity
  rw [hΛbit]
  field_simp
  ring

/-! ## E. Dark energy from the bit count -/

/-- **[Dark energy from the de Sitter bit count]** from the single identification
`N = holographicBits (deSitterHorizonArea Λ) G ℏ c`, the one cosmological-horizon bit count `N` fixes:
the **cosmological constant** `Λ = 12π c³/(ℏ G N)`; the **horizon entropy** `S_dS = ℏ N/4`; the
**decoherence** factor `e^{−N/4}`; and the **vacuum energy density** `ρ_Λ = 3c⁵/(2 G² ℏ N)`. Dark
energy, horizon entropy, and cosmic decoherence are three readings of one bit count — the same `N`
that carries the free-fall acceleration and the Einstein coupling of this arc. -/
theorem deSitter_darkEnergy_bitCount (S_R Λ G ℏ c N : ℝ)
    (hΛ : Λ ≠ 0) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hN : N ≠ 0)
    (hbits : N = holographicBits (deSitterHorizonArea Λ) G ℏ c) :
    Λ = 12 * Real.pi * c ^ 3 / (ℏ * G * N)
    ∧ horizonImaginaryAction G c (deSitterHorizonArea Λ) = ℏ * N / 4
    ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (deSitterHorizonArea Λ)) ℏ‖ = Real.exp (-(N / 4))
    ∧ vacuumEnergyDensity Λ G c = 3 * c ^ 5 / (2 * G ^ 2 * ℏ * N) :=
  have hΛbit := cosmologicalConstant_bitForm Λ G ℏ c N hΛ hG hℏ hc hbits
  ⟨hΛbit,
    deSitter_entropy_eq_quarter_bits Λ G ℏ c N hG hℏ hbits,
    deSitter_decoherence_bitCount S_R Λ G ℏ c N hG hℏ hbits,
    vacuumEnergyDensity_bitForm Λ G ℏ c N hΛbit hG hℏ hN⟩

end

@[expose] public section

/-! ## F. The Gibbons–Hawking temperature closes the Λ-ledger loop -/

/-- **The de Sitter horizon radius** `r_dS = √(3/Λ)`. -/
noncomputable def deSitterRadius (Λ : ℝ) : ℝ := Real.sqrt (3 / Λ)

/-- `r_dS² = 3/Λ` for `Λ > 0`. -/
lemma deSitterRadius_sq {Λ : ℝ} (hΛ : 0 < Λ) : (deSitterRadius Λ) ^ 2 = 3 / Λ := by
  unfold deSitterRadius
  exact Real.sq_sqrt (by positivity)

/-- `r_dS > 0` for `Λ > 0`. -/
lemma deSitterRadius_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < deSitterRadius Λ := by
  unfold deSitterRadius
  positivity

/-- **[The de Sitter horizon is the Verlinde sphere at the de Sitter radius]**
`A_dS = sphereArea r_dS`: the cosmological-horizon area of the ledger is exactly the Verlinde
holographic-screen sphere at `r_dS = √(3/Λ)` — the same `sphereArea` carrier as the equipartition
screens of `VerlindeNewtonGravity`. -/
lemma deSitterHorizonArea_eq_sphereArea {Λ : ℝ} (hΛ : 0 < Λ) :
    deSitterHorizonArea Λ = sphereArea (deSitterRadius Λ) := by
  unfold deSitterHorizonArea sphereArea
  rw [deSitterRadius_sq hΛ]

/-- **[The Gibbons–Hawking temperature is the KMS temperature at the horizon surface gravity]**
`T_GH(H = c/r_dS) = k_B·T_KMS(κ = c²/r_dS)`. The nat-counted Gibbons–Hawking temperature of the
comoving observer (`gibbonsHawkingTemperature`, the FLRW Clausius carrier) is the Boltzmann-scaled
Kay–Wald KMS temperature at the de Sitter surface gravity — the cosmological horizon sits on the
same temperature carrier as the black-hole horizon (`verlindeTemperature_at_horizon_is_hawking`)
and the modular flow (`ModularErasureCost`). -/
theorem gibbonsHawking_is_kms_at_deSitter {ℏ c kB r : ℝ} (hc : c ≠ 0) (hkB : kB ≠ 0) :
    Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature ℏ (c / r)
      = kB * Physlib.Relativity.SemiClassical.hawkingTemperature ℏ (c ^ 2 / r) c kB := by
  unfold Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature
    Physlib.Relativity.SemiClassical.hawkingTemperature
  field_simp

/-- **[The de Sitter Smarr relation in bit form]** `T_KMS(κ_dS)·(k_B·N/4) = c⁴·r_dS/(2G)`. The
KMS temperature at the de Sitter surface gravity times the ledger entropy — a quarter of the
holographic bit count of `deSitter_darkEnergy_bitCount`, in Boltzmann units — is the Misner–Sharp
energy of the cosmological horizon, `E = c⁴r/(2G)`: the same `T·S`-form as the Schwarzschild
`hawking_bekensteinTauEnt_smarr`, closing the Λ-ledger loop. The single bit count `N` that fixes
dark energy (`Λ = 12πc³/(ℏGN)`) also prices the horizon energy. -/
theorem deSitter_smarr_bitCount {Λ G ℏ c kB N : ℝ}
    (hΛ : 0 < Λ) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0)
    (hbits : N = holographicBits (deSitterHorizonArea Λ) G ℏ c) :
    Physlib.Relativity.SemiClassical.hawkingTemperature ℏ (c ^ 2 / deSitterRadius Λ) c kB
        * (kB * N / 4)
      = c ^ 4 * deSitterRadius Λ / (2 * G) := by
  have hr2 := deSitterRadius_sq hΛ
  have hr : deSitterRadius Λ ≠ 0 := (deSitterRadius_pos hΛ).ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hbits, Physlib.Relativity.SemiClassical.hawkingTemperature_def]
  unfold holographicBits deSitterHorizonArea
  have key : Λ * deSitterRadius Λ * deSitterRadius Λ = 3 := by
    have h := hr2
    rw [pow_two] at h
    field_simp at h ⊢
    linarith [h]
  field_simp
  nlinarith [key, sq_nonneg (deSitterRadius Λ), Real.pi_pos]

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach deSitterHorizonArea_eq_sphereArea where
  formalizes @ "claim:de-sitter-horizon-is-verlinde-sphere-at-de-sitter-radius",
  supported_by @ "paper:verlinde-2010-emergent-gravity"

zil_theorem_intent gibbonsHawking_is_kms_at_deSitter where
  at_level bridge_theorem
  must_mention [Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature,
    Physlib.Relativity.SemiClassical.hawkingTemperature]

zil attach gibbonsHawking_is_kms_at_deSitter where
  formalizes @ "claim:gibbons-hawking-temperature-is-kms-temperature-at-horizon-surface-gravity",
  supported_by @ "paper:gibbons-hawking-1977",
  supported_by @ "paper:kay-wald-1991-horizon-kms",
  caveat @ "claim:nat-counted-versus-boltzmann-scaled-carrier-weld"

zil_theorem_intent deSitter_smarr_bitCount where
  at_level bridge_theorem
  must_mention [Physlib.Relativity.SemiClassical.hawkingTemperature, holographicBits]

zil attach deSitter_smarr_bitCount where
  formalizes @ "claim:de-sitter-smarr-kms-temperature-times-quarter-bits-is-misner-sharp-energy",
  requires @ "claim:gibbons-hawking-temperature-is-kms-temperature-at-horizon-surface-gravity",
  supported_by @ "paper:gibbons-hawking-1977",
  supported_by @ "paper:smarr-1973",
  caveat @ "claim:static-identity-lambda-taken-from-ledger-not-derived"

zil_file_contract physlib.deSitterCosmologicalConstantBits where
  promises "The de Sitter horizon closes the Lambda-ledger loop on existing carriers: the cosmological constant in bit form with the horizon bit count fixing dark energy, the horizon entropy as a quarter of the bit count, the decoherence factor, the vacuum energy density, the horizon area as the Verlinde sphere at the de Sitter radius, the Gibbons-Hawking temperature identified with the Kay-Wald KMS temperature at the de Sitter surface gravity, and the de Sitter Smarr relation with the KMS temperature times the quarter-bit entropy equal to the Misner-Sharp horizon energy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.holographicBits",
    "lean:Physlib.Thermodynamics.sphereArea",
    "lean:Physlib.Relativity.SemiClassical.hawkingTemperature",
    "lean:Cosmology.FLRW.HorizonEntropyExpansion.gibbonsHawkingTemperature"]
  forbids_substitutes ["a derivation of the observed value of Lambda, which the ledger takes as measured input",
    "dynamical horizon thermodynamics or the first law variation, not proven here",
    "quantum gravity claims from static eigenvalue identities"]
  witnessed_by [cosmologicalConstant_bitForm, deSitter_entropy_eq_quarter_bits,
    deSitter_darkEnergy_bitCount, deSitterHorizonArea_eq_sphereArea,
    gibbonsHawking_is_kms_at_deSitter, deSitter_smarr_bitCount]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.DeSitterCosmologicalConstantBits
