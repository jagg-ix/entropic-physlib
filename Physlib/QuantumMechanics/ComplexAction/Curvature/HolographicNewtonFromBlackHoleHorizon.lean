/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling
public import Physlib.Thermodynamics.VerlindeNewtonGravity
meta import Zil

/-!
# The holographic Newton constant from a black-hole horizon

The holographic Newton constant `G = A c³/(N ℏ)` (`newtonG_holographic`) reconstructs `G` from the
holographic bit count `N = A c³/(G ℏ)` (`holographicBits`) of a screen of area `A`.  Applying this to the
horizons of the charged/rotating black holes built here closes the holographic loop: the horizon area of a
black-hole solution — itself built with `G` — carries a bit count that reproduces `G`.

* `bekensteinHawking_eq_holographicBits_div_four` — the Bekenstein–Hawking entropy `𝒜/4G` is a quarter of
  the holographic bit count (natural units `ℏ = c = 1`): the "`S = N/4`" law, the `bekensteinHawkingEntropy`
  companion of the existing `bekensteinTauEnt` version.
* `kn_bekensteinHawking_eq_holographicBits_div_four` — the Kerr–Newman horizon entropy is a quarter of its
  holographic bit count.
* `kn_newtonG_holographic_from_horizonBits` / `rn_newtonG_holographic_from_horizonBits` — the holographic
  Newton constant reconstructed from the Kerr–Newman / Reissner–Nordström horizon bit count returns `G`.

Honest scope: this connects the horizon area to the holographic `G`/bit-count carriers algebraically; the
statistical-mechanical origin of the horizon bits is not derived here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea
open Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
open Physlib.Thermodynamics

/-- **The Bekenstein–Hawking entropy is a quarter of the holographic bit count** `𝒜/4G = N/4`
(natural units `ℏ = c = 1`): the `bekensteinHawkingEntropy` companion of `bekensteinTauEnt = N/4`. -/
@[zil_level physical_theorem]
theorem bekensteinHawking_eq_holographicBits_div_four (A G : ℝ) :
    bekensteinHawkingEntropy A G = holographicBits A G 1 1 / 4 := by
  unfold bekensteinHawkingEntropy holographicBits
  ring

/-- **The Kerr–Newman horizon entropy is a quarter of its holographic bit count.** -/
@[zil_level physical_theorem]
theorem kn_bekensteinHawking_eq_holographicBits_div_four (M a Q G : ℝ) :
    bekensteinHawkingEntropy (knHorizonArea M a Q) G
      = holographicBits (knHorizonArea M a Q) G 1 1 / 4 :=
  bekensteinHawking_eq_holographicBits_div_four (knHorizonArea M a Q) G

/-- **The holographic Newton constant reconstructed from the Kerr–Newman horizon bit count returns `G`**
`G = 𝒜 c³/(N ℏ)` with `N` the horizon's own bit count — the holographic loop closes on the rotating
charged horizon (for `M > 0`, `ℏ, c, G ≠ 0`). -/
@[zil_level physical_theorem]
theorem kn_newtonG_holographic_from_horizonBits (M a Q ℏ c G : ℝ)
    (hM : 0 < M) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    newtonG_holographic (knHorizonArea M a Q) ℏ c
        (holographicBits (knHorizonArea M a Q) G ℏ c) = G :=
  newtonG_holographic_holographicBits (knHorizonArea M a Q) G ℏ c
    (knHorizonArea_pos M a Q hM).ne' hℏ hc hG

/-- **The holographic Newton constant reconstructed from the Reissner–Nordström horizon bit count returns
`G`** — the holographic loop closes on the charged horizon (for `M > 0`, `ℏ, c, G ≠ 0`). -/
@[zil_level physical_theorem]
theorem rn_newtonG_holographic_from_horizonBits (M Q ℏ c G : ℝ)
    (hM : 0 < M) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    newtonG_holographic (rnHorizonArea M Q) ℏ c
        (holographicBits (rnHorizonArea M Q) G ℏ c) = G :=
  newtonG_holographic_holographicBits (rnHorizonArea M Q) G ℏ c
    (rnHorizonArea_pos M Q hM).ne' hℏ hc hG

end Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon

zil attach bekensteinHawking_eq_holographicBits_div_four where
  formalizes @ "claim:the-bekenstein-hawking-entropy-area-over-four-g-is-a-quarter-of-the-holographic-bit-count-in-natural-units-the-s-equals-n-over-four-law",
  supported_by @ "lean:Physlib.Thermodynamics.holographicBits"

zil attach kn_bekensteinHawking_eq_holographicBits_div_four where
  supported_by @ "lean:bekensteinHawking_eq_holographicBits_div_four",
  formalizes @ "claim:the-kerr-newman-horizon-bekenstein-hawking-entropy-is-a-quarter-of-its-holographic-bit-count"

zil attach kn_newtonG_holographic_from_horizonBits where
  formalizes @ "claim:the-holographic-newton-constant-reconstructed-from-the-kerr-newman-horizon-bit-count-returns-g-the-holographic-loop-closes-on-the-rotating-charged-horizon",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic_holographicBits"

zil attach rn_newtonG_holographic_from_horizonBits where
  formalizes @ "claim:the-holographic-newton-constant-reconstructed-from-the-reissner-nordstrom-horizon-bit-count-returns-g-the-holographic-loop-closes-on-the-charged-horizon",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic_holographicBits"

zil_file_contract physlib.holographicNewtonFromBlackHoleHorizon where
  promises "The holographic Newton constant from a black-hole horizon, connecting the charged and rotating black-hole horizons to the holographic Newton constant and bit-count carriers. The holographic Newton constant G equals the horizon area times c cubed over the bit count times hbar, reconstructing G from the holographic bit count of a screen. The Bekenstein-Hawking entropy area over four G is a quarter of the holographic bit count in natural units, the S equals N over four law, the Bekenstein-Hawking companion of the existing entropic-time version; the Kerr-Newman horizon entropy is likewise a quarter of its holographic bit count. The holographic Newton constant reconstructed from the Kerr-Newman or Reissner-Nordstrom horizon's own bit count returns G, closing the holographic loop: the horizon area of a black-hole solution, itself built with G, carries a bit count that reproduces G. Honest scope: this connects the horizon area to the holographic G and bit-count carriers algebraically; the statistical-mechanical origin of the horizon bits is not derived here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic",
    "lean:Physlib.Thermodynamics.holographicBits",
    "lean:Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics.bekensteinHawkingEntropy"
  ]
  forbids_substitutes [
    "reading the algebraic reconstruction of G from the horizon bit count as a statistical-mechanical derivation of the horizon degrees of freedom"
  ]
  witnessed_by [
    bekensteinHawking_eq_holographicBits_div_four,
    kn_bekensteinHawking_eq_holographicBits_div_four,
    kn_newtonG_holographic_from_horizonBits,
    rn_newtonG_holographic_from_horizonBits
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.holographicNewtonFromBlackHoleHorizon
