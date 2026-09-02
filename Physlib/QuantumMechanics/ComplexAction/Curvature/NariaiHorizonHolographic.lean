/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling
public import Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
public import Physlib.Thermodynamics.VerlindeNewtonGravity
meta import Zil

/-!
# Holography of the Nariai (merged) horizon

At the Nariai limit the black-hole and cosmological horizons merge into a single degenerate horizon at
`r₀ = 1/√Λ`, with area `𝒜 = 4π r₀² = 4π/Λ`.  Its Bekenstein–Hawking entropy is a quarter of its
holographic bit count, and the holographic Newton constant reconstructed from that bit count returns `G` —
extending the holographic-loop closure (already established for the Reissner–Nordström and Kerr–Newman
horizons) to the cosmological-constant-driven Nariai horizon.

* `nariaiHorizonArea` — `𝒜 = 4π/Λ`.
* `nariai_bekensteinHawking_eq_holographicBits_div_four` — `S = N/4`.
* `nariai_newtonG_holographic_from_horizonBits` — `G = 𝒜 c³/(N ℏ)` reconstructed from the Nariai bit count.

Honest scope: the horizon-area / holographic-bit-count algebra; the statistical-mechanical origin of the
horizon bits is not derived here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai
open Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
open Physlib.Thermodynamics

/-- **The Nariai merged-horizon area** `𝒜 = 4π r₀² = 4π/Λ`. -/
def nariaiHorizonArea (Λ : ℝ) : ℝ := 4 * Real.pi * nariaiRadius Λ ^ 2

/-- `𝒜 = 4π/Λ`. -/
@[zil_level physical_theorem]
theorem nariaiHorizonArea_eq (Λ : ℝ) (hΛ : 0 < Λ) : nariaiHorizonArea Λ = 4 * Real.pi / Λ := by
  unfold nariaiHorizonArea
  rw [nariaiRadius_sq hΛ]
  ring

/-- **The Nariai horizon entropy is a quarter of its holographic bit count** `S = N/4`. -/
@[zil_level physical_theorem]
theorem nariai_bekensteinHawking_eq_holographicBits_div_four (Λ G : ℝ) :
    bekensteinHawkingEntropy (nariaiHorizonArea Λ) G
      = holographicBits (nariaiHorizonArea Λ) G 1 1 / 4 := by
  unfold bekensteinHawkingEntropy holographicBits
  ring

/-- **The holographic Newton constant reconstructed from the Nariai horizon bit count returns `G`** — the
holographic loop closes on the cosmological Nariai horizon (for `Λ > 0`, `ℏ, c, G ≠ 0`). -/
@[zil_level physical_theorem]
theorem nariai_newtonG_holographic_from_horizonBits (Λ ℏ c G : ℝ)
    (hΛ : 0 < Λ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    newtonG_holographic (nariaiHorizonArea Λ) ℏ c
        (holographicBits (nariaiHorizonArea Λ) G ℏ c) = G := by
  have hA : nariaiHorizonArea Λ ≠ 0 := by rw [nariaiHorizonArea_eq Λ hΛ]; positivity
  exact newtonG_holographic_holographicBits (nariaiHorizonArea Λ) G ℏ c hA hℏ hc hG

end Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic

zil attach nariaiHorizonArea_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariaiRadius_sq",
  formalizes @ "claim:the-nariai-merged-horizon-area-is-four-pi-over-lambda-four-pi-times-the-nariai-radius-squared"

zil attach nariai_bekensteinHawking_eq_holographicBits_div_four where
  formalizes @ "claim:the-nariai-horizon-bekenstein-hawking-entropy-is-a-quarter-of-its-holographic-bit-count"

zil attach nariai_newtonG_holographic_from_horizonBits where
  formalizes @ "claim:the-holographic-newton-constant-reconstructed-from-the-nariai-horizon-bit-count-returns-g-the-holographic-loop-closes-on-the-cosmological-nariai-horizon",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic_holographicBits"

zil_file_contract physlib.nariaiHorizonHolographic where
  promises "The holography of the Nariai merged horizon. At the Nariai limit the black-hole and cosmological horizons merge into a single degenerate horizon at one over the square root of Lambda, with area four pi over Lambda, four pi times the Nariai radius squared. Its Bekenstein-Hawking entropy is a quarter of its holographic bit count, and the holographic Newton constant, the horizon area times c cubed over the bit count times hbar, reconstructed from that bit count returns G, extending the holographic-loop closure already established for the Reissner-Nordstrom and Kerr-Newman horizons to the cosmological-constant-driven Nariai horizon. Honest scope: the horizon-area and holographic-bit-count algebra; the statistical-mechanical origin of the horizon bits is not derived here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariaiRadius",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic",
    "lean:Physlib.Thermodynamics.holographicBits"
  ]
  forbids_substitutes [
    "reading the algebraic reconstruction of G from the Nariai horizon bit count as a statistical-mechanical derivation of the horizon degrees of freedom"
  ]
  witnessed_by [
    nariaiHorizonArea_eq,
    nariai_bekensteinHawking_eq_holographicBits_div_four,
    nariai_newtonG_holographic_from_horizonBits
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.nariaiHorizonHolographic
