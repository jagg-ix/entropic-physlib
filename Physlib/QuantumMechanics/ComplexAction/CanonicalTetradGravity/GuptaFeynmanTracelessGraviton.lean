/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HPMGravitationalWaves
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation
meta import Zil

/-!
# The Gupta–Feynman traceless massless spin-2 graviton

Plastino–Rocca, *Gupta-Feynman based QFT of Einstein's Gravity* (J. Phys. Commun. 4 (2020) 035014):
the linearized graviton field `φ^μν` (from `h^μν = η^μν + κφ^μν`) is quantized under the **traceless
gauge constraint** `φ^μ_μ = 0` (their eq. 3.6), which forces the **massless spin-2 wave equation**
`□φ_μν = 0` (eq. 3.7) with a plane-wave solution on the luminal shell `k₀ = |k|` (eq. 3.8).

The repo carries both halves: the trace-free (transverse-traceless) tidal GW perturbation
(`HPMGravitationalWaves.gw_traceless`) and the on-shell d'Alembertian `□R = 0`
(`GWWaveEquation.gw_dalembertian`, `gw_onshell_symbol`).  This module conjoins them into the
Gupta–Feynman statement.

* `guptaFeynman_traceless_massless_graviton` — for a York-orthogonal (traceless) tidal
  configuration whose polarization amplitude is a plane wave on the luminal shell `ω² = c²k²`,
  the trace-free constraint (eq. 3.6), the massless spin-2 wave equation `□φ = 0` (eq. 3.7), and
  the on-shell condition `k² = ω²/c²` (`k₀ = |k|`, eq. 3.8) all hold.

Honest scope: this is the classical / first-quantized *amplitude* level (`R = cos(k·x − ωt)`); the
paper's operator mode expansion `φ_μν = ∫[a_μν e^{ikx} + a⁺_μν e^{−ikx}]/√(2k₀)d³k` with graviton
creation/annihilation operators is not formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HPMGravitationalWaves
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

/-- **The Gupta–Feynman traceless massless spin-2 graviton.**  For a York-orthogonal (traceless
gauge, `φ^μ_μ = 0`, eq. 3.6) tidal configuration `γ` with polarization amplitudes `Rpol`, whose
plane-wave amplitude `amp` propagates on the luminal shell `ω² = c²k²`:

* the tidal GW perturbation is **trace-free**, `∑_r 2·tidalLog γ Rpol r = 0` (eq. 3.6);
* the amplitude solves the **massless spin-2 wave equation** `(1/c²)∂²_t − ∂²_x` acting on it is `0`
  (`□φ = 0`, eq. 3.7);
* the mode is **on the luminal shell**, `k² − ω²/c² = 0` (`k₀ = |k|`, eq. 3.8). -/
@[zil_level bridge_theorem]
theorem guptaFeynman_traceless_massless_graviton {m n : ℕ}
    (γ : Fin m → Fin n → ℝ) (Rpol : Fin m → ℝ) (hγ : YorkGammaOrtho γ)
    (k ω c amp : ℝ) (hc : c ≠ 0) (hshell : ω ^ 2 = c ^ 2 * k ^ 2) :
    (∑ r : Fin n, 2 * tidalLog γ Rpol r = 0)
      ∧ ((1 / c ^ 2) * (-ω ^ 2 * amp) - (-k ^ 2 * amp) = 0)
      ∧ (k ^ 2 - ω ^ 2 / c ^ 2 = 0) :=
  ⟨gw_traceless γ Rpol hγ, gw_dalembertian k ω c amp hc hshell, gw_onshell_symbol k ω c hc hshell⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton

zil attach guptaFeynman_traceless_massless_graviton where
  formalizes @ "claim:the-gupta-feynman-linearized-graviton-under-the-traceless-gauge-constraint-phi-mu-mu-zero-is-a-massless-spin-two-plane-wave-the-trace-free-tidal-perturbation-satisfies-the-dalembertian-wave-equation-box-phi-zero-on-the-luminal-shell-k-zero-equals-magnitude-k",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HPMGravitationalWaves.gw_traceless",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation.gw_dalembertian"

zil_file_contract physlib.guptaFeynmanTracelessGraviton where
  promises "The Gupta-Feynman traceless massless spin-2 graviton of Plastino-Rocca. The linearized graviton field, quantized under the traceless gauge constraint phi mu mu equals zero, is a massless spin-2 plane wave on the luminal shell. For a York-orthogonal traceless tidal configuration whose polarization amplitude is a plane wave on the shell omega squared equals c squared k squared, the tidal gravitational-wave perturbation is trace-free, the amplitude solves the massless spin-2 dalembertian wave equation box phi equals zero, and the mode is on the luminal shell k squared equals omega squared over c squared, that is k zero equals magnitude of k. This is the classical amplitude level; the paper's operator mode expansion with graviton creation and annihilation operators is not formalized here."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis.tidalLog",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation.gw_onshell_symbol"
  ]
  forbids_substitutes [
    "reading the classical plane-wave amplitude as the paper's quantized operator mode expansion with graviton creation and annihilation operators"
  ]
  witnessed_by [
    guptaFeynman_traceless_massless_graviton
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.guptaFeynmanTracelessGraviton
