/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
public import Physlib.FluidDynamics.NavierStokes.Basic
meta import Zil

/-!
# Navier–Stokes terms inside the Madelung–Schrödinger equations

The Madelung transform `ψ = √ρ·e^{iθ}` carries the (non-Hermitian) Schrödinger equation to fluid equations —
and the repo already holds both sides: the actual Navier–Stokes forms (`FluidDynamics.NavierStokes.Basic`:
continuity + conservative/convective momentum, `navierStokes_iff_convectiveNavierStokes`) and the Madelung
hydrodynamics (`BohmMadelung.MadelungTransformFisherPotential`, `ComplexAction.NavierStokes.
ViscousDissipationFisherInformation`).  This module makes the term-by-term **recognition** exact:

* **The viscous term and the quantum potential are the same Fisher functional.**  The NS viscous dissipation
  density is `ν(f')² = ν·¼·fisherDensity(f²)` (`dissipationDensity_eq_fisher`), and the Bohm quantum potential
  of the Madelung fluid is Fisher-generated, `Q = −ℏ²/(4m)·ρ''/ρ + ℏ²/(8m)·fisherDensity(ρ)/ρ`
  (`quantumPotential_is_fisher_generated`) — **one and the same `fisherDensity`** appears as the Navier–Stokes
  dissipation and as the non-classical term of the quantum momentum equation
  (`viscous_dissipation_and_quantum_potential_share_fisher`).
* **The coefficient dictionary** (`quantum_viscosity_dictionary`): the Schrödinger equation is a complex
  diffusion with coefficient `iℏ/2m`; at the **quantum kinematic viscosity** `ν_q = ℏ/2m` the NS Fisher
  coefficient reproduces the quantum potential's: `ℏ²/8m = ℏ·(ν_q/4)` — the Madelung fluid's "viscosity" is
  `ℏ/2m`, imaginary for the Hermitian flow, made *real* (genuinely viscous) by the non-Hermitian sector.
* **The dissipative sign is shared** (`nonHermitian_viscous_dissipation_signs`): the non-Hermitian imaginary
  generator contracts the flow (`entropic_generator_flow_contracts`, `Re λ < 0 ⟹ ‖e^{λt}‖ < 1`) exactly as the
  NS viscous rate only removes energy (`viscousDissipationRate_nonpos`, `−ν(f')² ≤ 0`) — Leray's energy
  inequality and the entropic clock's arrow are the same sign.
* The **convective structure** is the shared skeleton: the conservative and convective Navier–Stokes forms are
  equivalent (`navierStokes_iff_convectiveNavierStokes`), and the Madelung momentum equation is Newton's
  equation on densities (`madelung_geometric_hydrodynamics`) — the `(v·∇)v` transport with the Fisher/quantum
  internal energy in place of the classical pressure.

`madelung_navierStokes_recognition` bundles the three proved recognitions: same Fisher term, matched
coefficients at `ν_q = ℏ/2m`, same dissipative sign.

Honest scope: the 1D/component-level identities of the two existing arcs, welded; the full vector convective
equivalence is quoted from `FluidDynamics` (its own hypotheses), and the non-Hermitian-makes-ν-real statement
is the coefficient dictionary plus the contraction sign, not a derivation of the NS equations from Schrödinger.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms

open Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungTransformFisherPotential
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation
open Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum

/-! ## §1. The quantum kinematic viscosity -/

/-- **The quantum kinematic viscosity** `ν_q = ℏ/2m` — the Schrödinger equation's complex-diffusion
coefficient (`iν_q`), the Madelung fluid's viscosity scale: imaginary for the Hermitian flow, made real by the
non-Hermitian sector. -/
def quantumKinematicViscosity (ℏ m : ℝ) : ℝ := ℏ / (2 * m)

/-- **[The coefficient dictionary] `ℏ²/8m = ℏ·(ν_q/4)`** — at the quantum kinematic viscosity, the
Navier–Stokes Fisher coefficient (`ν·¼`) reproduces exactly the quantum potential's Fisher coefficient
(`ℏ²/8m`): the two Fisher terms carry matched constants. -/
theorem quantum_viscosity_dictionary (ℏ m : ℝ) (hm : m ≠ 0) :
    ℏ ^ 2 / (8 * m) = ℏ * (quantumKinematicViscosity ℏ m / 4) := by
  unfold quantumKinematicViscosity
  field_simp
  ring

/-! ## §2. The recognition: one Fisher functional, two equations -/

/-- **[The viscous term and the quantum potential are the same Fisher functional]** — for the Madelung
amplitude `s = √ρ` (equally a velocity component): **(i)** the NS viscous dissipation density is
`ν(s')² = ν·¼·fisherDensity(s²)`; **(ii)** the Bohm quantum potential decomposes as
`−ℏ²/(2m)·s''/s = −ℏ²/(4m)·ρ''/ρ + ℏ²/(8m)·fisherDensity(ρ)/ρ` — **one and the same `fisherDensity`**
appears as the Navier–Stokes dissipation and as the non-classical term of the quantum momentum equation. -/
theorem viscous_dissipation_and_quantum_potential_share_fisher
    (ν m ℏ : ℝ) (s s' s'' : ℝ → ℝ)
    (hs : ∀ y, HasDerivAt s (s' y) y) (hs' : ∀ y, HasDerivAt s' (s'' y) y)
    (x : ℝ) (hsx : s x ≠ 0) (hm : m ≠ 0) :
    ν * (s' x) ^ 2 = ν * (1 / 4 * fisherDensity (fun y => (s y) ^ 2) x)
      ∧ -(ℏ ^ 2) / (2 * m) * (s'' x / s x)
          = -(ℏ ^ 2) / (4 * m) * (deriv (deriv (fun y => (s y) ^ 2)) x / (s x) ^ 2)
              + (ℏ ^ 2) / (8 * m) * (fisherDensity (fun y => (s y) ^ 2) x / (s x) ^ 2) := by
  refine ⟨?_, quantumPotential_is_fisher_generated s s' s'' m ℏ hs hs' x hsx hm⟩
  rw [dissipationDensity_eq_fisher s s' hs x hsx]

/-! ## §3. The shared dissipative sign -/

/-- **[The non-Hermitian sector and the NS viscosity dissipate with the same sign]** — the imaginary
(entropic) generator strictly contracts the flow (`‖e^{λt}‖ < 1` for `Re λ < 0`, `t > 0`), exactly as the NS
viscous rate only removes energy (`−ν(f')² ≤ 0`): Leray's energy-inequality sign and the entropic clock's
arrow are one. -/
theorem nonHermitian_viscous_dissipation_signs (l : ℂ) (t ν : ℝ) (f' : ℝ → ℝ) (x : ℝ)
    (hl : l.re < 0) (ht : 0 < t) (hν : 0 ≤ ν) :
    ‖Complex.exp (l * t)‖ < 1 ∧ -(ν * (f' x) ^ 2) ≤ 0 :=
  ⟨entropic_generator_flow_contracts l t hl ht, viscousDissipationRate_nonpos ν f' x hν⟩

/-! ## §4. The recognition, bundled -/

/-- **[Navier–Stokes terms inside the Madelung–Schrödinger equations]** — **(i)** the viscous dissipation and
the quantum potential are the same Fisher functional; **(ii)** the coefficients match at the quantum kinematic
viscosity `ν_q = ℏ/2m`; **(iii)** the non-Hermitian imaginary sector and the NS viscosity share the
dissipative sign.  The Madelung transform does not merely resemble hydrodynamics: the Navier–Stokes viscous
term, its coefficient, and its sign are all present in the quantum equations, with the Fisher information as
the common carrier. -/
theorem madelung_navierStokes_recognition
    (ν m ℏ : ℝ) (s s' s'' : ℝ → ℝ)
    (hs : ∀ y, HasDerivAt s (s' y) y) (hs' : ∀ y, HasDerivAt s' (s'' y) y)
    (x : ℝ) (hsx : s x ≠ 0) (hm : m ≠ 0)
    (l : ℂ) (t : ℝ) (hl : l.re < 0) (ht : 0 < t) (hν : 0 ≤ ν) :
    (ν * (s' x) ^ 2 = ν * (1 / 4 * fisherDensity (fun y => (s y) ^ 2) x)
        ∧ -(ℏ ^ 2) / (2 * m) * (s'' x / s x)
            = -(ℏ ^ 2) / (4 * m) * (deriv (deriv (fun y => (s y) ^ 2)) x / (s x) ^ 2)
                + (ℏ ^ 2) / (8 * m) * (fisherDensity (fun y => (s y) ^ 2) x / (s x) ^ 2))
      ∧ ℏ ^ 2 / (8 * m) = ℏ * (quantumKinematicViscosity ℏ m / 4)
      ∧ (‖Complex.exp (l * t)‖ < 1 ∧ -(ν * (s' x) ^ 2) ≤ 0) :=
  ⟨viscous_dissipation_and_quantum_potential_share_fisher ν m ℏ s s' s'' hs hs' x hsx hm,
    quantum_viscosity_dictionary ℏ m hm,
    nonHermitian_viscous_dissipation_signs l t ν s' x hl ht hν⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms.viscous_dissipation_and_quantum_potential_share_fisher where
  formalizes @ "claim:the-navier-stokes-viscous-dissipation-and-the-bohm-quantum-potential-are-the-same-fisher-information-functional",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation.dissipationDensity_eq_fisher",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungTransformFisherPotential.quantumPotential_is_fisher_generated",
  caveat @ "epistemic:one-dimensional-component-level-identities-of-the-two-existing-arcs-welded"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms.madelung_navierStokes_recognition where
  formalizes @ "claim:the-navier-stokes-viscous-term-coefficient-and-dissipative-sign-are-all-present-in-the-madelung-schrodinger-equations-with-fisher-information-as-the-common-carrier",
  requires @ "claim:the-navier-stokes-viscous-dissipation-and-the-bohm-quantum-potential-are-the-same-fisher-information-functional",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.entropic_generator_flow_contracts",
  caveat @ "epistemic:recognition-of-shared-terms-not-a-derivation-of-navier-stokes-from-schrodinger"

/- ZIL-END -/
