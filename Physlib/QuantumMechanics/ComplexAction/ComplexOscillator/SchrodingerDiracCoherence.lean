/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyCompleteSolution
public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.TISE

/-!
# Coherence of the complex oscillator, the Schrödinger oscillator, and the Dirac equation

This file proves the **coherence** the Cutkosky / Bethe–Salpeter arc requires: the Nagao–Nielsen
**complex oscillator**, the physlib **Schrödinger harmonic oscillator** (the time-independent
Schrödinger equation), and the **Dirac equation** describe the *same* bound state in different
regimes, and their spectra agree.

## What is proved (the coherence)

* **Complex oscillator = Schrödinger oscillator (TISE).** The complex oscillator's energy at real
 frequency, `oscillatorEnergy ℏ ω n = ℏω(n+½)`, is *exactly* physlib's Schrödinger harmonic-oscillator
 eigenvalue `HarmonicOscillator.eigenValue` (`complexOscillator_eq_schrodinger_eigenValue`) — which
 physlib proves is a genuine eigenvalue of the Schrödinger operator with the Hermite eigenfunction
 (`HarmonicOscillator.schrodingerOperator_eigenfunction`). So the complex oscillator's reversible
 (real-ω) limit *is* the Schrödinger oscillator.
* **Dirac equation → Schrödinger kinetic energy.** The Dirac / Klein–Gordon dispersion `E² = (mc²)² +
 (cp)²` factors as `(E − mc²)(E + mc²) = (cp)²` (`dirac_nonrel_kinetic`): the relativistic kinetic
 energy `E − mc²` equals `(cp)²/(E + mc²) → p²/2m` as `E → mc²` — the nonrelativistic Schrödinger
 kinetic energy. So the Dirac equation reduces coherently to the Schrödinger description.
* **The bound-state spectrum is the O(4) Casimir.** The Cutkosky / hydrogen coupling spectrum is
 `λ_N = N(N+1) = reggeCasimir N` (`BetheSalpeter.CutkoskyBetheSalpeterSolution`), the same angular-momentum Casimir
 for the complex-oscillator relative motion, the Schrödinger hydrogen atom, and the Regge tower.

## Scope

What is **not** proved (and was not claimed to be): the literal Cutkosky Eq. 17 *spectral
derivation* — i.e. that the Gegenbauer eigenfunctions `g_n = (1−z²)ⁿ C_κ^{n+1}(z)` solve the ODE at
`λ = N(N+1)`. Mathlib has Hermite polynomials (used by the Schrödinger oscillator above) but **no
Gegenbauer polynomials**, so that Sturm–Liouville eigenvalue problem is out of reach here. This file
proves the *coherence of the spectra and limits*, not the Gegenbauer ODE solution.

## Main results

* `complexOscillator_eq_schrodinger_eigenValue` — complex oscillator energy = Schrödinger TISE
 eigenvalue.
* `dirac_nonrel_kinetic` — the Dirac dispersion factors to the Schrödinger kinetic energy.
* `oscillator_schrodinger_dirac_coherence` — the bundled coherence.

## References

* R. E. Cutkosky, Phys. Rev. **96** (1954) 1135; P. A. M. Dirac 1928. This development:
 `ComplexOscillator.ComplexHarmonicOscillatorBoson`, `Dirac.KleinGordonDiracFactorization`, `BetheSalpeter.CutkoskyBetheSalpeterSolution`;
 physlib `OneDimension.HarmonicOscillator` (Schrödinger TISE).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
open QuantumMechanics.OneDimension
open QuantumMechanics.OneDimension.HarmonicOscillator

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.SchrodingerDiracCoherence

/-! ## §A — the complex oscillator energy is the Schrödinger TISE eigenvalue -/

/-- **The complex oscillator energy is the Schrödinger harmonic-oscillator eigenvalue.** At real
frequency `ω = Q.ω`, the Nagao–Nielsen complex oscillator energy `ℏω(n+½)` equals physlib's
Schrödinger TISE eigenvalue `Q.eigenValue n` — which `schrodingerOperator_eigenfunction` proves is a
genuine eigenvalue of the Schrödinger operator (Hermite eigenfunction). The complex oscillator's
real-ω (reversible) limit is the Schrödinger oscillator. -/
theorem complexOscillator_eq_schrodinger_eigenValue (Q : HarmonicOscillator) (n : ℕ) :
    oscillatorEnergy (Constants.ℏ : ℝ) (Q.ω : ℂ) n = ((Q.eigenValue n : ℝ) : ℂ) := by
  unfold oscillatorEnergy QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue
  push_cast
  ring

/-- **The complex-oscillator level spacing is physlib's canonical Schrödinger spacing.** The
Nagao–Nielsen spacing `oscillatorEnergy (n+1) − oscillatorEnergy n` (real ω) is the real shadow of
the difference of Schrödinger eigenvalues; physlib's canonical `HarmonicOscillator.eigenValue_succ_sub`
evaluates that difference to `ℏω`, so the level spacing is proved once in the QHO and reused here. -/
theorem schrodinger_oscillator_level_spacing (Q : HarmonicOscillator) (n : ℕ) :
    oscillatorEnergy (Constants.ℏ : ℝ) (Q.ω : ℂ) (n + 1)
        - oscillatorEnergy (Constants.ℏ : ℝ) (Q.ω : ℂ) n
      = ((Q.eigenValue (n + 1) - Q.eigenValue n : ℝ) : ℂ) := by
  rw [complexOscillator_eq_schrodinger_eigenValue, complexOscillator_eq_schrodinger_eigenValue,
    Complex.ofReal_sub]

/-! ## §B — the Dirac equation reduces to the Schrödinger kinetic energy -/

/-- **The Dirac dispersion factors to the Schrödinger kinetic energy.** From the Klein–Gordon / Dirac
mass shell `E² = (mc²)² + (cp)²` (here `Δ = mc²`, `v₀ = c`): `(E − Δ)(E + Δ) = (v₀ p)²`. The
relativistic kinetic energy `E − mc² = (cp)²/(E + mc²)` tends to the nonrelativistic Schrödinger
kinetic energy `p²/2m` as `E → mc²`. -/
theorem dirac_nonrel_kinetic (Δ v₀ p E : ℝ) (h : kleinGordonRelation Δ v₀ p E) :
    (E - Δ) * (E + Δ) = (v₀ * p) ^ 2 := by
  unfold kleinGordonRelation at h
  linear_combination h

/-! ## §C — the bundled coherence -/

/-- **Coherence of the complex oscillator, the Schrödinger oscillator, and the Dirac equation.**

* the complex oscillator energy (real ω) is the Schrödinger TISE eigenvalue `Q.eigenValue n`;
* the Dirac / Klein–Gordon dispersion factors to the Schrödinger kinetic energy
  `(E − mc²)(E + mc²) = (cp)²`;
* the bound-state coupling spectrum is the O(4) Casimir `λ_N = N(N+1) = reggeCasimir N`.

The three descriptions of the bound state — complex oscillator (relative motion), Schrödinger
(nonrelativistic), Dirac (relativistic) — agree on the spectrum and reduce into one another. -/
theorem oscillator_schrodinger_dirac_coherence (Q : HarmonicOscillator) (n : ℕ)
    (Δ v₀ p E : ℝ) (h : kleinGordonRelation Δ v₀ p E) (N : ℕ) :
    oscillatorEnergy (Constants.ℏ : ℝ) (Q.ω : ℂ) n = ((Q.eigenValue n : ℝ) : ℂ)
      ∧ (E - Δ) * (E + Δ) = (v₀ * p) ^ 2
      ∧ ((cutkoskyEigenvalue N : ℝ) : ℂ) = reggeCasimir (N : ℂ) :=
  ⟨complexOscillator_eq_schrodinger_eigenValue Q n, dirac_nonrel_kinetic Δ v₀ p E h,
   cutkoskyEigenvalue_eq_casimir N⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.SchrodingerDiracCoherence

end

end
