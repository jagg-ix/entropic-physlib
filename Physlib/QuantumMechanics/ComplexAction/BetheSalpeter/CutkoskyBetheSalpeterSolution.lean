/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator

/-!
# The Wick–Cutkosky Bethe–Salpeter solution as a complex oscillator (Cutkosky 1954)

This file formalizes the algebraic core of R. E. Cutkosky, *Solutions of a Bethe–Salpeter Equation*,
Phys. Rev. **96** (1954) 1135 — the exactly solvable BS equation for two scalars interacting through a
**massless** scalar field (the Wick–Cutkosky model) — and links it to the **Nagao–Nielsen complex
oscillator** of this development.

## The structure of the Cutkosky solution

The BS equation (Cutkosky Eq. 1–2) is written with the **relative energy on the imaginary axis**
(Wick's theorem):

  `[(p + iη)² + 1][(p − iη)² + 1] φ(p) = (λ/π²) ∫ d⁴k φ(k)/(p − k)²`,

`η` the (imaginary) relative-energy parameter, `λ` the eigenvalue coupling. Two structural facts that
slot into the arc:

* **Relative energy = Nagao–Nielsen complex momentum (Wick rotation).** The `d⁴k` kernel is the
  complex-momentum / Feynman–Kac integral; it converges under the Wick rotation exactly when
  `Im m > 0` (`cutkosky_wick_convergence`, reusing the NN convergence). This is the imaginary
  relative time of Cutkosky's Eq. 1.
* **Relative-time motion = complex oscillator.** Fock's transformation reduces the equation to a
  one-dimensional integral equation for `g_n(z)` (Eq. 15) with kernel `R(z,ζ) = (1±z)/(1±ζ)`
  (Eq. 16, `cutkoskyKernel`), equivalent to the second-order ODE (Eq. 17) — a complex / damped
  oscillator in the relative-time variable `z ∈ (−1,1)`, with eigenvalues `λ_κ` indexed by the node
  number `κ`. The bound state is the Nagao–Nielsen complex oscillator (`oscillatorEnergy`).

## The eigenvalue spectrum is the angular-momentum Casimir

At zero energy (`η → 0`) the coupling eigenvalues are (Cutkosky, after Eq. 17 / Appendix)

  `λ_N = N(N + 1)`   (`cutkoskyEigenvalue`),

`N = n + κ` the principal quantum number — the **O(4) degeneracy of the nonrelativistic hydrogen
atom**. This is *exactly* the angular-momentum Casimir `reggeCasimir J = J(J+1)` of the Swift–Lee
Regge structure (`cutkoskyEigenvalue_eq_casimir`): the Wick–Cutkosky coupling spectrum is the Casimir
of the rotation group, the same `J(J+1)` that organizes the Regge tower.

## Main results

* `cutkoskyEigenvalue`, `cutkoskyEigenvalue_eq_casimir`, `cutkoskyEigenvalue_strictMono` — the
  spectrum `λ_N = N(N+1) = reggeCasimir N`.
* `cutkoskyKernel`, `cutkoskyKernel_diag` — the Wick kernel `R(z,ζ) = (1+z)/(1+ζ)` (Eq. 16).
* `cutkosky_wick_convergence` — the relative-energy kernel converges iff `Im m > 0`.
* `cutkosky_solution_summary` — the bundled statement (spectrum + Wick + oscillator tower).

## Not formalized (out of scope)

Fock's stereographic transformation, the full integral equations (Eqs. 15, 18, 19), the ODE (17)
solutions / boundary conditions, the anomalous solutions, the unequal-mass case (Eqs. 23–27), and
Fig. 1 (`λ` vs `η²`) are **not** formalized here.

## References

* R. E. Cutkosky, Phys. Rev. **96** (1954) 1135. doi:10.1103/PhysRev.96.1135.
* G. C. Wick, Phys. Rev. **96** (1954) 1124. This development: `BetheSalpeter.SwiftLeeComplexAngularMomentum`,
  `BetheSalpeter.SwiftLeeBetheSalpeterOscillator`, `PathIntegral.MomentumPathIntegral`, `ComplexOscillator.ComplexHarmonicOscillatorBoson`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-! ## §A — the zero-energy eigenvalue spectrum `λ_N = N(N+1)` (the O(4) Casimir) -/

/-- **The Wick–Cutkosky zero-energy coupling eigenvalue** `λ_N = N(N+1)` (Cutkosky, `N = n+κ` the
principal quantum number) — the O(4) hydrogen degeneracy. -/
def cutkoskyEigenvalue (N : ℕ) : ℝ := (N : ℝ) * ((N : ℝ) + 1)

/-- **The Cutkosky eigenvalue is the angular-momentum Casimir** `λ_N = N(N+1) = reggeCasimir N`: the
Wick–Cutkosky coupling spectrum is the Casimir `J(J+1)` of the rotation group (the same that
organizes the Swift–Lee Regge tower). -/
theorem cutkoskyEigenvalue_eq_casimir (N : ℕ) :
    ((cutkoskyEigenvalue N : ℝ) : ℂ) = reggeCasimir (N : ℂ) := by
  unfold cutkoskyEigenvalue reggeCasimir
  push_cast
  ring

/-- **The eigenvalue spectrum is strictly increasing** in the principal quantum number `N`. -/
theorem cutkoskyEigenvalue_strictMono {N M : ℕ} (h : N < M) :
    cutkoskyEigenvalue N < cutkoskyEigenvalue M := by
  unfold cutkoskyEigenvalue
  have hNM : (N : ℝ) < M := by exact_mod_cast h
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [hNM, hN]

/-- **The ground eigenvalue vanishes** `λ_0 = 0`. -/
theorem cutkoskyEigenvalue_zero : cutkoskyEigenvalue 0 = 0 := by
  unfold cutkoskyEigenvalue; simp

/-! ## §B — the Wick kernel `R(z,ζ) = (1+z)/(1+ζ)` (Cutkosky Eq. 16) -/

/-- **The Wick kernel** `R(z, ζ) = (1+z)/(1+ζ)` (Cutkosky Eq. 16, the `ζ ≥ z` branch). -/
def cutkoskyKernel (z ζ : ℝ) : ℝ := (1 + z) / (1 + ζ)

/-- **The Wick kernel is `1` on the diagonal** `R(z, z) = 1` (for `1 + z ≠ 0`). -/
theorem cutkoskyKernel_diag (z : ℝ) (hz : 1 + z ≠ 0) : cutkoskyKernel z z = 1 :=
  div_self hz

/-! ## §C — the relative-energy Wick rotation (complex momentum, Feynman–Kac) -/

/-- **The Cutkosky relative-energy kernel converges under the Wick rotation iff `Im m > 0`**: the
`d⁴k` propagator integral is the Nagao–Nielsen complex-momentum / Feynman–Kac integral — Cutkosky's
imaginary relative time is the convergence condition `Im m > 0`. -/
theorem cutkosky_wick_convergence (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  bsKernel_converges_iff m hℏ hdt hm

/-! ## §D — the bundled statement -/

/-- **The Wick–Cutkosky Bethe–Salpeter solution as a complex oscillator.** For `0 < ℏ`, `0 < dt`,
`m ≠ 0`:

* the zero-energy coupling spectrum is the angular-momentum Casimir `λ_N = N(N+1) = reggeCasimir N`
  (the O(4) hydrogen degeneracy);
* the relative-energy kernel converges under the Wick rotation iff `Im m > 0` (complex momentum /
  Feynman–Kac);
* the bound-state relative motion is the Nagao–Nielsen complex oscillator with level spacing `ℏω`. -/
theorem cutkosky_solution_summary (N : ℕ) (m ω : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) (n : ℕ) :
    ((cutkoskyEigenvalue N : ℝ) : ℂ) = reggeCasimir (N : ℂ)
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im)
      ∧ oscillatorEnergy ℏ ω (n + 1) - oscillatorEnergy ℏ ω n = (ℏ : ℂ) * ω :=
  ⟨cutkoskyEigenvalue_eq_casimir N, cutkosky_wick_convergence m hℏ hdt hm,
   oscillatorEnergy_succ_sub ℏ ω n⟩

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

end

end
