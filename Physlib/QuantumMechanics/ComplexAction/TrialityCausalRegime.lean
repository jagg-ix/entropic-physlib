/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalRegimeCPTVertex
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

/-!
# Colour triality is a causal regime: singlet = timelike/HO, coloured = spacelike/IHO

An inspection linking the `ℤ/3` **colour centre / triality** (`Particles.StrongInteractionColorOctet`,
`colourCentre_triality`: `ωⁿ = 1 ↔ 3 ∣ n`) to the Nagao–Nielsen **causal regimes** (`ComplexOscillator.CausalRegimes`,
via `CausalRegimeCPTVertex`).

The bridge is exact: the Lorentzian form of the `ℤ/3` centre phase `ω = cubeRoot` distinguishes triality classes.
The three cube-root-of-unity phases sit at `0°` (`ω⁰ = 1`, on the real axis) and `±120°` (`ω, ω²`), so

* `lorentzianForm(ωⁿ) = 1 > 0` — **timelike** — exactly when `3 ∣ n` (**colour singlet**);
* `lorentzianForm(ωⁿ) = −½ < 0` — **spacelike** — exactly when `3 ∤ n` (**coloured**).

Hence a colour singlet's centre phase is **timelike = harmonic oscillator** (physical), while a coloured phase is
**spacelike = inverted harmonic oscillator** (the confinement analogue). The colour triality *is* a causal regime.

**Honest layering.** These are exact `lorentzianForm` / cube-root-of-unity identities: an internal `ℤ/3` colour
phase placed in the complex plane, whose `(Re)² − (Im)²` is `+1` on the real-axis singlet and `−½` on the coloured
phases. The identification with spacetime *timelike/spacelike* is a structural analogy (the "Three Faces": internal
colour ↔ causal regime), **not** a claim that coloured states are literally spacelike particles.

**Inspection note (`spin 3/2`, neutrino `1+1+1`).** These share the number *three* (spin 3/2 = `Sym³` of three
spin-½; three neutrino generations) but are *internal* spin/flavour structures with no `ℤ/3` phase, and the purely
nonlinear oscillator has parity `ℤ/2` (`sgn q`), not `ℤ/3` — so they are **not** formalized as oscillator/triality
links here (that would be a coincidental *three*). The genuine bridges are this centre-phase causal regime and the
CPT-evenness of `CausalRegimeCPTVertex`.

* **`cubeRoot_of_unity_spacelike`** (any non-trivial cube root of unity is spacelike);
* **`colourSinglet_timelike`** / **`coloured_spacelike`**; **`colourSinglet_iff_timelike`** (`timelike(ωⁿ) ↔ 3∣n`);
* **`colourSinglet_isHarmonicOscillator`**, **`coloured_isInvertedHarmonicOscillator`**.

## References

* Links `Particles.StrongInteractionColorOctet` (`colourCentre_triality`) to `ComplexOscillator.CausalRegimes`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TrialityCausalRegime

/-- **A non-trivial cube root of unity is spacelike** `lorentzianForm z < 0` — for `z³ = 1`, `z ≠ 1`, the phase
sits at `±120°`, so `(Re z)² − (Im z)² < 0`. -/
lemma cubeRoot_of_unity_spacelike (z : ℂ) (h3 : z ^ 3 = 1) (hne : z ≠ 1) : spacelike z := by
  have hquad : z ^ 2 + z + 1 = 0 := by
    have hmul : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      have hfac : (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      rw [hfac, h3, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hns : Complex.normSq z = 1 := by
    have h1 : Complex.normSq z ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    nlinarith [Complex.normSq_nonneg z, h1, sq_nonneg (Complex.normSq z - 1)]
  rw [Complex.normSq_apply] at hns
  have hre : (z ^ 2).re + z.re + 1 = 0 := by
    have hquadRe := congrArg Complex.re hquad
    simpa [Complex.add_re, Complex.one_re] using hquadRe
  have hsq : (z ^ 2).re = z.re * z.re - z.im * z.im := by rw [sq, Complex.mul_re]
  unfold spacelike lorentzianForm
  nlinarith [hns, hre, hsq, sq_nonneg (2 * z.re + 1)]

/-- **A colour singlet's centre phase is timelike** `3 ∣ n → timelike(ωⁿ)` — trivial triality `ωⁿ = 1` lies on the
real axis, `lorentzianForm 1 = 1 > 0`: the singlet is the underdamped / harmonic regime. -/
lemma colourSinglet_timelike {n : ℤ} (h : (3 : ℤ) ∣ n) : timelike (cubeRoot ^ n) := by
  rw [(colourCentre_triality n).mpr h]
  unfold timelike lorentzianForm
  norm_num [Complex.one_re, Complex.one_im]

/-- **A coloured centre phase is spacelike** `3 ∤ n → spacelike(ωⁿ)` — a non-singlet triality phase is a
non-trivial cube root of unity, `lorentzianForm = −½ < 0`: the coloured (confined) regime is overdamped / inverted.
-/
lemma coloured_spacelike {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) : spacelike (cubeRoot ^ n) := by
  refine cubeRoot_of_unity_spacelike (cubeRoot ^ n) ?_ ?_
  · rw [← zpow_natCast (cubeRoot ^ n) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      cubeRoot_pow_three, one_zpow]
  · exact fun hn => h ((colourCentre_triality n).mp hn)

/-- **The colour singlet condition is the timelike condition** `timelike(ωⁿ) ↔ 3 ∣ n` — the causal character of the
`ℤ/3` centre phase *is* the triality: physical (timelike) exactly for colour singlets. -/
lemma colourSinglet_iff_timelike (n : ℤ) : timelike (cubeRoot ^ n) ↔ (3 : ℤ) ∣ n := by
  constructor
  · intro ht
    by_contra h
    exact absurd ht (by
      have hs := coloured_spacelike h
      unfold timelike spacelike at *
      linarith)
  · exact colourSinglet_timelike

/-- **The colour singlet is a harmonic oscillator** `3 ∣ n → IsHarmonicOscillator 1 (ωⁿ)`. -/
lemma colourSinglet_isHarmonicOscillator {n : ℤ} (h : (3 : ℤ) ∣ n) :
    IsHarmonicOscillator 1 (cubeRoot ^ n) :=
  (timelike_iff_isHarmonicOscillator _).mp (colourSinglet_timelike h)

/-- **A coloured state is an inverted harmonic oscillator** `3 ∤ n → IsInvertedHarmonicOscillator 1 (ωⁿ)` — the
confinement analogue: coloured centre phases are the overdamped / runaway regime. -/
lemma coloured_isInvertedHarmonicOscillator {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) :
    IsInvertedHarmonicOscillator 1 (cubeRoot ^ n) :=
  (spacelike_iff_isInvertedHarmonicOscillator _).mp (coloured_spacelike h)

end Physlib.QuantumMechanics.ComplexAction.TrialityCausalRegime
