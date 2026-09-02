/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TrialityCausalRegime

/-!
# The action-angle turning point and colour triality are the same causal dichotomy

This links `ActionAngleCausalRegimes` (the purely nonlinear oscillator's turning-point structure) to
`TrialityCausalRegime` (the `ℤ/3` colour centre): both partition into the *same* two causal regimes.

* **Physical face** — timelike / harmonic oscillator: the **classically-allowed** action-angle motion (`R > 0`, real
  momentum `reducedMomentum`) and the **colour singlet** (`3 ∣ n`, `cubeRoot^n = 1`) are both timelike, both
  `IsHarmonicOscillator 1`.
* **Confined face** — spacelike / inverted harmonic oscillator: the **classically-forbidden** tunneling motion
  (`R < 0`, imaginary momentum `nnReducedMomentum`) and the **coloured** state (`3 ∤ n`) are both spacelike, both
  `IsInvertedHarmonicOscillator 1`.

So the oscillator's turning point `R = 0` and the triality light cone `lorentzianForm(ωⁿ) = 0` are two faces of one
`lorentzianForm` dichotomy: **tunneling under the barrier is the confinement regime**, and **oscillatory
(on-shell) motion is the colour-singlet regime**. The Nagao–Nielsen Wick rotation `p ↦ i·p`
(`reducedMomentum_wick_isInverted`) that carries the allowed regime to the forbidden one is the same `HO ↔ IHO`
swap (`wick_swaps_HO_IHO`) that distinguishes singlet from coloured.

* **`allowed_singlet_both_harmonicOscillator`** — the physical face (both HO).
* **`forbidden_coloured_both_invertedOscillator`** — the confined face (both IHO).

**Honest layering.** Exact regime identities reusing `reducedMomentum_isHarmonicOscillator`,
`nnReducedMomentum_isInvertedHarmonicOscillator`, `colourSinglet_isHarmonicOscillator`,
`coloured_isInvertedHarmonicOscillator`. The correspondence is the shared `lorentzianForm` causal class; the
tunneling↔confinement reading is the structural analogy (the "Three Faces"), not a dynamical identification.

## References

* Links `ActionAngleCausalRegimes` to `TrialityCausalRegime` on `ComplexOscillator.CausalRegimes`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.ActionAngleCausalRegimes
open Physlib.QuantumMechanics.ComplexAction.TrialityCausalRegime

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ActionAngleTrialityRegime

/-- **The physical face** — classically-allowed action-angle motion (`R > 0`) and the colour singlet (`3 ∣ n`) are
both harmonic oscillators (timelike): on-shell oscillatory motion and the colour singlet share the physical
regime. -/
lemma allowed_singlet_both_harmonicOscillator (I α τ q : ℝ)
    (hR : 0 < 2 * I / τ - q ^ (α + 1) / τ ^ 2) {n : ℤ} (hn : (3 : ℤ) ∣ n) :
    IsHarmonicOscillator 1 ((reducedMomentum I α τ q : ℝ) : ℂ)
      ∧ IsHarmonicOscillator 1 (cubeRoot ^ n) :=
  ⟨reducedMomentum_isHarmonicOscillator I α τ q hR, colourSinglet_isHarmonicOscillator hn⟩

/-- **The confined face** — classically-forbidden tunneling (`R < 0`, imaginary momentum) and a coloured state
(`3 ∤ n`) are both inverted harmonic oscillators (spacelike): tunneling under the barrier and colour confinement
share the unphysical regime. -/
lemma forbidden_coloured_both_invertedOscillator (I α τ q : ℝ)
    (hR : 2 * I / τ - q ^ (α + 1) / τ ^ 2 < 0) {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n) :
    IsInvertedHarmonicOscillator 1 (nnReducedMomentum I α τ q)
      ∧ IsInvertedHarmonicOscillator 1 (cubeRoot ^ n) :=
  ⟨nnReducedMomentum_isInvertedHarmonicOscillator I α τ q hR, coloured_isInvertedHarmonicOscillator hn⟩

end Physlib.QuantumMechanics.ComplexAction.ActionAngleTrialityRegime
