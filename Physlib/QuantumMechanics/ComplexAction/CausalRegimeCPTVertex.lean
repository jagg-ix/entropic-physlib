/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ActionAngleCausalRegimes
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering

/-!
# The causal regime is CPT-even: the QED vertex configuration is CPT-invariant

This extends `ActionAngleCausalRegimes` by linking the Nagao–Nielsen causal-regime classification to the
**CPT-even QED vertex** `p_f + p_γ = p_f'` — the support of the continuum `δ⁴(Σp)` that survives the continuum
limit (`PathIntegral.QEDFunctionalIntegralConstruction.free_continuum_limit`), whose CPT-evenness is
`FirstQuantizedQED.CPTOneLoopScattering.cpt_momentum_conservation_invariant`.

The bridge is exact: under the CPT momentum reversal `ω ↦ −ω`, the Lorentzian form is unchanged,
`lorentzianForm(−ω) = (Re ω)² − (Im ω)² = lorentzianForm(ω)`. So the **causal regime** — timelike / lightlike /
spacelike, i.e. harmonic / critical / inverted-harmonic (`CausalRegimes`) — of every momentum is **CPT-even**. The
vertex `δ⁴(Σp)` conservation being CPT-even (`δ⁴(−Σp) = δ⁴(Σp)`) and each leg's on-shell causal type being CPT-even
are two faces of the same `p ↦ −p` invariance: the entire on-shell vertex configuration (a **timelike** fermion
`p_f`, a **lightlike** photon `p_γ`, a **timelike** fermion `p_f'`, momentum-conserving) maps to its CPT conjugate
with identical causal structure.

* **§A — the causal regime is CPT-even.** **`lorentzianForm_neg`**; `timelike_neg_iff`, `spacelike_neg_iff`,
  `lightlike_neg_iff`; **`isHarmonicOscillator_neg_iff`**, `isInvertedHarmonicOscillator_neg_iff`.
* **§B — the CPT-even vertex configuration.** **`vertex_causal_configuration_cpt_even`** (the `δ⁴` conservation and
  each leg's causal type are jointly CPT-even), `reducedMomentum_regime_cpt_even`.

**Honest layering.** Exact `Complex`/`lorentzianForm` identities; reuses `cpt_momentum_conservation_invariant`,
the `CausalRegimes` trichotomy and `reducedMomentum`. ## References

* Links `ActionAngleCausalRegimes` / `ComplexOscillator.CausalRegimes` to
  `FirstQuantizedQED.CPTOneLoopScattering` (`free_continuum_limit`, `cpt_momentum_conservation_invariant`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalRegimeCPTVertex


/-- **The Lorentzian form is CPT-even** `lorentzianForm(−ω) = lorentzianForm(ω)` — the mass-shell form
`(Re ω)² − (Im ω)²` is unchanged under the CPT momentum reversal `ω ↦ −ω`. -/
lemma lorentzianForm_neg (ω : ℂ) : lorentzianForm (-ω) = lorentzianForm ω := by
  unfold lorentzianForm
  rw [Complex.neg_re, Complex.neg_im, neg_sq, neg_sq]

/-- **Timelike is CPT-even** — `ω ↦ −ω` preserves the timelike (underdamped / harmonic) regime. -/
lemma timelike_neg_iff (ω : ℂ) : timelike (-ω) ↔ timelike ω := by
  unfold timelike; rw [lorentzianForm_neg]

/-- **Spacelike is CPT-even** — `ω ↦ −ω` preserves the spacelike (overdamped / inverted) regime. -/
lemma spacelike_neg_iff (ω : ℂ) : spacelike (-ω) ↔ spacelike ω := by
  unfold spacelike; rw [lorentzianForm_neg]

/-- **Lightlike is CPT-even** — `ω ↦ −ω` preserves the lightlike (critical, `45°`) regime; the photon leg's
on-shell character is CPT-invariant. -/
lemma lightlike_neg_iff (ω : ℂ) : lightlike (-ω) ↔ lightlike ω := by
  unfold lightlike; rw [lorentzianForm_neg]

/-- **The harmonic-oscillator regime is CPT-even** — `IsHarmonicOscillator 1 (−ω) ⟺ IsHarmonicOscillator 1 ω`. -/
lemma isHarmonicOscillator_neg_iff (ω : ℂ) :
    IsHarmonicOscillator 1 (-ω) ↔ IsHarmonicOscillator 1 ω := by
  rw [← timelike_iff_isHarmonicOscillator, ← timelike_iff_isHarmonicOscillator, timelike_neg_iff]

/-- **The inverted-harmonic regime is CPT-even** — `IsInvertedHarmonicOscillator 1 (−ω) ⟺ … ω`. -/
lemma isInvertedHarmonicOscillator_neg_iff (ω : ℂ) :
    IsInvertedHarmonicOscillator 1 (-ω) ↔ IsInvertedHarmonicOscillator 1 ω := by
  rw [← spacelike_iff_isInvertedHarmonicOscillator, ← spacelike_iff_isInvertedHarmonicOscillator,
    spacelike_neg_iff]


/-- **The entire on-shell vertex configuration is CPT-even.** At the QED vertex `p_f + p_γ = p_f'` — the support of
the continuum `δ⁴(Σp)` surviving `free_continuum_limit` — the CPT reversal `p ↦ −p` preserves *both* the
momentum-conservation constraint (`cpt_momentum_conservation_invariant`) *and* the causal type of each leg: the
**timelike** fermion `ω_f`, the **lightlike** photon `ω_γ` and the **timelike** outgoing fermion `ω_f'` all keep
their regime. The vertex maps to its CPT conjugate with identical on-shell causal structure. -/
lemma vertex_causal_configuration_cpt_even (pf pγ pf' : ℝ) (ωf ωγ ωf' : ℂ) :
    ((-pf) + (-pγ) = (-pf') ↔ pf + pγ = pf')
      ∧ (timelike (-ωf) ↔ timelike ωf)
      ∧ (lightlike (-ωγ) ↔ lightlike ωγ)
      ∧ (timelike (-ωf') ↔ timelike ωf') :=
  ⟨cpt_momentum_conservation_invariant pf pγ pf', timelike_neg_iff ωf, lightlike_neg_iff ωγ,
    timelike_neg_iff ωf'⟩

/-- **The action-angle fermion momentum's regime is CPT-even** — a leg carried by the purely nonlinear
oscillator's allowed-region (timelike / harmonic) momentum `reducedMomentum` keeps its causal type under CPT. -/
lemma reducedMomentum_regime_cpt_even (I α τ q : ℝ) :
    timelike (-((reducedMomentum I α τ q : ℝ) : ℂ)) ↔ timelike ((reducedMomentum I α τ q : ℝ) : ℂ) :=
  timelike_neg_iff _

end Physlib.QuantumMechanics.ComplexAction.CausalRegimeCPTVertex
