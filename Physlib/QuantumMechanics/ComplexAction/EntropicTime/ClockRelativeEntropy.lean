/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
meta import Zil

/-!
# The entropic clock on the density operator: relative entropy + frequency-lapse Tolman (entanglement leg)

The scalar entropic-clock chain of `EntangledRegionFrequencyTimeDilation` (`entropicTimeRate`,
`frequencyLapse`) is here tied to the **operator-level entropic proper time** of `EntropicProperTime`, which
is the relative entropy of the actual density operators `MState`:

  `τ_ent = (ℏ/k_B T_∞)·D(ρ‖σ)`   (`entropicProperTimeMetric = scale · entropicGap`).

So the entropic clock's reading is the relative-entropy gap between the local density state `ρ` and the
reference `σ` — the entanglement/distinguishability of the region. This file connects the two:

* **§A — the clock is the relative-entropy gap.** `entropicTime_mono_gap`: a region whose state is more
  distinguishable from the reference (`D(ρ₁‖σ) ≤ D(ρ₂‖σ)` — more entangled/excited) accumulates more entropic
  proper time. `entropicProperTimeMetric_self` (reference state, `τ = 0`) is the zero of the clock.
* **§B — the frequency lapse is the Tolman lapse on the operator clock.** `entropicTime_lapse_tolman`:
  `(τ_ent / N)·N = τ_ent` with `N = frequencyLapse ω ω_∞ = ω/ω_∞` — the mode-frequency ratio is the
  gravitational lapse acting on the *relative-entropy* entropic time, the operator version of
  `entropicProperTimeLocalMetric_tolman`.
* **§C — denser ⟹ smaller lapse ⟹ larger local entropic time.** `entropicTime_local_antitone_lapse`: the
  local (redshifted) entropic time `τ_ent/N` grows as the lapse `N` shrinks. Composed with
  `regionFrequency_antitone` (a denser, bigger region has lower `ω`, hence smaller `N = ω/ω_∞`), the denser
  region carries a larger local entropic time — the Tolman conjugate of the slower *rate* `α·ω` of
  `EntangledRegionFrequencyTimeDilation` (rate `∝ N`, local accumulated value `∝ 1/N`).

**Honest layering.** Genuine operator facts: the entropic proper time is `scale·D(ρ‖σ)` on real density
operators (`MState`), monotone in the relative-entropy gap, and the Tolman lapse algebra is exact. The
identifications — the frequency ratio `ω/ω_∞` as the lapse `N`, and "denser/more-entangled ⟹ larger gap" —
are the modelling bridges (the residual freedom flagged as the loosest link). `entangledRegionSize ↔ MState
dimension d = 2ⁿ` (fermionic Fock dimension) is noted, not formalized here.

## References

* `Physlib` (`SpaceAndTime.EntropicProperTime` `entropicProperTimeMetric`/`entropicGap`/Tolman,
  `EntangledRegionFrequencyTimeDilation` `frequencyLapse`/`regionFrequency_antitone`). `QuantumInfo` `MState`.


-/

set_option autoImplicit false

open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockRelativeEntropy

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **[More relative entropy ⟹ more entropic time]** a region whose density state `ρ₂` is more
distinguishable from the reference `σ` than `ρ₁` (`D(ρ₁‖σ) ≤ D(ρ₂‖σ)` — more entangled/excited) accumulates
at least as much entropic proper time: `τ_ent` is monotone in the relative-entropy gap. -/
lemma entropicTime_mono_gap (U : EntropicTimeUnits) {ρ₁ ρ₂ σ : MState d}
    (h : entropicGap ρ₁ σ ≤ entropicGap ρ₂ σ) :
    entropicProperTimeMetric U ρ₁ σ ≤ entropicProperTimeMetric U ρ₂ σ := by
  unfold entropicProperTimeMetric
  exact mul_le_mul_of_nonneg_left h U.scale_pos.le


/-- **HJW ensemble freedom is invisible to the operator entropic clock.**  If two finite
pure-state ensembles mix to the same density operator, their explicit HJW purifications have
the same relative-entropy gap, the same metric entropic proper time against every reference
state, and the same von Neumann entropy.  Thus entropic time depends on the physical reduced
state, not on which ancilla basis/ensemble description realizes it. -/
theorem hjw_entropicObservables_decompositionInvariant
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : EntropicTimeUnits) (e : PEnsemble d α) (f : PEnsemble d β) (σ : MState d)
    (h : Ensemble.mix (e : MEnsemble d α) = Ensemble.mix (f : MEnsemble d β)) :
    entropicGap (MState.pure (ensemblePurification e)).traceRight σ =
        entropicGap (MState.pure (ensemblePurification f)).traceRight σ ∧
      entropicProperTimeMetric U (MState.pure (ensemblePurification e)).traceRight σ =
        entropicProperTimeMetric U (MState.pure (ensemblePurification f)).traceRight σ ∧
      Sᵥₙ (MState.pure (ensemblePurification e)).traceRight =
        Sᵥₙ (MState.pure (ensemblePurification f)).traceRight := by
  rw [ensemblePurification_traceRight, ensemblePurification_traceRight, h]
  exact ⟨rfl, rfl, rfl⟩


/-- **[Frequency-lapse Tolman invariant on the operator entropic time]** `(τ_ent / N)·N = τ_ent` with the
lapse `N = frequencyLapse ω ω_∞ = ω/ω_∞`: the mode-frequency ratio redshifts the *relative-entropy*
entropic proper time exactly as the gravitational lapse, the operator version of
`entropicProperTimeLocalMetric_tolman`. -/
lemma entropicTime_lapse_tolman (U : EntropicTimeUnits) (ρ σ : MState d) (ω ωInf : ℝ)
    (hN : frequencyLapse ω ωInf ≠ 0) :
    entropicProperTimeMetric U ρ σ / frequencyLapse ω ωInf * frequencyLapse ω ωInf
      = entropicProperTimeMetric U ρ σ :=
  div_mul_cancel₀ _ hN


/-- **[Smaller lapse ⟹ larger local entropic time]** the local redshifted entropic time `τ_ent / N` is
antitone in the lapse `N` (for `0 < N`). Composed with `regionFrequency_antitone` — a denser, bigger region
has lower `ω`, hence smaller `N = ω/ω_∞` — the denser region carries a *larger* local entropic time, the
Tolman conjugate of the slower rate `α·ω`. -/
lemma entropicTime_local_antitone_lapse (U : EntropicTimeUnits) (ρ σ : MState d)
    {N₁ N₂ : ℝ} (h0 : 0 < N₁) (h : N₁ ≤ N₂) :
    entropicProperTimeMetric U ρ σ / N₂ ≤ entropicProperTimeMetric U ρ σ / N₁ := by
  gcongr
  exact entropicProperTimeMetric_nonneg U ρ σ

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockRelativeEntropy

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockRelativeEntropy.hjw_entropicObservables_decompositionInvariant where
  formalizes @ "claim:relative-entropy-gap-metric-entropic-time-and-von-neumann-entropy-depend-only-on-the-reduced-density-state-not-its-finite-ensemble-decomposition",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
  supported_by @ "lean:QuantumInfo.Finite.entropicProperTimeMetric",
  caveat @ "epistemic:exact-decomposition-invariance-of-defined-density-operator-observables-not-a-proof-that-every-physical-clock-is-entropic"

zil_file_contract physlib.hjwEntropicClock where
  promises "The finite HJW ensemble freedom is gauge for the operator entropic clock: equal mixed states realized by different explicit ensemble purifications have identical relative-entropy gaps, metric entropic proper times, and von Neumann entropies."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
    "lean:Physlib.SpaceAndTime.EntropicProperTime.entropicGap",
    "lean:QuantumInfo.Finite.entropicProperTimeMetric"]
  forbids_substitutes ["claiming physical equivalence of distinct preparations beyond their common reduced state",
    "claiming an unconditional identification of relational or geometric time with entropic proper time"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockRelativeEntropy.hjw_entropicObservables_decompositionInvariant]

/- ZIL-END -/
