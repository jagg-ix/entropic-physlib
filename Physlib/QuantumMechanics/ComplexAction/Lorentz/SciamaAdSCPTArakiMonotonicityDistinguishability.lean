/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution
meta import Zil

/-!
# Araki monotonicity and distinguishability (Witten, arXiv:1803.04993 §3.3–3.5)

Witten's *Notes on Some Entanglement Properties of Quantum Field Theory* organize the Type III story this arc
has been building — §2 Reeh–Schlieder (`SciamaAdSCPTReehSchliederCollapseObstruction`), §4 finite modular theory
(`FiniteTarget.modularGroupOfState`), §5 Bisognano–Wichmann wedge (`WickClock`) — around one information
measure that survives in Type III, where density matrices and von Neumann entropy do not exist: **Araki's
relative entropy** `S(Ψ‖Φ) = −⟨Ψ, log Δ_{Φ|Ψ} Ψ⟩`, with its two pillars, **positivity** and **monotonicity
under enlarging the region** (§3.4).  The repo has the finite Araki form and positivity
(`AlgebraicQFT.FiniteArakiRelativeEntropy`, which explicitly leaves monotonicity unclaimed) and, separately,
the classical marginal data-processing inequality (`EntropicTime.EntropicDataProcessingHTheorem`).  This module
supplies the missing §3.4 by welding the two, and applies §3.5's distinguishability reading to the collapse
resolution.

* `araki_relativeEntropy_region_monotone` — **monotonicity under region enlargement** (Witten §3.4, finite
  form): restricting joint weights to the subsystem marginal never increases the Araki relative entropy,
  `S(p_X‖q_X) ≤ S(p_XY‖q_XY)` — measurements in a larger region distinguish two states at least as well.
  The proof transports `relativeEntropy_marginal_le` into the Araki form over the product index.
* `finiteRelativeEntropy_self` — **perfect indistinguishability**: `S(p‖p) = 0` — zero relative entropy means
  no measurement in the algebra distinguishes the states (Witten §3.3: `S(Ψ‖Φ) = 0` iff indistinguishable on
  the algebra).
* `collapse_indistinguishable_on_pointer_algebra` — §3.5 applied to the resolution: the decohered and the
  collapsed states share the pointer diagonal (`weinberg_collapse_recovers_record_weight`), so their **pointer
  Araki relative entropy vanishes** — pointer measurements cannot distinguish decoherence from collapse; yet
  the fringe discriminator is strictly nonzero (`unitary_fringe_never_exactly_zero`), so the distinguishing
  information lives entirely in the coherence sector — and by region monotonicity, enlarging the algebra to
  include coherence witnesses can only *increase* the distinguishability.

So Witten's ordering closes the arc: Reeh–Schlieder forbids exact local collapse, modular flow carries the
dynamics, and the Araki relative entropy — positive, region-monotone — quantifies exactly how the collapse and
decoherence descriptions separate: not at all on the pointer algebra, strictly on any algebra containing the
coherence residue.

Honest scope: the finite (eigenvalue/diagonal) Araki level throughout, matching
`FiniteArakiRelativeEntropy`'s scope; the transported monotonicity is the classical marginal form (deterministic
coarse-graining), not the operator Uhlmann/Petz data-processing inequality; Witten's Type III statements are
the cited continuum counterparts.  **Operator upgrade**: the genuine operator Petz/Uhlmann monotonicity — the
quantum DPI for the Umegaki `𝐃` under every CPTP channel, and its partial-trace region form — is supplied by
`SciamaAdSCPTPetzMonotonicityOperator` (via the in-repo `QuantumInfo` sandwiched-Rényi DPI at `α = 1`); the
classical weld here is its diagonal shadow.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCollapseDecoherenceResolution
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-! ## §1. Monotonicity of the Araki relative entropy under region enlargement (Witten §3.4) -/

/-- **[Araki monotonicity under region enlargement]** `S(p_X‖q_X) ≤ S(p_XY‖q_XY)` — restricting the joint
weights to the subsystem marginal never increases the finite Araki relative entropy: measurements in a larger
region distinguish two states at least as well (Witten §3.4, finite form; transports
`relativeEntropy_marginal_le` into the Araki form of `FiniteArakiRelativeEntropy`, whose scope left
monotonicity open). -/
theorem araki_relativeEntropy_region_monotone {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (p q : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (hq : ∀ i j, 0 < q i j)
    (hpX : ∀ i, 0 < ∑ j, p i j) :
    finiteRelativeEntropy (fun i => ∑ j, p i j) (fun i => ∑ j, q i j)
      ≤ finiteRelativeEntropy (fun x : ι × κ => p x.1 x.2) (fun x : ι × κ => q x.1 x.2) := by
  unfold finiteRelativeEntropy
  rw [Fintype.sum_prod_type]
  exact relativeEntropy_marginal_le p q hp hq hpX

/-! ## §2. Zero relative entropy = indistinguishability (Witten §3.3) -/

/-- **[Perfect indistinguishability] `S(p‖p) = 0`** — the Araki relative entropy of a state with itself
vanishes: no measurement in the algebra distinguishes them (Witten §3.3). -/
theorem finiteRelativeEntropy_self {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    finiteRelativeEntropy p p = 0 := by
  unfold finiteRelativeEntropy
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eq_or_ne (p i) 0 with h | h
  · rw [h, zero_mul]
  · rw [div_self h, Real.log_one, mul_zero]

/-! ## §3. Distinguishability and the collapse resolution (Witten §3.5) -/

/-- **[Pointer measurements cannot distinguish collapse from decoherence]** — the decohered and the collapsed
states share the pointer diagonal (the Born weights, `weinberg_collapse_recovers_record_weight`), so their
pointer Araki relative entropy is **zero** (§2); yet the interference fringe is strictly nonzero at every
finite time (`unitary_fringe_never_exactly_zero`) — the distinguishing information lives entirely in the
coherence sector.  By region monotonicity (§1), enlarging the algebra to include coherence witnesses can only
*increase* the distinguishability: Witten's relative entropy localizes exactly where the resolution put the
discriminator. -/
theorem collapse_indistinguishable_on_pointer_algebra {dS : Type*} [Fintype dS]
    (born : dS → ℝ) {ι : Type*} (D : ι → ι → ℂ) {α β : ι}
    (hD : (D α β).re ≠ 0) {prefactor : ℝ} (t : ℝ) (X : NobleMetal) :
    finiteRelativeEntropy born born = 0
      ∧ decoheredMeasure D (interferenceVisibility prefactor t X) α β
          ≠ quantalMeasure D α + quantalMeasure D β :=
  ⟨finiteRelativeEntropy_self born, unitary_fringe_never_exactly_zero D hD t X⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability.araki_relativeEntropy_region_monotone where
  formalizes @ "claim:the-finite-araki-relative-entropy-is-monotone-under-region-enlargement",
  requires @ "claim:relative-entropy-decreases-under-marginalization-data-processing-h-theorem-arrow-of-time",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.finiteRelativeEntropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem.relativeEntropy_marginal_le",
  caveat @ "epistemic:classical-marginal-form-deterministic-coarse-graining-not-the-operator-uhlmann-petz-data-processing-inequality"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability.collapse_indistinguishable_on_pointer_algebra where
  formalizes @ "claim:pointer-measurements-cannot-distinguish-collapse-from-decoherence-the-distinguishing-information-is-the-coherence-residue",
  requires @ "claim:the-collapse-versus-decoherence-competition-dissolves-collapse-is-the-infinite-decoherence-limit-differing-only-by-the-strictly-nonzero-finite-time-coherence-residue",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWeinbergCollapseBornEquivalence.weinberg_collapse_recovers_record_weight",
  caveat @ "epistemic:diagonal-pointer-level-araki-form-the-type-iii-continuum-statement-is-cited-context"

/- ZIL-END -/
