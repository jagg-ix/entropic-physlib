/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Channels.CPTP
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability
meta import Zil

/-!
# Operator Petz monotonicity: the quantum data-processing inequality for the Umegaki relative entropy
(Witten, arXiv:1803.04993 §3.4/§4.3, operator form)

The Witten arc's monotonicity theorem (`SciamaAdSCPTArakiMonotonicityDistinguishability`) was the *classical
marginal* form, with the honest caveat "not the operator Uhlmann–Petz data-processing inequality".  Deep search
shows the **operator theorem is already proved in the repo**: the in-repo `QuantumInfo` package carries the
sandwiched-Rényi data-processing inequality for all `α ≥ 1` (`sandwichedRenyiEntropy_DPI`, with the `α = 1`
continuity limit `sandwichedRenyiEntropy_DPI_eq_one`), and the Umegaki quantum relative entropy is definitionally
its `α = 1` point (`qRelativeEnt ρ σ = D̃_1(ρ‖σ)`).  What was missing is only the *phrasing*: no theorem stated
the DPI for `𝐃` itself, and none instantiated it at the partial-trace channel.  This module supplies both:

* `qRelativeEnt_DPI` — **the operator Petz/Uhlmann monotonicity**: `𝐃(Φρ‖Φσ) ≤ 𝐃(ρ‖σ)` for every CPTP channel
  `Φ` — quantum relative entropy contracts under quantum operations (Witten §4.3; Petz, Uhlmann, Lieb–Ruskai).
* `qRelativeEnt_region_monotone` — **the operator region monotonicity** (Witten §3.4, operator form): at the
  partial-trace channel `Φ = tr_{d₂}` (`CPTPMap.traceRight`), restricting both states to the subsystem never
  increases the relative entropy, `𝐃(ρ|_A‖σ|_A) ≤ 𝐃(ρ‖σ)` — measurements in the larger system distinguish at
  least as well, now at full operator level (non-commuting states, not only diagonal weights).
* `witten_monotonicity_operator_and_classical` — the operator theorem and the classical marginal shadow
  (`araki_relativeEntropy_region_monotone`) side by side: the §3.4 monotonicity at both levels, the classical
  weld now certified as the diagonal shadow of a genuinely-proved operator inequality.

Honest scope: the operator content (operator convexity, the `α ↓ 1` continuity) is `QuantumInfo`'s proof,
reused; this module's contribution is the Umegaki phrasing, the partial-trace instantiation, and the weld to
the Witten arc.  The Type III Araki data-processing (the `CatichaTypeIIIUnboundedDynamics` supplied datum)
remains the continuum counterpart, cited.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability

/-! ## §1. The operator Petz/Uhlmann monotonicity -/

/-- **[Operator Petz monotonicity — the quantum data-processing inequality]** `𝐃(Φρ‖Φσ) ≤ 𝐃(ρ‖σ)` — the
Umegaki quantum relative entropy contracts under every CPTP channel (Witten §4.3; Petz–Uhlmann–Lieb–Ruskai).
The operator content is `QuantumInfo`'s sandwiched-Rényi DPI at its `α = 1` continuity point, of which the
Umegaki entropy is the definitional value. -/
theorem qRelativeEnt_DPI {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    qRelativeEnt (Φ ρ) (Φ σ) ≤ qRelativeEnt ρ σ :=
  sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-! ## §2. The operator region monotonicity -/

/-- **[Operator region monotonicity]** `𝐃(ρ|_A‖σ|_A) ≤ 𝐃(ρ‖σ)` — instantiating the operator DPI at the
partial-trace channel (`CPTPMap.traceRight`): restricting both states to the subsystem never increases the
quantum relative entropy.  Witten §3.4 at full operator level — the statement whose classical marginal shadow
was `araki_relativeEntropy_region_monotone`. -/
theorem qRelativeEnt_region_monotone {d₁ d₂ : Type*}
    [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState (d₁ × d₂)) :
    qRelativeEnt ρ.traceRight σ.traceRight ≤ qRelativeEnt ρ σ :=
  sandwichedRenyiEntropy_DPI_eq_one ρ σ CPTPMap.traceRight

/-! ## §3. Operator and classical monotonicity, welded -/

/-- **[Witten §3.4 monotonicity at both levels]** — the operator region monotonicity (§2, genuine
Uhlmann–Petz content) together with its classical diagonal shadow
(`araki_relativeEntropy_region_monotone`): the classical weld of the Witten arc is now certified as the
diagonal shadow of a proved operator inequality. -/
theorem witten_monotonicity_operator_and_classical {d₁ d₂ : Type*}
    [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ σ : MState (d₁ × d₂))
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (p q : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (hq : ∀ i j, 0 < q i j)
    (hpX : ∀ i, 0 < ∑ j, p i j) :
    qRelativeEnt ρ.traceRight σ.traceRight ≤ qRelativeEnt ρ σ
      ∧ finiteRelativeEntropy (fun i => ∑ j, p i j) (fun i => ∑ j, q i j)
          ≤ finiteRelativeEntropy (fun x : ι × κ => p x.1 x.2) (fun x : ι × κ => q x.1 x.2) :=
  ⟨qRelativeEnt_region_monotone ρ σ,
    araki_relativeEntropy_region_monotone p q hp hq hpX⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator.qRelativeEnt_DPI where
  formalizes @ "claim:the-umegaki-quantum-relative-entropy-contracts-under-every-cptp-channel-the-operator-petz-uhlmann-data-processing-inequality",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:sandwichedRenyiEntropy_DPI_eq_one",
  caveat @ "epistemic:finite-dimensional-operator-theorem-the-type-iii-araki-data-processing-is-the-cited-continuum-counterpart"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTPetzMonotonicityOperator.qRelativeEnt_region_monotone where
  formalizes @ "claim:the-quantum-relative-entropy-is-monotone-under-region-restriction-at-full-operator-level",
  requires @ "claim:the-umegaki-quantum-relative-entropy-contracts-under-every-cptp-channel-the-operator-petz-uhlmann-data-processing-inequality",
  supported_by @ "lean:CPTPMap.traceRight",
  caveat @ "epistemic:partial-trace-channel-instantiation-of-the-operator-dpi"

/- ZIL-END -/
