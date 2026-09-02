/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction
public import Physlib.QFT.PathIntegral.WickClock
meta import Zil

/-!
# The spectrum condition: bounded energy makes evolution a Euclidean contraction (Witten §2.3)

The Reeh–Schlieder derivation (`SciamaAdSCPTReehSchliederCollapseObstruction`) carries the vacuum-cyclicity
hypothesis `hcyc` with the honest caveat "supplied by the spectrum condition".  This module formalizes the
**mechanism** at the eigenvalue level (Witten §2.3, *Vectors of Bounded Energy-Momentum*): positive energy
makes the complex-time evolution `e^{−i(E/ℏ)z}` a **contraction on the lower (Euclidean) half-plane** — the
boundedness that, in the continuum, makes correlation functions boundary values of holomorphic functions and
proves the vacuum cyclic for every open region.

* `spectrum_condition_lower_half_contraction` — **the core**: for `E/ℏ ≥ 0` and `Im z ≤ 0`,
  `‖e^{−i(E/ℏ)z}‖ ≤ 1` — the spectrum condition is exactly what bounds the analytically-continued evolution on
  the Euclidean side (`z = t − iτ`, `τ ≥ 0`).
* `euclidean_weight_le_one` — the Wick-rotated instance: at `z = −iτ` (`wickRotate`), the evolution is the real
  heat kernel `e^{−Eτ/ℏ} ≤ 1` — the Euclidean weight never amplifies.
* `wedgeModular_le_one` — the §5 link: for `κ/ℏ ≥ 0` the wedge-modular eigenvalue obeys `Δ ≤ 1` — the
  positive-boost-energy spectrum condition bounds the modular operator on the vacuum side, the eigenvalue face
  of `Δ ≤ 1` on the standard subspace.
* `spectrum_condition_powers_reehSchlieder` — the bundle: the Euclidean contraction (the §2.3 mechanism)
  together with the conditional Reeh–Schlieder obstruction (`reehSchlieder_no_local_collapse`): boundedness of
  the continued evolution is what, in the continuum, discharges the cyclicity hypothesis and yields "no
  nonzero local operator annihilates the vacuum".

Honest scope: the contraction bound is exact at the eigenvalue level; the continuum step — analytic
continuation of `e^{izH}ψ` for spectrum-bounded `H`, density of the continued orbit, hence cyclicity — is
Witten's §2.2–2.3 argument, cited: the cyclicity hypothesis of the RS modules is *not* discharged here, its
mechanism is exhibited.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTSpectrumConditionAnalyticity

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTReehSchliederCollapseObstruction
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QFT.PathIntegral

/-! ## §1. The core contraction: positive energy bounds the continued evolution -/

/-- **[The spectrum condition makes evolution a Euclidean contraction]** — for `E/ℏ ≥ 0` and `Im z ≤ 0`,
`‖e^{−i(E/ℏ)z}‖ ≤ 1`: positive energy bounds the analytically-continued evolution on the lower (Euclidean)
half-plane `z = t − iτ`, `τ ≥ 0` — the §2.3 mechanism behind Reeh–Schlieder. -/
theorem spectrum_condition_lower_half_contraction (E ℏ : ℝ) (hE : 0 ≤ E / ℏ)
    {z : ℂ} (hz : z.im ≤ 0) :
    ‖reversiblePhaseC E ℏ z‖ ≤ 1 := by
  unfold reversiblePhaseC
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Complex.I * ((E / ℏ : ℝ) : ℂ) * z).re = (E / ℏ) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  exact mul_nonpos_of_nonneg_of_nonpos hE hz

/-- **[The Euclidean weight never amplifies]** — at Wick-rotated time `z = −iτ` (`τ ≥ 0`) the continued
evolution is the real heat kernel, bounded by `1`: the Wick-rotated instance of the contraction. -/
theorem euclidean_weight_le_one (E ℏ τ : ℝ) (hE : 0 ≤ E / ℏ) (hτ : 0 ≤ τ) :
    ‖reversiblePhaseC E ℏ (wickRotate τ)‖ ≤ 1 := by
  refine spectrum_condition_lower_half_contraction E ℏ hE ?_
  simp [wickRotate]
  exact hτ

/-! ## §2. The §5 link: the modular eigenvalue is bounded by one -/

/-- **[`Δ ≤ 1` from the spectrum condition]** — for `κ/ℏ ≥ 0` the wedge-modular eigenvalue obeys
`Δ = e^{−2πκ/ℏ} ≤ 1`: positive boost energy bounds the modular operator on the vacuum side — the eigenvalue
face of `Δ ≤ 1` on the standard subspace. -/
theorem wedgeModular_le_one (κ ℏ : ℝ) (hκ : 0 ≤ κ / ℏ) :
    wedgeModularEigenvalue κ ℏ ≤ 1 := by
  unfold wedgeModularEigenvalue
  rw [Real.exp_le_one_iff, neg_nonpos]
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc (0 : ℝ) ≤ 2 * Real.pi * (κ / ℏ) := mul_nonneg hπ hκ
    _ = 2 * Real.pi * κ / ℏ := by ring

/-! ## §3. The bundle: the mechanism behind Reeh–Schlieder -/

/-- **[The spectrum condition powers Reeh–Schlieder]** — the Euclidean contraction (the §2.3 mechanism: bounded
energy bounds the continued evolution) together with the conditional obstruction: given the cyclicity the
continuum argument extracts from that boundedness, no nonzero local operator annihilates the vacuum
(`reehSchlieder_no_local_collapse`).  The analytic-continuation step from the contraction to the cyclicity is
Witten §2.2–2.3, cited — the hypothesis's mechanism, exhibited at the eigenvalue level. -/
theorem spectrum_condition_powers_reehSchlieder
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Preorder ι] (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcyc : IsCyclic (N.alg (N.compl O)) Ω)
    (E ℏ : ℝ) (hE : 0 ≤ E / ℏ) {z : ℂ} (hz : z.im ≤ 0) :
    ‖reversiblePhaseC E ℏ z‖ ≤ 1
      ∧ (∀ a ∈ N.alg O, a ≠ 0 → 0 < ‖a Ω‖) :=
  ⟨spectrum_condition_lower_half_contraction E ℏ hE hz,
    fun _ haM ha => reehSchlieder_no_local_collapse N O Ω hdual hcyc haM ha⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTSpectrumConditionAnalyticity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTSpectrumConditionAnalyticity.spectrum_condition_lower_half_contraction where
  formalizes @ "claim:the-spectrum-condition-makes-the-analytically-continued-evolution-a-contraction-on-the-euclidean-half-plane",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhaseC",
  caveat @ "epistemic:eigenvalue-level-bound-the-analytic-continuation-to-cyclicity-is-the-cited-continuum-argument"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTSpectrumConditionAnalyticity.spectrum_condition_powers_reehSchlieder where
  formalizes @ "claim:the-euclidean-contraction-of-bounded-energy-is-the-mechanism-that-supplies-reeh-schlieder-cyclicity",
  requires @ "claim:over-a-reeh-schlieder-vacuum-no-nonzero-local-operator-implements-an-exact-collapse-annihilation",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  caveat @ "epistemic:the-cyclicity-hypothesis-is-not-discharged-its-mechanism-is-exhibited-at-the-eigenvalue-level"

/- ZIL-END -/
