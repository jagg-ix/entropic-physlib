/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight

/-!
# Causal-set quantum gravity decoheres like the Caldeira–Leggett open system

This links the **Sorkin causal-set quantum-gravity path integral** (`SorkinCausalSetGravityPathIntegral`) directly
to the **Caldeira–Leggett / Nishimura–Watanabe** decoherence arc: `CaldeiraLeggettDecoherence` (the thermal-bath
suppression `e^{−φ}`), `CaldeiraLeggettOhmicRenormalization` (the Ohmic frequency renormalization `renormFreqSq`),
`ComplexSaddleDecoherence` (the complex-saddle magnitude `|ρ_S| = e^{−Re A}`, arXiv:2408.16627) and
`CaldeiraLeggettInfluenceFunctional` (the Feynman–Vernon modulus `e^{−W_R}`, arXiv:2503.20699).

The causal-set gravity weight supplies the discrete Einstein–Hilbert action as the real phase; its **entropic
action `S_I` is left free**. Feeding in each open-system decoherence action makes the causal-set path integral's
modulus *coincide with that open system's decoherence weight*:

* `S_I = φ` (Caldeira–Leggett thermal exponent) ⟹ modulus `= caldeiraLeggettSuppression = e^{−φ}`;
* `S_I = Re A` (complex-saddle decoherence, 2408.16627) ⟹ modulus `= rhoMagnitude = e^{−Re A}`;
* `S_I = W_R` (influence-functional decoherence, 2503.20699) ⟹ modulus `= ‖feynmanVernonWeight‖`.

So the quantum-gravity sum over causal sets, coupled to a Caldeira–Leggett environment, decoheres *identically* to
that environment — one entropic weight. The **free-bath limit `γ = 0`** ties in
`CaldeiraLeggettOhmicRenormalization`: it simultaneously un-renormalizes the frequency (`renormFreqSq = ω_b²`),
kills the decoherence (`φ = 0`) and makes the causal-set path integral **unitary** — the reversible limit across
gravity, dissipation and decoherence at once.

* **§A — causal-set gravity = Caldeira–Leggett suppression.** **`causalSet_gravity_eq_caldeiraLeggett_suppression`**,
  **`causalSet_gravity_caldeiraLeggett_diagonal_unitary`**.
* **§B — causal-set gravity = the Nishimura–Watanabe decoherence weights.**
  **`causalSet_gravity_eq_rhoMagnitude`** (2408.16627), **`causalSet_gravity_eq_influenceFunctional`** (2503.20699).
* **§C — the free-bath reversible limit (Ohmic renormalization).** **`causalSet_gravity_freeBath_reversible`**.

**Honest layering.** Exact identities routing each open-system decoherence action through the shared
`kuikenWeight`; the decoherence physics is developed in the respective modules and reused, not re-derived.

## References

* Reuses `CaldeiraLeggettDecoherence`, `CaldeiraLeggettOhmicRenormalization`, `ComplexSaddleDecoherence`,
  `CaldeiraLeggettInfluenceFunctional`, `SorkinCausalSetGravityPathIntegral` on `ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
open Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettInfluenceFunctional
open Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalSetGravityCaldeiraLeggettLink


/-- **Causal-set gravity decoheres by the Caldeira–Leggett suppression** — the causal-set QG path integral with the
Caldeira–Leggett thermal-bath decoherence exponent `φ = 2Mγk_BTτξ²` as its entropic action has modulus exactly the
`CaldeiraLeggettDecoherence.caldeiraLeggettSuppression = e^{−φ}`: the discrete geometry decoheres like the
Caldeira–Leggett open system. -/
lemma causalSet_gravity_eq_caldeiraLeggett_suppression (N N₀ N₁ N₂ M γ kB T τ ξ : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂)
        (caldeiraLeggettDecoherence M γ kB T τ ξ) 1‖
      = caldeiraLeggettSuppression M γ kB T τ ξ := by
  rw [causalSet_gravity_is_fifth]
  simp only [caldeiraLeggettSuppression, kuikenWeight, div_one]

/-- **On the diagonal the causal-set gravity path integral is unitary** — with zero path separation (`ξ = 0`) the
Caldeira–Leggett exponent vanishes, so the causal-set QG weight has unit modulus: no decoherence of the diagonal
(Born) sector. -/
lemma causalSet_gravity_caldeiraLeggett_diagonal_unitary (N N₀ N₁ N₂ M γ kB T τ : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂)
        (caldeiraLeggettDecoherence M γ kB T τ 0) 1‖ = 1 := by
  rw [causalSet_gravity_eq_caldeiraLeggett_suppression, caldeiraLeggettSuppression_diagonal]


/-- **Causal-set gravity = the complex-saddle reduced-density magnitude (2408.16627)** — with the decoherence
quadratic form `Re A = reADiag` as its entropic action, the causal-set QG weight's modulus is
`ComplexSaddleDecoherence.rhoMagnitude = e^{−Re A}`: the geometry decoheres like the complex-saddle reduced density
matrix. -/
lemma causalSet_gravity_eq_rhoMagnitude (N N₀ N₁ N₂ J K x y : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂) (reADiag J K x y) 1‖
      = rhoMagnitude J K x y := by
  rw [causalSet_gravity_is_fifth, ← rhoMagnitude_eq_kuiken]

/-- **Causal-set gravity = the Feynman–Vernon influence functional modulus (2503.20699)** — with the
influence-functional decoherence exponent `W_R = (2Mγ/β) ξ² t` as its entropic action, the causal-set QG weight's
modulus equals the Caldeira–Leggett Feynman–Vernon influence functional's modulus. -/
lemma causalSet_gravity_eq_influenceFunctional (N N₀ N₁ N₂ S_R M γ β ξ t : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂)
        (decoherenceExponentIF M γ β ξ t) 1‖
      = ‖feynmanVernonWeight S_R (decoherenceExponentIF M γ β ξ t) 1‖ := by
  rw [causalSet_gravity_is_fifth, ← caldeiraLeggett_feynmanVernon_is_kuiken]


/-- **Decoupling the environment is the reversible limit across gravity, dissipation and decoherence** — at zero
coupling `γ = 0` the Ohmic frequency renormalization vanishes (`CaldeiraLeggettOhmicRenormalization.renormFreqSq
= ω_b²`, the bare frequency), the Caldeira–Leggett decoherence exponent vanishes (`φ = 0`), and the causal-set
quantum-gravity path integral is **unitary** (unit modulus). One `γ` controls dissipation, decoherence and the
loss of unitarity together. -/
lemma causalSet_gravity_freeBath_reversible
    (N N₀ N₁ N₂ ωb ωcut NE M kB T τ ξ : ℝ) (n : ℕ) :
    renormFreqSq ωb 0 ωcut NE n = ωb ^ 2
      ∧ caldeiraLeggettDecoherence M 0 kB T τ ξ = 0
      ∧ ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂)
          (caldeiraLeggettDecoherence M 0 kB T τ ξ) 1‖ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [renormFreqSq, couplingSq]
  · simp [caldeiraLeggettDecoherence]
  · rw [show caldeiraLeggettDecoherence M 0 kB T τ ξ = 0 by simp [caldeiraLeggettDecoherence]]
    exact causalSet_bdg_real_unitary N N₀ N₁ N₂ 1

end Physlib.QuantumMechanics.ComplexAction.CausalSetGravityCaldeiraLeggettLink
