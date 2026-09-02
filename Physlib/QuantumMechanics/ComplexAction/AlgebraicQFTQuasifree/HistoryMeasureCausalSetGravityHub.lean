/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral

/-!
# Integrating the AQFT quasi-free state with sum-over-histories and causal-set gravity (entropic hub)

Integrates the von-Neumann-algebraic AQFT of Labuschagne–Majewski (the quasi-local net, quasi-free states) with
the repository's **sum-over-histories** (`QuantumMeasureHistoryHilbert`) and **causal-set gravity path integral**
(`SorkinCausalSetGravityPathIntegral`). The common ground is the entropic weight `kuikenWeight = e^{−·/·}` that
already carries the quasi-free state (`quasifreeWeight = e^{−s/2}`), confinement, and the complex-action path
integral.

The Dowker–Johnston–Sorkin **decoherence functional** `D(α,β)` is the correlation kernel of the sum-over-histories
quantum measure `μ(α) = Re D(α,α)`; the quasi-free two-point function is exactly such a positive-semidefinite
Gram kernel. Here:

* the **quantum measure is non-negative** `μ(α) ≥ 0` (`quantalMeasure_nonneg`, from the strong positivity of the
  decoherence functional) — a genuine (quantum) probability;
* the **Gaussian weight of the quantum measure is the entropic weight** `e^{−μ(α)/2} = kuikenWeight 2 (μ α)`
  (`historyMeasureWeight`, `historyMeasureWeight_is_kuiken`), bounded by `1` (`historyMeasureWeight_le_one`) —
  the sum-over-histories measure sits on the same `kuikenWeight` hub as the quasi-free state
  (`quasifreeWeight = e^{−s/2}`), confinement, and the complex-action weight;
* the **causal-set gravity path-integral modulus is the same entropic weight**
  `‖e^{(i/ℏ)·ℏ·S_BDG − S_I/ℏ}‖ = kuikenWeight ℏ S_I` (`causalSet_bdg_modulus_is_kuiken`), so the sum-over-histories
  quantum measure and the Benincasa–Dowker causal-set gravity action share one hub
  (`history_measure_and_gravity_share_hub`).

So the AQFT quasi-free two-point function (a decoherence-functional Gram kernel), the sum-over-histories quantum
measure, and the causal-set gravity path integral are one entropic-weight structure: `kuikenWeight = e^{−·/·}`,
with the real (imaginary-action / entropy-production) part the suppression and the imaginary part the phase.

* **§A — the quantum measure is non-negative** (`quantalMeasure_nonneg`).
* **§B — the history measure weight is the entropic hub** (`historyMeasureWeight`, `_is_kuiken`, `_le_one`).
* **§C — sum-over-histories and causal-set gravity share the hub** (`history_measure_and_gravity_share_hub`).

**Honest layering.** The non-negativity of the quantum measure and the identification of its Gaussian weight with
`kuikenWeight` are exact (reusing `IsDecoherenceFunctional.posSemidef` and `kuikenWeight`); the causal-set gravity
modulus is the reused `causalSet_bdg_modulus_is_kuiken`. The GNS Hilbert-space realization of the quasi-free state
as a decoherence functional (`gram_isDecoherenceFunctional`), and the full path-integral sum, are recorded links,
not re-derived here. ## References

* R. Dowker, S. Johnston, R.D. Sorkin (quantum measure / decoherence functional); Benincasa–Dowker (causal-set
  action). Repo carriers: `QuantumMeasureHistoryHilbert` (`IsDecoherenceFunctional`, `quantalMeasure`),
  `SorkinCausalSetGravityPathIntegral` (`causalSet_bdg_modulus_is_kuiken`),
  `PathIntegral.ComplexActionPathIntegralWeight` (`kuikenWeight`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HistoryMeasureCausalSetGravityHub

variable {ι : Type*} {D : ι → ι → ℂ}


/-- **[The sum-over-histories quantum measure is non-negative] `μ(α) = Re D(α,α) ≥ 0`.** The strong positivity
(positive-semidefiniteness) of the decoherence functional applied to the single history `{α}` gives a
non-negative quantum measure — a genuine quantum probability. -/
lemma quantalMeasure_nonneg [DistribLattice ι] [OrderBot ι] (h : IsDecoherenceFunctional D)
    (α : ι) : 0 ≤ quantalMeasure D α := by
  have hpos := h.posSemidef {α} (fun _ => 1)
  simpa [Finset.sum_singleton, quantalMeasure, map_one] using hpos


/-- **The Gaussian weight of the quantum measure** `e^{−μ(α)/2}` — the quasi-free / entropic weight of the
sum-over-histories quantum measure `μ(α) = Re D(α,α)`. -/
noncomputable def historyMeasureWeight (D : ι → ι → ℂ) (α : ι) : ℝ :=
  Real.exp (-(quantalMeasure D α) / 2)

/-- **[The history measure weight is the entropic `kuikenWeight`] `e^{−μ(α)/2} = kuikenWeight 2 (μ α)`.** The
Gaussian weight of the sum-over-histories quantum measure is the complex-action entropic weight
`kuikenWeight c Π = e^{−Π/c}` at `c = 2` — the same hub carrying the quasi-free state (`e^{−s/2}`), confinement,
and the path integral. -/
lemma historyMeasureWeight_is_kuiken (α : ι) :
    historyMeasureWeight D α = kuikenWeight 2 (quantalMeasure D α) := by
  unfold historyMeasureWeight kuikenWeight
  rw [neg_div]

/-- **[The history measure weight is a suppression] `e^{−μ(α)/2} ≤ 1`.** Since the quantum measure is
non-negative, its Gaussian weight is a bona-fide entropic suppression bounded by `1`. -/
lemma historyMeasureWeight_le_one [DistribLattice ι] [OrderBot ι] (h : IsDecoherenceFunctional D)
    (α : ι) : historyMeasureWeight D α ≤ 1 := by
  unfold historyMeasureWeight
  rw [Real.exp_le_one_iff]
  have := quantalMeasure_nonneg h α
  linarith


/-- **[The sum-over-histories quantum measure and the causal-set gravity path integral share the entropic hub].**
For a decoherence functional `D` (the quasi-free / history correlation kernel) and Benincasa–Dowker causal-set
gravity parameters:

* the Gaussian weight of the quantum measure is `kuikenWeight 2 (μ α)`;
* the causal-set gravity path-integral weight has modulus `kuikenWeight ℏ S_I`.

Both the AQFT quasi-free / sum-over-histories measure and the causal-set gravity action live on the one entropic
weight `kuikenWeight = e^{−·/·}` — the imaginary-action (entropy-production) suppression common to quantum theory
and quantum gravity in this framework. -/
lemma history_measure_and_gravity_share_hub (α : ι) (N N₀ N₁ N₂ S_I ℏ : ℝ) :
    historyMeasureWeight D α = kuikenWeight 2 (quantalMeasure D α)
      ∧ ‖complexActionPathIntegralWeight (ℏ * bdgAction2D N N₀ N₁ N₂) S_I ℏ‖ = kuikenWeight ℏ S_I :=
  ⟨historyMeasureWeight_is_kuiken α, causalSet_bdg_modulus_is_kuiken N N₀ N₁ N₂ S_I ℏ⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HistoryMeasureCausalSetGravityHub

end
