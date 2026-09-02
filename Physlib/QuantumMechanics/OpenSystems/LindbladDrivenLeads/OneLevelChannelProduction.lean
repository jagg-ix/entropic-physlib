/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelCalibration
public import Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem
meta import Zil

/-!
# Strict entropy production along the one-level trajectory

The binary relative entropy of the occupation against the stationary reference has, along the one-level
relaxation `N(t) = f + (N₀-f)·exp(-2γt)`, the production law `d/dt D_bin(N(t)‖f) = -σ(t)` with

`σ(N, f) = 2γ(N - f)·[log(N/f) - log((1-N)/(1-f))]`.

This file establishes the two ingredients of the strict second law for this channel:

* `entropyProductionRate_pos` — the production rate `σ` is **strictly positive away from equilibrium**
  (`N ≠ f`), because `(N - f)` and the log-odds difference always share sign;
* `predictedOccupation_absDeviation_strictAnti` — the occupation deviation `|N(t) - f|` is **strictly
  decreasing**, so the trajectory relaxes monotonically to the calibrated fixed point.

`binaryKL_eq` records the explicit Bernoulli form used above. The exact derivative law
`d/dt D_bin(N(t)‖f) = -σ(t)` certifying `σ` as minus the time-derivative of the binary relative entropy
is `binaryKL_predictedOccupation_hasDerivAt` in `OneLevelChannelStrictArrow`.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Real
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
open Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem

/-- Explicit Bernoulli form of the binary relative entropy,
`D_bin(N‖f) = N·log(N/f) + (1-N)·log((1-N)/(1-f))`. -/
theorem binaryKL_eq (N f : ℝ) :
    binaryKL N f = N * Real.log (N / f) + (1 - N) * Real.log ((1 - N) / (1 - f)) := by
  unfold binaryKL klDivergence
  rw [Fin.sum_univ_two]
  simp [binaryDist]

/-- The relative-entropy production rate along the one-level trajectory (od6),
`σ(N, f) = 2γ(N - f)·[log(N/f) - log((1-N)/(1-f))]`. -/
def entropyProductionRate (γ N f : ℝ) : ℝ :=
  2 * γ * (N - f) * (Real.log (N / f) - Real.log ((1 - N) / (1 - f)))

/-- **Strict second law.** The entropy production rate is strictly positive away from equilibrium:
`(N - f)` and the log-odds difference `log(N/f) - log((1-N)/(1-f))` always carry the same sign. -/
theorem entropyProductionRate_pos {γ N f : ℝ} (hγ : 0 < γ)
    (hN0 : 0 < N) (hN1 : N < 1) (hf0 : 0 < f) (hf1 : f < 1) (hNf : N ≠ f) :
    0 < entropyProductionRate γ N f := by
  unfold entropyProductionRate
  rcases lt_or_gt_of_ne hNf with h | h
  · -- N < f : both factors negative
    have hA : N - f < 0 := by linarith
    have hlogNf : Real.log (N / f) < 0 :=
      Real.log_neg (by positivity) ((div_lt_one hf0).mpr h)
    have hlog1 : 0 < Real.log ((1 - N) / (1 - f)) :=
      Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
    have hprod : 0 < (N - f) * (Real.log (N / f) - Real.log ((1 - N) / (1 - f))) :=
      mul_pos_of_neg_of_neg hA (by linarith)
    have key : (0:ℝ) < γ * ((N - f) * (Real.log (N / f) - Real.log ((1 - N) / (1 - f)))) :=
      mul_pos hγ hprod
    nlinarith [key]
  · -- N > f : both factors positive
    have hA : 0 < N - f := by linarith
    have hlogNf : 0 < Real.log (N / f) := Real.log_pos ((one_lt_div hf0).mpr h)
    have hlog1 : Real.log ((1 - N) / (1 - f)) < 0 :=
      Real.log_neg (by positivity) ((div_lt_one (by linarith)).mpr (by linarith))
    have hprod : 0 < (N - f) * (Real.log (N / f) - Real.log ((1 - N) / (1 - f))) :=
      mul_pos hA (by linarith)
    have key : (0:ℝ) < γ * ((N - f) * (Real.log (N / f) - Real.log ((1 - N) / (1 - f)))) :=
      mul_pos hγ hprod
    nlinarith [key]

/-- **Bridge to the Grad-1958 collision production.** The one-level production rate is exactly twice the
sum of the two `gradCollisionProduction` terms — the occupied channel `(N, f)` and the empty channel
`(1-N, 1-f)`. This identifies `σ` as the repository's existing binary-collision entropy production
(`SpohnVariationalHTheorem.gradCollisionProduction`), so its positivity and equilibrium-vanishing are the
`gradCollisionProduction_nonneg` / `gradCollisionProduction_eq_zero_iff` facts, not a separate result. -/
theorem entropyProductionRate_eq_gradCollisionSum (γ N f : ℝ) :
    entropyProductionRate γ N f =
      2 * γ * (gradCollisionProduction N f + gradCollisionProduction (1 - N) (1 - f)) := by
  unfold entropyProductionRate gradCollisionProduction
  ring

/-- The signed occupation deviation from the stationary reference decays exactly exponentially. -/
theorem RateData.predictedOccupation_sub_occupation (r : RateData) (N₀ t : ℝ) :
    r.predictedOccupation N₀ t - r.occupation = (N₀ - r.occupation) * Real.exp (-2 * r.gamma * t) := by
  simp [RateData.predictedOccupation]

/-- **Monotone relaxation.** The occupation deviation `|N(t) - f|` is strictly decreasing in time, so
the trajectory approaches the calibrated fixed point monotonically (away from equilibrium). -/
theorem RateData.predictedOccupation_absDeviation_strictAnti (r : RateData) {N₀ : ℝ}
    (hne : N₀ ≠ r.occupation) :
    StrictAnti (fun t => |r.predictedOccupation N₀ t - r.occupation|) := by
  intro a b hab
  simp only [RateData.predictedOccupation_sub_occupation, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have habs : 0 < |N₀ - r.occupation| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hexp : Real.exp (-2 * r.gamma * b) < Real.exp (-2 * r.gamma * a) :=
    Real.exp_lt_exp.mpr (by nlinarith [r.gamma_pos])
  exact mul_lt_mul_of_pos_left hexp habs

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.entropyProductionRate_pos where
  supported_by @ "lean:gradCollisionProduction_eq_zero_iff",
  supported_by @ "lean:gradCollisionProduction_nonneg",
  formalizes @ "claim:the-one-level-relative-entropy-production-rate-is-strictly-positive-away-from-equilibrium",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation_absDeviation_strictAnti where
  formalizes @ "claim:the-one-level-occupation-deviation-from-the-stationary-reference-is-strictly-decreasing-so-the-trajectory-relaxes-monotonically-to-the-calibrated-fixed-point",
  epistemic_status @ "consistency-identity"

/- ZIL-END -/
