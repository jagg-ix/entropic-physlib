/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval

/-!
# Transformations that produce the kinematic or the entropic invariant from the metric

`EntropicTime.MetricCommonRootEntropicTime` showed the single metric `S`-norm `m = u² − v² = ξ/E` roots both the
kinematic rest mass and the entropic time `τ_ent = binEntropy((1 − m)/2)`. This file **inspects which
transformations produce each invariant** from `m`, and classifies them.

There are three classes of transformation, distinguished by what they do to the metric:

## 1. Metric-preserving boost → the kinematic invariant

The Lorentz boost (bosonic Bogoliubov transformation, `𝒱ᵀ S 𝒱 = S`) **preserves the metric `S`-norm**
— the rest mass `t² − x²` is the invariant (`boost_preserves_kinematic`), while the velocity
`m = tanh θ` is the coordinate, composing by the relativistic velocity-addition law
(`kinematic_velocity_addition`). So the metric-*preserving* transformation gives the **kinematic**
structure: rest mass invariant, velocity orbit. To *extract* the rest mass one boosts to the rest
frame.

## 2. The occupation–entropy map → the entropic invariant

The entropic time is obtained from `m` by the (non-invertible) **occupation–entropy functional**
`m ↦ v² = (1 − m)/2 ↦ binEntropy(v²) = τ_ent` (`entropic_from_metric`). This is *not* a symmetry — it
is the entropy extraction. It is maximal at the symmetric point `m = 0` (`entropic_maximal_at_metric_zero`,
`v² = ½`) and vanishes at the metric-null `m = ±1` (`entropic_zero_at_metric_luminal`, the light
cone).

## 3. The Wick rotation → sector exchange (kinematic ↔ entropic)

Multiplication by `i` (Wick rotation, real-time ↔ imaginary-time) **flips the metric sign**,
`lorentzianForm(i q) = − lorentzianForm(q)` (`wick_exchanges_sectors`): it exchanges the timelike
(kinematic, real) and spacelike (entropic, imaginary) sectors — the bridge between the two.

## The link between the classes

The kinematic boost is *compatible* with the entropic structure: composing sub-luminal velocities
`|m| < 1` (the entropy-*positive*, timelike region `τ_ent > 0`) stays sub-luminal
(`boost_preserves_entropic_region`), and the metric-null `|m| = 1` (`τ_ent = 0`, the light cone) is
the invariant boundary. So the kinematic transformation preserves the entropic regions.

## Main results

* `boost_preserves_kinematic`, `kinematic_velocity_addition` — the kinematic class (metric-preserving).
* `entropic_from_metric`, `entropic_maximal_at_metric_zero`, `entropic_zero_at_metric_luminal` — the
  entropic class (occupation–entropy map).
* `wick_exchanges_sectors` — the sector-exchange class (Wick rotation).
* `boost_preserves_entropic_region` — the kinematic boost preserves the entropy-positive region.
* `transformation_classification` — the bundled classification.

## References

* N. N. Bogoliubov 1947; K. Nagao, H. B. Nielsen, arXiv:1902.01424. P. T. Nam, M. Napiórkowski,
  J. P. Solovej, J. Funct. Anal. **270** (2016) 4340. doi:10.1016/j.jfa.2015.12.007.
* This development: `EntropicTime.MetricCommonRootEntropicTime`, `Rapidity.PoincarePolarMinkowskiInterval`,
  `TimeOperator.HyperbolicPoincareLorentzMisra`, `ComplexDelta.Convergence`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Real
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations

/-! ## §1 — metric-preserving boost → the kinematic invariant -/

/-- **The boost preserves the kinematic invariant** (the rest mass = metric `S`-norm `t² − x²`). -/
theorem boost_preserves_kinematic (θ t x : ℝ) :
    (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2 :=
  lorentzBoost_preserves_form θ t x

/-- **The velocity composes by relativistic addition** `m = tanh θ`: the kinematic coordinate under
the boost. -/
theorem kinematic_velocity_addition (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) :=
  tanh_add a b

/-! ## §2 — the occupation–entropy map → the entropic invariant -/

/-- **The entropic invariant from the metric value** `τ_ent = binEntropy((1 − m)/2)`, `m = ξ/E`: the
occupation–entropy functional. -/
theorem entropic_from_metric (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2) :=
  entropicTime_eq_binEntropy_velocity ξ Δ

/-- **Kinematic entropic time** `binEntropy((1 − m)/2)` with boost velocity
`m = tanh θ` (rapidity θ). The entropy produced at a given metric velocity is
the entropic-time readout of a boost. -/
def kinematicEntropy (θ : ℝ) : ℝ := Real.binEntropy ((1 - Real.tanh θ) / 2)

/-- **The kinematic entropic time is a valid non-negative entropy production.**
Since `m = tanh θ ∈ (-1,1)`, the occupation `(1 − m)/2` lies in `(0,1)`, where
binary entropy is non-negative. -/
theorem kinematicEntropy_nonneg (θ : ℝ) : 0 ≤ kinematicEntropy θ := by
  have h1 := Real.tanh_lt_one θ
  have h2 := Real.neg_one_lt_tanh θ
  exact Real.binEntropy_nonneg (by linarith) (by linarith)

/-- **[Bogoliubov / Nagao–Nielsen link]** When the boost velocity equals the
metric `S`-norm, `m = tanh θ = ξ/E`, the kinematic entropy
`binEntropy((1 − m)/2)` equals `bogoliubovEntropicTime ξ Δ`, the genuine
Bogoliubov entropic time of the mode. -/
theorem kinematicEntropy_eq_bogoliubovEntropicTime (θ ξ Δ : ℝ)
    (hm : Real.tanh θ = ξ / bogoliubovEnergy ξ Δ) :
    kinematicEntropy θ = bogoliubovEntropicTime ξ Δ := by
  unfold kinematicEntropy
  rw [entropic_from_metric, hm]

/-- **Entropy is maximal at the symmetric metric point** `m = 0` (`ξ = 0`, `v² = ½`). -/
theorem entropic_maximal_at_metric_zero (Δ : ℝ) :
    bogoliubovEntropicTime 0 Δ = Real.binEntropy (1 / 2) :=
  bogoliubov_entropicTime_at_zero_xi Δ

/-- **Entropy vanishes at the metric-null** `m = ±1` (the light cone / massless limit). -/
theorem entropic_zero_at_metric_luminal (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0
      ↔ ξ / bogoliubovEnergy ξ Δ = 1 ∨ ξ / bogoliubovEnergy ξ Δ = -1 :=
  entropicTime_zero_iff_metric_luminal ξ Δ

/-! ## §3 — the Wick rotation → sector exchange (kinematic ↔ entropic) -/

/-- **The Wick rotation flips the metric sign** `lorentzianForm(i q) = − lorentzianForm(q)`: it
exchanges the timelike (kinematic) and spacelike (entropic) sectors. -/
theorem wick_exchanges_sectors (q : ℂ) :
    lorentzianForm (Complex.I * q) = - lorentzianForm q :=
  lorentzianForm_mul_I q

/-! ## §4 — the link: the kinematic boost preserves the entropic regions -/

/-- **The boost preserves the entropy-positive region** `|m| < 1` (sub-luminal, timelike,
`τ_ent > 0`): composing velocities keeps `|m| < 1`. The metric-null `|m| = 1` (`τ_ent = 0`, the light
cone) is the invariant boundary. So the kinematic transformation is compatible with the entropic
structure. -/
theorem boost_preserves_entropic_region {m₁ m₂ : ℝ} (h₁ : |m₁| < 1) (h₂ : |m₂| < 1) :
    |(m₁ + m₂) / (1 + m₁ * m₂)| < 1 :=
  velocity_addition_lt_one h₁ h₂

/-! ## §5 — the classification -/

/-- **The transformation classification.** From the metric `S`-norm `m`:

* **(kinematic)** the metric-preserving boost preserves the rest mass `t² − x²`, and the velocity
  `m = tanh θ` composes by relativistic addition;
* **(entropic)** the occupation–entropy map gives `τ_ent = binEntropy((1 − m)/2)`;
* **(sector exchange)** the Wick rotation `× i` flips the metric, exchanging the kinematic and
  entropic sectors.

Metric-*preserving* transformations give the kinematic invariant; the occupation–entropy *map* gives
the entropic invariant; the metric-*flipping* Wick rotation bridges them. -/
theorem transformation_classification (θ t x ξ Δ a b : ℝ) (q : ℂ) :
    ((lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2)
      ∧ (Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b))
      ∧ (bogoliubovEntropicTime ξ Δ = Real.binEntropy ((1 - ξ / bogoliubovEnergy ξ Δ) / 2))
      ∧ (lorentzianForm (Complex.I * q) = - lorentzianForm q) :=
  ⟨boost_preserves_kinematic θ t x, kinematic_velocity_addition a b,
   entropic_from_metric ξ Δ, wick_exchanges_sectors q⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations

end

end
