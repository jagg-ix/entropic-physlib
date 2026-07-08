/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Physlib.QFT.Wick.Consistency

/-!
# The Hyperbolic Unification: the Schmidt number is the rapidity coth

Formalizes the complex-action/entropic-time **Hyperbolic Unification** — *entanglement as rapidity* — which identifies the
imaginary action `S_I` (the entropic / "communicative" sector) with the bipartite **Schmidt number**
`K`, and `K` with an **effective thermal rapidity** `η_eff`:

  `S_I = ħ · log K`,    `K = coth η_eff`,    `e^{−S_I/ħ} = 1/K = tanh η_eff`.

This welds quantum-information entanglement onto the relativistic rapidity / light-cone structure of the
arc. With the Schmidt number `K = cosh η / sinh η = coth η` (`schmidtNumber`):

* `K = E/ξ` — the Schmidt number is the **inverse velocity** `bogoliubovEnergy(ξ)/ξ`
  (`schmidtNumber_eq_energy_over_momentum`, via `diamond_horizon_energy`), with `K > 1` for entangled
  states (`schmidtNumber_gt_one`);
* `S_I = ħ log K ≥ 0` (`entropicAction_nonneg`), vanishing iff `K = 1` — the **separable / reversible**
  limit (`reversible_iff_separable`);
* the **entanglement-suppression factor** `e^{−S_I/ħ} = tanh η = β` **is the boost velocity**
  (`suppression_eq_tanh`, `suppression_eq_diamond_velocity` `= ξ/E`), so the **path-integral weight**
  `‖e^{iS_R/ħ − S_I/ħ}‖ = tanh η = 1/K` (`pathIntegralWeight_eq_tanh`, via
  `Wick.Consistency.norm_complexActionWeight`).

So the document's `Amplitude = e^{iS_R/ħ}·e^{−S_I/ħ} = e^{iS_R/ħ}·tanh η_eff`: the entanglement-suppression
is the relativistic velocity, the Schmidt number is the inverse velocity `coth η`, and `S_I` is `ħ log`
of it. Entanglement (`K > 1`) is exactly a sub-luminal rapidity; the separable/reversible limit
(`K = 1`, `S_I = 0`) is the luminal `45°` cone where Bell correlations vanish (the boundary of the
CHSH spacelike face, `Bell.DeterministicBounds` / `Bell.ThreeFaces`).

* **§A — the Schmidt number as `coth η`** (`schmidtNumber`, `schmidtNumber_gt_one`,
  `schmidtNumber_eq_energy_over_momentum`).
* **§B — the entropic action `S_I = ħ log K`** (`entropicAction`, `entropicAction_nonneg`,
  `reversible_iff_separable`).
* **§C — the suppression factor is the boost velocity** (`suppression_eq_tanh`,
  `suppression_eq_diamond_velocity`, `pathIntegralWeight_eq_tanh`).
* **§D — the unification** (`hyperbolic_unification`).

## References

* complex-action/entropic-time Hyperbolic Unification "Rosetta Stone" (`S_I = ħ log K`, `K = coth η_eff`); the
  purity / Rényi-2 refinement `K = e^{S₂} = (Tr ρ_A²)⁻¹`. Repo dependencies: `CausalDiamond.Helicity`
  (`bogoliubovEnergy`, `diamond_horizon_energy`), `Physlib.QFT.Wick.Consistency`
  (`complexActionWeight`, `norm_complexActionWeight`), `Bell.DeterministicBounds`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QFT.Wick.Consistency

/-! ## §A — the Schmidt number is the rapidity `coth` -/

/-- **The Schmidt number** `K = coth η_eff = cosh η / sinh η` — the bipartite entanglement measure of
the Hyperbolic Unification, mapped to the effective thermal rapidity `η_eff`. -/
noncomputable def schmidtNumber (η : ℝ) : ℝ := Real.cosh η / Real.sinh η

/-- **[Entanglement ⟺ `K > 1`] `coth η > 1` for `η > 0`.** A non-trivial rapidity gives a Schmidt
number above `1` — an entangled state (irreversible, `S_I > 0`). -/
theorem schmidtNumber_gt_one (η : ℝ) (hη : 0 < η) : 1 < schmidtNumber η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  unfold schmidtNumber
  rw [lt_div_iff₀ hs, one_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq η, hs, Real.cosh_pos η]

/-- **[The Schmidt number is the inverse velocity] `K = E/ξ`.** With `E = cosh η = bogoliubovEnergy ξ`
(`diamond_horizon_energy`, the on-shell energy at momentum `ξ = sinh η`), the Schmidt number is
`E/ξ = 1/(ξ/E) = 1/β` — the inverse of the relativistic velocity. -/
theorem schmidtNumber_eq_energy_over_momentum (η : ℝ) :
    schmidtNumber η = bogoliubovEnergy (Real.sinh η) 1 / Real.sinh η := by
  unfold schmidtNumber
  rw [← diamond_horizon_energy]

/-! ## §B — the entropic action `S_I = ħ log K` -/

/-- **The entropic (imaginary) action** `S_I = ħ · log K` — the entanglement content of the
"communicative" sector, the `ħ log` of the Schmidt number. -/
noncomputable def entropicAction (ħ η : ℝ) : ℝ := ħ * Real.log (schmidtNumber η)

/-- **[`S_I ≥ 0`] the entropic action is non-negative** for `ħ ≥ 0`, `η > 0` (`K > 1 ⟹ log K > 0`) —
irreversibility is the presence of entanglement. -/
theorem entropicAction_nonneg (ħ η : ℝ) (hħ : 0 ≤ ħ) (hη : 0 < η) :
    0 ≤ entropicAction ħ η :=
  mul_nonneg hħ (Real.log_nonneg (le_of_lt (schmidtNumber_gt_one η hη)))

/-- **[Reversible ⟺ separable] `S_I = 0 ⟺ K = 1`** (for `ħ ≠ 0`). The imaginary action vanishes
exactly when the Schmidt number is `1` — the separable, reversible (standard-QM) limit. -/
theorem reversible_iff_separable (ħ η : ℝ) (hħ : ħ ≠ 0) (hK : 0 < schmidtNumber η) :
    entropicAction ħ η = 0 ↔ schmidtNumber η = 1 := by
  unfold entropicAction
  rw [mul_eq_zero, or_iff_right hħ]
  constructor
  · intro h
    have he := Real.exp_log hK
    rw [h, Real.exp_zero] at he
    exact he.symm
  · intro h; rw [h, Real.log_one]

/-! ## §C — the entanglement-suppression factor is the boost velocity -/

/-- **[Entanglement-suppression = boost velocity] `e^{−S_I/ħ} = tanh η = β`.** The path-amplitude
suppression factor `e^{−S_I/ħ} = 1/K` is exactly the relativistic velocity `tanh η_eff` — the
document's `Amplitude = e^{iS_R/ħ}·tanh η_eff`. -/
theorem suppression_eq_tanh (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) :
    Real.exp (-(entropicAction ħ η / ħ)) = Real.tanh η := by
  have hK : 0 < schmidtNumber η := by
    have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
    unfold schmidtNumber; positivity
  unfold entropicAction
  rw [show -(ħ * Real.log (schmidtNumber η) / ħ) = -Real.log (schmidtNumber η) from by field_simp]
  rw [Real.exp_neg, Real.exp_log hK, schmidtNumber, Real.tanh_eq_sinh_div_cosh, inv_div]

/-- **[The velocity is `ξ/E`] `tanh η = ξ / E`.** The boost velocity / suppression factor is the
momentum-to-energy ratio `sinh η / bogoliubovEnergy ξ` (`= β`, `diamond_horizon_energy`). -/
theorem suppression_eq_diamond_velocity (η : ℝ) :
    Real.tanh η = Real.sinh η / bogoliubovEnergy (Real.sinh η) 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, ← diamond_horizon_energy]

/-- **[The path-integral weight is the velocity] `‖e^{iS_R/ħ − S_I/ħ}‖ = tanh η = 1/K`.** The norm of
the complex-action/entropic-time path-integral weight (`Wick.Consistency.complexActionWeight`) with `S_I = ħ log K` is the
entanglement-suppression factor `tanh η_eff` — the relativistic velocity. -/
theorem pathIntegralWeight_eq_tanh (S_R ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) :
    ‖complexActionWeight S_R (entropicAction ħ η) ħ‖ = Real.tanh η := by
  rw [norm_complexActionWeight, suppression_eq_tanh ħ η hħ hη]

/-! ## §D — the unification -/

/-- **[The Hyperbolic Unification, assembled].** The Schmidt number `K = coth η_eff` is the inverse
relativistic velocity `E/ξ` (`schmidtNumber_eq_energy_over_momentum`), above `1` exactly when entangled
(`schmidtNumber_gt_one`); the imaginary action `S_I = ħ log K` is the entanglement content, vanishing in
the separable/reversible limit (`reversible_iff_separable`); and the entanglement-suppression factor
`e^{−S_I/ħ}` — the path-integral weight norm — **is** the boost velocity `tanh η_eff = ξ/E`
(`suppression_eq_tanh`, `pathIntegralWeight_eq_tanh`). Entanglement is rapidity: the Schmidt number, the
imaginary action, and the relativistic velocity are one hyperbolic structure. -/
theorem hyperbolic_unification (S_R ħ η : ℝ) (hħ : ħ ≠ 0) (hηnn : 0 ≤ ħ) (hη : 0 < η) :
    schmidtNumber η = bogoliubovEnergy (Real.sinh η) 1 / Real.sinh η
      ∧ 1 < schmidtNumber η
      ∧ 0 ≤ entropicAction ħ η
      ∧ Real.exp (-(entropicAction ħ η / ħ)) = Real.tanh η
      ∧ ‖complexActionWeight S_R (entropicAction ħ η) ħ‖ = Real.tanh η :=
  ⟨schmidtNumber_eq_energy_over_momentum η, schmidtNumber_gt_one η hη,
    entropicAction_nonneg ħ η hηnn hη, suppression_eq_tanh ħ η hħ hη,
    pathIntegralWeight_eq_tanh S_R ħ η hħ hη⟩

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

end
