/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt

/-!
# The α-channel Schmidt target and storage-ring reconstruction

`MuonAnomaly.RapidityFromSchmidt` showed the operating-point rapidity is *derived* from the Schmidt number `K`.
This file pins the value selected by the Schwinger `α` channel and proves the round-trip closes.
`MuonAnomaly.AnomalyRapidity` also reconstructs the operational Schmidt coordinate from the published
storage-ring Lorentz factor without mentioning `α` in its definition, but the magic operating point is
anomaly-dependent and therefore is not an independent prediction of the anomaly.

The Schwinger value `a = schwingerAnomaly α` (`= α/2π`) together with `a = K² − 1` forces

  `K = √(1 + schwingerAnomaly α)`   (`schmidtNumberFromAlpha`),

which at `α ≈ 1/137` is `K ≈ 1.00058` (`schmidtNumberFromAlpha_bounds`) — a Schmidt number just barely above `1`
(barely-entangled), the entanglement content of the muon's QED dressing. By construction it reproduces the
anomaly, `K² − 1 = a` (`schmidtNumberFromAlpha_sq_sub_one_eq_schwinger`), and the *full chain closes*:

  `a( η( K(α) ) ) = α/2π`   (`anomaly_chain_eq_schwinger`),  `K( η( K(α) ) ) = K(α)`   (round-trip).

So the entire structure `K → η → a → α` is self-consistent at `K = √(1 + α/2π)`. The separate `γ`
reconstruction gives `K ∈ (1.0005, 1.0006)` and checks the same target interval at the level of storage-ring
kinematics. This is not an anomaly-independent prediction: the magic operating point is selected using the
Thomas–BMT anomaly relation. What remains unproved is a first-principles QFT Schmidt-spectrum calculation,
direct entanglement tomography, or a genuinely independent determination of the anomaly from `K`.

* **§A — the target.** `schmidtNumberFromAlpha α = √(1 + schwingerAnomaly α)`; `schmidtNumberFromAlpha_sq`,
  `one_lt_schmidtNumberFromAlpha` (`K > 1`, valid Schmidt number), `schmidtNumberFromAlpha_bounds` (`≈ 1.00058`).
* **§B — the round-trip closes.** `schmidtNumberFromAlpha_sq_sub_one_eq_schwinger` (`K²−1 = a`),
  `schmidtNumber_rapidity_eq` (`K(η(K)) = K`), `anomaly_chain_eq_schwinger` (`a(η(K(α))) = α/2π`).
* **§C — two-reconstruction agreement.** `schmidtNumberFromAlpha_eq_schmidtNumberFromGamma` proves that
  the `α` and storage-ring `γ` reconstructions coincide whenever their reconstructed anomalies coincide;
  the theorem assumes that agreement explicitly.

**Honest layering.** `K = √(1+α/2π)` is *defined from* `α`, so that route alone is a consistency check.
The storage-ring reconstruction `K(γ) = γ/√(γ²−1)` is not definitionally built from `α`, but the magic
operating point is chosen from the anomaly-dependent Thomas–BMT cancellation. It therefore verifies
kinematic bookkeeping, not an independent `a_μ` prediction. Neither route is direct
QFT Schmidt tomography, and the 2025 theory update reports no statistically significant Standard-Model versus
experiment tension. The exact content here is the cross-channel identity and bounds, not a new-physics claim.

## References

* `a = K² − 1` ⟹ `K = √(1 + a)`, `a = α/2π` (Schwinger). Muon `g − 2` Collaboration,
  final 2025 measurement; R. Aliberti et al., Muon `g − 2` Theory Initiative update (2025). `Physlib`
  (`MuonAnomaly.RapidityFromSchmidt`, `MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_bounds`,
  `MuonAnomaly.AnomalyRapidity.fermilabMagicGamma_determines_schmidtNumber`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha


/-- **The Schmidt number forced by the Schwinger value** `K = √(1 + α/2π)` — the entanglement measure that
`a = K² − 1` and `a = α/2π` together demand; `≈ 1.00058` at `α ≈ 1/137` (barely-entangled). -/
noncomputable def schmidtNumberFromAlpha (α : ℝ) : ℝ := Real.sqrt (1 + schwingerAnomaly α)

/-- **[`K² = 1 + a` with `a = schwingerAnomaly α`]** the square of the target Schmidt number. -/
lemma schmidtNumberFromAlpha_sq (α : ℝ) (hα : 0 ≤ α) :
    (schmidtNumberFromAlpha α) ^ 2 = 1 + schwingerAnomaly α := by
  unfold schmidtNumberFromAlpha
  have hs : 0 ≤ schwingerAnomaly α := by
    rw [schwingerAnomaly]; exact div_nonneg hα (by positivity)
  rw [Real.sq_sqrt (by linarith)]

/-- **[`K > 1`]** the target Schmidt number is a valid (above-unity) Schmidt number for `α > 0`. -/
lemma one_lt_schmidtNumberFromAlpha (α : ℝ) (hα : 0 < α) : 1 < schmidtNumberFromAlpha α := by
  have hpos : 0 < schwingerAnomaly α := by
    rw [schwingerAnomaly]; exact div_pos hα (by positivity)
  unfold schmidtNumberFromAlpha
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (1 + schwingerAnomaly α) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)

/-- **[`K ≈ 1.00058` at `α ≈ 1/137`]** the numerical target — a Schmidt number just above `1`. -/
lemma schmidtNumberFromAlpha_bounds :
    1.0005 < schmidtNumberFromAlpha ((1 : ℝ) / 137) ∧ schmidtNumberFromAlpha ((1 : ℝ) / 137) < 1.0006 := by
  have hb := MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_bounds
  unfold schmidtNumberFromAlpha
  refine ⟨?_, ?_⟩
  · rw [show (1.0005 : ℝ) = Real.sqrt (1.0005 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hb.1]
  · rw [show (1.0006 : ℝ) = Real.sqrt (1.0006 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_lt_sqrt (by linarith [hb.1])
    nlinarith [hb.2]


/-- **[`K² − 1 = a`]** the target Schmidt number reproduces the Schwinger anomaly (consistency check). -/
lemma schmidtNumberFromAlpha_sq_sub_one_eq_schwinger (α : ℝ) (hα : 0 ≤ α) :
    (schmidtNumberFromAlpha α) ^ 2 - 1 = schwingerAnomaly α := by
  rw [schmidtNumberFromAlpha_sq α hα]; ring

/-- **[Round-trip `K(η(K)) = K`]** mapping the target Schmidt number to its rapidity and back is the
identity — the inverse map of `MuonAnomaly.RapidityFromSchmidt` instantiated at `K = √(1+α/2π)`. -/
lemma schmidtNumber_rapidity_eq (α : ℝ) (hα : 0 < α) :
    schmidtNumber (rapidity (schmidtNumberFromAlpha α)) = schmidtNumberFromAlpha α :=
  schmidtNumber_rapidity (schmidtNumberFromAlpha α) (one_lt_schmidtNumberFromAlpha α hα)

/-- **[The full chain closes: `a(η(K(α))) = α/2π`]** starting from the target Schmidt number `K(α)`, deriving
its rapidity `η`, and evaluating the anomaly returns the Schwinger value `α/2π` — the entire structure
`K → η → a → α` is self-consistent at `K = √(1 + α/2π)`. -/
lemma anomaly_chain_eq_schwinger (α : ℝ) (hα : 0 < α) :
    anomaly (rapidity (schmidtNumberFromAlpha α)) = schwingerAnomaly α := by
  rw [anomaly_rapidity (schmidtNumberFromAlpha α) (one_lt_schmidtNumberFromAlpha α hα)]
  exact schmidtNumberFromAlpha_sq_sub_one_eq_schwinger α hα.le

/-! ## C. Agreement of the α and storage-ring γ reconstructions -/

/-- If the anomaly reconstructed from `α` agrees with a supplied storage-ring Lorentz
factor, then their reconstructed operational Schmidt numbers agree exactly. Positivity removes the otherwise
possible sign ambiguity after equating the squares. The hypothesis explicitly assumes the anomaly agreement;
the conclusion is therefore a consistency theorem, not independent empirical confirmation. -/
lemma schmidtNumberFromAlpha_eq_schmidtNumberFromGamma
    (α γ : ℝ) (hα : 0 < α) (hγ : 1 < γ)
    (hchannels : schwingerAnomaly α = magicAnomalyFromGamma γ) :
    schmidtNumberFromAlpha α = schmidtNumberFromGamma γ := by
  have hαsq := schmidtNumberFromAlpha_sq α hα.le
  have hγdef := schmidtNumberFromGamma_sq_sub_one γ hγ
  have hαpos : 0 < schmidtNumberFromAlpha α :=
    lt_trans one_pos (one_lt_schmidtNumberFromAlpha α hα)
  have hγpos : 0 < schmidtNumberFromGamma γ :=
    lt_trans one_pos (one_lt_schmidtNumberFromGamma γ hγ)
  nlinarith

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha

end
