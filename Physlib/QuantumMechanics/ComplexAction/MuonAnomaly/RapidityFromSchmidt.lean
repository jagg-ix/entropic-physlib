/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation -/

/-!
# Equating Schwinger dynamics with operating-point momentum kinematics: `α = 2π(K² − 1)`

Two independent expressions for the muon anomaly `a` meet here:

* **dynamics** — the verified QED Schwinger term `a = α/(2π)` (`schwingerAnomaly`), which at `α ≈ 1/137`
  gives `a ≈ 0.001162`, ≈ 99.6 % of the measured `a = 0.00116592` (`schwinger_anomaly_value`);
* **kinematics** — the operating-point momentum / rapidity relation `a = 1/sinh²η = K² − 1`
  (`MuonAnomaly.AnomalyRapidity`, Schmidt number `K = coth η`).

**Setting them equal and isolating** yields a *new equation* tying the fine-structure constant to the
operating-point rapidity / Schmidt number:

  `α = 2π/sinh²η = 2π (K² − 1)`,  equivalently  `K² = 1 + α/(2π)`.

So the fine-structure constant is `2π` times the **entanglement (Schmidt) defect** at the muon's operating-point
rapidity. Numerically, with `α = 1/137.036`: `sinh²η = 2π/α ≈ 861`, `γ = cosh η ≈ 29.36`; and
`2π·a` reproduces `α` (exactly at the Schwinger level, with a `≈ 0.4 %` excess when the *measured* `a` is
used — that excess `2π(a − α/2π)` is `2π` times the beyond-Schwinger anomaly: higher QED loops + hadronic +
electroweak + any new physics, i.e. the home of the `Δa_μ` discrepancy).

* **§A — the isolation.** `alpha_isolated` (`α = 2π·anomaly η`), `alpha_eq_twoPi_schmidt_defect`
  (`α = 2π(K²−1)`), `schmidt_sq_eq_one_add_schwinger` (`K² = 1 + schwingerAnomaly α`).
* **§B — the value.** `schwinger_anomaly_value`: `a = α/(2π) ∈ (0.001161, 0.001162)` at `α ≈ 1/137`.

**Honest layering.** This is an *exact algebraic consequence* of equating the (verified) Schwinger value with
the (exact) operating-point momentum kinematics — a reparametrization that writes `α` as `2π(K²−1)`. It is **not** a
derivation of `α`: the operating-point rapidity is itself fixed by `a = α/2π`, so the relation is consistent by
construction, not predictive of the coupling. Its content is structural — the same dimensionless number plays
the QED coupling, the rapidity defect, and the Schmidt-number entanglement — and it cleanly isolates the
beyond-Schwinger remainder.

## References

* J. Schwinger 1948 (`a = α/2π`); Thomas–BMT operating-point momentum (`a = 1/(γ²−1) = K²−1`). `Physlib`
  (`FirstQuantizedQED.AnomalousMagneticMoment.schwingerAnomaly`, `MuonAnomaly.AnomalyRapidity.anomaly`/`schmidtNumber`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation


/-- **[The isolated equation]** `α = 2π·a(η)` with `a(η) = anomaly η`: equating the Schwinger anomaly
`schwingerAnomaly α` with the operating-point momentum anomaly `anomaly η` and solving for the fine-structure
constant. -/
lemma alpha_isolated (α η : ℝ) (hη : 0 < η) (h : schwingerAnomaly α = anomaly η) :
    α = 2 * Real.pi * anomaly η := by
  have hs : Real.sinh η ≠ 0 := (Real.sinh_pos_iff.mpr hη).ne'
  unfold schwingerAnomaly anomaly at h
  rw [anomaly]
  field_simp [Real.pi_ne_zero, hs] at h ⊢
  linarith

/-- **[`α = 2π(K² − 1)`]** the fine-structure constant is `2π` times the Schmidt-number (entanglement) defect
`K² − 1` at the muon's operating-point rapidity — the new equation. -/
lemma alpha_eq_twoPi_schmidt_defect (α η : ℝ) (hη : 0 < η)
    (h : schwingerAnomaly α = anomaly η) :
    α = 2 * Real.pi * ((schmidtNumber η) ^ 2 - 1) := by
  rw [alpha_isolated α η hη h, anomaly_eq_schmidt_sq_sub_one η hη]

/-- **[`K² = 1 + α/(2π)`]** the Schmidt number squared at the operating-point rapidity is one plus the Schwinger
anomaly — the entanglement measure read off from the fine-structure constant. -/
lemma schmidt_sq_eq_one_add_schwinger (α η : ℝ) (hη : 0 < η)
    (h : schwingerAnomaly α = anomaly η) :
    (schmidtNumber η) ^ 2 = 1 + schwingerAnomaly α := by
  have hm := anomaly_eq_schmidt_sq_sub_one η hη
  rw [hm] at h
  linarith


/-- **[The Schwinger value]** `a = α/(2π) ∈ (0.001161, 0.001162)` at the empirical `α ≈ 1/137` — the leading
QED anomaly, ≈ 99.6 % of the measured `a = 0.00116592`. -/
lemma schwinger_anomaly_value :
    0.001161 < schwingerAnomaly ((1 : ℝ) / 137) ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.001162 :=
  MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_bounds

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation

end

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt -/

/-!
# Exact inversion of the Schmidt/rapidity coordinate

The Schmidt number coordinate `K = coth η` is invertible on the physical branch: `η` is a genuine function
of `K`,

  `η(K) = arccoth K = arsinh(1/√(K² − 1))`   (`rapidity`),

and this inverse map is exact — `K` is recovered:

  `K(η(K)) = K`   (`schmidtNumber_rapidity`),  `a(η(K)) = K² − 1`   (`anomaly_rapidity`).

This permits the coordinate order `K → η(K) → a`. It does **not** establish that physical `K` is primitive
or independently known. In particular, `alpha_from_schmidt` assumes
`schwingerAnomaly α = anomaly (rapidity K)` and then solves that premise for `α`; it is a consistency identity,
not a first-principles derivation of the fine-structure constant.

* **§A — the inverse map.** `rapidity K = arsinh(1/√(K²−1))`; `sinh_rapidity`, `rapidity_pos`,
  and the key `schmidtNumber_rapidity` (`K(η(K)) = K`) — `η` is a function of `K`, exactly.
* **§B — the conditional rewrite.** `anomaly_rapidity` (`a = K²−1` in the `K` coordinate);
  `alpha_from_schmidt` (`α = 2π(K²−1)` under the explicit Schwinger/anomaly equality premise).

**Honest layering.** What this settles is purely mathematical: `η(K)` is an exact inverse coordinate and the
round trip closes. It does not settle the epistemic direction of the physics. The storage-ring reconstruction
`K(γ) = γ/√(γ²−1)` makes `K` operational, but the magic `γ` is selected through the anomaly-dependent
Thomas–BMT cancellation; it is not an anomaly-independent prediction. What remains open is deriving `K`
from a specified QFT bipartition, measuring it by direct Schmidt tomography, or otherwise fixing it without
using the anomaly relation that is then recovered.

## References

* `Real.arsinh` (inverse `sinh`); `coth`-inversion `η = arccoth K`. Muon `g − 2` Collaboration,
  final 2025 measurement; M. Sorbara for the collaboration, RICAP-24 (2025). `Physlib`
  (`MuonAnomaly.SchwingerRapidityEquation`, `MuonAnomaly.AnomalyRapidity.anomaly`/`schmidtNumber`,
  `MuonAnomaly.AnomalyRapidity.fermilabMagicGamma_determines_schmidtNumber`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt


/-- **The operating-point rapidity as a function of the Schmidt number** `η(K) = arccoth K = arsinh(1/√(K²−1))` — the
inverse of `K = coth η`, making `η` a *derived* quantity once `K` is given. -/
noncomputable def rapidity (K : ℝ) : ℝ := Real.arsinh (1 / Real.sqrt (K ^ 2 - 1))

/-- **[`sinh η(K) = 1/√(K²−1)`]** the rapidity sinh recovered from the Schmidt number (`= ξ`, the momentum). -/
lemma sinh_rapidity (K : ℝ) :
    Real.sinh (rapidity K) = 1 / Real.sqrt (K ^ 2 - 1) := by
  unfold rapidity; exact Real.sinh_arsinh _

/-- **[`η(K) > 0`]** the derived operating-point rapidity is positive for `K > 1`. -/
lemma rapidity_pos (K : ℝ) (hK : 1 < K) : 0 < rapidity K := by
  have hK2 : 0 < K ^ 2 - 1 := by nlinarith
  rw [← Real.sinh_pos_iff, sinh_rapidity]
  exact div_pos one_pos (Real.sqrt_pos.mpr hK2)

/-- **[The anomaly from `K`]** `a(η(K)) = K² − 1` — the operating-point momentum anomaly evaluated at the derived
rapidity returns the Schmidt-number defect (with `η` a *function* of `K`, not a free parameter). -/
lemma anomaly_rapidity (K : ℝ) (hK : 1 < K) :
    anomaly (rapidity K) = K ^ 2 - 1 := by
  have hK2 : 0 < K ^ 2 - 1 := by nlinarith
  unfold anomaly
  rw [sinh_rapidity, div_pow, one_pow, Real.sq_sqrt hK2.le, one_div_one_div]

/-- **[The inverse map is exact: `K(η(K)) = K`]** the Schmidt number of the reconstructed rapidity returns
`K`. This proves an exact coordinate inverse; it does not prove that physical `K` is primitive or independently
measured. -/
lemma schmidtNumber_rapidity (K : ℝ) (hK : 1 < K) :
    schmidtNumber (rapidity K) = K := by
  have hpos : 0 < rapidity K := rapidity_pos K hK
  have hsq : (schmidtNumber (rapidity K)) ^ 2 = K ^ 2 := by
    have h1 := anomaly_eq_schmidt_sq_sub_one (rapidity K) hpos
    have h2 := anomaly_rapidity K hK
    linarith
  have hsn_pos : 0 < schmidtNumber (rapidity K) := by
    unfold schmidtNumber
    exact div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr hpos)
  calc schmidtNumber (rapidity K)
      = Real.sqrt ((schmidtNumber (rapidity K)) ^ 2) := (Real.sqrt_sq hsn_pos.le).symm
    _ = Real.sqrt (K ^ 2) := by rw [hsq]
    _ = K := Real.sqrt_sq (by linarith)


/-- **[`α = 2π(K² − 1)` under an explicit equality premise]** equating the Schwinger value with the anomaly
at the rapidity reconstructed from `K` yields the displayed rewrite. The hypothesis `h` supplies precisely
that physical identification, so this theorem is not an independent derivation of `α`. -/
lemma alpha_from_schmidt (α K : ℝ) (hK : 1 < K)
    (h : schwingerAnomaly α = anomaly (rapidity K)) :
    α = 2 * Real.pi * (K ^ 2 - 1) := by
  have hpos : 0 < rapidity K := rapidity_pos K hK
  rw [MuonAnomaly.SchwingerRapidityEquation.alpha_eq_twoPi_schmidt_defect α (rapidity K) hpos h,
    schmidtNumber_rapidity K hK]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt

end

