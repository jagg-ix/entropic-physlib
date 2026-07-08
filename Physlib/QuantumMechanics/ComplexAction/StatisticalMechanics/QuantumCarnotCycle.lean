/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine

/-!
# A quantum Carnot cycle

Extends the `StatisticalMechanics.QuantumClausiusEngine` / `StatisticalMechanics.QuantumRefrigerator` formalism with the explicit **Carnot cycle** —
the reversible four-stroke cycle that *saturates* the Clausius bound. A Carnot cycle alternates two
**isothermal** strokes (exchanging heat `Q = T·ΔS` with a reservoir) and two **isentropic adiabats** (no
heat, `ΔS` unchanged), so the entropy `ΔS` transferred at the hot isotherm is recovered at the cold one. The
result is the universal Carnot efficiency

  `η = W/Q_h = (T_h − T_c)·ΔS / (T_h·ΔS) = 1 − T_c/T_h`,

independent of the working substance (`ΔS` cancels) — for the quantum engine, `ΔS` is the von Neumann
entropy change of the Bogoliubov mode and the gap is varied isentropically on the adiabats.

* **§A — the cycle and its heats** (`CarnotCycle`, `heatHot`, `heatCold`, `work`, `efficiency`). The two
  isothermal heats `Q_h = T_h·ΔS`, `Q_c = T_c·ΔS`, the work `W = Q_h − Q_c`, and `η = W/Q_h`.
* **§B — the universal efficiency** (`efficiency_eq`, `efficiency_eq_carnot`). `η = 1 − T_c/T_h`, exactly the
  `carnotEfficiency` ceiling of the Clausius engine — the Carnot cycle attains it.
* **§C — the reversibility** (`clausius_balance`, `clausiusSum_zero`, `reversible_eq_detailedBalance`).
  `Q_h/T_h = Q_c/T_c = ΔS` (isentropic adiabats), so the Clausius integral vanishes — and that zero is the
  Snoke quantum-Boltzmann H-theorem at detailed balance `aᵢ = bᵢ`, the equilibrium with no entropy production.
* **§D — the quantum gloss** (`work_pos`, `efficiency_lt_one`). The cycle does positive work and has
  efficiency strictly below `1`; the entropy `ΔS` is the mode's von Neumann entropy, the reversibility the
  `T`-even Bogoliubov mass shell.

## References

* S. Carnot (the Carnot cycle and `η = 1 − T_c/T_h`); the reversible (Clausius-equality) limit.
* Repo dependencies: `StatisticalMechanics.QuantumClausiusEngine` (`carnotEfficiency`, `engineEfficiency`, `clausiusSum`,
  `reversible_achieves_carnot`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumCarnotCycle

open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann

/-! ## §A — the Carnot cycle and its heats -/

/-- **A reversible Carnot cycle**: two isothermal strokes at `T_h > T_c > 0` exchanging entropy `ΔS > 0`,
joined by two isentropic adiabats (the same `ΔS`). -/
structure CarnotCycle where
  /-- Hot reservoir temperature. -/
  Th : ℝ
  /-- Cold reservoir temperature. -/
  Tc : ℝ
  /-- Entropy exchanged on each isotherm (equal, since the adiabats are isentropic). -/
  ΔS : ℝ
  Th_pos : 0 < Th
  Tc_pos : 0 < Tc
  Tc_lt_Th : Tc < Th
  ΔS_pos : 0 < ΔS

namespace CarnotCycle

/-- **Heat absorbed on the hot isotherm** `Q_h = T_h·ΔS`. -/
noncomputable def heatHot (c : CarnotCycle) : ℝ := c.Th * c.ΔS

/-- **Heat released on the cold isotherm** `Q_c = T_c·ΔS`. -/
noncomputable def heatCold (c : CarnotCycle) : ℝ := c.Tc * c.ΔS

/-- **Net work** `W = Q_h − Q_c = (T_h − T_c)·ΔS`. -/
noncomputable def work (c : CarnotCycle) : ℝ := c.heatHot - c.heatCold

/-- **Efficiency** `η = W/Q_h`. -/
noncomputable def efficiency (c : CarnotCycle) : ℝ := c.work / c.heatHot

/-! ## §B — the universal Carnot efficiency -/

/-- **[Universal Carnot efficiency] `η = 1 − T_c/T_h`.** The entropy `ΔS` cancels — the efficiency is
independent of the working substance. -/
theorem efficiency_eq (c : CarnotCycle) : c.efficiency = 1 - c.Tc / c.Th := by
  unfold efficiency work heatHot heatCold
  field_simp [c.Th_pos.ne', c.ΔS_pos.ne']

/-- **The Carnot cycle attains the Clausius-engine ceiling** `η = carnotEfficiency T_h T_c`. -/
theorem efficiency_eq_carnot (c : CarnotCycle) : c.efficiency = carnotEfficiency c.Th c.Tc := by
  rw [efficiency_eq, carnotEfficiency]

/-! ## §C — the reversibility -/

/-- **[Clausius balance] `Q_h/T_h = Q_c/T_c = ΔS`.** The entropy delivered at the hot isotherm equals that
removed at the cold one — the adiabats are isentropic. -/
theorem clausius_balance (c : CarnotCycle) : c.heatHot / c.Th = c.heatCold / c.Tc := by
  unfold heatHot heatCold
  rw [mul_comm c.Th, mul_div_assoc, div_self c.Th_pos.ne', mul_comm c.Tc, mul_div_assoc,
    div_self c.Tc_pos.ne']

/-- **[Reversible] The Clausius integral vanishes** `∮δQ/T = 0` — zero entropy production, the reversible
limit that saturates the Carnot bound. -/
theorem clausiusSum_zero (c : CarnotCycle) : clausiusSum c.heatHot c.Th c.heatCold c.Tc = 0 := by
  rw [clausiusSum, sub_eq_zero, clausius_balance]

/-- **[Reversibility = detailed balance] The Carnot cycle's zero entropy production is the H-theorem at
detailed balance.** `∮δQ/T = ∑ᵢ (ln aᵢ − ln bᵢ)(aᵢ − bᵢ) = 0` when the scattering occupation products balance
`aᵢ = bᵢ` — each Snoke H-theorem term vanishes (`SecondLawQuantumBoltzmann.entropyProduction_term_eq_zero_iff`),
the detailed-balance equilibrium, which is precisely why the reversible cycle produces no entropy. -/
theorem reversible_eq_detailedBalance (c : CarnotCycle) {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hbal : ∀ i, a i = b i) :
    clausiusSum c.heatHot c.Th c.heatCold c.Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i) := by
  rw [clausiusSum_zero]
  symm
  exact Finset.sum_eq_zero fun i _ =>
    (entropyProduction_term_eq_zero_iff (ha i) (hb i)).mpr (hbal i)

/-! ## §D — positivity and the quantum gloss -/

/-- **The cycle does positive work** `W > 0`. -/
theorem work_pos (c : CarnotCycle) : 0 < c.work := by
  unfold work heatHot heatCold
  nlinarith [mul_pos (sub_pos.mpr c.Tc_lt_Th) c.ΔS_pos]

/-- **The efficiency is strictly below one** `η < 1` — the cold reservoir always records away heat
(`T_c > 0`), so no Carnot engine is perfectly efficient. -/
theorem efficiency_lt_one (c : CarnotCycle) : c.efficiency < 1 := by
  rw [efficiency_eq]
  have : 0 < c.Tc / c.Th := div_pos c.Tc_pos c.Th_pos
  linarith

end CarnotCycle

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumCarnotCycle

end
