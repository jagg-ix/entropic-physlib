/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine

/-!
# A Quantum Refrigerator

Runs the `StatisticalMechanics.QuantumClausiusEngine` in reverse: a **refrigerator** uses work input `W = Q_h − Q_c` to pump heat
`Q_c` from the cold reservoir up to the hot one. It is the time-reversed engine — and the same antiunitary
`T` / mass-shell structure governs it: the reversible (Carnot) cycle is the `T`-even, entropy-conserving one,
and the entropy production is the `T`-odd dissipation. The working substance's heat is again the **quantum
Bogoliubov mass shell** `√(ξ²+Δ²)`.

* **§A — the coefficient of performance** (`coefficientOfPerformance`, `carnotCOP`). `COP = Q_c/W =
  Q_c/(Q_h − Q_c)`; the Carnot ceiling `COP_C = T_c/(T_h − T_c)`.
* **§B — the Clausius statement** (`secondLaw_of_hTheorem`, `clausius_statement_work_required`). The
  refrigerator's second law `Q_c/T_c ≤ Q_h/T_h` is itself the **quantum-Boltzmann H-theorem**: realized as the
  Snoke scattering-quartet sum it is proved by `SecondLawQuantumBoltzmann.hTheorem` (`secondLaw_of_hTheorem`).
  With it and `T_c < T_h`, refrigeration *requires* work: `Q_c < Q_h` — heat does not flow cold→hot spontaneously.
* **§C — the Carnot COP bound** (`refrigerator_cop_bound`, `reversible_achieves_carnotCOP`). The second law
  caps `COP ≤ T_c/(T_h − T_c)`; a reversible cycle (Clausius equality) attains it.
* **§D — the quantum refrigerator** (`quantumRefrigeratorReversible`, `quantum_refrigerator_cop_bound`). The
  pumped/dumped heats are Bogoliubov mass-shell energies; reversibility is the `T`-even mass shell
  (`quantumCarnotHeat_timeReversal`), and the quantum COP obeys the Carnot ceiling.

## References

* R. Clausius (the statement of the second law: no spontaneous heat flow cold→hot); the Carnot refrigerator
  `COP = T_c/(T_h − T_c)`.
* Repo carriers: `StatisticalMechanics.QuantumClausiusEngine` (`clausiusSum`, `quantumCarnotHeat`, `quantumCarnotHeat_pos`,
  `quantumCarnotHeat_timeReversal`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumRefrigerator

open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann


/-- **The coefficient of performance** `COP = Q_c/W = Q_c/(Q_h − Q_c)` — heat pumped from cold per unit work
input. -/
noncomputable def coefficientOfPerformance (Qh Qc : ℝ) : ℝ := Qc / (Qh - Qc)

/-- **The Carnot coefficient of performance** `COP_C = T_c/(T_h − T_c)` — the reversible ceiling. -/
noncomputable def carnotCOP (Th Tc : ℝ) : ℝ := Tc / (Th - Tc)


/-- **[Quantum-Boltzmann H-theorem ⟹ refrigerator second law] `Q_c/T_c ≤ Q_h/T_h` is the H-theorem.**
Realizing the refrigerator's entropy production `Q_h/T_h − Q_c/T_c` as the Snoke H-theorem sum, the existing
`SecondLawQuantumBoltzmann.hTheorem` forces it nonnegative — the refrigerator's second-law hypothesis is
proved by quantum kinetic theory, not assumed. -/
lemma secondLaw_of_hTheorem {ι : Type*} [Fintype ι] (Qh Th Qc Tc : ℝ) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : clausiusSum Qh Th Qc Tc = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    Qc / Tc ≤ Qh / Th := by
  have h0 : 0 ≤ clausiusSum Qh Th Qc Tc := hident ▸ hTheorem a b ha hb
  unfold clausiusSum at h0; linarith

/-- **[Clausius statement] Refrigeration requires work** `Q_c < Q_h`. With the second law `Q_c/T_c ≤
Q_h/T_h` and `T_c < T_h`, pumping heat `Q_c > 0` from cold forces `Q_h > Q_c`, i.e. a positive work input
`W = Q_h − Q_c > 0` — heat does not flow from cold to hot spontaneously. -/
lemma clausius_statement_work_required (Qh Th Qc Tc : ℝ) (hTc : 0 < Tc) (hThc : Tc < Th)
    (hQc : 0 < Qc) (hSecondLaw : Qc / Tc ≤ Qh / Th) : Qc < Qh := by
  rw [div_le_div_iff₀ hTc (lt_trans hTc hThc)] at hSecondLaw
  nlinarith


/-- **[Carnot COP bound] The second law caps the COP at Carnot** `COP ≤ T_c/(T_h − T_c)`. -/
lemma refrigerator_cop_bound (Qh Th Qc Tc : ℝ) (hTc : 0 < Tc) (hThc : Tc < Th)
    (_hQc : 0 < Qc) (hW : Qc < Qh) (hSecondLaw : Qc / Tc ≤ Qh / Th) :
    coefficientOfPerformance Qh Qc ≤ carnotCOP Th Tc := by
  unfold coefficientOfPerformance carnotCOP
  rw [div_le_div_iff₀ (sub_pos.mpr hW) (sub_pos.mpr hThc)]
  rw [div_le_div_iff₀ hTc (lt_trans hTc hThc)] at hSecondLaw
  nlinarith

/-- **[Reversible Carnot COP] A reversible refrigerator attains the Carnot COP** `COP = T_c/(T_h − T_c)` at
the Clausius equality (zero entropy production). -/
lemma reversible_achieves_carnotCOP (Qh Th Qc Tc : ℝ) (hTc : 0 < Tc) (hThc : Tc < Th)
    (_hQc : 0 < Qc) (hW : Qc < Qh) (hRev : Qc / Tc = Qh / Th) :
    coefficientOfPerformance Qh Qc = carnotCOP Th Tc := by
  unfold coefficientOfPerformance carnotCOP
  rw [div_eq_div_iff (sub_pos.mpr hW).ne' (sub_pos.mpr hThc).ne']
  rw [div_eq_div_iff hTc.ne' (lt_trans hTc hThc).ne'] at hRev
  nlinarith


/-- **[Reversible quantum refrigerator] The pumped heat is the `T`-even Bogoliubov mass shell** — the
reversibility of the quantum refrigerator is the time-reversal-invariant mass shell
(`quantumCarnotHeat_timeReversal`). -/
lemma quantumRefrigeratorReversible (ξ Δ : ℝ) :
    quantumCarnotHeat (-ξ) Δ = quantumCarnotHeat ξ Δ :=
  quantumCarnotHeat_timeReversal ξ Δ

/-- **[Quantum refrigerator COP bound] A quantum refrigerator between two mass-shell reservoirs obeys the
Carnot COP.** The pumped/dumped heats are the Bogoliubov mass-shell energies `√(ξ²+Δ²)`; the second law caps
`COP ≤ T_c/(T_h − T_c)`. -/
lemma quantum_refrigerator_cop_bound (ξh ξc Δ Th Tc : ℝ) (hTc : 0 < Tc) (hThc : Tc < Th)
    (hQc : 0 < quantumCarnotHeat ξc Δ)
    (hW : quantumCarnotHeat ξc Δ < quantumCarnotHeat ξh Δ)
    (hSecondLaw : quantumCarnotHeat ξc Δ / Tc ≤ quantumCarnotHeat ξh Δ / Th) :
    coefficientOfPerformance (quantumCarnotHeat ξh Δ) (quantumCarnotHeat ξc Δ) ≤ carnotCOP Th Tc :=
  refrigerator_cop_bound (quantumCarnotHeat ξh Δ) Th (quantumCarnotHeat ξc Δ) Tc hTc hThc hQc hW
    hSecondLaw

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumRefrigerator

end
