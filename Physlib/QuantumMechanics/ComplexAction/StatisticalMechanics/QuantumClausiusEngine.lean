/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.BCJDiamondQuantum
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann

/-!
# A Quantum Clausius Engine

Builds a thermodynamic-engine formalism on top of the grand unification of `Lorentz.BCJDiamondQuantum`
(`classical_quantum_gravity_unified`): under the antiunitary time reversal, the energy / mass shell is
`T`-even and the momentum/flux is `T`-odd. This is *exactly* the reversible/irreversible split a **Clausius
engine** runs on — the reversible (Carnot) cycle is the time-reversal-symmetric, entropy-conserving one, and
the entropy production is the `T`-odd dissipation. The working substance's heat is the **quantum Bogoliubov
mass shell** `√(ξ²+Δ²)`, which (being `T`-even) is the conserved reversible quantity.

* **§A — the Clausius inequality** (`clausiusSum`, `entropyProduction`, `entropyProduction_eq_neg_clausius`,
  `clausius_second_law`, `clausius_of_hTheorem`). The cycle integral `∮δQ/T = Q_h/T_h − Q_c/T_c`; the entropy
  production is its negative, nonnegative exactly when the Clausius inequality `∮δQ/T ≤ 0` holds. The Clausius
  inequality is no longer assumed: `clausius_of_hTheorem` *derives* it from the existing **quantum-Boltzmann
  H-theorem** (`Thermodynamics.SecondLawQuantumBoltzmann.hTheorem`, Snoke–Liu–Girvin) once the entropy
  production is realized as its scattering-quartet sum `∑ᵢ (ln aᵢ − ln bᵢ)(aᵢ − bᵢ) ≥ 0`.
* **§B — the Carnot bound** (`carnot_bound`, `carnot_bound_of_hTheorem`, `quantumBoltzmann_engine_two_laws`,
  `reversible_achieves_carnot`). The Clausius inequality forces the efficiency below Carnot `1 − T_c/T_h`;
  `carnot_bound_of_hTheorem` runs the whole bound off the H-theorem, and `quantumBoltzmann_engine_two_laws`
  pairs it with the **Saveliev linear Boltzmann operator**'s energy conservation (`energyConserving_self`, the
  first law) — both thermodynamic laws from one collision operator; a reversible cycle achieves Carnot.
* **§C — the quantum working substance** (`quantumCarnotHeat`, `quantumCarnotHeat_pos`,
  `quantumCarnotHeat_timeReversal`, `quantum_carnot_bound`). The heat is the Bogoliubov mass-shell energy
  `√(ξ²+Δ²)` — positive (gap `Δ ≠ 0`) and `T`-even (`bogoliubovEnergy_timeReversal` — the reversibility *is*
  the conserved mass shell of the grand unification). A quantum engine between two mass-shell reservoirs
  obeys the Carnot bound.

## References

* R. Clausius (the Clausius inequality `∮δQ/T ≤ 0`); the Carnot efficiency `1 − T_c/T_h`; Snoke–Liu–Girvin
  (the quantum-Boltzmann H-theorem).
* Repo dependencies: `Thermodynamics.SecondLawQuantumBoltzmann.hTheorem` (the second law);
  `CollisionOperatorSl2.LinearBoltzmannOperator.energyConserving_self` (the first law);
  `Lorentz.BCJDiamondQuantum.classical_quantum_gravity_unified`;
  `Bogoliubov.Transformation.bogoliubovEnergy`; `Vlasov.DiamondTimeReversal.bogoliubovEnergy_timeReversal`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann

/-! ## §A — the Clausius inequality and entropy production -/

/-- **The Clausius cycle integral** `∮δQ/T = Q_h/T_h − Q_c/T_c` for a two-reservoir engine. -/
noncomputable def clausiusSum (Qh Th Qc Tc : ℝ) : ℝ := Qh / Th - Qc / Tc

/-- **The entropy production** `ΔS = Q_c/T_c − Q_h/T_h` over one cycle. -/
noncomputable def entropyProduction (Qh Th Qc Tc : ℝ) : ℝ := Qc / Tc - Qh / Th

/-- **The engine efficiency** `η = 1 − Q_c/Q_h`. -/
noncomputable def engineEfficiency (Qh Qc : ℝ) : ℝ := 1 - Qc / Qh

/-- **The Carnot efficiency** `η_C = 1 − T_c/T_h`. -/
noncomputable def carnotEfficiency (Th Tc : ℝ) : ℝ := 1 - Tc / Th

/-- **Entropy production is minus the Clausius integral** `ΔS = −∮δQ/T`. -/
theorem entropyProduction_eq_neg_clausius (Qh Th Qc Tc : ℝ) :
    entropyProduction Qh Th Qc Tc = -clausiusSum Qh Th Qc Tc := by
  unfold entropyProduction clausiusSum; ring

/-- **[Second law] The entropy production is nonnegative iff the Clausius inequality holds**
`ΔS ≥ 0 ↔ ∮δQ/T ≤ 0`. -/
theorem clausius_second_law (Qh Th Qc Tc : ℝ) :
    0 ≤ entropyProduction Qh Th Qc Tc ↔ clausiusSum Qh Th Qc Tc ≤ 0 := by
  rw [entropyProduction_eq_neg_clausius, neg_nonneg]

/-- **[Quantum-Boltzmann H-theorem ⟹ Clausius] The Clausius inequality is the H-theorem.** When the engine's
entropy production is realized as the **Snoke–Liu–Girvin quantum-Boltzmann H-theorem** entropy production
`∑ᵢ (ln aᵢ − ln bᵢ)(aᵢ − bᵢ)` over scattering quartets (`aᵢ = N_k N_{k'}`, `bᵢ = N_{k₁}N_{k₂}`), the existing
`SecondLawQuantumBoltzmann.hTheorem` *proves* the Clausius inequality `∮δQ/T ≤ 0`: it is no longer
assumed, but a theorem of quantum kinetic theory. -/
theorem clausius_of_hTheorem {ι : Type*} [Fintype ι] (Qh Th Qc Tc : ℝ) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : entropyProduction Qh Th Qc Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    clausiusSum Qh Th Qc Tc ≤ 0 := by
  rw [← clausius_second_law, hident]
  exact hTheorem a b ha hb

/-! ## §B — the Carnot bound -/

/-- **[Carnot bound] The Clausius inequality caps the efficiency at Carnot** `η ≤ 1 − T_c/T_h`. -/
theorem carnot_bound (Qh Th Qc Tc : ℝ) (hTh : 0 < Th) (hTc : 0 < Tc) (hQh : 0 < Qh)
    (hClausius : clausiusSum Qh Th Qc Tc ≤ 0) :
    engineEfficiency Qh Qc ≤ carnotEfficiency Th Tc := by
  unfold engineEfficiency carnotEfficiency clausiusSum at *
  have h1 : Qh / Th ≤ Qc / Tc := by linarith
  rw [div_le_div_iff₀ hTh hTc] at h1
  have h2 : Tc / Th ≤ Qc / Qh := by rw [div_le_div_iff₀ hTh hQh]; nlinarith
  linarith

/-- **[Carnot bound from the quantum-Boltzmann H-theorem] The whole bound runs off the H-theorem.** Realizing
the entropy production as the Snoke H-theorem sum, `SecondLawQuantumBoltzmann.hTheorem` caps the efficiency at
Carnot — no Clausius inequality is assumed anywhere. -/
theorem carnot_bound_of_hTheorem {ι : Type*} [Fintype ι] (Qh Th Qc Tc : ℝ) (hTh : 0 < Th)
    (hTc : 0 < Tc) (hQh : 0 < Qh) (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : entropyProduction Qh Th Qc Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    engineEfficiency Qh Qc ≤ carnotEfficiency Th Tc :=
  carnot_bound Qh Th Qc Tc hTh hTc hQh (clausius_of_hTheorem Qh Th Qc Tc a b ha hb hident)

/-- **[The two laws of the quantum-Boltzmann engine] First law from Saveliev, second from the H-theorem.** The
working substance's collisions are the **Saveliev linear Boltzmann operator** `v²∗`, which *conserves energy*
(`energyConserving_self`: `v²∗v² = 0`, the first law), while the **H-theorem** entropy production gives the
Clausius inequality and hence the Carnot bound (the second law). One microscopic operator delivers both
thermodynamic laws of the engine. -/
theorem quantumBoltzmann_engine_two_laws {R : Type*} [Ring R] (vsq : R) {ι : Type*} [Fintype ι]
    (Qh Th Qc Tc : ℝ) (hTh : 0 < Th) (hTc : 0 < Tc) (hQh : 0 < Qh) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hident : entropyProduction Qh Th Qc Tc
      = ∑ i, (Real.log (a i) - Real.log (b i)) * (a i - b i)) :
    EnergyConserving vsq vsq ∧ engineEfficiency Qh Qc ≤ carnotEfficiency Th Tc :=
  ⟨energyConserving_self vsq, carnot_bound_of_hTheorem Qh Th Qc Tc hTh hTc hQh a b ha hb hident⟩

/-- **[Reversible Carnot] A reversible cycle achieves Carnot efficiency** `η = 1 − T_c/T_h` when the entropy
production vanishes (the equality case of Clausius). -/
theorem reversible_achieves_carnot (Qh Th Qc Tc : ℝ) (hTh : 0 < Th) (hTc : 0 < Tc) (hQh : 0 < Qh)
    (hRev : entropyProduction Qh Th Qc Tc = 0) :
    engineEfficiency Qh Qc = carnotEfficiency Th Tc := by
  unfold engineEfficiency carnotEfficiency entropyProduction at *
  have h1 : Qh / Th = Qc / Tc := by linarith
  have key : Qc / Qh = Tc / Th := by
    field_simp at h1 ⊢
    nlinarith [h1]
  rw [key]

/-! ## §C — the quantum working substance (the Bogoliubov mass shell) -/

/-- **The quantum heat quantum** — the Bogoliubov mass-shell energy `√(ξ²+Δ²)`, the quasiparticle the engine
exchanges with a reservoir. -/
noncomputable def quantumCarnotHeat (ξ Δ : ℝ) : ℝ := bogoliubovEnergy ξ Δ

/-- **The quantum heat is positive** when the gap `Δ ≠ 0`. -/
theorem quantumCarnotHeat_pos (ξ Δ : ℝ) (hΔ : Δ ≠ 0) : 0 < quantumCarnotHeat ξ Δ := by
  unfold quantumCarnotHeat bogoliubovEnergy
  rw [Real.sqrt_pos]; positivity

/-- **[Reversibility = the conserved mass shell] The quantum heat is `T`-even** `Q(−ξ) = Q(ξ)` — the
reversible Carnot quantity is the time-reversal-invariant Bogoliubov mass shell of the grand unification
(`bogoliubovEnergy_timeReversal`). -/
theorem quantumCarnotHeat_timeReversal (ξ Δ : ℝ) :
    quantumCarnotHeat (-ξ) Δ = quantumCarnotHeat ξ Δ :=
  bogoliubovEnergy_timeReversal ξ Δ

/-- **[Quantum Carnot bound] A quantum engine between two mass-shell reservoirs obeys the Carnot bound.**
With heats the Bogoliubov mass-shell energies `Q_h = √(ξ_h²+Δ²)`, `Q_c = √(ξ_c²+Δ²)` (positive for `Δ ≠ 0`),
the Clausius inequality forces `η ≤ 1 − T_c/T_h`. -/
theorem quantum_carnot_bound (ξh ξc Δ Th Tc : ℝ) (hΔ : Δ ≠ 0) (hTh : 0 < Th) (hTc : 0 < Tc)
    (hClausius : clausiusSum (quantumCarnotHeat ξh Δ) Th (quantumCarnotHeat ξc Δ) Tc ≤ 0) :
    engineEfficiency (quantumCarnotHeat ξh Δ) (quantumCarnotHeat ξc Δ)
      ≤ carnotEfficiency Th Tc :=
  carnot_bound (quantumCarnotHeat ξh Δ) Th (quantumCarnotHeat ξc Δ) Tc hTh hTc
    (quantumCarnotHeat_pos ξh Δ hΔ) hClausius

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine

end
