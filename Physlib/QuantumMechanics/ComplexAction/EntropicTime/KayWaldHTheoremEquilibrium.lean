/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy
public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann

/-!
# The Kay–Wald / Hawking KMS state is the equilibrium fixed point of the quantum-Boltzmann H-theorem

Bridges the Kay–Wald thermal arc to the repository's **quantum-Boltzmann H-theorem**
(`Thermodynamics.SecondLawQuantumBoltzmann`, Snoke–Liu–Girvin). The Hawking occupation
`hawkingOccupation β ω = 1/(e^{βω} − 1)` is *definitionally* the repository's `boseEinstein`, which the H-theorem
already identifies as its relaxation equilibrium; here that identification is made explicit and, more, the Hawking
occupation is shown to be the **fixed point of the Boltzmann collision term** and the point of **vanishing entropy
production** — so the Kay–Wald KMS state is exactly where the H-theorem's monotone entropy increase terminates.

* the **shared occupation object** `hawkingOccupation = boseEinstein` (`hawkingOccupation_eq_boseEinstein`) — the
 Kay–Wald horizon occupation is the H-theorem's Bose–Einstein equilibrium distribution, no new object;
* the **Boltzmann collision term vanishes** at the Hawking occupation
 `boltzmannRHS n (e^{βω}Γ<) Γ< = 0` (`hawking_boltzmann_fixed_point`) — with gain/loss rates in KMS detailed
 balance `Γ> = e^{βω}Γ<`, the Hawking occupation is the stationary (equilibrium) solution of the quantum Boltzmann
 equation; the proof is exactly the detailed-balance identity `n e^{βω} = n+1` (`occupation_mul_exp`);
* the **equilibrium occupation is the Hawking occupation** `equilibriumOccupation (e^{βω}Γ<) Γ< = n`
 (`hawking_is_equilibriumOccupation`) — the H-theorem's `Γ</(Γ> − Γ<)` fixed point returns `1/(e^{βω}−1)`;
* the **entropy production vanishes at the Hawking state** (`hawking_zero_entropy_production`) — the
 gain–loss log-balance `(ln a − ln b)(a − b)` of the H-theorem (`entropyProduction_term_eq_zero_iff`) is zero
 because gain equals loss (`a = b`), the detailed-balance / equilibrium endpoint of the second law;
* the **bundled equilibrium statement** (`kay_wald_is_hTheorem_equilibrium`).

So the Kay–Wald / Hawking KMS state is the equilibrium of the quantum-Boltzmann H-theorem: the Bose–Einstein fixed
point where the collision term vanishes, the `equilibriumOccupation` is `n`, and the H-theorem's entropy production
reaches its zero (detailed-balance) endpoint. The thermal state built geometrically from the bifurcate Killing
horizon coincides with the dynamical relaxation endpoint of the second law.

* **§A — the shared occupation object** (`hawkingOccupation_eq_boseEinstein`).
* **§B — the Boltzmann fixed point** (`hawking_boltzmann_fixed_point`, `hawking_is_equilibriumOccupation`).
* **§C — zero entropy production and the equilibrium bundle** (`hawking_zero_entropy_production`,
 `kay_wald_is_hTheorem_equilibrium`).

The occupation identification, the collision-term fixed point, the equilibrium occupation, and
the vanishing entropy production are exact algebra, reusing `boltzmannRHS`, `equilibriumOccupation`, `boseEinstein`,
and the H-theorem's `entropyProduction_term_eq_zero_iff` — nothing is re-derived. The full Snoke relaxation
worldline and the second-law monotonicity live in `SecondLawQuantumBoltzmann` and are cited, not duplicated. No new
axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; D.W. Snoke, G. Liu, S.M. Girvin (quantum Boltzmann H-theorem).
 Repo dependencies: `Thermodynamics.SecondLawQuantumBoltzmann`,
 `StatisticalMechanics.BoltzmannFromQFT` (`boltzmannRHS`, `equilibriumOccupation`),
 `ThermoFieldDynamics.MatsubaraThermalOscillator` (`boseEinstein`),
 `EntropicTime.KayWaldKMSAnalyticPeriodicity` (`occupation_mul_exp`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannFromQFT
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHTheoremEquilibrium

/-! ## §A — the shared occupation object -/

/-- **[The Hawking occupation is the Bose–Einstein equilibrium] `hawkingOccupation = boseEinstein`.** The Kay–Wald
horizon occupation `1/(e^{βω}−1)` is *definitionally* the repository's `boseEinstein`, which the quantum-Boltzmann
H-theorem identifies as its relaxation equilibrium (`QuantumBoltzmannRelaxation.fbar_eq_boseEinstein`). No new
object — the geometric Hawking state and the dynamical H-theorem equilibrium are the same distribution. -/
theorem hawkingOccupation_eq_boseEinstein (β ω : ℝ) :
    hawkingOccupation β ω = boseEinstein β ω := rfl

/-! ## §B — the Boltzmann fixed point -/

/-- **[The Hawking occupation is the Boltzmann collision fixed point] `boltzmannRHS n (e^{βω}Γ<) Γ< = 0`.** With
the gain/loss rates in KMS detailed balance `Γ> = e^{βω}Γ<`, the Hawking occupation `n = 1/(e^{βω}−1)` makes the
quantum-Boltzmann collision term `(1+n)Γ< − n Γ>` vanish — it is the stationary equilibrium solution. The proof is
exactly the detailed-balance identity `n e^{βω} = n+1` (`occupation_mul_exp`). -/
theorem hawking_boltzmann_fixed_point (β ω Γlt : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    boltzmannRHS (hawkingOccupation β ω) (Real.exp (β * ω) * Γlt) Γlt = 0 := by
  unfold boltzmannRHS
  rw [show hawkingOccupation β ω * (Real.exp (β * ω) * Γlt)
        = (hawkingOccupation β ω * Real.exp (β * ω)) * Γlt from by ring,
    occupation_mul_exp β ω h]
  ring

/-- **[The H-theorem equilibrium occupation is the Hawking occupation] `Γ</(Γ> − Γ<) = n`.** The Snoke relaxation's
`equilibriumOccupation` at KMS-detailed-balanced rates `Γ> = e^{βω}Γ<` returns exactly the Hawking / Bose–Einstein
occupation `1/(e^{βω}−1)`. -/
theorem hawking_is_equilibriumOccupation (β ω Γlt : ℝ) (hΓ : Γlt ≠ 0) :
    equilibriumOccupation (Real.exp (β * ω) * Γlt) Γlt = hawkingOccupation β ω := by
  unfold equilibriumOccupation hawkingOccupation
  rw [show Real.exp (β * ω) * Γlt - Γlt = (Real.exp (β * ω) - 1) * Γlt from by ring,
    mul_comm (Real.exp (β * ω) - 1) Γlt, ← div_div, div_self hΓ]

/-! ## §C — zero entropy production and the equilibrium bundle -/

/-- **[The entropy production vanishes at the Hawking state].** The H-theorem's per-collision gain–loss log-balance
`(ln a − ln b)(a − b)` (`entropyProduction_term_eq_zero_iff`) is zero at the Hawking occupation, because the gain
`a = (1+n)Γ<` equals the loss `b = n(e^{βω}Γ<)` — the detailed-balance / equilibrium endpoint where the
quantum-Boltzmann second law's monotone entropy increase terminates. -/
theorem hawking_zero_entropy_production (β ω Γlt : ℝ) (hβω : 0 < β * ω) (hΓ : 0 < Γlt)
    (h : Real.exp (β * ω) - 1 ≠ 0) :
    (Real.log ((1 + hawkingOccupation β ω) * Γlt)
        - Real.log (hawkingOccupation β ω * (Real.exp (β * ω) * Γlt)))
      * ((1 + hawkingOccupation β ω) * Γlt
        - hawkingOccupation β ω * (Real.exp (β * ω) * Γlt)) = 0 := by
  have hn : 0 < hawkingOccupation β ω := hawkingOccupation_pos β ω hβω
  have hg : 0 < (1 + hawkingOccupation β ω) * Γlt := mul_pos (by linarith) hΓ
  have hl : 0 < hawkingOccupation β ω * (Real.exp (β * ω) * Γlt) :=
    mul_pos hn (mul_pos (Real.exp_pos _) hΓ)
  have hbal : (1 + hawkingOccupation β ω) * Γlt
      = hawkingOccupation β ω * (Real.exp (β * ω) * Γlt) := by
    rw [← mul_assoc, occupation_mul_exp β ω h]; ring
  exact (entropyProduction_term_eq_zero_iff hg hl).mpr hbal

/-- **[The Kay–Wald / Hawking KMS state is the quantum-Boltzmann H-theorem equilibrium].** Bundling the
equilibrium facts: the Hawking occupation is the Bose–Einstein distribution, it is the Boltzmann collision fixed
point, and it is the H-theorem's `equilibriumOccupation` — the geometric Kay–Wald thermal state coincides with the
dynamical relaxation endpoint of the second law. -/
theorem kay_wald_is_hTheorem_equilibrium (β ω Γlt : ℝ) (hΓ : Γlt ≠ 0)
    (h : Real.exp (β * ω) - 1 ≠ 0) :
    (hawkingOccupation β ω = boseEinstein β ω)
      ∧ (boltzmannRHS (hawkingOccupation β ω) (Real.exp (β * ω) * Γlt) Γlt = 0)
      ∧ (equilibriumOccupation (Real.exp (β * ω) * Γlt) Γlt = hawkingOccupation β ω) :=
  ⟨hawkingOccupation_eq_boseEinstein β ω,
   hawking_boltzmann_fixed_point β ω Γlt h,
   hawking_is_equilibriumOccupation β ω Γlt hΓ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHTheoremEquilibrium

end
