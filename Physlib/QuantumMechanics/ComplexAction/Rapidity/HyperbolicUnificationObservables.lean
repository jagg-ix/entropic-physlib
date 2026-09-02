/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh

/-!
# One Schmidt number, many observables: the Hyperbolic Unification dictionary

The muon `g − 2` operating-point momentum relation `a = K² − 1` (`MuonAnomaly.AnomalyRapidity`) is one entry of a much
larger dictionary. The single **Schmidt number** `K = coth η` of the Hyperbolic Unification
(`MuonAnomaly.SchmidtRapidityHyperbolicUnification`) — the bipartite entanglement measure at effective rapidity `η` —
simultaneously encodes a special-relativistic, a thermal-statistical, and an anomalous-moment observable.
With `η > 0` (`K > 1`):

| observable | as a function of `K` | hyperbolic form | physical case |
|---|---|---|---|
| boost velocity `β` | `1/K` | `tanh η` | special relativity / entanglement-suppression |
| Lorentz factor `γ` | `K/√(K²−1)` | `cosh η` | time dilation / Bogoliubov energy |
| Bose occupation `n_B` | `(K−1)/2` | `(coth η − 1)/2` | Bose–Einstein statistics (unbounded) |
| Fermi occupation `n_F` | `(1 − 1/K)/2` | `(1 − tanh η)/2` | Fermi–Dirac / Pauli (`< 1/2`) |
| rapidity defect `a` | `K² − 1` | `csch²η = 1/sinh²η` | muon `g − 2` anomaly; inverse squeezed-state photon number |

* **§A — relativity.** `velocity_eq_inv_schmidt` (`β = 1/K`), `lorentzGamma_schmidt` (`γ·√(K²−1) = K`).
* **§B — quantum statistics.** `boseOccupation_eq_schmidt` (`n_B = (K−1)/2`),
  `fermiOccupation_eq_schmidt` (`n_F = (1−1/K)/2`), `fermiOccupation_lt_half` (Pauli bound).
* **§C — the rapidity defect.** `rapidityDefect_eq_schmidt_sq_sub_one` (`a = K²−1`) — the same `K²−1` that is
  the muon `g − 2` anomaly is the inverse momentum² and the inverse mean photon number of a two-mode
  squeezed vacuum.

So entanglement (`K`), the boost velocity, the Lorentz factor, the Bose and Fermi occupations, and the `g − 2`
anomaly are *five faces of one rapidity* — the content of the Hyperbolic Unification, now applied across the
cases.

**Honest layering.** These are exact identities of the hyperbolic functions of one rapidity `η`, tied to the
repo's verified Bose/Fermi (`tanh = 1−2n_F`, `coth = 1+2n_B`) and the entanglement `K = coth η`. They are
*relations* among observables sharing a rapidity, not predictions of any one observable's value (each `η` is
set by its own physics — temperature, boost, operating-point momentum).

## References

* `Physlib` (`MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber`,
  `Bogoliubov.RapidityBoseFermiCothTanh.tanh_eq_one_sub_two_fermiDirac`/`coshDivSinh_eq_one_add_two_boseEinstein`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Rapidity.HyperbolicUnificationObservables


/-- **[Boost velocity is the inverse Schmidt number]** `β = tanh η = 1/K`. -/
lemma velocity_eq_inv_schmidt (η : ℝ) : Real.tanh η = 1 / schmidtNumber η := by
  unfold schmidtNumber
  rw [Real.tanh_eq_sinh_div_cosh, one_div_div]

/-- **[Lorentz factor from `K`]** `γ·√(K²−1) = K`, i.e. `γ = cosh η = K/√(K²−1)` — the time-dilation /
Bogoliubov-energy factor expressed through the Schmidt number. -/
lemma lorentzGamma_schmidt (η : ℝ) (hη : 0 < η) :
    Real.cosh η * Real.sqrt ((schmidtNumber η) ^ 2 - 1) = schmidtNumber η := by
  have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
  have hsne : Real.sinh η ≠ 0 := hs.ne'
  simp only [schmidtNumber]
  rw [show (Real.cosh η / Real.sinh η) ^ 2 - 1 = (1 / Real.sinh η) ^ 2 from by
      field_simp; nlinarith [Real.cosh_sq_sub_sinh_sq η],
    Real.sqrt_sq (by positivity), mul_one_div]


/-- **[Bose occupation from `K`]** `K = 1 + 2 n_B`, i.e. `n_B = (K−1)/2` — the Bose–Einstein occupation is the
Schmidt number shifted and halved (unbounded as `K → ∞`). -/
lemma boseOccupation_eq_schmidt (η : ℝ) (hη : 0 < η) :
    schmidtNumber η = 1 + 2 * boseEinstein 1 (2 * η) := by
  unfold schmidtNumber
  exact coshDivSinh_eq_one_add_two_boseEinstein η (ne_of_gt hη)

/-- **[Fermi occupation from `K`]** `n_F = (1 − 1/K)/2` — the Fermi–Dirac (Pauli-bounded) occupation as the
complementary face of the same `K`. -/
lemma fermiOccupation_eq_schmidt (η : ℝ) :
    fermiDirac (2 * η) = (1 - 1 / schmidtNumber η) / 2 := by
  have h1 := tanh_eq_one_sub_two_fermiDirac η
  have h2 := velocity_eq_inv_schmidt η
  linarith

/-- **[Pauli bound]** `n_F = (1 − 1/K)/2 < 1/2` for `K > 0` — the Pauli-bounded fermionic occupation, in
contrast to the unbounded Bose occupation. -/
lemma fermiOccupation_lt_half (η : ℝ) (hη : 0 < η) : fermiDirac (2 * η) < 1 / 2 := by
  unfold fermiDirac
  have hexp : (2 : ℝ) < Real.exp (2 * η) + 1 := by
    have h := Real.add_one_lt_exp (show (2 * η) ≠ 0 by positivity)
    linarith
  exact one_div_lt_one_div_of_lt (by norm_num) hexp


/-- **[The rapidity defect is `K² − 1`]** `1/sinh²η = K² − 1` — the *same* `K²−1` that is the muon `g − 2`
anomaly (`MuonAnomaly.AnomalyRapidity`) is the inverse momentum² and the inverse mean photon number of a
two-mode squeezed vacuum (`n = sinh²η`). -/
lemma rapidityDefect_eq_schmidt_sq_sub_one (η : ℝ) (hη : 0 < η) :
    1 / (Real.sinh η) ^ 2 = (schmidtNumber η) ^ 2 - 1 := by
  have hs : Real.sinh η ≠ 0 := (Real.sinh_pos_iff.mpr hη).ne'
  unfold schmidtNumber
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

end Physlib.QuantumMechanics.ComplexAction.Rapidity.HyperbolicUnificationObservables

end
