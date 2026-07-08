/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

/-!
# Bose–Einstein vs Fermi–Dirac as su(1,1) vs su(2): the Bogoliubov / Bloch-sphere weld

Welds the Saito Stokes-Bogoliubov cluster and the Verch/Bloch-sphere complex structure to the **two quantum
statistics**, realizing the Bose/Fermi dichotomy as the **su(1,1) hyperboloid vs su(2) sphere** split of the
Bogoliubov transformations:

| statistics | algebra | Bogoliubov | normalization | occupation | geometry |
|---|---|---|---|---|---|
| **Fermi–Dirac** | `su(2)` | `fermiBogoliubov` (`cos,sin`) | `u² + v² = 1` | `v² = n_F ≤ 1` (Pauli) | Bloch/Poincaré **sphere** `J²=−1` |
| **Bose–Einstein** | `su(1,1)` | `thermoBogoliubov` (`cosh,sinh`) | `cosh²−sinh² = 1` | `sinh² = n_B` (unbounded) | **hyperboloid** `K²=+1` |

The compactness of `su(2)` (the `+` sign, the sphere) forces the occupation `v² ≤ 1` — **Pauli exclusion**; the
non-compactness of `su(1,1)` (the `−` sign, the hyperboloid) lets `n_B = sinh²θ` grow without bound — **Bose
enhancement**. The single sign in the normalization is the whole of quantum statistics.

* **§A — Fermi–Dirac from the fermion (su(2)/Bloch) Bogoliubov** (`fermiDirac_eq_half_one_sub_tanh`,
  `bogoliubovV2_eq_fermiDirac`, `fermi_pauli_bound`). The Saito coherence factor `v² = ½(1 − ξ/E)`
  (`Bogoliubov.Transformation.bogoliubovV2`) at the thermal angle `ξ/E = tanh(βω/2)` is exactly the Fermi–Dirac
  distribution `n_F = 1/(e^{βω}+1)`; `u²+v²=1` with `u² ≥ 0` gives the Pauli bound `n_F ≤ 1`.
* **§B — Bose–Einstein from the boson (su(1,1)/hyperboloid) Bogoliubov** (`bose_occupation_eq`). The
  thermo-Bogoliubov weight `sinh²θ = n_B` gives `cosh²θ = 1 + n_B` (`ThermoFieldDynamics.TFDImaginaryPart.thermal_cosh_sq`), the
  `su(1,1)` mass shell.
* **§C — the dichotomy and the Bloch weld** (`bose_fermi_dichotomy`, `fermiGen_eq_neg_I_pauliY`). The
  normalizations `cosh²−sinh²=1` (Bose) and `u²+v²=1` (Fermi) side by side — the statistics is the sign; and
  the fermion Bogoliubov generator is `−iσ₂` (`= −sympForm` complexified, the Bloch/Poincaré generator), so
  Fermi–Dirac lives on the Verch/Saito Bloch sphere `J² = −1`.

## References

* S. Saito, Front. Phys. 11 (2024) 1225334 (the Stokes-Bogoliubov coherence factors, Poincaré sphere).
* R. Verch, arXiv:funct-an/9609004 (the pure-state complex structure `J² = −1`).
* Repo dependencies: `Bogoliubov.Transformation` (`bogoliubovV2`, `bogoliubov_normalization`),
  `ComplexOscillator.ComplexFermionicOscillator` (`fermiDirac`), `ThermoFieldDynamics.TFDImaginaryPart` (`boseEinstein`, `thermal_cosh_sq`),
  `ThermoFieldDynamics.TFDBogoliubovHopf` (`fermiBogoliubovGenerator`), `AlgebraicQFTQuasifree.PolarizatorBlochSphere`
  (`sympFormC_eq_I_smul_pauliY`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.SaitoBogoliubovBoseFermiStatistics

open Matrix PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

/-! ## §A — Fermi–Dirac from the fermion (su(2) / Bloch) Bogoliubov -/

/-- **[Fermi occupation = `(1 − tanh)/2`] `n_F(y) = ½(1 − tanh(y/2))`.** The fermion Bogoliubov occupation, in
the thermal parametrization, is the Fermi–Dirac distribution `1/(e^y + 1)`. -/
theorem fermiDirac_eq_half_one_sub_tanh (y : ℝ) :
    fermiDirac y = (1 - Real.tanh (y / 2)) / 2 := by
  rw [fermiDirac, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hne : Real.exp (y / 2) ≠ 0 := ne_of_gt hpos
  have h1 : Real.exp (-(y / 2)) = 1 / Real.exp (y / 2) := by rw [Real.exp_neg, one_div]
  have h2 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]; field_simp; ring

/-- **[Saito coherence factor = Fermi–Dirac] `v² = n_F`.** The Saito/BCS coherence factor `v² = ½(1 − ξ/E)`
(`Bogoliubov.Transformation.bogoliubovV2`) at the thermal angle `ξ/E = tanh(βω/2)` is the Fermi–Dirac
occupation `n_F = 1/(e^{βω}+1)` — the quasiparticle occupation of the fermion (su(2)) Bogoliubov vacuum is the
Fermi distribution. -/
theorem bogoliubovV2_eq_fermiDirac (ξ Δ β ω : ℝ)
    (hξ : ξ / bogoliubovEnergy ξ Δ = Real.tanh (β * ω / 2)) :
    bogoliubovV2 ξ Δ = fermiDirac (β * ω) := by
  rw [bogoliubovV2, hξ]; exact (fermiDirac_eq_half_one_sub_tanh (β * ω)).symm

/-- **[Pauli exclusion from compact su(2)] `n_F ≤ 1`.** The fermionic normalization `u² + v² = 1`
(`bogoliubov_normalization`, the `su(2)`/Bloch sphere) with `u² ≥ 0` forces the occupation `v² ≤ 1` — Pauli
exclusion is the compactness of the sphere. -/
theorem fermi_pauli_bound (ξ Δ : ℝ) (hu : 0 ≤ bogoliubovU2 ξ Δ) : bogoliubovV2 ξ Δ ≤ 1 := by
  have h := bogoliubov_normalization ξ Δ; linarith

/-! ## §B — Bose–Einstein from the boson (su(1,1) / hyperboloid) Bogoliubov -/

/-- **[Bose occupation, su(1,1) mass shell] `cosh²θ = 1 + n_B`.** The thermo-Bogoliubov weight `sinh²θ = n_B`
(`ThermoFieldDynamics.TFDImaginaryPart.thermal_cosh_sq`) on the `su(1,1)` mass shell `cosh²θ − sinh²θ = 1` — the boson occupation
`n_B = 1/(e^{βk}−1)` is unbounded (the non-compact hyperboloid). -/
theorem bose_occupation_eq (θ β k : ℝ) (h : Real.sinh θ ^ 2 = boseEinstein β k) :
    Real.cosh θ ^ 2 = 1 + boseEinstein β k :=
  thermal_cosh_sq θ β k h

/-! ## §C — the dichotomy and the Bloch-sphere weld -/

/-- **[Bose/Fermi dichotomy = the normalization sign] `cosh²−sinh²=1` vs `u²+v²=1`.** Side by side: the boson
(su(1,1)) Bogoliubov satisfies the *hyperbolic* normalization `cosh²θ − sinh²θ = 1` (the `−` sign, Bose), while
the fermion (su(2)) Bogoliubov satisfies the *spherical* `u² + v² = 1` (the `+` sign, Fermi). The single sign
of the second Casimir is the whole distinction between the two quantum statistics. -/
theorem bose_fermi_dichotomy (θ ξ Δ : ℝ) :
    Real.cosh θ ^ 2 - Real.sinh θ ^ 2 = 1
      ∧ bogoliubovU2 ξ Δ + bogoliubovV2 ξ Δ = 1 :=
  ⟨Real.cosh_sq_sub_sinh_sq θ, bogoliubov_normalization ξ Δ⟩

/-- **[The fermion Bogoliubov generator is the Bloch generator `−iσ₂`].** Complexifying the fermion (su(2))
Bogoliubov generator `J_F = !![0,−1;1,0]` gives `−i·σ₂`, i.e. `−sympForm` complexified
(`AlgebraicQFTQuasifree.PolarizatorBlochSphere.sympFormC_eq_I_smul_pauliY`, `AlgebraicQFT.SymplecticAdjointHadamard.sympForm_eq_neg_fermiGen`):
the generator of Fermi–Dirac statistics is the Pauli-`Y`/Bloch-sphere generator, and its square `J_F² = −1` is
the Verch pure-state complex structure. Fermi–Dirac lives on the Bloch/Poincaré sphere. -/
theorem fermiGen_eq_neg_I_pauliY :
    fermiBogoliubovGenerator.map (Complex.ofReal) = -(Complex.I • σ (Sum.inr 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiBogoliubovGenerator, pauliMatrix, Matrix.map_apply,
      Matrix.neg_apply, Complex.I_mul_I]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.SaitoBogoliubovBoseFermiStatistics

end
