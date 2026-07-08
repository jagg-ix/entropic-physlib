/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval
public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

/-!
# The polar Minkowski interval as the Dirac spectrum and Einstein's `E = mc²`

`Rapidity.PoincarePolarMinkowskiInterval` proved the polar coordinate is a Minkowski interval: the
Bogoliubov pair `(E, ξ)` is timelike with invariant `E² − ξ² = Δ²` and `(E, ξ)` is a boost of the
rest vector `(Δ, 0)`. This file inspects that result through the **Dirac equation** and **Einstein's
mass–energy equivalence**, identifying the abstract gap `Δ` as the physical rest mass.

## The identifications (each proven, not assumed)

* **Einstein.** The gap is the rest energy `Δ = m·c²` (`gap_eq_einstein_rest_energy`, from
  `relativisticInertialMass`/`energy_eq_inertialMass_mul_c_sq` with `c = v₀`). So the Minkowski
  invariant `E² − ξ² = Δ²` is Einstein's energy–momentum relation `E² = ξ² + (mc²)²`
  (`bogoliubov_energy_kleinGordon`, the Klein–Gordon mass-shell with `v₀ = 1`, `ξ = pc`).
* **Dirac.** `E` is an eigenvalue of the Dirac Hamiltonian `H = Δσ₃ + ξσ₁`
  (`bogoliubov_energy_dirac_eigenvalue`): the Minkowski mass-shell **is** the Dirac spectrum
  `±√(ξ²+Δ²)`. At rest (`ξ = 0`) the eigenvalues are `±Δ = ±mc²`
  (`dirac_rest_eigenvalue_iff_einstein_rest`) — Einstein's rest energy as the particle/antiparticle
  Dirac doublet.
* **Lorentz factor.** The rapidity `η` of `exists_rapidity` gives `E = (cosh η)·Δ = γ·mc²`
  (`einstein_energy_eq_gamma_rest_energy`) with `γ = cosh η ≥ 1` (`lorentzFactor_ge_one`) — Einstein's
  relativistic energy `E = γmc²`, so `E ≥ Δ = mc²` (`einstein_energy_ge_rest_energy`, equality at
  rest).

## Main results

* `gap_eq_einstein_rest_energy` — `Δ = m·c²` (gap = rest energy).
* `bogoliubov_energy_kleinGordon` — `E² = Δ² + ξ²` (Einstein/Klein–Gordon mass-shell).
* `bogoliubov_energy_dirac_eigenvalue` — `E` is a Dirac-Hamiltonian eigenvalue (shell = spectrum).
* `dirac_rest_eigenvalue_iff_einstein_rest` — at rest the Dirac eigenvalues are `±mc²`.
* `lorentzFactor`, `lorentzFactor_ge_one`, `einstein_energy_eq_gamma_rest_energy`,
  `einstein_energy_ge_rest_energy` — `E = γmc² ≥ mc²`.
* `minkowski_interval_is_dirac_einstein_massShell` — the bundled identification.

## References

* A. Einstein, Ann. Phys. 18 (1905) 639 (`E = mc²`); P. A. M. Dirac, Proc. R. Soc. A 117 (1928) 610.
* `Rapidity.PoincarePolarMinkowskiInterval`, `Dirac.KleinGordonDiracFactorization`, `Dirac.ConfinedPhotonDiracDispersion`,
  `MassOrigin.BosonicInertialMass`, `Bogoliubov.Transformation` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
open Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass

/-! ## §A — Einstein: the gap is the rest energy `Δ = m·c²` -/

/-- **The gap is Einstein's rest energy** `Δ = m·c²`: the Minkowski invariant `Δ` of the timelike
energy vector is the inertial mass `m = relativisticInertialMass Δ v₀` times `c² = v₀²`. So the
abstract gap *is* the rest mass (energy) — mass–energy equivalence. -/
theorem gap_eq_einstein_rest_energy (Δ v₀ : ℝ) (hv : 0 < v₀) :
    Δ = relativisticInertialMass Δ v₀ * v₀ ^ 2 :=
  energy_eq_inertialMass_mul_c_sq Δ v₀ hv

/-- **The Einstein / Klein–Gordon mass-shell** `E² = Δ² + ξ²`: the Minkowski interval `E² − ξ² = Δ²`
is the relativistic energy–momentum relation with rest energy `Δ = mc²` and `ξ = pc` (taking the
renormalised speed `v₀ = 1`). -/
theorem bogoliubov_energy_kleinGordon (ξ Δ : ℝ) :
    kleinGordonRelation Δ 1 ξ (bogoliubovEnergy ξ Δ) := by
  rw [bogoliubov_energy_eq_photonDispersion]
  exact photonDispersion_kleinGordon Δ 1 ξ

/-! ## §B — Dirac: the mass-shell is the Dirac spectrum, at rest `±mc²` -/

/-- **`E` is a Dirac-Hamiltonian eigenvalue**: `det(E·1 − H) = 0` for `H = Δσ₃ + ξσ₁`
(`diracHamiltonian Δ ξ`). The Minkowski mass-shell of the Bogoliubov energy vector **is** the Dirac
spectrum `±√(ξ²+Δ²)` (the Klein–Gordon factorisation = the Dirac equation). -/
theorem bogoliubov_energy_dirac_eigenvalue (ξ Δ : ℝ) :
    (bogoliubovEnergy ξ Δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ ξ).det = 0 := by
  have h := (diracHamiltonian_eigenvalue_iff_kleinGordon Δ 1 ξ (bogoliubovEnergy ξ Δ)).mpr
    (bogoliubov_energy_kleinGordon ξ Δ)
  simpa using h

/-- **At rest the Dirac eigenvalues are `±mc²`**: with `ξ = 0` (zero momentum) the Dirac Hamiltonian
`Δσ₃` has eigenvalue `lam` iff `lam² = Δ²`, i.e. `lam = ±Δ = ±mc²` — Einstein's rest energy as the
particle/antiparticle Dirac doublet. -/
theorem dirac_rest_eigenvalue_iff_einstein_rest (Δ lam : ℝ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ 0).det = 0 ↔ lam ^ 2 = Δ ^ 2 := by
  have h := diracHamiltonian_eigenvalue_iff_kleinGordon Δ 1 0 lam
  simp only [mul_zero] at h
  rw [h, kleinGordonRelation]
  constructor <;> intro hh <;> nlinarith [hh]

/-! ## §C — Lorentz factor: `E = γ·mc² ≥ mc²` -/

/-- **The Lorentz factor** `γ = cosh η` of the boost with rapidity `η`. -/
def lorentzFactor (η : ℝ) : ℝ := Real.cosh η

/-- **`γ ≥ 1`** (`cosh η ≥ 1`): the relativistic energy is never below the rest energy. -/
theorem lorentzFactor_ge_one (η : ℝ) : 1 ≤ lorentzFactor η := by
  unfold lorentzFactor
  nlinarith [Real.cosh_sq_sub_sinh_sq η, sq_nonneg (Real.sinh η), Real.cosh_pos η]

/-- **Einstein's relativistic energy** `E = γ·mc²`: the Bogoliubov energy is the Lorentz factor
`γ = cosh η` times the rest energy `Δ = mc²` (the rapidity `η` from `exists_rapidity`). -/
theorem einstein_energy_eq_gamma_rest_energy (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ η : ℝ, bogoliubovEnergy ξ Δ = lorentzFactor η * Δ := by
  obtain ⟨η, _, hE⟩ := exists_rapidity ξ Δ hΔ
  exact ⟨η, by rw [hE, lorentzFactor, mul_comm]⟩

/-- **The relativistic energy is at least the rest energy** `mc² ≤ E` (equality at rest `ξ = 0`):
`E = √(ξ²+Δ²) ≥ √(Δ²) = Δ` — the Einstein inequality `E = γmc² ≥ mc²`. -/
theorem einstein_energy_ge_rest_energy (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    Δ ≤ bogoliubovEnergy ξ Δ := by
  unfold bogoliubovEnergy
  calc Δ = Real.sqrt (Δ ^ 2) := (Real.sqrt_sq hΔ.le).symm
    _ ≤ Real.sqrt (ξ ^ 2 + Δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ξ])

/-! ## §D — the bundled identification -/

/-- **The polar Minkowski interval is the Dirac–Einstein mass-shell.** For a genuine gap `Δ > 0`
and renormalised speed `v₀ > 0`:

* **(i)** the gap is Einstein's rest energy `Δ = m·c²`;
* **(ii)** the Minkowski interval `E² − ξ² = Δ²` is the Einstein/Klein–Gordon mass-shell `E² = Δ² + ξ²`;
* **(iii)** `E` is a Dirac-Hamiltonian eigenvalue — the mass-shell is the Dirac spectrum;
* **(iv)** `E = γ·mc²` with the Lorentz factor `γ = cosh η ≥ 1` — Einstein's relativistic energy.

So the gap `Δ` that confines the polar coordinate inside the light cone is exactly the rest mass
`mc²`, the energy vector is the Dirac spectrum, and the boost rapidity is the Lorentz factor. -/
theorem minkowski_interval_is_dirac_einstein_massShell (ξ Δ v₀ : ℝ) (hΔ : 0 < Δ) (hv : 0 < v₀) :
    Δ = relativisticInertialMass Δ v₀ * v₀ ^ 2
      ∧ kleinGordonRelation Δ 1 ξ (bogoliubovEnergy ξ Δ)
      ∧ (bogoliubovEnergy ξ Δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ ξ).det = 0
      ∧ ∃ η : ℝ, bogoliubovEnergy ξ Δ = lorentzFactor η * Δ ∧ 1 ≤ lorentzFactor η := by
  refine ⟨gap_eq_einstein_rest_energy Δ v₀ hv, bogoliubov_energy_kleinGordon ξ Δ,
    bogoliubov_energy_dirac_eigenvalue ξ Δ, ?_⟩
  obtain ⟨η, hh⟩ := einstein_energy_eq_gamma_rest_energy ξ Δ hΔ
  exact ⟨η, hh, lorentzFactor_ge_one η⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass

end

end
