/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

/-!
# The matter 4-momentum: full Einstein shell = Minkowski invariant = Bogoliubov rest mass

This is target **A1** of the complex-Einstein-field-equation roadmap: the relativistic 4-momentum
`p^μ = (E/c, p⃗)` of the matter on the full Einstein mass shell, with its invariant mass identified
across three formalizations of this development.

For the on-shell energy `E = √((mc²)² + (cp)²)` (`ComplexEinstein.FullEinsteinDispersionConsistency.einsteinEnergy`),
the time component is `p⁰ = E/c`. The Minkowski norm of the 4-momentum is the rest mass squared:

  `(E/c)² − p² = (mc)²`   (`minkowski_norm_eq_mass_sq`).

The single value `(mc)²` is simultaneously:

* the **Minkowski form** of the energy–momentum vector, `lorentzianForm(E/c + ip) = (mc)²`
  (`fourMomentum_lorentzianForm`);
* the **bosonic Bogoliubov diagonalized frequency** of the pair `(E/c, p)`, namely
  `diagonalizedFrequency (E/c) p = mc` (`diagonalizedFrequency_eq_restMass`,
  `Bogoliubov.BosonicBogoliubovDiagonalization`) — so the Bogoliubov diagonalization of the matter is the
  passage to its **rest frame**;
* and the 4-momentum is the **Lorentz boost** of the rest 4-momentum `(mc, 0)`:
  `E/c = mc cosh θ`, `p = mc sinh θ` (`fourMomentum_is_boost_of_rest`).

With the Nagao–Nielsen complex mass `m = m_R + i m_I`, the physical invariant is the effective mass
`m_eff = |m|²/Re m` (`complexMass_fourMomentum_restMass`,
`ComplexEinstein.ComplexMassEinsteinEquations.effectiveMass`).

So the full Einstein energy–momentum relation, the Minkowski symplectic form, and the bosonic
Bogoliubov diagonalization are three faces of the same invariant mass — the matter source whose
stress-energy (target A2) will feed the complex Einstein equations.

## Main results

* `minkowski_norm_eq_mass_sq` — `(E/c)² − p² = (mc)²` (the mass shell).
* `fourMomentum_lorentzianForm` — `lorentzianForm(E/c + ip) = (mc)²`.
* `diagonalizedFrequency_eq_restMass` — `diagonalizedFrequency (E/c) p = mc` (Bogoliubov rest mass).
* `fourMomentum_is_boost_of_rest` — the 4-momentum is the boost of `(mc, 0)`.
* `complexMass_fourMomentum_restMass` — the complex-mass invariant is the effective mass `m_eff`.
* `matter_fourMomentum_mass_shell` — the bundled identification.

## References

* A. Einstein, Ann. Phys. **323** (1905) 639. doi:10.1002/andp.19053231314.
* P. T. Nam, M. Napiórkowski, J. P. Solovej, J. Funct. Anal. **270** (2016) 4340.
  doi:10.1016/j.jfa.2015.12.007.
* This development: `ComplexEinstein.FullEinsteinDispersionConsistency`, `Bogoliubov.BosonicBogoliubovDiagonalization`,
  `ComplexEinstein.ComplexMassEinsteinEquations`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

namespace Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.MatterFourMomentum

/-! ## §A — the 4-momentum mass shell `(E/c)² − p² = (mc)²` -/

/-- **The Minkowski norm of the 4-momentum is the rest mass squared** `(E/c)² − p² = (mc)²`
(`p⁰ = E/c`, `E = √((mc²)² + (cp)²)`). The full Einstein relation written as the mass shell. -/
theorem minkowski_norm_eq_mass_sq (m c p : ℝ) (hc : c ≠ 0) :
    (einsteinEnergy m c p / c) ^ 2 - p ^ 2 = (m * c) ^ 2 := by
  rw [div_pow, einsteinEnergy_sq]
  field_simp
  ring

/-- **The mass shell is the Minkowski form of the energy–momentum vector** `lorentzianForm(E/c + ip)
= (mc)²`. -/
theorem fourMomentum_lorentzianForm (m c p : ℝ) (hc : c ≠ 0) :
    lorentzianForm (((einsteinEnergy m c p / c : ℝ) : ℂ) + ((p : ℝ) : ℂ) * Complex.I)
      = (m * c) ^ 2 := by
  rw [lorentzianForm_ofReal_add_mul_I, minkowski_norm_eq_mass_sq m c p hc]

/-! ## §B — the mass shell is the bosonic Bogoliubov diagonalized rest mass -/

/-- **The Bogoliubov diagonalization of the matter is its rest frame** `diagonalizedFrequency (E/c) p
= mc`: the bosonic Bogoliubov diagonalized frequency of the energy–momentum pair `(E/c, p)` is the
rest mass `mc` (the boost-invariant of `Bogoliubov.BosonicBogoliubovDiagonalization`). -/
theorem diagonalizedFrequency_eq_restMass (m c p : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    diagonalizedFrequency (einsteinEnergy m c p / c) p = m * c := by
  unfold diagonalizedFrequency
  rw [minkowski_norm_eq_mass_sq m c p hc.ne', Real.sqrt_sq (mul_nonneg hm hc.le)]

/-- **The 4-momentum is the Lorentz boost of the rest 4-momentum** `(mc, 0)`: there is a rapidity `θ`
with `p = mc sinh θ` and `E/c = mc cosh θ`. The moving matter is the boost (= bosonic Bogoliubov
transformation) of the rest state. -/
theorem fourMomentum_is_boost_of_rest (m c p : ℝ) (hc : 0 < c) (hm : 0 ≤ m)
    (hsub : |p| < einsteinEnergy m c p / c) :
    ∃ θ : ℝ, p = (m * c) * Real.sinh θ ∧ einsteinEnergy m c p / c = (m * c) * Real.cosh θ := by
  have hh : 0 < einsteinEnergy m c p / c := lt_of_le_of_lt (abs_nonneg p) hsub
  obtain ⟨θ, hsin, hcos⟩ := exists_diagonalizing_rapidity (einsteinEnergy m c p / c) p hh hsub
  rw [diagonalizedFrequency_eq_restMass m c p hc hm] at hsin hcos
  exact ⟨θ, hsin, hcos⟩

/-! ## §C — the Nagao–Nielsen complex mass: the invariant is the effective mass -/

/-- **The complex-mass invariant is the effective mass** `m_eff = |m|²/Re m`: with the Nagao–Nielsen
complex mass `m = m_R + i m_I`, the diagonalized rest mass of the 4-momentum is the physical
effective mass times `c` (`ComplexEinstein.ComplexMassEinsteinEquations`). -/
theorem complexMass_fourMomentum_restMass (m_R m_I c p : ℝ) (hc : 0 < c)
    (hm : 0 ≤ effectiveMass m_R m_I) :
    diagonalizedFrequency (einsteinEnergy (effectiveMass m_R m_I) c p / c) p
      = effectiveMass m_R m_I * c :=
  diagonalizedFrequency_eq_restMass (effectiveMass m_R m_I) c p hc hm

/-! ## §D — the bundled identification -/

/-- **The matter 4-momentum's invariant mass, three ways.** For a physical mass `m ≥ 0`, speed
`c > 0`, sub-luminal momentum `|p| < E/c`:

* **mass shell** — `(E/c)² − p² = (mc)²`;
* **Minkowski form** — `lorentzianForm(E/c + ip) = (mc)²`;
* **Bogoliubov rest mass** — `diagonalizedFrequency (E/c) p = mc`;
* **boost of rest** — `(E/c, p) = (mc cosh θ, mc sinh θ)` for a rapidity `θ`.

The full Einstein relation, the Minkowski symplectic metric, and the bosonic Bogoliubov
diagonalization agree on the single invariant `mc`. -/
theorem matter_fourMomentum_mass_shell (m c p : ℝ) (hc : 0 < c) (hm : 0 ≤ m)
    (hsub : |p| < einsteinEnergy m c p / c) :
    (einsteinEnergy m c p / c) ^ 2 - p ^ 2 = (m * c) ^ 2
      ∧ lorentzianForm (((einsteinEnergy m c p / c : ℝ) : ℂ) + ((p : ℝ) : ℂ) * Complex.I)
          = (m * c) ^ 2
      ∧ diagonalizedFrequency (einsteinEnergy m c p / c) p = m * c
      ∧ ∃ θ : ℝ, p = (m * c) * Real.sinh θ ∧ einsteinEnergy m c p / c = (m * c) * Real.cosh θ :=
  ⟨minkowski_norm_eq_mass_sq m c p hc.ne', fourMomentum_lorentzianForm m c p hc.ne',
   diagonalizedFrequency_eq_restMass m c p hc hm, fourMomentum_is_boost_of_rest m c p hc hm hsub⟩

end Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.MatterFourMomentum

end

end
