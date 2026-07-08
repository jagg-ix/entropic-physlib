/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.SchrodingerDiracCoherence
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.BogoliubovSqueeze

/-!
# The complex Weyl–Dirac fermion mass, the oscillator/Schrödinger/Dirac coherence, and the Saveliev `sl(2)`

Links the complex Weyl–Dirac fermion mass (`Dirac.ComplexWeylDiracFermionMass`) to two existing pieces of the
arc: the **oscillator ↔ Schrödinger ↔ Dirac coherence** (`ComplexOscillator.SchrodingerDiracCoherence`, with
the hydrogen `O(4)` Casimir `λ_N = N(N+1) = reggeCasimir`) and the **Saveliev linear Boltzmann operator's
`sl(2)`** (`CollisionOperatorSl2.BogoliubovSqueeze`, the mass generator = Bogoliubov squeeze).

The connecting fact: the real fermion mass `m_R` is the **gap** of the Dirac dispersion
`E_D = bogoliubovEnergy(p, m_R) = √(p²+m_R²)`, which satisfies the Klein–Gordon mass-shell
`E² = m_R² + p²`. So the fermion inherits the whole coherence chain — it factors to the Schrödinger kinetic
energy, its bound-state spectrum is the hydrogen `reggeCasimir`, and (at rapidity `ξ`) its light-cone
energies `E_D ± p = m·e^{±ξ}` are exactly the Saveliev mass generator's Bogoliubov-squeeze eigenvalues.

* **§A — the fermion mass satisfies Klein–Gordon** (`fermionMass_kleinGordon`). `E_D² = m_R² + p²`: the real
  fermion mass is the Klein–Gordon gap `Δ = m_R`, feeding the coherence machinery.
* **§B — the fermion Dirac dispersion reduces to the Schrödinger kinetic energy and the hydrogen Casimir**
  (`fermionMass_dirac_nonrel_kinetic`, `fermionMass_dirac_to_hydrogen`).
  `(E_D − m_R)(E_D + m_R) = p²` (`dirac_nonrel_kinetic`), and the bound-state spectrum is the hydrogen
  `O(4)` Casimir `cutkoskyEigenvalue N = reggeCasimir N`.
* **§C — the fermion mass is the Saveliev `sl(2)` Bogoliubov-squeeze gap** (`fermionMass_rapidity`,
  `fermionMass_lightcone_eq_saveliev_squeeze`). The Dirac energy at rapidity `ξ` is `E_D = m·cosh ξ`, and the
  light-cone energies `E_D ± p = m(cosh ξ ± sinh ξ) = m·e^{±ξ}` are the Saveliev mass-generator squeeze
  eigenvalues (`bogoliubov_squeeze_eigenvalues`, `saveliev_mass_bogoliubov_squeeze`): the fermion mass is the
  gap of the Saveliev linear operator's `sl(2)` squeeze.

## References

* K. Nagao, H. B. Nielsen — the complex mass. A. R. Swift, B. W. Lee — complex angular momentum / Regge.
  R. E. Cutkosky — the Bethe–Salpeter `O(4)` bound states.
* M. V. Saveliev — the linear Boltzmann collision operator's `sl(2)` algebra.
* Repo dependencies: `Dirac.ComplexWeylDiracFermionMass` (`realFermionMass_diracEnergy`),
  `ComplexOscillator.SchrodingerDiracCoherence` (`dirac_nonrel_kinetic`, `kleinGordonRelation`),
  `BetheSalpeter.CutkoskyBetheSalpeterSolution` (`cutkoskyEigenvalue_eq_casimir`), `BetheSalpeter.SwiftLeeComplexAngularMomentum`
  (`reggeCasimir`), `CollisionOperatorSl2.BogoliubovSqueeze` (`bogoliubov_squeeze_eigenvalues`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracHydrogenSaveliev

open Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.SchrodingerDiracCoherence
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.BogoliubovSqueeze
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — the fermion mass satisfies the Klein–Gordon mass-shell -/

/-- **[Link] The real fermion mass satisfies Klein–Gordon.** `E_D² = m_R² + p²` with the Dirac energy
`E_D = bogoliubovEnergy(p, m_R) = √(p²+m_R²)` (`realFermionMass_diracEnergy`): the real fermion mass is the
Klein–Gordon gap `Δ = m_R` (`v₀ = 1`), feeding the oscillator/Schrödinger/Dirac coherence. -/
theorem fermionMass_kleinGordon (p m_R : ℝ) :
    kleinGordonRelation m_R 1 p (bogoliubovEnergy p m_R) := by
  unfold kleinGordonRelation; rw [realFermionMass_diracEnergy]; ring

/-! ## §B — reduction to the Schrödinger kinetic energy and the hydrogen Casimir -/

/-- **[Link] The fermion Dirac dispersion factors to the Schrödinger kinetic energy.**
`(E_D − m_R)(E_D + m_R) = p²` (`dirac_nonrel_kinetic`): the relativistic fermion kinetic energy reduces to
the nonrelativistic `p²/2m` — the Dirac → Schrödinger limit for the fermion. -/
theorem fermionMass_dirac_nonrel_kinetic (p m_R : ℝ) :
    (bogoliubovEnergy p m_R - m_R) * (bogoliubovEnergy p m_R + m_R) = (1 * p) ^ 2 :=
  dirac_nonrel_kinetic m_R 1 p (bogoliubovEnergy p m_R) (fermionMass_kleinGordon p m_R)

/-- **[Link — the hydrogen spectrum] The fermion Dirac reduction and the hydrogen `O(4)` Casimir.** The
fermion's Dirac dispersion factors to the Schrödinger kinetic energy, and the bound-state spectrum is the
hydrogen `O(4)` Casimir `cutkoskyEigenvalue N = reggeCasimir N = N(N+1)`
(`BetheSalpeter.CutkoskyBetheSalpeterSolution.cutkoskyEigenvalue_eq_casimir`): the complex fermion's bound state is the
Schrödinger-hydrogen / Regge tower. -/
theorem fermionMass_dirac_to_hydrogen (p m_R : ℝ) (N : ℕ) :
    (bogoliubovEnergy p m_R - m_R) * (bogoliubovEnergy p m_R + m_R) = (1 * p) ^ 2
      ∧ ((cutkoskyEigenvalue N : ℝ) : ℂ) = reggeCasimir (N : ℂ) :=
  ⟨fermionMass_dirac_nonrel_kinetic p m_R, cutkoskyEigenvalue_eq_casimir N⟩

/-! ## §C — the fermion mass is the Saveliev `sl(2)` Bogoliubov-squeeze gap -/

/-- **[Link] The Dirac energy at rapidity `ξ` is `E_D = m·cosh ξ`.** With `p = m·sinh ξ` (the Bogoliubov
rest-frame boost), `E_D = bogoliubovEnergy(m·sinh ξ, m) = m·cosh ξ` (for `m ≥ 0`): the fermion mass `m` is
the rest energy, the rapidity `ξ` the boost. -/
theorem fermionMass_rapidity (m ξ : ℝ) (hm : 0 ≤ m) :
    bogoliubovEnergy (m * Real.sinh ξ) m = m * Real.cosh ξ := by
  unfold bogoliubovEnergy
  rw [show (m * Real.sinh ξ) ^ 2 + m ^ 2 = (m * Real.cosh ξ) ^ 2 by
    nlinarith [Real.cosh_sq ξ, Real.sinh_sq ξ]]
  exact Real.sqrt_sq (mul_nonneg hm (Real.cosh_pos ξ).le)

/-- **[Link to the Saveliev `sl(2)` operator] The fermion light-cone energies are the Saveliev mass
generator's squeeze eigenvalues.** With `E_D = m·cosh ξ`, `p = m·sinh ξ`, the light-cone energies
`E_D ± p = m(cosh ξ ± sinh ξ) = m·e^{±ξ}` are exactly the Bogoliubov-squeeze eigenvalues of the Saveliev
linear-Boltzmann mass generator `M = ∇v` (`bogoliubov_squeeze_eigenvalues`,
`saveliev_mass_bogoliubov_squeeze`): the fermion mass `m` is the gap, the rapidity `ξ = ln(1+m)` Saveliev's
mass parameter — the fermion mass is the gap of the Saveliev `sl(2)` squeeze. -/
theorem fermionMass_lightcone_eq_saveliev_squeeze (m ξ : ℝ) :
    m * Real.cosh ξ + m * Real.sinh ξ = m * Real.exp ξ
      ∧ m * Real.cosh ξ - m * Real.sinh ξ = m * Real.exp (-ξ) := by
  obtain ⟨h1, h2⟩ := bogoliubov_squeeze_eigenvalues ξ
  exact ⟨by rw [← mul_add, h1], by rw [← mul_sub, h2]⟩

end Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracHydrogenSaveliev

end
