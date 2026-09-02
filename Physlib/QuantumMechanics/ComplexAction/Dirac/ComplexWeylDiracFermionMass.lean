/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.DiracFisherQuantumPotential

/-!
# The fermionic complex mass in the standard Dirac mass shell

The Dirac equation couples the two Weyl (chiral) spinors `ψ_L, ψ_R` through the **mass term**: in the chiral
basis `iσ̄·∂ ψ_L = m ψ_R`, `iσ·∂ ψ_R = m ψ_L`, so the mass `m` is the off-diagonal chirality coupling. The
**Weyl equation** is the massless limit `m = 0`, where the chiralities decouple and the spinor is luminal
(`E = |p|`). Combining the two coupled Weyl equations gives the mass-shell `E² = p² + m²`.

This file does not introduce a new Dirac equation merely from the use of complex scalars: the standard
Dirac equation is already a complex-spinor equation.  Instead it feeds the **Nagao–Nielsen complex mass**
`m_C = m_R + i m_I` of the
complex-action oscillator
(`PathIntegral.MomentumPathIntegral`, `phaseLagrangian`, with `Im m > 0` the convergence condition) into the Dirac
mass-shell, deriving an equation for the (complex) fermionic mass:

  `m_C² = E_C² − p²`,   `Re(m_C²) = m_R² − m_I²`,   `Im(m_C²) = 2 m_R m_I`.

So the imaginary (dissipative) part `m_I` **lowers the physical mass-squared** (`m_R² − m_I²`) and supplies a
**decay width** (`2 m_R m_I`); the real-mass invariant `|m_C|² = m_R² + m_I²` is the Nagao–Nielsen effective
mass times `m_R`.

* **§A — the complex fermion mass** (`complexFermionMass`, `_re`, `_im`). `m_C = m_R + i m_I`, the NN
  complex-action oscillator mass that couples the Weyl chiralities.
* **§B — the fermionic mass-squared equation** (`complexFermionMass_sq_re`, `complexFermionMass_sq_im`,
  `complexFermionMassSq_from_diracDispersion`). The Dirac mass-shell `m_C² = E_C² − p²` with the
  real/imaginary split:
  physical mass-squared `m_R² − m_I²` and decay width `2 m_R m_I`.
* **§C — the massless dispersion limit** (`complexFermionMass_eq_zero_iff`,
  `complexMassDiracEnergySq_massless`). `m_C = 0 ⟺ m_R = m_I = 0`; then `E_C² = p²` (`E = |p|`). The
  chiral Weyl-decoupling statement is physics context, not separately formalized here.
* **§D — links to the NN oscillator and the Bogoliubov/Dirac dispersion**
  (`fermionInvariantMassSq_eq_effectiveMass`, `realFermionMass_diracEnergy`). The invariant mass
  `|m_C|² = m_R² + m_I² = m_R · effectiveMass(m_R, m_I)` (the NN effective mass); the real-mass case
  (`m_I = 0`) gives `E_D = bogoliubovEnergy(p, m_R) = √(p²+m_R²)` — the fermion mass is the Bogoliubov/Dirac
  gap of `GravLapse.DiracFisherQuantumPotential`.

**Coherence and hydrogen / Saveliev link** (`Dirac.ComplexWeylDiracHydrogenSaveliev`). Because
`realFermionMass_diracEnergy` is the Klein–Gordon mass-shell `E_D² = m_R² + p²`, the fermion mass joins the
**oscillator ↔ Schrödinger ↔ Dirac coherence** (`ComplexOscillator.SchrodingerDiracCoherence`): the Dirac
dispersion factors `(E_D − m_R)(E_D + m_R) = p²` to the Schrödinger kinetic energy, the bound-state spectrum
is the hydrogen `O(4)` Casimir `N(N+1) = reggeCasimir`, and the fermion light-cone energies
`E_D ± p = m·e^{±ξ}` are the **Saveliev linear-Boltzmann `sl(2)` mass-generator squeeze eigenvalues** — the
fermion mass is the gap of the Saveliev `sl(2)` Bogoliubov squeeze.

## References

* H. Weyl, *Elektron und Gravitation*, Z. Phys. 56 (1929) 330 — the Weyl equation. P. A. M. Dirac (1928).
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory* — the complex mass `m = m_R + i m_I`
  (`PathIntegral.MomentumPathIntegral`, `Im m > 0`).
* Repo carriers: `PathIntegral.MomentumPathIntegral` (`effectiveMass`, complex mass), `Bogoliubov.Transformation`
  (`bogoliubovEnergy`), `GravLapse.DiracFisherQuantumPotential` (`diracGap_eq_bogoliubovEnergy_sq`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation


/-- **[Nagao–Nielsen complex mass] The complex fermionic (Dirac) mass** `m_C = m_R + i m_I` — the chirality
coupling of the Weyl spinors, taken complex as the Nagao–Nielsen complex-action oscillator mass
(`PathIntegral.MomentumPathIntegral`, `Im m_C = m_I > 0` for convergence). -/
noncomputable def complexFermionMass (m_R m_I : ℝ) : ℂ := (m_R : ℂ) + Complex.I * (m_I : ℂ)

/-- The real part of the complex fermion mass is `m_R`. -/
lemma complexFermionMass_re (m_R m_I : ℝ) : (complexFermionMass m_R m_I).re = m_R := by
  simp [complexFermionMass]

/-- The imaginary part of the complex fermion mass is `m_I` (the NN gap / decay part). -/
lemma complexFermionMass_im (m_R m_I : ℝ) : (complexFermionMass m_R m_I).im = m_I := by
  simp [complexFermionMass]


/-- **[The fermionic mass equation — real part] `Re(m_C²) = m_R² − m_I²`.** The physical mass-squared: the
imaginary (dissipative) mass `m_I` *lowers* the real mass-squared. -/
lemma complexFermionMass_sq_re (m_R m_I : ℝ) :
    ((complexFermionMass m_R m_I) ^ 2).re = m_R ^ 2 - m_I ^ 2 := by
  rw [pow_two, Complex.mul_re, complexFermionMass_re, complexFermionMass_im]; ring

/-- **[The fermionic mass equation — imaginary part] `Im(m_C²) = 2 m_R m_I`.** The decay width: the product
of the real and imaginary masses. -/
lemma complexFermionMass_sq_im (m_R m_I : ℝ) :
    ((complexFermionMass m_R m_I) ^ 2).im = 2 * m_R * m_I := by
  rw [pow_two, Complex.mul_im, complexFermionMass_re, complexFermionMass_im]; ring

/-- **[Complex-mass Dirac dispersion] `E_C² = p² + m_C²`** — the standard Dirac mass shell with the
mass parameter complexified to `m_C`; the Dirac equation itself is already complex-valued. -/
noncomputable def complexMassDiracEnergySq (p m_R m_I : ℝ) : ℂ :=
  (p : ℂ) ^ 2 + (complexFermionMass m_R m_I) ^ 2

/-- **[The fermionic mass from the dispersion] `m_C² = E_C² − p²`.** The complex fermion mass-squared is the
Dirac dispersion minus the kinetic term — the invariant mass read off from the mass shell. -/
lemma complexFermionMassSq_from_diracDispersion (p m_R m_I : ℝ) :
    (complexFermionMass m_R m_I) ^ 2 = complexMassDiracEnergySq p m_R m_I - (p : ℂ) ^ 2 := by
  unfold complexMassDiracEnergySq; ring


/-- **[Massless limit] The complex fermion mass vanishes iff both parts vanish.** `m_C = 0 ⟺
 m_R = 0 ∧ m_I = 0`. -/
lemma complexFermionMass_eq_zero_iff (m_R m_I : ℝ) :
    complexFermionMass m_R m_I = 0 ↔ m_R = 0 ∧ m_I = 0 := by
  rw [Complex.ext_iff, complexFermionMass_re, complexFermionMass_im]; simp

/-- **[Massless dispersion]** `E_C² = p²` (`E = |p|`) for the complex-mass Dirac mass shell at zero mass. -/
lemma complexMassDiracEnergySq_massless (p : ℝ) : complexMassDiracEnergySq p 0 0 = (p : ℂ) ^ 2 := by
  unfold complexMassDiracEnergySq complexFermionMass; simp


/-- **[NN effective mass] The invariant fermion mass is the Nagao–Nielsen effective mass.**
`|m_C|² = m_R² + m_I² = m_R · effectiveMass(m_R, m_I)` (`PathIntegral.MomentumPathIntegral.effectiveMass`,
`= m_R + m_I²/m_R`): the squared modulus of the complex fermion mass is the NN effective mass scaled by the
real mass. -/
lemma fermionInvariantMassSq_eq_effectiveMass (m_R m_I : ℝ) (h : m_R ≠ 0) :
    m_R ^ 2 + m_I ^ 2 = m_R * effectiveMass m_R m_I := by
  unfold effectiveMass; field_simp

/-- **[Bogoliubov/Dirac gap] The real fermion mass gives the Dirac dispersion.** At `m_I = 0` (the reversible
/ real-mass point), the Dirac energy is `E_D = bogoliubovEnergy(p, m_R) = √(p² + m_R²)`
(`bogoliubovEnergy² = p² + m_R²`): the real fermionic mass is the Bogoliubov gap `Δ` of the Dirac field
(`GravLapse.DiracFisherQuantumPotential.diracGap_eq_bogoliubovEnergy_sq`). This `E_D² = p² + m_R²` is exactly
Bennett's parametrized-Dirac mass shell `E_p² = m_p² + |p|²` with `m_p = √(−p·p)`
(`FirstQuantizedQED.ParametrizedDirac.bennett_energy_eq_bogoliubov`). -/
lemma realFermionMass_diracEnergy (p m_R : ℝ) :
    bogoliubovEnergy p m_R ^ 2 = p ^ 2 + m_R ^ 2 := by
  unfold bogoliubovEnergy; exact Real.sq_sqrt (by positivity)

end Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass

end
