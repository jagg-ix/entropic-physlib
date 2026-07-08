/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
public import Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.GreenFunction

/-!
# The complex Einstein full energy–momentum relation implies Dirac implies Schrödinger

This file proves the **directed chain**

 complex Einstein full energy `E² = (mc²)² + (cp)²` ⟹ Dirac ⟹ Schrödinger

as genuine implications (hypothesis ⟹ conclusion), composing so that the conclusion of each arrow is
the hypothesis of the next. It does *not* restate the existing conjunction bundle
(`fullEinstein_dirac_tdse_tise`); it gives the arrows and their composition.

## The arrows

* **Complex Einstein ⟹ complex Dirac (the Clifford linearization).** The full complex dispersion
 `E_C² = Δ_C² + (cp)²` with the complex rest energy `Δ_C = Δ_R − iΔ_I` (the complex-action `H_C = H_R − iH_I`
 convention) says exactly that `E_C²·1` is the square of the complex Dirac Hamiltonian
 `H_C` (`complexFullEinstein_implies_complexDirac`, via `complexDiracHamiltonian_sq`). The quadratic
 Einstein dispersion *is* the Dirac factorization `H_C² = (Δ_C² + (cp)²)·1`.

* **Full Einstein dispersion ⟹ Dirac eigenvalue.** At real (effective) mass the dispersion
 `E² = (mc²)² + (cp)²` implies `det(E·1 − H) = 0` — `E` is an eigenvalue of the Dirac Hamiltonian
 `H = (mc²)σ₃ + (cp)σ₁`, i.e. `H ψ = E ψ` (`fullEinstein_implies_dirac`, via
 `diracHamiltonian_eigenvalue_iff_kleinGordon`).

* **Dirac ⟹ Schrödinger kinetic energy.** From the Dirac eigenvalue condition the dispersion factors
 as `(E − mc²)(E + mc²) = (cp)²` (`dirac_implies_schrodinger_kinetic`); the relativistic kinetic
 energy `E − mc² = (cp)²/(E + mc²)` evaluated in the nonrelativistic regime `E + mc² → 2mc²` is the
 Schrödinger kinetic energy `p²/2m` (`dirac_kinetic_nonrel_eq_schrodinger`).

* **Schrödinger evolution (TDSE).** The on-shell mode `Ψ(t) = e^{−iEt/ℏ}` solves
 `iℏ ∂_t Ψ = E Ψ` (`greenKernel_satisfies_tdse`).

## The composition

`einstein_implies_dirac_implies_schrodinger` composes the arrows: the full Einstein dispersion implies
the Dirac eigenvalue, which implies the Schrödinger kinetic factorization and (in the nonrelativistic
limit) `p²/2m`, with the on-shell mode solving the TDSE.

## Scope

"Implies Dirac" is the dispersion ⟹ eigenvalue linearization (`H ψ = E ψ` at the mass shell). "Implies
Schrödinger" is the **energy-relation** reduction: the kinetic-energy factorization, its nonrelativistic
value `p²/2m`, and the TDSE for the on-shell mode. It is **not** a derivation of the Schrödinger PDE
*with potential* from the Dirac PDE — the spinor lower-component (Foldy–Wouthuysen) elimination is not
formalized. The complex sign convention is `H_C = H_R − iĤ_I` (`Δ_C = Δ_R − iΔ_I`); the
Nagao–Nielsen mass `m = m_R + i m_I` includes the opposite imaginary sign, so the complex arrow is
stated in the `H_C` convention.

## References

* A. Einstein 1905; P. A. M. Dirac 1928; E. Schrödinger 1926. This development:
 `Dirac.KleinGordonDiracFactorization`, `ComplexEinstein.FullEinsteinDispersionConsistency`,
 `Dirac.StressEnergyComplexHamiltonian`, `ComplexEinstein.ComplexMassEinsteinEquations`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
open Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain

/-! ## §A — complex Einstein full energy ⟹ complex Dirac (the Clifford linearization) -/

/-- **The complex Einstein full energy equation implies the complex Dirac equation.** The full
complex dispersion `E_C² = Δ_C² + (cp)²` with complex rest energy `Δ_C = Δ_R − iΔ_I` says exactly
that `E_C²·1` is the square of the complex Dirac Hamiltonian `H_C` — i.e. the quadratic Einstein
dispersion is the Dirac factorization `H_C² = (Δ_C² + (cp)²)·1`. So the complex Einstein energy is the
(squared) eigenvalue of `H_C`. -/
theorem complexFullEinstein_implies_complexDirac (Δ_R Δ_I vp : ℝ) (E_C : ℂ)
    (h : E_C ^ 2 = ((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ)) ^ 2 + (vp : ℂ) ^ 2) :
    E_C ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = complexDiracHamiltonian Δ_R Δ_I vp * complexDiracHamiltonian Δ_R Δ_I vp := by
  rw [complexDiracHamiltonian_sq, h]

/-! ## §B — full Einstein dispersion ⟹ Dirac eigenvalue (`H ψ = E ψ`) -/

/-- **The full Einstein dispersion implies the Dirac eigenvalue equation.** `E² = (mc²)² + (cp)²`
(here `Δ = mc²`, `v₀ = c`) implies `det(E·1 − H) = 0` — `E` is an eigenvalue of the Dirac Hamiltonian
`H = Δσ₃ + (cp)σ₁`. The quadratic dispersion linearizes to the Dirac eigenvalue problem. -/
theorem fullEinstein_implies_dirac (Δ v₀ p E : ℝ) (h : kleinGordonRelation Δ v₀ p E) :
    (E • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ (v₀ * p)).det = 0 :=
  (diracHamiltonian_eigenvalue_iff_kleinGordon Δ v₀ p E).mpr h

/-! ## §C — Dirac ⟹ Schrödinger kinetic energy -/

/-- **The Dirac eigenvalue equation implies the Schrödinger kinetic factorization.** From
`det(E·1 − H) = 0` the dispersion factors `(E − Δ)(E + Δ) = (v₀ p)²` — the relativistic kinetic
energy `E − mc²` times `E + mc²` is the momentum term. -/
theorem dirac_implies_schrodinger_kinetic (Δ v₀ p E : ℝ)
    (h : (E • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ (v₀ * p)).det = 0) :
    (E - Δ) * (E + Δ) = (v₀ * p) ^ 2 := by
  have hkg := (diracHamiltonian_eigenvalue_iff_kleinGordon Δ v₀ p E).mp h
  unfold kleinGordonRelation at hkg
  linear_combination hkg

/-- **The exact relativistic kinetic energy** `E − mc² = (cp)²/(E + mc²)` (for `E + Δ ≠ 0`), from the
Dirac eigenvalue condition. -/
theorem dirac_kinetic_exact (Δ v₀ p E : ℝ) (hEΔ : E + Δ ≠ 0)
    (h : (E • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ (v₀ * p)).det = 0) :
    E - Δ = (v₀ * p) ^ 2 / (E + Δ) := by
  rw [eq_div_iff hEΔ]
  exact dirac_implies_schrodinger_kinetic Δ v₀ p E h

/-- **The nonrelativistic kinetic energy is the Schrödinger kinetic energy `p²/2m`.** Evaluating the
exact relativistic kinetic energy `(cp)²/(E + mc²)` in the nonrelativistic regime `E + mc² → 2mc²`
(rest frame `E ≈ mc²`) gives `(cp)²/(2mc²) = p²/2m` — the Schrödinger kinetic energy. -/
theorem dirac_kinetic_nonrel_eq_schrodinger (m c p : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    (c * p) ^ 2 / (m * c ^ 2 + m * c ^ 2) = p ^ 2 / (2 * m) := by
  rw [show m * c ^ 2 + m * c ^ 2 = 2 * (m * c ^ 2) by ring]
  field_simp

/-! ## §D — the composed chain: complex Einstein ⟹ Dirac ⟹ Schrödinger -/

/-- **Complex Einstein full energy ⟹ Dirac ⟹ Schrödinger (composed).** For a physical (effective)
mass `m`, momentum `p`, speed `c`, and `ℏ ≠ 0`, starting from the full Einstein dispersion
`E² = (mc²)² + (cp)²`:

* **(Einstein ⟹ Dirac)** `E` is an eigenvalue of the Dirac Hamiltonian, `det(E·1 − H) = 0`;
* **(Dirac ⟹ Schrödinger)** the dispersion factors `(E − mc²)(E + mc²) = (cp)²`;
* **(nonrelativistic limit)** the kinetic energy reduces to the Schrödinger `p²/2m`;
* **(Schrödinger evolution)** the on-shell mode `e^{−iEt/ℏ}` solves the TDSE `iℏ ∂_t Ψ = E Ψ`.

The Dirac conclusion is the hypothesis of the Schrödinger step — a genuine implication chain. -/
theorem einstein_implies_dirac_implies_schrodinger (m c p : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - diracHamiltonian (m * c ^ 2) (c * p)).det = 0
      ∧ (einsteinEnergy m c p - m * c ^ 2) * (einsteinEnergy m c p + m * c ^ 2) = (c * p) ^ 2
      ∧ (c * p) ^ 2 / (m * c ^ 2 + m * c ^ 2) = p ^ 2 / (2 * m)
      ∧ (Complex.I * (ℏ : ℂ))
            * deriv (fun s : ℝ => greenKernel (einsteinEnergy m c p : ℂ) ℏ s) t
          = (einsteinEnergy m c p : ℂ) * greenKernel (einsteinEnergy m c p : ℂ) ℏ t := by
  have hdirac : (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      - diracHamiltonian (m * c ^ 2) (c * p)).det = 0 :=
    fullEinstein_implies_dirac (m * c ^ 2) c p (einsteinEnergy m c p) (einstein_fullDispersion m c p)
  exact ⟨hdirac,
    dirac_implies_schrodinger_kinetic (m * c ^ 2) c p (einsteinEnergy m c p) hdirac,
    dirac_kinetic_nonrel_eq_schrodinger m c p hm hc,
    greenKernel_satisfies_tdse (einsteinEnergy m c p : ℂ) ℏ t hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain

end

end
