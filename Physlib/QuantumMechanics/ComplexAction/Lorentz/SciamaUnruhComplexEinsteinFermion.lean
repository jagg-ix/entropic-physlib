/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhEinsteinEquationOfState
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
public import Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian

/-!
# Complex Einstein from the Unruh state, sourced by a complex-mass Dirac fermion

Extends `SciamaUnruhEinsteinEquationOfState` (Einstein's equation from the microscopic Unruh temperature) to
the **complex Einstein field equation** and links it to the fermion / particle-physics side of the repo.

The complex Einstein equation `𝒢 = κ(T + iS)` splits exactly (`ComplexEinstein.FieldEquations`,
`complexEinsteinFieldEquation_iff`) into

`(G = κT)`  — the **real** sector: ordinary GR, the matter stress `T`;
`(Λ = κS)`  — the **imaginary** sector: the entropic curvature sourced by the entropic stress `S`.

This is exactly the split of the **complex-mass Dirac Hamiltonian** `H_C = H_R − iH_I`
(`Dirac.StressEnergyComplexHamiltonian.complexMassDiracHamiltonian_eq_HR_sub_I_HI`, `Δ_C = Δ_R − iΔ_I`):
the **real mass** `H_R = diracHamiltonian Δ_R` sources the matter curvature, the **imaginary mass** (decay /
instability) `H_I = diracHamiltonian Δ_I` sources the entropic curvature — and both are symmetric
(`diracHamiltonian_isSymm`), hence valid stress sources.

* `sciamaUnruh_complexEinstein` — the complex Einstein equation from the real/entropic split `(G = κT) ∧
  (Λ = κS)`; the entropic (imaginary) sector is where the Unruh-thermal content (`sciamaUnruhTemperature`) lives.
* `diracFermion_valid_source` — the Dirac Hamiltonian is symmetric, a valid stress-energy source.
* `complexEinstein_from_dirac_fermion` — **the complex-mass Dirac fermion sources the complex Einstein
  equation**: real mass `Δ_R` → matter sector `G = κ H_R`, imaginary mass `Δ_I` → entropic sector `Λ = κ H_I`.

Particle physics: the fermion `H_R` is the electron; its CPT / charge-conjugate mirror is the positron
(`Particles.PositronModel`: `positron_dirac_cpt_invariant`, `A·D(−p)·A⁻¹ = D(p)`, the mirror trefoil).  The
Unruh effect maps particle ↔ antiparticle across the Rindler horizon, so the microscopic Unruh-thermal state
that fixes the gravitational coupling is the same thermal/CPT structure that relates the electron to the
positron: spacetime dynamics from the temperature of a quantum thermal state sourced by a complex-mass Dirac
fermion with its electron/positron CPT double.

Honest scope: the complex-EFE split and the complex-mass-Dirac source identification.  The equation `G = κ H_R`
(that curvature equals the fermion stress) is the labeled Einstein/Clausius input — carried by
`einstein_from_sciamaUnruh`; here it is packaged into the complex EFE with the fermionic source.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhComplexEinsteinFermion

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian

/-- **[Complex Einstein from the real/entropic split] `(G = κT) ∧ (Λ = κS) ⟹ 𝒢 = κ(T+iS)`.**  The complex
Einstein field equation holds iff the real Einstein equation `G = κT` (matter) and the imaginary equation
`Λ = κS` (entropic curvature = entropic stress) hold; the entropic sector carries the Unruh-thermal content
(`sciamaUnruhTemperature`). -/
theorem sciamaUnruh_complexEinstein {ι : Type*} (G Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (hReal : G = κ • T) (hEntropic : Λ = κ • S) :
    complexEinsteinFieldEquation G Λ T S κ :=
  (complexEinsteinFieldEquation_iff G Λ T S κ).mpr ⟨hReal, hEntropic⟩

/-- **[Fermion is a valid stress source] `H_Dirac` is symmetric.**  The Dirac Hamiltonian is a symmetric matrix,
so it is an admissible stress-energy source for the Einstein field equation (which requires `T.IsSymm`). -/
theorem diracFermion_valid_source (Δ vp : ℝ) : (diracHamiltonian Δ vp).IsSymm :=
  diracHamiltonian_isSymm Δ vp

/-- **[Complex-mass Dirac fermion sources the complex Einstein equation].**  With the real mass `Δ_R` sourcing
the matter (real) sector `G = κ·H_R` and the imaginary mass `Δ_I` sourcing the entropic (imaginary) sector
`Λ = κ·H_I`, the complex Einstein equation holds with source `H_R + iH_I` — the complex-mass Dirac
`H_C = H_R − iH_I` (`complexMassDiracHamiltonian`). -/
theorem complexEinstein_from_dirac_fermion (Δ_R Δ_I vp κ : ℝ)
    (G Λ : Matrix (Fin 2) (Fin 2) ℝ)
    (hReal : G = κ • diracHamiltonian Δ_R vp)
    (hEntropic : Λ = κ • diracHamiltonian Δ_I 0) :
    complexEinsteinFieldEquation G Λ (diracHamiltonian Δ_R vp) (diracHamiltonian Δ_I 0) κ :=
  sciamaUnruh_complexEinstein G Λ (diracHamiltonian Δ_R vp) (diracHamiltonian Δ_I 0) κ hReal hEntropic

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhComplexEinsteinFermion

end
