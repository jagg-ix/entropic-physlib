/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HerglotzThermoComputability
public import Physlib.QuantumMechanics.RelationalTime.EntropicLandauer
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.GreenFunction

/-!
# S-matrix and density matrix: reversible scattering ⟹ Herglotz → Hamilton

This file links the Herglotz-convergence result (`TimeOperator.HerglotzThermoComputability`) to the
**S-matrix** (the unitary scattering / real-time evolution operator) and the **density matrix**
(`MState`), making the reversibility that collapses Herglotz dissipation into Hamilton's
equations visible in both objects.

## The S-matrix side (spectral kernel)

The S-matrix on an `H_C`-eigenmode is the real-time evolution amplitude
`smatrixKernel λ ℏ t = greenKernel λ ℏ t = e^{−iλt/ℏ}` (the Lorentzian propagator). Its modulus
is the dissipative decay:

* `smatrixKernel_norm` — `‖S‖ = e^{Im λ·t/ℏ}`: the S-matrix is sub-unitary exactly when the
  eigenvalue has a negative imaginary part (`H_I > 0`, decay / probability loss).
* `smatrixKernel_unitary_iff` — **`‖S‖ = 1 ⟺ Im λ = 0`**: the S-matrix is *unitary* iff the
  Hamiltonian eigenvalue is real (`H_I = 0`, no dissipation, reversible).

## The density-matrix side (von Neumann entropy)

A unitary S-matrix `S` conjugates the density matrix `ρ ↦ S ◃ ρ` and **preserves von Neumann
entropy** (`smatrix_preserves_vonNeumann = Sᵥₙ_U_conj'`): reversible scattering produces no
entropy. The marginal Landauer cost (`EntropicLandauer.landauer_export`: erasure exports
`≥ ln 2`) is paid only by *irreversible* (erasing) channels; the reversible S-matrix exports
`0`.

## Convergence to Herglotz / Hamilton

The reversible point — unitary S-matrix, entropy-conserving density matrix, `Im λ = 0`,
`S_I = 0`, `D(ρ‖σ) = 0` — is exactly where the Herglotz contact Lagrangian reduces to `L_R`
(Hamilton). `smatrix_reversible_conserves_and_hamilton` packages both faces: a unitary S-matrix
conserves the density matrix's entropy **and** (at the no-information point) the Herglotz
dynamics converges to Hamilton's equations.

## References

* S-matrix / unitary scattering; `MState` density matrices, `Sᵥₙ` von Neumann entropy
  (QuantumInfo); `RelationalTime.EntropicLandauer` (Landauer / unitary entropy balance).
* `TimeOperator.HerglotzThermoComputability`, `NonHermitianComplexAction.GreenFunction` (this development).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped MState
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HerglotzThermoComputability
open Physlib.QuantumMechanics.RelationalTime.Landauer

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.SMatrixDensityHerglotz


/-- **The S-matrix on an `H_C`-eigenmode** = the Lorentzian real-time amplitude
`e^{−iλt/ℏ}` (`greenKernel`). -/
def smatrixKernel (lam : ℂ) (ℏ t : ℝ) : ℂ := greenKernel lam ℏ t

/-- **The S-matrix modulus is the dissipative decay** `‖S‖ = e^{Im λ·t/ℏ}` — sub-unitary when
`Im λ < 0` (probability loss / `H_I > 0`). -/
lemma smatrixKernel_norm (lam : ℂ) (ℏ t : ℝ) :
    ‖smatrixKernel lam ℏ t‖ = Real.exp (lam.im * t / ℏ) :=
  norm_greenKernel lam ℏ t

/-- **The S-matrix is unitary iff the Hamiltonian eigenvalue is real**: `‖S‖ = 1 ⟺ Im λ = 0`
(`H_I = 0`, no dissipation, reversible scattering). -/
lemma smatrixKernel_unitary_iff (lam : ℂ) {ℏ t : ℝ} (hℏ : ℏ ≠ 0) (ht : t ≠ 0) :
    ‖smatrixKernel lam ℏ t‖ = 1 ↔ lam.im = 0 :=
  greenKernel_norm_one_iff hℏ ht lam


variable {d dE : Type*} [Fintype d] [DecidableEq d] [Fintype dE] [DecidableEq dE]

/-- **A unitary S-matrix preserves the density matrix's von Neumann entropy**:
`Sᵥₙ (S ◃ ρ) = Sᵥₙ ρ` — reversible scattering produces no entropy (`Sᵥₙ_U_conj'`). -/
lemma smatrix_preserves_vonNeumann (ρ : MState (d × dE)) (S : 𝐔[d × dE]) :
    Sᵥₙ (S ◃ ρ) = Sᵥₙ ρ :=
  Sᵥₙ_U_conj' ρ S


/-- **Reversible scattering ⟹ entropy-conserving density matrix and Herglotz → Hamilton.** A
unitary S-matrix conserves the density matrix's von Neumann entropy, and at the no-information
point (`ρ = σ`, `D(ρ‖σ) = 0` — the reversible / Landauer-free regime) the Herglotz contact
Lagrangian reduces to `L_R`, recovering Hamilton's equations. Both are faces of the same
reversibility (`Im λ = 0`, `S_I = 0`, unitary S-matrix). -/
lemma smatrix_reversible_conserves_and_hamilton
    (ρ : MState (d × dE)) (S : 𝐔[d × dE])
    (L_R ρcoeff : ℝ → ℝ) (states : ℝ → MState d × MState d) (t : ℝ)
    (h_rev : (states t).1 = (states t).2) :
    Sᵥₙ (S ◃ ρ) = Sᵥₙ ρ
      ∧ (computabilityHerglotzSlice L_R ρcoeff states).effectiveLagrangian t = L_R t :=
  ⟨smatrix_preserves_vonNeumann ρ S,
   computability_reversible_to_hamilton L_R ρcoeff states t h_rev⟩

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.SMatrixDensityHerglotz

end

end
