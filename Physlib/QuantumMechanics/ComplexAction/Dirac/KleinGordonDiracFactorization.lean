/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Klein–Gordon equation and its Dirac factorisation (confined photon)

This file formalizes the **Klein–Gordon** mass-shell relation and the **Dirac** factorisation
that produces it, for the confined photon of `Dirac.ConfinedPhotonDiracDispersion` (Saito 2024).

## Klein–Gordon

The Klein–Gordon relation is the mass-shell / dispersion condition

  `E² = Δ² + (v₀ p)²`   (`kleinGordonRelation`),

`Δ = m*·v₀²` the mass gap. The confined-photon dispersion `E = photonDispersion` satisfies it
(`photonDispersion_kleinGordon`), and so do both Dirac branches `±E`.

## Dirac (factorising Klein–Gordon)

To get a *first-order* equation with a probabilistic interpretation one factorises `E²` into a
matrix square root — the 2×2 Dirac Hamiltonian (Saito's 2D Dirac for the photon)

  `H = Δ σ₃ + (v₀p) σ₁ = !![Δ, v₀p; v₀p, −Δ]`.

It satisfies the Clifford-algebra factorisation

  `H² = (Δ² + (v₀p)²)·I`   (`diracHamiltonian_sq`),

so the Dirac operator is a square root of Klein–Gordon: its energy² is the Klein–Gordon `E²`
(`diracHamiltonian_sq_eq_dispersion`). With `tr H = 0` and `det H = −(Δ²+(v₀p)²)` the
characteristic polynomial is `λ² − (Δ²+(v₀p)²)` (`diracHamiltonian_charpoly`), so

  **`λ` is a Dirac eigenvalue ⟺ `λ² = Δ² + (v₀p)²` (the Klein–Gordon relation)**
  (`diracHamiltonian_eigenvalue_iff_kleinGordon`),

and the two eigenvalues are exactly the photon Dirac branches `±E`
(`diracHamiltonian_eigenvalue_eq_photonBranch`). `tr H = 0` is the particle–antiparticle
symmetry (the two branches sum to zero).

## References

* O. Klein, W. Gordon (1926); P. A. M. Dirac (1928); S. Saito, Heliyon 10 (2024) e28367
  (2D Dirac for the confined photon).
* `Dirac.ConfinedPhotonDiracDispersion` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

/-! ## §A — the Klein–Gordon relation -/

/-- **The Klein–Gordon mass-shell relation** `E² = Δ² + (v₀p)²` (gap `Δ`). -/
def kleinGordonRelation (Δ v₀ p E : ℝ) : Prop := E ^ 2 = Δ ^ 2 + (v₀ * p) ^ 2

/-- **The confined-photon dispersion satisfies Klein–Gordon** (`photonDispersion_sq`). -/
theorem photonDispersion_kleinGordon (Δ v₀ p : ℝ) :
    kleinGordonRelation Δ v₀ p (photonDispersion Δ v₀ p) :=
  photonDispersion_sq Δ v₀ p

/-! ## §B — the Dirac Hamiltonian and the factorisation `H² = (Δ²+(v₀p)²)·I` -/

/-- **The 2D Dirac Hamiltonian** `H = Δ σ₃ + (v₀p) σ₁ = !![Δ, v₀p; v₀p, −Δ]` (Saito), with
`vp = v₀p`. -/
def diracHamiltonian (Δ vp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Δ, vp; vp, -Δ]

/-- **The Clifford factorisation** `H² = (Δ² + vp²)·I`: the Dirac operator squares to the
Klein–Gordon operator. -/
theorem diracHamiltonian_sq (Δ vp : ℝ) :
    diracHamiltonian Δ vp * diracHamiltonian Δ vp
      = (Δ ^ 2 + vp ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold diracHamiltonian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- **`tr H = 0`** — the particle–antiparticle symmetry (the two eigenvalues sum to zero). -/
theorem diracHamiltonian_trace (Δ vp : ℝ) : (diracHamiltonian Δ vp).trace = 0 := by
  unfold diracHamiltonian
  simp [Matrix.trace_fin_two]

/-- **`det H = −(Δ² + vp²)`**. -/
theorem diracHamiltonian_det (Δ vp : ℝ) :
    (diracHamiltonian Δ vp).det = -(Δ ^ 2 + vp ^ 2) := by
  unfold diracHamiltonian
  rw [Matrix.det_fin_two_of]
  ring

/-! ## §C — Klein–Gordon ⟺ Dirac: eigenvalues are the photon branches -/

/-- **The Dirac energy² is the Klein–Gordon `E²`**: `H² = (photonDispersion)²·I`. -/
theorem diracHamiltonian_sq_eq_dispersion (Δ v₀ p : ℝ) :
    diracHamiltonian Δ (v₀ * p) * diracHamiltonian Δ (v₀ * p)
      = (photonDispersion Δ v₀ p) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [diracHamiltonian_sq, photonDispersion_sq]

/-- **The characteristic polynomial** `det(λI − H) = λ² − (Δ²+vp²)` (using `tr H = 0`,
`det H = −(Δ²+vp²)`). -/
theorem diracHamiltonian_charpoly (Δ vp lam : ℝ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ vp).det
      = lam ^ 2 - (Δ ^ 2 + vp ^ 2) := by
  unfold diracHamiltonian
  rw [Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **`λ` is a Dirac eigenvalue ⟺ it satisfies the Klein–Gordon relation** `λ² = Δ² + vp²`:
the Dirac eigenvalue condition is exactly the Klein–Gordon mass shell. -/
theorem diracHamiltonian_eigenvalue_iff_kleinGordon (Δ v₀ p lam : ℝ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diracHamiltonian Δ (v₀ * p)).det = 0
      ↔ kleinGordonRelation Δ v₀ p lam := by
  rw [diracHamiltonian_charpoly]
  unfold kleinGordonRelation
  constructor <;> intro h <;> linarith

/-- **The Dirac eigenvalues are the photon Dirac branches** `±E`: the upper branch `+E` is an
eigenvalue. -/
theorem diracHamiltonian_eigenvalue_photonBranch_pos (Δ v₀ p : ℝ) :
    ((photonDiracBranch Δ v₀ p true) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - diracHamiltonian Δ (v₀ * p)).det = 0 := by
  rw [diracHamiltonian_eigenvalue_iff_kleinGordon]
  show photonDiracBranch Δ v₀ p true ^ 2 = Δ ^ 2 + (v₀ * p) ^ 2
  unfold photonDiracBranch
  rw [if_pos rfl, photonDispersion_sq]

end Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

end
