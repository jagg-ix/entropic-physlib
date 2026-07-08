/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-!
# Canonical variables for a relativistic particle: spin, helicity, Casimir (Acharya–Sudarshan 1960 §2)

`Dirac.FourSpinorDiracHamiltonian` / `Dirac.FoldyWouthuysenExact` formalized Section 3 (the Dirac equation and
its exact Foldy–Wouthuysen reduction). This file formalizes the **matrix-level content of Section 2**
("Canonical Variables for a Relativistic Particle") of R. Acharya, E. C. G. Sudarshan, J. Math. Phys.
**1** (1960) 532 — the spin/rotation algebra, the helicity, and the Casimir, in the spin-`½`
representation `Sᵢ = ½σᵢ`.

## The spin (rotation) algebra and Casimir

The spin operators `Sᵢ = ½σᵢ` satisfy the `so(3)` rotation algebra (Acharya Eqs. 3–5, the quantum form
of the Poisson bracket `{Sᵢ,Sⱼ} = ε_{ijk}Sₖ`):

 `[Sᵢ, Sⱼ] = i ε_{ijk} Sₖ` (`spin_algebra_12/23/31`),

and the spin **Casimir** is the `s = ½` value `s(s+1) = ¾`:

 `S² = S₁²+S₂²+S₃² = ¾·1` (`spin_casimir`).

The spin commutes with the (c-number) momentum (Acharya Eq. 4): `[Sᵢ, c·1] = 0`
(`spin_commutes_scalar`).

## The helicity (Acharya Eq. 6)

The helicity is the projection of spin on the momentum, `h = S·p̂` — the second Casimir `T·R = p·S`
divided by `|T| = |p|`:

 `T·R = p·S = ½ σ·p` (`helicity_eq_spin_momentum`), `h² = ¼·1` (`helicity_sq_unit`),

so the helicity eigenvalues are `±½`. The helicity is a **constant of motion** (Acharya Eq. 6): it
commutes with the positive-energy Schrödinger Hamiltonian `√(p²+m²)·1` (`helicity_commutes_energy`) —
Acharya Eq. 9, `i ∂ψ/∂t = +(p²+m²)^½ ψ`, the positive-energy block of the Foldy–Wouthuysen reduction.

## Scope

What is formalized is the **spin-½ (matrix) content** of Section 2: the spin algebra, the Casimir, the
helicity, and helicity conservation. What is **not** (and cannot be at the finite-matrix level): the
canonical commutators `[qᵢ,pⱼ] = iδ` (Eq. 1) and orbital `L = q×p` (Eq. 2) — the infinite-dimensional
Heisenberg algebra; the full Euclidean-group relation `[Rᵢ,Tⱼ] = iε Tₖ` (Eq. 7) — needs orbital
generators; the two Casimirs `T²`, `T·R` of the *representation* and Wigner's classification of the
inhomogeneous-Lorentz-group irreps (classes I/II/III: finite/zero/imaginary mass, Eq. 8 ff.) — these
are representation theory, not matrix identities. The first Casimir `T² = |p|²` is, at the c-number
momentum level, just `dotR p p`.

## References

* R. Acharya, E. C. G. Sudarshan, J. Math. Phys. **1** (1960) 532, §2. This development:
 `Dirac.PauliEquationSpinOrbit`, `Relativity/PauliMatrices`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Complex PauliMatrix

namespace Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity

open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-! ## §A — the spin operators `Sᵢ = ½σᵢ` and the rotation algebra (Acharya Eqs. 3–5) -/

/-- **The spin-`x` operator** `S₁ = ½σ₁`. -/
def spin1 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ1

/-- **The spin-`y` operator** `S₂ = ½σ₂`. -/
def spin2 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ2

/-- **The spin-`z` operator** `S₃ = ½σ₃`. -/
def spin3 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ3

/-- **The spin algebra** `[S₁, S₂] = i S₃` (the `so(3)` rotation algebra, Acharya Eq. 5). -/
theorem spin_algebra_12 : spin1 * spin2 - spin2 * spin1 = I • spin3 := by
  simp only [spin1, spin2, spin3, smul_mul_smul_comm, ← smul_sub, σ1_σ2_commutator, smul_smul]
  congr 1
  ring

/-- **The spin algebra** `[S₂, S₃] = i S₁`. -/
theorem spin_algebra_23 : spin2 * spin3 - spin3 * spin2 = I • spin1 := by
  simp only [spin1, spin2, spin3, smul_mul_smul_comm, ← smul_sub, σ2_σ3_commutator, smul_smul]
  congr 1
  ring

/-- **The spin algebra** `[S₃, S₁] = i S₂`. -/
theorem spin_algebra_31 : spin3 * spin1 - spin1 * spin3 = I • spin2 := by
  simp only [spin1, spin2, spin3, smul_mul_smul_comm, ← smul_sub, σ3_σ1_commutator, smul_smul]
  congr 1
  ring

/-- **The spin Casimir** `S² = S₁²+S₂²+S₃² = ¾·1` — the `s(s+1)` value for spin `s = ½`
(Acharya, the first Casimir for the spin). -/
theorem spin_casimir : spin1 * spin1 + spin2 * spin2 + spin3 * spin3 = ((3 / 4 : ℂ)) • 1 := by
  simp only [spin1, spin2, spin3, smul_mul_smul_comm, pauliMatrix_mul_self]
  rw [← add_smul, ← add_smul]
  norm_num

/-- **Spin commutes with the (c-number) momentum** `[Sᵢ, c·1] = 0` (Acharya Eq. 4): the spin
variables Poisson-commute with the phase-space (momentum) variables. -/
theorem spin_commutes_scalar (c : ℂ) : spin1 * (c • 1) - (c • 1) * spin1 = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]

/-! ## §B — the helicity (Acharya Eq. 6) -/

/-- **The spin–momentum projection** `S·p = ½ σ·p` — the second Casimir `T·R` (Acharya Eq. 8); the
helicity is `h = T·R/|T| = S·p/|p|`. -/
def helicityProj (p : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • sigmaDot p

/-- **`T·R = p·S`** `= ½ σ·p`: the spin–momentum projection is the sum `Σ pᵢ Sᵢ` (Acharya Eqs. 6, 8). -/
theorem helicity_eq_spin_momentum (p : Fin 3 → ℝ) :
    helicityProj p = (p 0 : ℂ) • spin1 + (p 1 : ℂ) • spin2 + (p 2 : ℂ) • spin3 := by
  simp only [helicityProj, sigmaDot, spin1, spin2, spin3, smul_add]
  module

/-- **The helicity squares to `¼·|p|²·1`** — for a unit momentum direction the helicity `h = S·p̂`
satisfies `h² = ¼·1`, so its eigenvalues are `±½`. -/
theorem helicityProj_sq (p : Fin 3 → ℝ) :
    helicityProj p * helicityProj p = ((1 / 4 * dotR p p : ℝ) : ℂ) • 1 := by
  rw [helicityProj, smul_mul_smul_comm, sigmaDot_sq, smul_smul]
  congr 1
  push_cast
  ring

/-- **The helicity has eigenvalues `±½`**: for a unit momentum `|p̂| = 1`, `h² = ¼·1`. -/
theorem helicity_sq_unit (p : Fin 3 → ℝ) (hp : dotR p p = 1) :
    helicityProj p * helicityProj p = ((1 / 4 : ℂ)) • 1 := by
  rw [helicityProj_sq, hp]
  norm_num

/-- **The helicity is a constant of motion** (Acharya Eq. 6): it commutes with the positive-energy
Schrödinger Hamiltonian `√(p²+m²)·1` (a scalar on the two-spinor) — Acharya Eq. 9
`i ∂ψ/∂t = +(p²+m²)^½ ψ`, the positive-energy block of the Foldy–Wouthuysen reduction. -/
theorem helicity_commutes_energy (p : Fin 3 → ℝ) (E : ℝ) :
    helicityProj p * ((E : ℂ) • 1) - ((E : ℂ) • 1) * helicityProj p = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]

/-! ## §C — the canonical-variables structure, bundled -/

/-- **Acharya–Sudarshan §2 (matrix content), bundled.** In the spin-`½` representation `Sᵢ = ½σᵢ`:

* the spin algebra `[S₁,S₂] = i S₃` (the `so(3)` rotation algebra);
* the spin Casimir `S² = ¾·1` (`s(s+1)` for `s = ½`);
* the helicity squares to `¼|p|²·1` (eigenvalues `±½` for unit `p`);
* the helicity commutes with the positive-energy Hamiltonian `E·1` (constant of motion). -/
theorem acharya_canonical_spin_summary (p : Fin 3 → ℝ) (E : ℝ) :
    spin1 * spin2 - spin2 * spin1 = I • spin3
      ∧ spin1 * spin1 + spin2 * spin2 + spin3 * spin3 = ((3 / 4 : ℂ)) • 1
      ∧ helicityProj p * helicityProj p = ((1 / 4 * dotR p p : ℝ) : ℂ) • 1
      ∧ helicityProj p * ((E : ℂ) • 1) - ((E : ℂ) • 1) * helicityProj p = 0 :=
  ⟨spin_algebra_12, spin_casimir, helicityProj_sq p, helicity_commutes_energy p E⟩

end Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity

end
