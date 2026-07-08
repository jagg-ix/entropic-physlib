/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Ehrenfest
public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-!
# The Pauli equation: the spin–orbit and Darwin terms (Foldy–Wouthuysen / Acharya–Sudarshan 1960)

`Dirac.FourSpinorDiracHamiltonian` built the genuine four-spinor Dirac Hamiltonian `H = α·p + βm` and its
free Foldy–Wouthuysen square `H² = (E·β)² = (p²+m²)·1` (Acharya–Sudarshan 1960, Eqs. 12–15 — the
**free** reduction). This file formalizes the **matrix heart** of the *interacting* reduction — the
**Pauli equation** with its **spin–orbit** and **Darwin** terms — using physlib's canonical Pauli
matrices `σ1,σ2,σ3` and the Heisenberg-equation formalization `heisenbergGen`.

## The Pauli vector identity (the source of spin–orbit)

For 3-vectors `a, b`, with `σ·a = a₁σ₁ + a₂σ₂ + a₃σ₃`,

 `(σ·a)(σ·b) = (a·b)·1 + i σ·(a×b)` (`pauli_vector_identity`).

Its symmetric part gives the kinetic term `(σ·a)² = |a|²·1` (`sigmaDot_sq`); its antisymmetric part
gives the **spin commutator** `[σ·a, σ·b] = 2i σ·(a×b)` (`sigmaDot_commutator`). With `a = ∇V`,
`b = p` the antisymmetric part is `2i σ·(∇V×p)` — the operator structure of the **spin–orbit
coupling** `(1/4m²c²) σ·(∇V×p)` (`spinOrbit_from_commutator`).

## The Heisenberg spin precession

Driving the spin `σ·b` by `σ·a` through the Heisenberg equation (`heisenbergGen ℏ H O = (i/ℏ)[H,O]`):

 `heisenbergGen ℏ (σ·a) (σ·b) = (−2/ℏ)·σ·(a×b)` (`heisenberg_spin_precession`),

the precession of the spin about `a` — Larmor/Thomas precession, the dynamics behind spin–orbit.

## The Pauli Hamiltonian with spin–orbit and Darwin

`pauliHamiltonianFW` assembles the full Foldy–Wouthuysen Hamiltonian to order `1/m²` (natural units
`c = ℏ = 1`):

 `H_P = (p²/2m + V − p⁴/8m³ + (∇²V)/8m²)·1 + (1/4m²) σ·(∇V×p)`,

i.e. non-relativistic kinetic + potential + relativistic mass correction + **Darwin** `(∇²V)/8m²`
(scalar) + **spin–orbit** `(1/4m²) σ·(∇V×p)`. It is self-adjoint (`pauliHamiltonianFW_isSelfAdjoint`).

## Scope

The Pauli vector identity, the spin commutator, the spin precession, the spin–orbit operator
structure, and the self-adjointness of the assembled Hamiltonian are proved exactly. What is **not**
derived: that the term *coefficients* `1/4m²`, `1/8m²`, `−1/8m³` follow from the Dirac equation — that
is the Foldy–Wouthuysen perturbative expansion (L. L. Foldy, S. A. Wouthuysen 1950; cited by
Acharya–Sudarshan 1960, which itself gives only the *free* reduction `β√(p²+m²)`), a nested-commutator
/ matrix-exponential calculation not formalized here. Here `p, ∇V` are c-number vectors (momentum
space), not the operators `−i∇`, so the magnetic `[πᵢ,πⱼ]` term is represented by its c-number
cross-product structure.

## References

* L. L. Foldy, S. A. Wouthuysen, Phys. Rev. **78** (1950) 29; R. Acharya, E. C. G. Sudarshan,
 J. Math. Phys. **1** (1960) 532. This development: `Relativity/PauliMatrices`,
 `PeriodicQHermitian.Ehrenfest` (Heisenberg equation), `Dirac.FourSpinorDiracHamiltonian`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Complex PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-! ## §A — the spin vector `σ·a`, the dot and cross products -/

/-- **The spin projection** `σ·a = a₁σ₁ + a₂σ₂ + a₃σ₃` for a 3-vector `a`. -/
def sigmaDot (a : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a 0 : ℂ) • σ1 + (a 1 : ℂ) • σ2 + (a 2 : ℂ) • σ3

/-- **The Euclidean dot product** `a·b = a₁b₁ + a₂b₂ + a₃b₃`. -/
def dotR (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- **The cross product** `(a×b) = (a₂b₃−a₃b₂, a₃b₁−a₁b₃, a₁b₂−a₂b₁)`. -/
def crossR (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-! ## §B — the Pauli vector identity `(σ·a)(σ·b) = (a·b)·1 + iσ·(a×b)` -/

/-- **The Pauli vector identity** `(σ·a)(σ·b) = (a·b)·1 + i σ·(a×b)` — the fundamental `SU(2)` matrix
identity that, with `a = ∇V`, `b = p`, generates the spin–orbit coupling. -/
theorem pauli_vector_identity (a b : Fin 3 → ℝ) :
    sigmaDot a * sigmaDot b = ((dotR a b : ℝ) : ℂ) • 1 + I • sigmaDot (crossR a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaDot, dotR, crossR, pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- **The cross product is alternating**: `a×a = 0`. -/
theorem crossR_self (a : Fin 3 → ℝ) : crossR a a = 0 := by
  funext k; fin_cases k <;> simp [crossR] <;> ring

/-- **`σ·a` is linear in `a` for negation**: `σ·(−a) = −(σ·a)`. -/
theorem sigmaDot_neg (a : Fin 3 → ℝ) : sigmaDot (-a) = -sigmaDot a := by
  simp only [sigmaDot, Pi.neg_apply, Complex.ofReal_neg, neg_smul]
  abel

/-- **The cross product is antisymmetric**: `b×a = −(a×b)`. -/
theorem crossR_comm (a b : Fin 3 → ℝ) : crossR b a = -crossR a b := by
  funext k; fin_cases k <;> simp [crossR] <;> ring

/-- **The dot product is symmetric**: `b·a = a·b`. -/
theorem dotR_comm (a b : Fin 3 → ℝ) : dotR b a = dotR a b := by
  simp only [dotR]; ring

/-! ## §C — kinetic term and the spin commutator (the source of spin–orbit) -/

/-- **The kinetic term** `(σ·a)² = |a|²·1` — the symmetric part of the Pauli identity (`a×a = 0`),
the `(σ·p)² = p²` that gives the non-relativistic kinetic energy `p²/2m`. -/
theorem sigmaDot_sq (a : Fin 3 → ℝ) :
    sigmaDot a * sigmaDot a = ((dotR a a : ℝ) : ℂ) • 1 := by
  rw [pauli_vector_identity, crossR_self]
  simp [sigmaDot]

/-- **The spin commutator** `[σ·a, σ·b] = 2i σ·(a×b)` — the antisymmetric part of the Pauli identity.
With `a = ∇V`, `b = p` this is `2i σ·(∇V×p)`, the spin–orbit operator structure. -/
theorem sigmaDot_commutator (a b : Fin 3 → ℝ) :
    sigmaDot a * sigmaDot b - sigmaDot b * sigmaDot a = (2 * I) • sigmaDot (crossR a b) := by
  rw [pauli_vector_identity a b, pauli_vector_identity b a, crossR_comm, dotR_comm, sigmaDot_neg]
  module

/-- **The spin–orbit operator is the commutator of `σ·∇V` and `σ·p`.** The spin–orbit structure
`σ·(∇V×p)` is `(1/2i)·[σ·∇V, σ·p]` — it arises from the Foldy–Wouthuysen cross term `(σ·∇V)(σ·p)`. -/
theorem spinOrbit_from_commutator (gradV p : Fin 3 → ℝ) :
    commutator (sigmaDot gradV) (sigmaDot p) = (2 * I) • sigmaDot (crossR gradV p) :=
  sigmaDot_commutator gradV p

/-! ## §D — the Heisenberg spin precession -/

/-- **The Heisenberg spin precession** `dO/dt = (i/ℏ)[σ·a, σ·b] = (−2/ℏ)·σ·(a×b)`: driving the spin
`σ·b` by the field `σ·a` through the Heisenberg equation (`heisenbergGen`) precesses it about `a` —
Larmor/Thomas precession, the dynamics underlying spin–orbit coupling. -/
theorem heisenberg_spin_precession (ℏ : ℂ) (a b : Fin 3 → ℝ) :
    heisenbergGen ℏ (sigmaDot a) (sigmaDot b) = ((-2 / ℏ : ℂ)) • sigmaDot (crossR a b) := by
  rw [heisenbergGen, spinOrbit_from_commutator, smul_smul]
  congr 1
  rw [show I / ℏ * (2 * I) = 2 * (I * I) / ℏ by ring, Complex.I_mul_I]
  ring

/-! ## §E — the Pauli Hamiltonian with spin–orbit and Darwin terms -/

/-- **The self-adjointness of `σ·a`** (`a` real): `(σ·a)ᴴ = σ·a` — the Pauli Hamiltonian's spin terms
are Hermitian observables. -/
theorem sigmaDot_isSelfAdjoint (a : Fin 3 → ℝ) : (sigmaDot a)ᴴ = sigmaDot a := by
  simp only [sigmaDot, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, pauliMatrix_selfAdjoint,
    RCLike.star_def, Complex.conj_ofReal]

/-- **The Foldy–Wouthuysen Pauli Hamiltonian to order `1/m²`** (natural units `c = ℏ = 1`):

  `H_P = (p²/2m + V − p⁴/8m³ + (∇²V)/8m²)·1 + (1/4m²)·σ·(∇V×p)`,

the non-relativistic kinetic energy + potential `V` + relativistic mass correction `−p⁴/8m³` +
**Darwin** term `(∇²V)/8m²` (scalar) + **spin–orbit** coupling `(1/4m²)·σ·(∇V×p)`. The kinetic,
potential, relativistic-correction values and the Laplacian `∇²V` are supplied as the parameters
`kinetic`, `potential`, `relCorr`, `lapV`; the vectors `gradV = ∇V` and `p` give the spin–orbit. -/
def pauliHamiltonianFW (m kinetic potential relCorr lapV : ℝ) (gradV p : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((kinetic + potential + relCorr + lapV / (8 * m ^ 2) : ℝ) : ℂ) • 1
    + ((1 / (4 * m ^ 2) : ℝ) : ℂ) • sigmaDot (crossR gradV p)

/-- **The spin–orbit term of the Pauli Hamiltonian** is `(1/4m²)·σ·(∇V×p)` — extracted from the
assembled `pauliHamiltonianFW` by removing the scalar (identity) part. -/
theorem pauliHamiltonianFW_spinOrbit (m kinetic potential relCorr lapV : ℝ) (gradV p : Fin 3 → ℝ) :
    pauliHamiltonianFW m kinetic potential relCorr lapV gradV p
        - ((kinetic + potential + relCorr + lapV / (8 * m ^ 2) : ℝ) : ℂ) • 1
      = ((1 / (4 * m ^ 2) : ℝ) : ℂ) • sigmaDot (crossR gradV p) := by
  rw [pauliHamiltonianFW]; abel

/-- **The Pauli Hamiltonian is self-adjoint** (`H_Pᴴ = H_P`): a genuine Hermitian observable. The
scalar part is real; the spin–orbit part is `σ·(real vector)`, Hermitian by `sigmaDot_isSelfAdjoint`. -/
theorem pauliHamiltonianFW_isSelfAdjoint (m kinetic potential relCorr lapV : ℝ)
    (gradV p : Fin 3 → ℝ) :
    (pauliHamiltonianFW m kinetic potential relCorr lapV gradV p)ᴴ
      = pauliHamiltonianFW m kinetic potential relCorr lapV gradV p := by
  simp only [pauliHamiltonianFW, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, sigmaDot_isSelfAdjoint, RCLike.star_def, Complex.conj_ofReal]

end Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

end
