/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Operators.Unitary
public import QuantumInfo.ForMathlib.HermitianMat.Inner
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Entropic time vs modular (thermal) time: complementarity

This file records that the entropy-producing ("entropic") direction of an open
quantum system and the Connes-Rovelli modular/thermal-time flow are
**complementary** intrinsic times, distinct from each other and from the
standard unitary parameter time.

The companion `Physlib.QuantumMechanics.RelationalTime.ModularEntropicLadder`
provides the *static bridge* between the two: at a Gibbs state the modular
Hamiltonian equals the entropic-time operator up to a free-energy offset
(`modularHamiltonianMat_eq_entropicTimeOperator_add_offset`), equivalently
`⟨K⟩ = S_vN`. Here we record the two *dynamical* facts that make the clocks
complementary rather than identical:

* **§A (reversibility of thermal time).** The modular/thermal flow is unitary
  conjugation `ρ ↦ U ◃ ρ` (`U = e^{-iKs}`), and von Neumann entropy depends only
  on the spectrum, which unitary conjugation preserves. Hence the modular clock
  is **isospectral / entropy-preserving** (`Sᵥₙ_U_conj`): `dS/ds = 0`.

* **§B (orthogonality).** The modular-flow generator on operators is the
  commutator `adK X = K * X - X * K`. For Hermitian `K` it is anti-self-adjoint
  for the Hilbert-Schmidt inner product `⟪A, B⟫ = trace (Aᴴ * B)`, so its image
  is HS-orthogonal to the commutant of `K`
  (`modular_direction_orthogonal_to_commutant`). The commutant of `K = -ln ρ_ss`
  contains `ρ_ss`, its functions (populations), and the entropy gradient -- the
  directions along which a dissipative (entropic) flow produces entropy. So the
  entropy-producing direction is orthogonal to the modular flow.

Reading: thermal/modular time is the reversible, isospectral symmetry flow;
entropic time is the irreversible, entropy-producing flow. They meet only at the
static `⟨K⟩ = S_vN` bridge and coincide at equilibrium. Neither is the unitary
parameter time of standard quantum mechanics.

## References

* A. Connes, C. Rovelli, *Von Neumann algebra automorphisms and time-
  thermodynamics relation in generally covariant quantum theories*,
  Class. Quantum Grav. **11** (1994) 2899.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.Complementarity

open scoped MState Matrix

/-! ## §A -- Modular/thermal time is entropy-preserving (isospectral) -/

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §0 -- Modular weights and Heisenberg-picture observables -/

/-- **Modular weight**: `η_K(ρ) := ⟪ρ, K⟫_ℝ = Re Tr(ρ·K)`. The expectation
value of a Hermitian observable `K` in the possibly non-normalised Hermitian
state `ρ`. -/
noncomputable def modularWeight (ρ K : HermitianMat d ℂ) : ℝ :=
  inner ℝ ρ K

/-- **Constant-shift invariance of modular weight**: shifting the observable
`K` by `c·1` adds `c·Tr(ρ)` to the modular weight. -/
theorem modularWeight_add_smul_one
    (ρ K : HermitianMat d ℂ) (c : ℝ) :
    modularWeight ρ (K + c • (1 : HermitianMat d ℂ)) = modularWeight ρ K + c * ρ.trace := by
  unfold modularWeight
  rw [HermitianMat.inner_add_right, HermitianMat.inner_smul_right, HermitianMat.inner_one]

/-- For a normalised state (`Tr ρ = 1`), shifting by `c·1` shifts the modular
weight by exactly `c`. -/
theorem modularWeight_add_smul_one_of_unit_trace
    (ρ K : HermitianMat d ℂ) (c : ℝ) (h_tr : ρ.trace = 1) :
    modularWeight ρ (K + c • (1 : HermitianMat d ℂ)) = modularWeight ρ K + c := by
  rw [modularWeight_add_smul_one, h_tr, mul_one]

/-- **Relative modular weight**: `Δ⟨K⟩ := η_K(ρ) − η_K(ρ₀)`. -/
noncomputable def relativeModularWeight
    (ρ ρ₀ K : HermitianMat d ℂ) : ℝ :=
  modularWeight ρ K - modularWeight ρ₀ K

/-- Relative modular weight against itself vanishes. -/
@[simp]
theorem relativeModularWeight_refl
    (ρ K : HermitianMat d ℂ) :
    relativeModularWeight ρ ρ K = 0 := by
  unfold relativeModularWeight; ring

/-- Swapping reference and target flips the sign. -/
theorem relativeModularWeight_swap
    (ρ ρ₀ K : HermitianMat d ℂ) :
    relativeModularWeight ρ₀ ρ K = -relativeModularWeight ρ ρ₀ K := by
  unfold relativeModularWeight; ring

/-- Relative modular weight is additive in the generator:
`Δ⟨K₁ + K₂⟩ = Δ⟨K₁⟩ + Δ⟨K₂⟩`. -/
theorem relativeModularWeight_add_generator
    (ρ ρ₀ K₁ K₂ : HermitianMat d ℂ) :
    relativeModularWeight ρ ρ₀ (K₁ + K₂)
      = relativeModularWeight ρ ρ₀ K₁ + relativeModularWeight ρ ρ₀ K₂ := by
  unfold relativeModularWeight modularWeight
  rw [HermitianMat.inner_add_right, HermitianMat.inner_add_right]
  ring

/-- **Constant-shift invariance of the relative form**:
`Δ⟨K + c·1⟩ = Δ⟨K⟩ + c(Tr ρ − Tr ρ₀)`. -/
theorem relativeModularWeight_add_smul_one
    (ρ ρ₀ K : HermitianMat d ℂ) (c : ℝ) :
    relativeModularWeight ρ ρ₀ (K + c • (1 : HermitianMat d ℂ))
      = relativeModularWeight ρ ρ₀ K
        + c * (ρ.trace - ρ₀.trace) := by
  unfold relativeModularWeight
  rw [modularWeight_add_smul_one, modularWeight_add_smul_one]
  ring

/-- **Constant-shift invariance for unit-trace states**. -/
theorem relativeModularWeight_add_smul_one_of_unit_trace
    (ρ ρ₀ K : HermitianMat d ℂ) (c : ℝ)
    (h_ρ : ρ.trace = 1) (h_ρ₀ : ρ₀.trace = 1) :
    relativeModularWeight ρ ρ₀ (K + c • (1 : HermitianMat d ℂ))
      = relativeModularWeight ρ ρ₀ K := by
  rw [relativeModularWeight_add_smul_one, h_ρ, h_ρ₀, sub_self, mul_zero, add_zero]

/-- **Hermitian square**: for any Hermitian matrix `A`, `A * A` is Hermitian. -/
noncomputable def HermitianMatSq (A : HermitianMat d ℂ) : HermitianMat d ℂ :=
  ⟨A.mat * A.mat, by
    show Matrix.conjTranspose (A.mat * A.mat) = A.mat * A.mat
    rw [Matrix.conjTranspose_mul, A.H]⟩

@[simp]
theorem HermitianMatSq_mat (A : HermitianMat d ℂ) :
    (HermitianMatSq A).mat = A.mat * A.mat := rfl

/-- **Heisenberg-picture expectation value**:
`⟨A⟩_ρ := ⟪ρ, A⟫_ℝ = Re Tr(ρ·A)`. -/
noncomputable abbrev expectation (ρ A : HermitianMat d ℂ) : ℝ :=
  modularWeight ρ A

/-- **Variance** of a Hermitian observable `A` in state `ρ`. -/
noncomputable def variance (ρ A : HermitianMat d ℂ) : ℝ :=
  expectation ρ (HermitianMatSq A) - (expectation ρ A) ^ 2

/-- **Uncertainty** of a Hermitian observable `A` in state `ρ`. -/
noncomputable def uncertainty (ρ A : HermitianMat d ℂ) : ℝ :=
  Real.sqrt (variance ρ A)

/-- The uncertainty is non-negative. -/
theorem uncertainty_nonneg (ρ A : HermitianMat d ℂ) :
    0 ≤ uncertainty ρ A := Real.sqrt_nonneg _

/-- **Real part of an operator**: `Re(A) := (A + Aᴴ)/2`. -/
noncomputable def realPartOpMatrix (A : Matrix d d ℂ) : Matrix d d ℂ :=
  (1 / 2 : ℂ) • (A + Matrix.conjTranspose A)

/-- **Imaginary part of an operator**: `Im(A) := (A − Aᴴ)/(2i)`. -/
noncomputable def imPartOpMatrix (A : Matrix d d ℂ) : Matrix d d ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (A - Matrix.conjTranspose A)

/-- **Operator decomposition**: `A = Re(A) + i · Im(A)` for any matrix `A`. -/
theorem operator_decomposition_matrix (A : Matrix d d ℂ) :
    A = realPartOpMatrix A + Complex.I • imPartOpMatrix A := by
  unfold realPartOpMatrix imPartOpMatrix
  rw [smul_smul,
      show Complex.I * (1 / (2 * Complex.I)) = (1 / 2 : ℂ) by field_simp,
      ← smul_add,
      show (A + Matrix.conjTranspose A) + (A - Matrix.conjTranspose A)
            = (2 : ℂ) • A by
        rw [show ((2 : ℂ) • A) = A + A from by rw [two_smul]]
        abel,
      smul_smul,
      show ((1 / 2 : ℂ) * 2) = 1 by norm_num,
      one_smul]

/-- **Real part is Hermitian**: `(Re(A))ᴴ = Re(A)`. -/
theorem realPartOpMatrix_isHermitian (A : Matrix d d ℂ) :
    (realPartOpMatrix A).IsHermitian := by
  unfold realPartOpMatrix
  show Matrix.conjTranspose ((1 / 2 : ℂ) • (A + Matrix.conjTranspose A))
      = (1 / 2 : ℂ) • (A + Matrix.conjTranspose A)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
  rw [show (star ((1 : ℂ) / 2)) = ((1 : ℂ) / 2) by
    simp]
  rw [add_comm]

/-- **Modular/thermal time preserves von Neumann entropy.** Unitary conjugation
(the modular flow `U = e^{-iKs}`) leaves `Sᵥₙ` invariant, because `Sᵥₙ` depends
only on the spectrum and `MState.U_conj` preserves the spectrum. Formal content
of `dS/ds = 0`: thermal time is the reversible, isospectral clock. -/
theorem Sᵥₙ_U_conj (ρ : MState d) (U : 𝐔[d]) :
    Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ := by
  simp only [Sᵥₙ, MState.U_conj_spectrum_eq]

/-! ## §B -- The entropic (dissipative) direction is orthogonal to the modular one

`⟪A, B⟫ = trace (Aᴴ * B)` is the Hilbert-Schmidt inner product; `K * X - X * K`
is the modular-flow generator `adK X`. -/

variable {n : Type*} [Fintype n]

/-- **Adjoint-shift identity for `adK`** (HS anti-self-adjointness of the modular
generator). For Hermitian `K`,
`trace ((K*X - X*K)ᴴ * D) = trace (Xᴴ * (K*D - D*K))`. -/
theorem hs_adK_shift (K X D : Matrix n n ℂ) (hK : Kᴴ = K) :
    Matrix.trace ((K * X - X * K)ᴴ * D) = Matrix.trace (Xᴴ * (K * D - D * K)) := by
  have hKX : (K * X - X * K)ᴴ = Xᴴ * K - K * Xᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hK]
  rw [hKX, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · rw [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc K Xᴴ D, Matrix.trace_mul_comm K (Xᴴ * D),
        Matrix.mul_assoc Xᴴ D K]

/-- **Complementarity / orthogonality.** When `D` commutes with the modular
Hamiltonian `K` (so `D` is a function of `ρ_ss`: a population operator, `ρ_ss`
itself, or the entropy gradient), the modular-flow direction `K*X - X*K` is
HS-orthogonal to `D`: `trace ((K*X - X*K)ᴴ * D) = 0`. The entropy-producing
(dissipative) direction is orthogonal to the modular (thermal-time) direction. -/
theorem modular_direction_orthogonal_to_commutant
    (K X D : Matrix n n ℂ) (hK : Kᴴ = K) (hKD : K * D = D * K) :
    Matrix.trace ((K * X - X * K)ᴴ * D) = 0 := by
  rw [hs_adK_shift K X D hK]
  have h0 : K * D - D * K = 0 := by rw [hKD]; exact sub_self _
  rw [h0, Matrix.mul_zero, Matrix.trace_zero]

end Physlib.QuantumMechanics.RelationalTime.Complementarity

end
