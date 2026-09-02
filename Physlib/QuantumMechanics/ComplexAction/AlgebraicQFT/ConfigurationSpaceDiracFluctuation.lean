/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Yang–Mills–Dirac from a twisted fluctuation on configuration space

Formalizes the exact algebraic skeleton of Aastrup–Grimstrup, *A Yang-Mills-Dirac
Quantum Field Theory Emerging From a Dirac Operator on a Configuration Space*,
arXiv:2501.00005: a Dirac operator on the configuration space of `SU(2)` connections,
whose **twisted inner fluctuation** (conjugation of the Chern–Simons unitary by the
grading `γ`) squares to a Yang–Mills Hamiltonian plus a fermionic sector satisfying
nonlocal canonical anticommutation relations.

## §A — the Clifford algebra of the configuration space (paper §3)

The paper's `(ext, int)` pair on the fermionic Fock space `Λ*Ω¹(M, S ⊕ S)` is exactly
a CAR field: `int = B`, `ext = star ∘ B` for `B` with `Bogoliubov.IsCAR B`. On that
carrier we build the two Clifford multiplications `c(ψ) = ext(ψ) + int(ψ)` and
`c̄(ψ) = ext(ψ) − int(ψ)` and prove the paper's relations *exactly*:

* `cliffordMul_anticomm` / `cliffordMulBar_anticomm` — `{c(ψ₁), c(ψ₂)} =
  (⟨ψ₂,ψ₁⟩ + ⟨ψ₁,ψ₂⟩)·1` and `{c̄(ψ₁), c̄(ψ₂)} = −(⟨ψ₂,ψ₁⟩ + ⟨ψ₁,ψ₂⟩)·1` (for the
  paper's real metric `⟨·,·⟩_A` this is `±2⟨ψ₁,ψ₂⟩·1`; the paper's `δᵢⱼ` convention
  absorbs the normalization).
* `cliffordMul_mulBar_anticomm` — `{c(ψ₁), c̄(ψ₂)} = (⟨ψ₁,ψ₂⟩ − ⟨ψ₂,ψ₁⟩)·1`, hence
  `= 0` whenever the inner product is symmetric (`cliffordMul_mulBar_anticomm_real`) —
  the paper's `{c, c̄} = 0`.
* `cliffordMul_star` / `cliffordMulBar_star` — `c(ψ)* = c(ψ)`, `c̄(ψ)* = −c̄(ψ)`.
* **the twist (paper Eq. 2)**: `int` is antilinear, so multiplying a basis vector by
  the complex `i` interchanges the two Clifford multiplications:
  `c(iψ) = i·c̄(ψ)` (`cliffordMul_twist`) and `c̄(iψ) = i·c(ψ)` (`cliffordMulBar_twist`).
* **dimension doubling**: `{c(iψ₁), c(iψ₂)} = {c(ψ₁), c(ψ₂)}` (`doubled_anticomm`) while
  `{c(ψ₁), c(iψ₂)} = 0` on a symmetric-inner-product family (`doubled_mixed_anticomm`)
  — the doubled Clifford algebra inside the operators on the exterior algebra.

## §B — the twisted inner fluctuation (paper §4, Eqs 4–6)

Block `2×2` matrices over a noncommutative ring: `D = diag(D₁, D₂)`, the grading
`γ = offdiag(1,1)` with `γ² = 1` (`gammaSwap_mul_self`), and
`γ·diag(P,Q)·γ = diag(Q,P)` (`gammaSwap_conj`). The **twisted fluctuation is exact
matrix algebra** (`twistedFluctuation_eq`): for any unitary-like pair `u = diag(a,b)`,

`D + γ·u[D, u⁻¹]·γ⁻¹ = diag(D₁ + b[D₂,b⁻¹]·, D₂ + a[D₁,a⁻¹])` —

the `γ`-twist moves the `D₂`-fluctuation into the `D₁` block and vice versa; that
interchange is the entire mechanism. With the Chern–Simons input
`b[D₂,b⁻¹] = i[D₂, CS]` (the paper's `u = diag(e^{iCS}, e^{−iCS})`, taken as a
commutator hypothesis since the exponential expansion is the paper's implicit
first-order/BCH-truncation step) the fluctuated operator is the paper's
`D̃ = diag(D₁ + i[D₂,CS], D₂ − i[D₁,CS])` (`twistedFluctuation_chernSimons`).

The square splits **exactly** into a bosonic and a fermionic part
(`square_bosonic_fermionic_split`): since `i` is central and `i² = −1`,

`(D₁ + i·X)² = (D₁² − X²) + i·(D₁X + XD₁)` —

the paper's `D̃² = H_YM + H_fermionic` with `H_YM ∼ D₁² − X²` (Yang–Mills) and
`H_fermionic ∼ i{D₁, X}`, `X = [D₂, CS]` the second Chern–Simons functional
derivative. Blockwise: `blockDiag_sq`.

## §C — the nonlocal fermionic CAR and the change of basis (Eqs 8, 11; paper §5)

Smearing the CAR field against real coefficient vectors (the field at a point `x` has
coefficients `ξᵢ(x)`), `Φ(ξ) = Σᵢ ξᵢ·int(ψᵢ)`, `Φ†(ξ) = Σᵢ ξᵢ·ext(ψᵢ)`:

* `smearedField_anticomm_zero`, `smearedFieldDagger_anticomm_zero` — `{Φ,Φ} = 0`,
  `{Φ†,Φ†} = 0`;
* `smearedField_CAR_kernel` — `{Φ(ζ), Φ†(ξ)} = (Σᵢ ξᵢζᵢ)·1` on an orthonormal family:
  the paper's nonlocal CAR with kernel `K(x,y) = Σᵢ ξᵢ(x)ξᵢ(y)` (Eq. 8);
* `basisChange_CAR_kernel` — the paper's §5: transporting the coefficients through a
  row-orthonormal matrix `M` (`M·Mᵀ = 1`, the triad change of basis
  `ξᵢ = Σₘ φ̃ₘMₘᵢ`) the CAR is **form-invariant** with the transformed kernel
  `Σₘ φₘ(x)φₘ(y)` (Eq. 11) — the algebraic content of "the fermions are no longer
  one-forms".

## Honest scope

Exact `*`-algebra and finite matrix/sum computations on the `IsCAR` carrier.  Recorded,
not re-derived: the configuration-space metric `⟨·,·⟩_A` and its `L²(F)`/BRST
construction, the spin embedding `χ_{(ψ₁,ψ₂)}`, the exponential expansion of the
Chern–Simons unitary (entering only through the commutator hypotheses above), the
basis-dependence term `Ξ` (paper Eq. 3), the identification of `D₁² − X²` with the
Yang–Mills Hamiltonian `Σᵢ(−∇²_{ξᵢ} + [∇_{ξᵢ}, CS]²)`, and the spatial Dirac operator
`D^A = −iσᵃe^μ_a(∇^A_μ + ω_μ)` of Eq. 10.  Non-vacuity: the `IsCAR` hypothesis is
realizable (`Bogoliubov.CARAlgebraAutomorphism.caroneMode_isCAR`), and the antilinear
twist input as well (`caroneMode_twist_antilinear` below).

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2501.00005 [hep-th] (2024): §3 (Clifford algebra,
  Eq. 2), §4 (Dirac operator Eq. 4, twisted fluctuation Eqs 5–6, fermionic sector
  Eqs 7–8), §5 (change of basis, Eqs 9–11).  Companions: arXiv:2410.07290,
  arXiv:2309.06374.  Carriers: `Bogoliubov.CARAlgebraAutomorphism` (`IsCAR`,
  `caroneMode`), `Bogoliubov.FermionicBogoliubovCAR`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-! ## §A — the Clifford algebra of the configuration space -/

/-- **The Clifford multiplication** `c(ψ) = ext(ψ) + int(ψ)` on the CAR carrier:
`int = B`, `ext = star ∘ B`. -/
def cliffordMul (B : K → A) (ψ : K) : A := star (B ψ) + B ψ

/-- **The odd Clifford multiplication** `c̄(ψ) = ext(ψ) − int(ψ)`. -/
def cliffordMulBar (B : K → A) (ψ : K) : A := star (B ψ) - B ψ

/-- `{ext(ψ₁), ext(ψ₂)} = 0` — the star of the CAR annihilator relation. -/
lemma ext_anticomm_zero {B : K → A} (hB : IsCAR B) (ψ₁ ψ₂ : K) :
    star (B ψ₁) * star (B ψ₂) + star (B ψ₂) * star (B ψ₁) = 0 := by
  have h := congrArg star (hB.2 ψ₂ ψ₁)
  simpa [star_add, star_mul] using h

/-- **`{c(ψ₁), c(ψ₂)} = (⟨ψ₂,ψ₁⟩ + ⟨ψ₁,ψ₂⟩)·1`** — for the paper's real metric
`⟨·,·⟩_A` this is `2⟨ψ₁,ψ₂⟩·1`; the paper's `{c(ηᵢ), c(ηⱼ)} = δᵢⱼ` convention absorbs
the normalization. -/
theorem cliffordMul_anticomm {B : K → A} (hB : IsCAR B) (ψ₁ ψ₂ : K) :
    cliffordMul B ψ₁ * cliffordMul B ψ₂ + cliffordMul B ψ₂ * cliffordMul B ψ₁
      = (inner ℂ ψ₂ ψ₁ + inner ℂ ψ₁ ψ₂) • (1 : A) := by
  have h12 := hB.1 ψ₁ ψ₂
  have h21 := hB.1 ψ₂ ψ₁
  have hbb := hB.2 ψ₁ ψ₂
  have hee := ext_anticomm_zero hB ψ₁ ψ₂
  have key : cliffordMul B ψ₁ * cliffordMul B ψ₂ + cliffordMul B ψ₂ * cliffordMul B ψ₁
      = (B ψ₁ * star (B ψ₂) + star (B ψ₂) * B ψ₁)
        + (B ψ₂ * star (B ψ₁) + star (B ψ₁) * B ψ₂)
        + ((star (B ψ₁) * star (B ψ₂) + star (B ψ₂) * star (B ψ₁))
          + (B ψ₁ * B ψ₂ + B ψ₂ * B ψ₁)) := by
    unfold cliffordMul
    noncomm_ring
  rw [key, h12, h21, hee, hbb, add_zero, add_zero, ← add_smul, add_comm]

/-- **`{c̄(ψ₁), c̄(ψ₂)} = −(⟨ψ₂,ψ₁⟩ + ⟨ψ₁,ψ₂⟩)·1`** — the odd multiplications generate
the negative-definite copy. -/
theorem cliffordMulBar_anticomm {B : K → A} (hB : IsCAR B) (ψ₁ ψ₂ : K) :
    cliffordMulBar B ψ₁ * cliffordMulBar B ψ₂ + cliffordMulBar B ψ₂ * cliffordMulBar B ψ₁
      = -((inner ℂ ψ₂ ψ₁ + inner ℂ ψ₁ ψ₂) • (1 : A)) := by
  have h12 := hB.1 ψ₁ ψ₂
  have h21 := hB.1 ψ₂ ψ₁
  have hbb := hB.2 ψ₁ ψ₂
  have hee := ext_anticomm_zero hB ψ₁ ψ₂
  have key : cliffordMulBar B ψ₁ * cliffordMulBar B ψ₂
        + cliffordMulBar B ψ₂ * cliffordMulBar B ψ₁
      = ((star (B ψ₁) * star (B ψ₂) + star (B ψ₂) * star (B ψ₁))
          + (B ψ₁ * B ψ₂ + B ψ₂ * B ψ₁))
        - ((B ψ₁ * star (B ψ₂) + star (B ψ₂) * B ψ₁)
          + (B ψ₂ * star (B ψ₁) + star (B ψ₁) * B ψ₂)) := by
    unfold cliffordMulBar
    noncomm_ring
  rw [key, h12, h21, hee, hbb, add_zero, zero_sub, ← add_smul,
    add_comm (inner ℂ ψ₁ ψ₂) (inner ℂ ψ₂ ψ₁)]

/-- **`{c(ψ₁), c̄(ψ₂)} = (⟨ψ₁,ψ₂⟩ − ⟨ψ₂,ψ₁⟩)·1`** — purely the antisymmetric part of
the inner product. -/
theorem cliffordMul_mulBar_anticomm {B : K → A} (hB : IsCAR B) (ψ₁ ψ₂ : K) :
    cliffordMul B ψ₁ * cliffordMulBar B ψ₂ + cliffordMulBar B ψ₂ * cliffordMul B ψ₁
      = (inner ℂ ψ₁ ψ₂ - inner ℂ ψ₂ ψ₁) • (1 : A) := by
  have h12 := hB.1 ψ₁ ψ₂
  have h21 := hB.1 ψ₂ ψ₁
  have hbb := hB.2 ψ₁ ψ₂
  have hee := ext_anticomm_zero hB ψ₁ ψ₂
  have key : cliffordMul B ψ₁ * cliffordMulBar B ψ₂
        + cliffordMulBar B ψ₂ * cliffordMul B ψ₁
      = ((star (B ψ₁) * star (B ψ₂) + star (B ψ₂) * star (B ψ₁))
          - (B ψ₁ * B ψ₂ + B ψ₂ * B ψ₁))
        + ((B ψ₁ * star (B ψ₂) + star (B ψ₂) * B ψ₁)
          - (star (B ψ₁) * B ψ₂ + B ψ₂ * star (B ψ₁))) := by
    unfold cliffordMul cliffordMulBar
    noncomm_ring
  have h21' : star (B ψ₁) * B ψ₂ + B ψ₂ * star (B ψ₁) = inner ℂ ψ₂ ψ₁ • 1 := by
    rw [← h21]; exact add_comm _ _
  rw [key, h12, h21', hee, hbb, sub_zero, zero_add, ← sub_smul]

/-- **`{c, c̄} = 0` for a symmetric inner product** — the paper's `⟨·,·⟩_A` is a real
metric, so its two Clifford families anticommute (paper §3). -/
theorem cliffordMul_mulBar_anticomm_real {B : K → A} (hB : IsCAR B) (ψ₁ ψ₂ : K)
    (hsym : inner ℂ ψ₁ ψ₂ = inner ℂ ψ₂ ψ₁) :
    cliffordMul B ψ₁ * cliffordMulBar B ψ₂ + cliffordMulBar B ψ₂ * cliffordMul B ψ₁
      = 0 := by
  rw [cliffordMul_mulBar_anticomm hB, hsym, sub_self, zero_smul]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Module ℂ A] in
/-- **`c(ψ)* = c(ψ)`** — the even Clifford multiplication is self-adjoint. -/
theorem cliffordMul_star (B : K → A) (ψ : K) :
    star (cliffordMul B ψ) = cliffordMul B ψ := by
  unfold cliffordMul
  rw [star_add, star_star, add_comm]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Module ℂ A] in
/-- **`c̄(ψ)* = −c̄(ψ)`** — the odd Clifford multiplication is anti-self-adjoint. -/
theorem cliffordMulBar_star (B : K → A) (ψ : K) :
    star (cliffordMulBar B ψ) = -cliffordMulBar B ψ := by
  unfold cliffordMulBar
  rw [star_sub, star_star, neg_sub]

/-! ### The twist (paper Eq. 2) -/

/-- **`c(iψ) = i·c̄(ψ)`** (paper Eq. 2): since `int` is antilinear
(`B(iψ) = −i·B(ψ)`) and `ext` is linear, multiplying the argument by the complex `i`
interchanges the two Clifford multiplications.  This is the twist on which the whole
fluctuation mechanism rests. -/
theorem cliffordMul_twist [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ : K) :
    cliffordMul B (Complex.I • ψ) = Complex.I • cliffordMulBar B ψ := by
  unfold cliffordMul cliffordMulBar
  rw [hanti, star_neg, star_smul, Complex.star_def, Complex.conj_I, neg_smul, neg_neg,
    smul_sub, sub_eq_add_neg]

/-- **`c̄(iψ) = i·c(ψ)`** — the twist in the other direction. -/
theorem cliffordMulBar_twist [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ : K) :
    cliffordMulBar B (Complex.I • ψ) = Complex.I • cliffordMul B ψ := by
  unfold cliffordMul cliffordMulBar
  rw [hanti, star_neg, star_smul, Complex.star_def, Complex.conj_I, neg_smul, neg_neg,
    sub_neg_eq_add, smul_add]

/-- **Dimension doubling, same relations**: `{c(iψ₁), c(iψ₂)} = {c(ψ₁), c(ψ₂)}` — the
twisted family `c(iηᵢ)` satisfies the *same* Clifford relations as `c(ηᵢ)` (paper §3:
"the Clifford algebra of double dimension"). -/
theorem doubled_anticomm [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ₁ ψ₂ : K) :
    cliffordMul B (Complex.I • ψ₁) * cliffordMul B (Complex.I • ψ₂)
        + cliffordMul B (Complex.I • ψ₂) * cliffordMul B (Complex.I • ψ₁)
      = (inner ℂ ψ₂ ψ₁ + inner ℂ ψ₁ ψ₂) • (1 : A) := by
  rw [cliffordMul_twist hanti, cliffordMul_twist hanti,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, cliffordMulBar_anticomm hB,
    smul_neg, Complex.I_mul_I, neg_smul, neg_neg, one_smul]

/-- **The two families anticommute on a symmetric pair**: `{c(ψ₁), c(iψ₂)} = 0` —
together with `doubled_anticomm` this exhibits the doubled Clifford algebra inside the
operators on the exterior algebra. -/
theorem doubled_mixed_anticomm [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ₁ ψ₂ : K)
    (hsym : inner ℂ ψ₁ ψ₂ = inner ℂ ψ₂ ψ₁) :
    cliffordMul B ψ₁ * cliffordMul B (Complex.I • ψ₂)
        + cliffordMul B (Complex.I • ψ₂) * cliffordMul B ψ₁ = 0 := by
  rw [cliffordMul_twist hanti, mul_smul_comm, smul_mul_assoc, ← smul_add,
    cliffordMul_mulBar_anticomm_real hB ψ₁ ψ₂ hsym, smul_zero]

/-- **Non-vacuity of the twist input**: the concrete single-mode CAR field
`caroneMode` is antilinear in the required sense, so `hanti` (and with
`caroneMode_isCAR` the whole §A) is realizable. -/
lemma caroneMode_twist_antilinear (c : ℂ) :
    caroneMode (Complex.I • c) = -(Complex.I • caroneMode c) := by
  unfold caroneMode
  rw [← neg_smul, smul_smul]
  congr 1
  rw [smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]

/-! ## §B — the twisted inner fluctuation -/

variable {R : Type*} [Ring R]

/-- The block-diagonal `2×2` operator `diag(P, Q)` (the paper's Eq. 4 shape). -/
def blockDiag (P Q : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then P else 0) else (if j = 1 then Q else 0)

/-- The grading `γ = offdiag(1,1)` of paper §4. -/
def gammaSwap : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => if i = j then 0 else 1

/-- `γ² = 1`, so `γ⁻¹ = γ`. -/
theorem gammaSwap_mul_self : (gammaSwap : Matrix (Fin 2) (Fin 2) R) * gammaSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`γ·diag(P,Q)·γ = diag(Q,P)`** — conjugation by the grading interchanges the two
blocks: the mechanism that feeds the `D₂` fluctuation into the `D₁` sector. -/
theorem gammaSwap_conj (P Q : R) :
    gammaSwap * blockDiag P Q * gammaSwap = blockDiag Q P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaSwap, blockDiag, Matrix.mul_apply, Fin.sum_univ_two]

/-- `diag(P,Q)·diag(P',Q') = diag(PP', QQ')`. -/
theorem blockDiag_mul (P Q P' Q' : R) :
    blockDiag P Q * blockDiag P' Q' = blockDiag (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.mul_apply, Fin.sum_univ_two]

/-- `diag(P,Q) + diag(P',Q') = diag(P+P', Q+Q')`. -/
theorem blockDiag_add (P Q P' Q' : R) :
    blockDiag P Q + blockDiag P' Q' = blockDiag (P + P') (Q + Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag]

/-- `diag(P,Q)² = diag(P², Q²)` — the fluctuated Dirac operator squares blockwise
(paper: `D̃² = diag(H_YM + H_f, H_YM + H_f)`). -/
theorem blockDiag_sq (P Q : R) : blockDiag P Q ^ 2 = blockDiag (P ^ 2) (Q ^ 2) := by
  rw [sq, sq, sq, blockDiag_mul]

/-- **The twisted inner fluctuation is exact block algebra** (paper Eqs 5–6): for
`D = diag(D₁,D₂)`, `u = diag(a,b)` with two-sided inverse `diag(a',b')`,

`D + γ·u[D,u⁻¹]·γ⁻¹ = diag(D₁ + b(D₂b' − b'D₂), D₂ + a(D₁a' − a'D₁))` —

the `γ`-twist interchanges which block receives which fluctuation.  No expansion of
the unitary is needed; this is an identity in any ring. -/
theorem twistedFluctuation_eq (D₁ D₂ a b a' b' : R) :
    blockDiag D₁ D₂
      + gammaSwap * (blockDiag a b
          * (blockDiag D₁ D₂ * blockDiag a' b' - blockDiag a' b' * blockDiag D₁ D₂))
        * gammaSwap
    = blockDiag (D₁ + b * (D₂ * b' - b' * D₂)) (D₂ + a * (D₁ * a' - a' * D₁)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, gammaSwap, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two]

/-- **The fluctuated Dirac operator with the Chern–Simons unitary** (paper Eq. 6):
with the commutator inputs `b[D₂,b⁻¹] = i[D₂,CS]` and `a[D₁,a⁻¹] = −i[D₁,CS]` (the
content of `u = diag(e^{iCS}, e^{−iCS})`; the exponential expansion is the paper's
implicit truncation step, recorded here as the hypothesis),

`D̃ = D + γ·u[D,u⁻¹]·γ⁻¹ = diag(D₁ + i[D₂,CS], D₂ − i[D₁,CS])`. -/
theorem twistedFluctuation_chernSimons [Algebra ℂ R] (D₁ D₂ CS a b a' b' : R)
    (hb : b * (D₂ * b' - b' * D₂)
      = algebraMap ℂ R Complex.I * (D₂ * CS - CS * D₂))
    (ha : a * (D₁ * a' - a' * D₁)
      = -(algebraMap ℂ R Complex.I * (D₁ * CS - CS * D₁))) :
    blockDiag D₁ D₂
      + gammaSwap * (blockDiag a b
          * (blockDiag D₁ D₂ * blockDiag a' b' - blockDiag a' b' * blockDiag D₁ D₂))
        * gammaSwap
    = blockDiag (D₁ + algebraMap ℂ R Complex.I * (D₂ * CS - CS * D₂))
        (D₂ - algebraMap ℂ R Complex.I * (D₁ * CS - CS * D₁)) := by
  rw [twistedFluctuation_eq, hb, ha]
  congr 1
  exact (sub_eq_add_neg _ _).symm

/-- **The square splits exactly into bosonic + fermionic parts** (paper §4, the
`D̃² = H_YM + H_fermionic` mechanism): since `i` is central with `i² = −1`,

`(D + i·X)² = (D² − X²) + i·(DX + XD)` —

the `i`-free part `D² − X²` is the bosonic (Yang–Mills) Hamiltonian, and the term the
twist alone made survive, `i·{D, X}` with `X = [D₂, CS]` the second functional
derivative of the Chern–Simons term, is the fermionic Hamiltonian (paper Eq. 7). -/
theorem square_bosonic_fermionic_split [Algebra ℂ R] (D X : R) :
    (D + algebraMap ℂ R Complex.I * X) ^ 2
      = (D ^ 2 - X ^ 2) + algebraMap ℂ R Complex.I * (D * X + X * D) := by
  have hI2 : algebraMap ℂ R Complex.I * algebraMap ℂ R Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hc : ∀ r : R, r * algebraMap ℂ R Complex.I = algebraMap ℂ R Complex.I * r :=
    fun r => (Algebra.commutes Complex.I r).symm
  have expand : (D + algebraMap ℂ R Complex.I * X) ^ 2
      = D * D + D * (algebraMap ℂ R Complex.I * X)
        + (algebraMap ℂ R Complex.I * X) * D
        + (algebraMap ℂ R Complex.I * X) * (algebraMap ℂ R Complex.I * X) := by
    noncomm_ring
  rw [expand, ← mul_assoc D, hc D, mul_assoc _ X D,
    show (algebraMap ℂ R Complex.I * X) * (algebraMap ℂ R Complex.I * X)
        = algebraMap ℂ R Complex.I * algebraMap ℂ R Complex.I * (X * X) by
      rw [mul_assoc, ← mul_assoc X, hc X, mul_assoc, mul_assoc],
    hI2]
  noncomm_ring

/-! ## §C — the nonlocal fermionic CAR and the change of basis -/

variable {n m : ℕ}

/-- **The fermionic field** `Φ(ξ) = Σᵢ ξᵢ·int(ψᵢ)` — the paper's
`Φ(x) = Σᵢ ξᵢ(x)·int(ψᵢ)`, with the point `x` abstracted into its real coefficient
vector `ξ`. -/
def smearedField (B : K → A) (ψ : Fin n → K) (ξ : Fin n → ℝ) : A :=
  ∑ i, ((ξ i : ℂ)) • B (ψ i)

/-- **The conjugate fermionic field** `Φ†(ξ) = Σᵢ ξᵢ·ext(ψᵢ)`. -/
def smearedFieldDagger (B : K → A) (ψ : Fin n → K) (ξ : Fin n → ℝ) : A :=
  ∑ i, ((ξ i : ℂ)) • star (B (ψ i))

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] in
/-- `Φ†(ξ) = Φ(ξ)*` — the dagger field is the star of the field. -/
lemma smearedFieldDagger_eq_star [StarModule ℂ A] (B : K → A) (ψ : Fin n → K) (ξ : Fin n → ℝ) :
    smearedFieldDagger B ψ ξ = star (smearedField B ψ ξ) := by
  unfold smearedField smearedFieldDagger
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal]

/-- **`{Φ(ξ), Φ(ζ)} = 0`** (paper Eq. 8, first relation): bilinearity over the CAR
annihilator relation. -/
theorem smearedField_anticomm_zero [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (ψ : Fin n → K) (ξ ζ : Fin n → ℝ) :
    smearedField B ψ ξ * smearedField B ψ ζ
      + smearedField B ψ ζ * smearedField B ψ ξ = 0 := by
  unfold smearedField
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ i, ∑ j, ((ζ i : ℂ)) • B (ψ i) * ((ξ j : ℂ)) • B (ψ j))
      = ∑ i, ∑ j, ((ζ j : ℂ)) • B (ψ j) * ((ξ i : ℂ)) • B (ψ i) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((ζ j : ℂ)) ((ξ i : ℂ)),
    ← smul_add, hB.2, smul_zero]

/-- **`{Φ†(ξ), Φ†(ζ)} = 0`** (paper Eq. 8, second relation). -/
theorem smearedFieldDagger_anticomm_zero [StarModule ℂ A] [SMulCommClass ℂ A A]
    [IsScalarTower ℂ A A] {B : K → A} (hB : IsCAR B)
    (ψ : Fin n → K) (ξ ζ : Fin n → ℝ) :
    smearedFieldDagger B ψ ξ * smearedFieldDagger B ψ ζ
      + smearedFieldDagger B ψ ζ * smearedFieldDagger B ψ ξ = 0 := by
  rw [smearedFieldDagger_eq_star, smearedFieldDagger_eq_star, ← star_mul, ← star_mul,
    ← star_add]
  rw [smearedField_anticomm_zero hB ψ ζ ξ, star_zero]

/-- **The nonlocal CAR** (paper Eq. 8): on an orthonormal family,
`{Φ(ζ), Φ†(ξ)} = (Σᵢ ξᵢζᵢ)·1` — the anticommutator is the integral kernel
`K(x,y) = Σᵢ ξᵢ(x)ξᵢ(y)`, a nonlocal Dirac delta in the flat limit. -/
theorem smearedField_CAR_kernel [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (ψ : Fin n → K) (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (ξ ζ : Fin n → ℝ) :
    smearedField B ψ ζ * smearedFieldDagger B ψ ξ
      + smearedFieldDagger B ψ ξ * smearedField B ψ ζ
      = (((∑ i, ξ i * ζ i : ℝ) : ℂ)) • (1 : A) := by
  unfold smearedField smearedFieldDagger
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ i, ∑ j, ((ξ i : ℂ)) • star (B (ψ i)) * ((ζ j : ℂ)) • B (ψ j))
      = ∑ i, ∑ j, ((ξ j : ℂ)) • star (B (ψ j)) * ((ζ i : ℂ)) • B (ψ i) :=
    Finset.sum_comm
  have hterm : ∀ i j : Fin n,
      ((ζ i : ℂ)) • B (ψ i) * ((ξ j : ℂ)) • star (B (ψ j))
        + ((ξ j : ℂ)) • star (B (ψ j)) * ((ζ i : ℂ)) • B (ψ i)
      = (if i = j then ((ξ j * ζ i : ℝ) : ℂ) else 0) • (1 : A) := by
    intro i j
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((ξ j : ℂ)) ((ζ i : ℂ)),
      ← smul_add, hB.1, hON, smul_smul, mul_ite, mul_one, mul_zero]
    congr 1
    by_cases h : i = j <;> simp [h, mul_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  have hrow : ∀ i : Fin n,
      ((∑ j, ((ζ i : ℂ)) • B (ψ i) * ((ξ j : ℂ)) • star (B (ψ j)))
        + ∑ j, ((ξ j : ℂ)) • star (B (ψ j)) * ((ζ i : ℂ)) • B (ψ i))
      = ((ξ i * ζ i : ℝ) : ℂ) • (1 : A) := by
    intro i
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => hterm i j]
    simp [ite_smul]
  rw [Finset.sum_congr rfl fun i _ => hrow i, ← Finset.sum_smul]
  norm_cast

/-- **The change of basis preserves the CAR and transforms the kernel** (paper §5,
Eq. 11): transporting the coefficients through a row-orthonormal matrix `M`
(`M·Mᵀ = 1` — the triad change of basis `ξᵢ = Σₘ φ̃ₘ·Mₘᵢ`), the transformed fields
`Ψ(φ) = Φ(Mᵀφ)` satisfy the *same* CAR with the transformed kernel
`{Ψ(χ), Ψ†(φ)} = (Σₘ φₘχₘ)·1` — the algebraic content of the paper's statement that
the new fermions (no longer one-forms) are canonically quantized on the curved
background. -/
theorem basisChange_CAR_kernel [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (ψ : Fin n → K) (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (M : Matrix (Fin m) (Fin n) ℝ) (hM : M * M.transpose = 1)
    (φ χ : Fin m → ℝ) :
    smearedField B ψ (fun i => ∑ m', χ m' * M m' i)
        * smearedFieldDagger B ψ (fun i => ∑ m', φ m' * M m' i)
      + smearedFieldDagger B ψ (fun i => ∑ m', φ m' * M m' i)
        * smearedField B ψ (fun i => ∑ m', χ m' * M m' i)
      = (((∑ m', φ m' * χ m' : ℝ) : ℂ)) • (1 : A) := by
  rw [smearedField_CAR_kernel hB ψ hON]
  congr 2
  calc ∑ i, (∑ m', φ m' * M m' i) * (∑ m', χ m' * M m' i)
      = ∑ i, ∑ p, ∑ q, φ p * M p i * (χ q * M q i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ p, ∑ q, φ p * χ q * ∑ i, M p i * M q i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ p, ∑ q, φ p * χ q * (if p = q then 1 else 0) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        have : (M * M.transpose) p q = ∑ i, M p i * M q i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [Matrix.transpose_apply]
        rw [← this, hM, Matrix.one_apply]
    _ = ∑ p, φ p * χ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_ite, Finset.sum_ite_eq]

/-! ## §D — Dirac's dead-wood model (Dirac 1965)

Dirac's model Hamiltonian from *Quantum Electrodynamics without Dead Wood*, Phys.
Rev. **139**, B684 (1965), lives on exactly this module's CAR carriers: his Eq. 8 is
`IsCAR` (`η* = B` absorption, `η = star ∘ B` emission) and his Hamiltonian is
`H = ½·a_{rs}(η_rη_s − η*_rη*_s)` with `a` real antisymmetric, `a² = −1`.  Dirac's
thesis — *"the Heisenberg picture is a good picture, the Schrödinger picture is a
bad picture, and the two pictures are not equivalent"* — rests on two exact facts:

* `deadwood_coefficient` — the scalar coefficient in `H²|S⟩` equals the mode count,
  `Σ_{rs}a_{rs}² = n`: finite for every finite model, divergent as `n → ∞` — why
  `H²|S⟩` *"does not exist"* and the Schrödinger flow fails on the bare vacuum
  (`column_orthogonality` gives the `aᵀa = 1` contraction; `deadwood_witness` the
  symplectic example).
* `seaModes_anticommute` — the shifted modes `ζ_r = η*_r + a_{rs}η_s` of Dirac's
  Eq. 14 (the filled-sea/Bogoliubov vacuum `ζ_r|Y⟩ = 0`) pairwise anticommute
  **precisely because `a` is antisymmetric** — his *"as one easily checks"*, so the
  sea-vacuum conditions are simultaneously satisfiable; the Schrödinger picture
  works on `|Y⟩` though not on `|S⟩`.  The contraction engines
  (`bare_sum_contraction`, `starred_sums_anticommute`) also serve the
  normal-ordering identity `Σζ*_pζ_p = 2H + n·1` (recorded). -/

/-! ### The dead wood: divergence data of the model -/

/-- **The dead-wood coefficient equals the mode count**: for a real antisymmetric
`a` with `a² = −1` (Dirac's example), the scalar coefficient appearing in `H²|S⟩`
is `Σ_{rs} a_{rs}² = n` — finite for every finite model, divergent as `n → ∞`:
exactly why `H²|S⟩` *"does not exist"* and the Schrödinger picture fails on the
bare vacuum. -/
theorem deadwood_coefficient (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) :
    ∑ r, ∑ s, (a r s) ^ 2 = n := by
  have h1 : ∀ r : Fin n, ∑ s, (a r s) ^ 2 = -(∑ s, a r s * a s r) := by
    intro r
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hanti r s]
    ring
  calc ∑ r, ∑ s, (a r s) ^ 2
      = ∑ r : Fin n, -(∑ s, a r s * a s r) :=
        Finset.sum_congr rfl fun r _ => h1 r
    _ = ∑ r : Fin n, -(if r = r then (-1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun r _ => by rw [hsq r r]
    _ = n := by simp

/-- **Antisymmetry with `a² = −1` makes `a` orthogonal**: `Σ_p a_{ps}a_{pq} = δ_{sq}`
(`aᵀa = 1`) — the contraction that collapses the normal-ordering cross terms. -/
theorem column_orthogonality (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) (s q : Fin n) :
    ∑ p, a p s * a p q = if s = q then 1 else 0 := by
  have h1 : ∑ p, a p s * a p q = -(∑ p, a s p * a p q) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hanti p s]
    ring
  rw [h1, hsq s q]
  by_cases h : s = q <;> simp [h]

/-- **Dirac's example exists** (non-vacuity): the symplectic `J = [[0,−1],[1,0]]`
is real antisymmetric with `J² = −1`. -/
theorem deadwood_witness :
    ∃ a : Fin 2 → Fin 2 → ℝ,
      (∀ r s, a r s = -(a s r))
        ∧ (∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) := by
  refine ⟨fun r s => if r = 0 ∧ s = 1 then -1 else if r = 1 ∧ s = 0 then 1 else 0,
    ?_, ?_⟩
  · intro r s
    fin_cases r <;> fin_cases s <;> norm_num
  · intro r q
    fin_cases r <;> fin_cases q <;> simp

/-! ### The sea vacuum (Dirac's Eq. 14) -/

/-- **Dirac's shifted mode** (Eq. 14): `ζ_r = η*_r + Σ_s a_{rs}·η_s` — on the CAR
carrier, `ζ_r = B(ψ_r) + Σ_s a_{rs}·(B(ψ_s))*`.  The condition `ζ_r|Y⟩ = 0`
defines the sea vacuum, a fermionic Bogoliubov shift of the bare modes. -/
noncomputable def seaMode (B : K → A) (ψ : Fin n → K)
    (a : Fin n → Fin n → ℝ) (r : Fin n) : A :=
  B (ψ r) + ∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s))

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] in
/-- The star of the shifted mode: `ζ*_r = η_r + Σ_s a_{rs}·η*_s`. -/
theorem star_seaMode [StarModule ℂ A] (B : K → A) (ψ : Fin n → K)
    (a : Fin n → Fin n → ℝ) (r : Fin n) :
    star (seaMode B ψ a r)
      = star (B (ψ r)) + ∑ s, ((a r s : ℝ) : ℂ) • B (ψ s) := by
  unfold seaMode
  rw [star_add, star_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_smul, star_star, Complex.star_def, Complex.conj_ofReal]

/-- Contraction of a bare mode against a coefficient sum of starred modes:
`{B_r, Σ_q c_q·B*_q} = c_r·1`. -/
private theorem bare_sum_contraction [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} {ψ : Fin n → K} (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (c : Fin n → ℂ) (r : Fin n) :
    B (ψ r) * (∑ q, c q • star (B (ψ q)))
        + (∑ q, c q • star (B (ψ q))) * B (ψ r)
      = c r • (1 : A) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  calc ∑ q, (B (ψ r) * (c q • star (B (ψ q))) + (c q • star (B (ψ q))) * B (ψ r))
      = ∑ q, c q • ((if r = q then 1 else 0 : ℂ) • (1 : A)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hB.1, hON]
    _ = ∑ q, (if r = q then c q else 0) • (1 : A) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul, mul_ite, mul_one, mul_zero]
    _ = c r • (1 : A) := by
        simp [ite_smul]

/-- Two coefficient sums of starred modes anticommute:
`{Σ_s c_s·B*_s, Σ_q d_q·B*_q} = 0`. -/
private theorem starred_sums_anticommute [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} {ψ : Fin n → K} (hB : IsCAR B) (c d : Fin n → ℂ) :
    (∑ s, c s • star (B (ψ s))) * (∑ q, d q • star (B (ψ q)))
        + (∑ q, d q • star (B (ψ q))) * (∑ s, c s • star (B (ψ s)))
      = 0 := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ q, ∑ s, (d q • star (B (ψ q))) * (c s • star (B (ψ s))))
      = ∑ s, ∑ q, (d q • star (B (ψ q))) * (c s • star (B (ψ s))) :=
    Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (d q) (c s), ← smul_add,
    ext_anticomm_zero hB, smul_zero]

/-- **Dirac's consistency check for Eq. 14** (*"as one easily checks, the
quantities anticommute"*): the shifted modes pairwise anticommute,
`ζ_r ζ_p + ζ_p ζ_r = 0` — **precisely because `a` is antisymmetric**: the two CAR
`δ`-contractions produce `a_{pr} + a_{rp} = 0`, so the sea-vacuum conditions for
different `r` are simultaneously satisfiable. -/
theorem seaModes_anticommute [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} {ψ : Fin n → K} (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r)) (r p : Fin n) :
    seaMode B ψ a r * seaMode B ψ a p + seaMode B ψ a p * seaMode B ψ a r = 0 := by
  unfold seaMode
  have key : (B (ψ r) + ∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
        * (B (ψ p) + ∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s)))
      + (B (ψ p) + ∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s)))
        * (B (ψ r) + ∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
      = (B (ψ r) * B (ψ p) + B (ψ p) * B (ψ r))
        + (B (ψ r) * (∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s)))
            + (∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s))) * B (ψ r))
        + (B (ψ p) * (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
            + (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s))) * B (ψ p))
        + ((∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
              * (∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s)))
            + (∑ s, ((a p s : ℝ) : ℂ) • star (B (ψ s)))
              * (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))) := by
    noncomm_ring
  rw [key, hB.2, bare_sum_contraction hB hON _ r, bare_sum_contraction hB hON _ p,
    starred_sums_anticommute hB, zero_add, add_zero, ← add_smul]
  have hzero : ((a p r : ℝ) : ℂ) + ((a r p : ℝ) : ℂ) = 0 := by
    rw [hanti p r]
    push_cast
    ring
  rw [hzero, zero_smul]

/-- **Dirac's quadratic Hamiltonian, doubled**: `2H = a_{rs}(η_rη_s − η*_rη*_s)` on
the CAR carrier (`η = star ∘ B` emission, `η* = B` absorption). -/
noncomputable def diracQuadratic (B : K → A) (ψ : Fin n → K)
    (a : Fin n → Fin n → ℝ) : A :=
  (∑ r, ∑ s, ((a r s : ℝ) : ℂ) • (star (B (ψ r)) * star (B (ψ s))))
    - ∑ r, ∑ s, ((a r s : ℝ) : ℂ) • (B (ψ r) * B (ψ s))

/-- **Dirac's normal-ordering identity**: `Σ_p ζ*_p ζ_p = 2H + n·1` — the
normal-ordered positive form reproduces (twice) the Hamiltonian plus the
mode-count constant.  Dirac: *"the last term here is an infinite constant and may
be discarded"* — at finite `n` it is exactly `n`, the same divergence as
`deadwood_coefficient`. -/
theorem hamiltonian_normalOrdered [StarModule ℂ A] [SMulCommClass ℂ A A]
    [IsScalarTower ℂ A A] {B : K → A} {ψ : Fin n → K} (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) :
    ∑ p, star (seaMode B ψ a p) * seaMode B ψ a p
      = diracQuadratic B ψ a + (n : ℂ) • (1 : A) := by
  -- per-mode expansion of ζ*_p ζ_p into the four CAR groups
  have hexp : ∀ p : Fin n, star (seaMode B ψ a p) * seaMode B ψ a p
      = star (B (ψ p)) * B (ψ p)
        + (∑ q, ((a p q : ℝ) : ℂ) • (star (B (ψ p)) * star (B (ψ q))))
        + (∑ s, ((a p s : ℝ) : ℂ) • (B (ψ s) * B (ψ p)))
        + ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (B (ψ s) * star (B (ψ q))) := by
    intro p
    rw [star_seaMode]
    unfold seaMode
    have e1 : star (B (ψ p)) * (∑ q, ((a p q : ℝ) : ℂ) • star (B (ψ q)))
        = ∑ q, ((a p q : ℝ) : ℂ) • (star (B (ψ p)) * star (B (ψ q))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => mul_smul_comm _ _ _
    have e2 : (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s)) * B (ψ p)
        = ∑ s, ((a p s : ℝ) : ℂ) • (B (ψ s) * B (ψ p)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => smul_mul_assoc _ _ _
    have e3 : (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
          * (∑ q, ((a p q : ℝ) : ℂ) • star (B (ψ q)))
        = ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (B (ψ s) * star (B (ψ q))) := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ =>
        smul_mul_smul_comm _ _ _ _
    rw [add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  -- resolve the mixed group through the CAR: b_s e_q = δ_{sq}·1 − e_q b_s
  have hmix : ∀ p : Fin n,
      (∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
          • (B (ψ s) * star (B (ψ q))))
        = (∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) • (1 : A)
          - ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
              • (star (B (ψ q)) * B (ψ s)) := by
    intro p
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    calc ∑ s, ((∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (B (ψ s) * star (B (ψ q))))
          + ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
              • (star (B (ψ q)) * B (ψ s)))
        = ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (B (ψ s) * star (B (ψ q)) + star (B (ψ q)) * B (ψ s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun q _ => (smul_add _ _ _).symm
      _ = ∑ s, ∑ q, (if s = q then ((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ) else 0)
            • (1 : A) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
          rw [hB.1, hON, smul_smul, mul_ite, mul_one, mul_zero]
      _ = ∑ s, (((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) • (1 : A) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [ite_smul]
      _ = (∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) • (1 : A) :=
          (Finset.sum_smul).symm
  -- the diagonal-square scalar sums to the mode count
  have hP4 : (∑ p : Fin n, ∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) = (n : ℂ) := by
    have hcast : (∑ p : Fin n, ∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ))
        = ((∑ p : Fin n, ∑ s, (a p s) ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => (sq _).symm
    rw [hcast, deadwood_coefficient a hanti hsq]
    norm_cast
  -- the cross group collapses to the bare number operator via column orthogonality
  have hP5 : (∑ p : Fin n, ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
        • (star (B (ψ q)) * B (ψ s)))
      = ∑ s, star (B (ψ s)) * B (ψ s) := by
    calc ∑ p : Fin n, ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
          • (star (B (ψ q)) * B (ψ s))
        = ∑ s, ∑ p : Fin n, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (star (B (ψ q)) * B (ψ s)) := Finset.sum_comm
      _ = ∑ s, ∑ q, ∑ p : Fin n, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (star (B (ψ q)) * B (ψ s)) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s, ∑ q, (∑ p : Fin n, ((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
            • (star (B (ψ q)) * B (ψ s)) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ =>
            (Finset.sum_smul).symm
      _ = ∑ s, ∑ q, ((if s = q then 1 else 0 : ℂ)) • (star (B (ψ q)) * B (ψ s)) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
          congr 1
          have hcast : (∑ p, ((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
              = ((∑ p, a p s * a p q : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [hcast, column_orthogonality a hanti hsq s q]
          by_cases h : s = q <;> simp [h]
      _ = ∑ s, star (B (ψ s)) * B (ψ s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [ite_smul]
  -- the anomalous group is antisymmetric-odd: relabel through `hanti`
  have hP3 : (∑ p : Fin n, ∑ s, ((a p s : ℝ) : ℂ) • (B (ψ s) * B (ψ p)))
      = -∑ r, ∑ s, ((a r s : ℝ) : ℂ) • (B (ψ r) * B (ψ s)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show ((a s r : ℝ) : ℂ) = -((a r s : ℝ) : ℂ) by
      rw [hanti s r]; push_cast; ring, neg_smul]
  -- assemble
  calc ∑ p, star (seaMode B ψ a p) * seaMode B ψ a p
      = ∑ p, (star (B (ψ p)) * B (ψ p)
          + (∑ q, ((a p q : ℝ) : ℂ) • (star (B (ψ p)) * star (B (ψ q))))
          + (∑ s, ((a p s : ℝ) : ℂ) • (B (ψ s) * B (ψ p)))
          + ((∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) • (1 : A)
            - ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
                • (star (B (ψ q)) * B (ψ s)))) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hexp p, hmix p]
    _ = (∑ p, star (B (ψ p)) * B (ψ p))
        + (∑ p, ∑ q, ((a p q : ℝ) : ℂ) • (star (B (ψ p)) * star (B (ψ q))))
        + (∑ p, ∑ s, ((a p s : ℝ) : ℂ) • (B (ψ s) * B (ψ p)))
        + ((∑ p, (∑ s, ((a p s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ)) • (1 : A))
          - ∑ p, ∑ s, ∑ q, (((a p s : ℝ) : ℂ) * ((a p q : ℝ) : ℂ))
              • (star (B (ψ q)) * B (ψ s))) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = (∑ p, star (B (ψ p)) * B (ψ p))
        + (∑ r, ∑ s, ((a r s : ℝ) : ℂ) • (star (B (ψ r)) * star (B (ψ s))))
        + (-∑ r, ∑ s, ((a r s : ℝ) : ℂ) • (B (ψ r) * B (ψ s)))
        + ((n : ℂ) • (1 : A) - ∑ s, star (B (ψ s)) * B (ψ s)) := by
        rw [hP3, hP5, ← Finset.sum_smul, hP4]
    _ = diracQuadratic B ψ a + (n : ℂ) • (1 : A) := by
        unfold diracQuadratic
        abel

/-- **The sea vacuum is an exact eigenvector**: if `ζ_p·Y = 0` for all `p` (Dirac's
Eq. 14 conditions, consistent by `seaModes_anticommute`), then

`2H·Y = −n·Y` —

the sea vacuum has energy `−n/2`: finite for every finite model, Dirac's
*"infinite constant"* as `n → ∞`; after discarding it, `H|Y⟩ = 0` — *"the constant
vector `|Y⟩` is a solution of the Schrödinger equation"* — while `|S⟩` (on which
`H²` diverges, `deadwood_coefficient`) is not. -/
theorem seaVacuum_eigenvector [StarModule ℂ A] [SMulCommClass ℂ A A]
    [IsScalarTower ℂ A A] {B : K → A} {ψ : Fin n → K} (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0)
    {Y : A} (hY : ∀ p, seaMode B ψ a p * Y = 0) :
    diracQuadratic B ψ a * Y = -((n : ℂ) • Y) := by
  have hzero : (∑ p, star (seaMode B ψ a p) * seaMode B ψ a p) * Y = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [mul_assoc, hY p, mul_zero]
  rw [hamiltonian_normalOrdered hB hON a hanti hsq, add_mul, smul_mul_assoc,
    one_mul] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-! ### The Heisenberg flow: the solution "leads to no infinities"

Dirac solves the Heisenberg equations `iℏη̇_r = −a_{rp}η*_p`, `iℏη̇*_r = a_{rp}η_p`
of the model exactly: with `a² = −1`, `ℏ²η̈_r = −η_r` and
`η_r(t) = cos(t/ℏ)η_r(0) + i·sin(t/ℏ)a_{rs}η*_s(0)` — globally defined, bounded
trigonometric coefficients on the initial operators: *"the solution of the
Heisenberg equations of motion leads to no infinities"* — the good-picture half of
the dead-wood argument, complementing the `|S⟩`-divergence.  The mode dynamics is
linear, so it is verified on any normed `ℂ`-module of initial data. -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- **Dirac's oscillating-mode ansatz**:
`η_r(t) = cos(t/ℏ)·η_r(0) + i·sin(t/ℏ)·Σ_s a_{rs}η*_s(0)`. -/
noncomputable def heisenbergMode (η ηs : Fin n → W) (a : Fin n → Fin n → ℝ)
    (hbar : ℝ) (r : Fin n) (t : ℝ) : W :=
  ((Real.cos (t / hbar) : ℝ) : ℂ) • η r
    + (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ)) • ∑ s, ((a r s : ℝ) : ℂ) • ηs s

/-- **The ansatz is differentiable with the expected derivative** — the calculus
half of Dirac's solution. -/
theorem heisenbergMode_hasDerivAt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (η ηs : Fin n → V) (a : Fin n → Fin n → ℝ)
    (hbar : ℝ) (r : Fin n) (t : ℝ) :
    HasDerivAt (heisenbergMode η ηs a hbar r)
      (((-Real.sin (t / hbar) * (1 / hbar) : ℝ) : ℂ) • η r
        + (Complex.I * ((Real.cos (t / hbar) * (1 / hbar) : ℝ) : ℂ))
            • ∑ s, ((a r s : ℝ) : ℂ) • ηs s) t := by
  unfold heisenbergMode
  have h1 : HasDerivAt (fun t : ℝ => t / hbar) (1 / hbar) t := by
    simpa using (hasDerivAt_id t).div_const hbar
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (t / hbar))
      (-Real.sin (t / hbar) * (1 / hbar)) t := (Real.hasDerivAt_cos _).comp t h1
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (t / hbar))
      (Real.cos (t / hbar) * (1 / hbar)) t := (Real.hasDerivAt_sin _).comp t h1
  exact ((hcos.ofReal_comp).smul_const (η r)).add
    (((hsin.ofReal_comp).const_mul Complex.I).smul_const _)

/-- **The ansatz solves Dirac's Heisenberg equation** `iℏ·η̇_r = −Σ_s a_{rs}η*_s(t)`
(with `η*_s(t) = cos(t/ℏ)η*_s(0) − i·sin(t/ℏ)a_{sq}η_q(0)` the conjugate-mode
flow): the `a² = −1` contraction closes the system, so the exact solution exists
globally with bounded coefficients — *"the solution of the Heisenberg equations of
motion leads to no infinities."* -/
theorem heisenbergMode_solves (η ηs : Fin n → W) (a : Fin n → Fin n → ℝ)
    (hbar : ℝ) (hh : hbar ≠ 0)
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) (r : Fin n)
    (t : ℝ) :
    (Complex.I * (hbar : ℂ))
        • (((-Real.sin (t / hbar) * (1 / hbar) : ℝ) : ℂ) • η r
          + (Complex.I * ((Real.cos (t / hbar) * (1 / hbar) : ℝ) : ℂ))
              • ∑ s, ((a r s : ℝ) : ℂ) • ηs s)
      = -∑ s, ((a r s : ℝ) : ℂ)
          • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s
            - (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
                • ∑ q, ((a s q : ℝ) : ℂ) • η q) := by
  have hb : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hbb : (hbar : ℂ) * (1 / (hbar : ℂ)) = 1 := by field_simp
  have hIh1 : (Complex.I * (hbar : ℂ)) * ((-Real.sin (t / hbar) * (1 / hbar) : ℝ) : ℂ)
      = -(Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one]
    linear_combination (-(Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))) * hbb
  have hIh2 : (Complex.I * (hbar : ℂ))
        * (Complex.I * ((Real.cos (t / hbar) * (1 / hbar) : ℝ) : ℂ))
      = -((Real.cos (t / hbar) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    linear_combination (((Real.cos (t / hbar) : ℝ) : ℂ) * (hbar : ℂ) * (1 / (hbar : ℂ)))
        * Complex.I_mul_I + (-((Real.cos (t / hbar) : ℝ) : ℂ)) * hbb
  have hcollapse : (∑ s, ((a r s : ℝ) : ℂ) • ∑ q, ((a s q : ℝ) : ℂ) • η q)
      = -η r := by
    calc ∑ s, ((a r s : ℝ) : ℂ) • ∑ q, ((a s q : ℝ) : ℂ) • η q
        = ∑ s, ∑ q, (((a r s : ℝ) : ℂ) * ((a s q : ℝ) : ℂ)) • η q := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun q _ => smul_smul _ _ _
      _ = ∑ q, ∑ s, (((a r s : ℝ) : ℂ) * ((a s q : ℝ) : ℂ)) • η q :=
          Finset.sum_comm
      _ = ∑ q, (∑ s, ((a r s : ℝ) : ℂ) * ((a s q : ℝ) : ℂ)) • η q :=
          Finset.sum_congr rfl fun q _ => (Finset.sum_smul).symm
      _ = ∑ q, ((if r = q then (-1 : ℂ) else 0)) • η q := by
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 1
          have hcast : (∑ s, ((a r s : ℝ) : ℂ) * ((a s q : ℝ) : ℂ))
              = ((∑ s, a r s * a s q : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [hcast, hsq r q]
          by_cases h : r = q <;> simp [h]
      _ = -η r := by
          simp [ite_smul]
  calc (Complex.I * (hbar : ℂ))
        • (((-Real.sin (t / hbar) * (1 / hbar) : ℝ) : ℂ) • η r
          + (Complex.I * ((Real.cos (t / hbar) * (1 / hbar) : ℝ) : ℂ))
              • ∑ s, ((a r s : ℝ) : ℂ) • ηs s)
      = (-(Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))) • η r
        + (-((Real.cos (t / hbar) : ℝ) : ℂ))
            • ∑ s, ((a r s : ℝ) : ℂ) • ηs s := by
        rw [smul_add, smul_smul, smul_smul, hIh1, hIh2]
    _ = -(((Real.cos (t / hbar) : ℝ) : ℂ) • ∑ s, ((a r s : ℝ) : ℂ) • ηs s)
        - (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ)) • η r := by
        rw [neg_smul, neg_smul]
        abel
    _ = -(((Real.cos (t / hbar) : ℝ) : ℂ) • ∑ s, ((a r s : ℝ) : ℂ) • ηs s)
        + (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
            • ∑ s, ((a r s : ℝ) : ℂ) • ∑ q, ((a s q : ℝ) : ℂ) • η q := by
        rw [hcollapse, smul_neg]
        abel
    _ = -(∑ s, ((a r s : ℝ) : ℂ) • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s))
        + ∑ s, ((a r s : ℝ) : ℂ)
            • ((Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
              • ∑ q, ((a s q : ℝ) : ℂ) • η q) := by
        rw [show (((Real.cos (t / hbar) : ℝ) : ℂ) • ∑ s, ((a r s : ℝ) : ℂ) • ηs s)
            = ∑ s, ((a r s : ℝ) : ℂ) • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s) by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _]
        rw [show ((Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
              • ∑ s, ((a r s : ℝ) : ℂ) • ∑ q, ((a s q : ℝ) : ℂ) • η q)
            = ∑ s, ((a r s : ℝ) : ℂ)
                • ((Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
                  • ∑ q, ((a s q : ℝ) : ℂ) • η q) by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _]
    _ = -∑ s, ((a r s : ℝ) : ℂ)
          • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s
            - (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
                • ∑ q, ((a s q : ℝ) : ℂ) • η q) := by
        have h1 : (∑ s, ((a r s : ℝ) : ℂ)
              • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s
                - (Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
                    • ∑ q, ((a s q : ℝ) : ℂ) • η q))
            = (∑ s, ((a r s : ℝ) : ℂ) • (((Real.cos (t / hbar) : ℝ) : ℂ) • ηs s))
              - ∑ s, ((a r s : ℝ) : ℂ)
                  • ((Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ))
                    • ∑ q, ((a s q : ℝ) : ℂ) • η q) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ => smul_sub _ _ _
        rw [h1, neg_sub]
        abel

/-! ### Welds: the Bogoliubov CAR, evenness, and the flow automorphism

Linking the dead-wood model to the rest of the arc: the sea modes form a
(`√2`-normalized) CAR family — the fermionic Bogoliubov weld to
`Bogoliubov.CARAlgebraAutomorphism`; the model *requires* an even mode number (the
determinant obstruction); and the Heisenberg flow preserves the anticommutation
relations — time evolution is a CAR automorphism, the dynamical face of
`bogoliubov_preserves_CAR`. -/

/-- **Row orthogonality**: `Σ_s a_{rs}a_{ps} = δ_{rp}` (`a·aᵀ = 1`) — the mirror of
`column_orthogonality`. -/
theorem row_orthogonality {n : ℕ} (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) (r p : Fin n) :
    ∑ s, a r s * a p s = if r = p then 1 else 0 := by
  have h1 : ∑ s, a r s * a p s = -(∑ s, a r s * a s p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hanti p s]
    ring
  rw [h1, hsq r p]
  by_cases h : r = p <;> simp [h]

/-- **Dirac's model requires an even number of modes**: a real antisymmetric `a`
with `a² = −1` forces `det(a)² = (−1)ⁿ`, impossible for odd `n` — the mode space
carries a complex structure, so it is even-dimensional (the pairing behind the
`±i`-symmetric spectrum and the two-vacuum structure). -/
theorem deadwood_modes_even {n : ℕ} (a : Fin n → Fin n → ℝ)
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) :
    Even n := by
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of a with hA
  have hA2 : A * A = -1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [hA, Matrix.of_apply, Matrix.neg_apply, Matrix.one_apply]
    rw [hsq i j]
    by_cases h : i = j <;> simp [h]
  have hdet : (A.det) ^ 2 = (-1 : ℝ) ^ n := by
    have h := congrArg Matrix.det hA2
    rw [Matrix.det_mul, ← sq] at h
    rw [h, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [Odd.neg_one_pow hodd] at hdet
  nlinarith [sq_nonneg A.det]

section BogoliubovWelds

variable [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] {n : ℕ} {B : K → A}
  {ψ : Fin n → K}

/-- Bare modes anticommute with bare-mode sums: `{B_r, Σ_q c_q·B_q} = 0`. -/
private theorem bare_bareSum_anticommute (hB : IsCAR B) (c : Fin n → ℂ) (r : Fin n) :
    B (ψ r) * (∑ q, c q • B (ψ q)) + (∑ q, c q • B (ψ q)) * B (ψ r) = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hB.2, smul_zero]

/-- Starred modes contract against bare-mode sums:
`{B*_r, Σ_q c_q·B_q} = c_r·1`. -/
private theorem star_bareSum_contraction (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (c : Fin n → ℂ) (r : Fin n) :
    star (B (ψ r)) * (∑ q, c q • B (ψ q)) + (∑ q, c q • B (ψ q)) * star (B (ψ r))
      = c r • (1 : A) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  calc ∑ q, (star (B (ψ r)) * (c q • B (ψ q)) + (c q • B (ψ q)) * star (B (ψ r)))
      = ∑ q, c q • ((if q = r then 1 else 0 : ℂ) • (1 : A)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm, hB.1, hON]
    _ = ∑ q, (if q = r then c q else 0) • (1 : A) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul, mul_ite, mul_one, mul_zero]
    _ = c r • (1 : A) := by
        simp [ite_smul]

/-- Two bare-mode sums anticommute: `{Σ_s c_s·B_s, Σ_q d_q·B_q} = 0`. -/
private theorem bare_sums_anticommute (hB : IsCAR B) (c d : Fin n → ℂ) :
    (∑ s, c s • B (ψ s)) * (∑ q, d q • B (ψ q))
        + (∑ q, d q • B (ψ q)) * (∑ s, c s • B (ψ s)) = 0 := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ q, ∑ s, (d q • B (ψ q)) * (c s • B (ψ s)))
      = ∑ s, ∑ q, (d q • B (ψ q)) * (c s • B (ψ s)) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (d q) (c s), ← smul_add,
    hB.2, smul_zero]

/-- Starred-mode sums contract against bare-mode sums:
`{Σ_s c_s·B*_s, Σ_q d_q·B_q} = (Σ_s c_s d_s)·1`. -/
private theorem starredSum_bareSum_contraction (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (c d : Fin n → ℂ) :
    (∑ s, c s • star (B (ψ s))) * (∑ q, d q • B (ψ q))
        + (∑ q, d q • B (ψ q)) * (∑ s, c s • star (B (ψ s)))
      = (∑ s, c s * d s) • (1 : A) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ q, ∑ s, (d q • B (ψ q)) * (c s • star (B (ψ s))))
      = ∑ s, ∑ q, (d q • B (ψ q)) * (c s • star (B (ψ s))) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  calc ∑ s, ((∑ q, (c s • star (B (ψ s))) * (d q • B (ψ q)))
        + ∑ q, (d q • B (ψ q)) * (c s • star (B (ψ s))))
      = ∑ s, ∑ q, (c s * d q)
          • (star (B (ψ s)) * B (ψ q) + B (ψ q) * star (B (ψ s))) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (d q) (c s), ← smul_add]
    _ = ∑ s, ∑ q, (if q = s then c s * d q else 0) • (1 : A) := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
        rw [add_comm, hB.1, hON, smul_smul, mul_ite, mul_one, mul_zero]
    _ = ∑ s, (c s * d s) • (1 : A) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp [ite_smul]
    _ = (∑ s, c s * d s) • (1 : A) := (Finset.sum_smul).symm

/-- **The sea modes are a `√2`-normalized CAR family**: `{ζ_r, ζ*_p} = 2δ_{rp}·1` —
together with `seaModes_anticommute` this exhibits Dirac's Eq. 14 shift as a
fermionic **Bogoliubov transformation** of the bare modes (the anomalous
particle-hole mixing beyond the unitary case of
`Bogoliubov.CARAlgebraAutomorphism.bogoliubov_preserves_CAR`): the sea vacuum is
the Fock vacuum of the canonically rescaled modes `ζ/√2`. -/
theorem seaModes_car [StarModule ℂ A] (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r))
    (hsq : ∀ r q, ∑ p, a r p * a p q = if r = q then -1 else 0) (r p : Fin n) :
    seaMode B ψ a r * star (seaMode B ψ a p)
        + star (seaMode B ψ a p) * seaMode B ψ a r
      = ((if r = p then 2 else 0 : ℂ)) • (1 : A) := by
  rw [star_seaMode]
  unfold seaMode
  have key : (B (ψ r) + ∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
        * (star (B (ψ p)) + ∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
      + (star (B (ψ p)) + ∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
        * (B (ψ r) + ∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
      = (B (ψ r) * star (B (ψ p)) + star (B (ψ p)) * B (ψ r))
        + (B (ψ r) * (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
            + (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s)) * B (ψ r))
        + (star (B (ψ p)) * (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
            + (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s))) * star (B (ψ p)))
        + ((∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
              * (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
            + (∑ s, ((a p s : ℝ) : ℂ) • B (ψ s))
              * (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))) := by
    noncomm_ring
  rw [key, hB.1, hON, bare_bareSum_anticommute hB,
    starredSum_bareSum_contraction hB hON]
  have hstar : star (B (ψ p)) * (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s)))
      + (∑ s, ((a r s : ℝ) : ℂ) • star (B (ψ s))) * star (B (ψ p)) = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm,
      ext_anticomm_zero hB, smul_zero]
  rw [hstar, add_zero, add_zero]
  have hrow : (∑ s, ((a r s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ))
      = ((if r = p then 1 else 0 : ℂ)) := by
    have hcast : (∑ s, ((a r s : ℝ) : ℂ) * ((a p s : ℝ) : ℂ))
        = ((∑ s, a r s * a p s : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, row_orthogonality a hanti hsq r p]
    by_cases h : r = p <;> simp [h]
  rw [hrow, ← add_smul]
  congr 1
  by_cases h : r = p <;> simp [h]
  norm_num

/-- **The Heisenberg flow preserves the anticommutation relations**: at every time
`t`, the evolved emission modes `η_r(t)` still pairwise anticommute — Dirac's exact
time evolution is a **CAR automorphism** (a Bogoliubov transformation at each
instant, the dynamical face of `bogoliubov_preserves_CAR`), again precisely because
`a` is antisymmetric. -/
theorem heisenbergFlow_preserves_anticommute [StarModule ℂ A] (hB : IsCAR B)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (a : Fin n → Fin n → ℝ) (hanti : ∀ r s, a r s = -(a s r))
    (hbar t : ℝ) (r p : Fin n) :
    heisenbergMode (fun i => star (B (ψ i))) (fun i => B (ψ i)) a hbar r t
        * heisenbergMode (fun i => star (B (ψ i))) (fun i => B (ψ i)) a hbar p t
      + heisenbergMode (fun i => star (B (ψ i))) (fun i => B (ψ i)) a hbar p t
        * heisenbergMode (fun i => star (B (ψ i))) (fun i => B (ψ i)) a hbar r t
      = 0 := by
  unfold heisenbergMode
  set cc : ℂ := ((Real.cos (t / hbar) : ℝ) : ℂ) with hcc
  set ss : ℂ := Complex.I * ((Real.sin (t / hbar) : ℝ) : ℂ) with hss
  set e : Fin n → A := fun i => star (B (ψ i)) with he
  set b : Fin n → A := fun i => B (ψ i) with hb
  have key : (cc • e r + ss • ∑ s, ((a r s : ℝ) : ℂ) • b s)
        * (cc • e p + ss • ∑ s, ((a p s : ℝ) : ℂ) • b s)
      + (cc • e p + ss • ∑ s, ((a p s : ℝ) : ℂ) • b s)
        * (cc • e r + ss • ∑ s, ((a r s : ℝ) : ℂ) • b s)
      = (cc * cc) • (e r * e p + e p * e r)
        + (cc * ss) • ((e r * ∑ s, ((a p s : ℝ) : ℂ) • b s)
            + (∑ s, ((a p s : ℝ) : ℂ) • b s) * e r)
        + (cc * ss) • ((e p * ∑ s, ((a r s : ℝ) : ℂ) • b s)
            + (∑ s, ((a r s : ℝ) : ℂ) • b s) * e p)
        + (ss * ss) • ((∑ s, ((a r s : ℝ) : ℂ) • b s)
              * (∑ s, ((a p s : ℝ) : ℂ) • b s)
            + (∑ s, ((a p s : ℝ) : ℂ) • b s) * (∑ s, ((a r s : ℝ) : ℂ) • b s)) := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, smul_add]
    rw [mul_comm ss cc]
    abel
  rw [key]
  have hee : e r * e p + e p * e r = 0 := ext_anticomm_zero hB _ _
  have h1 : e r * (∑ s, ((a p s : ℝ) : ℂ) • b s)
      + (∑ s, ((a p s : ℝ) : ℂ) • b s) * e r = ((a p r : ℝ) : ℂ) • (1 : A) :=
    star_bareSum_contraction hB hON _ r
  have h2 : e p * (∑ s, ((a r s : ℝ) : ℂ) • b s)
      + (∑ s, ((a r s : ℝ) : ℂ) • b s) * e p = ((a r p : ℝ) : ℂ) • (1 : A) :=
    star_bareSum_contraction hB hON _ p
  have h4 : (∑ s, ((a r s : ℝ) : ℂ) • b s) * (∑ s, ((a p s : ℝ) : ℂ) • b s)
      + (∑ s, ((a p s : ℝ) : ℂ) • b s) * (∑ s, ((a r s : ℝ) : ℂ) • b s) = 0 :=
    bare_sums_anticommute hB _ _
  have hzero : cc * ss * ((a p r : ℝ) : ℂ) + cc * ss * ((a r p : ℝ) : ℂ) = 0 := by
    rw [hanti p r]
    push_cast
    ring
  rw [hee, h1, h2, h4, smul_zero, smul_zero, smul_smul, smul_smul, zero_add,
    add_zero, ← add_smul, hzero, zero_smul]

end BogoliubovWelds

/-! ### The interaction-picture `K`-recursion (Dirac's Eqs 15–18)

Dirac's constants of the motion `K` (`iℏdK/dt = iℏ∂K/∂t + KH − HK = 0`, Eq. 15) are
computed in the interaction representation: with `H = H₀ + V`, every `q`-number is
transformed to `ξ† = e^{iH₀t/ℏ}·ξ·e^{−iH₀t/ℏ}`; the transform of a constant of the
motion satisfies `iℏ∂K†/∂t = V†K† − K†V†` (Eq. 16), solved perturbatively by
`∂K†⁽⁰⁾/∂t = 0` and `iℏ∂K†⁽ⁿ⁺¹⁾/∂t = V†K†⁽ⁿ⁾ − K†⁽ⁿ⁾V†` (Eqs 17–18) — the scheme
behind Dirac's Heisenberg-picture calculation of the anomalous magnetic moment and
the Lamb shift.  The frame calculus runs on Mathlib's `NormedSpace.exp`; the
Hilbert-space pictures are `FiniteTarget.QIFHeisenbergPicture` and
`FiniteTarget.Basic.timeEvolution`.  The carrier takes `NormedAlgebra ℚ 𝒜`
explicitly: every complex Banach algebra is one (ℚ acts through ℂ), but Mathlib's
`exp_add_of_commute` is stated over ℚ-algebras and the general instance is absent
on this pin. -/

section InteractionPicture

open NormedSpace

variable {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜] [NormedAlgebra ℚ 𝒜]
  [CompleteSpace 𝒜]

/-- The interaction-frame generator `m = iH₀/ℏ`. -/
noncomputable def interactionGenerator (H₀ : 𝒜) (hbar : ℝ) : 𝒜 :=
  (Complex.I * ((hbar : ℂ))⁻¹) • H₀

/-- The interaction frame `U(t) = e^{iH₀t/ℏ}`. -/
noncomputable def interactionFrame (H₀ : 𝒜) (hbar t : ℝ) : 𝒜 :=
  exp ((t : ℂ) • interactionGenerator H₀ hbar)

/-- The inverse interaction frame `W(t) = e^{−iH₀t/ℏ}`. -/
noncomputable def interactionFrameInv (H₀ : 𝒜) (hbar t : ℝ) : 𝒜 :=
  exp ((t : ℂ) • -interactionGenerator H₀ hbar)

/-- The frame and its inverse multiply to one, in both orders. -/
theorem interactionFrame_mul_inv (H₀ : 𝒜) (hbar t : ℝ) :
    interactionFrame H₀ hbar t * interactionFrameInv H₀ hbar t = 1
      ∧ interactionFrameInv H₀ hbar t * interactionFrame H₀ hbar t = 1 := by
  unfold interactionFrame interactionFrameInv
  constructor
  · rw [smul_neg, ← exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel,
      exp_zero]
  · rw [smul_neg, ← exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel,
      exp_zero]

omit [NormedAlgebra ℚ 𝒜] [CompleteSpace 𝒜] in
/-- `H₀` commutes with both frames. -/
theorem interactionFrame_commute (H₀ : 𝒜) (hbar t : ℝ) :
    Commute H₀ (interactionFrame H₀ hbar t)
      ∧ Commute H₀ (interactionFrameInv H₀ hbar t) := by
  unfold interactionFrame interactionFrameInv interactionGenerator
  exact ⟨(((Commute.refl H₀).smul_right _).smul_right _).exp_right,
    ((((Commute.refl H₀).smul_right _).neg_right).smul_right _).exp_right⟩

omit [NormedAlgebra ℚ 𝒜] in
/-- **The interaction-picture derivative** (the display before Dirac's Eq. 16):
`ξ†(t) = U(t)·ξ(t)·W(t)` is differentiable with the frame generator acting from
both sides. -/
theorem interactionPicture_hasDerivAt (H₀ : 𝒜) (hbar : ℝ) (ξ : ℝ → 𝒜) (ξ' : 𝒜)
    (t : ℝ) (hξ : HasDerivAt ξ ξ' t) :
    HasDerivAt
      (fun u => interactionFrame H₀ hbar u * ξ u * interactionFrameInv H₀ hbar u)
      (interactionGenerator H₀ hbar
          * (interactionFrame H₀ hbar t * ξ t * interactionFrameInv H₀ hbar t)
        + interactionFrame H₀ hbar t * ξ' * interactionFrameInv H₀ hbar t
        - (interactionFrame H₀ hbar t * ξ t * interactionFrameInv H₀ hbar t)
            * interactionGenerator H₀ hbar) t := by
  unfold interactionFrame interactionFrameInv
  set m := interactionGenerator H₀ hbar with hm
  have hc : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hU : HasDerivAt (fun u : ℝ => exp ((u : ℂ) • m)) (m * exp ((t : ℂ) • m)) t := by
    simpa [Function.comp_def] using
      HasDerivAt.scomp t (hasDerivAt_exp_smul_const' (𝕂 := ℂ) m (t : ℂ)) hc
  have hW : HasDerivAt (fun u : ℝ => exp ((u : ℂ) • -m))
      (exp ((t : ℂ) • -m) * -m) t := by
    simpa [Function.comp_def] using
      HasDerivAt.scomp t (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-m) (t : ℂ)) hc
  have h1 := (hU.mul hξ).mul hW
  have hEq : m * (exp ((t : ℂ) • m) * ξ t * exp ((t : ℂ) • -m))
        + exp ((t : ℂ) • m) * ξ' * exp ((t : ℂ) • -m)
        - (exp ((t : ℂ) • m) * ξ t * exp ((t : ℂ) • -m)) * m
      = (m * exp ((t : ℂ) • m) * ξ t + exp ((t : ℂ) • m) * ξ')
          * exp ((t : ℂ) • -m)
        + exp ((t : ℂ) • m) * ξ t * (exp ((t : ℂ) • -m) * -m) := by
    noncomm_ring
  rw [hEq]
  exact h1

omit [NormedAlgebra ℚ 𝒜] [CompleteSpace 𝒜] in
/-- **Dirac's interaction-picture identity**:
`iℏ·∂ξ†/∂t = e^{iH₀t/ℏ}(iℏ·∂ξ/∂t − H₀ξ + ξH₀)e^{−iH₀t/ℏ}` — the frame derivative
packaged with `iℏ·m = −H₀` and the frame–`H₀` commutation. -/
theorem interactionPicture_dirac_identity (H₀ : 𝒜) (hbar : ℝ) (hh : hbar ≠ 0)
    (ξ : ℝ → 𝒜) (ξ' : 𝒜) (t : ℝ) :
    (Complex.I * (hbar : ℂ))
        • (interactionGenerator H₀ hbar
            * (interactionFrame H₀ hbar t * ξ t * interactionFrameInv H₀ hbar t)
          + interactionFrame H₀ hbar t * ξ' * interactionFrameInv H₀ hbar t
          - (interactionFrame H₀ hbar t * ξ t * interactionFrameInv H₀ hbar t)
              * interactionGenerator H₀ hbar)
      = interactionFrame H₀ hbar t
          * ((Complex.I * (hbar : ℂ)) • ξ' - H₀ * ξ t + ξ t * H₀)
          * interactionFrameInv H₀ hbar t := by
  have hb : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hmH : (Complex.I * (hbar : ℂ)) • interactionGenerator H₀ hbar = -H₀ := by
    unfold interactionGenerator
    rw [smul_smul]
    have hsc : Complex.I * (hbar : ℂ) * (Complex.I * ((hbar : ℂ))⁻¹) = -1 := by
      have h1 : Complex.I * (hbar : ℂ) * (Complex.I * ((hbar : ℂ))⁻¹)
          = (Complex.I * Complex.I) * ((hbar : ℂ) * ((hbar : ℂ))⁻¹) := by ring
      rw [h1, Complex.I_mul_I, mul_inv_cancel₀ hb]
      ring
    rw [hsc, neg_one_smul]
  set U := interactionFrame H₀ hbar t
  set W := interactionFrameInv H₀ hbar t
  have hUH : H₀ * U = U * H₀ := (interactionFrame_commute H₀ hbar t).1.eq
  have hWH : H₀ * W = W * H₀ := (interactionFrame_commute H₀ hbar t).2.eq
  have hL1 : (Complex.I * (hbar : ℂ)) • (interactionGenerator H₀ hbar * (U * ξ t * W))
      = -(U * (H₀ * ξ t) * W) := by
    rw [← smul_mul_assoc, hmH]
    calc -H₀ * (U * ξ t * W) = -(H₀ * U * (ξ t * W)) := by noncomm_ring
      _ = -(U * H₀ * (ξ t * W)) := by rw [hUH]
      _ = -(U * (H₀ * ξ t) * W) := by noncomm_ring
  have hL3 : (Complex.I * (hbar : ℂ)) • ((U * ξ t * W) * interactionGenerator H₀ hbar)
      = -(U * (ξ t * H₀) * W) := by
    rw [← mul_smul_comm, hmH]
    calc U * ξ t * W * -H₀ = -(U * ξ t * (W * H₀)) := by noncomm_ring
      _ = -(U * ξ t * (H₀ * W)) := by rw [← hWH]
      _ = -(U * (ξ t * H₀) * W) := by noncomm_ring
  have hL2 : (Complex.I * (hbar : ℂ)) • (U * ξ' * W)
      = U * ((Complex.I * (hbar : ℂ)) • ξ') * W := by
    rw [← smul_mul_assoc, ← mul_smul_comm]
  rw [smul_sub, smul_add, hL1, hL2, hL3]
  noncomm_ring

/-- **Dirac's Eq. 16**: for a constant of the motion —
`iℏ·∂K/∂t = HK − KH` with `H = H₀ + V` — the interaction transform satisfies
`iℏ·∂K†/∂t = V†K† − K†V†`: only the interaction survives in the frame. -/
theorem constantOfMotion_interaction (H₀ Vop : 𝒜) (hbar : ℝ)
    (K : ℝ → 𝒜) (K' : 𝒜) (t : ℝ)
    (hmotion : (Complex.I * (hbar : ℂ)) • K'
      = (H₀ + Vop) * K t - K t * (H₀ + Vop)) :
    interactionFrame H₀ hbar t
        * ((Complex.I * (hbar : ℂ)) • K' - H₀ * K t + K t * H₀)
        * interactionFrameInv H₀ hbar t
      = (interactionFrame H₀ hbar t * Vop * interactionFrameInv H₀ hbar t)
          * (interactionFrame H₀ hbar t * K t * interactionFrameInv H₀ hbar t)
        - (interactionFrame H₀ hbar t * K t * interactionFrameInv H₀ hbar t)
          * (interactionFrame H₀ hbar t * Vop * interactionFrameInv H₀ hbar t) := by
  set U := interactionFrame H₀ hbar t
  set W := interactionFrameInv H₀ hbar t
  have hWU : W * U = 1 := (interactionFrame_mul_inv H₀ hbar t).2
  have hstep : (Complex.I * (hbar : ℂ)) • K' - H₀ * K t + K t * H₀
      = Vop * K t - K t * Vop := by
    rw [hmotion]
    noncomm_ring
  rw [hstep]
  have h1 : (U * Vop * W) * (U * K t * W) = U * (Vop * K t) * W := by
    calc (U * Vop * W) * (U * K t * W) = U * Vop * (W * U) * (K t * W) := by
          noncomm_ring
      _ = U * (Vop * K t) * W := by rw [hWU]; noncomm_ring
  have h2 : (U * K t * W) * (U * Vop * W) = U * (K t * Vop) * W := by
    calc (U * K t * W) * (U * Vop * W) = U * K t * (W * U) * (Vop * W) := by
          noncomm_ring
      _ = U * (K t * Vop) * W := by rw [hWU]; noncomm_ring
  rw [h1, h2]
  noncomm_ring

/-- **The perturbative `K`-recursion telescopes** (Dirac's Eqs 17–18): with
`∂K†⁽⁰⁾/∂t = 0` and `iℏ·∂K†⁽ⁿ⁺¹⁾/∂t = V†K†⁽ⁿ⁾ − K†⁽ⁿ⁾V†`, the partial sums of the
hierarchy satisfy Eq. 16 order by order:
`iℏ·∂(Σ_{k≤n+1}K†⁽ᵏ⁾)/∂t = V†(Σ_{k≤n}K†⁽ᵏ⁾) − (Σ_{k≤n}K†⁽ᵏ⁾)V†` — successive
integrations build the constant of the motion to any order in `e²/ℏc`. -/
theorem kRecursion_telescopes {R : Type*} [Ring R] [Module ℂ R]
    (c : ℂ) (Vd : R) (D Kf : ℕ → R) (hD0 : D 0 = 0)
    (hrec : ∀ k, c • D (k + 1) = Vd * Kf k - Kf k * Vd) (n : ℕ) :
    c • (∑ k ∈ Finset.range (n + 2), D k)
      = Vd * (∑ k ∈ Finset.range (n + 1), Kf k)
        - (∑ k ∈ Finset.range (n + 1), Kf k) * Vd := by
  rw [Finset.sum_range_succ', hD0, add_zero, Finset.smul_sum,
    Finset.sum_congr rfl fun k _ => hrec k, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]

end InteractionPicture

/-! ## §F — Aastrup-Grimstrup 2008: Chern-Simons phase and Bott oscillator algebra -/

/-! ### §F.1 — The doubled Chern-Simons ground state -/

/-- The real two-sector ground-state column of Aastrup-Grimstrup 2008 Eq. (47):
`(cos(CS/(2τ₂)), sin(CS/(2τ₂))) · exp(-S/τ₂)`. The two entries encode the doubled
CAR representation used to make the Chern-Simons phase compatible with both
`Bα` and `Bα*`. -/
noncomputable def doubledChernSimonsGroundState (tau2 S CS : ℝ) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then Real.cos (CS / (2 * tau2)) * Real.exp (-S / tau2)
    else Real.sin (CS / (2 * tau2)) * Real.exp (-S / tau2)

/-- The first sector is the cosine component of the doubled Chern-Simons state. -/
@[simp]
lemma doubledChernSimonsGroundState_zero (tau2 S CS : ℝ) :
    doubledChernSimonsGroundState tau2 S CS 0 =
      Real.cos (CS / (2 * tau2)) * Real.exp (-S / tau2) := by
  simp [doubledChernSimonsGroundState]

/-- The second sector is the sine component of the doubled Chern-Simons state. -/
@[simp]
lemma doubledChernSimonsGroundState_one (tau2 S CS : ℝ) :
    doubledChernSimonsGroundState tau2 S CS 1 =
      Real.sin (CS / (2 * tau2)) * Real.exp (-S / tau2) := by
  simp [doubledChernSimonsGroundState]

/-- The Chern-Simons phase rotates the two doubled sectors without changing the
common damping factor: the squared sector norm is `exp(-S/τ₂)^2`. This is the
finite algebraic content of replacing `exp(i CS/(2τ₂))` by the real doubled
cosine/sine state in Eq. (47). -/
lemma doubledChernSimonsGroundState_norm_sq (tau2 S CS : ℝ) :
    ∑ i : Fin 2, doubledChernSimonsGroundState tau2 S CS i ^ 2 =
      Real.exp (-S / tau2) ^ 2 := by
  rw [Fin.sum_univ_two]
  simp only [doubledChernSimonsGroundState_zero, doubledChernSimonsGroundState_one]
  have htrig := Real.cos_sq_add_sin_sq (CS / (2 * tau2))
  nlinarith [htrig]

/-! ### §F.2 — The Bott oscillator variables `q` and `q†` -/

/-- The lower Bott oscillator variable of Eq. (34), abstracted to a ring:
`q = ∂S + τ₂ ∂`. -/
def bottOscillatorQ {R : Type*} [Ring R] [SMul ℝ R] (tau2 : ℝ) (d gradS : R) : R :=
  gradS + tau2 • d

/-- The upper Bott oscillator variable of Eq. (34):
`q† = ∂S - τ₂ ∂`. -/
def bottOscillatorQdag {R : Type*} [Ring R] [SMul ℝ R] (tau2 : ℝ) (d gradS : R) : R :=
  gradS - tau2 • d

/-- Adding `q` and `q†` recovers twice the gradient term `∂S`. -/
lemma bottOscillatorQ_add_qdag {R : Type*} [Ring R] [Module ℝ R] (tau2 : ℝ) (d gradS : R) :
    bottOscillatorQ tau2 d gradS + bottOscillatorQdag tau2 d gradS = (2 : ℝ) • gradS := by
  unfold bottOscillatorQ bottOscillatorQdag
  module

/-- Subtracting `q†` from `q` recovers twice the derivative term `τ₂∂`. -/
lemma bottOscillatorQ_sub_qdag {R : Type*} [Ring R] [Module ℝ R] (tau2 : ℝ) (d gradS : R) :
    bottOscillatorQ tau2 d gradS - bottOscillatorQdag tau2 d gradS = (2 * tau2) • d := by
  unfold bottOscillatorQ bottOscillatorQdag
  module

/-- The finite matrix oscillator commutator is the Hessian/derivative commutator term:
`[q,q†] = 2τ₂(∂·∂S - ∂S·∂)`. This is the regulated finite-mode algebraic form of
Eq. (35). -/
lemma bottOscillatorQ_commutator {n : Type*} [Fintype n] [DecidableEq n] (tau2 : ℝ)
    (d gradS : Matrix n n ℂ) :
    bottOscillatorQ tau2 d gradS * bottOscillatorQdag tau2 d gradS
        - bottOscillatorQdag tau2 d gradS * bottOscillatorQ tau2 d gradS
      = ((2 * tau2 : ℝ) : ℂ) • (d * gradS - gradS * d) := by
  ext i j
  simp [bottOscillatorQ, bottOscillatorQdag, Matrix.mul_apply, sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- If the derivative commutes with the action-gradient term, the Bott oscillator
variables commute. This is the finite harmonic-oscillator specialization of Eq. (35). -/
lemma bottOscillatorQ_commutator_zero_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {tau2 : ℝ} {d gradS : Matrix n n ℂ}
    (h : d * gradS = gradS * d) :
    bottOscillatorQ tau2 d gradS * bottOscillatorQdag tau2 d gradS
        - bottOscillatorQdag tau2 d gradS * bottOscillatorQ tau2 d gradS = 0 := by
  rw [bottOscillatorQ_commutator, h, sub_self]
  simp

/-! ### §F.3 — The doubled sector weight -/

/-- Scaling the Chern-Simons off-diagonal sector by `λ` and `λ⁻¹` leaves the product
of the two sector weights unchanged, matching the ambiguity described after Eq. (60). -/
lemma doubledSectorWeight_product_invariant {R : Type*} [Field R] (lam C Ctilde : R)
    (hlam : lam ≠ 0) :
    (lam * C) * (lam⁻¹ * Ctilde) = C * Ctilde := by
  field_simp [hlam]


end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation

end
