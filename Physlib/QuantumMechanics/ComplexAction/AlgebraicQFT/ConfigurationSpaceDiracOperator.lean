/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry

meta import Zil

/-!
# The configuration-space Dirac operator: spin embedding and the square

The remaining exact content of Aastrup–Grimstrup arXiv:2501.00005 §2 (*Metrics on
configuration spaces*) and §4 (*A Dirac operator*), on the carriers of
`ConfigurationSpaceDiracFluctuation` and `ConfigurationSpaceGaugeGeometry`.

## §A — paper §2: the spinor-pair embedding `χ_{(ψ₁,ψ₂)}`

The paper lifts the configuration-space metric from `Ω¹(M,𝔤)` to `Ω¹(M, S ⊕ S)`
through an embedding `χ_{(ψ₁,ψ₂)}` built from two spinors, *"independent of the
two-spinors `ψ₁` and `ψ₂` under certain conditions"*, and requiring `G = SU(2)`. At a
point the embedding sends `X ∈ 𝔰𝔲(2)` to the spinor pair `(Xψ₁, Xψ₂)` — its exact
algebra:

* `columnsInner_eq_trace` — the induced metric of the column embedding is the
  Hilbert–Schmidt trace form: `Σⱼ⟨Xeⱼ, Yeⱼ⟩ = Tr(XᴴY)`.
* `embeddingMetric_spinorPair_invariant` — **the independence of the spinor pair**:
  replacing the pair `(e₁,e₂)` by any unitary rotation `(Ue₁, Ue₂)` leaves the
  induced metric unchanged, `Tr((XU)ᴴ(YU)) = Tr(XᴴY)` — the paper's "certain
  conditions" are exactly that the two spinors form an orthonormal pair.
* `embeddingMetric_faithful` — the embedding is metrically faithful:
  `Tr(XᴴX) = 0 ↔ X = 0` (Mathlib's trace positivity), so `χ` is injective.
* `su2Basis_embeddingMetric` — on the `𝔰𝔲(2)` basis `{iσᵃ}` the embedding metric is
  `Tr((iσᵃ)ᴴ(iσᵇ)) = 2δᵃᵇ`: the Pauli generators are orthogonal with norm `√2` —
  the `SU(2)`-specific input (`𝔤 = 𝔰𝔲(2)` spanned by `iσᵃ`), welded to
  `pauliVec_trace_pair`.

## §B — paper §4: the Dirac operator and its square

`D = diag(D₁, D₂)` with `D₁ = Σᵢ c̄(ψᵢ)∇_{ξᵢ}`, `D₂ = Σᵢ c̄(iψᵢ)∇_{ξᵢ}` (Eq. 4). The
Clifford squares, extracted from the §A anticommutators of
`ConfigurationSpaceDiracFluctuation` by cancelling the `2` (a `ℂ`-module has no
2-torsion):

* `cliffordMul_sq` / `cliffordMulBar_sq` — `c(ψ)² = ⟨ψ,ψ⟩·1`, `c̄(ψ)² = −⟨ψ,ψ⟩·1`;
  on unit vectors `c² = 1`, `c̄² = −1` (`cliffordMul_unit_sq`,
  `cliffordMulBar_unit_sq`).
* `cliffordMul_anticommute` / `cliffordMulBar_anticommute` — on orthogonal vectors
  the multiplications anticommute.
* `cliffordDirac_sq_neg_laplacian` — **the abstract square**: for any family with
  `cᵢ² = −1`, `cᵢcⱼ = −cⱼcᵢ` (`i ≠ j`), commuting derivatives, and derivatives
  commuting with the Clifford elements, `(Σᵢ cᵢ∇ᵢ)² = −Σᵢ∇ᵢ²` — the double sum
  splits over the diagonal (squares) and the off-diagonal (cancelled in swapped
  pairs by an involution).
* `diracOne_sq` / `diracTwo_sq` — the two blocks of Eq. 4: on an orthonormal family
  `{ψᵢ}` (the paper's `ψᵢ = χ(ξᵢ)`), **both** `D₁ = Σc̄(ψᵢ)∇ᵢ` and the twisted
  `D₂ = Σc̄(iψᵢ)∇ᵢ` square to the *same* free Laplacian `−Σᵢ∇ᵢ²` — the
  `−(∇_{ξᵢ})²` term of the paper's `H_YM`, equal in the two diagonal blocks exactly
  as in `D̃² = diag(H_YM + H_f, H_YM + H_f)`. `D₂`'s hypotheses are *derived* from
  `D₁`'s through the twist `c̄(iψ) = i·c(ψ)` and dimension doubling.

The hypotheses `[∇ᵢ, c(ψⱼ)] = 0` are the trivial-geometry condition — precisely the
vanishing of the `Ξ` term (`ConfigurationSpaceGaugeGeometry.xi_commutator_vanishes_iff`);
with a fibered metric the failure of these hypotheses is the `Ξ` correction, and the
`[∇ᵢ, CS]²` and fermionic terms are the fluctuation layer
(`ConfigurationSpaceDiracFluctuation`).

## Honest scope

The affine structure `T𝒜 = 𝒜 × Ω¹(M,𝔤)` of §2 is Mathlib's `AddTorsor` and is not
restated; the embedding is formalized at a point (`𝔰𝔲(2) → S ⊕ S` column algebra),
not as a map of one-form bundles; `∇_{ξᵢ}` are abstract ring elements (the flat
`∂/∂ξᵢ` of the paper's trivial-geometry assumption), not covariant derivatives on
`L²(ℱ)`; the Hilbert space `ℋ = (L²(ℱ) ⊕ L²(ℱ)) ⊗ Λ*Ω¹(M,S⊕S)` itself is the
analytic layer.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2501.00005: §2 (metric, `χ_{(ψ₁,ψ₂)}`), §4
  (Eq. 4, the Dirac operator); arXiv:2410.07290 (the embedding's construction).
* Carriers: `AlgebraicQFT.ConfigurationSpaceDiracFluctuation` (Clifford pair, twist),
  `AlgebraicQFT.ConfigurationSpaceGaugeGeometry` (`pauliVec`, `Ξ`),
  `Bogoliubov.CARAlgebraAutomorphism` (`IsCAR`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator

/-! ## §A — the spinor-pair embedding -/

/-- **The induced metric of the column embedding is the Hilbert–Schmidt trace form**:
`Σⱼ Σᵢ (Xᵢⱼ)* Yᵢⱼ = Tr(XᴴY)` — the inner product of the spinor pairs `(Xe₁, Xe₂)` and
`(Ye₁, Ye₂)` is the trace form on `𝔰𝔲(2) ⊆ M₂(ℂ)`, the lift `⟨·,·⟩_A` of paper §2 at
a point. -/
theorem columnsInner_eq_trace (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ j : Fin 2, ∑ i : Fin 2, star (X i j) * Y i j
      = (X.conjTranspose * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **The embedding metric is independent of the spinor pair** (paper §2: `χ_{(ψ₁,ψ₂)}`
independent of `ψ₁, ψ₂` "under certain conditions"): rotating the pair by any unitary
leaves the induced metric unchanged — the condition is exactly that the pair is
orthonormal. -/
theorem embeddingMetric_spinorPair_invariant (X Y U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U.conjTranspose * U = 1) :
    ((X * U).conjTranspose * (Y * U)).trace = (X.conjTranspose * Y).trace := by
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hassoc : (X * U).conjTranspose * (Y * U)
      = U.conjTranspose * (X.conjTranspose * Y) * U := by
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  rw [hassoc, Matrix.trace_mul_cycle, hU', one_mul]

open scoped ComplexOrder in
/-- **The embedding is metrically faithful**: `Tr(XᴴX) = 0 ↔ X = 0` — the lifted
metric is nondegenerate, so the embedding `χ` is injective. -/
theorem embeddingMetric_faithful (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (X.conjTranspose * X).trace = 0 ↔ X = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- The Pauli matrices are Hermitian: `(σᵃ)ᴴ = σᵃ`. -/
theorem pauliVec_hermitian (a : Fin 3) :
    (pauliVec a).conjTranspose = pauliVec a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliVec, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

/-- **The `𝔰𝔲(2)` basis is orthogonal in the embedding metric**:
`Tr((iσᵃ)ᴴ(iσᵇ)) = 2δᵃᵇ` — the Pauli generators `iσᵃ` of `𝔤 = 𝔰𝔲(2)` (the paper's
`SU(2)` requirement) carry the rescaled Kronecker metric, welding the embedding to
`pauliVec_trace_pair`. -/
theorem su2Basis_embeddingMetric (a b : Fin 3) :
    ((Complex.I • pauliVec a).conjTranspose * (Complex.I • pauliVec b)).trace
      = 2 * (if a = b then 1 else 0) := by
  rw [Matrix.conjTranspose_smul, pauliVec_hermitian, Complex.star_def, Complex.conj_I,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  exact pauliVec_trace_pair a b

/-! ## §B — the Clifford squares and the Dirac operator -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-- `c(ψ)² = ⟨ψ,ψ⟩·1` — the even Clifford square, from the anticommutator by
cancelling the `2` (a `ℂ`-module has no 2-torsion). -/
theorem cliffordMul_sq {B : K → A} (hB : IsCAR B) (ψ : K) :
    cliffordMul B ψ * cliffordMul B ψ = (inner ℂ ψ ψ) • (1 : A) := by
  have h2 : (2 : ℂ) • (cliffordMul B ψ * cliffordMul B ψ)
      = (2 : ℂ) • ((inner ℂ ψ ψ : ℂ) • (1 : A)) := by
    calc (2 : ℂ) • (cliffordMul B ψ * cliffordMul B ψ)
        = cliffordMul B ψ * cliffordMul B ψ + cliffordMul B ψ * cliffordMul B ψ :=
          two_smul ℂ _
      _ = (inner ℂ ψ ψ + inner ℂ ψ ψ) • (1 : A) := cliffordMul_anticomm hB ψ ψ
      _ = (2 : ℂ) • ((inner ℂ ψ ψ : ℂ) • (1 : A)) := by
          rw [← two_mul, mul_smul]
  have hhalf := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
  simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)] using hhalf

/-- `c̄(ψ)² = −⟨ψ,ψ⟩·1` — the odd Clifford square. -/
theorem cliffordMulBar_sq {B : K → A} (hB : IsCAR B) (ψ : K) :
    cliffordMulBar B ψ * cliffordMulBar B ψ = -((inner ℂ ψ ψ) • (1 : A)) := by
  have h2 : (2 : ℂ) • (cliffordMulBar B ψ * cliffordMulBar B ψ)
      = (2 : ℂ) • (-((inner ℂ ψ ψ : ℂ) • (1 : A))) := by
    calc (2 : ℂ) • (cliffordMulBar B ψ * cliffordMulBar B ψ)
        = cliffordMulBar B ψ * cliffordMulBar B ψ
            + cliffordMulBar B ψ * cliffordMulBar B ψ := two_smul ℂ _
      _ = -((inner ℂ ψ ψ + inner ℂ ψ ψ) • (1 : A)) := cliffordMulBar_anticomm hB ψ ψ
      _ = (2 : ℂ) • (-((inner ℂ ψ ψ : ℂ) • (1 : A))) := by
          rw [← two_mul, mul_smul, smul_neg]
  have hhalf := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
  simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)] using hhalf

/-- On a unit vector, `c(ψ)² = 1`. -/
theorem cliffordMul_unit_sq {B : K → A} (hB : IsCAR B) {ψ : K}
    (hψ : inner ℂ ψ ψ = 1) : cliffordMul B ψ * cliffordMul B ψ = 1 := by
  rw [cliffordMul_sq hB, hψ, one_smul]

/-- On a unit vector, `c̄(ψ)² = −1` — the Clifford relation entering the Dirac
square. -/
theorem cliffordMulBar_unit_sq {B : K → A} (hB : IsCAR B) {ψ : K}
    (hψ : inner ℂ ψ ψ = 1) : cliffordMulBar B ψ * cliffordMulBar B ψ = -1 := by
  rw [cliffordMulBar_sq hB, hψ, one_smul]

/-- On orthogonal vectors the even multiplications anticommute. -/
theorem cliffordMul_anticommute {B : K → A} (hB : IsCAR B) {ψ₁ ψ₂ : K}
    (h12 : inner ℂ ψ₁ ψ₂ = 0) :
    cliffordMul B ψ₁ * cliffordMul B ψ₂ = -(cliffordMul B ψ₂ * cliffordMul B ψ₁) := by
  have h21 : inner ℂ ψ₂ ψ₁ = 0 := inner_eq_zero_symm.mp h12
  have h := cliffordMul_anticomm hB ψ₁ ψ₂
  rw [h12, h21, add_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- On orthogonal vectors the odd multiplications anticommute. -/
theorem cliffordMulBar_anticommute {B : K → A} (hB : IsCAR B) {ψ₁ ψ₂ : K}
    (h12 : inner ℂ ψ₁ ψ₂ = 0) :
    cliffordMulBar B ψ₁ * cliffordMulBar B ψ₂
      = -(cliffordMulBar B ψ₂ * cliffordMulBar B ψ₁) := by
  have h21 : inner ℂ ψ₂ ψ₁ = 0 := inner_eq_zero_symm.mp h12
  have h := cliffordMulBar_anticomm hB ψ₁ ψ₂
  rw [h12, h21, add_zero, zero_smul, neg_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **The abstract Dirac square** — for a Clifford family (`cᵢ² = −1`,
`cᵢcⱼ = −cⱼcᵢ` for `i ≠ j`) and commuting derivatives commuting with the Clifford
elements (the trivial-geometry / `Ξ = 0` condition), `(Σᵢ cᵢ∇ᵢ)² = −Σᵢ ∇ᵢ²`: the
diagonal of the double sum contributes the Laplacian through `cᵢ² = −1`, and the
off-diagonal cancels in swapped pairs. -/
theorem cliffordDirac_sq_neg_laplacian {R : Type*} [Ring R] {n : ℕ}
    (c d : Fin n → R)
    (hsq : ∀ i, c i * c i = -1)
    (hanti : ∀ i j, i ≠ j → c i * c j = -(c j * c i))
    (hd : ∀ i j, d i * d j = d j * d i)
    (hcd : ∀ i j, c i * d j = d j * c i) :
    (∑ i, c i * d i) * (∑ i, c i * d i) = -(∑ i, d i * d i) := by
  rw [Finset.sum_mul_sum]
  have hterm : ∀ i j : Fin n,
      (c i * d i) * (c j * d j) = c i * c j * (d i * d j) := by
    intro i j
    calc c i * d i * (c j * d j) = c i * (d i * c j) * d j := by noncomm_ring
      _ = c i * (c j * d i) * d j := by rw [← hcd j i]
      _ = c i * c j * (d i * d j) := by noncomm_ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j,
    ← Finset.sum_product' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin n)))
      (f := fun i j => c i * c j * (d i * d j)),
    ← Finset.diag_union_offDiag (Finset.univ : Finset (Fin n)),
    Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hdiag : ∑ p ∈ (Finset.univ : Finset (Fin n)).diag,
      c p.1 * c p.2 * (d p.1 * d p.2) = -(∑ i, d i * d i) := by
    rw [Finset.sum_diag]
    calc ∑ i, c i * c i * (d i * d i)
        = ∑ i, -(d i * d i) := Finset.sum_congr rfl fun i _ => by
          rw [hsq i]; noncomm_ring
      _ = -(∑ i, d i * d i) := by rw [← Finset.sum_neg_distrib]
  have hoff : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
      c p.1 * c p.2 * (d p.1 * d p.2) = 0 := by
    refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hp
      show c p.1 * c p.2 * (d p.1 * d p.2) + c p.2 * c p.1 * (d p.2 * d p.1) = 0
      rw [hanti p.2 p.1 (Ne.symm hne), hd p.2 p.1, neg_mul, add_neg_cancel]
    · intro p hp _
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hp
      intro hswap
      exact hne ((Prod.ext_iff.mp hswap).2.symm ▸ rfl)
    · intro p hp
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_offDiag.mpr ⟨h2, h1, Ne.symm hne⟩
    · intro p hp
      exact Prod.swap_swap p
  rw [hdiag, hoff, add_zero]

/-- **The first Dirac block squares to the free Laplacian** (paper §4, Eq. 4): on an
orthonormal family `{ψᵢ = χ(ξᵢ)}`, with commuting flat derivatives that commute with
the Clifford elements (trivial geometry, `Ξ = 0`),
`D₁² = (Σᵢ c̄(ψᵢ)∇ᵢ)² = −Σᵢ∇ᵢ²` — the `−(∇_{ξᵢ})²` term of the paper's `H_YM`. -/
theorem diracOne_sq {B : K → A} (hB : IsCAR B) {n : ℕ} (ψ : Fin n → K)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (dv : Fin n → A) (hd : ∀ i j, dv i * dv j = dv j * dv i)
    (hcd : ∀ i j, cliffordMulBar B (ψ i) * dv j = dv j * cliffordMulBar B (ψ i)) :
    (∑ i, cliffordMulBar B (ψ i) * dv i) * (∑ i, cliffordMulBar B (ψ i) * dv i)
      = -(∑ i, dv i * dv i) :=
  cliffordDirac_sq_neg_laplacian _ _
    (fun i => cliffordMulBar_unit_sq hB (by simpa using hON i i))
    (fun i j hij => cliffordMulBar_anticommute hB (by simpa [hij] using hON i j))
    hd hcd

/-- **The twisted Dirac block squares to the same free Laplacian**: the second block
`D₂ = Σᵢ c̄(iψᵢ)∇ᵢ` of paper Eq. 4, whose Clifford family is the *twisted* one, also
satisfies `D₂² = −Σᵢ∇ᵢ²` — its Clifford relations are **derived** from the first
family through the twist `c̄(iψ) = i·c(ψ)` and dimension doubling, so the two diagonal
blocks of `D²` carry the same free Hamiltonian, exactly as in the paper's
`D̃² = diag(H_YM + H_f, H_YM + H_f)`. -/
theorem diracTwo_sq [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    {B : K → A} (hB : IsCAR B)
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) {n : ℕ} (ψ : Fin n → K)
    (hON : ∀ i j, inner ℂ (ψ i) (ψ j) = if i = j then 1 else 0)
    (dv : Fin n → A) (hd : ∀ i j, dv i * dv j = dv j * dv i)
    (hcd : ∀ i j, cliffordMul B (ψ i) * dv j = dv j * cliffordMul B (ψ i)) :
    (∑ i, cliffordMulBar B (Complex.I • ψ i) * dv i)
        * (∑ i, cliffordMulBar B (Complex.I • ψ i) * dv i)
      = -(∑ i, dv i * dv i) := by
  refine cliffordDirac_sq_neg_laplacian _ _ ?_ ?_ hd ?_
  · intro i
    rw [cliffordMulBar_twist hanti, smul_mul_smul_comm, Complex.I_mul_I,
      cliffordMul_unit_sq hB (by simpa using hON i i), neg_smul, one_smul]
  · intro i j hij
    rw [cliffordMulBar_twist hanti, cliffordMulBar_twist hanti, smul_mul_smul_comm,
      smul_mul_smul_comm, cliffordMul_anticommute hB (by simpa [hij] using hON i j),
      smul_neg]
  · intro i j
    rw [cliffordMulBar_twist hanti, smul_mul_assoc, mul_smul_comm, hcd i j]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.cliffordDirac_sq_neg_laplacian where
  formalizes @ "claim:a-clifford-dirac-operator-built-from-anticommuting-generators-with-c-squared-equals-minus-one-squares-to-minus-the-free-laplacian-d-squared-equals-minus-sum-of-nabla-squared-the-algebraic-identity-underlying-the-yang-mills-hamiltonian",
  supported_by @ "paper:aastrup-grimstrup-arxiv-2410-07290-dirac-operators-on-configuration-spaces"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.diracOne_sq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.cliffordDirac_sq_neg_laplacian",
  formalizes @ "claim:the-first-block-of-the-configuration-space-dirac-operator-squares-to-the-free-field-space-laplacian-reproducing-the-minus-sum-nabla-squared-kinetic-term-of-the-yang-mills-hamiltonian",
  requires @ "claim:a-clifford-dirac-operator-built-from-anticommuting-generators-with-c-squared-equals-minus-one-squares-to-minus-the-free-laplacian-d-squared-equals-minus-sum-of-nabla-squared-the-algebraic-identity-underlying-the-yang-mills-hamiltonian"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.diracTwo_sq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.cliffordDirac_sq_neg_laplacian",
  formalizes @ "claim:the-twisted-second-dirac-block-built-from-c-bar-of-i-psi-squares-to-the-same-free-laplacian-so-both-diagonal-blocks-of-the-squared-twisted-dirac-operator-carry-identical-free-hamiltonians"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.su2Basis_embeddingMetric where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.pauliVec_hermitian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry.pauliVec_trace_pair",
  formalizes @ "claim:the-su-two-pauli-generators-i-sigma-a-are-orthogonal-in-the-hilbert-schmidt-trace-metric-with-trace-of-i-sigma-a-dagger-times-i-sigma-b-equal-to-two-delta-a-b-encoding-the-gauge-group-su-two-requirement-of-the-spinor-pair-embedding"

zil_file_contract physlib.configurationSpaceDiracOperator where
  promises "The configuration-space Dirac operator of the Aastrup-Grimstrup spectral construction (arXiv:2410.07290). A Clifford-Dirac operator from anticommuting generators with c^2 = -1 squares to minus the free Laplacian, D^2 = -sum nabla^2 (cliffordDirac_sq_neg_laplacian); the first block squares to the free field-space Laplacian, the Yang-Mills kinetic term (diracOne_sq), and the twisted second block squares to the same Laplacian (diracTwo_sq), so both diagonal blocks carry identical free Hamiltonians. The su(2) Pauli generators are Hilbert-Schmidt orthogonal with Tr((i sigma^a)^H (i sigma^b)) = 2 delta^{ab} (su2Basis_embeddingMetric), encoding the G = SU(2) requirement."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.cliffordMulBar",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry.pauliVec"]
  forbids_substitutes ["the compact-resolvent / summability analysis that makes (A, H, D) a genuine spectral triple, and the functional-analytic self-adjointness of the field-space Dirac operator, which are the cited noncommutative-geometry infrastructure",
    "any claim that the Yang-Mills Hamiltonian is quantized; only the algebraic Clifford-square = free-Laplacian identities and the su(2) orthogonality are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.cliffordDirac_sq_neg_laplacian,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.diracOne_sq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.diracTwo_sq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator.su2Basis_embeddingMetric]

/- ZIL-END -/
