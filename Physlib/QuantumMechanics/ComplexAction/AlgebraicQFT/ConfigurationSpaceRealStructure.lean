/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature

meta import Zil

/-!
# The real structure and the rotation into self-dual/anti-self-dual Yang–Mills

The new exact content of the companion paper Aastrup–Grimstrup arXiv:2410.07290
(*Dirac Operators on Configuration Spaces: Fermions with Half-integer Spin, Real
Structure, and Yang-Mills Quantum Field Theory*) — the paper whose real structure and
untwisted fluctuation the main arc (arXiv:2501.00005) cites as [15].  Its §2.3
metric-independence computation and §3.1 CAR/Clifford algebra are already formalized
(`ConfigurationSpaceDiracOperator.columnsInner_eq_trace`,
`ConfigurationSpaceDiracFluctuation`); here are §3.2 and §4.

## §A — the real structure and the KO-sign identity (paper §3.2, Eqs 3–4)

The charge conjugation `C` is a fiberwise antilinear isometry with `C² = −1`,
implemented on the Fock space by `C_F` with `C_F c̄(ψ) C_F = ε·c̄(Cψ)` (paper Eq. 3,
`ε = (−1)^deg` on a fixed-degree sector).  Exactly:

* `cliffordMulBar_neg` — `c̄(−ψ) = −c̄(ψ)`, from the antilinearity of `int` alone.
* `chargeConj_double` — applying the conjugation relation at `Cψ` and using
  `C² = −1` **flips the sign**: `C_F c̄(Cψ) C_F = −ε·c̄(ψ)`. This asymmetry between
  the two spin sectors is the origin of the grading `γ` in Eq. 4.
* `chargeConj_diracPlus`/`chargeConj_diracMinus` — on the Dirac blocks
  `D⁺ = Σc̄(ψᵢ)∇ᵢ`, `D⁻ = Σc̄(Cψᵢ)∇ᵢ`: conjugation exchanges them with the
  asymmetric signs, `C_F D⁺ C_F = ε·D⁻` and `C_F D⁻ C_F = −ε·D⁺`.
* `realStructure_KO_identity` — **paper Eq. 4**: with `𝒥 = offdiag(C_F, C_F)` and
  `𝒟 = diag(D⁺, D⁻)`,

  `𝒥𝒟𝒥 = ε·(γ𝒟)`, `γ = diag(−1, 1)` —

  the KO-sign compatibility of the real structure with the Dirac operator.  Together
  with `ConfigurationSpaceTwistSignature.twist_not_conjugation` this completes the
  main paper's §6 comparison: *this* is the real-structure conjugation, and the twist
  provably is not it.

## §B — the rotation into Yang–Mills (paper §4, Eq. 7)

The unitary rotation `𝒟^U = U𝒟U*` with `U = diag(e^{ikCS}, e^{−ikCS})`:

* `conjugated_sq` — conjugation passes through the square:
  `g·D²·g⁻¹ = (g·D·g⁻¹)²`.
* `conjugated_sq_normalOrdered` — with the rotated block `g·D·g⁻¹ = D − s` (`s` the
  Chern–Simons gradient contraction `ik·∂CS`) and the normal-ordering commutator
  `D·s = s·D + t` (`t = ik·∂²CS`, **the second functional derivative of the
  Chern–Simons term**), the conjugated square expands exactly as paper Eq. 7:

  `g·D²·g⁻¹ = D² − 2sD − t + s²`.

* `rotated_sq_sectors` — assembling both blocks: the rotated squares are
  `diag(D² − 2sD + s² − t, D² + 2sD + s² + t)` — **the self-dual and anti-self-dual
  sectors emerge in a two-by-two matrix structure** (the paper's abstract): the two
  diagonal blocks differ exactly by the sign of the cross term `2sD` and of the
  second Chern–Simons derivative `t`, the `|E ± B|²` completion that separates the
  dual sectors.  The `±`-split of the norm is the Hodge decomposition of
  `SelfDualQuaternionYangMills.crossTerm_split`.

## Honest scope

`ε = (−1)^deg` is a fixed scalar (a fixed-degree Fock sector); the one-particle `C`
is a map `K → K` with `C² = −1` as hypothesis (the fiberwise antilinear isometry of
the paper's `ℂl(TM)` real structure `x ⊗ λ ↦ x ⊗ λ̄`; the `Cl(TM) ≅ ℍ ⊕ ℍ` fiber
statement connects to `SelfDualQuaternionYangMills.quaternionRep`); the Levi-Civita
connection on the configuration space, the spectral invariant measuring spectral
asymmetry, and the `Ξ` term of paper Eq. 7 (the `Ξ` mechanism is
`ConfigurationSpaceGaugeGeometry` §B) are recorded, not re-derived.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2410.07290: §3.2 (real structure, Eqs 3–4),
  §4 (rotation, Eqs 5–7); companion arXiv:2410.03699; main arc arXiv:2501.00005.
* Carriers: `AlgebraicQFT.ConfigurationSpaceDiracFluctuation` (Clifford pair, twist),
  `AlgebraicQFT.ConfigurationSpaceTwistSignature` (the twist/real-structure
  distinction this module completes), `AlgebraicQFT.SelfDualQuaternionYangMills`
  (the `±` split of the sectors).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-! ## §A — the real structure and the KO-sign identity -/

/-- `c̄(−ψ) = −c̄(ψ)` — from the antilinearity of `int` alone (via `−ψ = i·(i·ψ)`). -/
theorem cliffordMulBar_neg [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ : K) :
    cliffordMulBar B (-ψ) = -(cliffordMulBar B ψ) := by
  have h : -ψ = Complex.I • (Complex.I • ψ) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [h, cliffordMulBar_twist hanti, cliffordMul_twist hanti, smul_smul,
    Complex.I_mul_I, neg_one_smul]

/-- **The conjugation relation at `Cψ` flips the sign** (the mechanism of the grading
`γ`): from `C_F c̄(ψ) C_F = ε·c̄(Cψ)` (paper Eq. 3) and `C² = −1` on one-particle
spinors, `C_F c̄(Cψ) C_F = −ε·c̄(ψ)`. -/
theorem chargeConj_double [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ))
    {Cop : K → K} (hC2 : ∀ ψ, Cop (Cop ψ) = -ψ) {CF : A} {ε : ℂ}
    (hconj : ∀ ψ, CF * cliffordMulBar B ψ * CF = ε • cliffordMulBar B (Cop ψ))
    (ψ : K) :
    CF * cliffordMulBar B (Cop ψ) * CF = -(ε • cliffordMulBar B ψ) := by
  rw [hconj (Cop ψ), hC2 ψ, cliffordMulBar_neg hanti, smul_neg]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] in
/-- **Conjugation sends `D⁺` to `ε·D⁻`**: for `D⁺ = Σc̄(ψᵢ)∇ᵢ` and
`D⁻ = Σc̄(Cψᵢ)∇ᵢ`, with `C_F² = −1` and `C_F` commuting with the derivatives,
`C_F D⁺ C_F = ε·D⁻`. -/
theorem chargeConj_diracPlus [IsScalarTower ℂ A A] {B : K → A} {n : ℕ}
    (ψ : Fin n → K) (Cop : K → K)
    (dv : Fin n → A) {CF : A} {ε : ℂ}
    (hCFCF : CF * CF = -1)
    (hCFd : ∀ i, CF * dv i = dv i * CF)
    (hconj : ∀ φ, CF * cliffordMulBar B φ * CF = ε • cliffordMulBar B (Cop φ)) :
    CF * (∑ i, cliffordMulBar B (ψ i) * dv i) * CF
      = ε • ∑ i, cliffordMulBar B (Cop (ψ i)) * dv i := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hins : CF * (cliffordMulBar B (ψ i) * dv i) * CF
      = (CF * cliffordMulBar B (ψ i) * CF) * -(CF * dv i * CF) := by
    have h1 : CF * -CF = 1 := by
      rw [mul_neg, hCFCF, neg_neg]
    calc CF * (cliffordMulBar B (ψ i) * dv i) * CF
        = CF * cliffordMulBar B (ψ i) * (CF * -CF) * dv i * CF := by
          rw [h1]; noncomm_ring
      _ = (CF * cliffordMulBar B (ψ i) * CF) * -(CF * dv i * CF) := by noncomm_ring
  have hd : CF * dv i * CF = -(dv i) := by
    rw [hCFd i, mul_assoc, hCFCF, mul_neg, mul_one]
  rw [hins, hd, neg_neg, hconj (ψ i), smul_mul_assoc]

/-- **Conjugation sends `D⁻` back with the opposite sign**: `C_F D⁻ C_F = −ε·D⁺` —
the sign asymmetry produced by `C² = −1` (`chargeConj_double`). -/
theorem chargeConj_diracMinus [StarModule ℂ A] [IsScalarTower ℂ A A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ))
    {n : ℕ} (ψ : Fin n → K) {Cop : K → K} (hC2 : ∀ φ, Cop (Cop φ) = -φ)
    (dv : Fin n → A) {CF : A} {ε : ℂ}
    (hCFCF : CF * CF = -1)
    (hCFd : ∀ i, CF * dv i = dv i * CF)
    (hconj : ∀ φ, CF * cliffordMulBar B φ * CF = ε • cliffordMulBar B (Cop φ)) :
    CF * (∑ i, cliffordMulBar B (Cop (ψ i)) * dv i) * CF
      = -(ε • ∑ i, cliffordMulBar B (ψ i) * dv i) := by
  rw [chargeConj_diracPlus (B := B) (fun i => Cop (ψ i)) Cop dv hCFCF hCFd hconj]
  have hsum : (∑ i, cliffordMulBar B (Cop (Cop (ψ i))) * dv i)
      = -(∑ i, cliffordMulBar B (ψ i) * dv i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hC2 (ψ i), cliffordMulBar_neg hanti, neg_mul]
  rw [hsum, smul_neg]

/-- The off-diagonal block operator `offdiag(P, Q)` — the shape of the real structure
`𝒥 = offdiag(C_F, C_F)` of paper §3.2. -/
def blockOffDiag {R : Type*} [Ring R] (P Q : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 1 then P else 0) else (if j = 0 then Q else 0)

/-- Conjugating a diagonal block operator by `offdiag(C, C)` swaps the blocks and
dresses them: `𝒥·diag(X, Y)·𝒥 = diag(C·Y·C, C·X·C)`. -/
theorem blockOffDiag_conj {R : Type*} [Ring R] (C X Y : R) :
    blockOffDiag C C * ConfigurationSpaceDiracFluctuation.blockDiag X Y
        * blockOffDiag C C
      = ConfigurationSpaceDiracFluctuation.blockDiag (C * Y * C) (C * X * C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockOffDiag, ConfigurationSpaceDiracFluctuation.blockDiag,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **The KO-sign identity, paper Eq. 4**: `𝒥𝒟𝒥 = ε·(γ𝒟)` — with
`𝒥 = offdiag(C_F, C_F)`, `𝒟 = diag(D⁺, D⁻)` and the grading `γ = diag(−1, 1)`, the
real structure conjugates the Dirac operator into `ε` times its `γ`-graded self: the
compatibility of the real structure with the Dirac operator, whose sign asymmetry
descends from `C² = −1`. -/
theorem realStructure_KO_identity [StarModule ℂ A] [IsScalarTower ℂ A A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ))
    {n : ℕ} (ψ : Fin n → K) {Cop : K → K} (hC2 : ∀ φ, Cop (Cop φ) = -φ)
    (dv : Fin n → A) {CF : A} {ε : ℂ}
    (hCFCF : CF * CF = -1)
    (hCFd : ∀ i, CF * dv i = dv i * CF)
    (hconj : ∀ φ, CF * cliffordMulBar B φ * CF = ε • cliffordMulBar B (Cop φ)) :
    blockOffDiag CF CF
        * ConfigurationSpaceDiracFluctuation.blockDiag
            (∑ i, cliffordMulBar B (ψ i) * dv i)
            (∑ i, cliffordMulBar B (Cop (ψ i)) * dv i)
        * blockOffDiag CF CF
      = ε • (ConfigurationSpaceDiracFluctuation.blockDiag (-1 : A) 1
          * ConfigurationSpaceDiracFluctuation.blockDiag
              (∑ i, cliffordMulBar B (ψ i) * dv i)
              (∑ i, cliffordMulBar B (Cop (ψ i)) * dv i)) := by
  rw [blockOffDiag_conj, ConfigurationSpaceDiracFluctuation.blockDiag_mul,
    chargeConj_diracPlus (B := B) ψ Cop dv hCFCF hCFd hconj,
    chargeConj_diracMinus (B := B) hanti ψ hC2 dv hCFCF hCFd hconj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConfigurationSpaceDiracFluctuation.blockDiag]

/-! ## §B — the rotation into Yang–Mills (paper §4, Eq. 7) -/

/-- **Conjugation passes through the square**: `g·D²·g⁻¹ = (g·D·g⁻¹)²`. -/
theorem conjugated_sq {R : Type*} [Ring R] {g g' d : R} (hg'g : g' * g = 1) :
    g * (d * d) * g' = (g * d * g') * (g * d * g') := by
  calc g * (d * d) * g' = g * d * (g' * g) * d * g' := by rw [hg'g]; noncomm_ring
    _ = (g * d * g') * (g * d * g') := by noncomm_ring

/-- **The conjugated square, paper Eq. 7**: with the rotated block `g·D·g⁻¹ = D − s`
(`s = ik·∂CS`, the Chern–Simons gradient) and the normal ordering `D·s = s·D + t`
(`t = ik·∂²CS`, the **second functional derivative of the Chern–Simons term**),

`g·D²·g⁻¹ = D² − 2sD − t + s²` —

the four terms of Eq. 7: the free Laplacian, the first-order transport, the second
Chern–Simons derivative, and the squared gradient (the magnetic term of `H_YM`). -/
theorem conjugated_sq_normalOrdered {R : Type*} [Ring R] {g g' d s t : R}
    (hg'g : g' * g = 1) (hrot : g * d * g' = d - s) (hds : d * s = s * d + t) :
    g * (d * d) * g' = d * d - (s * d + s * d) - t + s * s := by
  rw [conjugated_sq hg'g, hrot]
  calc (d - s) * (d - s) = d * d - d * s - s * d + s * s := by noncomm_ring
    _ = d * d - (s * d + t) - s * d + s * s := by rw [hds]
    _ = d * d - (s * d + s * d) - t + s * s := by noncomm_ring

/-- **The self-dual and anti-self-dual sectors emerge in a two-by-two matrix
structure** (the paper's abstract; §4): the two diagonal blocks of the rotated
squared Dirac operator carry *opposite* signs of the cross term `2sD` and of the
second Chern–Simons derivative `t`:

`U𝒟²U* = diag(D₊² − 2sD₊ + s² − t, D₋² + 2sD₋ + s² + t)` —

the `|E ∓ B|²`-type completions distinguishing the dual sectors; their `±` norm
split is the Hodge decomposition of `SelfDualQuaternionYangMills.crossTerm_split`. -/
theorem rotated_sq_sectors {R : Type*} [Ring R] {g g' dp dm s t : R}
    (hg'g : g' * g = 1) (hgg' : g * g' = 1)
    (hrotp : g * dp * g' = dp - s) (hrotm : g' * dm * g = dm + s)
    (hdsp : dp * s = s * dp + t) (hdsm : dm * s = s * dm + t) :
    ConfigurationSpaceDiracFluctuation.blockDiag g g'
        * ConfigurationSpaceDiracFluctuation.blockDiag (dp * dp) (dm * dm)
        * ConfigurationSpaceDiracFluctuation.blockDiag g' g
      = ConfigurationSpaceDiracFluctuation.blockDiag
          (dp * dp - (s * dp + s * dp) - t + s * s)
          (dm * dm + (s * dm + s * dm) + t + s * s) := by
  rw [ConfigurationSpaceDiracFluctuation.blockDiag_mul,
    ConfigurationSpaceDiracFluctuation.blockDiag_mul]
  congr 1
  · exact conjugated_sq_normalOrdered hg'g hrotp hdsp
  · rw [conjugated_sq hgg', hrotm]
    calc (dm + s) * (dm + s) = dm * dm + dm * s + s * dm + s * s := by noncomm_ring
      _ = dm * dm + (s * dm + t) + s * dm + s * s := by rw [hdsm]
      _ = dm * dm + (s * dm + s * dm) + t + s * s := by abel

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.realStructure_KO_identity where
  formalizes @ "claim:the-charge-conjugation-real-structure-j-conjugates-the-dirac-operator-into-epsilon-times-its-gamma-graded-self-j-d-j-equals-epsilon-gamma-d-the-ko-dimension-sign-compatibility-of-the-real-structure-with-the-dirac-operator",
  supported_by @ "paper:aastrup-grimstrup-arxiv-2410-07290-dirac-operators-on-configuration-spaces"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.rotated_sq_sectors where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.conjugated_sq_normalOrdered",
  formalizes @ "claim:unitary-rotation-by-the-chern-simons-phase-splits-the-squared-dirac-operator-into-diagonal-self-dual-and-anti-self-dual-yang-mills-blocks-differing-by-the-sign-of-the-cross-term-and-the-second-chern-simons-derivative"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.chargeConj_double where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.cliffordMulBar_neg",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:because-charge-conjugation-squares-to-minus-one-on-one-particle-spinors-conjugating-the-clifford-generator-twice-flips-sign-the-asymmetry-that-generates-the-grading-gamma"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.conjugated_sq_normalOrdered where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.conjugated_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills.crossTerm_split",
  formalizes @ "claim:the-rotated-dirac-square-expands-to-d-squared-minus-two-s-d-minus-t-plus-s-squared-the-free-laplacian-plus-transport-plus-second-chern-simons-derivative-plus-squared-gradient-magnetic-term"

zil_file_contract physlib.configurationSpaceRealStructure where
  promises "The real structure and the rotation into self-dual / anti-self-dual Yang-Mills (Aastrup-Grimstrup arXiv:2410.07290). The charge-conjugation real structure J conjugates the Dirac operator into epsilon times its gamma-graded self, J D J = epsilon gamma D -- the KO-dimension sign compatibility (realStructure_KO_identity) -- arising because C^2 = -1 on one-particle spinors generates the grading (chargeConj_double). Unitary rotation by the Chern-Simons phase splits the squared Dirac operator into self-dual and anti-self-dual Yang-Mills blocks (rotated_sq_sectors); the rotated square expands to D^2 - 2sD - t + s^2 (conjugated_sq_normalOrdered), the free Laplacian plus transport, second Chern-Simons derivative, and magnetic term."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.blockOffDiag",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.blockDiag"]
  forbids_substitutes ["the KO-dimension table and the axioms (order-one, regularity, reality) that make (A, H, D, J, gamma) a genuine real spectral triple, which are the cited noncommutative-geometry infrastructure",
    "any claim that the self-dual Yang-Mills equations are solved; only the algebraic KO-sign identity and the block rotation are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.realStructure_KO_identity,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.rotated_sq_sectors,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.chargeConj_double,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure.conjugated_sq_normalOrdered]

/- ZIL-END -/
