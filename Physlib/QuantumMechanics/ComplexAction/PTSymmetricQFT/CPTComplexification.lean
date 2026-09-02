/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
meta import Zil

/-!
# The Greaves–Thomas `CPT` theorem: complexification and `CPT` as spinorial total inversion

Formalizes the conceptual core of *H. Greaves, T. Thomas, "The CPT Theorem"* (Studies Hist. Phil. Mod.
Phys. 45 (2014) 46, arXiv:1204.4674): a rigorous Lagrangian-QFT account of `CPT`. Two ideas drive their
proof, and both land exactly on the `−iγ⁵` operator of `FirstQuantizedQED.CPTAntiunitary`:

1. **`CPT` is the spinorial total spacetime inversion `PT = −1`.** The `P·T` part reverses every spacetime
   direction, `x^μ ↦ −x^μ` (total inversion `−I`); at the Dirac level this is the adjoint action of `−iγ⁵`,
   which sends each gamma `γ^μ ↦ −γ^μ` (`cpt_total_inversion`). This is the "prima facie mysterious"
   Greaves–Thomas link between charge conjugation and spacetime symmetry: the `C` rides on the spinorial
   realization of total inversion.
2. **Complexification — the key technique.** Total inversion `−I` is *disconnected* from the identity in
   the real proper-orthochronous Lorentz group, but is *connected to it through the complex Lorentz group*.
   The spinorial witness is the **chiral one-parameter group** `R(θ) = cos θ · I + sin θ · (iγ⁵)`
   (`chiralRot`): a complex-rotation flow with `R(0) = I` (`chiralRot_zero`), group law
   `R(α)R(β) = R(α+β)` (`chiralRot_add`), every `R(θ)` invertible (`chiralRot_inv`), and
   `R(−π/2) = −iγ⁵ = CPT` (`chiralRot_cpt`). So `CPT` is reached from the identity by the continuous path
   `θ : 0 ↦ −π/2` inside this one-parameter subgroup of `GL₄(ℂ)` — Greaves–Thomas's passage to the complex
   group, made explicit. (`R(−π) = −I = CPT²`, `chiralRot_pi`, matching `tpc_matrix_sq`.)

The generator `J := iγ⁵` is a **complex structure** `J² = −I` (`chiralGen_sq`), so `R(θ) = cos θ + sin θ J`
rotates exactly like `e^{iθ}` — the analytic continuation that connects `−I` to `I`.

* **§A — complexification: the chiral one-parameter group** (`chiralGen`, `chiralGen_sq`, `chiralRot`,
  `chiralRot_zero`, `chiralRot_add`, `chiralRot_inv`, `chiralRot_cpt`, `chiralRot_pi`, `cpt_eq_chiralRot`).
* **§B — `CPT` as total spacetime inversion** (`gamma50_anticomm`, `γ5_anticomm_γ`, `cpt_conj_inversion`,
  `cpt_total_inversion`): `(−iγ⁵) γ^μ (−iγ⁵)⁻¹ = −γ^μ` for every `μ`.
* **§C — properness in even dimension** (`totalInversion_proper`): `det(−I₄) = (−1)⁴ = 1` — total inversion
  is in the *proper* (`det = 1`) Lorentz component precisely because the dimension is even; the spinor side
  has unit-modulus determinant (`FirstQuantizedQED.CPTOneLoopScattering.cptMatrix_det_sq_one`). In odd dimension
  `det(−I) = −1` (improper) — one of the Greaves–Thomas obstructions to a `PT`/`CPT` theorem.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, Studies Hist. Phil. Mod. Phys. 45 (2014) 46, arXiv:1204.4674 —
  complexification of the Lorentz group as the key technique; `CPT` as spinorial total inversion.
* Repo carriers: `FirstQuantizedQED.CPTAntiunitary` (`cpt`, `cpt_eq_tpcMatrix`); `FirstQuantizedQED.ChiralityHelicityProjectors`
  (`γ5_sq`, `tpc_matrix_sq`, `gamma5ⁱ_anticomm`); `Relativity.CliffordAlgebra` (`γ0`–`γ5`, Dirac rep).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification

open Matrix Complex
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary


/-- **The chiral complex structure** `J = iγ⁵`. -/
noncomputable def chiralGen : Matrix (Fin 4) (Fin 4) ℂ := I • γ5

/-- **`J² = −I`.** `iγ⁵` is a complex structure (`(iγ⁵)² = i²(γ⁵)² = −1`), the generator that lets the
chiral flow `cos θ + sin θ J` rotate like `e^{iθ}` and connect `−I` to `I` in the complex group. -/
lemma chiralGen_sq : chiralGen * chiralGen = -1 := by
  rw [chiralGen, smul_mul_smul_comm, γ5_sq, Complex.I_mul_I, neg_one_smul]

/-- **[Greaves–Thomas complexification] The chiral one-parameter group** `R(θ) = cos θ · I + sin θ · (iγ⁵)`
— the complex-rotation flow whose path from `θ = 0` to `θ = −π/2` carries the identity to `CPT`. -/
noncomputable def chiralRot (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Real.cos θ : ℂ) • 1 + (Real.sin θ : ℂ) • chiralGen

/-- **`R(0) = I`** — the path starts at the identity. -/
lemma chiralRot_zero : chiralRot 0 = 1 := by simp [chiralRot]

/-- **The one-parameter group law `R(α)R(β) = R(α+β)`.** `R` is a homomorphism `(ℝ,+) → GL₄(ℂ)` — the
chiral flow is genuinely a (complexified) rotation group, proved from `J² = −I` and the angle-addition
formulae. -/
lemma chiralRot_add (α β : ℝ) : chiralRot α * chiralRot β = chiralRot (α + β) := by
  simp only [chiralRot, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    smul_smul, chiralGen_sq]
  rw [Real.cos_add, Real.sin_add]; push_cast; module

/-- **Every `R(θ)` is invertible** with inverse `R(−θ)` — the whole path lies in `GL₄(ℂ)`, so `CPT` is
connected to the identity *within the group*. -/
lemma chiralRot_inv (θ : ℝ) : chiralRot θ * chiralRot (-θ) = 1 := by
  rw [chiralRot_add, add_neg_cancel, chiralRot_zero]

/-- **[Greaves–Thomas] `R(−π/2) = −iγ⁵ = CPT`.** The endpoint of the complexification path is exactly the
`CPT` matrix `−iγ⁵` (`FirstQuantizedQED.CPTAntiunitary`, `FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq`). -/
lemma chiralRot_cpt : chiralRot (-(Real.pi / 2)) = (-I) • γ5 := by
  simp only [chiralRot, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
    chiralGen]
  push_cast; simp [neg_smul, smul_smul]

/-- **`R(−π) = −I = CPT²`.** Continuing the path to `θ = −π` reaches total inversion `−I` on the spinor
space — consistent with `CPT² = (−iγ⁵)² = −1` (`tpc_matrix_sq`). -/
lemma chiralRot_pi : chiralRot (-Real.pi) = -1 := by
  simp only [chiralRot, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  push_cast; simp

/-- **[Link] The antiunitary `CPT` operator is the endpoint of the chiral complexification path.** Combining
`FirstQuantizedQED.CPTAntiunitary.cpt_eq_tpcMatrix` (`CPT ψ = (−iγ⁵)ψ`) with `chiralRot_cpt`, the combined `CPT`
operator on spinors is `R(−π/2)` — the identity flowed to `θ = −π/2` through the complex chiral group. -/
lemma cpt_eq_chiralRot (ψ : Fin 4 → ℂ) : cpt ψ = chiralRot (-(Real.pi / 2)) *ᵥ ψ := by
  rw [cpt_eq_tpcMatrix, chiralRot_cpt]


/-- The fourth `γ⁵`-anticommutator `γ⁵γ⁰ = −γ⁰γ⁵` (completing `γ⁵γ¹, γ⁵γ², γ⁵γ³`). -/
lemma gamma50_anticomm : γ5 * γ0 = -(γ0 * γ5) := by
  simp only [γ5, γ0, γ1, γ2, γ3]; ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **`γ⁵` anticommutes with every Dirac vector** `γ⁵ γ^μ = −γ^μ γ⁵` (`μ = 0,1,2,3`) — the algebraic seed
of total inversion. -/
lemma γ5_anticomm_γ (μ : Fin 4) : γ5 * γ μ = -(γ μ * γ5) := by
  fin_cases μ <;> simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  · exact gamma50_anticomm
  · exact gamma51_anticomm
  · exact gamma52_anticomm
  · exact gamma53_anticomm

/-- **The `CPT` adjoint action inverts any `γ⁵`-anticommuting operator.** If `γ⁵ g = −g γ⁵`, then
`(−iγ⁵) g (−iγ⁵)⁻¹ = −g` — the inverse being `−(−iγ⁵)` since `(−iγ⁵)² = −1` (`tpc_matrix_sq`). -/
lemma cpt_conj_inversion (g : Matrix (Fin 4) (Fin 4) ℂ) (hg : γ5 * g = -(g * γ5)) :
    ((-I) • γ5) * g * (-((-I) • γ5)) = -g := by
  have hanti : ((-I) • γ5) * g = -(g * ((-I) • γ5)) := by
    rw [smul_mul_assoc, hg, smul_neg, ← mul_smul_comm]
  calc ((-I) • γ5) * g * (-((-I) • γ5))
      = -(g * ((-I) • γ5)) * (-((-I) • γ5)) := by rw [hanti]
    _ = g * (((-I) • γ5) * ((-I) • γ5)) := by rw [neg_mul_neg, mul_assoc]
    _ = g * (-1) := by rw [tpc_matrix_sq]
    _ = -g := by rw [mul_neg_one]

/-- **[Greaves–Thomas] `CPT` is the spinorial total spacetime inversion.** For every Dirac vector,
`(−iγ⁵) γ^μ (−iγ⁵)⁻¹ = −γ^μ` — the adjoint action of `CPT` sends `x^μ ↦ −x^μ`, i.e. `CPT` realizes the
total inversion `PT = −I` on the spinor representation. This is why the charge conjugation `C` is bound to
the spacetime `PT`: they share the single spinor matrix `−iγ⁵`. -/
lemma cpt_total_inversion (μ : Fin 4) :
    ((-I) • γ5) * (γ μ) * (-((-I) • γ5)) = -(γ μ) :=
  cpt_conj_inversion (γ μ) (γ5_anticomm_γ μ)


/-- **[Greaves–Thomas even-dimension] Total spacetime inversion is proper in `d = 4`.**
`det(−I₄) = (−1)⁴ = 1` — total inversion `PT = −I` lies in the *proper* (`det = 1`) Lorentz component
exactly because the dimension is even; this is what lets the complex-group path of `chiralRot` reach it. In
odd dimension `det(−I) = −1` (improper), a Greaves–Thomas obstruction. The spinor `CPT` matrix correspondingly
has unit-modulus determinant (`FirstQuantizedQED.CPTOneLoopScattering.cptMatrix_det_sq_one`). -/
lemma totalInversion_proper : (-1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralGen_sq where
  formalizes @ "claim:the-chiral-generator-squares-to-minus-one-so-it-generates-a-one-parameter-rotation-subgroup-in-the-complexified-gamma-matrix-algebra",
  supported_by @ "paper:greaves-thomas-arxiv-1204-4674-the-cpt-theorem-complexification"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot_cpt where
  supported_by @ "lean:Vector.neg_smul",
  formalizes @ "claim:the-chiral-rotation-by-minus-pi-over-two-equals-minus-i-times-gamma-five-the-spinor-cpt-operator-reached-by-the-complexified-group-path",
  requires @ "claim:the-chiral-generator-squares-to-minus-one-so-it-generates-a-one-parameter-rotation-subgroup-in-the-complexified-gamma-matrix-algebra"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot_pi where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot_cpt",
  formalizes @ "claim:the-chiral-rotation-by-minus-pi-equals-minus-one-cpt-squared-is-the-spinorial-total-spacetime-inversion-pt-equals-minus-one"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.cpt_total_inversion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTOneLoopScattering.cptMatrix_det_sq_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.cpt_conj_inversion",
  formalizes @ "claim:conjugating-any-gamma-matrix-by-the-spinor-cpt-operator-minus-i-gamma-five-flips-its-sign-so-cpt-is-the-total-spacetime-inversion-reversing-every-spacetime-index"

zil_file_contract physlib.cptComplexification where
  promises "The conceptual core of the Greaves-Thomas CPT theorem (arXiv:1204.4674): CPT is the spinorial total spacetime inversion PT = -1, reached by a one-parameter subgroup of the complexified gamma-matrix algebra that lands on the -i gamma5 operator. The chiral generator squares to minus one (chiralGen_sq), so it generates a rotation subgroup; the chiral rotation by -pi/2 is exactly the spinor CPT operator -i gamma5 (chiralRot_cpt), and the rotation by -pi is -1, the spinorial total inversion (chiralRot_pi). Conjugating any gamma matrix by -i gamma5 flips its sign, so CPT reverses every spacetime index -- the total spacetime inversion (cpt_total_inversion)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot",
    "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralGen"]
  forbids_substitutes ["the full Lagrangian-QFT derivation of CPT invariance from Lorentz invariance and the spectrum condition, which is the theorem the -i gamma5 realization instantiates",
    "the analytic continuation of the S-matrix, only the algebraic chiral-rotation path to the CPT operator is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralGen_sq,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot_cpt,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.chiralRot_pi,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification.cpt_total_inversion]

/- ZIL-END -/
