/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Mathlib.Data.Nat.Choose.Basic
meta import Zil

/-!
# The `SU(3)` representation layer: adjoint Casimir, Weyl dimensions, tensor decompositions

The QCD representation-theory spine (layers L1–L2 plus the structure-constant Casimir) in three
namespaces (each formerly its own module):

* **Part I — `AdjointCasimir`.** The adjoint quadratic Casimir `C₂(adj) = N = 3` assembled from the
  Gell-Mann commutators by the trace projection `f^{abc} = Tr([λₐ,λ_b]λ_c)/(4i)` (`structConst`,
  with the values `1, 1/2, −1/2, √3/2, √3/2`), evaluated along the `a = 1` and `a = 8` rows
  (`adjointCasimirRow1_eq_three`, `adjointCasimirRow8_eq_three`, `adjoint_casimir_eq_three`).
* **Part II — `Su3WeylDimensionCasimir`.** The two invariants labelling an `SU(3)` irrep `(p,q)`:
  the Weyl dimension `½(p+1)(q+1)(p+q+2)` (`weylDim3`, with `1, 3, 3̄, 8, 6, 10, 27` and the
  conjugation symmetry) and the quadratic Casimir `⅓(p²+q²+pq+3p+3q)` (`casimir3`, with
  `C₂(fund) = 4/3`, `C₂(adj) = 3` and the tie `casimir3_adjoint_eq_structConst` to Part I); the
  general `SU(N)` formulas `fundamentalCasimirN N = (N²−1)/2N`, `adjointCasimirN N = N`.
* **Part III — `Su3TensorDecomposition`.** The Clebsch–Gordan dimension bookkeeping: the meson
  `3⊗3̄ = 1⊕8`, the diquark `3⊗3 = 3̄⊕6`, the baryon `3⊗3⊗3 = 10⊕8⊕8⊕1` (`baryon_decomp`), and
  the Young-tableau dimensions `⋀²ℂ³ = 3`, `Sym²ℂ³ = 6`, `⋀³ℂ³ = 1` (the baryon singlet),
  `Sym³ℂ³ = 10` (the decuplet).

**Honest layering.** Proven: the trace-projected structure constants and the two displayed Casimir
rows (each summed over its nonzero support; the remaining rows follow by the same projection and are
not enumerated), the Weyl/Casimir evaluations with their conjugation symmetries, the Part I ↔ Part II
adjoint tie, and the tensor dimension identities. The fundamental-representation realizations of the
singlets are `ColorSingletBaryon` (in `Su6SpinFlavorBaryon`).

## References

* Quadratic Casimir `Σ_{cd}f^{acd}f^{bcd} = C₂(adj)δ^{ab}` with `Tr(λ_aλ_b) = 2δ_{ab}`; the Weyl
  dimension / Freudenthal formula and `C₂ = ⅓(p²+q²+pq+3p+3q)`; `SU(3)` Clebsch–Gordan / Young
  tableaux. Built on `Particles.GellMannStructureConstants` (including its `GluonLieAlgebra` part)
  and `Particles.StrongInteractionColorOctet`; the `A₂` affine weight system is
  `LeviCivita.SorkinSimplecticNetR4`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir

open Matrix Complex
open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants


/-- The `su(3)` structure constant `f^{abc} = Tr([a,b]·c)/(4i)` — the projection of the commutator onto the
generator `c`, using the orthogonality `Tr(λ_cλ_d) = 2δ_{cd}`. -/
noncomputable def structConst (a b c : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  trace ((a * b - b * a) * c) / (4 * I)

/-- **[`f^{123} = 1`]** read off `[λ₁,λ₂] = 2iλ₃` and `Tr(λ₃²) = 2`. -/
lemma structConst_123 : structConst lambda1 lambda2 lambda3 = 1 := by
  have ht : trace (lambda3 * lambda3) = 2 := by
    simp [lambda3, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]; norm_num
  rw [structConst, comm_12, Matrix.smul_mul, trace_smul, ht, smul_eq_mul]
  field_simp
  ring

/-- **[`f^{147} = 1/2`]** read off `[λ₁,λ₄] = iλ₇` and `Tr(λ₇²) = 2`. -/
lemma structConst_147 : structConst lambda1 lambda4 lambda7 = 1 / 2 := by
  have ht : trace (lambda7 * lambda7) = 2 := by
    simp [lambda7, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]; norm_num
  rw [structConst, comm_14, Matrix.smul_mul, trace_smul, ht, smul_eq_mul]
  field_simp
  ring

/-- **[`f^{156} = −1/2`]** read off `[λ₁,λ₅] = −iλ₆` and `Tr(λ₆²) = 2`. -/
lemma structConst_156 : structConst lambda1 lambda5 lambda6 = -1 / 2 := by
  have ht : trace (lambda6 * lambda6) = 2 := by
    simp [lambda6, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]; norm_num
  rw [structConst, comm_15, Matrix.smul_mul, trace_smul, ht, smul_eq_mul]
  field_simp
  ring

/-- **[`f^{458} = √3/2`]** read off `[λ₄,λ₅] = iλ₃ + i√3 λ₈`, with `Tr(λ₃λ₈) = 0` and `Tr(λ₈²) = 2`. -/
lemma structConst_458 : structConst lambda4 lambda5 lambda8 = (Real.sqrt 3 : ℂ) / 2 := by
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have ht38 : trace (lambda3 * lambda8) = 0 := by
    simp [lambda3, lambda8, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  have ht88 : trace (lambda8 * lambda8) = 2 := by
    simp [lambda8, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    rw [hsq]; ring
  rw [structConst, comm_45, add_mul, Matrix.smul_mul, Matrix.smul_mul, trace_add, trace_smul,
    trace_smul, ht38, ht88, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- **[`f^{678} = √3/2`]** read off `[λ₆,λ₇] = −iλ₃ + i√3 λ₈`, with `Tr(λ₃λ₈) = 0` and `Tr(λ₈²) = 2`. -/
lemma structConst_678 : structConst lambda6 lambda7 lambda8 = (Real.sqrt 3 : ℂ) / 2 := by
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have ht38 : trace (lambda3 * lambda8) = 0 := by
    simp [lambda3, lambda8, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  have ht88 : trace (lambda8 * lambda8) = 2 := by
    simp [lambda8, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    rw [hsq]; ring
  rw [structConst, comm_67, add_mul, Matrix.smul_mul, Matrix.smul_mul, trace_add, trace_smul,
    trace_smul, ht38, ht88, smul_eq_mul, smul_eq_mul]
  field_simp
  ring


/-- The diagonal adjoint Casimir element `C^{11} = Σ_{c,d}(f^{1cd})²`, summed over its nonzero support: the
antisymmetric pairs from `f^{123}, f^{147}, f^{156}` (each pair contributes `2×` its square). -/
noncomputable def adjointCasimirRow1 : ℂ :=
  2 * structConst lambda1 lambda2 lambda3 ^ 2
    + 2 * structConst lambda1 lambda4 lambda7 ^ 2
    + 2 * structConst lambda1 lambda5 lambda6 ^ 2

/-- **[`C₂(adj) = 3` (row `1`)]** `2·1² + 2·(1/2)² + 2·(−1/2)² = 3 = N`. -/
lemma adjointCasimirRow1_eq_three : adjointCasimirRow1 = 3 := by
  rw [adjointCasimirRow1, structConst_123, structConst_147, structConst_156]; ring


/-- The diagonal adjoint Casimir element `C^{88} = Σ_{c,d}(f^{8cd})²`, summed over its nonzero support: the
antisymmetric pairs from `f^{458}, f^{678}`. -/
noncomputable def adjointCasimirRow8 : ℂ :=
  2 * structConst lambda4 lambda5 lambda8 ^ 2
    + 2 * structConst lambda6 lambda7 lambda8 ^ 2

/-- **[`C₂(adj) = 3` (row `8`)]** `2·(√3/2)² + 2·(√3/2)² = 3 = N` — the same eigenvalue via the `λ₈`-direction
constants (`(√3/2)² = 3/4`). -/
lemma adjointCasimirRow8_eq_three : adjointCasimirRow8 = 3 := by
  have hsq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  rw [adjointCasimirRow8, structConst_458, structConst_678]
  field_simp
  ring_nf
  rw [hsq]; ring


/-- **[The adjoint quadratic Casimir is `N = 3`]** the diagonal Casimir element `Σ_{cd}(f^{acd})²` evaluates
to `3` along both the `a=1` row (from `f^{123},f^{147},f^{156}`) and the `a=8` row (from `f^{458},f^{678}`) —
the row-independent eigenvalue `C₂(adj) = N = 3` of the eight-gluon `su(3)` colour algebra. -/
lemma adjoint_casimir_eq_three : adjointCasimirRow1 = 3 ∧ adjointCasimirRow8 = 3 :=
  ⟨adjointCasimirRow1_eq_three, adjointCasimirRow8_eq_three⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir

/-! ## Part II — `SU(3)` irreps: the Weyl dimension and the quadratic Casimir -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir

/-- The **`SU(3)` Weyl dimension formula** `dim(p,q) = ½(p+1)(q+1)(p+q+2)` for the irrep of highest weight
(Dynkin labels) `(p, q)`. -/
def weylDim3 (p q : ℕ) : ℕ := (p + 1) * (q + 1) * (p + q + 2) / 2

/-- The **singlet** `1 = dim(0,0)`. -/
lemma weylDim3_singlet : weylDim3 0 0 = 1 := by decide

/-- The **fundamental** `3 = dim(1,0)`. -/
lemma weylDim3_fundamental : weylDim3 1 0 = 3 := by decide

/-- The **anti-fundamental** `3̄ = dim(0,1)` — same dimension as `3` (its `weightConjugation`). -/
lemma weylDim3_antifundamental : weylDim3 0 1 = 3 := by decide

/-- The **adjoint / octet** `8 = dim(1,1)`. -/
lemma weylDim3_adjoint : weylDim3 1 1 = 8 := by decide

/-- The **sextet** `6 = dim(2,0)`. -/
lemma weylDim3_sextet : weylDim3 2 0 = 6 := by decide

/-- The **decuplet** `10 = dim(3,0)`. -/
lemma weylDim3_decuplet : weylDim3 3 0 = 10 := by decide

/-- The `27 = dim(2,2)` (the `8 ⊗ 8` leading rep). -/
lemma weylDim3_27 : weylDim3 2 2 = 27 := by decide

/-- **The dimension is conjugation-symmetric** `dim(p,q) = dim(q,p)`: a representation and its conjugate
(`p ↔ q`, the `weightConjugation` `3 ↔ 3̄`) have the same dimension. -/
lemma weylDim3_conj (p q : ℕ) : weylDim3 p q = weylDim3 q p := by
  show (p + 1) * (q + 1) * (p + q + 2) / 2 = (q + 1) * (p + 1) * (q + p + 2) / 2
  congr 1; ring

/-- **The adjoint dimension is the gluon count** `dim(1,1) = N² − 1 = 8`
(`StrongInteractionColorOctet.gluon_count`): the eight gluons are the `su(3)` adjoint. -/
lemma weylDim3_adjoint_eq_gluonCount : weylDim3 1 1 = 3 ^ 2 - 1 := by
  rw [Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet.gluon_count]; decide

/-- The **`su(3)` quadratic Casimir eigenvalue** `C₂(p,q) = ⅓(p² + q² + pq + 3p + 3q)` on the irrep of highest
weight `(p, q)` (normalized so the adjoint gives `N = 3`). -/
def casimir3 (p q : ℚ) : ℚ := (p ^ 2 + q ^ 2 + p * q + 3 * p + 3 * q) / 3

/-- The **singlet** Casimir `C₂(0,0) = 0`. -/
lemma casimir3_singlet : casimir3 0 0 = 0 := by norm_num [casimir3]

/-- The **fundamental** Casimir `C₂(1,0) = 4/3 = (N²−1)/2N` — completing the value `AdjointCasimir` left
uncomputed. -/
lemma casimir3_fundamental : casimir3 1 0 = 4 / 3 := by norm_num [casimir3]

/-- The **adjoint** Casimir `C₂(1,1) = 3 = N`. -/
lemma casimir3_adjoint : casimir3 1 1 = 3 := by norm_num [casimir3]

/-- The **decuplet** Casimir `C₂(3,0) = 6`. -/
lemma casimir3_decuplet : casimir3 3 0 = 6 := by norm_num [casimir3]

/-- **The Casimir is conjugation-symmetric** `C₂(p,q) = C₂(q,p)` (the `weightConjugation` `3 ↔ 3̄`). -/
lemma casimir3_conj (p q : ℚ) : casimir3 p q = casimir3 q p := by
  unfold casimir3; ring

/-- **The Weyl-formula adjoint Casimir is the structure-constant Casimir** `C₂(adjoint) = Σ_{cd}(f^{1cd})² = 3`:
the highest-weight Casimir `casimir3 1 1` equals `AdjointCasimir.adjointCasimirRow1`, tying the Freudenthal
formula to the explicit `f^{abc}` computation of `AdjointCasimir`. -/
lemma casimir3_adjoint_eq_structConst :
    ((casimir3 1 1 : ℚ) : ℂ) =
      Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir.adjointCasimirRow1 := by
  rw [Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir.adjointCasimirRow1_eq_three,
    casimir3_adjoint]
  norm_num

/-- The **fundamental quadratic Casimir of `su(N)`** `C₂(fund) = (N² − 1)/2N`. -/
def fundamentalCasimirN (N : ℚ) : ℚ := (N ^ 2 - 1) / (2 * N)

/-- The **adjoint quadratic Casimir of `su(N)`** `C₂(adj) = N`. -/
def adjointCasimirN (N : ℚ) : ℚ := N

/-- At `N = 3` the fundamental Casimir is `4/3`, matching `casimir3_fundamental`. -/
lemma fundamentalCasimirN_three : fundamentalCasimirN 3 = 4 / 3 := by norm_num [fundamentalCasimirN]

/-- At `N = 3` the adjoint Casimir is `3`, matching `casimir3_adjoint` and `AdjointCasimir` (`C₂(adj) = N`). -/
lemma adjointCasimirN_three : adjointCasimirN 3 = 3 := rfl

end Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir

/-! ## Part III — `SU(3)` tensor-product decompositions -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su3TensorDecomposition

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir

/-- **The meson `3 ⊗ 3̄ = 1 ⊕ 8`** `dim 3 · dim 3̄ = dim 1 + dim 8` (`9 = 1 + 8`): a quark–antiquark pair
splits into the colour singlet (the trace, `ColorSingletBaryon.mesonSinglet`) and the octet. -/
lemma meson_decomp : weylDim3 1 0 * weylDim3 0 1 = weylDim3 0 0 + weylDim3 1 1 := by decide

/-- **The diquark `3 ⊗ 3 = 3̄ ⊕ 6`** `dim 3 · dim 3 = dim 3̄ + dim 6` (`9 = 3 + 6`): two quarks split into the
antisymmetric `3̄` and the symmetric `6`. -/
lemma diquark_decomp : weylDim3 1 0 * weylDim3 1 0 = weylDim3 0 1 + weylDim3 2 0 := by decide

/-- **The baryon `3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1`** `(dim 3)³ = dim 10 + 2·dim 8 + dim 1` (`27 = 10 + 16 + 1`):
three quarks split into the symmetric decuplet, two mixed octets, and the totally antisymmetric singlet
(`ColorSingletBaryon.baryonColor`, the `ε_{abc}` determinant). -/
lemma baryon_decomp : weylDim3 1 0 ^ 3 = weylDim3 3 0 + 2 * weylDim3 1 1 + weylDim3 0 0 := by decide

/-- **The mixed octets** `8 + 8 = 27 − 10 − 1 = 16`. -/
lemma baryon_mixed_dim : weylDim3 1 0 ^ 3 - weylDim3 3 0 - weylDim3 0 0 = 2 * weylDim3 1 1 := by decide

/-- **The antisymmetric diquark** `⋀²(ℂ³) = C(3,2) = 3 = 3̄`. -/
lemma antisym2_dim : Nat.choose 3 2 = weylDim3 0 1 := by decide

/-- **The symmetric diquark** `Sym²(ℂ³) = C(4,2) = 6`. -/
lemma sym2_dim : Nat.choose 4 2 = weylDim3 2 0 := by decide

/-- **The totally antisymmetric baryon singlet** `⋀³(ℂ³) = C(3,3) = 1`: the one-dimensional totally
antisymmetric colour combination — the `ε_{abc}` determinant `ColorSingletBaryon.baryonColor`, the colour
singlet baryon. -/
lemma antisym3_dim : Nat.choose 3 3 = weylDim3 0 0 := by decide

/-- **The totally symmetric baryon** `Sym³(ℂ³) = C(5,3) = 10`: the decuplet (the spin-3/2 baryons). The same
`C(5,3) = 10` pentagon that gave the `d`-shell / `SU(5)` `10`. -/
lemma sym3_dim : Nat.choose 5 3 = weylDim3 3 0 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.Su3TensorDecomposition

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir.adjoint_casimir_eq_three where
  formalizes @ "claim:su3-adjoint-quadratic-casimir-is-N-equals-three-from-structure-constants",
  supported_by @ "paper:gell-mann-1962-symmetries-of-baryons-and-mesons",
  caveat @ "claim:each-casimir-row-summed-over-its-nonzero-structure-constant-support"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.casimir3_adjoint_eq_structConst where
  formalizes @ "claim:weyl-formula-adjoint-casimir-equals-the-structure-constant-casimir",
  requires @ "claim:su3-adjoint-quadratic-casimir-is-N-equals-three-from-structure-constants",
  supported_by @ "paper:gell-mann-1962-symmetries-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.casimir3_fundamental where
  supported_by @ "lean:ContinuousLinearMap.adjoint",
  formalizes @ "claim:su3-fundamental-quadratic-casimir-is-four-thirds",
  caveat @ "claim:exact-weyl-freudenthal-evaluation-not-a-fitted-value"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3TensorDecomposition.baryon_decomp where
  formalizes @ "claim:su3-baryon-tensor-product-is-decuplet-octet-octet-singlet",
  requires @ "claim:su3-fundamental-quadratic-casimir-is-four-thirds"

zil_file_contract physlib.su3WeylDimensionCasimir where
  promises "The SU(3) representation layer: the adjoint quadratic Casimir is N equals three assembled from the trace-projected Gell-Mann structure constants, the Weyl-formula adjoint Casimir equals that structure-constant Casimir, the fundamental Casimir is four-thirds, and the baryon tensor product decomposes as decuplet plus two octets plus the singlet."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir.structConst",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.weylDim3",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.casimir3"]
  forbids_substitutes ["an enumeration of all eight Casimir rows, only the a=1 and a=8 rows are displayed",
    "the fundamental-representation realization of the singlets, which is ColorSingletBaryon"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.AdjointCasimir.adjoint_casimir_eq_three,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.casimir3_adjoint_eq_structConst,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.casimir3_fundamental,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su3TensorDecomposition.baryon_decomp]

/- ZIL-END -/
