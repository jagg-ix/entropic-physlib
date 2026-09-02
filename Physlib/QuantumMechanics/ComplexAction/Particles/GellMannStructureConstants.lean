/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.NonAbelianThreeVertex
public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Mathlib.Algebra.Lie.OfAssociative
meta import Zil

/-!
# The su(3) colour algebra: gluon Lie bracket, Gell-Mann matrices, Gell-Mann–Nishijima charges

The colour-algebra layer in three namespaces (each formerly its own module):

* **Part I — `GluonLieAlgebra`.** The gluon self-interaction grounded in the matrix-commutator Lie
  bracket: the three-gluon vertex is the commutator (`gluon_vertex_commutator`), antisymmetric
  (`gluon_vertex_antisymm` — the `f^{abc}` antisymmetry), self-annihilating, satisfying the cyclic
  Jacobi identity (`gluon_jacobi` — four-gluon consistency), with the abelian contrast
  (`abelian_vertex_zero`: no photon self-vertex) and the summary `gluon_lie_structure`. Basis-free —
  the concrete Lie-algebraic origin of `ChernSimons.NonAbelianThreeVertex`.
* **Part II — `GellMannStructureConstants`.** The explicit `su(3)` realization: the eight traceless
  Gell-Mann matrices (`gellMann_traceless`), the embedded `su(2)` with `f^{123} = 1`
  (`comm_12`/`comm_23`/`comm_31`), the off-block `f^{147} = 1/2` and `f^{156} = −1/2`
  (`comm_14`/`comm_15`), and the distinctive `λ₈`-direction `f^{458} = f^{678} = √3/2`
  (`comm_45`/`comm_67`) — the three distinct magnitudes of the full antisymmetric `f^{abc}` table
  (`gellMann_structure_constants`).
* **Part III — `GellMannNishijima`.** The fractional charges *derived* from weak isospin and
  hypercharge, `Q = T₃ + Y/2`: the relation reproduces the winding charges exactly
  (`gmn_up`/`gmn_down`/`gmn_neutrino`/`gmn_electron`), the hypercharge is the doublet's mean charge
  (`hypercharge_eq_average_doublet_charge`), and the intra-doublet splitting is `1`
  (`doublet_charge_splitting`).

**Honest layering.** Proven: the bracket antisymmetry/Jacobi from Mathlib's commutator Lie ring, the
listed Gell-Mann commutators exactly (the remaining nonzero `f^{abc}` entries follow by the identical
computation), and the Gell-Mann–Nishijima reproduction of the winding charges. The `(T₃, Y)`
assignments are the empirical SM multiplet structure; the gauge-field dynamics are not built here.

## References

* Yang–Mills self-interaction, structure constants `⁅Tₐ,T_b⁆ = f^{abc}T_c`; Gell-Mann matrices with
  `f^{123} = 1`, `f^{147} = 1/2`, `f^{458} = √3/2`; Gell-Mann–Nishijima `Q = T₃ + Y/2`. `Physlib`
  (`ChernSimons.NonAbelianThreeVertex`, `Winding.QuarkChargeWinding.windingCharge`); Mathlib
  (`Algebra.Lie.OfAssociative`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra

variable {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)


/-- **[The three-gluon vertex is the commutator]** `⁅A, B⁆ = A·B − B·A` — two gauge fields couple through
their commutator (the cubic `A³` term of `F = dA + g[A,A]`). -/
lemma gluon_vertex_commutator : ⁅A, B⁆ = A * B - B * A := Ring.lie_def A B

/-- **[The three-gluon vertex is antisymmetric]** `⁅A, B⁆ = −⁅B, A⁆` — the structure constants `f^{abc}` are
antisymmetric in the first two indices. -/
lemma gluon_vertex_antisymm : ⁅A, B⁆ = -⁅B, A⁆ := by
  rw [Ring.lie_def, Ring.lie_def]; abel

/-- **[A gluon does not self-couple to its own copy]** `⁅A, A⁆ = 0`. -/
lemma gluon_self_vertex_zero : ⁅A, A⁆ = 0 := by rw [Ring.lie_def, sub_self]


/-- **[The structure-constant Jacobi identity]** `⁅A,⁅B,C⁆⁆ + ⁅B,⁅C,A⁆⁆ + ⁅C,⁅A,B⁆⁆ = 0` — the cyclic Jacobi
`f^{abe}f^{ecd} + ⟲ = 0`, the consistency condition for the nested (four-gluon) vertices. -/
lemma gluon_jacobi : ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := by
  simp only [Ring.lie_def]; noncomm_ring


/-- **[Abelian fields have no self-vertex]** if `A` and `B` commute (an abelian `U(1)` gauge theory, e.g. the
photon), their bracket vanishes — `⁅A, B⁆ = 0`: no self-interaction. -/
lemma abelian_vertex_zero (h : A * B = B * A) : ⁅A, B⁆ = 0 := by
  rw [Ring.lie_def, h, sub_self]


/-- **[The gluon Lie structure]** the gauge-field bracket is antisymmetric (`⁅A,B⁆ = −⁅B,A⁆`), self-annihilating
(`⁅A,A⁆=0`), and satisfies the cyclic Jacobi identity — the three-gluon vertex and its four-gluon (Jacobi)
consistency. -/
lemma gluon_lie_structure :
    ⁅A, B⁆ = -⁅B, A⁆
      ∧ ⁅A, A⁆ = 0
      ∧ ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 :=
  ⟨by rw [Ring.lie_def, Ring.lie_def]; abel, by rw [Ring.lie_def, sub_self],
    by simp only [Ring.lie_def]; noncomm_ring⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra

/-! ## Part II — the Gell-Mann matrices and the `su(3)` structure constants `f^{abc}` -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants

open Matrix Complex


/-- Gell-Mann matrix `λ₁`. -/
def lambda1 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
/-- Gell-Mann matrix `λ₂`. -/
noncomputable def lambda2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, -I, 0; I, 0, 0; 0, 0, 0]
/-- Gell-Mann matrix `λ₃`. -/
def lambda3 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
/-- Gell-Mann matrix `λ₄`. -/
def lambda4 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]
/-- Gell-Mann matrix `λ₅`. -/
noncomputable def lambda5 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, -I; 0, 0, 0; I, 0, 0]
/-- Gell-Mann matrix `λ₆`. -/
def lambda6 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]
/-- Gell-Mann matrix `λ₇`. -/
noncomputable def lambda7 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, -I; 0, I, 0]
/-- Gell-Mann matrix `λ₈ = diag(1,1,−2)/√3`. -/
noncomputable def lambda8 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(Real.sqrt 3 : ℂ)⁻¹, 0, 0; 0, (Real.sqrt 3 : ℂ)⁻¹, 0; 0, 0, -2 * (Real.sqrt 3 : ℂ)⁻¹]

/-- **[The Gell-Mann matrices are traceless]** `Tr λₐ = 0` — the `su(3)` generators are traceless. -/
lemma gellMann_traceless :
    trace lambda1 = 0 ∧ trace lambda2 = 0 ∧ trace lambda3 = 0 ∧ trace lambda4 = 0
      ∧ trace lambda5 = 0 ∧ trace lambda6 = 0 ∧ trace lambda7 = 0 ∧ trace lambda8 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three]
  ring


/-- **[`[λ₁,λ₂] = 2iλ₃`]** structure constant `f^{123} = 1` — the `(1,2,3)` generators form the embedded
`su(2)` (Pauli) subalgebra. -/
lemma comm_12 : lambda1 * lambda2 - lambda2 * lambda1 = (2 * I) • lambda3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda1, lambda2, lambda3, Matrix.sub_apply] <;> ring

/-- **[`[λ₂,λ₃] = 2iλ₁`]** the cyclic `su(2)` relation. -/
lemma comm_23 : lambda2 * lambda3 - lambda3 * lambda2 = (2 * I) • lambda1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda1, lambda2, lambda3, Matrix.sub_apply] <;> ring

/-- **[`[λ₃,λ₁] = 2iλ₂`]** the cyclic `su(2)` relation. -/
lemma comm_31 : lambda3 * lambda1 - lambda1 * lambda3 = (2 * I) • lambda2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda1, lambda2, lambda3, Matrix.sub_apply] <;>
      ring_nf <;> (try simp only [Complex.I_sq]) <;> ring


/-- **[`[λ₁,λ₄] = iλ₇`]** so `2i·f^{147} = i`, i.e. `f^{147} = 1/2` — a representative half-integer
structure constant linking different `su(2)` subblocks. -/
lemma comm_14 : lambda1 * lambda4 - lambda4 * lambda1 = I • lambda7 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda1, lambda4, lambda7, Matrix.sub_apply]

/-- **[`[λ₁,λ₅] = −iλ₆`]** so `2i·f^{156} = −i`, i.e. `f^{156} = −1/2` — a representative negative
half-integer structure constant. -/
lemma comm_15 : lambda1 * lambda5 - lambda5 * lambda1 = (-I) • lambda6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda1, lambda5, lambda6, Matrix.sub_apply]


/-- **[`[λ₄,λ₅] = iλ₃ + i√3 λ₈`]** so `2i·f^{453} = i` and `2i·f^{458} = i√3`, i.e. `f^{345} = 1/2` and the
distinctive `λ₈`-direction constant `f^{458} = √3/2` — the structure constant that reaches outside the `su(2)`
subblocks into the hypercharge generator `λ₈`. -/
lemma comm_45 :
    lambda4 * lambda5 - lambda5 * lambda4 = I • lambda3 + (I * (Real.sqrt 3 : ℂ)) • lambda8 := by
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda3, lambda4, lambda5, lambda8, Matrix.sub_apply, Matrix.add_apply]
  field_simp
  ring

/-- **[`[λ₆,λ₇] = −iλ₃ + i√3 λ₈`]** so `2i·f^{367} = −i` and `2i·f^{678} = i√3`, i.e. `f^{367} = −1/2` and the
second `λ₈`-direction constant `f^{678} = √3/2`. -/
lemma comm_67 :
    lambda6 * lambda7 - lambda7 * lambda6 = (-I) • lambda3 + (I * (Real.sqrt 3 : ℂ)) • lambda8 := by
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda3, lambda6, lambda7, lambda8, Matrix.sub_apply, Matrix.add_apply]
  field_simp
  ring


/-- **[Representative `su(3)` structure constants]** the commutators above give the canonical `f^{abc}`
values `f^{123} = 1` (`[λ₁,λ₂]=2iλ₃`, the `su(2)` subalgebra), `f^{147} = 1/2` (`[λ₁,λ₄]=iλ₇`), and the
distinctive `λ₈`-direction `f^{458} = √3/2` (`[λ₄,λ₅]=iλ₃+i√3λ₈`) — realizing the `Particles.GluonLieAlgebra` bracket
concretely on `su(3)`. -/
lemma gellMann_structure_constants :
    lambda1 * lambda2 - lambda2 * lambda1 = (2 * I) • lambda3
      ∧ lambda1 * lambda4 - lambda4 * lambda1 = I • lambda7
      ∧ lambda4 * lambda5 - lambda5 * lambda4 = I • lambda3 + (I * (Real.sqrt 3 : ℂ)) • lambda8 :=
  ⟨comm_12, comm_14, comm_45⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants

/-! ## Part III — Gell-Mann–Nishijima: the fractional charges from weak isospin and hypercharge -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima

open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding


/-- **The Gell-Mann–Nishijima electric charge** `Q = T₃ + Y/2` — electric charge from the third weak-isospin
component `T₃` and the weak hypercharge `Y`. -/
def gellMannNishijima (t3 y : ℚ) : ℚ := t3 + y / 2


/-- **[Up-type]** `T₃ = +1/2`, `Y = 1/3` ⟹ `Q = +2/3 = Q(up)`. -/
lemma gmn_up : gellMannNishijima (1 / 2) (1 / 3) = windingCharge upWinding := by
  rw [upQuark_charge]; unfold gellMannNishijima; norm_num

/-- **[Down-type]** `T₃ = −1/2`, `Y = 1/3` ⟹ `Q = −1/3 = Q(down)`. -/
lemma gmn_down : gellMannNishijima (-1 / 2) (1 / 3) = windingCharge downWinding := by
  rw [downQuark_charge]; unfold gellMannNishijima; norm_num

/-- **[Neutrino]** `T₃ = +1/2`, `Y = −1` ⟹ `Q = 0 = Q(ν)`. -/
lemma gmn_neutrino : gellMannNishijima (1 / 2) (-1) = windingCharge 0 := by
  rw [neutrino_charge]; unfold gellMannNishijima; norm_num

/-- **[Electron]** `T₃ = −1/2`, `Y = −1` ⟹ `Q = −1 = Q(e)`. -/
lemma gmn_electron : gellMannNishijima (-1 / 2) (-1) = windingCharge (-3) := by
  rw [electron_charge]; unfold gellMannNishijima; norm_num


/-- **[Hypercharge is the mean doublet charge]** `(Q₊ + Q₋)/2 = Y/2` — averaging the two members of a
weak-isospin doublet cancels `T₃ = ±1/2`, leaving `Y/2`. -/
lemma hypercharge_eq_average_doublet_charge (y : ℚ) :
    (gellMannNishijima (1 / 2) y + gellMannNishijima (-1 / 2) y) / 2 = y / 2 := by
  unfold gellMannNishijima; ring

/-- **[Doublet charge splitting]** `Q₊ − Q₋ = ΔT₃ = 1` — the two members of a doublet differ in charge by
exactly `1` (the `W` charge), independent of the hypercharge. -/
lemma doublet_charge_splitting (y : ℚ) :
    gellMannNishijima (1 / 2) y - gellMannNishijima (-1 / 2) y = 1 := by
  unfold gellMannNishijima; ring

end Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra.gluon_jacobi where
  formalizes @ "claim:the-gluon-vertex-bracket-satisfies-the-cyclic-jacobi-identity",
  supported_by @ "paper:yang-mills-1954-isotopic-gauge-invariance"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants.gellMann_structure_constants where
  formalizes @ "claim:the-su3-structure-constants-realize-the-gluon-bracket-concretely",
  requires @ "claim:the-gluon-vertex-bracket-satisfies-the-cyclic-jacobi-identity",
  supported_by @ "paper:gell-mann-1962-symmetries-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima.gmn_up where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.upQuark_charge",
  formalizes @ "claim:gell-mann-nishijima-derives-the-fractional-quark-charges-from-isospin-and-hypercharge",
  caveat @ "claim:the-weak-isospin-and-hypercharge-assignments-are-empirical-standard-model-structure"

zil_file_contract physlib.gellMannStructureConstants where
  promises "The su(3) colour algebra: the gluon vertex bracket satisfies the cyclic Jacobi identity, the eight Gell-Mann commutators realize the structure constants concretely, and Gell-Mann-Nishijima derives the fractional quark charges from weak isospin and hypercharge."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants.lambda1",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima.gellMannNishijima"]
  forbids_substitutes ["the gauge-field dynamics, not built here",
    "the weak isospin and hypercharge multiplet assignments, which are empirical"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra.gluon_jacobi,
    Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants.gellMann_structure_constants,
    Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima.gmn_up]

/- ZIL-END -/
