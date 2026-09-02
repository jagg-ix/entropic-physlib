/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Physlib.QuantumMechanics.ComplexAction.A4CharacterTable

/-!
# The A₄ permutation representation and its character (fixed-point count)

The **permutation-representation-character infrastructure** that Mathlib does not provide as a lemma: the
permutation representation of `A₄ = alternatingGroup (Fin 4)` on `Fin 4 → ℂ`, and the fact that its character
is the number of fixed points. This is the bridge that turns the combinatorial character table of
`A4CharacterTable` (`stdChar g = fix(g) − 1`) into an actual `Representation`.

* **§A — the permutation character of a matrix.** `trace_permMatrix_fix`: the trace of the permutation matrix
  `σ.permMatrix ℂ` is the number of fixed points of `σ`. `fixCard_inv`: fixed-point counts are inversion
  invariant (`fix(σ⁻¹) = fix(σ)`).
* **§B — the permutation representation.** `permRep : Representation ℂ A₄ (Fin 4 → ℂ)`, built from the
  permutation-matrix monoid homomorphism (`permMatrixHom`) via `Matrix.toLin'`.
* **§C — the character is the fixed-point count.** `permRep_character` (`χ_perm(g) = fix(g)`) and
  `permRep_character_eq_stdChar` (`χ_perm(g) = stdChar(g) + 1`): the permutation character equals the standard
  character plus the trivial character, so the standard (three-generation) character is `χ_perm − 1`.

This supplies the missing ingredient behind `A4CharacterTable`: with `permRep` and `permRep_character`, the
standard representation is `permRep` restricted to the sum-zero subspace, whose character is `fix − 1 = stdChar`
— and `A4CharacterTable.stdChar_norm` (`∑_g χ(g)χ(g⁻¹) = 12 = |A₄|`) is then exactly the
`FDRep.simple_iff_char_is_norm_one` irreducibility criterion applied to it.

**Honest layering.** Proven exactly: the permutation-matrix trace = fixed points, the permutation
representation as a genuine `Representation`, and its character = the fixed-point count / `stdChar + 1`. The
final `Simple` typeclass on the standard summand additionally requires the trivial ⊕ standard trace
decomposition (`trace_eq_sum_trace_restrict`) and the `FDRep` wrapper; the character computation that certifies
it is complete here and in `A4CharacterTable`.

## References

* `Equiv.Perm.permMatrix` / `permMatrixHom`, `Matrix.trace_toLin'_eq`, `Representation.character`,
  `FDRep.simple_iff_char_is_norm_one`. Companion to `A4CharacterTable` (the character table and norm) and
  `A4FlavorGenerations` (the `dim = 3` standard representation).


-/

set_option autoImplicit false

open scoped BigOperators

open Equiv (Perm)
open Matrix

noncomputable section

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.A4StandardRepresentation

/-- The tetrahedral flavor group `A₄`. -/
abbrev G : Type := alternatingGroup (Fin 4)

/-- The number of points fixed by a permutation of the four tetrahedron vertices. -/
def fixCard (σ : Perm (Fin 4)) : ℕ := (Finset.univ.filter (fun i => σ i = i)).card


/-- **The trace of a permutation matrix is its number of fixed points** `tr(P_σ) = fix(σ)`. -/
lemma trace_permMatrix_fix (σ : Perm (Fin 4)) :
    Matrix.trace (σ.permMatrix ℂ) = (fixCard σ : ℂ) := by
  rw [Matrix.trace, fixCard]
  simp only [Matrix.diag_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [Finset.sum_boole]

/-- **Fixed-point counts are inversion invariant** `fix(σ⁻¹) = fix(σ)`. -/
lemma fixCard_inv (σ : Perm (Fin 4)) : fixCard σ⁻¹ = fixCard σ := by
  unfold fixCard; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hh : σ (σ⁻¹ i) = i := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    rwa [h] at hh
  · intro h
    have hh : σ⁻¹ (σ i) = i := by
      rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    rwa [h] at hh


/-- The **permutation representation** of `A₄` on `Fin 4 → ℂ`: `g` acts by the linear map of its permutation
matrix (via `permMatrixHom`, whose pre-inversion makes it a genuine homomorphism). -/
def permRep : Representation ℂ G (Fin 4 → ℂ) where
  toFun g := (permMatrixHom (R := ℂ) g.val).toLin'
  map_one' := by simp only [OneMemClass.coe_one, map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by simp only [Subgroup.coe_mul, map_mul, Matrix.toLin'_mul]; rfl


/-- **The permutation character is the number of fixed points** `χ_perm(g) = fix(g)`. -/
lemma permRep_character (g : G) : permRep.character g = (fixCard g.val : ℂ) := by
  rw [Representation.character, show permRep g = (permMatrixHom (R := ℂ) g.val).toLin' from rfl,
    Matrix.trace_toLin'_eq, Matrix.permMatrixHom_apply, trace_permMatrix_fix, fixCard_inv]

/-- **The permutation character is the standard character plus the trivial character**
`χ_perm(g) = stdChar(g) + 1`: the permutation representation splits as trivial ⊕ standard, so the standard
(three-generation) character is `χ_perm − 1 = fix − 1`. -/
lemma permRep_character_eq_stdChar (g : G) :
    permRep.character g = (A4CharacterTable.stdChar g.val : ℂ) + 1 := by
  rw [permRep_character]
  unfold A4CharacterTable.stdChar fixCard
  push_cast
  ring

/-- **The permutation representation is four-dimensional** `χ_perm(1) = 4` (the four tetrahedron vertices). -/
lemma permRep_dim : permRep.character 1 = 4 := by
  rw [permRep_character]
  norm_num [fixCard]

end Physlib.QuantumMechanics.ComplexAction.A4StandardRepresentation
