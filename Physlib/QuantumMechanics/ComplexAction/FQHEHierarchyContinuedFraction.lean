/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
import Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean
meta import Zil

/-!
# The FQHE hierarchy filling fraction as a continued fraction

Fujita–Li–Ryu–Takayanagi, *Fractional Quantum Hall Effect via Holography* (arXiv:0901.0924), Eq. (1.2): the
generic (hierarchical) FQHE filling fractions are the continued fractions

`ν = 1 / (a₁ − 1 / (a₂ − 1 / (a₃ − ⋯)))`,

each level `aᵢ` a Chern–Simons gauge field whose quasiparticles are the constituents of the next level
(the "hierarchy").  This formalizes that structure as a recursion on the list of levels, extending the
repository's Laughlin `ν = 1/m` (`FractionalQuantumHallHalfFilling.laughlinFilling`) to the whole hierarchy.

* `hierarchyLevel` — the denominator `a₁ − 1/(a₂ − ⋯)` (recursion `1/0 = 0` terminates the tail).
* `hierarchyFilling` — the filling fraction `ν = 1/hierarchyLevel`.
* `hierarchyFilling_cons` — the hierarchy recursion `ν(a::as) = 1/(a − ν(as))`.
* `laughlin_base`, `hierarchyFilling_single_eq_laughlinFilling` — a one-level hierarchy is Laughlin `1/k`.
* `jain_two_fifths`, `jain_three_sevenths` — the observed Jain states `2/5 = ⟨3,2⟩`, `3/7 = ⟨3,2,2⟩` are
  instances of the general recursion, not fitted values.

This is the same rational / continued-fraction arithmetic as the rational Lorentz boosts of
`RationalBoostPythagorean` (both are rational points built by a Möbius/`SL(2,ℤ)` iteration); here it produces
Hall filling fractions rather than boost velocities.

The first two nontrivial hierarchy depths are also realized by explicit integral
Chern--Simons `K`-matrices.  Their inverses are checked on both sides and their
charge contractions `tᵀK⁻¹t` are proved equal to the continued fractions.  This
closes the `K`-matrix gap for the observed `2/5` and `3/7` Jain states without
pretending that two examples constitute an arbitrary-rank construction.

Honest scope: the algebraic continued-fraction structure of the filling fractions
(Eq. 1.2), its Laughlin base, and explicit rank-two/rank-three `K`-matrix
realizations.  An arbitrary-rank integral `K`-matrix construction and the
holographic brane embedding are not built here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction

open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
open Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean

/-! ## A. Hierarchy recursion -/

/-- **The hierarchy denominator** `a₁ − 1/(a₂ − 1/(a₃ − ⋯))` on a list of Chern–Simons levels.  The empty
tail gives `0`, so `1/0 = 0` terminates the continued fraction (`hierarchyLevel [a] = a`). -/
def hierarchyLevel : List ℝ → ℝ
  | [] => 0
  | a :: as => a - 1 / hierarchyLevel as

/-- **The hierarchy filling fraction** `ν = 1/(a₁ − 1/(a₂ − ⋯))` (Eq. 1.2). -/
def hierarchyFilling (as : List ℝ) : ℝ := 1 / hierarchyLevel as

/-- **The hierarchy denominator recursion** `a₁ − 1/(a₂ − ⋯)`. -/
theorem hierarchyLevel_cons (a : ℝ) (as : List ℝ) :
    hierarchyLevel (a :: as) = a - 1 / hierarchyLevel as := rfl

/-- **A one-level hierarchy denominator is the level itself** `hierarchyLevel [k] = k`. -/
theorem hierarchyLevel_single (k : ℝ) : hierarchyLevel [k] = k := by
  simp [hierarchyLevel]

/-- **The hierarchy recursion** `ν(a::as) = 1/(a − ν(as))` — each level's filling is `1` over its level minus
the filling of the sub-hierarchy it is built on. -/
theorem hierarchyFilling_cons (a : ℝ) (as : List ℝ) :
    hierarchyFilling (a :: as) = 1 / (a - hierarchyFilling as) := by
  unfold hierarchyFilling
  rw [hierarchyLevel_cons]

/-- **The Laughlin base** `ν = 1/k` — a single-level hierarchy is the Laughlin state. -/
theorem laughlin_base (k : ℝ) : hierarchyFilling [k] = 1 / k := by
  unfold hierarchyFilling
  rw [hierarchyLevel_single]

/-- **A one-level hierarchy is the repository's Laughlin filling** `hierarchyFilling [k] = laughlinFilling k`. -/
theorem hierarchyFilling_single_eq_laughlinFilling (k : ℝ) :
    hierarchyFilling [k] = laughlinFilling k := by
  rw [laughlin_base, laughlinFilling]

/-! ## B. Determinant-one Möbius realization -/

/-- The determinant-one matrix whose fractional-linear action is one hierarchy
step, `x ↦ 1 / (a - x)`.  It records the genuine `SL(2, ℝ)` arithmetic shared
by continued fractions without identifying Hall states with Lorentz boosts. -/
noncomputable def hierarchyMobiusMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, a]

/-- Every hierarchy-step matrix has determinant one. -/
lemma hierarchyMobiusMatrix_det (a : ℝ) : (hierarchyMobiusMatrix a).det = 1 := by
  simp [hierarchyMobiusMatrix, Matrix.det_fin_two]

/-- The hierarchy recursion is exactly the fractional-linear action of
`hierarchyMobiusMatrix a` on the filling of the remaining hierarchy. -/
@[zil_level bridge_theorem]
lemma hierarchyFilling_cons_eq_mobius (a : ℝ) (as : List ℝ) :
    hierarchyFilling (a :: as) =
      ((hierarchyMobiusMatrix a) 0 0 * hierarchyFilling as +
          (hierarchyMobiusMatrix a) 0 1) /
        ((hierarchyMobiusMatrix a) 1 0 * hierarchyFilling as +
          (hierarchyMobiusMatrix a) 1 1) := by
  simp [hierarchyFilling_cons, hierarchyMobiusMatrix]
  ring

/-! ## C. The complete `p = 1` Jain family -/

/-- A tail of `n` hierarchy levels equal to two has filling `n/(n+1)`.
This is the induction that turns the isolated `2/5` and `3/7` checks into a
uniform hierarchy theorem. -/
lemma hierarchyFilling_replicate_two (n : ℕ) :
    hierarchyFilling (List.replicate n (2 : ℝ)) = (n : ℝ) / (n + 1) := by
  induction n with
  | zero => norm_num [hierarchyFilling, hierarchyLevel]
  | succ n ih =>
      rw [List.replicate_succ, hierarchyFilling_cons, ih]
      push_cast
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hden : 2 - (n : ℝ) / (n + 1) = (n + 2) / (n + 1) := by
        field_simp [hn1]
        ring
      rw [hden, one_div_div]
      ring

/-- Prepending level three to `n` level-two descendants gives the closed form
`(n+1)/(2(n+1)+1)`. -/
lemma hierarchyFilling_three_cons_replicate_two (n : ℕ) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
      ((n : ℝ) + 1) / (2 * ((n : ℝ) + 1) + 1) := by
  rw [hierarchyFilling_cons, hierarchyFilling_replicate_two]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : 3 - (n : ℝ) / (n + 1) =
      (2 * ((n : ℝ) + 1) + 1) / (n + 1) := by
    field_simp [hn1]
    ring
  rw [hden, one_div_div]

/-- The entire hierarchy `[3, 2, ..., 2]` is the repository's `p = 1` Jain
sequence, not merely the first two observed examples. -/
@[zil_level physical_theorem]
lemma hierarchyFilling_jain_sequence (n : ℕ) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
      jainFilling ((n : ℝ) + 1) 1 := by
  rw [hierarchyFilling_three_cons_replicate_two]
  simp [jainFilling]

/-- **[Jain `2/5`] `hierarchyFilling ⟨3,2⟩ = 2/5`.**  The observed second-hierarchy state, an instance of the
general recursion. -/
theorem jain_two_fifths : hierarchyFilling [3, 2] = 2 / 5 := by
  have h := hierarchyFilling_jain_sequence 1
  norm_num [jainFilling] at h ⊢
  exact h

/-- **[Jain `3/7`] `hierarchyFilling ⟨3,2,2⟩ = 3/7`.**  The observed third-hierarchy state. -/
theorem jain_three_sevenths : hierarchyFilling [3, 2, 2] = 3 / 7 := by
  have h := hierarchyFilling_jain_sequence 2
  norm_num [jainFilling] at h ⊢
  exact h

/-! ## D. Explicit hierarchy `K`-matrices -/

/-- The rank-two hierarchy matrix with adjacent Chern--Simons coupling one. -/
noncomputable def hierarchyKMatrix2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 1; 1, b]

/-- The displayed inverse of the rank-two hierarchy matrix. -/
noncomputable def hierarchyKInverse2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (a * b - 1)) • !![b, -1; -1, a]

/-- The electromagnetic charge vector selecting the first hierarchy gauge
field at rank two. -/
def hierarchyChargeVector2 : Fin 2 → ℝ := ![1, 0]

/-- The rank-two `K`-matrix filling formula `tᵀK⁻¹t`. -/
noncomputable def hierarchyFillingFromK2 (a b : ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    hierarchyChargeVector2 i * hierarchyKInverse2 a b i j * hierarchyChargeVector2 j

/-- A terminal rank-two hierarchy quasiparticle.  The minus sign fixes the
orientation convention so that `tᵀK⁻¹ℓ` is the positive elementary charge
fraction for the `K`-matrix convention used in this file. -/
def hierarchyTerminalQuasiparticle2 : Fin 2 → ℝ := ![0, -1]

/-- The terminal quasiparticle charge in electron-charge units, computed by
the standard Abelian Chern--Simons contraction `tᵀK⁻¹ℓ`. -/
noncomputable def hierarchyTerminalQuasiparticleCharge2 (a b : ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    hierarchyChargeVector2 i * hierarchyKInverse2 a b i j *
      hierarchyTerminalQuasiparticle2 j

/-- The determinant of the rank-two hierarchy matrix is `ab - 1`. -/
lemma hierarchyKMatrix2_det (a b : ℝ) :
    (hierarchyKMatrix2 a b).det = a * b - 1 := by
  simp [hierarchyKMatrix2, Matrix.det_fin_two]

/-- The displayed rank-two inverse is a left inverse when the determinant is
nonzero. -/
lemma hierarchyKInverse2_mul_KMatrix2 (a b : ℝ) (hdet : a * b - 1 ≠ 0) :
    hierarchyKInverse2 a b * hierarchyKMatrix2 a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchyKInverse2, hierarchyKMatrix2, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    field_simp [hdet] <;> ring

/-- The displayed rank-two inverse is a right inverse when the determinant is
nonzero. -/
lemma hierarchyKMatrix2_mul_KInverse2 (a b : ℝ) (hdet : a * b - 1 ≠ 0) :
    hierarchyKMatrix2 a b * hierarchyKInverse2 a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchyKInverse2, hierarchyKMatrix2, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    field_simp [hdet] <;> ring

/-- Contracting the rank-two inverse with `t=(1,0)` gives `b/(ab-1)`. -/
lemma hierarchyFillingFromK2_eq (a b : ℝ) :
    hierarchyFillingFromK2 a b = b / (a * b - 1) := by
  simp [hierarchyFillingFromK2, hierarchyChargeVector2, hierarchyKInverse2,
    Fin.sum_univ_two, div_eq_mul_inv, mul_comm]

/-- The selected terminal rank-two excitation has elementary charge fraction
`1/(ab-1)`. -/
lemma hierarchyTerminalQuasiparticleCharge2_eq (a b : ℝ) :
    hierarchyTerminalQuasiparticleCharge2 a b = 1 / (a * b - 1) := by
  simp [hierarchyTerminalQuasiparticleCharge2, hierarchyChargeVector2,
    hierarchyTerminalQuasiparticle2, hierarchyKInverse2, Fin.sum_univ_two,
    div_eq_mul_inv, mul_comm]

/-- The two-level continued fraction is exactly the rank-two `K`-matrix charge
contraction. -/
@[zil_level bridge_theorem]
lemma hierarchyFilling_two_eq_fromK (a b : ℝ) (hb : b ≠ 0) :
    hierarchyFilling [a, b] = hierarchyFillingFromK2 a b := by
  rw [hierarchyFilling_cons, laughlin_base, hierarchyFillingFromK2_eq]
  field_simp [hb]

/-- The rank-three hierarchy matrix with nearest-neighbor Chern--Simons
couplings. -/
noncomputable def hierarchyKMatrix3 (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, 1, 0; 1, b, 1; 0, 1, c]

/-- The explicit adjugate of the rank-three hierarchy matrix. -/
noncomputable def hierarchyKAdjugate3 (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![b * c - 1, -c, 1; -c, a * c, -a; 1, -a, a * b - 1]

/-- The adjugate-over-determinant inverse of the rank-three hierarchy matrix. -/
noncomputable def hierarchyKInverse3 (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (a * b * c - a - c)⁻¹ • hierarchyKAdjugate3 a b c

/-- The electromagnetic charge vector selecting the first hierarchy gauge
field at rank three. -/
def hierarchyChargeVector3 : Fin 3 → ℝ := ![1, 0, 0]

/-- The rank-three `K`-matrix filling formula `tᵀK⁻¹t`. -/
noncomputable def hierarchyFillingFromK3 (a b c : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    hierarchyChargeVector3 i * hierarchyKInverse3 a b c i j * hierarchyChargeVector3 j

/-- A terminal rank-three hierarchy quasiparticle. -/
def hierarchyTerminalQuasiparticle3 : Fin 3 → ℝ := ![0, 0, 1]

/-- The terminal rank-three quasiparticle charge in electron-charge units,
again computed as `tᵀK⁻¹ℓ`. -/
noncomputable def hierarchyTerminalQuasiparticleCharge3 (a b c : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    hierarchyChargeVector3 i * hierarchyKInverse3 a b c i j *
      hierarchyTerminalQuasiparticle3 j

/-- The determinant of the rank-three hierarchy matrix is `abc-a-c`. -/
lemma hierarchyKMatrix3_det (a b c : ℝ) :
    (hierarchyKMatrix3 a b c).det = a * b * c - a - c := by
  simp [hierarchyKMatrix3, Matrix.det_fin_three]

/-- The rank-three adjugate times the hierarchy matrix is its determinant times
the identity. -/
lemma hierarchyKAdjugate3_mul_KMatrix3 (a b c : ℝ) :
    hierarchyKAdjugate3 a b c * hierarchyKMatrix3 a b c =
      (a * b * c - a - c) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchyKAdjugate3, hierarchyKMatrix3, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

/-- The rank-three hierarchy matrix times its adjugate is its determinant times
the identity. -/
lemma hierarchyKMatrix3_mul_KAdjugate3 (a b c : ℝ) :
    hierarchyKMatrix3 a b c * hierarchyKAdjugate3 a b c =
      (a * b * c - a - c) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchyKAdjugate3, hierarchyKMatrix3, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

/-- The displayed rank-three inverse is a left inverse when the determinant is
nonzero. -/
lemma hierarchyKInverse3_mul_KMatrix3 (a b c : ℝ)
    (hdet : a * b * c - a - c ≠ 0) :
    hierarchyKInverse3 a b c * hierarchyKMatrix3 a b c = 1 := by
  rw [hierarchyKInverse3, Matrix.smul_mul,
    hierarchyKAdjugate3_mul_KMatrix3, smul_smul, inv_mul_cancel₀ hdet,
    one_smul]

/-- The displayed rank-three inverse is a right inverse when the determinant is
nonzero. -/
lemma hierarchyKMatrix3_mul_KInverse3 (a b c : ℝ)
    (hdet : a * b * c - a - c ≠ 0) :
    hierarchyKMatrix3 a b c * hierarchyKInverse3 a b c = 1 := by
  rw [hierarchyKInverse3, Matrix.mul_smul,
    hierarchyKMatrix3_mul_KAdjugate3, smul_smul, inv_mul_cancel₀ hdet,
    one_smul]

/-- Contracting the rank-three inverse with `t=(1,0,0)` gives the ratio of
successive continuants `(bc-1)/(abc-a-c)`. -/
lemma hierarchyFillingFromK3_eq (a b c : ℝ) :
    hierarchyFillingFromK3 a b c =
      (b * c - 1) / (a * b * c - a - c) := by
  simp [hierarchyFillingFromK3, hierarchyChargeVector3, hierarchyKInverse3,
    hierarchyKAdjugate3, Fin.sum_univ_three, div_eq_mul_inv, mul_comm]

/-- The selected terminal rank-three excitation has elementary charge fraction
`1/(abc-a-c)`. -/
lemma hierarchyTerminalQuasiparticleCharge3_eq (a b c : ℝ) :
    hierarchyTerminalQuasiparticleCharge3 a b c =
      1 / (a * b * c - a - c) := by
  simp [hierarchyTerminalQuasiparticleCharge3, hierarchyChargeVector3,
    hierarchyTerminalQuasiparticle3, hierarchyKInverse3, hierarchyKAdjugate3,
    Fin.sum_univ_three, div_eq_mul_inv, mul_comm]

/-- The three-level continued fraction is exactly the rank-three `K`-matrix
charge contraction. -/
@[zil_level bridge_theorem]
lemma hierarchyFilling_three_eq_fromK (a b c : ℝ) (hc : c ≠ 0)
    (hbc : b * c - 1 ≠ 0) :
    hierarchyFilling [a, b, c] = hierarchyFillingFromK3 a b c := by
  rw [hierarchyFilling_cons, hierarchyFilling_cons, laughlin_base,
    hierarchyFillingFromK3_eq]
  field_simp [hc, hbc]

/-! ## E. Observed Jain states from the checked matrices -/

/-- The observed `2/5` state has a nonsingular rank-two `K`-matrix of
determinant five, and its filling is obtained from `tᵀK⁻¹t`. -/
@[zil_level physical_theorem]
lemma jain_two_fifths_kmatrix_derivation :
    (hierarchyKMatrix2 3 2).det = 5 ∧
      hierarchyKInverse2 3 2 * hierarchyKMatrix2 3 2 = 1 ∧
      hierarchyKMatrix2 3 2 * hierarchyKInverse2 3 2 = 1 ∧
      hierarchyFilling [3, 2] = hierarchyFillingFromK2 3 2 ∧
      hierarchyFillingFromK2 3 2 = 2 / 5 := by
  exact ⟨by norm_num [hierarchyKMatrix2_det],
    hierarchyKInverse2_mul_KMatrix2 3 2 (by norm_num),
    hierarchyKMatrix2_mul_KInverse2 3 2 (by norm_num),
    hierarchyFilling_two_eq_fromK 3 2 (by norm_num),
    by norm_num [hierarchyFillingFromK2_eq]⟩

/-- The observed `3/7` state has a nonsingular rank-three `K`-matrix of
determinant seven, and its filling is obtained from `tᵀK⁻¹t`. -/
@[zil_level physical_theorem]
lemma jain_three_sevenths_kmatrix_derivation :
    (hierarchyKMatrix3 3 2 2).det = 7 ∧
      hierarchyKInverse3 3 2 2 * hierarchyKMatrix3 3 2 2 = 1 ∧
      hierarchyKMatrix3 3 2 2 * hierarchyKInverse3 3 2 2 = 1 ∧
      hierarchyFilling [3, 2, 2] = hierarchyFillingFromK3 3 2 2 ∧
      hierarchyFillingFromK3 3 2 2 = 3 / 7 := by
  exact ⟨by norm_num [hierarchyKMatrix3_det],
    hierarchyKInverse3_mul_KMatrix3 3 2 2 (by norm_num),
    hierarchyKMatrix3_mul_KInverse3 3 2 2 (by norm_num),
    hierarchyFilling_three_eq_fromK 3 2 2 (by norm_num) (by norm_num),
    by norm_num [hierarchyFillingFromK3_eq]⟩

/-! ## F. Cayley embedding of fillings into the rational boost hyperbola -/

/-- The positive-filling Cayley energy coordinate
`(1+ν²)/(2ν)`.  It is a dimensionless mathematical embedding coordinate, not
the physical energy of a Hall sample. -/
noncomputable def fillingCayleyEnergy (ν : ℝ) : ℝ :=
  (1 + ν ^ 2) / (2 * ν)

/-- The positive-filling Cayley momentum coordinate
`(1-ν²)/(2ν)`. -/
noncomputable def fillingCayleyMomentum (ν : ℝ) : ℝ :=
  (1 - ν ^ 2) / (2 * ν)

/-- The Cayley velocity coordinate `(1-ν²)/(1+ν²)`. -/
noncomputable def fillingCayleyVelocity (ν : ℝ) : ℝ :=
  (1 - ν ^ 2) / (1 + ν ^ 2)

/-- Applying the repository's rational-boost law at `k=ν⁻¹` identifies the
Cayley energy coordinate with `cosh(log ν⁻¹)`. -/
lemma cosh_log_inv_filling (ν : ℝ) (hν : 0 < ν) :
    Real.cosh (Real.log ν⁻¹) = fillingCayleyEnergy ν := by
  rw [cosh_log ν⁻¹ (inv_pos.mpr hν)]
  simp only [fillingCayleyEnergy]
  field_simp [hν.ne']

/-- Applying the rational-boost law at `k=ν⁻¹` identifies the Cayley momentum
coordinate with `sinh(log ν⁻¹)`. -/
lemma sinh_log_inv_filling (ν : ℝ) (hν : 0 < ν) :
    Real.sinh (Real.log ν⁻¹) = fillingCayleyMomentum ν := by
  rw [sinh_log ν⁻¹ (inv_pos.mpr hν)]
  simp only [fillingCayleyMomentum]
  field_simp [hν.ne']

/-- Applying the rational-boost law at `k=ν⁻¹` identifies the Cayley velocity
with `tanh(log ν⁻¹)`. -/
lemma tanh_log_inv_filling (ν : ℝ) (hν : 0 < ν) :
    Real.tanh (Real.log ν⁻¹) = fillingCayleyVelocity ν := by
  rw [tanh_log ν⁻¹ (inv_pos.mpr hν)]
  simp only [fillingCayleyVelocity]
  field_simp [hν.ne']

/-- The filling-coordinate triple obeys Euclid's universal Pythagorean law.
This is the sign-reversed first leg of `rationalBoost_pythagorean`; the square
removes that orientation choice. -/
lemma fillingCayley_pythagorean (ν : ℝ) :
    (1 - ν ^ 2) ^ 2 + (2 * ν) ^ 2 = (1 + ν ^ 2) ^ 2 := by
  convert rationalBoost_pythagorean ν using 1 <;> ring

/-- The Cayley energy and momentum coordinates lie on the unit hyperbola.  The
proof reuses the existing rational-boost mass-shell theorem at `ν⁻¹`. -/
@[zil_level bridge_theorem]
lemma fillingCayley_massShell (ν : ℝ) (hν : 0 < ν) :
    fillingCayleyEnergy ν ^ 2 - fillingCayleyMomentum ν ^ 2 = 1 := by
  rw [← cosh_log_inv_filling ν hν, ← sinh_log_inv_filling ν hν]
  exact rationalBoost_massShell ν⁻¹ (inv_pos.mpr hν)

/-- Every positive hierarchical filling has a canonical Cayley presentation
as a rational-boost hyperbola point.  This packages the three hyperbolic
coordinates and the mass shell without identifying the physical meanings of
Hall filling and spacetime velocity. -/
@[zil_level bridge_theorem]
lemma hierarchyFilling_cayley_rationalBoost (as : List ℝ)
    (hν : 0 < hierarchyFilling as) :
    Real.cosh (Real.log (hierarchyFilling as)⁻¹) =
        fillingCayleyEnergy (hierarchyFilling as) ∧
      Real.sinh (Real.log (hierarchyFilling as)⁻¹) =
        fillingCayleyMomentum (hierarchyFilling as) ∧
      Real.tanh (Real.log (hierarchyFilling as)⁻¹) =
        fillingCayleyVelocity (hierarchyFilling as) ∧
      fillingCayleyEnergy (hierarchyFilling as) ^ 2 -
        fillingCayleyMomentum (hierarchyFilling as) ^ 2 = 1 := by
  exact ⟨cosh_log_inv_filling _ hν, sinh_log_inv_filling _ hν,
    tanh_log_inv_filling _ hν, fillingCayley_massShell _ hν⟩

/-- The whole `p=1` Jain sequence has the rational Cayley velocity obtained
from numerator `p=n+1` and denominator `q=2p+1`:
`β=(q²-p²)/(q²+p²)`.  Thus the observed `2/5` and `3/7` cases are again
instances of a single family theorem. -/
@[zil_level physical_theorem]
lemma jainHierarchy_cayleyVelocity (n : ℕ) :
    fillingCayleyVelocity
        (hierarchyFilling ((3 : ℝ) :: List.replicate n 2)) =
      ((2 * ((n : ℝ) + 1) + 1) ^ 2 - ((n : ℝ) + 1) ^ 2) /
        ((2 * ((n : ℝ) + 1) + 1) ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  rw [hierarchyFilling_three_cons_replicate_two]
  simp only [fillingCayleyVelocity]
  have hp : (n : ℝ) + 1 ≠ 0 := by positivity
  have hq : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  have hsum :
      (2 * ((n : ℝ) + 1) + 1) ^ 2 + ((n : ℝ) + 1) ^ 2 ≠ 0 := by
    positivity
  field_simp [hp, hq, hsum]

/-! ## G. Contact with measured Hall response -/

/-- The checked `2/5` hierarchy state has dimensionless Hall conductance
`σ_xy /(e²/h) = 2/5`, using the repository's standard Hall-response
normalization `hallConductanceUnits ν = ν`. -/
@[zil_level physical_theorem]
lemma jain_two_fifths_hallConductance :
    hallConductanceUnits (hierarchyFilling [3, 2]) = 2 / 5 := by
  simpa [hallConductanceUnits] using jain_two_fifths

/-- The checked `3/7` hierarchy state has dimensionless Hall conductance
`σ_xy /(e²/h) = 3/7`. -/
@[zil_level physical_theorem]
lemma jain_three_sevenths_hallConductance :
    hallConductanceUnits (hierarchyFilling [3, 2, 2]) = 3 / 7 := by
  simpa [hallConductanceUnits] using jain_three_sevenths

/-- The `2/5` plateau has transverse resistivity `5/2` in units of `h/e²`.
This is the reciprocal-response consequence of its checked filling. -/
@[zil_level physical_theorem]
lemma jain_two_fifths_hallResistivity :
    hallResistivityUnits (hierarchyFilling [3, 2]) = 5 / 2 := by
  rw [jain_two_fifths]
  norm_num [hallResistivityUnits]

/-- The `3/7` plateau has transverse resistivity `7/3` in units of `h/e²`. -/
@[zil_level physical_theorem]
lemma jain_three_sevenths_hallResistivity :
    hallResistivityUnits (hierarchyFilling [3, 2, 2]) = 7 / 3 := by
  rw [jain_three_sevenths]
  norm_num [hallResistivityUnits]

/-- The determinant-five `2/5` hierarchy matrix gives a terminal
quasiparticle of charge `e/5` in the standard K-matrix coupling. -/
@[zil_level physical_theorem]
lemma jain_two_fifths_terminalQuasiparticleCharge :
    hierarchyTerminalQuasiparticleCharge2 3 2 = 1 / 5 := by
  norm_num [hierarchyTerminalQuasiparticleCharge2_eq]

/-- The determinant-seven `3/7` hierarchy matrix gives a terminal
quasiparticle of charge `e/7` in the standard K-matrix coupling. -/
@[zil_level physical_theorem]
lemma jain_three_sevenths_terminalQuasiparticleCharge :
    hierarchyTerminalQuasiparticleCharge3 3 2 2 = 1 / 7 := by
  norm_num [hierarchyTerminalQuasiparticleCharge3_eq]

end Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_cons_eq_mobius where
  formalizes @ "claim:each-fqhe-hierarchy-level-is-a-determinant-one-mobius-step-on-the-tail-filling",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  caveat @ "claim:the-shared-mobius-arithmetic-does-not-identify-fqhe-hall-states-with-lorentz-boosts"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence where
  formalizes @ "claim:the-level-list-three-followed-by-n-twos-realizes-the-entire-p-one-jain-filling-sequence",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.jainFilling"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_two_eq_fromK where
  formalizes @ "claim:the-two-level-hierarchy-filling-is-the-charge-contraction-of-the-explicit-rank-two-chern-simons-k-matrix",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  caveat @ "claim:the-denominator-level-is-required-nonzero-because-the-list-recursion-uses-totalized-real-division"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_three_eq_fromK where
  formalizes @ "claim:the-three-level-hierarchy-filling-is-the-charge-contraction-of-the-explicit-rank-three-chern-simons-k-matrix",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  caveat @ "claim:the-tail-continuants-are-required-nonzero-because-the-list-recursion-uses-totalized-real-division"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_kmatrix_derivation where
  derives @ "claim:jain-two-fifths-from-a-nonsingular-determinant-five-rank-two-k-matrix",
  standard_physics_postulates @ "postulate:abelian-chern-simons-k-matrix-charge-vector-coupling",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  caveat @ "claim:this-derives-the-filling-and-determinant-from-the-selected-integral-k-matrix-not-the-experimental-selection-of-that-topological-phase"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_kmatrix_derivation where
  derives @ "claim:jain-three-sevenths-from-a-nonsingular-determinant-seven-rank-three-k-matrix",
  standard_physics_postulates @ "postulate:abelian-chern-simons-k-matrix-charge-vector-coupling",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  caveat @ "claim:this-derives-the-filling-and-determinant-from-the-selected-integral-k-matrix-not-the-experimental-selection-of-that-topological-phase"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.fillingCayley_massShell where
  formalizes @ "claim:every-positive-filling-cayley-coordinate-lies-on-the-rational-boost-unit-hyperbola",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.rationalBoost_massShell",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-a-dimensionless-cayley-embedding-not-an-identification-of-hall-filling-with-physical-spacetime-velocity"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_cayley_rationalBoost where
  formalizes @ "claim:every-positive-hierarchical-fqhe-filling-has-the-cosh-sinh-tanh-cayley-presentation-at-log-inverse-filling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.cosh_log",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.sinh_log",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.tanh_log",
  caveat @ "claim:the-shared-sl-two-rational-geometry-does-not-equate-the-physical-observables-of-the-two-sectors"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jainHierarchy_cayleyVelocity where
  formalizes @ "claim:the-entire-p-one-jain-family-maps-to-the-rational-cayley-velocity-with-numerator-n-plus-one-and-denominator-two-n-plus-three",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.tanh_log",
  caveat @ "claim:this-family-law-is-an-arithmetic-embedding-and-does-not-predict-a-lorentz-velocity-for-a-hall-fluid"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallConductance where
  formalizes @ "claim:the-rank-two-hierarchy-state-has-dimensionless-hall-conductance-two-fifths",
  epistemic_status @ "consistency-identity",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "law:fractional-hall-conductance-sigma-xy-equals-filling-times-e-squared-over-h",
  supported_by @ "paper:jain-1989-composite-fermion-approach-doi-10.1103-physrevlett.63.199",
  supported_by @ "measurement:feldman-krauss-smet-yacoby-2012-incompressible-two-fifths-state-doi-10.1126-science.1224784",
  experimental_bound @ "value:sigma-xy-over-e-squared-over-h-equals-two-fifths-on-the-two-fifths-hall-plateau;test:the-transverse-response-must-lock-to-two-fifths-while-longitudinal-response-is-suppressed",
  caveat @ "epistemic:this-is-a-postdiction-of-an-observed-plateau-after-selecting-the-three-two-k-matrix-not-an-independent-phase-selection-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallConductance where
  formalizes @ "claim:the-rank-three-hierarchy-state-has-dimensionless-hall-conductance-three-sevenths",
  epistemic_status @ "consistency-identity",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "law:fractional-hall-conductance-sigma-xy-equals-filling-times-e-squared-over-h",
  supported_by @ "paper:jain-1989-composite-fermion-approach-doi-10.1103-physrevlett.63.199",
  supported_by @ "measurement:feldman-krauss-smet-yacoby-2012-incompressible-three-sevenths-state-doi-10.1126-science.1224784",
  experimental_bound @ "value:sigma-xy-over-e-squared-over-h-equals-three-sevenths-on-the-three-sevenths-hall-plateau;test:the-transverse-response-must-lock-to-three-sevenths-while-longitudinal-response-is-suppressed",
  caveat @ "epistemic:this-is-a-postdiction-of-an-observed-plateau-after-selecting-the-three-two-two-k-matrix-not-an-independent-phase-selection-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallResistivity where
  formalizes @ "claim:the-two-fifths-hierarchy-state-has-dimensionless-hall-resistivity-five-halves",
  epistemic_status @ "consistency-identity",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "law:hall-resistivity-is-the-reciprocal-of-hall-conductance-on-a-dissipationless-plateau",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallConductance",
  experimental_bound @ "value:rho-xy-over-h-over-e-squared-equals-five-halves-on-the-two-fifths-plateau",
  caveat @ "epistemic:this-is-the-reciprocal-response-identity-not-an-independent-observable-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallResistivity where
  formalizes @ "claim:the-three-sevenths-hierarchy-state-has-dimensionless-hall-resistivity-seven-thirds",
  epistemic_status @ "consistency-identity",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "law:hall-resistivity-is-the-reciprocal-of-hall-conductance-on-a-dissipationless-plateau",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallConductance",
  experimental_bound @ "value:rho-xy-over-h-over-e-squared-equals-seven-thirds-on-the-three-sevenths-plateau",
  caveat @ "epistemic:this-is-the-reciprocal-response-identity-not-an-independent-observable-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_terminalQuasiparticleCharge where
  derives @ "claim:the-terminal-excitation-of-the-determinant-five-jain-k-matrix-has-charge-one-fifth-of-the-electron-charge",
  epistemic_status @ "conditional-model",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "postulate:abelian-chern-simons-quasiparticle-charge-is-t-transpose-k-inverse-l",
  supported_by @ "paper:jain-1989-composite-fermion-approach-doi-10.1103-physrevlett.63.199",
  supported_by @ "measurement:chung-heiblum-umansky-2003-shot-noise-e-over-five-doi-10.1103-physrevlett.91.216804",
  experimental_bound @ "value:elementary-backscattered-charge-over-e-equals-one-fifth-at-two-fifths-in-the-unbunched-regime",
  caveat @ "epistemic:the-charge-follows-after-selecting-the-k-matrix-and-terminal-integer-excitation-vector",
  caveat @ "experiment:very-low-temperature-weak-backscattering-can-bunch-elementary-quasiparticles-and-produce-effective-charge-two-fifths"

zil attach Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_terminalQuasiparticleCharge where
  derives @ "claim:the-terminal-excitation-of-the-determinant-seven-jain-k-matrix-has-charge-one-seventh-of-the-electron-charge",
  epistemic_status @ "conditional-model",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "postulate:abelian-chern-simons-quasiparticle-charge-is-t-transpose-k-inverse-l",
  supported_by @ "paper:jain-1989-composite-fermion-approach-doi-10.1103-physrevlett.63.199",
  supported_by @ "measurement:chung-heiblum-umansky-2003-shot-noise-e-over-seven-doi-10.1103-physrevlett.91.216804",
  experimental_bound @ "value:elementary-backscattered-charge-over-e-equals-one-seventh-at-three-sevenths-in-the-unbunched-regime",
  caveat @ "epistemic:the-charge-follows-after-selecting-the-k-matrix-and-terminal-integer-excitation-vector",
  caveat @ "experiment:very-low-temperature-weak-backscattering-can-bunch-elementary-quasiparticles-and-change-the-effective-shot-noise-charge"

zil_file_contract physlib.fqheHierarchyContinuedFraction where
  promises "The hierarchical FQHE filling recursion is realized by determinant-one fractional-linear steps; its one-level endpoint is the existing Laughlin filling, the uniform family [3,2,...,2] is the complete p=1 Jain sequence, the observed 2/5 and 3/7 states are derived from checked rank-two and rank-three Chern-Simons K-matrices and connected to their standard Hall conductances, reciprocal resistivities, and terminal e/5 and e/7 quasiparticle charges, and every positive filling has the existing rational-boost Pythagorean/Cayley presentation with the full Jain family mapped by one formula."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.laughlinFilling",
    "lean:Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.jainFilling",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean.rationalBoost_massShell"]
  forbids_substitutes ["claiming-that-shared-continued-fraction-arithmetic-is-a-physical-equivalence-between-hall-states-and-lorentz-boosts",
    "extrapolating-the-checked-rank-two-and-rank-three-k-matrices-to-an-unproved-arbitrary-rank-construction",
    "claiming-that-a-k-matrix-determinant-alone-fixes-the-full-modular-tensor-category",
    "identifying-the-filling-cayley-coordinate-with-a-measured-spacetime-velocity"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_cons_eq_mobius,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_kmatrix_derivation,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_kmatrix_derivation,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallConductance,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallConductance,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallResistivity,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallResistivity,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_terminalQuasiparticleCharge,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_terminalQuasiparticleCharge,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_cayley_rationalBoost,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jainHierarchy_cayleyVelocity,
    Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_single_eq_laughlinFilling]

/- ZIL-END -/
