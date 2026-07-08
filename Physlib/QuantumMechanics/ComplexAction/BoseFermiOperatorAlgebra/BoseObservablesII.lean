/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.JordanWignerTwoMode
public import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Kalnay-Mac Cotrina II: observables as Bose bilinears

This file formalizes the finite algebraic core of A. J. Kalnay and E. Mac Cotrina,
*Quantum Field Theory of Fermions and Parafermions Constructed from Quantum Bose Fields. II: A Remark on
the Observables*, Prog. Theor. Phys. 55 (1976), 297-301.

The paper's main point is not a new CAR construction, but a statement about observables: although a Fermi
observable first represented through the composite Bose fields can look non-bilinear in the Bose operators,
on the relevant Bose sector it has a representative in the usual Bose-bilinear form. In the Fock/Jordan-Wigner
case, a diagonal Fermi observable

  `sum_i w_i f_i^+ f_i`

becomes a diagonal Bose bilinear with weights

  `W_r = sum_i w_i eta_i^r`,

where `eta_i^r` is the `i`-th binary occupation label of the Jordan-Wigner basis.

We formalize the checked, finite two-mode shadow of that statement, using the existing Kalnay infrastructure:

* `BoseFermiOperatorAlgebra.JordanWignerTwoMode` supplies the concrete Jordan-Wigner matrices `kalnayJW0`, `kalnayJW1`;
* `BoseFermiOperatorAlgebra.CompositeFermionCAR` supplies `fermionNumber`;
* `BoseFermiOperatorAlgebra.FermionNetLocality` supplies `AnticommutingFermionModes` and the commuting projector layer.

The main theorem is `kalnay_ii_theorem_2_5_two_mode`:

  `(w0 : C) • n0 + (w1 : C) • n1 = diagonal (fun r => w0 eta0(r) + w1 eta1(r))`.

This is exactly the two-mode instance of Kalnay-Mac Cotrina's Theorem 2.5 and Corollary 2.6: real/positive
Fermi weights remain real/nonnegative Bose weights. The first section also records the quotient-by-sector
logic behind Theorems 2.1 and 3.1: a term that kills the chosen Bose sector may be added to a representative
without changing the observable on that sector. This is the algebraic content of the paper's para-Fermi
extension, abstracted away from the distributional field kernels.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseObservablesII

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.JordanWignerTwoMode

/-! ## Sector representatives -/

section Sector

variable {V : Type*} [AddCommMonoid V]

/-- Two operator representatives agree on the chosen sector. This is the sector-restricted equality used in
Kalnay-Mac Cotrina's Theorems 2.1 and 3.1. -/
def AgreesOn (S : Set V) (T U : V → V) : Prop :=
  ∀ v, v ∈ S → T v = U v

/-- An operator tail kills the chosen sector. In the paper this is the role of terms with too many rightmost
Bose annihilation operators for the selected `p`-boson sector. -/
def KillsOn (S : Set V) (K : V → V) : Prop :=
  ∀ v, v ∈ S → K v = 0

/-- Adding a sector-killing tail does not change the representative on that sector. This is the common
algebraic spine of the fermion (`p = 1`) and para-Fermi (`p > 1`) observable statements. -/
theorem add_killing_tail_agrees (S : Set V) (Q B K : V → V)
    (hQB : AgreesOn S Q B) (hK : KillsOn S K) :
    AgreesOn S Q (fun v => B v + K v) := by
  intro v hv
  rw [hQB v hv]
  change B v = B v + K v
  rw [hK v hv, add_zero]

end Sector

/-! ## The finite two-mode Theorem 2.5 calculation -/

/-- First Jordan-Wigner occupation label on the basis `|00>`, `|10>`, `|01>`, `|11>`. -/
def jwOcc0 : Fin 4 → ℝ := ![0, 1, 0, 1]

/-- Second Jordan-Wigner occupation label on the basis `|00>`, `|10>`, `|01>`, `|11>`. -/
def jwOcc1 : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The Bose weight `W_r = w0 eta0(r) + w1 eta1(r)` from Kalnay-Mac Cotrina Theorem 2.5. -/
def jwBoseWeight (w0 w1 : ℝ) (r : Fin 4) : ℝ :=
  w0 * jwOcc0 r + w1 * jwOcc1 r

/-- The diagonal Fermi observable `w0 n0 + w1 n1`, written using the existing Kalnay number projectors. -/
noncomputable def kalnayFermionDiagonalObservable (w0 w1 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (w0 : ℂ) • fermionNumber kalnayJW0 + (w1 : ℂ) • fermionNumber kalnayJW1

/-- The corresponding ordinary Bose-bilinear diagonal observable with weights `W_r`. -/
def kalnayBoseDiagonalObservable (w0 w1 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun r => (jwBoseWeight w0 w1 r : ℂ))

theorem jwBoseWeight_zero (w0 w1 : ℝ) :
    jwBoseWeight w0 w1 0 = 0 := by
  simp [jwBoseWeight, jwOcc0, jwOcc1]

theorem jwBoseWeight_one (w0 w1 : ℝ) :
    jwBoseWeight w0 w1 1 = w0 := by
  simp [jwBoseWeight, jwOcc0, jwOcc1]

theorem jwBoseWeight_two (w0 w1 : ℝ) :
    jwBoseWeight w0 w1 2 = w1 := by
  simp [jwBoseWeight, jwOcc0, jwOcc1]

theorem jwBoseWeight_three (w0 w1 : ℝ) :
    jwBoseWeight w0 w1 3 = w0 + w1 := by
  simp [jwBoseWeight, jwOcc0, jwOcc1]

/-- Corollary 2.6 in the two-mode finite model: nonnegative Fermi weights give nonnegative Bose weights. -/
theorem jwBoseWeight_nonneg {w0 w1 : ℝ} (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (r : Fin 4) :
    0 ≤ jwBoseWeight w0 w1 r := by
  fin_cases r <;> simp [jwBoseWeight, jwOcc0, jwOcc1, hw0, hw1, add_nonneg]

/-- The Bose representative is the expected diagonal matrix with entries `0`, `w0`, `w1`, `w0 + w1`. -/
theorem kalnayBoseDiagonalObservable_eq_explicit (w0 w1 : ℝ) :
    kalnayBoseDiagonalObservable w0 w1 =
      !![(0 : ℂ), 0, 0, 0;
         0, (w0 : ℂ), 0, 0;
         0, 0, (w1 : ℂ), 0;
         0, 0, 0, ((w0 + w1 : ℝ) : ℂ)] := by
  unfold kalnayBoseDiagonalObservable jwBoseWeight jwOcc0 jwOcc1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- **Kalnay-Mac Cotrina Theorem 2.5, finite two-mode form.** The diagonal Fermi observable
`w0 f0^+ f0 + w1 f1^+ f1` is exactly the ordinary diagonal Bose bilinear whose Bose weights are the
occupation-label sums `W_r = w0 eta0(r) + w1 eta1(r)`. -/
theorem kalnay_ii_theorem_2_5_two_mode (w0 w1 : ℝ) :
    kalnayFermionDiagonalObservable w0 w1 = kalnayBoseDiagonalObservable w0 w1 := by
  unfold kalnayFermionDiagonalObservable kalnayBoseDiagonalObservable jwBoseWeight jwOcc0 jwOcc1
  rw [fermionNumber_kalnayJW0, fermionNumber_kalnayJW1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.add_apply]

/-- **Kalnay-Mac Cotrina Corollary 2.6, finite two-mode form.** The real/nonnegative Fermi weights produce
the real/nonnegative Bose weights `0`, `w0`, `w1`, and `w0 + w1`. -/
theorem kalnay_ii_corollary_2_6_two_mode {w0 w1 : ℝ} (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) :
    (∀ r : Fin 4, 0 ≤ jwBoseWeight w0 w1 r)
      ∧ jwBoseWeight w0 w1 0 = 0
      ∧ jwBoseWeight w0 w1 1 = w0
      ∧ jwBoseWeight w0 w1 2 = w1
      ∧ jwBoseWeight w0 w1 3 = w0 + w1 := by
  exact ⟨jwBoseWeight_nonneg hw0 hw1, jwBoseWeight_zero w0 w1,
    jwBoseWeight_one w0 w1, jwBoseWeight_two w0 w1, jwBoseWeight_three w0 w1⟩

/-- Assembled bridge: the existing two-mode Kalnay/Jordan-Wigner structure supplies anticommuting fermion
modes, and the paper-II observable is the ordinary diagonal Bose representative with the explicit weights. -/
theorem kalnay_ii_observable_bridge (w0 w1 : ℝ) :
    AnticommutingFermionModes kalnayJW0 kalnayJW1
      ∧ kalnayFermionDiagonalObservable w0 w1 = kalnayBoseDiagonalObservable w0 w1
      ∧ kalnayBoseDiagonalObservable w0 w1 =
        !![(0 : ℂ), 0, 0, 0;
           0, (w0 : ℂ), 0, 0;
           0, 0, (w1 : ℂ), 0;
           0, 0, 0, ((w0 + w1 : ℝ) : ℂ)] :=
  ⟨kalnayJW_anticommutingModes, kalnay_ii_theorem_2_5_two_mode w0 w1,
    kalnayBoseDiagonalObservable_eq_explicit w0 w1⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseObservablesII

end
