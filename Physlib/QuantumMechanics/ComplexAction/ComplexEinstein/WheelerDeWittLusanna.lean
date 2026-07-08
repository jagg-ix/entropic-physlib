/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-!
# The Wheeler–DeWitt equation as the quantized ADM Hamiltonian constraint

Formalizes the **Wheeler–DeWitt equation** `(Ĥ_R − iĤ_I)Ψ = 0` as the quantization of the **ADM scalar
(Hamiltonian) constraint** of `CanonicalTetradGravity.TetradADMGravity`. This is *not* posited as an entropic structure:
the real part `Ĥ_R` is the standard ADM Hamiltonian constraint `ℋ = ³R + (tr K)² − K_ij K^ij`, and the
Wheeler–DeWitt equation is the statement that the wavefunctional of the universe is annihilated by the
(complexified) Hamiltonian constraint operator.

In the minisuperspace / one-mode representation the Hamiltonian constraint acts by multiplication by its
value, so the Wheeler–DeWitt equation is

  `(Ĥ_R − iĤ_I)·Ψ = 0`   (`WheelerDeWitt`, with `complexHamiltonianConstraint Ĥ_R Ĥ_I = Ĥ_R − iĤ_I`).

For a non-trivial wavefunctional `Ψ ≠ 0` this holds **iff** both the real and imaginary constraints vanish
(`wheelerDeWitt_iff_of_ne`): `Ĥ_R = 0 ∧ Ĥ_I = 0`. Taking `Ĥ_R` to be Lusanna's scalar constraint
`hamiltonianConstraint`, the real Wheeler–DeWitt constraint is *exactly* the ADM vacuum constraint
`³R + (tr K)² = K_ij K^ij` (`wheelerDeWitt_lusanna_vacuum`, via `hamiltonianConstraint_vacuum_iff`); with
matter, it is the sourced constraint `ℋ = κρ` (`wheelerDeWitt_lusanna_sourced`,
`sourcedHamiltonianConstraint`). At `Ĥ_I = 0` the equation is the ordinary real Wheeler–DeWitt equation
(`wheelerDeWitt_real_of_ne`).

So the standard Wheeler–DeWitt equation of canonical quantum gravity is the quantized Lusanna ADM
Hamiltonian constraint; the optional imaginary part `Ĥ_I` is a further constraint `Ĥ_I = 0` on the
physical state.

* **§A — the Wheeler–DeWitt equation** (`complexHamiltonianConstraint`, `WheelerDeWitt`,
  `wheelerDeWitt_iff_of_ne`, `wheelerDeWitt_real_of_ne`).
* **§B — grounding in the Lusanna ADM constraint** (`wheelerDeWitt_lusanna_vacuum`,
  `wheelerDeWitt_lusanna_sourced`).
* **§C — the assembly** (`wheelerDeWitt_lusanna`).

## References

* B. S. DeWitt, *Quantum Theory of Gravity. I*, Phys. Rev. 160 (1967) 1113; L. Lusanna, *Canonical ADM
  tetrad gravity*. Repo structure: `CanonicalTetradGravity.TetradADMGravity` (`hamiltonianConstraint`, `yorkTime`,
  `hamiltonianConstraint_vacuum_iff`, `sourcedHamiltonianConstraint`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

variable {d : ℕ}

/-! ## §A — the Wheeler–DeWitt equation -/

/-- **The complex Hamiltonian constraint operator value** `Ĥ_R − iĤ_I` (minisuperspace: the constraint
acts by multiplication by its value). -/
def complexHamiltonianConstraint (HR HI : ℝ) : ℂ := (HR : ℂ) - Complex.I * (HI : ℂ)

@[simp] theorem complexHamiltonianConstraint_re (HR HI : ℝ) :
    (complexHamiltonianConstraint HR HI).re = HR := by
  simp [complexHamiltonianConstraint]

@[simp] theorem complexHamiltonianConstraint_im (HR HI : ℝ) :
    (complexHamiltonianConstraint HR HI).im = -HI := by
  simp [complexHamiltonianConstraint]

/-- **The Wheeler–DeWitt equation** `(Ĥ_R − iĤ_I)Ψ = 0` — the wavefunctional `Ψ` is annihilated by the
(complexified) Hamiltonian constraint operator. -/
def WheelerDeWitt (HR HI : ℝ) (Ψ : ℂ) : Prop := complexHamiltonianConstraint HR HI * Ψ = 0

/-- **[Non-trivial state ⟹ both constraints vanish] `(Ĥ_R − iĤ_I)Ψ = 0 ⟺ Ĥ_R = 0 ∧ Ĥ_I = 0`** (for
`Ψ ≠ 0`). A non-trivial wavefunctional is annihilated by the complex Hamiltonian constraint exactly when
both the real (ADM) and imaginary Hamiltonian constraints vanish. -/
theorem wheelerDeWitt_iff_of_ne (HR HI : ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) :
    WheelerDeWitt HR HI Ψ ↔ HR = 0 ∧ HI = 0 := by
  unfold WheelerDeWitt
  rw [mul_eq_zero, or_iff_left hΨ, complexHamiltonianConstraint, Complex.ext_iff]
  simp [neg_eq_zero]

/-- A non-trivial Wheeler-DeWitt state forces both real and imaginary constraints to vanish. -/
theorem wheelerDeWitt_constraints_of_nontrivial_state
    (HR HI : ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (hWDW : WheelerDeWitt HR HI Ψ) :
    HR = 0 ∧ HI = 0 :=
  (wheelerDeWitt_iff_of_ne HR HI Ψ hΨ).mp hWDW

/-- **[The real Wheeler–DeWitt equation] `Ĥ_R Ψ = 0 ⟺ Ĥ_R = 0`** (at `Ĥ_I = 0`, `Ψ ≠ 0`) — the ordinary
Hamiltonian-constraint annihilation of canonical quantum gravity. -/
theorem wheelerDeWitt_real_of_ne (HR : ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) :
    WheelerDeWitt HR 0 Ψ ↔ HR = 0 := by
  rw [wheelerDeWitt_iff_of_ne HR 0 Ψ hΨ]; simp

/-! ## §B — grounding in the Lusanna ADM Hamiltonian constraint -/

/-- **[The real Wheeler–DeWitt constraint is the ADM vacuum constraint] `ℋ Ψ = 0 ⟺ ³R + (tr K)² =
K_ij K^ij`.** With the Hamiltonian operator taken to be Lusanna's scalar constraint
`hamiltonianConstraint`, the standard (real) Wheeler–DeWitt equation for a non-trivial wavefunctional is
*exactly* the ADM vacuum Hamiltonian constraint (`hamiltonianConstraint_vacuum_iff`). The Wheeler–DeWitt
equation is the quantized ADM Hamiltonian constraint. -/
theorem wheelerDeWitt_lusanna_vacuum (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ)
    (hΨ : Ψ ≠ 0) :
    WheelerDeWitt (hamiltonianConstraint R3 KdotK K) 0 Ψ ↔ R3 + yorkTime K ^ 2 = KdotK := by
  rw [wheelerDeWitt_real_of_ne _ Ψ hΨ, hamiltonianConstraint_vacuum_iff]

/-- **[The matter Wheeler–DeWitt constraint is the sourced ADM constraint] `(ℋ − κρ)Ψ = 0 ⟺ ℋ = κρ`.**
With matter energy density `ρ`, the real Wheeler–DeWitt constraint (the total Hamiltonian constraint
`ℋ − κρ` annihilating `Ψ`) is Lusanna's matter-sourced scalar constraint `ℋ = κρ`
(`sourcedHamiltonianConstraint`, the `G_{nn} = κ T_{nn}` Einstein equation). -/
theorem wheelerDeWitt_lusanna_sourced (R3 KdotK ρ κ : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ)
    (hΨ : Ψ ≠ 0) :
    WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * ρ) 0 Ψ
      ↔ sourcedHamiltonianConstraint R3 KdotK ρ κ K := by
  rw [wheelerDeWitt_real_of_ne _ Ψ hΨ, sourcedHamiltonianConstraint, sub_eq_zero]

/-! ## §C — the assembly -/

/-- **[The Wheeler–DeWitt equation as the quantized ADM constraint, assembled].** With Lusanna's scalar
constraint as the real Hamiltonian operator and an optional imaginary part `Ĥ_I`, the Wheeler–DeWitt
equation `(ℋ − iĤ_I)Ψ = 0` for a non-trivial wavefunctional is exactly the ADM vacuum Hamiltonian
constraint `³R + (tr K)² = K_ij K^ij` together with the imaginary constraint `Ĥ_I = 0`. The standard
Wheeler–DeWitt equation of canonical quantum gravity is the quantized Lusanna ADM Hamiltonian
constraint. -/
theorem wheelerDeWitt_lusanna (R3 KdotK HI : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) :
    WheelerDeWitt (hamiltonianConstraint R3 KdotK K) HI Ψ
      ↔ (R3 + yorkTime K ^ 2 = KdotK) ∧ HI = 0 := by
  rw [wheelerDeWitt_iff_of_ne _ HI Ψ hΨ, hamiltonianConstraint_vacuum_iff]

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna

end
