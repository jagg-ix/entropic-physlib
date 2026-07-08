/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint

/-!
# The Wheeler–DeWitt equation is the complex Einstein scalar constraint

Links the **Wheeler–DeWitt equation** (`ComplexEinstein.WheelerDeWittLusanna`, the quantized ADM Hamiltonian constraint)
to the **complex Einstein scalar constraint** (`CanonicalTetradGravity.ComplexEinsteinScalarConstraint`,
`ComplexEinstein.ComplexMassEinsteinEquations`), closing the loop of the complex-gravity arc.

Sourcing the Wheeler–DeWitt Hamiltonian operator by Nagao–Nielsen complex-mass matter — the real part of
the complex Einstein energy `Re E_C = m_R c²` in the gravitational constraint, the imaginary part
`Im E_C = m_I c²` as the imaginary Hamiltonian `Ĥ_I` — the Wheeler–DeWitt equation

  `(ℋ − κ·Re E_C − i·κ·Im E_C) Ψ = 0`

for a non-trivial wavefunctional `Ψ ≠ 0` is **exactly** the complex sourced ADM scalar constraint
`ℂ(ℋ) = κ E_C` (`wheelerDeWitt_eq_complexSourcedScalarConstraint`). Consequently a Wheeler–DeWitt physical
state forces **reversible matter** `m_I = 0` (`wheelerDeWitt_forces_reversible`) — the *same* reality
obstruction that the complex Einstein equation imposes
(`complexSourcedScalarConstraint_reality`): a real classical geometry admits only real-mass matter.

So the Wheeler–DeWitt equation, the complex Einstein scalar constraint, and the complex Einstein energy
are one structure: the quantized constraint annihilating `Ψ` is the complexified `G_{nn}` equation, real
exactly when the matter is reversible.

* **§A — Wheeler–DeWitt = complex sourced scalar constraint**
  (`wheelerDeWitt_eq_complexSourcedScalarConstraint`).
* **§B — a Wheeler–DeWitt state forces reversible matter** (`wheelerDeWitt_forces_reversible`).
* **§C — the assembly** (`wheelerDeWitt_isComplexEinsteinScalarConstraint`).

## References

* B. S. DeWitt (Wheeler–DeWitt); K. Nagao, H. B. Nielsen (complex mass). Repo dependencies:
  `ComplexEinstein.WheelerDeWittLusanna` (`WheelerDeWitt`, `wheelerDeWitt_iff_of_ne`),
  `CanonicalTetradGravity.ComplexEinsteinScalarConstraint` (`complexSourcedScalarConstraint`,
  `complexSourcedScalarConstraint_iff`, `complexSourcedScalarConstraint_reality`),
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint

variable {d : ℕ}

/-! ## §A — Wheeler–DeWitt = the complex sourced ADM scalar constraint -/

/-- **[The Wheeler–DeWitt equation is the complex sourced scalar constraint].** With the gravitational
Hamiltonian operator sourced by the complex Einstein energy — `Ĥ_R = ℋ − κ·Re E_C` (the total constraint
`ℋ − κ m_R c²`), `Ĥ_I = κ·Im E_C = κ m_I c²` — the Wheeler–DeWitt equation `(Ĥ_R − iĤ_I)Ψ = 0` for a
non-trivial wavefunctional `Ψ ≠ 0` is *exactly* the complex sourced ADM scalar constraint
`ℂ(ℋ) = κ E_C` (`complexSourcedScalarConstraint`): the quantized constraint annihilating `Ψ` is the
complexified `G_{nn} = κ T_{nn}` Einstein equation. -/
theorem wheelerDeWitt_eq_complexSourcedScalarConstraint (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) :
    WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K := by
  rw [wheelerDeWitt_iff_of_ne _ _ Ψ hΨ, complexEinsteinEnergy_re, complexEinsteinEnergy_im,
    sub_eq_zero, complexSourcedScalarConstraint_iff]

/-! ## §B — a Wheeler–DeWitt state forces reversible matter -/

/-- **[A Wheeler–DeWitt physical state forces reversible matter] `m_I = 0`.** A non-trivial Wheeler–DeWitt
state sourced by complex-mass matter (`κ ≠ 0`, `c ≠ 0`) forces the imaginary (entropic) mass to vanish —
the *same* reality obstruction as the complex Einstein equation
(`complexSourcedScalarConstraint_reality`): the quantized real ADM geometry admits only reversible
(real-mass) matter. -/
theorem wheelerDeWitt_forces_reversible (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) (hκ : κ ≠ 0) (hc : c ≠ 0)
    (h : WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
          (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ) :
    m_I = 0 :=
  complexSourcedScalarConstraint_reality R3 KdotK m_R m_I c κ K hκ hc
    ((wheelerDeWitt_eq_complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K Ψ hΨ).mp h)

/-! ## §C — the assembly: Wheeler–DeWitt *is* the complex Einstein scalar constraint -/

/-- **[The Wheeler–DeWitt equation is the complex Einstein scalar constraint, real ⟺ reversible matter].**
The single statement of the complex-gravity loop. For a non-trivial wavefunctional `Ψ ≠ 0` sourced by
Nagao–Nielsen complex-mass matter (`κ ≠ 0`, `c ≠ 0`), with the Wheeler–DeWitt Hamiltonian operator
`Ĥ_R = ℋ − κ·Re E_C`, `Ĥ_I = κ·Im E_C`:

1. the **Wheeler–DeWitt equation `(Ĥ_R − iĤ_I)Ψ = 0` is exactly the complex sourced ADM scalar
   constraint** `ℂ(ℋ) = κ E_C` — the quantized constraint annihilating `Ψ` is the complexified
   `G_{nn} = κ T_{nn}` Einstein equation;
2. equivalently, it is the **real ADM constraint sourced by the rest energy** `ℋ = κ m_R c²` *together
   with* the **vanishing of the imaginary (entropic) source** `κ m_I c² = 0`;
3. hence a **Wheeler–DeWitt physical state forces reversible matter** `m_I = 0` — a real quantized ADM
   geometry admits only real-mass matter.

The quantized ADM Hamiltonian constraint (`ComplexEinstein.WheelerDeWittLusanna`), the complex Einstein scalar constraint
(`CanonicalTetradGravity.ComplexEinsteinScalarConstraint`), and the complex Einstein energy
(`ComplexEinstein.ComplexMassEinsteinEquations`) are one structure: the Wheeler–DeWitt equation is the complexified
`G_{nn}` equation, real exactly when the matter is reversible. -/
theorem wheelerDeWitt_isComplexEinsteinScalarConstraint (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) (hκ : κ ≠ 0) (hc : c ≠ 0) :
    (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K)
    ∧ (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2) ∧ κ * (m_I * c ^ 2) = 0)
    ∧ (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ → m_I = 0) :=
  let hEq := wheelerDeWitt_eq_complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K Ψ hΨ
  ⟨hEq, hEq.trans (complexSourcedScalarConstraint_iff R3 KdotK m_R m_I c κ K),
    fun h => wheelerDeWitt_forces_reversible R3 KdotK m_R m_I c κ K Ψ hΨ hκ hc h⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein

end
