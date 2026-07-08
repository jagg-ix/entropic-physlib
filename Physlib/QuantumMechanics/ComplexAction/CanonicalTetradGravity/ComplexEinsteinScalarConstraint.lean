/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The ADM scalar constraint is the complex Einstein field equation's time–time component

Links **ADM tetrad gravity** (`CanonicalTetradGravity.TetradADMGravity`) to the **complex Einstein field equations**
(`ComplexEinstein.ComplexMassEinsteinEquations`, Nagao–Nielsen complex mass) through the **tensor Einstein field equation**
(`ComplexEinstein.EinsteinFieldEquationsPhysLean`, `G_μν = κ T_μν`).

The Lusanna scalar (Hamiltonian) constraint `ℋ = ³R + (tr K)² − K_ij K^ij` is the **time–time component**
`G_{nn}` of the tensor Einstein equation in Gauss–Codazzi form. So the matrix field equation `G = κ T`,
read at the `(n,n)` entry, *is* the matter-sourced scalar constraint `ℋ = κ T_{nn}`
(`sourcedScalarConstraint_of_einstein_nn`) — the ADM constraint sourced by the matter energy density
`ρ = T_{nn}`.

For **Nagao–Nielsen complex-mass matter**, the energy density is the complex Einstein energy
`E_C = m_C c² = (m_R + i m_I)c²` (`complexEinsteinEnergy`). Its **real part** `m_R c²` is the ordinary rest
energy that sources the real ADM geometry (`complexSource_re_sources_geometry`); its **imaginary part**
`m_I c²` is the entropic/dissipative (`H_I`) sector. Complexifying the scalar constraint,
`ℂ(ℋ) = κ E_C` (`complexSourcedScalarConstraint`), splits *exactly* into the real geometric constraint
`ℋ = κ m_R c²` **and** the vanishing of the entropic source `κ m_I c² = 0`
(`complexSourcedScalarConstraint_iff`). Hence a **real classical ADM geometry forces reversible matter**:
`m_I = 0` (`complexSourcedScalarConstraint_reality`). Entropic (imaginary-mass) matter requires a
complexified geometry — the geometric face of the complex action.

* **§A — the scalar constraint is the `G_{nn}` Einstein component**
  (`sourcedScalarConstraint_of_einstein_nn`).
* **§B — the complex-mass matter source** (`complexSource_re_sources_geometry`).
* **§C — the complex scalar constraint and the reality obstruction**
  (`complexSourcedScalarConstraint`, `complexSourcedScalarConstraint_iff`,
  `complexSourcedScalarConstraint_reality`).
* **§D — the assembly** (`lusanna_complexEinstein_scalarConstraint`).

## References

* L. Lusanna, *Canonical ADM tetrad gravity*, Int. J. Geom. Methods Mod. Phys. 12 (2015) 1530001;
  K. Nagao, H. B. Nielsen (complex action / complex mass). Repo dependencies: `CanonicalTetradGravity.TetradADMGravity`
  (`hamiltonianConstraint`, `sourcedHamiltonianConstraint`), `ComplexEinstein.EinsteinFieldEquationsPhysLean`
  (`einsteinTensor`, `einsteinFieldEquation`), `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`,
  `complexEinsteinEnergy_re`, `complexEinsteinEnergy_im`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

variable {d : ℕ}

/-! ## §A — the ADM scalar constraint is the `G_{nn}` component of the tensor Einstein equation -/

/-- **[The scalar constraint is the `(n,n)` Einstein component] `ℋ = κ T_{nn}`.** Given the Gauss–Codazzi
identity that the `(n,n)` entry of the Einstein tensor is the ADM scalar constraint `ℋ` (`hGC`), the matrix
Einstein field equation `G = κ T` (`hEFE`), read at the time–time entry, *is* the matter-sourced scalar
constraint with energy density `ρ = T_{nn}` — the ADM constraint is the `G_{nn}` Einstein equation. -/
theorem sourcedScalarConstraint_of_einstein_nn {ι : Type*} (n : ι)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ R3 KdotK : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (hGC : einsteinTensor Ric scalarR g n n = hamiltonianConstraint R3 KdotK K)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) :
    sourcedHamiltonianConstraint R3 KdotK (T n n) κ K := by
  unfold sourcedHamiltonianConstraint
  rw [← hGC]
  unfold einsteinFieldEquation at hEFE
  have h := congrFun (congrFun hEFE n) n
  rwa [Matrix.smul_apply, smul_eq_mul] at h

/-! ## §B — the complex-mass matter source -/

/-- **[The real rest energy sources the real geometry] `ρ = Re E_C = m_R c²`.** Sourcing the ADM scalar
constraint by the *real part* of the Nagao–Nielsen complex Einstein energy `E_C = m_C c²`
(`complexEinsteinEnergy_re`) is exactly the constraint sourced by the ordinary rest-energy density
`m_R c²` — the reversible, geometric matter content. -/
theorem complexSource_re_sources_geometry (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    sourcedHamiltonianConstraint R3 KdotK (complexEinsteinEnergy m_R m_I c).re κ K
      ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2) := by
  rw [sourcedHamiltonianConstraint, complexEinsteinEnergy_re]

/-! ## §C — the complex scalar constraint and the reality obstruction -/

/-- **The complexified ADM scalar constraint** `ℂ(ℋ) = κ E_C` — the real scalar constraint `ℋ`, embedded in
`ℂ`, sourced by the full complex Einstein energy `E_C = m_C c²` (real rest energy + imaginary entropic
energy). -/
def complexSourcedScalarConstraint (R3 KdotK m_R m_I c κ : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (hamiltonianConstraint R3 KdotK K : ℂ) = (κ : ℂ) * complexEinsteinEnergy m_R m_I c

/-- **[The complex constraint splits into geometry + entropic obstruction] `ℂ(ℋ) = κ E_C ⟺ (ℋ = κ m_R c²)
∧ (κ m_I c² = 0)`.** The complexified scalar constraint holds exactly when the real geometric constraint is
sourced by the rest energy `m_R c²` *and* the imaginary (entropic) source `κ m_I c²` vanishes — the real
scalar curvature has no imaginary part, so the entropic energy cannot source a real geometry. -/
theorem complexSourcedScalarConstraint_iff (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) :
    complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K
      ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2) ∧ κ * (m_I * c ^ 2) = 0 := by
  rw [complexSourcedScalarConstraint, Complex.ext_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    complexEinsteinEnergy_re, complexEinsteinEnergy_im, zero_mul, sub_zero, add_zero]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

/-- **[A real classical geometry forces reversible matter] `m_I = 0`.** If a complex Einstein energy sources
the real ADM scalar constraint (`complexSourcedScalarConstraint`) with non-trivial coupling `κ ≠ 0` and
`c ≠ 0`, then the imaginary (entropic) mass must vanish: `m_I = 0`. A real classical ADM geometry admits only
reversible (real-mass) matter — entropic (imaginary-mass) matter requires a complexified geometry. -/
theorem complexSourcedScalarConstraint_reality (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (hκ : κ ≠ 0) (hc : c ≠ 0)
    (h : complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K) : m_I = 0 := by
  have h2 := ((complexSourcedScalarConstraint_iff R3 KdotK m_R m_I c κ K).mp h).2
  have hI : m_I * c ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left hκ
  exact (mul_eq_zero.mp hI).resolve_right (pow_ne_zero 2 hc)

/-! ## §D — the assembly -/

/-- **[The ADM scalar constraint as the complex Einstein field equation, assembled].** Sourcing the Lusanna
ADM scalar constraint by the Nagao–Nielsen complex Einstein energy `E_C = m_C c²`: the real part `m_R c²`
sources the real geometry (`complexSource_re_sources_geometry`); the complexified constraint splits into the
real geometric equation and the vanishing of the entropic source (`complexSourcedScalarConstraint_iff`);
and a real classical geometry forces reversible matter `m_I = 0` (`complexSourcedScalarConstraint_reality`).
The `G_{nn}` time–time face of GR, sourced by complex-mass matter, is real exactly when the matter is
reversible. -/
theorem lusanna_complexEinstein_scalarConstraint (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (hκ : κ ≠ 0) (hc : c ≠ 0) :
    (sourcedHamiltonianConstraint R3 KdotK (complexEinsteinEnergy m_R m_I c).re κ K
        ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2))
      ∧ (complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K
        ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2) ∧ κ * (m_I * c ^ 2) = 0)
      ∧ (complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K → m_I = 0) :=
  ⟨complexSource_re_sources_geometry R3 KdotK m_R m_I c κ K,
    complexSourcedScalarConstraint_iff R3 KdotK m_R m_I c κ K,
    fun h => complexSourcedScalarConstraint_reality R3 KdotK m_R m_I c κ K hκ hc h⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint

end
