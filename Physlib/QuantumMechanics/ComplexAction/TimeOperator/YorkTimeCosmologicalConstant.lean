/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-!
# The York time as an effective cosmological constant (dark energy)

Links the ADM tetrad-gravity **York-time negative kinetic term** (`ParametrizedTetradGravity.YorkADMEnergy`) to the
**cosmological constant `Λ`** of the realized Einstein field equations (`ComplexEinstein.EinsteinFieldEquationsPhysLean`).
This is the gravitational analogue of the complex-action/entropic-time ↔ complex-Einstein bridge: just as the imaginary mass `m_I`
is the entropic term, the inertial **York time `³K` is the candidate dark-energy / cosmological term** — exactly
Alba–Lusanna's proposal that the clock-synchronization gauge freedom feeds the dark sector.

The weak ADM energy's York-time term `−a·³K²` (`yorkKineticTerm`, non-positive, vanishing only at `³K = 0`)
enters the Einstein field equations as an **effective cosmological constant** `Λ_york = −a·³K²`
(`yorkLambda`):

* `yorkLambda` is **non-positive** (`yorkLambda_nonpos`) and vanishes **exactly in the `³K = 0` gauge**
  (`yorkLambda_eq_zero_iff`) — a purely *inertial*, general-relativistic dark-energy term, absent in Newtonian
  gravity;
* with `Λ = Λ_york` the cosmological Einstein equation `G_μν + Λ_york g_μν = κ T_μν`
  (`yorkCosmologicalEinstein`) **reduces to the standard `G_μν = κ T_μν` exactly when `³K = 0`**
  (`york_cosmological_at_zero`) — no York time, no dark energy.

So `³K = 0` ⟺ no effective cosmological constant ⟺ standard Einstein, paralleling `m_I = 0` ⟺ reversible ⟺
real Einstein: both the imaginary-mass entropic sector and the York-time inertial sector switch off in their
respective "trivial" gauges, leaving the ordinary general relativity.

* **§A — the York-time effective cosmological constant** (`yorkLambda`, `yorkLambda_nonpos`,
  `yorkLambda_eq_zero_iff`, `yorkLambda_zero`).
* **§B — the cosmological Einstein equation** (`yorkCosmologicalEinstein`, `york_cosmological_at_zero`).

## References

* D. Alba, L. Lusanna, Can. J. Phys. 90 (2012) 1017 / 1077 (the York time as a candidate dark-energy /
  back-reaction term).
* Repo carriers: `ParametrizedTetradGravity.YorkADMEnergy` (`yorkKineticTerm`), `ComplexEinstein.EinsteinFieldEquationsPhysLean`
  (`einsteinFieldEquationCosmological`, `einsteinFieldEquation`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.YorkTimeCosmologicalConstant

open Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean


/-- **The York-time effective cosmological constant** `Λ_york = −a·³K²` — the weak-ADM-energy York-time
kinetic term (`yorkKineticTerm`), entering the Einstein field equations as a cosmological / dark-energy
term. -/
noncomputable def yorkLambda (a K3 : ℝ) : ℝ := yorkKineticTerm a K3

/-- **`Λ_york ≤ 0`** — the York-time cosmological term is non-positive (the negative inertial kinetic term). -/
lemma yorkLambda_nonpos (a K3 : ℝ) (ha : 0 ≤ a) : yorkLambda a K3 ≤ 0 :=
  yorkKineticTerm_nonpos a K3 ha

/-- **[No dark energy in the `³K = 0` gauge] `Λ_york = 0 ⟺ ³K = 0`** (for `a > 0`) — the effective
cosmological constant vanishes exactly when the York time does. -/
lemma yorkLambda_eq_zero_iff (a K3 : ℝ) (ha : 0 < a) : yorkLambda a K3 = 0 ↔ K3 = 0 :=
  yorkKineticTerm_eq_zero_iff a K3 ha

/-- **`Λ_york = 0` at `³K = 0`.** -/
lemma yorkLambda_zero (a : ℝ) : yorkLambda a 0 = 0 := by
  rw [yorkLambda, yorkKineticTerm]; ring


variable {ι : Type*}

/-- **[Einstein with the York-time dark energy] `G_μν + Λ_york g_μν = κ T_μν`** — the Einstein field equation
with the York-time effective cosmological constant `Λ_york = −a·³K²`. -/
def yorkCosmologicalEinstein (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (a K3 κ : ℝ) : Prop :=
  einsteinFieldEquationCosmological Ric scalarR g T (yorkLambda a K3) κ

/-- **[`³K = 0` ⟹ standard Einstein, no dark energy] the cosmological equation reduces.** When the York time
vanishes (`³K = 0`), the York-time cosmological constant is zero and `G_μν + Λ_york g_μν = κ T_μν` collapses
to the ordinary `G_μν = κ T_μν` — paralleling the `m_I = 0` reversible/real-Einstein limit. -/
lemma york_cosmological_at_zero (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (a κ : ℝ) :
    yorkCosmologicalEinstein Ric scalarR g T a 0 κ ↔ einsteinFieldEquation Ric scalarR g T κ := by
  unfold yorkCosmologicalEinstein einsteinFieldEquationCosmological einsteinFieldEquation
  rw [yorkLambda_zero, zero_smul, add_zero]

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.YorkTimeCosmologicalConstant

end
