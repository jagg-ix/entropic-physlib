/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# The gravitational (inertial) tensor as the generalisation of d'Alembert's principle (§8)

Formalizes the **d'Alembert-principle reading** of Levi-Civita's **§8 "Gravitational (or inertial)
tensor — Generalisation of d'Alembert's principle"** (arXiv:physics/9906004). The gravitational tensor
`A_ik = (1/κ)(G_ik − ½ g_ik G)` (Eq. 13, `LeviCivita.GravitationalTensor.gravitationalTensor`) and the
balance `T_ik + A_ik = 0` (Eq. 10') are already in `LeviCivita.GravitationalTensor`; this file adds the
mechanical interpretation that §8 attaches to them.

Levi-Civita interprets `A_ik` as the **energy tensor of the space-time environment — gravitational or
inertial** (both gravitation and inertia depend on `ds²`). The balance `T_ik + A_ik = 0` is then the
**generalisation of d'Alembert's principle**: the "lost forces" — the directly-applied (matter) actions
`T_ik` and the inertial actions `A_ik` — balance each other, their sum (the **lost tensor**) identically
vanishing. The nature of `ds²` is always such as to balance all mechanical actions.

* the **lost tensor** `L = T + A` (`lostTensor`) and **d'Alembert's principle** `L = 0`
  (`DAlembertPrinciple`) — the lost forces balance;
* the principle says the **inertial tensor is minus the applied tensor** `A = −T`
  (`dAlembertPrinciple_iff_inertial`), the relativistic `F_applied + F_inertial = 0`;
* on a solution of the Einstein field equation the principle **holds** (`dAlembertPrinciple_of_fieldEquation`,
  reusing the d'Alembert balance), and it holds **component by component** — every mechanical action
  (stress, the force/momentum row, energy density) balances (`dAlembert_componentwise`): for an isolated
  system force and power vanish within each elementary portion.

So Levi-Civita's gravitational/inertial tensor is the four-dimensional d'Alembert principle: matter and
inertia, both encoded in `ds²`, cancel as the lost tensor of the relativistic mechanical equilibrium.

* **§A — the lost tensor and d'Alembert's principle** (`lostTensor`, `DAlembertPrinciple`,
  `dAlembertPrinciple_iff_inertial`).
* **§B — the principle on a field-equation solution** (`dAlembertPrinciple_of_fieldEquation`,
  `dAlembert_componentwise`, `leviCivita_dAlembert_principle`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §8, Eq. 10', 13): the gravitational (inertial) tensor and the
  generalisation of d'Alembert's principle. structures: `LeviCivita.GravitationalTensor`
  (`gravitationalTensor`, `dAlembert_balance`, `gravitationalTensor_eq_neg_matter`).

No new axioms.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.DAlembertPrinciple

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

variable {ι : Type*}

/-! ## §A — the lost tensor and d'Alembert's principle -/

/-- **The lost tensor** `L = T + A` — the sum of the directly-applied (matter) energy tensor `T` and the
inertial/gravitational tensor `A`, the "lost forces" of d'Alembert's principle. -/
def lostTensor (T A : Matrix ι ι ℝ) : Matrix ι ι ℝ := T + A

/-- **D'Alembert's principle (generalised)** `T + A = 0` — the lost forces balance: the matter and
inertial energy tensors identically cancel. -/
def DAlembertPrinciple (T A : Matrix ι ι ℝ) : Prop := lostTensor T A = 0

/-- **[D'Alembert's principle is the inertial balance] `T + A = 0 ⟺ A = −T`.** The principle says the
inertial/gravitational tensor is minus the applied (matter) tensor — the relativistic
`F_applied + F_inertial = 0`. -/
theorem dAlembertPrinciple_iff_inertial (T A : Matrix ι ι ℝ) :
    DAlembertPrinciple T A ↔ A = -T := by
  rw [DAlembertPrinciple, lostTensor, add_comm]
  exact add_eq_zero_iff_eq_neg

/-! ## §B — the principle on a field-equation solution -/

/-- **[D'Alembert's principle holds on a field-equation solution].** On a solution of the Einstein field
equation, the gravitational/inertial tensor `A = (1/κ)(G − ½gG)` satisfies d'Alembert's principle
`T + A = 0` (the d'Alembert balance, Eq. 10'). -/
theorem dAlembertPrinciple_of_fieldEquation (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) (h : einsteinFieldEquation Ric scalarR g T κ) :
    DAlembertPrinciple T (gravitationalTensor Ric scalarR g κ) :=
  dAlembert_balance Ric scalarR g T κ hκ h

/-- **[D'Alembert's principle holds component by component] `T_μν + A_μν = 0`.** Not only the total force,
but every mechanical action — stress `T_ik`, the force/momentum row `T_0i`, and the energy density `T_00` —
balances against its inertial counterpart: force and power vanish within each elementary portion of an
isolated system. -/
theorem dAlembert_componentwise (T A : Matrix ι ι ℝ) (h : DAlembertPrinciple T A) (μ ν : ι) :
    T μ ν + A μ ν = 0 := by
  have h' : T + A = 0 := h
  have hμν := congrFun (congrFun h' μ) ν
  simpa using hμν

/-- **[Levi-Civita's d'Alembert principle, assembled].** On a solution of the Einstein field equation
(`κ ≠ 0`):

* d'Alembert's principle holds, `T + A = 0` (the lost forces balance);
* the inertial/gravitational tensor is minus the applied tensor, `A = −T`;
* the balance holds component by component, `T_μν + A_μν = 0` (every mechanical action — stress,
  force/momentum, energy — balances).

The gravitational/inertial tensor is the four-dimensional generalisation of d'Alembert's principle: matter
and inertia, both encoded in `ds²`, cancel as the lost tensor of the relativistic equilibrium. -/
theorem leviCivita_dAlembert_principle (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) (h : einsteinFieldEquation Ric scalarR g T κ) :
    DAlembertPrinciple T (gravitationalTensor Ric scalarR g κ)
      ∧ gravitationalTensor Ric scalarR g κ = -T
      ∧ ∀ μ ν, T μ ν + (gravitationalTensor Ric scalarR g κ) μ ν = 0 :=
  ⟨dAlembertPrinciple_of_fieldEquation Ric scalarR g T κ hκ h,
    gravitationalTensor_eq_neg_matter Ric scalarR g T κ hκ h,
    dAlembert_componentwise T (gravitationalTensor Ric scalarR g κ)
      (dAlembertPrinciple_of_fieldEquation Ric scalarR g T κ hκ h)⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.DAlembertPrinciple

end
