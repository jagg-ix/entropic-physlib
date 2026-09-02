/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Real.Basic
public import Physlib.Thermodynamics.Landauer
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Finite Poincare recurrence and the strict-Lyapunov dichotomy

Deterministic dynamics on a finite state space splits along injectivity, and the
split is exactly the reversible/erasing dichotomy of the thermodynamics of
computation:

* **Reversible side (finite Poincare recurrence).** A bijection of a finite
  state space has a positive global period: a single `n > 0` returns every
  state to itself (`bijective_global_period`). Injectivity alone suffices
  (`injective_global_period`), because injective self-maps of finite types are
  bijective - information-preserving evolution on finitely many states always
  returns.
* **No strict Lyapunov function under reversibility.** A strict Lyapunov
  function - one that strictly decreases on every state the dynamics moves -
  freezes any periodic dynamics (`isStrictLyapunov_fixed_of_periodic`): strict
  descent around a closed orbit would end strictly below its own starting
  value. Hence a finite reversible dynamics carrying a strict Lyapunov
  function has every state fixed (`isStrictLyapunov_bijective_forces_fixed`);
  monotone dissipation cannot arise inside a finite reversible dynamics.
* **Strict descent forces erasure.** Contrapositively, a dynamics on a finite
  state space that strictly decreases a state function somewhere it moves is
  not injective (`not_injective_of_isStrictLyapunov`). A strict
  entropy-production arrow requires merging of states - the non-injective
  side of the Landauer dichotomy formalized in
  `Physlib.Thermodynamics.ComputationLandauer`, where injective drivers
  preserve Kullback-Leibler divergence and only non-injective (erasing) steps
  pay a thermodynamic cost.
* **Minimal witnesses.** The bit flip is reversible, returns after two steps,
  and admits no strict Lyapunov function (`boolNot_no_strictLyapunov`); the
  bit reset carries the explicit strict Lyapunov function given by the
  indicator of the unerased state and is not injective
  (`boolReset_isStrictLyapunov`, `boolReset_not_injective`) - logical bit
  erasure in miniature.

**Honest boundary.** All statements concern deterministic dynamics on finite
state spaces (or `Bool`). No claim is made about infinite or continuum state
spaces, stochastic kernels, or which coarse-graining produces a physical
entropy; the arrow-of-time reading - no entropic arrow inside a finite
reversible dynamics - is the standard interpretation of the recurrence
theorem, and only the stated identities are proved.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov

variable {α : Type*}

/-- **Strict Lyapunov function** for a deterministic dynamics `f`: a real
state function that strictly decreases on every state that `f` moves. Fixed
points are exempt - descent is demanded only where there is motion. -/
def IsStrictLyapunov (f : α → α) (W : α → ℝ) : Prop :=
  ∀ x, f x ≠ x → W (f x) < W x

/-- Along a periodic orbit, one fixed iterate fixes the start: if
`f^[n] x = x` with `0 < n` and some iterate of `x` is a fixed point of `f`,
then `x` itself is fixed - past the fixed iterate the orbit sits still, yet it
must keep returning to `x`. -/
lemma fixed_of_iterate_fixed (f : α → α) {x : α} {n : ℕ} (hn : 0 < n)
    (hret : f^[n] x = x) {k : ℕ} (hfix : f (f^[k] x) = f^[k] x) :
    f x = x := by
  have hmul : f^[n * (k + 1)] x = x := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hret (k + 1)
  have hk : k ≤ n * (k + 1) :=
    le_trans (Nat.le_succ k) (Nat.le_mul_of_pos_left (k + 1) hn)
  have hx_eq : x = f^[k] x := by
    have hsplit : f^[n * (k + 1) - k + k] x = x := by
      rw [Nat.sub_add_cancel hk]; exact hmul
    rw [Function.iterate_add_apply] at hsplit
    calc x = f^[n * (k + 1) - k] (f^[k] x) := hsplit.symm
      _ = f^[k] x := Function.iterate_fixed hfix _
  calc f x = f (f^[k] x) := by rw [← hx_eq]
    _ = f^[k] x := hfix
    _ = x := hx_eq.symm

/-- **A strict Lyapunov function freezes periodic dynamics**: on a periodic
orbit (`f^[n] x = x` with `0 < n`) a strict Lyapunov function forces `x` to be
a fixed point, since strict descent around a closed loop would return strictly
below its own starting value. -/
@[zil_level physical_theorem]
theorem isStrictLyapunov_fixed_of_periodic {f : α → α} {W : α → ℝ}
    (hW : IsStrictLyapunov f W) {x : α} {n : ℕ} (hn : 0 < n)
    (hret : f^[n] x = x) : f x = x := by
  by_contra hx
  have hmove : ∀ k, f (f^[k] x) ≠ f^[k] x := fun k hfix =>
    hx (fixed_of_iterate_fixed f hn hret hfix)
  have hanti : StrictAnti fun k => W (f^[k] x) := by
    refine strictAnti_nat_of_succ_lt fun k => ?_
    have hstep := hW _ (hmove k)
    simpa [Function.iterate_succ_apply'] using hstep
  have hlt : W (f^[n] x) < W (f^[0] x) := hanti hn
  rw [hret] at hlt
  simp only [Function.iterate_zero_apply] at hlt
  exact lt_irrefl _ hlt

/-- **Finite Poincare recurrence, reversible form**: a bijection of a finite
state space has a positive global period - a single `n > 0` with `f^[n]`
returning every state to itself. The period is the order of the associated
permutation. -/
@[zil_level physical_theorem]
theorem bijective_global_period [Finite α] {f : α → α}
    (hf : Function.Bijective f) : ∃ n, 0 < n ∧ ∀ x, f^[n] x = x := by
  let e : Equiv.Perm α := Equiv.ofBijective f hf
  have hcoe : ⇑e = f := rfl
  refine ⟨orderOf e, orderOf_pos e, fun x => ?_⟩
  have h2 : (⇑e)^[orderOf e] x = x := by
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one e]
    rfl
  rw [← hcoe]
  exact h2

/-- **Finite Poincare recurrence, injective form**: an injective dynamics on a
finite state space is automatically bijective and hence globally periodic -
information-preserving evolution on finitely many states always returns. -/
@[zil_level physical_theorem]
theorem injective_global_period [Finite α] {f : α → α}
    (hf : Function.Injective f) : ∃ n, 0 < n ∧ ∀ x, f^[n] x = x :=
  bijective_global_period (Finite.injective_iff_bijective.mp hf)

/-- **No strict Lyapunov function under finite reversibility**: a bijection of
a finite state space carrying a strict Lyapunov function has every state
fixed. Equivalently, a finite reversible dynamics that moves any state at all
admits no strictly decreasing state function - monotone dissipation cannot be
generated inside a finite reversible dynamics. -/
@[zil_level physical_theorem]
theorem isStrictLyapunov_bijective_forces_fixed [Finite α] {f : α → α}
    (hf : Function.Bijective f) {W : α → ℝ} (hW : IsStrictLyapunov f W)
    (x : α) : f x = x := by
  obtain ⟨n, hn, hret⟩ := bijective_global_period hf
  exact isStrictLyapunov_fixed_of_periodic hW hn (hret x)

/-- **Strict descent forces erasure**: a deterministic dynamics on a finite
state space that strictly decreases a state function on some state it moves is
not injective. A strict entropy-production arrow requires merging of states -
the non-injective side of the Landauer dichotomy of
`Physlib.Thermodynamics.ComputationLandauer`. -/
@[zil_level physical_theorem]
theorem not_injective_of_isStrictLyapunov [Finite α] {f : α → α}
    {W : α → ℝ} (hW : IsStrictLyapunov f W) {x : α} (hx : f x ≠ x) :
    ¬ Function.Injective f := fun hinj =>
  hx (isStrictLyapunov_bijective_forces_fixed
    (Finite.injective_iff_bijective.mp hinj) hW x)

/-- **The bit flip admits no strict Lyapunov function**: the reversible NOT
gate moves both states, so strict descent would give `W false < W true` and
`W true < W false` simultaneously - the minimal instance of the freeze
theorem. -/
@[zil_level physical_theorem]
theorem boolNot_no_strictLyapunov (W : Bool → ℝ) :
    ¬ IsStrictLyapunov Bool.not W := by
  intro hW
  have h1 : W false < W true := by simpa using hW true (by simp)
  have h2 : W true < W false := by simpa using hW false (by simp)
  exact lt_irrefl _ (h1.trans h2)

/-- The bit reset - logical erasure of one bit. -/
def boolReset : Bool → Bool := fun _ => false

/-- **The bit reset carries an explicit strict Lyapunov function**: the
indicator of the unerased state strictly decreases on the one state the reset
moves. -/
@[zil_level physical_theorem]
theorem boolReset_isStrictLyapunov :
    IsStrictLyapunov boolReset fun b => if b then (1 : ℝ) else 0 := by
  intro x hx
  cases x with
  | false => simp [boolReset] at hx
  | true => simp [boolReset]

/-- **The bit reset is not injective**: erasure merges states, obtained as an
instance of `not_injective_of_isStrictLyapunov` from its explicit strict
Lyapunov function. -/
@[zil_level physical_theorem]
theorem boolReset_not_injective : ¬ Function.Injective boolReset :=
  not_injective_of_isStrictLyapunov boolReset_isStrictLyapunov
    (x := true) (by simp [boolReset])

/-- The bit flip returns after two steps - the minimal finite recurrence. -/
theorem boolNot_iterate_two : Bool.not^[2] = id := by
  funext b; cases b <;> rfl

/-- **The finite arrow dichotomy, assembled**: on a finite state space,
injective dynamics is globally periodic (recurrence - no escape to fresh
states), and any dynamics strictly decreasing a state function on a moved
state is non-injective (an arrow of strict descent is paid for by erasure). -/
@[zil_level physical_theorem]
theorem finite_arrow_dichotomy [Finite α] :
    (∀ f : α → α, Function.Injective f → ∃ n, 0 < n ∧ ∀ x, f^[n] x = x) ∧
    (∀ (f : α → α) (W : α → ℝ), IsStrictLyapunov f W →
      ∀ x, f x ≠ x → ¬ Function.Injective f) :=
  ⟨fun _ hf => injective_global_period hf,
   fun _ _ hW _ hx => not_injective_of_isStrictLyapunov hW hx⟩

end Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov

end

open Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov in
#physlib_axiom_clean_all [
  fixed_of_iterate_fixed,
  isStrictLyapunov_fixed_of_periodic,
  bijective_global_period,
  injective_global_period,
  isStrictLyapunov_bijective_forces_fixed,
  not_injective_of_isStrictLyapunov,
  boolNot_no_strictLyapunov,
  boolReset_isStrictLyapunov,
  boolReset_not_injective,
  boolNot_iterate_two,
  finite_arrow_dichotomy ]

open Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov in
#physlib_non_vacuous_all [
  fixed_of_iterate_fixed,
  isStrictLyapunov_fixed_of_periodic,
  bijective_global_period,
  injective_global_period,
  isStrictLyapunov_bijective_forces_fixed,
  not_injective_of_isStrictLyapunov,
  boolNot_no_strictLyapunov,
  boolReset_isStrictLyapunov,
  boolReset_not_injective,
  finite_arrow_dichotomy ]

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.bijective_global_period where
  formalizes @ "claim:finite-reversible-dynamics-is-globally-periodic-poincare-recurrence",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:poincare-1890-sur-le-probleme-des-trois-corps-et-les-equations-de-la-dynamique"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.injective_global_period where
  formalizes @ "claim:information-preserving-finite-dynamics-always-returns",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:poincare-1890-sur-le-probleme-des-trois-corps-et-les-equations-de-la-dynamique"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.isStrictLyapunov_fixed_of_periodic where
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.fixed_of_iterate_fixed",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:a-strict-lyapunov-function-freezes-periodic-dynamics",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.isStrictLyapunov_bijective_forces_fixed where
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.bijective_global_period",
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.isStrictLyapunov_fixed_of_periodic",
  formalizes @ "claim:no-strict-lyapunov-function-exists-for-a-moving-finite-reversible-dynamics",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:finite-state-spaces-only-no-continuum-or-stochastic-statement"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.not_injective_of_isStrictLyapunov where
  formalizes @ "claim:strict-monotone-descent-requires-state-merging-noninjective-dynamics",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:landauer-1961-irreversibility-and-heat-generation-in-the-computing-process",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.landauerEnergyForBits"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolNot_no_strictLyapunov where
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:the-reversible-bit-flip-admits-no-strict-lyapunov-function",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolReset_isStrictLyapunov where
  formalizes @ "claim:bit-reset-carries-an-explicit-strict-lyapunov-function",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:landauer-1961-irreversibility-and-heat-generation-in-the-computing-process"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolReset_not_injective where
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolReset_isStrictLyapunov",
  supported_by @ "lean:Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.not_injective_of_isStrictLyapunov",
  formalizes @ "claim:bit-reset-erasure-is-noninjective-as-an-instance-of-the-dichotomy",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.finite_arrow_dichotomy where
  formalizes @ "claim:the-finite-state-arrow-dichotomy-recurrence-versus-erasure",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:landauer-1961-irreversibility-and-heat-generation-in-the-computing-process",
  caveat @ "claim:the-arrow-of-time-reading-is-an-interpretation-only-the-stated-identities-are-proved"

zil_file_contract physlib.finiteRecurrenceStrictLyapunov where
  promises "Finite Poincare recurrence and the strict-Lyapunov dichotomy: bijective, equivalently injective, dynamics on a finite state space is globally periodic; a strict Lyapunov function freezes periodic dynamics, so a moving finite reversible dynamics admits none, and strict descent on a moved state forces non-injective erasing dynamics; with the bit flip and the bit reset as minimal witnesses."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:orderOf", "lean:pow_orderOf_eq_one",
    "lean:Equiv.Perm.coe_pow", "lean:Finite.injective_iff_bijective",
    "lean:strictAnti_nat_of_succ_lt"]
  forbids_substitutes ["a recurrence or dichotomy claim for infinite or continuum state spaces",
    "a stochastic-kernel or coarse-grained entropy statement",
    "a derivation of the thermodynamic Landauer bound from these finite-state identities"]
  witnessed_by [
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.bijective_global_period,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.injective_global_period,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.isStrictLyapunov_fixed_of_periodic,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.isStrictLyapunov_bijective_forces_fixed,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.not_injective_of_isStrictLyapunov,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolNot_no_strictLyapunov,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolReset_isStrictLyapunov,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.boolReset_not_injective,
    Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov.finite_arrow_dichotomy ]

/- ZIL-END -/

#zil_formalization_lint physlib.finiteRecurrenceStrictLyapunov
