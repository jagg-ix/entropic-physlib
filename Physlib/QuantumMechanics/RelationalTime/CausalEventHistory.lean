/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.WellFounded
meta import Zil

/-!
# Deterministic causal histories and their canonical clock

A deterministic local update and a well-founded causal event relation supply
four representation-independent facts: an initial state and event history have
a unique execution result; certified swaps of incomparable commuting events do
not change that result; any two duplicate-free causal linearizations of the same
finite event set are connected by such swaps under an explicit local commutation
law; and the predecessor-depth recurrence defines a unique normalized causal
clock.  No Lorentz, Bell, gravitational, or continuum law is inferred from this
discrete causal layer.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime.CausalEventHistory

/-! # A. Deterministic causal event histories -/

/-- A deterministic local event system with a well-founded causal relation and
a finite, complete enumeration of every event's predecessors. -/
structure CausalEventSystem (State Event : Type*) where
  step : Event → State → State
  before : Event → Event → Prop
  before_trans : ∀ {a b c}, before a b → before b c → before a c
  before_wf : WellFounded before
  predecessors : (e : Event) → Finset {p : Event // before p e}
  predecessors_complete : ∀ {p e}, before p e →
    ∃ q ∈ predecessors e, q.1 = p

namespace CausalEventSystem

variable {State Event : Type*} (C : CausalEventSystem State Event)

/-- Execute a finite event history from an initial state. -/
def run (initial : State) (events : List Event) : State :=
  events.foldl (fun state event ↦ C.step event state) initial

@[simp] lemma run_nil (initial : State) : C.run initial [] = initial := rfl

@[simp] lemma run_cons (initial : State) (e : Event) (events : List Event) :
    C.run initial (e :: events) = C.run (C.step e initial) events := rfl

lemma run_append (initial : State) (first second : List Event) :
    C.run initial (first ++ second) = C.run (C.run initial first) second :=
  List.foldl_append

/-- Operational execution relation for a fixed initial state and event history. -/
inductive Executes : State → List Event → State → Prop
  | nil (state : State) : Executes state [] state
  | cons (state : State) (event : Event) (events : List Event) (result : State) :
      Executes (C.step event state) events result →
      Executes state (event :: events) result

lemma run_executes (initial : State) (events : List Event) :
    C.Executes initial events (C.run initial events) := by
  induction events generalizing initial with
  | nil => exact Executes.nil initial
  | cons event events ih => exact Executes.cons initial event events _ (ih _)

lemma Executes.eq_run {initial result : State} {events : List Event}
    (h : C.Executes initial events result) : result = C.run initial events := by
  induction h with
  | nil => rfl
  | cons state event events result _ ih => exact ih

/-- **Deterministic history uniqueness.** Two executions with the same initial
state and event history have the same result. -/
@[zil_level structural]
theorem executes_unique {initial result₁ result₂ : State} {events : List Event}
    (h₁ : C.Executes initial events result₁)
    (h₂ : C.Executes initial events result₂) : result₁ = result₂ := by
  rw [h₁.eq_run, h₂.eq_run]

/-! # B. Scheduling invariance for independent events -/

/-- Two events are independent when neither causally precedes the other and
their deterministic state updates commute. -/
def Independent (e f : Event) : Prop :=
  ¬ C.before e f ∧ ¬ C.before f e ∧ Function.Commute (C.step e) (C.step f)

/-- Schedule equivalence generated only by swapping adjacent independent
events, together with reflexivity, symmetry, and transitivity. -/
inductive IndependentSwaps : List Event → List Event → Prop
  | refl (events : List Event) : IndependentSwaps events events
  | swap (pre suffix : List Event) (e f : Event) : C.Independent e f →
      IndependentSwaps (pre ++ e :: f :: suffix) (pre ++ f :: e :: suffix)
  | symm {first second : List Event} : IndependentSwaps first second →
      IndependentSwaps second first
  | trans {first second third : List Event} : IndependentSwaps first second →
      IndependentSwaps second third → IndependentSwaps first third

lemma run_swap_independent (initial : State) (pre suffix : List Event)
    (e f : Event) (h : C.Independent e f) :
    C.run initial (pre ++ e :: f :: suffix) =
      C.run initial (pre ++ f :: e :: suffix) := by
  simp only [C.run_append, C.run_cons]
  rw [h.2.2 (C.run initial pre)]

/-- **Scheduling invariance.** Reordering a history solely through adjacent
swaps of causally incomparable, commuting events does not change its result. -/
@[zil_level bridge_theorem]
theorem run_eq_of_independentSwaps {first second : List Event}
    (h : C.IndependentSwaps first second) (initial : State) :
    C.run initial first = C.run initial second := by
  induction h with
  | refl => rfl
  | swap pre suffix e f hIndependent =>
      exact C.run_swap_independent initial pre suffix e f hIndependent
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! # C. Finite causal confluence -/

/-- A causal linearization is a duplicate-free event list in which no later
event causally precedes an earlier event. -/
def IsCausalLinearization (events : List Event) : Prop :=
  events.Nodup ∧ events.Pairwise (fun earlier later => ¬ C.before later earlier)

/-- Local diamond condition: updates attached to causally incomparable events
commute.  This is an explicit hypothesis, not a consequence of incomparability. -/
def CommutesOnIncomparable : Prop :=
  ∀ e f, ¬ C.before e f → ¬ C.before f e → Function.Commute (C.step e) (C.step f)

/-- Prefixing the same history preserves independent-swap equivalence. -/
lemma IndependentSwaps.prefix (pre : List Event) {first second : List Event}
    (h : C.IndependentSwaps first second) :
    C.IndependentSwaps (pre ++ first) (pre ++ second) := by
  induction h with
  | refl events => exact IndependentSwaps.refl _
  | swap middle suffix e f hi =>
      simpa [List.append_assoc] using
        (IndependentSwaps.swap (C := C) (pre ++ middle) suffix e f hi)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Independent-swap equivalence preserves the event multiset. -/
lemma IndependentSwaps.perm {first second : List Event}
    (h : C.IndependentSwaps first second) : first.Perm second := by
  induction h with
  | refl events => exact List.Perm.refl events
  | swap pre suffix e f _ =>
      exact (List.Perm.refl pre).append (List.Perm.swap f e suffix)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Move an event left through a prefix whose events are all independent of it. -/
lemma independentSwaps_move_left (a : Event) (pre suffix : List Event)
    (h : ∀ b ∈ pre, C.Independent b a) :
    C.IndependentSwaps (pre ++ a :: suffix) (a :: pre ++ suffix) := by
  induction pre with
  | nil => exact IndependentSwaps.refl _
  | cons b pre ih =>
      have htail : C.IndependentSwaps (pre ++ a :: suffix) (a :: pre ++ suffix) :=
        ih (fun c hc => h c (by simp [hc]))
      have hlift := htail.prefix (C := C) [b]
      have hhead : C.IndependentSwaps (b :: a :: pre ++ suffix)
          (a :: b :: pre ++ suffix) := by
        simpa using (IndependentSwaps.swap (C := C) [] (pre ++ suffix) b a
          (h b (by simp)))
      simpa [List.append_assoc] using hlift.trans hhead

/-- **Finite causal confluence.** Any two duplicate-free causal linearizations
of the same finite event set are connected by adjacent independent swaps when
every causally incomparable pair has commuting updates.  The event orders need
not be equal; only their trace-monoid class is uniquely determined. -/
@[zil_level bridge_theorem]
theorem independentSwaps_of_perm_causalLinearizations
    {first second : List Event}
    (hfirst : C.IsCausalLinearization first)
    (hsecond : C.IsCausalLinearization second)
    (hperm : first.Perm second)
    (hcomm : C.CommutesOnIncomparable) :
    C.IndependentSwaps first second := by
  induction first generalizing second with
  | nil =>
      have hs : second = [] := hperm.symm.eq_nil
      subst second
      exact IndependentSwaps.refl []
  | cons a rest ih =>
      have ha : a ∈ second := hperm.mem_iff.mp (by simp)
      obtain ⟨pre, suffix, rfl⟩ := List.mem_iff_append.mp ha
      have hfirstTail : C.IsCausalLinearization rest := by
        exact ⟨(List.nodup_cons.mp hfirst.1).2,
          (List.pairwise_cons.mp hfirst.2).2⟩
      have hsecondParts := List.nodup_append.mp hsecond.1
      have hsecondPair := List.pairwise_append.mp hsecond.2
      have hsecondTail : C.IsCausalLinearization (pre ++ suffix) := by
        constructor
        · apply List.nodup_append.mpr
          exact ⟨hsecondParts.1, (List.nodup_cons.mp hsecondParts.2.1).2,
            fun b hb c hc => hsecondParts.2.2 b hb c (by simp [hc])⟩
        · apply List.pairwise_append.mpr
          exact ⟨hsecondPair.1, (List.pairwise_cons.mp hsecondPair.2.1).2,
            fun b hb c hc => hsecondPair.2.2 b hb c (by simp [hc])⟩
      have hindependent : ∀ b ∈ pre, C.Independent b a := by
        intro b hb
        have hba_ne : b ≠ a :=
          hsecondParts.2.2 b hb a (by simp)
        have hb_second : b ∈ pre ++ a :: suffix := by simp [hb]
        have hb_first : b ∈ a :: rest := hperm.mem_iff.mpr hb_second
        have hb_rest : b ∈ rest := by
          simpa [hba_ne] using hb_first
        have hnot_ba : ¬ C.before b a :=
          (List.pairwise_cons.mp hfirst.2).1 b hb_rest
        have hnot_ab : ¬ C.before a b :=
          hsecondPair.2.2 b hb a (by simp)
        exact ⟨hnot_ba, hnot_ab, hcomm b a hnot_ba hnot_ab⟩
      have hmove := C.independentSwaps_move_left a pre suffix hindependent
      have hrestPerm : rest.Perm (pre ++ suffix) := by
        exact (hperm.trans hmove.perm).cons_inv
      have htail := ih hfirstTail hsecondTail hrestPerm
      exact (htail.prefix (C := C) [a]).trans hmove.symm

/-- All causal linearizations of one finite event set produce the same final
state under the explicit local commutation law. -/
@[zil_level bridge_theorem]
theorem run_eq_of_perm_causalLinearizations
    {first second : List Event}
    (hfirst : C.IsCausalLinearization first)
    (hsecond : C.IsCausalLinearization second)
    (hperm : first.Perm second)
    (hcomm : C.CommutesOnIncomparable)
    (initial : State) : C.run initial first = C.run initial second :=
  C.run_eq_of_independentSwaps
    (C.independentSwaps_of_perm_causalLinearizations hfirst hsecond hperm hcomm) initial

/-! # D. The canonical causal clock -/

/-- The largest clock reading among the causal predecessors of `e`. -/
def predecessorSup (time : Event → ℕ) (e : Event) : ℕ :=
  (C.predecessors e).sup (fun p ↦ time p.1)

/-- Causal depth: one plus the greatest causal depth of any predecessor. -/
def causalDepth : Event → ℕ :=
  C.before_wf.fix fun e previous ↦
    (C.predecessors e).sup (fun p ↦ previous p.1 p.2) + 1

lemma causalDepth_eq (e : Event) :
    C.causalDepth e = C.predecessorSup C.causalDepth e + 1 := by
  rw [causalDepth, WellFounded.fix_eq]
  rfl

/-- Causal depth strictly increases along the causal relation. -/
lemma causalDepth_strict {p e : Event} (h : C.before p e) :
    C.causalDepth p < C.causalDepth e := by
  obtain ⟨q, hq, hqp⟩ := C.predecessors_complete h
  rw [C.causalDepth_eq e]
  apply Nat.lt_succ_of_le
  rw [predecessorSup]
  exact hqp ▸ Finset.le_sup (f := fun q ↦ C.causalDepth q.1) hq

/-- A positive causal clock is any natural-valued reading that strictly
increases along causal precedence. -/
def IsPositiveCausalClock (time : Event → ℕ) : Prop :=
  (∀ e, 0 < time e) ∧ ∀ p e, C.before p e → time p < time e

/-- **Minimality of causal depth.** Every positive causal clock lies pointwise
above the recursively defined causal depth. -/
@[zil_level structural]
theorem causalDepth_minimal {time : Event → ℕ}
    (hclock : C.IsPositiveCausalClock time) (e : Event) :
    C.causalDepth e ≤ time e := by
  induction e using C.before_wf.induction with
  | h e ih =>
      rw [C.causalDepth_eq, Nat.succ_le_iff]
      rw [predecessorSup]
      rw [Finset.sup_lt_iff (hclock.1 e)]
      intro p hp
      exact lt_of_le_of_lt (ih p.1 p.2) (hclock.2 p.1 e p.2)

/-- A normalized causal clock satisfies the same predecessor recurrence as
causal depth, including the convention that source events read `1`. -/
structure NormalizedCausalClock where
  time : Event → ℕ
  recurrence : ∀ e, time e = C.predecessorSup time e + 1

/-- Causal depth itself is a normalized causal clock. -/
def canonicalClock : C.NormalizedCausalClock where
  time := C.causalDepth
  recurrence := C.causalDepth_eq

/-- **Uniqueness of the normalized causal clock.** The predecessor recurrence
determines every event's reading, so every normalized causal clock is causal
depth. -/
@[zil_level bridge_theorem]
theorem NormalizedCausalClock.eq_causalDepth (clock : C.NormalizedCausalClock) :
    clock.time = C.causalDepth := by
  funext e
  induction e using C.before_wf.induction with
  | h e ih =>
      rw [clock.recurrence, C.causalDepth_eq]
      apply congrArg (fun n : ℕ ↦ n + 1)
      apply Finset.sup_congr rfl
      intro p hp
      exact ih p.1 p.2

/-- Any two normalized causal clocks agree pointwise. -/
lemma NormalizedCausalClock.unique (first second : C.NormalizedCausalClock) :
    first.time = second.time :=
  first.eq_causalDepth.trans second.eq_causalDepth.symm

end CausalEventSystem

/- ZIL-BEGIN -/

open Zil

zil attach CausalEventSystem.executes_unique where
  supported_by @ "lean:QuantumMechanics.SpaceDHilbertSpace.commute",
  formalizes @ "claim:an-initial-state-and-a-fixed-finite-causal-event-history-determine-a-unique-execution-result",
  determines @ "lean:Physlib.QuantumMechanics.RelationalTime.CausalEventHistory.CausalEventSystem.run",
  epistemic_status @ "consistency-identity"

zil attach CausalEventSystem.run_eq_of_independentSwaps where
  formalizes @ "claim:swapping-only-causally-incomparable-commuting-local-events-preserves-the-final-state",
  supported_by @ "lean:Function.Commute"

zil attach CausalEventSystem.independentSwaps_of_perm_causalLinearizations where
  formalizes @ "claim:any-two-duplicate-free-causal-linearizations-of-the-same-finite-event-set-are-connected-by-independent-swaps-under-the-local-commuting-diamond-law",
  supported_by @ "lean:List.Perm",
  caveat @ "claim:the-linearizations-need-not-be-equal-and-incomparable-updates-must-be-proved-to-commute"

zil attach CausalEventSystem.run_eq_of_perm_causalLinearizations where
  formalizes @ "claim:all-causal-linearizations-of-one-finite-event-set-have-the-same-final-state-under-the-local-commuting-diamond-law",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.CausalEventHistory.CausalEventSystem.independentSwaps_of_perm_causalLinearizations"

zil attach CausalEventSystem.causalDepth_minimal where
  formalizes @ "claim:recursive-causal-depth-is-the-pointwise-least-positive-natural-clock-strictly-increasing-along-causal-precedence",
  supported_by @ "lean:WellFounded.fix"

zil attach CausalEventSystem.NormalizedCausalClock.eq_causalDepth where
  formalizes @ "claim:the-predecessor-maximum-plus-one-recurrence-uniquely-determines-the-normalized-causal-clock",
  determines @ "lean:Physlib.QuantumMechanics.RelationalTime.CausalEventHistory.CausalEventSystem.causalDepth",
  supported_by @ "lean:WellFounded.fix"

zil_file_contract physlib.causalEventHistory where
  promises "A deterministic causal-history semantics in which a fixed initial state and event history have a unique execution result; adjacent swaps of causally incomparable commuting events preserve that result; any two duplicate-free causal linearizations of the same finite event set are connected by such swaps and therefore have the same final state under the explicit local commuting-diamond law; recursive causal depth is the least positive natural clock strictly increasing along causal precedence; and the predecessor-maximum-plus-one recurrence uniquely fixes the normalized causal clock."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Function.Commute",
    "lean:List.Perm",
    "lean:WellFounded.fix"
  ]
  forbids_substitutes [
    "claiming arbitrary incomparable updates commute without an explicit commutation proof",
    "claiming every topological ordering is unique",
    "deriving Lorentz Bell gravitational or continuum physics from the discrete event order alone"
  ]
  witnessed_by [
    CausalEventSystem.executes_unique,
    CausalEventSystem.run_eq_of_independentSwaps,
    CausalEventSystem.independentSwaps_of_perm_causalLinearizations,
    CausalEventSystem.run_eq_of_perm_causalLinearizations,
    CausalEventSystem.causalDepth_minimal,
    CausalEventSystem.NormalizedCausalClock.eq_causalDepth
  ]

#zil_formalization_lint physlib.causalEventHistory

/- ZIL-END -/

end Physlib.QuantumMechanics.RelationalTime.CausalEventHistory
