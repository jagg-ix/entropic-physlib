/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.ZilDatalogFast

/-!
# The fast evaluator equals the reference evaluator — for every program

`Physlib.Meta.ZilDatalogFast.deriveProgramFast` was pinned to `Zil.Datalog.deriveProgram` by
42 example-based `#guard`s in `Physlib.Meta.ZilDatalogFastCheck`.  This module replaces that
regression evidence with a theorem: **for every program and every fuel budget the two
evaluators return the same list** — same atoms, same order, duplicates and all.

The proof splits along the four ways the fast engine deviates from the reference:

1. **Hash-set deduplication** (`dedupAtoms_eq_eraseDups`): the single-pass
   `Array`/`Std.HashSet` dedup equals `List.eraseDups`, by a fold invariant tying the hash
   set's `contains` to membership in the emitted prefix.
2. **Indexed joins** (`matchPatternIndexed_eq`, `excludesPatternIndexed_eq`): probing the
   narrowest determined bucket of `buildIndex` yields exactly the reference scan, because a
   bucket is the order-preserving filter of the fact list by its key
   (`buildIndex_spec`) and `Zil.Datalog.unify` rejects every atom the bucket excludes
   (`unify_eq_none_of_relation_ne`, `unify_eq_none_of_object_resolved`,
   `unify_eq_none_of_subject_resolved`).
3. **Deduplicated inputs** (`deriveStep_eraseDups`): the reference stratified driver feeds
   the *raw* fact list into its first round while the fast engine dedups first.  A
   first-occurrence-order calculus for `eraseDups` (`eraseDups_filterMap_eraseDups`,
   `eraseDups_flatMap_eraseDups`, `eraseDups_flatMap_congr`, …) shows a round over
   deduplicated facts produces the same deduplicated output as a round over the raw list:
   duplicated facts only ever re-derive atoms whose first occurrence is already in place.
4. **Early saturation** (`saturate_eq_refIter`): on deduplicated facts a round that does not
   grow the list is the identity (`deriveStep_eq_self_of_length_eq`), and the reference
   driver then spends its remaining fuel doing nothing (`refIter_eq_self_of_fixed`), so
   exiting early is invisible in the result.

The headline theorems are `deriveProgramFast_eq`, `deriveFast_eq`, `deriveRuleSetFast_eq`
and `deriveStratifiedFast_eq`.  `Physlib.Meta.ZilDatalogFastCheck`'s guards remain as fast
end-to-end smoke tests, but the semantic claim no longer rests on them.
-/

@[expose] public section

open Zil.Datalog

namespace Physlib.Meta.ZilDatalogFast

/-! ### Hashing lawfulness for the atom vocabulary -/

instance : LawfulHashable Value := ⟨fun a b h => by cases eq_of_beq h; rfl⟩
instance : LawfulHashable Atom := ⟨fun a b h => by cases eq_of_beq h; rfl⟩

/-! ### A first-occurrence calculus for `List.eraseDups`

`eraseDups` keeps the first occurrence of each element.  The fast evaluator is equal to the
reference *as a list* precisely because every one of its shortcuts preserves first-occurrence
order; the lemmas in this section make that reusable.
-/

section EraseDupsCalculus

variable {α β : Type} [BEq α] [LawfulBEq α]

theorem nodup_eraseDups : ∀ (l : List α), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_eraseDups _⟩
    have := (List.mem_filter.mp (List.mem_eraseDups.mp h)).2
    simp at this
  termination_by l => l.length
  decreasing_by
    simpa using Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_eq_self_of_nodup : ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    obtain ⟨ha, has⟩ := List.nodup_cons.mp h
    rw [List.eraseDups_cons,
      List.filter_eq_self.mpr fun b hb => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        exact fun hba => ha (hba ▸ hb),
      eraseDups_eq_self_of_nodup has]

theorem eraseDups_idem (l : List α) : l.eraseDups.eraseDups = l.eraseDups :=
  eraseDups_eq_self_of_nodup (nodup_eraseDups l)

omit [BEq α] [LawfulBEq α] in
/-- Filtering away elements the function ignores does not change a `filterMap`. -/
theorem filterMap_filter_eq_filterMap {p : α → Bool} {f : α → Option β}
    (h : ∀ a, p a = false → f a = none) : ∀ (l : List α),
    (l.filter p).filterMap f = l.filterMap f
  | [] => rfl
  | a :: t => by
    by_cases hp : p a
    · rw [List.filter_cons, if_pos hp, List.filterMap_cons, List.filterMap_cons,
        filterMap_filter_eq_filterMap h t]
    · rw [List.filter_cons, if_neg hp, List.filterMap_cons,
        h a (Bool.eq_false_iff.mpr hp), filterMap_filter_eq_filterMap h t]

omit [BEq α] [LawfulBEq α] in
/-- Filtering away elements with empty contribution does not change a `flatMap`. -/
theorem flatMap_filter_eq_flatMap {p : α → Bool} {g : α → List β}
    (h : ∀ a, p a = false → g a = []) : ∀ (l : List α),
    (l.filter p).flatMap g = l.flatMap g
  | [] => rfl
  | a :: t => by
    by_cases hp : p a
    · rw [List.filter_cons, if_pos hp, List.flatMap_cons, List.flatMap_cons,
        flatMap_filter_eq_flatMap h t]
    · rw [List.filter_cons, if_neg hp, List.flatMap_cons, h a (Bool.eq_false_iff.mpr hp),
        flatMap_filter_eq_flatMap h t, List.nil_append]

omit [BEq α] [LawfulBEq α] in
theorem filter_flatMap {p : β → Bool} {g : α → List β} : ∀ (l : List α),
    (l.flatMap g).filter p = l.flatMap fun a => (g a).filter p
  | [] => rfl
  | a :: t => by
    rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, filter_flatMap t]

/-- Deduplicating the input of a `filterMap` does not change the deduplicated output:
first occurrences map to first occurrences. -/
theorem eraseDups_filterMap_eraseDups [BEq β] [LawfulBEq β] :
    ∀ (f : α → Option β) (l : List α),
      (l.eraseDups.filterMap f).eraseDups = (l.filterMap f).eraseDups
  | f, [] => rfl
  | f, a :: t => by
    have hdrop : ∀ (f' : α → Option β), f' a = none →
        (t.filter (fun b => !b == a)).filterMap f' = t.filterMap f' := fun f' hfa =>
      filterMap_filter_eq_filterMap
        (fun b hb => by
          have hba : b = a := eq_of_beq (show (b == a) = true by simpa using hb)
          rw [hba]; exact hfa) t
    rw [List.eraseDups_cons, List.filterMap_cons, List.filterMap_cons]
    cases hfa : f a with
    | none =>
      rw [eraseDups_filterMap_eraseDups f (t.filter _), hdrop f hfa]
    | some v =>
      rw [List.eraseDups_cons, List.eraseDups_cons]
      congr 1
      rw [List.filter_filterMap, List.filter_filterMap,
        eraseDups_filterMap_eraseDups _ (t.filter _),
        hdrop _ (by rw [hfa]; simp [Option.filter])]
  termination_by _ l => l.length
  decreasing_by
    all_goals simpa using Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Deduplicating the outer list of a `flatMap` does not change the deduplicated output:
a duplicated element only replays a block whose atoms have all occurred already. -/
theorem eraseDups_flatMap_eraseDups [BEq β] [LawfulBEq β] :
    ∀ (g : α → List β) (l : List α),
      (l.eraseDups.flatMap g).eraseDups = (l.flatMap g).eraseDups
  | g, [] => rfl
  | g, a :: t => by
    rw [List.eraseDups_cons, List.flatMap_cons, List.flatMap_cons, List.eraseDups_append,
      List.eraseDups_append]
    congr 1
    simp only [List.removeAll]
    rw [filter_flatMap, filter_flatMap,
      eraseDups_flatMap_eraseDups _ (t.filter _),
      flatMap_filter_eq_flatMap
        (fun b hb => by
          have hba : b = a := eq_of_beq (show (b == a) = true by simpa using hb)
          rw [hba]
          exact List.filter_eq_nil_iff.mpr fun y hy => by
            simpa [List.elem_eq_contains, List.contains_iff_mem] using hy) t]
  termination_by _ l => l.length
  decreasing_by
    all_goals simpa using Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_flatMap_congr_left [BEq β] [LawfulBEq β] {xs ys : List α}
    (g : α → List β) (h : xs.eraseDups = ys.eraseDups) :
    (xs.flatMap g).eraseDups = (ys.flatMap g).eraseDups := by
  rw [← eraseDups_flatMap_eraseDups g xs, h, eraseDups_flatMap_eraseDups]

theorem eraseDups_filterMap_congr [BEq β] [LawfulBEq β] {xs ys : List α}
    (f : α → Option β) (h : xs.eraseDups = ys.eraseDups) :
    (xs.filterMap f).eraseDups = (ys.filterMap f).eraseDups := by
  rw [← eraseDups_filterMap_eraseDups f xs, h, eraseDups_filterMap_eraseDups]

theorem eraseDups_filter_eraseDups (p : α → Bool) (l : List α) :
    (l.eraseDups.filter p).eraseDups = (l.filter p).eraseDups := by
  have hrepr : ∀ (m : List α), m.filter p = m.filterMap fun x => if p x then some x else none := by
    intro m
    induction m with
    | nil => rfl
    | cons a t ih =>
      by_cases hp : p a
      · rw [List.filter_cons, if_pos hp, List.filterMap_cons, if_pos hp, ih]
      · rw [List.filter_cons, if_neg hp, List.filterMap_cons, if_neg hp, ih]
  rw [hrepr, hrepr, eraseDups_filterMap_eraseDups]

theorem eraseDups_filter_congr {xs ys : List α} (p : α → Bool)
    (h : xs.eraseDups = ys.eraseDups) :
    (xs.filter p).eraseDups = (ys.filter p).eraseDups := by
  rw [← eraseDups_filter_eraseDups p xs, h, eraseDups_filter_eraseDups]

theorem mem_congr_of_eraseDups_eq {xs ys : List α} (h : xs.eraseDups = ys.eraseDups)
    (a : α) : a ∈ xs ↔ a ∈ ys := by
  rw [← List.mem_eraseDups (l := xs), h, List.mem_eraseDups]

theorem any_congr_of_eraseDups_eq {xs ys : List α} (h : xs.eraseDups = ys.eraseDups)
    (f : α → Bool) : xs.any f = ys.any f := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hfx⟩ => ⟨x, (mem_congr_of_eraseDups_eq h x).mp hx, hfx⟩,
    fun ⟨x, hx, hfx⟩ => ⟨x, (mem_congr_of_eraseDups_eq h x).mpr hx, hfx⟩⟩

omit [BEq α] [LawfulBEq α] in
/-- Blockwise congruence for `flatMap` under deduplication. -/
theorem eraseDups_flatMap_congr [BEq β] [LawfulBEq β] :
    ∀ {g h : α → List β} (l : List α),
      (∀ x ∈ l, (g x).eraseDups = (h x).eraseDups) →
      (l.flatMap g).eraseDups = (l.flatMap h).eraseDups
  | _, _, [], _ => rfl
  | g, h, a :: t, hgh => by
    rw [List.flatMap_cons, List.flatMap_cons, List.eraseDups_append, List.eraseDups_append,
      hgh a List.mem_cons_self]
    congr 1
    simp only [List.removeAll]
    have hmem : ∀ y : β, ((h a).elem y) = ((g a).elem y) := fun y => by
      rw [Bool.eq_iff_iff, List.elem_eq_contains, List.elem_eq_contains,
        List.contains_iff_mem, List.contains_iff_mem]
      exact (mem_congr_of_eraseDups_eq (hgh a List.mem_cons_self) y).symm
    have hpred : (fun x => !(h a).elem x) = (fun x => !(g a).elem x) := by
      funext x; rw [hmem]
    rw [hpred, filter_flatMap, filter_flatMap]
    exact eraseDups_flatMap_congr t fun x hx =>
      eraseDups_filter_congr _ (hgh x (List.mem_cons_of_mem a hx))

end EraseDupsCalculus

/-! ### Layer 1 — the hash-set dedup is `List.eraseDups` -/

private theorem dedupAtoms_go :
    ∀ (as : List Atom) (arr : Array Atom) (seen : Std.HashSet Atom),
      (∀ x, seen.contains x = arr.toList.contains x) →
      ((as.foldl (fun acc a =>
          if acc.2.contains a then acc else (acc.1.push a, acc.2.insert a)) (arr, seen)).1.toList
        = arr.toList ++ (as.filter fun a => !arr.toList.contains a).eraseDups)
  | [], arr, seen, _ => by simp
  | a :: as, arr, seen, h => by
    rw [List.foldl_cons]
    by_cases hc : seen.contains a
    · rw [if_pos hc, dedupAtoms_go as arr seen h, List.filter_cons,
        if_neg (by rw [← h a]; simp [hc])]
    · have harr : arr.toList.contains a = false := by rw [← h a]; exact Bool.eq_false_iff.mpr hc
      rw [if_neg hc,
        dedupAtoms_go as (arr.push a) (seen.insert a) (fun x => by
          rw [Std.HashSet.contains_insert, h x, Array.toList_push, List.contains_append,
            Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, List.contains_iff_mem, List.contains_cons,
            List.contains_nil, Bool.or_false, beq_iff_eq]
          rw [eq_comm (a := a)]
          exact or_comm),
        Array.toList_push, List.filter_cons,
        if_pos (show (!arr.toList.contains a) = true by rw [harr]; rfl),
        List.eraseDups_cons, List.append_assoc, List.singleton_append, List.filter_filter]
      congr 2
      refine congrArg List.eraseDups (List.filter_congr fun b _ => ?_)
      rw [List.contains_append, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
        ne_eq, List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_or]
      constructor
      · exact fun ⟨hba, hbm⟩ => ⟨hbm, hba⟩
      · exact fun ⟨hbm, hba⟩ => ⟨hba, hbm⟩

theorem dedupAtoms_eq_eraseDups (as : List Atom) : dedupAtoms as = as.eraseDups := by
  unfold dedupAtoms
  rw [dedupAtoms_go as #[] ∅ (fun x => by simp)]
  simp only [List.nil_append]
  rw [List.filter_eq_self.mpr fun _ _ => by simp]

/-! ### Layer 2 — bucket contents and unification rejection -/

private structure IndexSpec (idx : FactIndex) (facts : List Atom) : Prop where
  rel : ∀ r, (idx.byRel.getD r #[]).toList = facts.filter fun a => a.relation == r
  obj : ∀ r v, (idx.byRelObject.getD (r, v) #[]).toList
    = facts.filter fun a => a.relation == r && a.object == v
  subj : ∀ r v, (idx.byRelSubject.getD (r, v) #[]).toList
    = facts.filter fun a => a.relation == r && a.subject == v

private theorem buildIndex_go :
    ∀ (facts : List Atom) (idx : FactIndex) (pre : List Atom), IndexSpec idx pre →
      IndexSpec (facts.foldl (fun idx a =>
        { byRel := pushAt idx.byRel a.relation a
          byRelObject := pushAt idx.byRelObject (a.relation, a.object) a
          byRelSubject := pushAt idx.byRelSubject (a.relation, a.subject) a }) idx)
        (pre ++ facts)
  | [], idx, pre, h => by simpa using h
  | a :: facts, idx, pre, h => by
    rw [List.foldl_cons]
    have step : IndexSpec
        { byRel := pushAt idx.byRel a.relation a
          byRelObject := pushAt idx.byRelObject (a.relation, a.object) a
          byRelSubject := pushAt idx.byRelSubject (a.relation, a.subject) a }
        (pre ++ [a]) := by
      refine ⟨fun r => ?_, fun r v => ?_, fun r v => ?_⟩
      · show ((pushAt idx.byRel a.relation a).getD r #[]).toList = _
        rw [pushAt, Std.HashMap.getD_insert, List.filter_append]
        by_cases hr : a.relation = r
        · subst hr
          rw [if_pos (by simp), Array.toList_push, h.rel a.relation, List.filter_cons,
            if_pos (by simp), List.filter_nil]
        · rw [if_neg (by simpa using hr), h.rel r, List.filter_cons,
            if_neg (by simpa using hr), List.filter_nil, List.append_nil]
      · show ((pushAt idx.byRelObject (a.relation, a.object) a).getD (r, v) #[]).toList = _
        rw [pushAt, Std.HashMap.getD_insert, List.filter_append]
        by_cases hk : r = a.relation ∧ v = a.object
        · obtain ⟨rfl, rfl⟩ := hk
          rw [if_pos (by simp), Array.toList_push, h.obj a.relation a.object,
            List.filter_cons, if_pos (by simp), List.filter_nil]
        · have hkb : ¬(((a.relation, a.object) == (r, v)) = true) := by
            intro hc
            have := eq_of_beq hc
            exact hk ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
          have hpred : ¬((a.relation == r && a.object == v) = true) := by
            intro hc
            obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _) ▸ hc
            exact hk ⟨(eq_of_beq h1).symm, (eq_of_beq h2).symm⟩
          rw [if_neg hkb, h.obj r v, List.filter_cons, if_neg hpred,
            List.filter_nil, List.append_nil]
      · show ((pushAt idx.byRelSubject (a.relation, a.subject) a).getD (r, v) #[]).toList = _
        rw [pushAt, Std.HashMap.getD_insert, List.filter_append]
        by_cases hk : r = a.relation ∧ v = a.subject
        · obtain ⟨rfl, rfl⟩ := hk
          rw [if_pos (by simp), Array.toList_push, h.subj a.relation a.subject,
            List.filter_cons, if_pos (by simp), List.filter_nil]
        · have hkb : ¬(((a.relation, a.subject) == (r, v)) = true) := by
            intro hc
            have := eq_of_beq hc
            exact hk ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
          have hpred : ¬((a.relation == r && a.subject == v) = true) := by
            intro hc
            obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _) ▸ hc
            exact hk ⟨(eq_of_beq h1).symm, (eq_of_beq h2).symm⟩
          rw [if_neg hkb, h.subj r v, List.filter_cons, if_neg hpred,
            List.filter_nil, List.append_nil]
    have hres := buildIndex_go facts _ (pre ++ [a]) step
    rw [show (pre ++ [a]) ++ facts = pre ++ a :: facts by simp] at hres
    exact hres

private theorem buildIndex_spec (facts : List Atom) : IndexSpec (buildIndex facts) facts := by
  have h0 : IndexSpec { byRel := ∅, byRelObject := ∅, byRelSubject := ∅ } [] := by
    refine ⟨fun r => ?_, fun r v => ?_, fun r v => ?_⟩ <;> simp
  unfold buildIndex
  have hres := buildIndex_go facts _ [] h0
  simpa using hres

theorem unify_eq_none_of_relation_ne {p : Pattern} {a : Atom} (s : Substitution)
    (h : (p.relation == a.relation) = false) : unify p a s = none := by
  unfold unify
  simp [bne, h]

theorem unify_eq_none_of_object_resolved {p : Pattern} {a : Atom} {s : Substitution} {v : Value}
    (hres : resolveTerm s p.object = some v) (hne : (a.object == v) = false) :
    unify p a s = none := by
  unfold unify
  by_cases hrel : p.relation != a.relation
  · simp [hrel]
  · have hobj : unifyTerm p.object a.object s = none := by
      cases hp : p.object with
      | «value» w =>
        have hw : w = v := by simpa [resolveTerm, hp] using hres
        subst hw
        have : (w == a.object) = false := by
          rw [Bool.eq_false_iff] at hne ⊢
          exact fun hc => hne (beq_iff_eq.mpr (eq_of_beq hc).symm)
        simp [unifyTerm, this]
      | «variable» n =>
        have hlook : lookup n s = some v := by simpa [resolveTerm, hp] using hres
        have : (v == a.object) = false := by
          rw [Bool.eq_false_iff] at hne ⊢
          exact fun hc => hne (beq_iff_eq.mpr (eq_of_beq hc).symm)
        simp [unifyTerm, Zil.Datalog.bind, hlook, this]
    simp [hrel, hobj]

theorem unify_eq_none_of_subject_resolved {p : Pattern} {a : Atom} {s : Substitution} {v : Value}
    (hobj : resolveTerm s p.object = none) (hres : resolveTerm s p.subject = some v)
    (hne : (a.subject == v) = false) : unify p a s = none := by
  unfold unify
  by_cases hrel : p.relation != a.relation
  · simp [hrel]
  · obtain ⟨n, hn⟩ : ∃ n, p.object = .variable n := by
      cases hp : p.object with
      | «value» w => rw [hp] at hobj; simp [resolveTerm] at hobj
      | «variable» n => exact ⟨n, rfl⟩
    have hlookn : lookup n s = none := by simpa [resolveTerm, hn] using hobj
    have hbindn : unifyTerm p.object a.object s = some ((n, a.object) :: s) := by
      simp [unifyTerm, hn, Zil.Datalog.bind, hlookn]
    have hsubj : unifyTerm p.subject a.subject ((n, a.object) :: s) = none := by
      cases hp : p.subject with
      | «value» w =>
        have hw : w = v := by simpa [resolveTerm, hp] using hres
        subst hw
        have : (w == a.subject) = false := by
          rw [Bool.eq_false_iff] at hne ⊢
          exact fun hc => hne (beq_iff_eq.mpr (eq_of_beq hc).symm)
        simp [unifyTerm, this]
      | «variable» m =>
        have hlookm : lookup m s = some v := by simpa [resolveTerm, hp] using hres
        have hmn : (m == n) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          rw [eq_of_beq hc] at hlookm
          rw [hlookn] at hlookm
          simp at hlookm
        have hlookm' : lookup m ((n, a.object) :: s) = some v := by
          rw [lookup, List.lookup, hmn]
          exact hlookm
        have : (v == a.subject) = false := by
          rw [Bool.eq_false_iff] at hne ⊢
          exact fun hc => hne (beq_iff_eq.mpr (eq_of_beq hc).symm)
        simp [unifyTerm, Zil.Datalog.bind, hlookm', this]
    simp [hrel, hbindn, hsubj]

/-! ### Layer 3 — the indexed pipeline equals the reference pipeline -/

theorem matchPatternIndexed_eq (facts : List Atom) (p : Pattern) (s : Substitution) :
    matchPatternIndexed (buildIndex facts) p s = matchPattern facts p s := by
  have spec := buildIndex_spec facts
  unfold matchPatternIndexed candidates matchPattern
  cases hobj : resolveTerm s p.object with
  | some v =>
    rw [spec.obj p.relation v]
    exact filterMap_filter_eq_filterMap (fun a ha => by
      rcases Bool.and_eq_false_iff.mp ha with h | h
      · exact unify_eq_none_of_relation_ne s (by
          rw [Bool.eq_false_iff] at h ⊢
          exact fun hc => h (beq_iff_eq.mpr (eq_of_beq hc).symm))
      · exact unify_eq_none_of_object_resolved hobj h) facts
  | none =>
    cases hsubj : resolveTerm s p.subject with
    | some v =>
      rw [spec.subj p.relation v]
      exact filterMap_filter_eq_filterMap (fun a ha => by
        rcases Bool.and_eq_false_iff.mp ha with h | h
        · exact unify_eq_none_of_relation_ne s (by
            rw [Bool.eq_false_iff] at h ⊢
            exact fun hc => h (beq_iff_eq.mpr (eq_of_beq hc).symm))
        · exact unify_eq_none_of_subject_resolved hobj hsubj h) facts
    | none =>
      rw [spec.rel p.relation]
      exact filterMap_filter_eq_filterMap (fun a ha =>
        unify_eq_none_of_relation_ne s (by
          rw [Bool.eq_false_iff] at ha ⊢
          exact fun hc => ha (beq_iff_eq.mpr (eq_of_beq hc).symm))) facts

private theorem any_filter_eq_any {p : α → Bool} {f : α → Bool}
    (h : ∀ a, p a = false → f a = false) : ∀ (l : List α), (l.filter p).any f = l.any f
  | [] => rfl
  | a :: t => by
    by_cases hp : p a
    · rw [List.filter_cons, if_pos hp, List.any_cons, List.any_cons, any_filter_eq_any h t]
    · rw [List.filter_cons, if_neg hp, List.any_cons, h a (Bool.eq_false_iff.mpr hp),
        any_filter_eq_any h t, Bool.false_or]

theorem excludesPatternIndexed_eq (facts : List Atom) (p : Pattern) (s : Substitution) :
    excludesPatternIndexed (buildIndex facts) p s = excludesPattern facts p s := by
  have spec := buildIndex_spec facts
  unfold excludesPatternIndexed excludesPattern
  congr 1
  rw [← Array.any_toList]
  cases hobj : resolveTerm s p.object with
  | some v =>
    rw [show candidates (buildIndex facts) p s
        = ((facts.filter fun a => a.relation == p.relation && a.object == v).toArray) by
      unfold candidates; rw [hobj, ← spec.obj p.relation v, Array.toArray_toList]]
    rw [List.toList_toArray]
    exact any_filter_eq_any (fun a ha => by
      rcases Bool.and_eq_false_iff.mp ha with h | h
      · simp [unify_eq_none_of_relation_ne s (by
          rw [Bool.eq_false_iff] at h ⊢
          exact fun hc => h (beq_iff_eq.mpr (eq_of_beq hc).symm))]
      · simp [unify_eq_none_of_object_resolved hobj h]) facts
  | none =>
    cases hsubj : resolveTerm s p.subject with
    | some v =>
      rw [show candidates (buildIndex facts) p s
          = ((facts.filter fun a => a.relation == p.relation && a.subject == v).toArray) by
        unfold candidates; rw [hobj, hsubj, ← spec.subj p.relation v, Array.toArray_toList]]
      rw [List.toList_toArray]
      exact any_filter_eq_any (fun a ha => by
        rcases Bool.and_eq_false_iff.mp ha with h | h
        · simp [unify_eq_none_of_relation_ne s (by
            rw [Bool.eq_false_iff] at h ⊢
            exact fun hc => h (beq_iff_eq.mpr (eq_of_beq hc).symm))]
        · simp [unify_eq_none_of_subject_resolved hobj hsubj h]) facts
    | none =>
      rw [show candidates (buildIndex facts) p s
          = ((facts.filter fun a => a.relation == p.relation).toArray) by
        unfold candidates; rw [hobj, hsubj, ← spec.rel p.relation, Array.toArray_toList]]
      rw [List.toList_toArray]
      exact any_filter_eq_any (fun a ha => by
        simp [unify_eq_none_of_relation_ne s (by
          rw [Bool.eq_false_iff] at ha ⊢
          exact fun hc => ha (beq_iff_eq.mpr (eq_of_beq hc).symm))]) facts

theorem satisfyBodyIndexed_eq (facts : List Atom) (body : List Pattern) :
    satisfyBodyIndexed (buildIndex facts) body = satisfyBody facts body := by
  unfold satisfyBodyIndexed satisfyBody
  congr 1
  funext subs p
  congr 1
  funext s
  exact matchPatternIndexed_eq facts p s

theorem satisfyNegativeBodyIndexed_eq (facts : List Atom) (body : List Pattern)
    (subs : List Substitution) :
    satisfyNegativeBodyIndexed (buildIndex facts) body subs
      = satisfyNegativeBody facts body subs := by
  unfold satisfyNegativeBodyIndexed satisfyNegativeBody
  congr 1
  funext remaining p
  congr 1
  funext s
  exact excludesPatternIndexed_eq facts p s

theorem applyRuleIndexed_eq (facts : List Atom) (rule : Rule) :
    applyRuleIndexed (buildIndex facts) rule = applyRule facts rule := by
  unfold applyRuleIndexed applyRule
  rw [satisfyBodyIndexed_eq, satisfyNegativeBodyIndexed_eq]

theorem stepIndexed_eq (rules : List Rule) (facts : List Atom) :
    stepIndexed rules facts = (facts ++ rules.flatMap (applyRule facts)).eraseDups := by
  unfold stepIndexed
  rw [dedupAtoms_eq_eraseDups]
  congr 3
  funext r
  exact applyRuleIndexed_eq facts r

/-! ### Layer 4 — a round over deduplicated facts, deduplicated, is a round over raw facts -/

theorem satisfyBody_dedup (facts : List Atom) (body : List Pattern) :
    (satisfyBody facts.eraseDups body).eraseDups = (satisfyBody facts body).eraseDups := by
  unfold satisfyBody
  suffices h : ∀ (body : List Pattern) (xs ys : List Substitution),
      xs.eraseDups = ys.eraseDups →
      (body.foldl (fun subs p => subs.flatMap (matchPattern facts.eraseDups p)) xs).eraseDups
        = (body.foldl (fun subs p => subs.flatMap (matchPattern facts p)) ys).eraseDups by
    exact h body [[]] [[]] rfl
  intro body
  induction body with
  | nil => exact fun xs ys h => h
  | cons p rest ih =>
    intro xs ys h
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    have h1 : (xs.flatMap (matchPattern facts.eraseDups p)).eraseDups
        = (ys.flatMap (matchPattern facts.eraseDups p)).eraseDups :=
      eraseDups_flatMap_congr_left _ h
    have h2 : (ys.flatMap (matchPattern facts.eraseDups p)).eraseDups
        = (ys.flatMap (matchPattern facts p)).eraseDups :=
      eraseDups_flatMap_congr ys fun s _ =>
        eraseDups_filterMap_congr _ (eraseDups_idem facts)
    exact h1.trans h2

theorem excludesPattern_dedup (facts : List Atom) (p : Pattern) (s : Substitution) :
    excludesPattern facts.eraseDups p s = excludesPattern facts p s := by
  unfold excludesPattern
  rw [any_congr_of_eraseDups_eq (eraseDups_idem facts)]

theorem satisfyNegativeBody_dedup (facts : List Atom) (body : List Pattern)
    {xs ys : List Substitution} (h : xs.eraseDups = ys.eraseDups) :
    (satisfyNegativeBody facts.eraseDups body xs).eraseDups
      = (satisfyNegativeBody facts body ys).eraseDups := by
  unfold satisfyNegativeBody
  induction body generalizing xs ys with
  | nil => exact h
  | cons p rest ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih ?_
    have hpred : excludesPattern facts.eraseDups p = excludesPattern facts p := by
      funext s; exact excludesPattern_dedup facts p s
    rw [hpred]
    exact eraseDups_filter_congr _ h

theorem applyRule_dedup (facts : List Atom) (rule : Rule) :
    (applyRule facts.eraseDups rule).eraseDups = (applyRule facts rule).eraseDups := by
  unfold applyRule
  exact eraseDups_filterMap_congr _
    (satisfyNegativeBody_dedup facts rule.negativePatterns
      (satisfyBody_dedup facts rule.positiveBody))

/-- One reference round over the deduplicated facts equals one reference round over the raw
facts: the first stratified round may consume raw facts without changing the result. -/
theorem deriveStep_eraseDups (rules : List Rule) (facts : List Atom) :
    (facts.eraseDups ++ rules.flatMap (applyRule facts.eraseDups)).eraseDups
      = (facts ++ rules.flatMap (applyRule facts)).eraseDups := by
  rw [List.eraseDups_append, List.eraseDups_append, eraseDups_idem]
  congr 1
  simp only [List.removeAll]
  have hpred : (fun x : Atom => !facts.eraseDups.elem x) = (fun x => !facts.elem x) := by
    funext x
    have : (facts.eraseDups.elem x) = (facts.elem x) := by
      rw [Bool.eq_iff_iff, List.elem_eq_contains, List.elem_eq_contains,
        List.contains_iff_mem, List.contains_iff_mem, List.mem_eraseDups]
    rw [this]
  rw [hpred]
  refine eraseDups_filter_congr _ ?_
  exact eraseDups_flatMap_congr rules fun r _ => applyRule_dedup facts r

/-! ### Layer 5 — saturation -/

/-- The reference round, named. -/
private def refStep (rules : List Rule) (facts : List Atom) : List Atom :=
  (facts ++ rules.flatMap (applyRule facts)).eraseDups

/-- Reference iteration, outermost-step form. -/
private def refIter (rules : List Rule) : Nat → List Atom → List Atom
  | 0, l => l
  | n + 1, l => refStep rules (refIter rules n l)

private theorem refIter_step_comm (rules : List Rule) :
    ∀ (n : Nat) (l : List Atom), refIter rules n (refStep rules l) = refStep rules (refIter rules n l)
  | 0, _ => rfl
  | n + 1, l => by rw [refIter, refIter, refIter_step_comm rules n l]

private theorem refIter_eq_self_of_fixed (rules : List Rule) {l : List Atom}
    (h : refStep rules l = l) : ∀ n, refIter rules n l = l
  | 0 => rfl
  | n + 1 => by rw [refIter, refIter_eq_self_of_fixed rules h n, h]

private theorem nodup_refStep (rules : List Rule) (l : List Atom) : (refStep rules l).Nodup :=
  nodup_eraseDups _

private theorem refStep_prefix (rules : List Rule) {l : List Atom} (h : l.Nodup) :
    refStep rules l = l ++ ((rules.flatMap (applyRule l)).removeAll l).eraseDups := by
  rw [refStep, List.eraseDups_append, eraseDups_eq_self_of_nodup h]

private theorem refStep_eq_self_of_length_eq (rules : List Rule) {l : List Atom}
    (hnd : l.Nodup) (hlen : (refStep rules l).length = l.length) : refStep rules l = l := by
  rw [refStep_prefix rules hnd] at hlen ⊢
  rw [List.length_append] at hlen
  have : ((rules.flatMap (applyRule l)).removeAll l).eraseDups.length = 0 := by omega
  rw [List.length_eq_zero_iff.mp this, List.append_nil]

private theorem saturate_eq_refIter (rules : List Rule) :
    ∀ (fuel : Nat) {l : List Atom}, l.Nodup → saturate rules fuel l = refIter rules fuel l
  | 0, _, _ => rfl
  | fuel + 1, l, hnd => by
    rw [saturate, stepIndexed_eq]
    show (if (refStep rules l).length == l.length then refStep rules l
        else saturate rules fuel (refStep rules l)) = _
    by_cases hlen : (refStep rules l).length = l.length
    · rw [if_pos (by simpa using hlen)]
      have hfix := refStep_eq_self_of_length_eq rules hnd hlen
      rw [refIter, refIter_eq_self_of_fixed rules hfix fuel, hfix]
    · rw [if_neg (by simpa using hlen),
        saturate_eq_refIter rules fuel (nodup_refStep rules l), refIter_step_comm, refIter]

/-! ### The headline equivalences -/

/-- The fast non-stratified driver equals the reference `derive`. -/
theorem deriveFast_eq (program : Program) (fuel : Nat) :
    deriveFast program fuel = derive program fuel := by
  have hder : ∀ n, derive program n = refIter program.rules n program.facts.eraseDups := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derive, ih]; rfl
  rw [deriveFast, dedupAtoms_eq_eraseDups,
    saturate_eq_refIter program.rules fuel (nodup_eraseDups _), hder]

/-- The fast per-stratum driver equals the reference `deriveRuleSet` — on raw fact lists,
duplicates included. -/
theorem deriveRuleSetFast_eq (rules : List Rule) :
    ∀ (fuel : Nat) (facts : List Atom),
      deriveRuleSetFast rules fuel facts = deriveRuleSet rules fuel facts
  | 0, facts => by
    rw [deriveRuleSetFast, dedupAtoms_eq_eraseDups, deriveRuleSet]
    rfl
  | fuel + 1, facts => by
    have hraw : refStep rules facts.eraseDups
        = (facts ++ rules.flatMap (applyRule facts)).eraseDups := by
      rw [refStep, deriveStep_eraseDups]
    rw [deriveRuleSetFast, dedupAtoms_eq_eraseDups,
      saturate_eq_refIter rules (fuel + 1) (nodup_eraseDups _), refIter,
      refIter_step_comm rules fuel _ |>.symm, hraw, deriveRuleSet]
    rw [← deriveRuleSetFast_eq rules fuel ((facts ++ rules.flatMap (applyRule facts)).eraseDups),
      deriveRuleSetFast, dedupAtoms_eq_eraseDups, eraseDups_idem,
      saturate_eq_refIter rules fuel (nodup_eraseDups _)]

/-- The fast stratified driver equals the reference `deriveStratified`. -/
theorem deriveStratifiedFast_eq (program : Program) (fuel : Nat) :
    deriveStratifiedFast program fuel = deriveStratified program fuel := by
  rw [deriveStratifiedFast, deriveStratified]
  congr 1
  funext facts stratum
  exact deriveRuleSetFast_eq _ fuel facts

/-- **The fast evaluator equals the reference evaluator, for every program and every fuel
budget** — same atoms, same order, no side conditions.  The 42 `#guard`s of
`Physlib.Meta.ZilDatalogFastCheck` are instances of this theorem. -/
theorem deriveProgramFast_eq (program : Program) (fuel : Nat) :
    deriveProgramFast program fuel = deriveProgram program fuel := by
  rw [deriveProgramFast, deriveProgram]
  by_cases h : program.hasNegation
  · rw [if_pos h, if_pos h, deriveStratifiedFast_eq]
  · rw [if_neg h, if_neg h, deriveFast_eq]

end Physlib.Meta.ZilDatalogFast
