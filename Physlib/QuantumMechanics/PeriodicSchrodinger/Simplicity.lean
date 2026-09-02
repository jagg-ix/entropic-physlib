/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.ResonanceMatrix

/-!
# Separation and simplicity of Bloch eigenvalue labels

Veliev's simple sets are defined by requiring the known part of a selected
Bloch eigenvalue to remain at least `2 ε` away from the known parts of all
competing nonresonant and resonant eigenvalues.  Since each true eigenvalue is
within `ε` of its known part, two competing labels cannot describe the same
true eigenvalue.

This file isolates that argument in a reusable metric form.  It applies to
finite or infinite label types and does not presuppose a concrete spectral
enumeration.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

/-- A true spectral value is approximated by a known part to accuracy `ε`. -/
def ApproximatesKnownPart {A : Type*}
    (known : A → ℝ) (trueValue : ℝ) (a : A) (ε : ℝ) : Prop :=
  dist trueValue (known a) < ε

/-- Two known spectral parts are separated at scale `ε`. -/
def KnownPartsSeparated {A : Type*}
    (known : A → ℝ) (a b : A) (ε : ℝ) : Prop :=
  2 * ε ≤ dist (known a) (known b)

/-- Two labels whose known parts are separated by `2 ε` cannot both
approximate the same true eigenvalue within `ε`. -/
theorem not_both_approximate_of_separated
    {A : Type*} (known : A → ℝ)
    (trueValue : ℝ) (a b : A) (ε : ℝ)
    (hsep : KnownPartsSeparated known a b ε) :
    ¬ (ApproximatesKnownPart known trueValue a ε ∧
        ApproximatesKnownPart known trueValue b ε) := by
  rintro ⟨ha, hb⟩
  have htri :
      dist (known a) (known b) ≤
        dist (known a) trueValue + dist trueValue (known b) :=
    dist_triangle _ _ _
  have hlt :
      dist (known a) (known b) < 2 * ε := by
    calc
      dist (known a) (known b) ≤
          dist (known a) trueValue + dist trueValue (known b) := htri
      _ < ε + ε := add_lt_add
        (by simpa only [ApproximatesKnownPart, dist_comm] using ha) hb
      _ = 2 * ε := by ring
  exact (not_lt_of_ge hsep) hlt

/-- A label is simple at resolution `ε` when its known part is separated from
every distinct competing label. -/
def IsSimpleKnownLabel {A : Type*}
    (known : A → ℝ) (selected : A) (ε : ℝ) : Prop :=
  ∀ other, other ≠ selected →
    KnownPartsSeparated known selected other ε

/-- A simple selected label is the unique label whose known part can
approximate the same true eigenvalue within `ε`. -/
theorem unique_label_of_simple
    {A : Type*} (known : A → ℝ)
    (selected : A) (trueValue ε : ℝ)
    (hsimple : IsSimpleKnownLabel known selected ε)
    (hselected : ApproximatesKnownPart known trueValue selected ε) :
    ∀ other,
      ApproximatesKnownPart known trueValue other ε →
        other = selected := by
  intro other hother
  by_contra hne
  exact not_both_approximate_of_separated known trueValue selected other ε
    (hsimple other hne) ⟨hselected, hother⟩

/-- The two classes of competing known parts in Veliev's simplicity
conditions: other nonresonant expansions and finite resonance-matrix
eigenvalues. -/
structure TwoFamilySimplicity
    (A B : Type*) (knownA : A → ℝ) (knownB : B → ℝ)
    (selected : A) (ε : ℝ) : Prop where
  /-- Separation from every other nonresonant known part. -/
  nonresonant : ∀ a, a ≠ selected →
    2 * ε ≤ dist (knownA selected) (knownA a)
  /-- Separation from every resonant matrix known part. -/
  resonant : ∀ b,
    2 * ε ≤ dist (knownA selected) (knownB b)

/-- A true value close to the selected nonresonant known part cannot also be
close to another nonresonant known part. -/
theorem TwoFamilySimplicity.unique_nonresonant
    {A B : Type*} {knownA : A → ℝ} {knownB : B → ℝ}
    {selected : A} {ε trueValue : ℝ}
    (h : TwoFamilySimplicity A B knownA knownB selected ε)
    (hselected : ApproximatesKnownPart knownA trueValue selected ε) :
    ∀ a,
      ApproximatesKnownPart knownA trueValue a ε → a = selected := by
  intro a ha
  by_contra hne
  exact not_both_approximate_of_separated knownA trueValue selected a ε
    (h.nonresonant a hne) ⟨hselected, ha⟩

/-- A true value close to the selected nonresonant known part cannot also be
close to a resonant matrix known part. -/
theorem TwoFamilySimplicity.excludes_resonant
    {A B : Type*} {knownA : A → ℝ} {knownB : B → ℝ}
    {selected : A} {ε trueValue : ℝ}
    (h : TwoFamilySimplicity A B knownA knownB selected ε)
    (hselected : ApproximatesKnownPart knownA trueValue selected ε) :
    ∀ b, ¬ ApproximatesKnownPart knownB trueValue b ε := by
  intro b hb
  have htri :
      dist (knownA selected) (knownB b) ≤
        dist (knownA selected) trueValue +
          dist trueValue (knownB b) :=
    dist_triangle _ _ _
  have hlt : dist (knownA selected) (knownB b) < 2 * ε := by
    calc
      dist (knownA selected) (knownB b) ≤
          dist (knownA selected) trueValue +
            dist trueValue (knownB b) := htri
      _ < ε + ε :=
        add_lt_add
          (by simpa only [ApproximatesKnownPart, dist_comm] using hselected) hb
      _ = 2 * ε := by ring
  exact (not_lt_of_ge (h.resonant b)) hlt

/-- A simple-set predicate indexed by quasimomentum. -/
def InSimpleSet {K A B : Type*}
    (selected : K → A)
    (knownA : K → A → ℝ)
    (knownB : K → B → ℝ)
    (ε : K → ℝ) (k : K) : Prop :=
  TwoFamilySimplicity A B (knownA k) (knownB k)
    (selected k) (ε k)

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
