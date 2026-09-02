/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Asymptotics
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Isoenergetic crossings and the high-energy spectral tail

A central use of Veliev's simple set is topological. Along a continuous simple
band branch, if the band value is below `ρ²` at one endpoint and above `ρ²` at
the other, the isoenergetic surface is nonempty. Repeating this at every
sufficiently high energy yields a spectral half-line and therefore excludes
high-energy gaps.

This file formalizes that implication. The difficult measure and derivative
estimates that construct the crossing branch remain explicit hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open Set

/-- A continuous real band crosses an energy between two ordered parameter
values. -/
def HasBandCrossing
    (band : ℝ → ℝ) (a b energy : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn band (Icc a b) ∧
    band a ≤ energy ∧ energy ≤ band b

/-- Intermediate-value theorem for an isoenergetic crossing. -/
theorem exists_isoenergetic_point
    (band : ℝ → ℝ) (a b energy : ℝ)
    (hcross : HasBandCrossing band a b energy) :
    ∃ x ∈ Icc a b, band x = energy := by
  rcases hcross with ⟨hab, hcont, ha, hb⟩
  exact isPreconnected_Icc.intermediate_value₂
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    hcont continuousOn_const ha hb

/-- A selected simple branch is represented by its band function and the
fact that every value on the interval belongs to the operator spectrum. -/
structure SimpleBandBranch (spectrum : Set ℝ) where
  band : ℝ → ℝ
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  continuous : ContinuousOn band (Icc left right)
  spectral : ∀ x ∈ Icc left right, band x ∈ spectrum

namespace SimpleBandBranch

/-- A simple band branch crossing `energy` supplies a spectral point at that
energy. -/
theorem energy_mem_spectrum
    {spectrum : Set ℝ} (B : SimpleBandBranch spectrum)
    (energy : ℝ)
    (hleft : B.band B.left ≤ energy)
    (hright : energy ≤ B.band B.right) :
    energy ∈ spectrum := by
  obtain ⟨x, hx, hxe⟩ := exists_isoenergetic_point
    B.band B.left B.right energy
    ⟨B.ordered, B.continuous, hleft, hright⟩
  rw [← hxe]
  exact B.spectral x hx

end SimpleBandBranch

/-- The spectrum contains every energy above a threshold. -/
def HasSpectralTail (spectrum : Set ℝ) (threshold : ℝ) : Prop :=
  Ici threshold ⊆ spectrum

/-- A simple crossing branch for every high energy produces a spectral
tail. -/
theorem hasSpectralTail_of_crossing_branches
    (spectrum : Set ℝ) (threshold : ℝ)
    (branch : ℝ → SimpleBandBranch spectrum)
    (hcross : ∀ energy, threshold ≤ energy →
      (branch energy).band (branch energy).left ≤ energy ∧
        energy ≤ (branch energy).band (branch energy).right) :
    HasSpectralTail spectrum threshold := by
  intro energy henergy
  exact (branch energy).energy_mem_spectrum energy
    (hcross energy henergy).1 (hcross energy henergy).2

/-- No open interval entirely above a spectral-tail threshold can be disjoint
from the spectrum. -/
theorem no_high_energy_open_gap
    (spectrum : Set ℝ) (threshold a b : ℝ)
    (htail : HasSpectralTail spectrum threshold)
    (ha : threshold ≤ a) (hab : a < b) :
    ¬ Disjoint (Ioo a b) spectrum := by
  intro hdisjoint
  have hmid : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
    constructor <;> linarith
  have hspec : (a + b) / 2 ∈ spectrum :=
    htail (mem_Ici.mpr (by linarith [hmid.1]))
  have hopen : (a + b) / 2 ∈ Ioo a b := hmid
  exact Set.disjoint_left.1 hdisjoint hopen hspec

/-- Abstract Bethe--Sommerfeld conclusion: a spectral tail excludes all gaps
above one finite threshold. -/
def HasFiniteHighEnergyGapRegion
    (spectrum : Set ℝ) : Prop :=
  ∃ threshold, HasSpectralTail spectrum threshold

/-- Crossing branches above a threshold imply the finite-high-energy-gap
property. -/
theorem finiteHighEnergyGapRegion_of_crossings
    (spectrum : Set ℝ) (threshold : ℝ)
    (branch : ℝ → SimpleBandBranch spectrum)
    (hcross : ∀ energy, threshold ≤ energy →
      (branch energy).band (branch energy).left ≤ energy ∧
        energy ≤ (branch energy).band (branch energy).right) :
    HasFiniteHighEnergyGapRegion spectrum :=
  ⟨threshold,
    hasSpectralTail_of_crossing_branches spectrum threshold branch hcross⟩

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
