/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-!
# How the relativistic Fermi coupling repositions the noble-metal ordering across branches

The first conductivity model (`SciamaAdSCPTRelativisticFermiConductivity`) with an *idealized common* base and a
`σ ∝ 1/E` suppression gives only a monotone-in-`Z` ordering `Cu > Ag > Au` — it never reaches the **real**
`Ag > Cu > Au` (silver beats copper, gold last).  The real ordering needs the physically correct picture: gold
is *intrinsically* an excellent conductor — non-relativistically it is silver-like — and **relativity demotes
it** (the relativistic-gold anomaly: the `6s` valence electron moves at `v/c ≈ Zα`, its orbital contracts,
`s`–`d` hybridization and the effective mass rise, and conductivity drops the most for the heaviest atom).

Modelling that with a base conductivity ordered gold-first and a relativistic mass-suppression that scales with
`Z²` and an **effective coupling `κ`** (the vacuum/band relativistic strength — a counterfactual/landscape
parameter that encodes `α`, *not* an Everett-branch label; genuine branches all share it):

`σ(X, κ) = base(X) / (1 + κ · Z_X²)`,   `base = (Au:10, Ag:8, Cu:6)` (illustrative, gold-first intrinsic).

Changing `κ` moves the branch through three distinct orderings:

* `weakRelativistic_gold_first` — **`κ = 0`** (no relativistic suppression): `Au > Ag > Cu` — gold's intrinsic
  advantage wins.  This is the earlier "flipped" branch, now recovered as the *non-relativistic* limit.
* `physicalRelativistic_reference` — **`κ = 1/5000`** (physical-strength coupling): `Ag > Cu > Au` — the **real
  room-temperature ordering**: gold, suppressed most (largest `Z²`), drops below both silver and copper, and
  silver's higher base keeps it above copper.
* `strongRelativistic_copper_first` — **`κ = 1`** (strong coupling): `Cu > Ag > Au` — with heavy suppression the
  lightest metal wins; even silver falls below copper.
* `relSuppression_gold_most` — the mechanism: for any `κ > 0` the suppression factor is largest for gold and
  smallest for copper (`1 + κ·29² < 1 + κ·47² < 1 + κ·79²`), so increasing `κ` demotes gold fastest.
* `relConductivity_gold_antitone` — gold's conductivity strictly decreases as `κ` grows.

So this **counterfactual coupling family** is parameterized by `κ` (a landscape parameter, *not* an
Everett-branch label — `κ` is shared by all genuine branches): **weak-`κ` gives `Au > Ag > Cu`, physical-`κ`
the real `Ag > Cu > Au`, and strong-`κ` `Cu > Ag > Au`**.  The Au-first and Ag-first sectors of the earlier
binary model are two points of this continuous family, with the real ordering at intermediate coupling.  Every
genuine Everett branch sits at the *same* physical `κ`, so the ordering is branch-invariant
(`SciamaAdSCPTBranchConfigurationAnalogy.ordering_branch_invariant_at_shared_coupling`).

Honest scope: the base values are illustrative (chosen to exhibit the three orderings and to place the real one
at physical coupling), not fitted to measured conductivities; the real gold demotion is a band-structure effect
(`6s`–`5d`), captured here by the effective `κ·Z²` mass suppression that reproduces its `Z`-scaling.  The
transition is exhibited by the three `κ`-endpoints; the intervening crossings follow by continuity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-- The non-relativistic base conductivity: gold-first (`Au:10, Ag:8, Cu:6`), reflecting gold's intrinsic
(pre-relativistic, silver-like) conducting quality. -/
def baseConductivity : NobleMetal → ℝ
  | .gold => 10
  | .silver => 8
  | .copper => 6

/-- The relativistic mass-suppression factor `1 + κ Z²` at effective coupling `κ` — larger for heavier atoms. -/
def relSuppression (kappa : ℝ) (X : NobleMetal) : ℝ := 1 + kappa * atomicNumber X ^ 2

/-- The conductivity at relativistic coupling `κ`: `base(X)/(1 + κ Z²)` — the heavier the atom, the stronger the
relativistic suppression. -/
def relConductivity (kappa : ℝ) (X : NobleMetal) : ℝ := baseConductivity X / relSuppression kappa X

/-- The real room-temperature ordering `Ag > Cu > Au`. -/
def ReferenceOrder (σ : NobleMetal → ℝ) : Prop := σ .silver > σ .copper ∧ σ .copper > σ .gold

/-- **[Weak coupling `κ = 0`: `Au > Ag > Cu`].**  With no relativistic suppression the intrinsic base ordering
wins — gold first. -/
theorem weakRelativistic_gold_first : GoldFirstOrder (relConductivity 0) := by
  unfold GoldFirstOrder
  refine ⟨?_, ?_⟩ <;>
    norm_num [relConductivity, relSuppression, baseConductivity, atomicNumber]

/-- **[Physical coupling `κ = 1/5000`: `Ag > Cu > Au`, the real ordering].**  Gold, suppressed most by its
`Z² = 79²`, drops below silver and copper; silver's higher base keeps it above copper. -/
theorem physicalRelativistic_reference : ReferenceOrder (relConductivity (1 / 5000)) := by
  unfold ReferenceOrder
  refine ⟨?_, ?_⟩ <;>
    norm_num [relConductivity, relSuppression, baseConductivity, atomicNumber]

/-- **[Strong coupling `κ = 1`: `Cu > Ag > Au`].**  With heavy relativistic suppression the lightest metal wins;
even silver falls below copper. -/
theorem strongRelativistic_copper_first :
    relConductivity 1 .copper > relConductivity 1 .silver
      ∧ relConductivity 1 .silver > relConductivity 1 .gold := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [relConductivity, relSuppression, baseConductivity, atomicNumber]

/-- **[Mechanism: gold is suppressed most] `1 + κ·29² < 1 + κ·47² < 1 + κ·79²` for `κ > 0`.**  The relativistic
mass-suppression grows with `Z²`, so increasing the coupling demotes the heaviest metal (gold) fastest. -/
theorem relSuppression_gold_most (kappa : ℝ) (hk : 0 < kappa) :
    relSuppression kappa .copper < relSuppression kappa .silver
      ∧ relSuppression kappa .silver < relSuppression kappa .gold := by
  simp only [relSuppression, atomicNumber]
  refine ⟨?_, ?_⟩ <;> nlinarith [hk]

/-- **[Gold's conductivity decreases with the coupling].**  As the relativistic coupling `κ` grows, gold's
conductivity strictly falls — the drive that moves gold from first to last. -/
theorem relConductivity_gold_antitone {k₁ k₂ : ℝ} (h0 : 0 ≤ k₁) (hlt : k₁ < k₂) :
    relConductivity k₂ .gold < relConductivity k₁ .gold := by
  have hd1 : (0 : ℝ) < relSuppression k₁ .gold := by
    simp only [relSuppression, atomicNumber]; nlinarith [h0]
  have hden : relSuppression k₁ .gold < relSuppression k₂ .gold := by
    simp only [relSuppression, atomicNumber]; nlinarith [hlt]
  simp only [relConductivity, baseConductivity]
  rw [div_eq_mul_one_div (10 : ℝ) (relSuppression k₂ .gold),
    div_eq_mul_one_div (10 : ℝ) (relSuppression k₁ .gold)]
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hd1 hden) (by norm_num)

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches

end
