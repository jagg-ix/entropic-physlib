/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

/-!
# The configuration is branch-invariant; the ordering is invariant across genuine branches, relative only across the counterfactual κ-family

`SciamaAdSCPTConductorDerivation` derives the best-conductor **configuration** (`d¹⁰s¹`, one carrier) and the
**elements** (group 11, `Z = 29, 47, 79`) from Pauli + band-filling + Aufbau — quantities that do **not** depend
on the relativistic coupling `κ`.  The **reference ordering** varies only across the *counterfactual* `κ`-family
(different `α`), **not** across genuine Everett branches, which share `κ`
(`ordering_branch_invariant_at_shared_coupling`).  This module separates the two and formalizes the key
recognition: our `Ag > Cu > Au` is **not privileged**; the counterfactual `Au > Ag > Cu` is the *analogous* reference
ordering of the *same* configuration.

* `configuration_branch_invariant` — the derived `d¹⁰s¹` group-11 configuration (conducting, one carrier,
  `Z = 29, 47, 79`) is the *same* valid periodic-table configuration underlying both the physical branch and the
  analogous one; it carries no `κ`, so it is valid in every branch of this family.
* `branchAnalogy` — the element relabeling `Ag ↦ Au, Cu ↦ Ag, Au ↦ Cu` (a `3`-cycle) that matches each metal to
  its rank-counterpart between branches; `branchAnalogy_bijective`.
* **`branch_ordering_analogy`** — our reference ordering `Ag > Cu > Au` (at `κ = 1/5000`) maps under
  `branchAnalogy` to the weak branch's `Au > Ag > Cu` (at `κ = 0`): the two branches' physical orderings are
  **order-isomorphic** via the relabeling — analogous, neither fundamental.
* `branches_analogous_not_privileged` — bundles it: both `ReferenceOrder` (ours) and `GoldFirstOrder` (the
  analog) hold on the shared configuration, related by the bijection `branchAnalogy`.

Improving the "empirical configuration": rather than treating `Au > Ag > Cu` and `Ag > Cu > Au` as separate
inputs, this models a *single* valid group-11 configuration whose reference ordering is a branch-relative
observable.  Our branch and the analogous branch are two evaluations of the same structure at different
relativistic couplings; the ordering that looks fundamental to observers in one branch (`Ag > Cu > Au` for us)
is exactly analogous to the one that looks fundamental in another (`Au > Ag > Cu`).

Honest scope: the analogy is the order-isomorphism of the two reference orderings and the branch-invariance of
the derived configuration.  Whether a branch with the weak-coupling ordering is physically realized — and the
solid-state magnitudes — remain outside particle physics, as before; and the `d¹⁰s¹` Aufbau anomaly is still the
empirical configuration input, now recognized as the branch-invariant part.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchConfigurationAnalogy

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

/-- **[The configuration is branch-invariant] the derived `d¹⁰s¹` group-11 configuration underlies every branch.**
The conducting half-filled `s`-band, the single carrier, and the atomic numbers `Z = 29, 47, 79` carry no
relativistic coupling `κ`, so they are the *same* valid periodic-table configuration in our branch and in the
analogous one. -/
theorem configuration_branch_invariant :
    conducts (subshellCapacity 0) 1 ∧ conductionElectrons 1 = 1
      ∧ group11AtomicNumber 18 10 = 29 ∧ group11AtomicNumber 36 10 = 47
      ∧ group11AtomicNumber (54 + 14) 10 = 79 :=
  ⟨sBand_halfFilled_conducts, d10s1_single_carrier, copper_Z, silver_Z, gold_Z⟩

/-- The **branch analogy** relabeling: matches each metal to its rank-counterpart between branches, sending our
reference ordering `Ag > Cu > Au` to the weak branch's `Au > Ag > Cu`.  A `3`-cycle `Ag → Au → Cu → Ag`. -/
def branchAnalogy : NobleMetal → NobleMetal
  | .silver => .gold
  | .copper => .silver
  | .gold => .copper

/-- **[The analogy is a relabeling] `branchAnalogy` is a bijection of the group-11 elements.** -/
theorem branchAnalogy_bijective : Function.Bijective branchAnalogy := by decide

/-- **[The two branches' orderings are analogous] `Ag > Cu > Au` maps to `Au > Ag > Cu` under the relabeling.**
Our physical-branch reference ordering (`κ = 1/5000`) and the weak-branch ordering (`κ = 0`) are order-isomorphic
via `branchAnalogy`: the best/mid/worst of one branch relabels to the best/mid/worst of the other. -/
theorem branch_ordering_analogy :
    (relConductivity (1 / 5000) .silver > relConductivity (1 / 5000) .copper
        ∧ relConductivity (1 / 5000) .copper > relConductivity (1 / 5000) .gold)
      ∧ (relConductivity 0 (branchAnalogy .silver) > relConductivity 0 (branchAnalogy .copper)
        ∧ relConductivity 0 (branchAnalogy .copper) > relConductivity 0 (branchAnalogy .gold)) := by
  refine ⟨physicalRelativistic_reference, ?_⟩
  simp only [branchAnalogy]
  exact weakRelativistic_gold_first

/-- **[Neither ordering is privileged].**  Both the physical-branch `Ag > Cu > Au` and the weak-branch
`Au > Ag > Cu` are valid reference orderings of the *same* derived group-11 configuration, related by the
bijective relabeling `branchAnalogy`.  The ordering fundamental to observers in one branch is exactly analogous
to the one fundamental in another. -/
theorem branches_analogous_not_privileged :
    ReferenceOrder (relConductivity (1 / 5000)) ∧ GoldFirstOrder (relConductivity 0)
      ∧ Function.Bijective branchAnalogy
      ∧ (relConductivity 0 (branchAnalogy .silver) > relConductivity 0 (branchAnalogy .copper)
          ∧ relConductivity 0 (branchAnalogy .copper) > relConductivity 0 (branchAnalogy .gold)) :=
  ⟨physicalRelativistic_reference, weakRelativistic_gold_first, branchAnalogy_bijective,
    branch_ordering_analogy.2⟩

/-! ## Branch-invariance of the ordering at the shared physical coupling

The relabeling above is an *analogy*, not a claim that the two orderings are realized in two Everett branches
of our wavefunction.  The coupling `κ` encodes the fine-structure constant `α` and the atomic numbers, all
constants of the universal Hamiltonian — the **same in every Everett branch and every MIW world**.  So a
genuine branch cannot change the ordering; the different-ordering `κ`-family is a counterfactual/landscape
family (different `α`), *analogous to* branches, not a set of them. -/

open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-- The physical relativistic coupling `κ = 1/5000` — a constant of the universal Hamiltonian (it encodes `α`
and the atomic numbers), hence the **same in every Everett branch / MIW world**. -/
noncomputable def sharedCoupling : ℝ := 1 / 5000

/-- The conductivity ordering assigned to an Everett branch at the shared physical coupling: it does **not**
depend on the branch label `s` — `α` is not a measurement outcome. -/
noncomputable def physicalBranchConductivity (_s : SpinOutcome) : NobleMetal → ℝ :=
  relConductivity sharedCoupling

/-- **[The ordering is branch-invariant] every Everett branch has the same real ordering `Ag > Cu > Au`, and no
branch is gold-first.**  Because `sharedCoupling` is a constant of the universal Hamiltonian, every `SpinOutcome`
branch is evaluated at the *same* `κ`; the sequence is a shared quasiclassical fact, not a branch-dependent
observable — the gold-first flip does not occur across genuine branches. -/
theorem ordering_branch_invariant_at_shared_coupling :
    (∀ s : SpinOutcome, ReferenceOrder (physicalBranchConductivity s))
      ∧ ¬ GoldFirstOrder (relConductivity sharedCoupling) := by
  refine ⟨fun _s => physicalRelativistic_reference, ?_⟩
  intro hgf
  have href : ReferenceOrder (relConductivity sharedCoupling) := physicalRelativistic_reference
  linarith [href.1, href.2, hgf.1]

/-- **[The gold-first flip needs a counterfactual, branch-dependent coupling].**  Only if the two branches are
assigned *different* couplings via `sectorParameter` (a landscape move — a different `α`, not a measurement
outcome) do the orderings differ: the `−` sector is gold-first, the `+` sector is not.  This is the precise
sense in which the `κ`-family is *analogous to* branches, not genuine Everett branches (contrast
`ordering_branch_invariant_at_shared_coupling`). -/
theorem counterfactual_sector_coupling_flips (σ₀ : ℝ) (h0 : 0 < σ₀) :
    GoldFirstOrder (branchConductivity σ₀ (sectorParameter .minus))
      ∧ ¬ GoldFirstOrder (branchConductivity σ₀ (sectorParameter .plus)) := by
  refine ⟨flipped_branch_gold_first σ₀ h0, ?_⟩
  intro hgf
  have hplus : sectorParameter .plus = 0 := rfl
  rw [hplus] at hgf
  have hworst := branchConductivity_gold_worst_our_sector σ₀ h0
  linarith [hworst.2, hgf.1]

/-! ## The coupling scale: the bare relativistic `α²` vs the fitted `κ`

`counterfactual_sector_coupling_flips` shows the ordering is coupling-driven and `κ` is an `α`-like parameter
(`relSuppression κ Z = 1 + κ Z²`, cf. the bare relativistic `relEnhancement Z = 1 + (Zα)²`).  The natural *bare*
value is therefore `κ = α² = (1/137)² = 1/18769`.  Re-evaluating `physicalRelativistic_reference`'s `κ = 1/5000`
against it is a concrete, verifiable computation — and it pins down exact crossing couplings that
`NobleMetalBranchTransport.exists_gold_silver_crossing` only asserts to exist. -/

/-- **[The bare relativistic coupling is below the gold-demotion onset] `α² < 1/7259`.**  `α² = 1/18769`. -/
theorem fineStructureSq_below_gold_demotion : fineStructure ^ 2 < 1 / 7259 := by
  unfold fineStructure; norm_num

/-- **[Bare `α²` is too weak — the model is gold-FIRST there].**  At `κ = α²` the pure `(Zα)²` relativistic-mass
suppression does not demote gold below silver/copper, so `relConductivity (α²)` is `Au > Ag > Cu`.  The real
`Ag > Cu > Au` demotion therefore needs an effective coupling *stronger* than bare `α²` — the band-structure
amplification (`s–d` scattering, `d`-band proximity), which the illustrative `κ = 1/5000 ≈ 3.75 α²` absorbs. -/
theorem bare_relativistic_coupling_gold_first :
    GoldFirstOrder (relConductivity (fineStructure ^ 2)) := by
  unfold GoldFirstOrder relConductivity relSuppression baseConductivity atomicNumber fineStructure
  refine ⟨?_, ?_⟩ <;> norm_num

/-- **[Exact gold = silver crossing] `κ = 1/13919`.**  Gold and silver conduct equally here; below it gold
leads, above it silver overtakes gold — the exact coupling behind `exists_gold_silver_crossing`. -/
theorem goldSilver_crossing_coupling :
    relConductivity (1 / 13919) .gold = relConductivity (1 / 13919) .silver := by
  unfold relConductivity relSuppression baseConductivity atomicNumber; norm_num

/-- **[Exact gold = copper crossing] `κ = 1/7259`** — the onset of the gold-worst regime: above it gold drops
below copper too, giving the real `Ag > Cu > Au`. -/
theorem goldCopper_crossing_coupling :
    relConductivity (1 / 7259) .gold = relConductivity (1 / 7259) .copper := by
  unfold relConductivity relSuppression baseConductivity atomicNumber; norm_num

/-- **[The fitted `κ = 1/5000` sits inside the reference-ordering window] `1/7259 < 1/5000 < 1/3263`.**  The
window is bounded by the gold=copper onset (`1/7259`) and the silver=copper crossing (`1/3263`); the bare `α²`
lies below it (`fineStructureSq_below_gold_demotion`), so `κ = 1/5000` is a fitted, band-structure-enhanced
effective coupling, not the bare relativistic one. -/
theorem fitted_coupling_in_reference_window :
    (1 : ℝ) / 7259 < 1 / 5000 ∧ (1 : ℝ) / 5000 < 1 / 3263 := by
  constructor <;> norm_num

/-! ## What bare `α²` DOES predict: the relativistic valence contraction

Bare `α²` fails for the band-structure-limited DC conductivity, but it correctly predicts the **single-atom**
relativistic effect: the valence-orbital contraction (relativistic Bohr estimate `a_rel/a = √(1 − (Zα)²)`).
Sqrt-free via the squared ratio `1 − (Zα)²` (monotone), this reproduces the known relativistic-gold anomaly —
gold's `6s` contracts far more than silver's — the root of gold's colour, nobility, and the effective-mass rise.
The boundary is sharp: bare `α²` gives the atomic contraction ordering (gold extremal) but *not* the transport
ordering (`bare_relativistic_coupling_gold_first` vs the real, band-structure `physicalRelativistic_reference`). -/

/-- The squared relativistic contraction ratio `(a_rel/a_nonrel)² = 1 − (Zα)²` of the valence orbital
(relativistic Bohr estimate). -/
noncomputable def contractionRatioSq (Z : ℝ) : ℝ := 1 - (Z * fineStructure) ^ 2

/-- **[Gold's `6s` contracts most] `(a_rel/a)²_Au < _Ag < _Cu`.**  The heaviest atom's valence orbital contracts
most under relativity (smallest ratio) — the single-atom effect bare `α²` captures. -/
theorem contraction_gold_most :
    contractionRatioSq 79 < contractionRatioSq 47 ∧ contractionRatioSq 47 < contractionRatioSq 29 := by
  unfold contractionRatioSq fineStructure; constructor <;> norm_num

/-- **[Gold's contraction is substantial, copper's slight].**  `(a_rel/a)²_Au < 0.7` (gold's `6s` contracts by
more than ~16%), while `(a_rel/a)²_Cu > 0.95` (copper less than ~2.5%) — the ~3× gold/silver ratio of the
relativistic-gold anomaly, from the bare fine-structure coupling alone. -/
theorem gold_contraction_substantial :
    contractionRatioSq 79 < 7 / 10 ∧ contractionRatioSq 29 > 95 / 100 := by
  unfold contractionRatioSq fineStructure; constructor <;> norm_num

/-- **[The atomic/transport boundary].**  From the *same* bare fine-structure coupling `α²`: the single-atom
contraction is gold-extremal (`contraction_gold_most`) and the model conductivity is gold-*first*
(`bare_relativistic_coupling_gold_first`), yet the measured DC conductivity is gold-*worst* — the flip is a
collective band-structure effect (`s–d` scattering, `d`-band proximity), not a single-atom relativistic one. -/
theorem atomic_extremal_transport_needs_bandstructure :
    (contractionRatioSq 79 < contractionRatioSq 47 ∧ contractionRatioSq 47 < contractionRatioSq 29)
      ∧ GoldFirstOrder (relConductivity (fineStructure ^ 2)) :=
  ⟨contraction_gold_most, bare_relativistic_coupling_gold_first⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchConfigurationAnalogy

end
