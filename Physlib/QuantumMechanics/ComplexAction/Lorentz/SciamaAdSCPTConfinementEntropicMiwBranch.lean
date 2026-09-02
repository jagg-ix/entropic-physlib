/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.Relativity.SemiClassical.RiemannianPenroseInequality
public import Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-!
# QCD confinement as the entropic sector: Verlinde string, Witten trefoil, Penrose, and an MIW branch

Confinement is the long-distance dual of the fermion's inverse-square arc.  The Cornell potential
`V(r) = −C_F α/r + σr` has a short-distance **Coulomb** part (`1/r²` force — the deconfined / asymptotic-freedom
regime, the Verlinde *point-screen* entropic force `SciamaAdSCPTVerlindeNagaoNielsenEntropicSynthesis`, the MIW
inverse-square interworld term) and a long-distance **linear** part `σr` — the confining flux-tube **string**
(`WilsonLoopConfinementCriterion.staticQuarkPotential_confining`).  The two balance at the crossover radius
(`Su3ConfinementPotential.cornell_terms_balance_at_crossover`); beyond it the string wins and the quarks cannot
separate.  This module ties the *confining* (string) side to the same entropic / imaginary-action sector as the
decoherence, reusing the repo's confinement, Nagao–Nielsen, Penrose, trefoil, colour, and branch machinery.

* **§1 — confinement is the Nagao–Nielsen imaginary action** (`confinement_areaLaw_is_nagaoNielsen_modulus`):
  the Wilson-loop area law `⟨W⟩ = e^{−σA}` (`ConfinementAreaLawEntropicWeight.wilsonAreaLaw`) *is* the modulus of
  the Nagao–Nielsen complex-action weight `‖e^{(i/ℏ)(S_R+iS_I)}‖` with imaginary action `S_I = σ·A` (string
  tension × minimal area).  Confinement lives in the **same imaginary-action sector as the decoherence**
  (`decoherence_visibility_is_nagaoNielsen_modulus`): both are `kuikenWeight`.

* **§2 — Penrose bounds the confinement action** (`confinement_action_penrose_bounded`): the Wilson surface area
  obeys the Riemannian–Penrose inequality `A ≤ 16πm²` (`RiemannianPenroseInequality.area_bound_of_penrose_inequality`),
  so the confinement imaginary action is bounded, `σA ≤ σ·16πm²` — the minimal-area / string-worldsheet bound.

* **§3 — Witten trefoil** — the confined flux-tube Wilson loop is the chiral **trefoil**: its Jones invariant
  distinguishes matter from antimatter (`TrefoilFermionChernSimonsInvariant.trefoil_chiral_distinguishes`,
  `electronJones ≠ positronJones`).

* **§4 — confinement as an Everett/MIW branch** (`confinement_entropic_miw_branch_synthesis`): the confined
  colour charge is **not** a colour singlet (`StrongInteractionColorOctet.quark_not_colour_singlet`, triality
  `cubeRoot² ≠ 1`) — never observed free, exactly as a **branch-relative** observable is never directly seen; the
  observable is the colour singlet, as the observable ordering is `Ag > Cu > Au` while the counterfactual
  `Au > Ag > Cu` branch (`branchConductivity_gold_first_flipped_sector`, the weak-relativistic MIW branch) stays
  hidden.  The confining potential *binds* the worlds (`IsConfining`, the force never falls off) where the
  inverse-square one lets them decohere.

Honest scope: the new content is the two cross-links (confinement area law = Nagao–Nielsen modulus; Penrose
bounds the confinement action) and the synthesis bundle; everything else — the confining potential, the area
law, the colour triality, the trefoil chirality, the branch — is reused from the repo.  The
confinement-as-branch statement is an **analogy** (the confined quark and the counterfactual conductivity branch
are both branch-level, unobserved directly), not a claim that colour is a measurement outcome.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConfinementEntropicMiwBranch

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.Relativity.SemiClassical.RiemannianPenroseInequality
open Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-! ## §1. Confinement is the Nagao–Nielsen imaginary action `S_I = σ·A` -/

/-- **[The Wilson-loop area law is the Nagao–Nielsen complex-action modulus]**
`⟨W⟩ = e^{−σA} = ‖e^{(i/ℏ)(S_R + iS_I)}‖` with imaginary action `S_I = σ·A`.  The confinement area law is the
modulus of the Nagao–Nielsen complex-action weight — the string tension × minimal area *is* the imaginary
action.  So confinement sits in the same imaginary-action / entropic sector as the decoherence
(`decoherence_visibility_is_nagaoNielsen_modulus`): both are `kuikenWeight`. -/
theorem confinement_areaLaw_is_nagaoNielsen_modulus (S_R σ A : ℝ) :
    wilsonAreaLaw σ A = ‖nagaoNielsenComplexActionWeight S_R (σ * A) 1‖ := by
  rw [areaLaw_is_kuikenWeight, nagaoNielsen_eq_master S_R (σ * A) 1 one_ne_zero, master_modulus_is_kuiken]

/-! ## §2. The Penrose inequality bounds the confinement action -/

/-- **[The Penrose inequality bounds the confinement imaginary action] `σA ≤ σ·16πm²`.**  The Wilson-surface
area obeys the Riemannian–Penrose inequality `A ≤ 16πm²`, so the confinement action `S_I = σA` (string tension ×
area) is bounded by the minimal-area / string-worldsheet bound. -/
theorem confinement_action_penrose_bounded {m A : ℝ} (hA : 0 ≤ A) {σ : ℝ} (hσ : 0 ≤ σ)
    (hmass : blackHoleMassContribution A ≤ m) :
    σ * A ≤ σ * (16 * Real.pi * m ^ 2) :=
  mul_le_mul_of_nonneg_left (area_bound_of_penrose_inequality hA hmass) hσ

/-! ## §3–4. The synthesis — confinement as the entropic sector and an Everett/MIW branch -/

/-- **[Confinement, entropic sector, and MIW branch — the synthesis]**  For a positive string tension `σ` and a
Wilson surface obeying the Penrose bound: the confinement area law is the Nagao–Nielsen imaginary-action modulus
(§1); the Penrose inequality bounds the confinement action (§2); the linear potential is confining (binds the
worlds); the confined quark is not a colour singlet (`cubeRoot² ≠ 1`, never free); its flux-tube Wilson loop is
the chiral trefoil (`electronJones 2 ≠ positronJones 2`); and this is analogous to the counterfactual
`Au > Ag > Cu` Everett/MIW branch (`branchConductivity σ₀ 1`) — the confined colour, like that branch's ordering,
is a branch-level quantity never directly observed, only the colour singlet / physical ordering is. -/
theorem confinement_entropic_miw_branch_synthesis (S_R σ σ₀ : ℝ) (hσ : 0 < σ) (hσ0 : 0 < σ₀)
    {m A : ℝ} (hA : 0 ≤ A) (hmass : blackHoleMassContribution A ≤ m) :
    wilsonAreaLaw σ A = ‖nagaoNielsenComplexActionWeight S_R (σ * A) 1‖
      ∧ σ * A ≤ σ * (16 * Real.pi * m ^ 2)
      ∧ IsConfining (staticQuarkPotential σ)
      ∧ cubeRoot ^ (2 : ℤ) ≠ 1
      ∧ electronJones 2 ≠ positronJones 2
      ∧ GoldFirstOrder (branchConductivity σ₀ 1) :=
  ⟨confinement_areaLaw_is_nagaoNielsen_modulus S_R σ A,
    confinement_action_penrose_bounded hA hσ.le hmass,
    staticQuarkPotential_confining σ hσ,
    quark_not_colour_singlet,
    trefoil_chiral_distinguishes,
    branchConductivity_gold_first_flipped_sector σ₀ hσ0⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConfinementEntropicMiwBranch

end
