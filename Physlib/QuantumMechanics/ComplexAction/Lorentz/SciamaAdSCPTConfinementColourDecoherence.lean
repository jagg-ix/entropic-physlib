/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-!
# Confinement is decoherence in colour space: the singlet is the surviving branch

The confinement Wilson-loop weight `⟨W⟩ = e^{−σA}` is the *same* `kuikenWeight` as the transport decoherence
visibility `exp(−Γt)` (`SciamaAdSCPTConfinementEntropicMiwBranch.confinement_areaLaw_is_nagaoNielsen_modulus`).
So it plays the same *dynamical* role: a large Wilson loop (`σA → ∞`) gives a weight `→ 0` that **suppresses the
off-diagonal** of a colour decoherence functional, exactly as the transport visibility suppresses the
double-slit fringe.  This upgrades the "confinement is like a hidden branch" picture to a precise mechanism:

* **Primary analogy — confinement is einselection.**  Confinement *is* environmental decoherence in colour
  space: the coloured (non-singlet) states are the genuinely **decohered off-diagonal** (`confinement_decoheres_
  coloured` *proves* the Sorkin bound with `v = e^{−σA}`, it is not asserted), and the colour singlet is the
  **einselected pointer basis** (Zurek) — the robust surviving diagonal.  This is a dynamical identity (both
  suppress off-diagonals via one `kuikenWeight`), not a loose analogy.
* **Everett/MIW reading — the singlet is quasiclassical (branch-invariant).**  The colour singlet is the
  observable in *every* Everett branch (the quasiclassical domain), exactly as the conductivity ordering
  `Ag > Cu > Au` is branch-invariant (`SciamaAdSCPTBranchConfigurationAnalogy.ordering_branch_invariant_at_
  shared_coupling`); the coloured "which-colour" data is the un-observed off-diagonal, the analogue of
  which-world / which-path information.
* **Weaker landscape analogy (secondary).**  A branch where the flipped ordering `Au > Ag > Cu` is fundamental
  is a *counterfactual* (a different `α`, not a measurement-outcome branch, `branchConductivity σ₀ 1`); it is an
  illustration of "a branch-level quantity one never directly sees", kept only as a secondary analogue —
  the *primary* content is the einselection above.

* `confinement_weight_is_visibility` — `e^{−σA} ∈ (0, 1]` is a valid interference visibility.
* `confinement_decoheres_coloured` — the coloured off-diagonal, damped by the confinement weight, obeys the
  Sorkin strong-positivity bound `|Δ| ≤ μ(α) + μ(β)`; `σA → ∞` washes the coloured fringe out to the classical
  (singlet-diagonal) sum.
* `confinement_is_colour_decoherence_synthesis` — the einselection (decoherence + quark not a singlet) together
  with the secondary landscape-branch illustration, one statement.

Honest scope: the confinement weight is reused as a decoherence visibility in the repo's Sorkin decoherence
functional (an exact reuse); "confinement is einselection of the colour-singlet pointer basis" is the strong,
dynamical reading; the branch-invariance of the singlet is the genuine Everett/MIW parallel; the
`Au > Ag > Cu` counterfactual is only the weaker landscape illustration.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConfinementColourDecoherence

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity

/-- **[The confinement weight is a valid interference visibility] `e^{−σA} ∈ (0, 1]`.**  Positive (`Real.exp`)
and `≤ 1` (`confinement_weight_le_one`): the confinement Wilson weight can only suppress, never amplify — the
same range as the transport decoherence visibility. -/
theorem confinement_weight_is_visibility {σ A : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) :
    0 < wilsonAreaLaw σ A ∧ wilsonAreaLaw σ A ≤ 1 := by
  refine ⟨?_, confinement_weight_le_one σ A hσ hA⟩
  unfold wilsonAreaLaw
  exact Real.exp_pos _

variable {ι : Type*} [DistribLattice ι] [OrderBot ι] {D : ι → ι → ℂ}

/-- **[Confinement decoheres the coloured states]** — the coloured off-diagonal of a decoherence functional,
weighted by the confinement Wilson-loop factor `e^{−σA}`, obeys the Sorkin strong-positivity bound
`|μ_v(α⊔β) − (μα+μβ)| ≤ μα + μβ`.  As `σA → ∞` the weight `→ 0`, so the coloured "fringe" is washed out to the
classical (singlet-diagonal) sum: confinement is decoherence in colour space. -/
theorem confinement_decoheres_coloured (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    {σ A : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) :
    |decoheredMeasure D (wilsonAreaLaw σ A) α β - (quantalMeasure D α + quantalMeasure D β)|
      ≤ quantalMeasure D α + quantalMeasure D β :=
  decoheredMeasure_fringe_bound h hαβ (confinement_weight_is_visibility hσ hA).1.le
    (confinement_weight_is_visibility hσ hA).2

/-- **[Confinement is einselection of the colour-singlet pointer basis]** — *primary*: the confinement weight
decoheres the coloured off-diagonal (above) and the quark is **not** a colour singlet (`cubeRoot² ≠ 1`, the
decohered state), so the einselected pointer state is the singlet.  *Secondary (landscape illustration)*: the
counterfactual `Au > Ag > Cu` branch (`branchConductivity σ₀ 1`) is a weaker analogue of "a branch-level
quantity one never directly sees" — the genuine Everett/MIW parallel is the branch-invariance of the singlet
(quasiclassical domain), not this counterfactual. -/
theorem confinement_is_colour_decoherence_synthesis (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    {σ A σ₀ : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hσ0 : 0 < σ₀) :
    |decoheredMeasure D (wilsonAreaLaw σ A) α β - (quantalMeasure D α + quantalMeasure D β)|
        ≤ quantalMeasure D α + quantalMeasure D β
      ∧ cubeRoot ^ (2 : ℤ) ≠ 1
      ∧ GoldFirstOrder (branchConductivity σ₀ 1) :=
  ⟨confinement_decoheres_coloured h hαβ hσ hA, quark_not_colour_singlet,
    branchConductivity_gold_first_flipped_sector σ₀ hσ0⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConfinementColourDecoherence

end
