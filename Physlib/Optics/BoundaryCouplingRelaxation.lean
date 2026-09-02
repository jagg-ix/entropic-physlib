/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.MpembaIndexRateSelection

meta import Zil

/-!
# Boundary coupling: the relaxation structure survives being driven through a surface

Teza, Yaacoby & Raz, *Relaxation shortcuts through boundary coupling* (arXiv:2112.10187), observe
that "in most experiments the system is coupled to the bath through its boundaries, but all theories
so far assumed bulk coupling", and build the boundary-coupled framework.  Their rate matrix splits

  `W(Γ_ST, Γ_BC) = Γ_ST · W_ST + Γ_BC · W_BC`

into self-thermalization and boundary-coupling parts, with `C = Γ_BC/Γ_ST` the coupling strength.
`W_ST` "contains only transitions between states that have the same energy"; `W_BC` satisfies
detailed balance against the bath.  Their result is that the Mpemba effect persists, and
"surprisingly, it can survive even an arbitrarily weak coupling".

Why this matters for the ENZ arc
--------------------------------
A pumped epsilon-near-zero film is driven through its **surface**, not its bulk — the 40 nm ITO of
`ComptonAnchorCoherenceTime`'s discussion is illuminated from outside.  So boundary coupling, not
bulk coupling, is the applicable framework, and the question is whether the machinery that
`MpembaCrossingReadsEffectiveDamping` and `MpembaIndexRateSelection` rest on survives that change.

It does, and for a reason that is short to state: **detailed balance is preserved by the split**.
`W_ST` connects only equal-energy states, so it satisfies detailed balance trivially (§B), detailed
balance is closed under non-negative combination (§C), and therefore the composite generator
inherits it from the boundary part alone.  Since `MpembaIndexRateSelection.detailedBalance_symmetrizes`
turns detailed balance into the symmetry that supplies the real spectrum, the whole crossing and
index construction goes through unchanged for a boundary-driven system.

§D isolates why the coarse-grained weak-coupling rate works: its Fermi/Glauber factor
`(1 + e^{β(E_i−E_j)})⁻¹` makes the Boltzmann-weighted rate **symmetric in the two states**, so the
temperature dependence drops out of detailed balance entirely and only a combinatorial condition on
the transition counts remains.  That is what lets the effect survive `C → 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.BoundaryCouplingRelaxation

open Physlib.Optics.MpembaIndexRateSelection

/-! ### §A — The coupling split -/

/-- The boundary-coupled generator `W = Γ_ST W_ST + Γ_BC W_BC` (Teza et al. Eq. 3). -/
def coupledRate {n : Type*} (WST WBC : n → n → ℝ) (gST gBC : ℝ) (i j : n) : ℝ :=
  gST * WST i j + gBC * WBC i j

/-- The coupling strength `C = Γ_BC / Γ_ST`: small `C` is the weak-coupling regime, where boundary
flips are rare compared with internal thermalization. -/
def couplingStrength (gST gBC : ℝ) : ℝ := gBC / gST

/-! ### §B — Self-thermalization is detailed-balanced for free -/

/-- Teza et al.'s defining property of `W_ST`: it "contains only transitions between states that
have the same energy". -/
def EnergyPreserving {n : Type*} (W : n → n → ℝ) (E : n → ℝ) : Prop :=
  ∀ i j, W i j ≠ 0 → E i = E j

/-- **Energy-preserving transitions satisfy detailed balance automatically.**  Within an energy
shell the Boltzmann weights coincide, so the detailed-balance condition degenerates to the symmetry
of the rate.  This is why the self-thermalization part imposes no thermodynamic condition of its
own. -/
theorem detailedBalance_of_energyPreserving {n : Type*} {W : n → n → ℝ} {E : n → ℝ} (beta : ℝ)
    (hE : EnergyPreserving W E) (hsymm : ∀ i j, W i j = W j i) :
    DetailedBalance W E beta := by
  intro i j
  by_cases h : W i j = 0
  · have hji : W j i = 0 := by rw [← hsymm i j]; exact h
    rw [h, hji, zero_mul, zero_mul]
  · rw [hE i j h, hsymm i j]

/-! ### §C — Detailed balance survives the split -/

/-- **Detailed balance is closed under non-negative combination.**  If both parts of the generator
are detailed-balanced against the same bath, so is the coupled generator, for any coupling
constants.  Consequently a boundary-driven system inherits detailed balance from its boundary part
alone, and `MpembaIndexRateSelection.detailedBalance_symmetrizes` then supplies the real spectrum the
crossing and index construction need. -/
theorem detailedBalance_coupledRate {n : Type*} {WST WBC : n → n → ℝ} {E : n → ℝ} {beta : ℝ}
    (hST : DetailedBalance WST E beta) (hBC : DetailedBalance WBC E beta) (gST gBC : ℝ) :
    DetailedBalance (coupledRate WST WBC gST gBC) E beta := by
  intro i j
  unfold coupledRate
  have hs := hST i j
  have hb := hBC i j
  ring_nf
  ring_nf at hs hb
  linear_combination gST * hs + gBC * hb

/-- **The boundary-driven generator is symmetrizable.**  Combining §B and §C with the
symmetrization theorem: an energy-preserving symmetric self-thermalization plus a detailed-balanced
boundary coupling gives a generator whose Boltzmann conjugate is symmetric — hence the real spectrum
and orthogonal modes that the Mpemba crossing readout of `γ_eff` assumes. -/
theorem boundaryCoupled_symmetrizes {n : Type*} {WST WBC : n → n → ℝ} {E : n → ℝ} {beta : ℝ}
    (hE : EnergyPreserving WST E) (hsymm : ∀ i j, WST i j = WST j i)
    (hBC : DetailedBalance WBC E beta) (gST gBC : ℝ) (i j : n) :
    symmetrized (coupledRate WST WBC gST gBC) E beta i j
      = symmetrized (coupledRate WST WBC gST gBC) E beta j i :=
  detailedBalance_symmetrizes
    (detailedBalance_coupledRate (detailedBalance_of_energyPreserving beta hE hsymm) hBC gST gBC) i j

/-! ### §D — Why the weak-coupling rate works: the Fermi factor symmetrizes

Teza et al.'s coarse-grained weak-coupling rate is
`W_ij^weak = (G_ij/Ω_j) · (1 + e^{β_b(E_i − E_j)})⁻¹`.  The temperature-dependent factor is a
Fermi/Glauber form, and the point of it is that once weighted by the Boltzmann factor it becomes
**symmetric under exchange of the two states**: the whole temperature dependence cancels out of
detailed balance, leaving only a combinatorial condition on the transition counts.  That is what
makes the construction insensitive to the coupling strength, and so able to survive `C → 0`. -/

/-- The Fermi/Glauber acceptance factor `(1 + e^{β(E_i − E_j)})⁻¹`. -/
def glauberFactor (beta Ei Ej : ℝ) : ℝ := (1 + Real.exp (beta * (Ei - Ej)))⁻¹

/-- **The Boltzmann-weighted Glauber factor is symmetric.**  `e^{−β E_j} (1 + e^{β(E_i−E_j)})⁻¹`
equals `(e^{β E_i} + e^{β E_j})⁻¹`, which is manifestly unchanged by swapping `i` and `j`.  All the
temperature dependence of detailed balance is carried by this one symmetric expression. -/
theorem boltzmann_glauber_symmetric (beta Ei Ej : ℝ) :
    Real.exp (-(beta * Ej)) * glauberFactor beta Ei Ej
      = (Real.exp (beta * Ei) + Real.exp (beta * Ej))⁻¹ := by
  unfold glauberFactor
  have hj : Real.exp (beta * Ej) ≠ 0 := Real.exp_ne_zero _
  have hprod : Real.exp (beta * (Ei - Ej)) * Real.exp (beta * Ej) = Real.exp (beta * Ei) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.exp_neg, ← hprod]
  field_simp
  ring

/-- **The weak-coupling rate is detailed-balanced exactly when the counts balance.**  Because the
temperature factor is symmetric, detailed balance for `W_ij = c_ij · glauberFactor` reduces to
`c_ij = c_ji` — a purely combinatorial condition on the coarse-grained transition counts and shell
degeneracies, with no temperature in it.  This is the structural reason the effect persists down to
arbitrarily weak coupling. -/
theorem detailedBalance_of_glauber_form {n : Type*} (c : n → n → ℝ) (E : n → ℝ) (beta : ℝ)
    (hc : ∀ i j, c i j = c j i) :
    DetailedBalance (fun i j => c i j * glauberFactor beta (E i) (E j)) E beta := by
  intro i j
  have hij : c i j * glauberFactor beta (E i) (E j) * Real.exp (-(beta * E j))
      = c i j * (Real.exp (beta * E i) + Real.exp (beta * E j))⁻¹ := by
    rw [mul_comm (c i j * glauberFactor beta (E i) (E j)) (Real.exp (-(beta * E j)))]
    rw [← mul_assoc, mul_comm (Real.exp (-(beta * E j))) (c i j), mul_assoc,
      boltzmann_glauber_symmetric]
  have hji : c j i * glauberFactor beta (E j) (E i) * Real.exp (-(beta * E i))
      = c j i * (Real.exp (beta * E j) + Real.exp (beta * E i))⁻¹ := by
    rw [mul_comm (c j i * glauberFactor beta (E j) (E i)) (Real.exp (-(beta * E i)))]
    rw [← mul_assoc, mul_comm (Real.exp (-(beta * E i))) (c j i), mul_assoc,
      boltzmann_glauber_symmetric]
  rw [hij, hji, hc i j, add_comm (Real.exp (beta * E j)) (Real.exp (beta * E i))]

/- ZIL-BEGIN -/

zil attach Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_of_energyPreserving where
  supported_by @ "lean:Physlib.Optics.MpembaIndexRateSelection.detailedBalance_symmetrizes",
  formalizes @ "claim:a-self-thermalization-generator-whose-transitions-connect-only-states-of-equal-energy-satisfies-detailed-balance-automatically-because-the-boltzmann-weights-coincide-within-an-energy-shell",
  epistemic_status @ "consistency-identity",
  caveat @ "symmetry-of-the-within-shell-rates-is-a-hypothesis-here-teza-et-al-obtain-it-from-the-construction-of-the-self-thermalization-matrix"

zil attach Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_coupledRate where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:detailed-balance-is-closed-under-non-negative-combination-so-a-generator-split-into-self-thermalization-and-boundary-coupling-parts-inherits-it-from-the-boundary-part-alone",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Optics.BoundaryCouplingRelaxation.boundaryCoupled_symmetrizes where
  supported_by @ "lean:Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_coupledRate",
  supported_by @ "lean:Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_of_energyPreserving",
  supported_by @ "lean:Physlib.Optics.MpembaIndexRateSelection.detailedBalance_symmetrizes",
  formalizes @ "claim:a-boundary-driven-generator-with-energy-preserving-self-thermalization-is-symmetrizable-so-the-real-spectrum-and-orthogonal-modes-that-the-mpemba-crossing-readout-of-the-effective-damping-assumes-survive-driving-through-a-surface-rather-than-the-bulk",
  epistemic_status @ "conditional-model",
  requires @ "claim:detailed-balance-is-closed-under-non-negative-combination-so-a-generator-split-into-self-thermalization-and-boundary-coupling-parts-inherits-it-from-the-boundary-part-alone",
  caveat @ "this-establishes-symmetrizability-not-that-any-epsilon-near-zero-film-realizes-the-teza-boundary-coupled-model-whose-states-are-ising-microstates"

zil attach Physlib.Optics.BoundaryCouplingRelaxation.boltzmann_glauber_symmetric where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-boltzmann-weighted-fermi-glauber-acceptance-factor-equals-the-inverse-sum-of-the-two-boltzmann-weights-and-is-therefore-symmetric-under-exchange-of-the-states-so-all-temperature-dependence-cancels-out-of-detailed-balance",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_of_glauber_form where
  supported_by @ "lean:Physlib.Optics.BoundaryCouplingRelaxation.boltzmann_glauber_symmetric",
  formalizes @ "claim:for-a-rate-of-glauber-form-detailed-balance-reduces-to-symmetry-of-the-coarse-grained-transition-counts-a-purely-combinatorial-condition-with-no-temperature-in-it-which-is-the-structural-reason-the-mpemba-effect-persists-to-arbitrarily-weak-coupling",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-boltzmann-weighted-fermi-glauber-acceptance-factor-equals-the-inverse-sum-of-the-two-boltzmann-weights-and-is-therefore-symmetric-under-exchange-of-the-states-so-all-temperature-dependence-cancels-out-of-detailed-balance",
  caveat @ "the-count-symmetry-hypothesis-encodes-the-shell-degeneracy-bookkeeping-of-the-coarse-graining-and-is-assumed-rather-than-derived-from-the-microscopic-dynamics-here"

zil_file_contract physlib.boundaryCouplingRelaxation where
  promises "Teza Yaacoby and Raz note that most experiments couple a system to its bath through the boundaries while theories assumed bulk coupling, and build the boundary-coupled framework in which the generator splits into a self-thermalization part and a boundary-coupling part with a coupling-strength ratio. This matters for the epsilon-near-zero arc because a pumped film is driven through its surface rather than its bulk, so the question is whether the machinery the Mpemba crossing readout of the effective damping rests on survives that change. It does, because detailed balance is preserved by the split: the self-thermalization part connects only states of equal energy and so satisfies detailed balance automatically, detailed balance is closed under non-negative combination, and therefore the composite generator inherits it from the boundary part alone and is symmetrizable, which supplies the real spectrum and orthogonal modes the crossing and index construction assume. The weak-coupling coarse-grained rate works for a sharper reason, also proved here: its Fermi-Glauber acceptance factor, once weighted by the Boltzmann factor, equals the inverse sum of the two Boltzmann weights and is therefore symmetric under exchange of the states, so all temperature dependence cancels out of detailed balance and only a combinatorial condition on the coarse-grained transition counts remains. That temperature-free condition is the structural reason the effect persists to arbitrarily weak coupling."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Optics.MpembaIndexRateSelection.DetailedBalance",
    "lean:Physlib.Optics.MpembaIndexRateSelection.symmetrized",
    "lean:Physlib.Optics.MpembaIndexRateSelection.detailedBalance_symmetrizes",
    "lean:Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime"]
  forbids_substitutes ["claiming an epsilon-near-zero film realizes the Teza boundary-coupled model, whose states are Ising microstates, rather than sharing its detailed-balance structure",
    "treating the count-symmetry hypothesis as derived from the microscopic dynamics rather than assumed as the coarse-graining bookkeeping",
    "reading the weak-coupling persistence as established for the optical system rather than for the model in which it was proved"]
  witnessed_by [Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_of_energyPreserving,
    Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_coupledRate,
    Physlib.Optics.BoundaryCouplingRelaxation.boundaryCoupled_symmetrizes,
    Physlib.Optics.BoundaryCouplingRelaxation.boltzmann_glauber_symmetric,
    Physlib.Optics.BoundaryCouplingRelaxation.detailedBalance_of_glauber_form]

/- ZIL-END -/

end Physlib.Optics.BoundaryCouplingRelaxation

end
