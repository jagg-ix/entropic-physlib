/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionThermalBoundary
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-!
# The emitting boundary's generalized second law: entropy production on the entropic-weight hub

Closes the electron-exclusion-cell arc's thermodynamics. The exclusion cell's boundary emits photons
(`ElectronExclusionThermalBoundary`); each emission grows the boundary area `A`, hence its Bekenstein
imaginary action `S_I = (c³/4G)·A` (`MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction`).
That `S_I` is the imaginary part of the cell's complex action, and enters the master complex-action weight
whose **modulus is the entropic weight** `kuikenWeight ℏ S_I = e^{−S_I/ℏ}`
(`PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken`) — the same `kuikenWeight` hub that
unifies every complex-action path integral in the repository.

**The generalized second law is the monotonicity of the entropic weight.** As the boundary radiates and its
entropy grows (`A₁ ≤ A₂ ⟹ S_{I,1} ≤ S_{I,2}`), the entropic weight *decreases*
(`kuikenWeight_antitone`) and stays bounded by `1` (`kuikenWeight_le_one`): irreversibility increases
monotonically, and the reversible bound `e^{−S_I/ℏ} ≤ 1` holds for any non-negative entropy production. At the
static / reversible limit (`Ȧ = 0`, no emission) the entropy production rate vanishes, so the cell's
gravitational mass `m = Ṡ_I/c²` is zero (`exclusionCell_static_massless`) and the weight is `1`
(`exclusionCell_reversible_unit_weight`) — the massless bifurcation of the whole arc is the no-entropy-production
point.

* **§A — the boundary entropic weight is `kuikenWeight ℏ S_I`** (`exclusionCell_boundary_entropic_weight`).
* **§B — the generalized second law** (`kuikenWeight_le_one`, `kuikenWeight_antitone`).
* **§C — mass = entropy-production rate; static ⟹ reversible** (`exclusionCell_gravitationalMass_eq`,
  `exclusionCell_static_massless`, `exclusionCell_reversible_unit_weight`).
* **§D — assembled** (`electron_boundary_generalized_second_law`).

**Honest layering.** §A reuses `master_modulus_is_kuiken` verbatim; §C reuses `gravitationalMass_eq`. §B is the
new content — the monotonicity/bound of the entropic weight as the second law (exact `Real.exp` inequalities),
not previously stated for `kuikenWeight`. The `S_I = (c³/4G)A` identification is `horizonImaginaryAction`; no
new thermodynamic postulate is introduced. ## References

* Repo carriers: `PathIntegral.ComplexActionPathIntegralWeight` (`kuikenWeight`, `master_modulus_is_kuiken`),
  `MassOrigin.GravitationalMassHorizonEntropyNoYukawa`, `HorizonCell.ElectronExclusionThermalBoundary`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction


/-- **[The boundary's entropic weight is `kuikenWeight ℏ S_I`].** The exclusion cell's boundary carries the
Bekenstein imaginary action `S_I = horizonImaginaryAction G c A = (c³/4G)·A`; it enters the master
complex-action weight, whose modulus is the entropic damping `e^{−S_I/ℏ} = kuikenWeight ℏ S_I` — the boundary
sits on the entropic-weight hub. -/
lemma exclusionCell_boundary_entropic_weight (S_R G c A ħ : ℝ) :
    ‖complexActionPathIntegralWeight S_R (horizonImaginaryAction G c A) ħ‖
      = kuikenWeight ħ (horizonImaginaryAction G c A) :=
  master_modulus_is_kuiken S_R (horizonImaginaryAction G c A) ħ


/-- **[Reversible bound] `kuikenWeight ℏ S_I ≤ 1` for `S_I ≥ 0`.** Any non-negative entropy production gives an
entropic weight at most one — the boundary is (weakly) irreversible, never entropy-decreasing. -/
lemma kuikenWeight_le_one (ħ Pi : ℝ) (hħ : 0 < ħ) (hPi : 0 ≤ Pi) : kuikenWeight ħ Pi ≤ 1 := by
  unfold kuikenWeight
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr (div_nonneg hPi hħ.le))

/-- **[The generalized second law] the entropic weight is antitone in the entropy production.** As the
boundary radiates and its imaginary action grows (`Pi₁ ≤ Pi₂`), the entropic weight `e^{−Pi/ℏ}` *decreases*:
`kuikenWeight ℏ Pi₂ ≤ kuikenWeight ℏ Pi₁` — irreversibility increases monotonically with entropy production. -/
lemma kuikenWeight_antitone (ħ : ℝ) (hħ : 0 < ħ) {Pi1 Pi2 : ℝ} (h : Pi1 ≤ Pi2) :
    kuikenWeight ħ Pi2 ≤ kuikenWeight ħ Pi1 := by
  unfold kuikenWeight
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  gcongr


/-- **[The gravitational mass is the boundary entropy-production rate] `m = (c/4G)·Ȧ`.** The cell's mass is
its horizon entropy-production rate `Ṡ_I/c²` — the Higgs-free mass–entropy duality (`gravitationalMass_eq`). -/
lemma exclusionCell_gravitationalMass_eq (G c Adot : ℝ) (hc : c ≠ 0) :
    gravitationalMass G c Adot = c / (4 * G) * Adot :=
  gravitationalMass_eq G c Adot hc

/-- **[Static boundary ⟹ massless] `Ȧ = 0 → m = 0`.** With no photon emission the horizon is static, the
entropy-production rate vanishes, and the cell's gravitational mass is zero — the reversible / massless
bifurcation point of the arc. -/
lemma exclusionCell_static_massless (G c : ℝ) : gravitationalMass G c 0 = 0 := by
  unfold gravitationalMass horizonEntropyRate; simp

/-- **[Reversible boundary ⟹ unit entropic weight] `kuikenWeight ℏ 0 = 1`.** With no entropy production the
entropic weight is one: the boundary evolves reversibly (unitarily). -/
lemma exclusionCell_reversible_unit_weight (ħ : ℝ) : kuikenWeight ħ 0 = 1 := by
  unfold kuikenWeight; simp


/-- **[The emitting boundary's generalized second law, assembled].** As the exclusion cell's boundary radiates
and its area grows `A₁ ≤ A₂` (with `A₁ ≥ 0`), the entropic weight of the smaller area is bounded by one, and
the weight *decreases* with the emitted entropy: `kuikenWeight ℏ S_{I,2} ≤ kuikenWeight ℏ S_{I,1} ≤ 1`. The
photon-emitting boundary obeys the generalized second law on the entropic-weight hub — irreversibility grows
monotonically with each emission. -/
lemma electron_boundary_generalized_second_law
    (G c ħ : ℝ) (hħ : 0 < ħ) (hG : 0 < G) (hc : 0 < c) {A1 A2 : ℝ} (hA1 : 0 ≤ A1) (hA : A1 ≤ A2) :
    kuikenWeight ħ (horizonImaginaryAction G c A1) ≤ 1
      ∧ kuikenWeight ħ (horizonImaginaryAction G c A2)
          ≤ kuikenWeight ħ (horizonImaginaryAction G c A1) := by
  have hSI1 : 0 ≤ horizonImaginaryAction G c A1 := by unfold horizonImaginaryAction; positivity
  have hmono : horizonImaginaryAction G c A1 ≤ horizonImaginaryAction G c A2 := by
    unfold horizonImaginaryAction; gcongr
  exact ⟨kuikenWeight_le_one ħ _ hħ hSI1, kuikenWeight_antitone ħ hħ hmono⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction

end
