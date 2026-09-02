/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDEntropicWeightLinks
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
meta import Zil

/-!
# The Polyakov loop is the deconfinement order parameter: center Z(3) breaking + Boltzmann weight

The order parameter of the finite-temperature deconfinement transition is the **Polyakov loop** `⟨L⟩`. Under a
center `Z(N)` transformation it picks up a center element, `L ↦ z·L` with `z ∈ Z(N)`; its expectation is therefore
the order parameter of **center symmetry**:

* **confined phase** — center symmetry unbroken, so `⟨L⟩` is invariant under `L ↦ z·L` for a *nontrivial* center
  element `z ≠ 1`, which forces `⟨L⟩ = 0` (`center_invariant_forces_zero`, `cubeRoot_invariant_iff_confined`);
* **deconfined phase** — center symmetry broken, `⟨L⟩ ≠ 0`.

This ties three threads of the arc together through structure already built:

* the center is the repository's `Z(3)` triality `cubeRoot` (`colourCentre_triality`, `cubeRoot_ne_one`) — the
  same center that confines quarks (`quark_not_colour_singlet`) and deconfines the electron;
* the loop magnitude is the **Boltzmann weight of the single-quark free energy** `‖⟨L⟩‖ = e^{−F_q/T} =
  kuikenWeight T F_q` (`polyakovMagnitude`) — the entropic-weight hub of `ThermalQCDEntropicWeightLinks`. So the
  confined phase `⟨L⟩ = 0` is `F_q → ∞` (infinite energy to isolate a single quark), and the loop
  **grows with temperature** (`polyakov_grows_with_temperature`, via `kuikenWeight_monotone_in_temperature`) —
  heating drives deconfinement.

So deconfinement is `Z(3)` center-symmetry breaking, and the Polyakov loop is the single-quark Boltzmann weight
on the arc's entropic hub: `⟨L⟩ = 0` (confined, center-symmetric, `F_q = ∞`) vs `⟨L⟩ > 0` (deconfined,
center-broken, `F_q < ∞`, favored by high `T`).

* **§A — the center transformation `L ↦ z·L`** (`centerTransform`).
* **§B — center invariance forces `⟨L⟩ = 0`** (`center_invariant_forces_zero`, `cubeRoot_ne_one`).
* **§C — confined ⟺ `⟨L⟩ = 0`** (`cubeRoot_invariant_iff_confined`).
* **§D — the loop is the single-quark Boltzmann weight** (`polyakovMagnitude`, `polyakov_deconfined_pos`,
  `polyakov_grows_with_temperature`).
* **§E — assembled order parameter** (`polyakov_deconfinement_order_parameter`).

**Honest layering.** The center fixed-point (`⟨L⟩ = z⟨L⟩ ∧ z ≠ 1 ⟹ ⟨L⟩ = 0`) is exact field algebra; the loop
magnitude is *defined* as the Boltzmann weight `kuikenWeight T F_q`, reusing the entropic hub, and its
positivity / temperature-monotonicity are exact. The confined limit `⟨L⟩ = 0` is identified with `F_q → ∞`, not
taken as a formal limit; no lattice measure or transition temperature `T_c` is constructed. ## References

* A.M. Polyakov; L.D. McLerran, B. Svetitsky (Polyakov loop, center symmetry, deconfinement order parameter).
  Repo carriers: `Particles.StrongInteractionColorOctet` (`cubeRoot`, `colourCentre_triality`),
  `HorizonCell.ThermalQCDEntropicWeightLinks` (`kuikenWeight`, `kuikenWeight_monotone_in_temperature`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDEntropicWeightLinks
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement


/-- **The center transformation of the Polyakov loop** `L ↦ z·L` — under a `Z(N)` center element `z` the Polyakov
loop picks up `z` (the loop winds once around the thermal circle, so a center transformation multiplies it). -/
def centerTransform (z L : ℂ) : ℂ := z * L


/-- **[A loop invariant under a nontrivial center element vanishes] `L = z·L ∧ z ≠ 1 ⟹ L = 0`.** If the Polyakov
loop is unchanged by a nontrivial center transformation (unbroken center symmetry), it must be zero: `L(1−z) = 0`
with `1 − z ≠ 0`. This is the confinement half of the order parameter. -/
lemma center_invariant_forces_zero (z L : ℂ) (hz : z ≠ 1) (h : L = centerTransform z L) : L = 0 := by
  unfold centerTransform at h
  have h1 : (1 - z) * L = 0 := by rw [sub_mul, one_mul, ← h]; exact sub_self L
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2).symm hz
  · simpa using h2

/-- **[The `Z(3)` triality is nontrivial] `cubeRoot ≠ 1`.** The color center generator `cubeRoot = e^{2πi/3}` is a
nontrivial cube root of unity — `cubeRoot¹ = 1` would require `3 ∣ 1` (`colourCentre_triality`). -/
lemma cubeRoot_ne_one : cubeRoot ≠ 1 := by
  intro h
  have hd : (3 : ℤ) ∣ 1 := (colourCentre_triality 1).mp (by rw [zpow_one]; exact h)
  norm_num at hd


/-- **[Confinement ⟺ vanishing Polyakov loop] `L = cubeRoot·L ↔ L = 0`.** The Polyakov loop is invariant under
the `Z(3)` color center (center symmetry unbroken — the confined phase) exactly when it vanishes: `⟨L⟩ = 0` is the
confinement order parameter, `⟨L⟩ ≠ 0` is deconfinement (center broken). -/
lemma cubeRoot_invariant_iff_confined (L : ℂ) : L = centerTransform cubeRoot L ↔ L = 0 := by
  constructor
  · exact center_invariant_forces_zero cubeRoot L cubeRoot_ne_one
  · rintro rfl; unfold centerTransform; ring


/-- **The Polyakov-loop magnitude** `‖⟨L⟩‖ = e^{−F_q/T} = kuikenWeight T F_q` — the Boltzmann weight of the
single-quark free energy `F_q` at temperature `T`, on the arc's entropic-weight hub. -/
noncomputable def polyakovMagnitude (T F_q : ℝ) : ℝ := kuikenWeight T F_q

/-- **[The deconfined loop is positive] `‖⟨L⟩‖ > 0`.** For any finite single-quark free energy at positive
temperature the loop magnitude is strictly positive — the deconfined phase. The confined phase `⟨L⟩ = 0` is the
limit `F_q → ∞` (infinite energy to isolate one quark). -/
lemma polyakov_deconfined_pos (T F_q : ℝ) : 0 < polyakovMagnitude T F_q := by
  unfold polyakovMagnitude kuikenWeight; positivity

/-- **[The loop decreases as the single-quark free energy grows] `F₁ ≤ F₂ ⟹ ‖L‖(F₂) ≤ ‖L‖(F₁)`.** Larger
single-quark free energy means a smaller Polyakov loop — toward the confined `⟨L⟩ = 0` end (`kuikenWeight_antitone`,
the generalized second law). -/
lemma polyakov_antitone_in_freeEnergy (T : ℝ) (hT : 0 < T) {F1 F2 : ℝ} (h : F1 ≤ F2) :
    polyakovMagnitude T F2 ≤ polyakovMagnitude T F1 :=
  kuikenWeight_antitone T hT h

/-- **[Heating drives deconfinement: the loop grows with temperature] `T₁ ≤ T₂ ⟹ ‖L‖(T₁) ≤ ‖L‖(T₂)`.** At fixed
non-negative single-quark free energy, raising the temperature increases the Polyakov loop toward `1` — the
approach to deconfinement, via the temperature monotonicity of the entropic weight
(`kuikenWeight_monotone_in_temperature`). -/
lemma polyakov_grows_with_temperature (F_q : ℝ) (hF : 0 ≤ F_q) {T1 T2 : ℝ} (hT1 : 0 < T1)
    (h : T1 ≤ T2) : polyakovMagnitude T1 F_q ≤ polyakovMagnitude T2 F_q :=
  kuikenWeight_monotone_in_temperature F_q T1 T2 hF hT1 h


/-- **[The Polyakov loop as the deconfinement order parameter, assembled].**

* **confinement is `Z(3)` center symmetry**: the loop is center-invariant (`L = cubeRoot·L`) iff `⟨L⟩ = 0`;
* the loop magnitude is the **single-quark Boltzmann weight** `‖⟨L⟩‖ = kuikenWeight T F_q`, strictly positive for
  finite `F_q` (deconfined);
* it **grows with temperature** — heating drives deconfinement.

Deconfinement is center-symmetry breaking; the Polyakov loop is the single-quark Boltzmann weight on the arc's
entropic hub, vanishing (confined, `F_q = ∞`) exactly when the `Z(3)` center is unbroken. -/
lemma polyakov_deconfinement_order_parameter (L : ℂ) (T F_q : ℝ) :
    (L = centerTransform cubeRoot L ↔ L = 0)
      ∧ 0 < polyakovMagnitude T F_q
      ∧ polyakovMagnitude T F_q = kuikenWeight T F_q :=
  ⟨cubeRoot_invariant_iff_confined L, polyakov_deconfined_pos T F_q, rfl⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.cubeRoot_invariant_iff_confined where
  formalizes @ "claim:the-polyakov-loop-is-invariant-under-the-nontrivial-z3-center-transformation-iff-it-vanishes-the-confined-phase",
  supported_by @ "paper:polyakov-1978-thermal-deconfinement-center-symmetry"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakov_deconfinement_order_parameter where
  formalizes @ "claim:the-polyakov-loop-is-the-order-parameter-for-deconfinement-zero-in-the-confined-center-symmetric-phase-and-nonzero-when-the-center-symmetry-is-broken",
  requires @ "claim:the-polyakov-loop-is-invariant-under-the-nontrivial-z3-center-transformation-iff-it-vanishes-the-confined-phase",
  supported_by @ "paper:polyakov-1978-thermal-deconfinement-center-symmetry"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakov_grows_with_temperature where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDEntropicWeightLinks.kuikenWeight_monotone_in_temperature",
  formalizes @ "claim:the-polyakov-loop-magnitude-grows-with-temperature-so-deconfinement-sets-in-at-high-temperature"

zil_file_contract physlib.polyakovLoopDeconfinement where
  promises "The Polyakov loop as the order parameter of the QCD deconfinement transition: a loop invariant under the nontrivial Z(3) center transformation is forced to vanish (the confined, center-symmetric phase), and is nonzero exactly when the center symmetry is spontaneously broken (the deconfined phase); the loop magnitude is positive, decreases with the static-quark free energy, and grows with temperature, so deconfinement sets in at high temperature."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.centerTransform",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakovMagnitude"]
  forbids_substitutes ["a determination of the numerical deconfinement temperature, which is a lattice input",
    "a dynamical proof of the finite-temperature phase transition, only the center-symmetry order-parameter structure is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.center_invariant_forces_zero,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.cubeRoot_invariant_iff_confined,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakov_deconfinement_order_parameter,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement.polyakov_grows_with_temperature]

/- ZIL-END -/
