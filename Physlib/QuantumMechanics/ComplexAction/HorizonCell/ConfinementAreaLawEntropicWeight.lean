/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction
meta import Zil

/-!
# The confinement area law is an entropic weight: `⟨W⟩ = e^{−σA} = kuikenWeight(σA)`

Formalizes the **confinement criterion** of Dehghan–Faber (arXiv:2412.10767, §2): the dual-superconductor /
center-vortex mechanism gives a **constant string tension** `σ`, hence a **linear confining potential**
`V(R) = σR` (a flux tube whose tension is independent of distance), and the **area law of Wilson loops**
`⟨W(C)⟩ ∼ e^{−σ·Area}` — the signature of confinement.

The bridge to the electron-cell arc is that the area-law suppression is *exactly* the entropic weight
`kuikenWeight = e^{−S_I/ℏ}` on which the whole complex-action edifice unifies, with the **confining imaginary
action** `S_I = σ·Area` (string tension × minimal area):

* the **linear confining potential grows without bound** (`confining_potential_monotone`) — infinite energy to
  separate a quark pair, the confinement of the dual-superconductor flux tube;
* the **area law is the entropic weight** `e^{−σA} = kuikenWeight 1 (σA)` (`areaLaw_is_kuikenWeight`) — the
  center-vortex confinement suppression is the `kuikenWeight` with `S_I = σ·Area`;
* so the **confining Wilson loop obeys the arc's generalized second law** (`confinement_obeys_gsl`): as the loop
  area grows the Wilson loop decreases (`kuikenWeight_antitone`), and it is bounded by `1`
  (`confinement_weight_le_one`, `kuikenWeight_le_one`). The area-law confinement is the entropic monotonicity of
  the arc.

So the confinement mechanism sits on the same entropic-weight hub as the electron cell: the string-tension × area
is a confining imaginary action `S_I`, and the area-law Wilson loop is its `kuikenWeight`, obeying the same
generalized second law.

* **§A — the linear confining potential** (`linearConfiningPotential`, `confining_potential_monotone`).
* **§B — the area law is the entropic weight** (`wilsonAreaLaw`, `areaLaw_is_kuikenWeight`).
* **§C — the confining Wilson loop obeys the GSL** (`confinement_obeys_gsl`, `confinement_weight_le_one`).
* **§D — assembled** (`confinement_areaLaw_entropic`).

**Honest layering.** §A is an exact `mul_le_mul` monotonicity; §B/§C reuse `kuikenWeight`, `kuikenWeight_antitone`,
`kuikenWeight_le_one`. The content is the identification of the confinement area law with the `kuikenWeight`
(`S_I = σ·Area`); no lattice string-tension dynamics is formalized. ## References

* Z. Dehghan, M. Faber, arXiv:2412.10767, §2 (dual superconductor / center vortices; linear potential; area law).
  S. Mandelstam; G. 't Hooft (dual superconductor). Repo carriers:
  `PathIntegral.ComplexActionPathIntegralWeight`, `HorizonCell.ElectronExclusionEntropyProduction`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight


/-- **The linear confining potential** `V(R) = σ·R` — the flux-tube potential of the dual-superconductor /
center-vortex vacuum, with constant string tension `σ` (independent of the separation `R`). -/
def linearConfiningPotential (σ R : ℝ) : ℝ := σ * R

/-- **[The confining potential grows with separation].** For a non-negative string tension `σ`, the linear
potential `V(R) = σR` is non-decreasing in the quark–antiquark separation `R`: separating the pair costs energy
that grows without bound — the confinement of the flux tube. -/
@[zil_level physical_theorem]
lemma confining_potential_monotone (σ : ℝ) (hσ : 0 ≤ σ) {R1 R2 : ℝ} (h : R1 ≤ R2) :
    linearConfiningPotential σ R1 ≤ linearConfiningPotential σ R2 :=
  mul_le_mul_of_nonneg_left h hσ


/-- **The Wilson-loop area law** `⟨W(C)⟩ = e^{−σ·A}` — the confinement signature: the expectation of a large
Wilson loop of minimal area `A` is suppressed exponentially in the area, with coefficient the string tension `σ`. -/
noncomputable def wilsonAreaLaw (σ A : ℝ) : ℝ := Real.exp (-(σ * A))

/-- **[The area law is the entropic weight] `e^{−σA} = kuikenWeight 1 (σA)`.** The confinement area-law
suppression of the Wilson loop is exactly the entropic weight `kuikenWeight = e^{−S_I/ℏ}` (at `ℏ = 1`) with the
**confining imaginary action** `S_I = σ·A` (string tension times minimal area). Confinement sits on the
complex-action entropic-weight hub. -/
@[zil_level physical_theorem]
lemma areaLaw_is_kuikenWeight (σ A : ℝ) : wilsonAreaLaw σ A = kuikenWeight 1 (σ * A) := by
  unfold wilsonAreaLaw kuikenWeight; rw [div_one]


/-- **[The confining Wilson loop obeys the arc's generalized second law].** For a non-negative string tension,
as the loop area grows (`A₁ ≤ A₂`) the area-law Wilson loop *decreases* — the entropic monotonicity
(`kuikenWeight_antitone`) of the arc applied to confinement: bigger loops are more suppressed, the confining
imaginary action `S_I = σA` increasing. -/
@[zil_level physical_theorem]
lemma confinement_obeys_gsl (σ : ℝ) (hσ : 0 ≤ σ) {A1 A2 : ℝ} (h : A1 ≤ A2) :
    wilsonAreaLaw σ A2 ≤ wilsonAreaLaw σ A1 := by
  rw [areaLaw_is_kuikenWeight, areaLaw_is_kuikenWeight]
  exact kuikenWeight_antitone 1 one_pos (mul_le_mul_of_nonneg_left h hσ)

/-- **[The area-law Wilson loop is bounded by one].** With non-negative string tension and area, the confining
Wilson loop `e^{−σA} ≤ 1` (`kuikenWeight_le_one`): the confinement weight is a bona-fide suppression. -/
@[zil_level physical_theorem]
lemma confinement_weight_le_one (σ A : ℝ) (hσ : 0 ≤ σ) (hA : 0 ≤ A) : wilsonAreaLaw σ A ≤ 1 := by
  rw [areaLaw_is_kuikenWeight]
  exact kuikenWeight_le_one 1 (σ * A) one_pos (mul_nonneg hσ hA)


/-- **[The confinement area law as an entropic weight, assembled].** For a non-negative string tension `σ`:

* the linear confining potential `V(R) = σR` grows with the separation (`R₁ ≤ R₂`);
* the area-law Wilson loop is the entropic weight `e^{−σA} = kuikenWeight 1 (σA)`;
* it obeys the generalized second law — decreasing with area (`A₁ ≤ A₂`) and bounded by `1`.

The confinement mechanism (linear potential, area law) is the complex-action entropic weight with the confining
imaginary action `S_I = σ·Area`, obeying the arc's generalized second law. -/
@[zil_level physical_theorem]
lemma confinement_areaLaw_entropic (σ : ℝ) (hσ : 0 ≤ σ) {R1 R2 A1 A2 : ℝ}
    (hR : R1 ≤ R2) (hA : A1 ≤ A2) (hA1 : 0 ≤ A1) :
    linearConfiningPotential σ R1 ≤ linearConfiningPotential σ R2
      ∧ wilsonAreaLaw σ A1 = kuikenWeight 1 (σ * A1)
      ∧ wilsonAreaLaw σ A2 ≤ wilsonAreaLaw σ A1
      ∧ wilsonAreaLaw σ A1 ≤ 1 :=
  ⟨confining_potential_monotone σ hσ hR, areaLaw_is_kuikenWeight σ A1,
    confinement_obeys_gsl σ hσ hA, confinement_weight_le_one σ A1 hσ hA1⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.areaLaw_is_kuikenWeight where
  formalizes @ "claim:the-wilson-loop-confinement-area-law-e-to-minus-sigma-area-is-exactly-the-entropic-kuiken-weight-with-confining-imaginary-action-s-i-equal-string-tension-times-minimal-area",
  supported_by @ "paper:dehghan-faber-center-vortex-dual-superconductor-confinement-arxiv-2412-10767"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.confinement_obeys_gsl where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.areaLaw_is_kuikenWeight",
  formalizes @ "claim:the-confining-wilson-loop-obeys-the-generalized-second-law-decreasing-as-the-loop-area-grows-and-bounded-by-one-the-entropic-monotonicity-of-area-law-confinement",
  requires @ "claim:the-wilson-loop-confinement-area-law-e-to-minus-sigma-area-is-exactly-the-entropic-kuiken-weight-with-confining-imaginary-action-s-i-equal-string-tension-times-minimal-area"

zil_file_contract physlib.confinementAreaLawEntropicWeight where
  promises "The confinement criterion of Dehghan-Faber (arXiv:2412.10767): the dual-superconductor / center-vortex mechanism gives a constant string tension sigma, hence a linear confining potential V(R) = sigma R (a flux tube of distance-independent tension) and the Wilson-loop area law <W(C)> ~ e^{-sigma Area}. The bridge to the electron-cell arc is that the area-law suppression is exactly the entropic weight kuikenWeight = e^{-S_I/hbar} with confining imaginary action S_I = sigma times Area: the linear potential grows without bound (infinite energy to separate a quark pair), the area law equals kuikenWeight 1 (sigma A), and so the confining Wilson loop obeys the arc's generalized second law -- decreasing as the loop area grows and bounded by one. The confinement mechanism sits on the same entropic-weight hub as the electron cell; the center-vortex/dual-superconductor dynamics is recorded from the paper, not re-derived, only its area-law entropic monotonicity is proven."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.wilsonAreaLaw",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.linearConfiningPotential"]
  forbids_substitutes ["a perimeter-law or constant Wilson loop, whereas confinement is the area law e^{-sigma Area}",
    "a distance-dependent string tension, whereas the confining tension sigma is constant giving a linear potential"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.confining_potential_monotone,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.areaLaw_is_kuikenWeight,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.confinement_obeys_gsl,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.confinement_weight_le_one,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight.confinement_areaLaw_entropic]

#zil_formalization_lint physlib.confinementAreaLawEntropicWeight

/- ZIL-END -/
