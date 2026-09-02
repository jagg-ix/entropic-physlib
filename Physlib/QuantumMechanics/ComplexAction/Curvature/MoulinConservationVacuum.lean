/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinEnergyConservation
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinEnergyMomentumDecomposition

meta import Zil

/-!
# Linking energy conservation (§4.7) and the Schwarzschild vacuum (§5.2) to the rest of Moulin's theory

Connects `GravitationalFieldEquations.MoulinEnergyConservation` (§4.7) and the vacuum regime of `GravitationalFieldEquations.MoulinSchwarzschildVacuum` (§5.2) to the
4-index energy-momentum tensor, the Cotton tensor, and the `B`-tensor.

* **§A — total energy-momentum conservation (Moulin Eq. 49).** Since `T_{ijkl} = G_{ijkl}/χ`, the divergence
  of the total 4-index energy-momentum tensor is `∇^i T_{ijkl} = ∇^i G_{ijkl}/χ`
  (`energyMomentumDivergence4`); it vanishes at the energy-conserving `a = −1/(n−3)`
  (`energyMomentum4_conservation`).
* **§B — the actual Cotton tensor.** Instantiating `∇^i G_{ijkl} = −(1+a(n−3))/(n−2) C_{jkl}` with the genuine
  Cotton tensor (`GravitationalFieldEquations.MoulinDoubleDualCotton.cottonTensor`): with a non-vanishing Cotton tensor, total
  conservation fixes `a = −1/(n−3)` (`einsteinDivergence4_cottonTensor_eq_zero_iff`, Moulin Eq. 51).
* **§C — the vacuum / Schwarzschild regime.** A centrally symmetric vacuum (`T^(M) = 0`) is exactly the
  vanishing of the `B`-tensor — and `B` vanishes wherever the Ricci tensor and scalar curvature do
  (`bTensor_vacuum_zero`, `matterEnergyMomentum_vacuum_zero`). The Schwarzschild metric
  `A = 1/B = 1 + r_g/r` (`GravitationalFieldEquations.MoulinSchwarzschildVacuum`) is the centrally symmetric metric realizing this vacuum.

## References

* F. Moulin (2024), arXiv:2405.03698, §4.7, §5.2; Eqs. 49, 51, 58. Carrier: `Physlib`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*}


/-- **The covariant divergence of the total 4-index energy-momentum tensor** `∇^i T_{ijkl} = ∇^i G_{ijkl}/χ`
(from `T = G/χ`). -/
noncomputable def energyMomentumDivergence4 (χ a n : ℝ) (cotton : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun j k l => χ⁻¹ * einsteinDivergence4 a n cotton j k l

/-- **[Moulin Eq. 49] total energy-momentum conservation `∇^i T_{ijkl} = 0`** at the energy-conserving
parameter `a = −1/(n−3)`. -/
lemma energyMomentum4_conservation (χ n : ℝ) (cotton : ι → ι → ι → ℝ) (hn3 : n - 3 ≠ 0) (j k l : ι) :
    energyMomentumDivergence4 χ (-1 / (n - 3)) n cotton j k l = 0 := by
  rw [energyMomentumDivergence4, einsteinDivergence4_conserving n cotton hn3, mul_zero]


/-- **[Moulin Eq. 51, with the genuine Cotton tensor]** with a non-vanishing Cotton tensor, total
energy-momentum conservation `∇^i G_{ijkl} = 0` holds iff `a = −1/(n−3)`. -/
lemma einsteinDivergence4_cottonTensor_eq_zero_iff (a n : ℝ) (g : Matrix ι ι ℝ)
    (nablaRic : ι → ι → ι → ℝ) (nablaR : ι → ℝ) (hn2 : n - 2 ≠ 0) (hn3 : n - 3 ≠ 0)
    (hc : ∃ j k l, cottonTensor n g nablaRic nablaR j k l ≠ 0) :
    (∀ j k l, einsteinDivergence4 a n (cottonTensor n g nablaRic nablaR) j k l = 0)
      ↔ a = -1 / (n - 3) :=
  einsteinDivergence4_eq_zero_iff a n (cottonTensor n g nablaRic nablaR) hn2 hn3 hc


/-- **[The `B`-tensor vanishes in vacuum] `Ric = 0 ∧ R = 0 ⇒ B_{ijkl} = 0`.** A centrally symmetric vacuum
`T^(M) = 0` — the regime solved by the Schwarzschild metric — is the vanishing of the `B`-tensor. -/
lemma bTensor_vacuum_zero (n : ℝ) (g : Matrix ι ι ℝ) :
    bTensor n g 0 0 = (0 : RiemannTensor ι) := by
  funext i j k l; simp [bTensor]

/-- **[The matter energy-momentum vanishes in vacuum] `T^(M)_{ijkl} = 0`.** -/
lemma matterEnergyMomentum_vacuum_zero (χ n : ℝ) (g : Matrix ι ι ℝ) :
    matterEnergyMomentum χ n g 0 0 = (0 : RiemannTensor ι) := by
  rw [matterEnergyMomentum, bTensor_vacuum_zero, smul_zero]

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.energyMomentum4_conservation where
  formalizes @ "claim:the-covariant-divergence-of-the-total-4-index-energy-momentum-tensor-vanishes-identically-at-the-parameter-a-equals-minus-one-over-n-minus-three-automatic-topological-bianchi-conservation",
  supported_by @ "paper:moulin-arxiv-2405-03698-generalization-of-einsteins-gravitational-field-equations"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.einsteinDivergence4_cottonTensor_eq_zero_iff where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.einsteinDivergence4_eq_zero_iff",
  formalizes @ "claim:with-a-genuinely-non-vanishing-cotton-tensor-total-conservation-vanishing-divergence-of-the-4-index-einstein-tensor-holds-exactly-when-a-equals-minus-one-over-n-minus-three-fixing-the-parameter-uniquely"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor_vacuum_zero where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:ricci-flat-vacuum-with-vanishing-scalar-curvature-is-exactly-the-vanishing-of-the-b-matter-tensor-the-regime-realized-by-the-schwarzschild-metric"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.matterEnergyMomentum_vacuum_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor_vacuum_zero",
  formalizes @ "claim:in-ricci-flat-vacuum-the-matter-part-of-the-4-index-energy-momentum-tensor-vanishes-entirely"

zil_file_contract physlib.moulinConservationVacuum where
  promises "Energy conservation (Moulin section 4.7) and the Schwarzschild vacuum (section 5.2). The covariant divergence of the total 4-index energy-momentum tensor vanishes identically at a = -1/(n-3) (energyMomentum4_conservation) -- automatic topological/Bianchi conservation -- and with a non-vanishing Cotton tensor this fixes the parameter uniquely (einsteinDivergence4_cottonTensor_eq_zero_iff). Ricci-flat vacuum is exactly the vanishing of the B (matter) tensor, the Schwarzschild regime (bTensor_vacuum_zero), where the matter energy-momentum vanishes entirely (matterEnergyMomentum_vacuum_zero)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.energyMomentumDivergence4",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.cottonTensor"]
  forbids_substitutes ["the explicit Schwarzschild metric solution and the covariant conservation law on a genuine Ricci-flat spacetime, which are the cited GR infrastructure",
    "any claim that a solution of the field equations is exhibited; only the algebraic vacuum vanishing and the conservation-parameter fixing are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.energyMomentum4_conservation,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.einsteinDivergence4_cottonTensor_eq_zero_iff,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor_vacuum_zero,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.matterEnergyMomentum_vacuum_zero]

/- ZIL-END -/
