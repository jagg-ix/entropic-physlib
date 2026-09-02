/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy
meta import Zil

/-!
# Conservation from the electrogravitic residual

The electrogravitic residual (`electrograviticResidualCoordinate`) packages the Einstein-Maxwell
equation in its real part (`G − κ T^Maxwell`) and the entropic-Einstein equation in its imaginary part
(`Λ − κ S`).  Its vanishing is equivalent to stationarity, but conservation was never joined to it.

This module wires the residual directly to the conservation laws on both sides of the BCJ double copy.
When the residual vanishes, the Einstein-Maxwell equation `G = κ T^Maxwell` holds, so the contracted
(second) Bianchi identity `∇^μ G_{μν} = 0` forces the Maxwell stress-energy to be conserved
(`bianchi_implies_conservation`) — the gravity side; and the gauge side is the electromagnetic second
Bianchi `∂_ν J^ν = 0` (`em_second_bianchi`).  The two are the gravity/gauge double-copy partners
`∇^μ T^Maxwell_{μν} = 0` ↔ `∂_ν J^ν = 0`.

* `electrogravitic_residual_conservation` — a vanishing electrogravitic residual (with the contracted
  Bianchi `∇^μ G_{μν} = 0`) gives both conservation laws: `∇^μ T^Maxwell_{μν} = 0` and `∂_ν J^ν = 0`.

Honest scope: the contracted Bianchi `∇^μ G_{μν} = 0` is taken as the labeled input (its uncontracted
differential form is `SecondBianchiFromConnection.covariantRiemannFlat_secondBianchi`; the metric
contraction is not carried here).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-- **Conservation from the electrogravitic residual.**  If the electrogravitic residual vanishes at
every point (equivalently the Einstein-Maxwell equation `G = κ T^Maxwell` and `Λ = κ S` hold), then
with the contracted Bianchi identity `∇^μ G_{μν} = 0` (`hBianchi`) and `κ ≠ 0` **both** double-copy
conservation laws follow: the Maxwell stress-energy is conserved on the gravity side,
`∇^μ T^Maxwell_{μν} = 0`, and the electromagnetic current is conserved on the gauge side,
`∂_ν J^ν = 0`. -/
@[zil_level bridge_theorem]
theorem electrogravitic_residual_conservation
    (Div : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] (Fin 4 → ℝ))
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor) (κ : ℝ) (k A : Fin 4 → ℝ)
    (hResidual : ∀ μ ν, electrograviticResidualCoordinate Ric scalarR g gInv Λ S κ k A μ ν = 0)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) (hκ : κ ≠ 0) :
    Div (maxwellStressEnergy g gInv (faraday k A)) = 0
      ∧ ∑ i, k i * fourCurrent k A i = 0 := by
  have hEFE : einsteinFieldEquation Ric scalarR g (maxwellStressEnergy g gInv (faraday k A)) κ := by
    unfold einsteinFieldEquation
    ext μ ν
    have hre :
        (einsteinTensor Ric scalarR g - κ • maxwellStressEnergy g gInv (faraday k A)) μ ν = 0 := by
      have h := congrArg Complex.re (hResidual μ ν)
      rw [electrograviticResidualCoordinate_re] at h
      simpa using h
    rw [Matrix.sub_apply, sub_eq_zero] at hre
    exact hre
  exact ⟨bianchi_implies_conservation Div Ric scalarR g _ κ hEFE hBianchi hκ, em_second_bianchi k A⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation

zil attach electrogravitic_residual_conservation where
  formalizes @ "claim:a-vanishing-electrogravitic-residual-with-the-contracted-bianchi-identity-gives-both-double-copy-conservation-laws-the-maxwell-stress-energy-is-conserved-on-the-gravity-side-and-the-electromagnetic-current-is-conserved-on-the-gauge-side",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.bianchi_implies_conservation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy.em_second_bianchi"

zil_file_contract physlib.electrograviticResidualConservation where
  promises "Conservation from the electrogravitic residual, wiring the residual to the double-copy conservation laws on both the gravity and gauge sides. When the electrogravitic residual vanishes at every point, equivalently the Einstein-Maxwell equation Einstein tensor equals kappa times Maxwell stress-energy holds, then with the contracted second Bianchi identity the divergence of the Einstein tensor is zero and kappa nonzero, both double-copy conservation laws follow: the Maxwell stress-energy is conserved on the gravity side, its divergence is zero, and the electromagnetic four-current is conserved on the gauge side, the four-divergence of the current is zero. These are the gravity and gauge double-copy partners. Honest scope: the contracted second Bianchi that the divergence of the Einstein tensor is zero is taken as the labeled input; its uncontracted differential form is the second Bianchi from a connection, and the metric contraction is not carried here."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electrograviticResidualCoordinate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellStressEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy.em_second_bianchi"
  ]
  forbids_substitutes [
    "reading the residual conservation as also deriving the contracted Bianchi identity from a connection rather than taking it as a labeled input"
  ]
  witnessed_by [
    electrogravitic_residual_conservation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.electrograviticResidualConservation
