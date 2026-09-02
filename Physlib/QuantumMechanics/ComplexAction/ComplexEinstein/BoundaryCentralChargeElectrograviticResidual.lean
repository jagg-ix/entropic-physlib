/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.HolographicElectrograviticResidual
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual -/

/-!
# The boundary-CFT central charge controls the electrogravitic residual (AdS/CFT central-charge form)

The holographic screen dictionary (`HolographicElectrograviticResidual`) fixed the bulk Einstein
coupling by the Bekenstein–Hawking bit count.  This module gives the AdS/CFT *central-charge*
form of the same bridge: the boundary CFT central charge `c_CFT = N²/4` sets the bulk coupling
`κ₄ = (π²R³/(Vc⁴))/c_CFT = 4π²R³/(N²Vc⁴)` (the D3-brane reduction, `EMComplexEinsteinAdSCFT`),
at which *both* residual sectors — the Einstein–Maxwell residual and the imaginary
entropic-Einstein residual — vanish together iff the metric is electrogravitically stationary.

* `boundaryCentralCharge_electrograviticResidual_vanishing` — the boundary central-charge coupling
  equals the D3-reduced bulk coupling, and at it the electrogravitic residual vanishes iff
  stationarity.
* `boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual` — at the central-charge
  coupling, stationarity holds iff the Einstein–Maxwell residual and the imaginary entropic residual
  both vanish for every `μ, ν`.

Honest scope: a coupling dictionary parametrized by the boundary central charge, not a derivation
of AdS/CFT.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.HolographicElectrograviticResidual
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

/-- **The boundary central charge fixes the coupling that makes both residuals vanish.**  With the
boundary CFT central charge `c_CFT = N²/4`, the bulk coupling `boundaryCentralChargeEinsteinCoupling`
equals the D3-reduced coupling `4π²R³/(N²Vc⁴)`, and at that coupling the electrogravitic residual
(both sectors) vanishes iff the metric is electrogravitically stationary. -/
@[zil_level bridge_theorem]
theorem boundaryCentralCharge_electrograviticResidual_vanishing
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor) (k A : Fin 4 → ℝ)
    (R N V c : ℝ) (hN : N ≠ 0) (hV : V ≠ 0) (hc : c ≠ 0) :
    (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)
        = d3ReducedEinsteinCoupling R N V c)
      ∧ (IsElectrograviticMetricStationary Ric scalarR g gInv Λ S
            (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A
          ↔ ∀ μ ν, electrograviticResidualCoordinate Ric scalarR g gInv Λ S
              (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A μ ν = 0) :=
  ⟨(d3ReducedEinsteinCoupling_eq_boundaryCentralCharge R N V c hN hV hc).symm,
   metricStationary_iff_residualCoordinate_zero Ric scalarR g gInv Λ S
     (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A⟩

/-- **The boundary central charge governs both residual sectors.**  At the AdS/CFT central-charge
coupling `κ₄ = (π²R³/(Vc⁴))/(N²/4)`, the metric is electrogravitically stationary iff the
Einstein–Maxwell residual and the imaginary entropic-Einstein residual both vanish for every index
pair — one boundary CFT quantity controlling both residuals. -/
@[zil_level bridge_theorem]
theorem boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor) (k A : Fin 4 → ℝ) (R N V c : ℝ) :
    IsElectrograviticMetricStationary Ric scalarR g gInv Λ S
        (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A
      ↔ ∀ μ ν,
        (einsteinTensor Ric scalarR g
            - (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N))
              • maxwellStressEnergy g gInv (faraday k A)) μ ν = 0
          ∧ (Λ - (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) • S) μ ν = 0 := by
  rw [metricStationary_iff_residualCoordinate_zero Ric scalarR g gInv Λ S
    (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A]
  refine forall_congr' fun μ => forall_congr' fun ν => ?_
  exact electrograviticResidual_zero_iff_reim Ric scalarR g gInv Λ S
    (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A μ ν

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual

zil attach boundaryCentralCharge_electrograviticResidual_vanishing where
  formalizes @ "claim:the-boundary-cft-central-charge-n-squared-over-four-fixes-the-bulk-einstein-coupling-equal-to-the-d3-reduced-coupling-at-which-the-electrogravitic-residual-vanishes-iff-the-metric-is-stationary-the-ads-cft-central-charge-form",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3ReducedEinsteinCoupling_eq_boundaryCentralCharge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_residualCoordinate_zero"

zil attach boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual where
  formalizes @ "claim:at-the-boundary-cft-central-charge-coupling-the-metric-is-stationary-iff-the-einstein-maxwell-residual-and-the-imaginary-entropic-einstein-residual-both-vanish-so-one-boundary-central-charge-controls-both-residuals",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.HolographicElectrograviticResidual.electrograviticResidual_zero_iff_reim"

zil_file_contract physlib.boundaryCentralChargeElectrograviticResidual where
  promises "The AdS/CFT central-charge form of the holographic electrogravitic-residual dictionary. The boundary CFT central charge N squared over four fixes the bulk Einstein coupling equal to the D3-brane reduced coupling four pi squared R cubed over N squared V c to the fourth, at which the electrogravitic residual, whose real part is the Einstein-Maxwell residual and whose imaginary part is the imaginary entropic-Einstein residual, vanishes iff the metric is electrogravitically stationary. At that boundary central-charge coupling the metric is stationary iff the Einstein-Maxwell residual and the imaginary entropic residual both vanish for every index pair, so a single boundary CFT central charge controls both residual sectors. This is a coupling dictionary parametrized by the boundary central charge, not a derivation of AdS/CFT."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.electrograviticResidualCoordinate",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.boundaryCentralChargeEinsteinCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.centralChargeN4"
  ]
  forbids_substitutes [
    "reading the central-charge coupling dictionary as a derivation of AdS/CFT",
    "dropping the nonzero premises on N, V, c needed for the coupling identity"
  ]
  witnessed_by [
    boundaryCentralCharge_electrograviticResidual_vanishing,
    boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.boundaryCentralChargeElectrograviticResidual

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual -/

/-!
# The boundary central charge governs both the electrogravitic residual and the Liouville complexity

Two AdS/CFT bridges built earlier share one object — the boundary CFT central charge
`c_CFT = centralChargeN4 N = N²/4`:

* it fixes the electrogravitic residual coupling
  (`BoundaryCentralChargeElectrograviticResidual`), at which the Einstein–Maxwell residual and the
  imaginary entropic-Einstein residual vanish together iff the metric is stationary, and
* it normalizes the Caputa–Takayanagi Liouville path-integral complexity
  (`LiouvilleComplexityHolographicSpine`), `vacuumLiouvilleComplexity c ε = (c/6)(1/ε − 1)`.

This module ties the two.

* `boundaryCentralCharge_governs_residual_and_liouvilleComplexity` — at the boundary central charge
  `centralChargeN4 N`, the electrogravitic residual vanishes iff stationarity, and the same central
  charge sets a positive vacuum path-integral complexity.
* `liouvilleComplexity_times_residualCoupling_centralChargeInvariant` — the product of the Liouville
  complexity and the residual coupling is **independent of the central charge**: the `N²/4` cancels,
  leaving `(π²R³/6Vc⁴)(1/ε − 1)`.  Complexity grows with `c` while the coupling shrinks as `1/c`, and
  their product is a fixed geometric datum.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine

/-- **The boundary central charge governs both the residual and the complexity.**  At the boundary
CFT central charge `c_CFT = N²/4`, the electrogravitic residual vanishes iff the metric is
electrogravitically stationary, and the same central charge sets a positive vacuum path-integral
complexity — one boundary CFT quantity controlling both the gravitational residual and the
CFT-side path-integral complexity. -/
@[zil_level bridge_theorem]
theorem boundaryCentralCharge_governs_residual_and_liouvilleComplexity
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor) (k A : Fin 4 → ℝ)
    (R N V c ε : ℝ) (hN : N ≠ 0) (hV : V ≠ 0) (hc : c ≠ 0) (hε : 0 < ε) (hε1 : ε < 1) :
    (IsElectrograviticMetricStationary Ric scalarR g gInv Λ S
          (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A
        ↔ ∀ μ ν, electrograviticResidualCoordinate Ric scalarR g gInv Λ S
            (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)) k A μ ν = 0)
      ∧ 0 < vacuumLiouvilleComplexity (centralChargeN4 N) ε :=
  ⟨(boundaryCentralCharge_electrograviticResidual_vanishing
      Ric scalarR g gInv Λ S k A R N V c hN hV hc).2,
   vacuumLiouvilleComplexity_pos (centralChargeN4 N) ε (centralChargeN4_pos N hN) hε hε1⟩

/-- **Complexity × residual coupling is central-charge independent.**  The Liouville vacuum
complexity is proportional to the central charge and the electrogravitic residual coupling is
inversely proportional to it, so their product drops the `N²/4` entirely, leaving the fixed
geometric datum `(π²R³/6Vc⁴)(1/ε − 1)`. -/
@[zil_level bridge_theorem]
theorem liouvilleComplexity_times_residualCoupling_centralChargeInvariant
    (R V c N ε : ℝ) (hN : N ≠ 0) (hV : V ≠ 0) (hc : c ≠ 0) (hε : ε ≠ 0) :
    vacuumLiouvilleComplexity (centralChargeN4 N) ε
        * boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)
      = Real.pi ^ 2 * R ^ 3 / (6 * V * c ^ 4) * (1 / ε - 1) := by
  have hcB : centralChargeN4 N ≠ 0 := (centralChargeN4_pos N hN).ne'
  unfold vacuumLiouvilleComplexity boundaryCentralChargeEinsteinCoupling
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual

zil attach boundaryCentralCharge_governs_residual_and_liouvilleComplexity where
  formalizes @ "claim:at-the-boundary-cft-central-charge-the-electrogravitic-residual-vanishes-iff-stationarity-and-the-same-central-charge-sets-a-positive-liouville-path-integral-complexity-one-boundary-quantity-governing-both-the-gravitational-residual-and-the-cft-complexity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual.boundaryCentralCharge_electrograviticResidual_vanishing"

zil attach liouvilleComplexity_times_residualCoupling_centralChargeInvariant where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.centralChargeN4_pos",
  formalizes @ "claim:the-product-of-the-liouville-path-integral-complexity-and-the-electrogravitic-residual-coupling-is-independent-of-the-boundary-central-charge-since-the-complexity-grows-with-c-and-the-coupling-shrinks-as-one-over-c"

zil_file_contract physlib.liouvilleComplexityElectrograviticResidual where
  promises "Tying the electrogravitic-residual boundary-central-charge bridge to the Caputa-Takayanagi Liouville path-integral complexity through their shared object, the boundary CFT central charge N squared over four. At that central charge the electrogravitic residual, whose real part is the Einstein-Maxwell residual and imaginary part is the entropic-Einstein residual, vanishes iff the metric is stationary, and the same central charge sets a positive vacuum path-integral complexity. The product of the Liouville complexity and the residual coupling is independent of the boundary central charge: the complexity is proportional to the central charge, the residual coupling inversely proportional, so the central charge cancels leaving the fixed geometric datum pi squared R cubed over six V c to the fourth times one over epsilon minus one."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleComplexityHolographicSpine.vacuumLiouvilleComplexity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.boundaryCentralChargeEinsteinCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.centralChargeN4"
  ]
  forbids_substitutes [
    "conflating the AdS3 Brown-Henneaux central charge with the AdS5 D3 boundary central charge - both are used only as an abstract boundary central charge parameter",
    "reading the shared-central-charge bundle as a derivation of AdS/CFT rather than a coupling and normalization dictionary"
  ]
  witnessed_by [
    boundaryCentralCharge_governs_residual_and_liouvilleComplexity,
    liouvilleComplexity_times_residualCoupling_centralChargeInvariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.liouvilleComplexityElectrograviticResidual

