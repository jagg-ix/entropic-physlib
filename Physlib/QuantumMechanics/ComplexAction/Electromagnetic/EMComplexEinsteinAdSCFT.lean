/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification
public import Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy
meta import Zil

/-!
# The complex-Einstein/Dirac superoperator and AdS/CFT (Ryu–Takayanagi)

Links the complex-Hamiltonian split of `PTSymmetricQFT.LindbladSuperoperator` —
`𝓛_{H_R − iH_I} = −i[H_R, ·] − [H_I, ·]` (reversible + entropic) — to the **AdS/CFT modular flow**
and the **Ryu–Takayanagi entanglement entropy**. This closes the loop of the arc: the abstract field
adjoint → the GKSL open-system generator → the AdS/CFT causal-diamond modular flow → the RT area law.

The connection is one identification: the reversible part `−i[H_R, ·]` of the combined complex Liouvillian,
with `H_R = K = −log ρ_A` the **modular Hamiltonian**, is exactly the Tomita–Takesaki **modular flow**
`modularGenerator K = −i[K, ·]` of `PTSymmetricQFT.ModularFlowBoundedOp`. The entropic part `−[H_I, ·]` is the
imaginary Einstein `Λ` / imaginary Dirac mass. And the modular
Hamiltonian's expectation `⟨K⟩ = S_A = Area/4G` is the Ryu–Takayanagi entropy (`rtAreaEntropy`), a
time-reversal (modular) invariant.

* **§A — the modular flow is the reversible part** (`complexLiouvillian_eq_modular_plus_entropic`,
  `combined_reversible_is_modular`). `𝓛_{K − iH_I} = modularGenerator K − [H_I, ·]`: the combined
  superoperator splits into the AdS/CFT modular flow (reversible) and the entropic `Λ`; at `H_I = 0` it is
  the pure modular flow.
* **§B — the RT entropy is a nonnegative modular invariant** (`rt_modular_entropy_invariant_nonneg`). The
  modular-flow horizon RT entropy `S_A = rtAreaEntropy(W², G)` is time-reversal invariant
  (`areaEntropy_timeReversal_normSq_identity`) and nonnegative (`rtAreaEntropy_nonneg`) — the modular Hamiltonian's
  expectation `⟨K⟩`, the horizon area, and the entanglement entropy are one invariant.
* **§C — the independently supplied holographic coupling fixes the boundary data**
  (`comptonCell_brownHenneaux_rt_dictionary`,
  `comptonCell_entropicCFunction_rt_dictionary`).  The Compton-cell construction supplies
  `G = ℏc σ₀⁴` without using a bit count that already contains `G`; substituting that result into
  Brown–Henneaux and Ryu–Takayanagi fixes both the boundary central charge and the entropy coefficient.
  The parity-symmetric entropic c-function is exactly the same `c/3 = R/(2G)` coefficient.
* **§D — the same coupling normalizes the GKP–Witten response**
  (`comptonCell_gkpWitten_source_hessian`).  The second source response of the gravitationally
  normalized finite GKP–Witten carrier is the propagator quadratic multiplied by
  `1/(ℏc σ₀⁴)`.
* **§E — D3 compactification reaches the full Complex Einstein equations**
  (`d3_inferenceEinsteinCoupling_dictionary`,
  `d3_centralCharge_complexEinsteinCoupling`,
  `d3_complexEinstein_conservation_reversibleFamily`).  The explicit reduction
  `G₅=VG₄` and D3 result `G₅=πR³/(2N²)` turn the four-dimensional coupling into
  `κ₄=4π²R³/(N²Vc⁴)`.  Its product with the boundary central charge is
  `π²R³/(Vc⁴)`, and the existing rapidity-dependent Complex Einstein family,
  complex Bianchi identity, conservation laws, and reversible limit all hold
  with that AdS/CFT-normalized coupling.
* **§F — RT and GKP observables use the same field-equation normalization**
  (`d3_rtEntropy_complexEinsteinCoupling`,
  `d3_gkpWittenHessian_complexEinsteinCoupling`,
  `d3_boundaryCentralCharge_complexEinstein_equilibrium`).  The products
  `κ₄S_RT=2πA/c⁴` and `1/G₄=8π/(κ₄c⁴)` connect the entropy and source-response
  normalizations directly to the Complex Einstein coupling.  Finally
  `κ₄=π²R³/(Vc⁴c_CFT)` inserts the boundary central charge directly into the
  equilibrium complex/real Einstein correspondence.
* **§G — boundary central charge controls observables and full dynamics**
  (`d3_rtEntropy_boundaryCentralCharge`,
  `d3_gkpWittenHessian_boundaryCentralCharge`,
  `d3_boundaryCentralCharge_complexEinstein_conservationFamily`).  Both RT
  entropy and the GKP source Hessian are expressed directly through
  `c_CFT=N²/4`, and the complete rapidity-dependent Complex Einstein system is
  transported to the same boundary-central-charge coupling.
* **§H — light-front AdS/QCD joins the independent geometry spine**
  (`lightFrontAdSQCD_electroCartan_bianchiDoubleCopy_spine`).  The
  de Téramond--Brodsky soft-wall potential, scalar BF stability and Regge
  spacings are carried beside the projective Einstein--Cartan gauge theorem and
  the existing Einstein--Maxwell/BCJ first-and-second-Bianchi conservation
  chain, without attributing those independent gravity results to that paper.
* **§I — the D3-normalized AdS double copy**
  (`d3_adsCFT_BCJ_doubleCopy`).  The same coupling fixed by D3
  compactification and the boundary central charge normalizes the finite
  cubic-graph BCJ double-copy amplitude.  At that coupling, the
  Einstein--Maxwell Bianchi carrier derives stress-energy conservation from
  the gravitational second Bianchi identity.  The theorem composes the
  amplitude and field-equation faces without claiming that either alone
  proves the AdS/CFT correspondence.

So the combined Lorentz–EM superoperator's reversible part *is* the AdS/CFT modular flow, its entropic part
*is* the imaginary Einstein `Λ`, and the modular Hamiltonian whose flow it generates has expectation equal
to the Ryu–Takayanagi entanglement entropy.

## References

* S. Ryu, T. Takayanagi, *Holographic Derivation of Entanglement Entropy from AdS/CFT*, Phys. Rev. Lett. 96
  (2006) 181602 (`S_A = Area/4G`); Tomita–Takesaki modular theory (`σ_t(a) = Δ^{it} a Δ^{−it}`, generator
  `−i[K, ·]`).
* Repo carriers: `PTSymmetricQFT.LindbladSuperoperator` (`heisenbergGenerator_complex_decompose`);
  `PTSymmetricQFT.ModularFlowBoundedOp` (`modularGenerator`); `AdSCFT.RyuTakayanagiFormulaAlgebra`
  (`rtAreaEntropy`, `brownHenneaux`); `AdSCFT.GKPWittenAdSCFTDictionary`
  (`gkpWittenAffineSourceResponse`); `ComptonClock.ComptonCellNewtonConstant`
  (`newtonG_from_positionVariance`); `EntropicCTheorem` (`entropicCentralCharge_fixedPoint`).
  `AdSCFT.D3BraneHolographicSpectrum` (`d3_newton_from_string_compactification`,
  `comptonCell_d3_compactification_dictionary`); `ComptonClock.ReversibleLimitConvergence`
  (`gFree_complexEinstein_conservationFamily`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification
open Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QFT.ScalarGreenFunctions
open Physlib.Thermodynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- **[Combined = modular flow + entropic] `𝓛_{K − iH_I} = modularGenerator K − [H_I, ·]`.** With the real
energy taken to be the modular Hamiltonian `K = −log ρ_A`, the combined complex Liouvillian splits into the
Tomita–Takesaki **modular flow** `modularGenerator K = −i[K, ·]` (the reversible AdS/CFT flow) and the
**entropic** part `−[H_I, ·]` (the imaginary Einstein `Λ` / imaginary Dirac mass). -/
@[zil_level bridge_theorem]
lemma complexLiouvillian_eq_modular_plus_entropic (K H_I a : H →L[ℂ] H) :
    heisenbergGenerator (K - Complex.I • H_I) a = modularGenerator K a - (H_I * a - a * H_I) := by
  rw [modularGenerator, heisenbergGenerator_complex_decompose, heisenbergGenerator_apply]

omit [CompleteSpace H] in
/-- **[Reversible limit] At `H_I = 0` the combined superoperator is the pure modular flow.** No entropic
part: the combined complex Liouvillian reduces to the AdS/CFT modular generator `modularGenerator K`. -/
lemma combined_reversible_is_modular (K a : H →L[ℂ] H) :
    heisenbergGenerator (K - Complex.I • 0) a = modularGenerator K a := by
  rw [smul_zero, sub_zero, modularGenerator]


/-- **[RT = nonneg modular invariant] `S_A = rtAreaEntropy(W², G)`.** The modular-flow horizon Ryu–Takayanagi
entropy — the modular Hamiltonian's expectation `⟨K⟩` and the horizon area / `4G` — is **time-reversal
(modular) invariant** (`areaEntropy_timeReversal_normSq_identity`) and **nonnegative** (`rtAreaEntropy_nonneg`,
`G > 0`). The minimal surface area, the modular Hamiltonian expectation, and the entanglement entropy are one
invariant. -/
@[zil_level bridge_theorem]
lemma rt_modular_entropy_invariant_nonneg (W θ G : ℝ) (hG : 0 < G) :
    rtAreaEntropy (Complex.normSq (conjFactor true (adSComplexCoord W θ))) G
        = rtAreaEntropy (W ^ 2) G
      ∧ 0 ≤ rtAreaEntropy (W ^ 2) G :=
  ⟨areaEntropy_timeReversal_normSq_identity W θ G, rtAreaEntropy_nonneg (W ^ 2) G (sq_nonneg W) hG⟩

/-! ## §C — the Compton-cell coupling fixes Brown–Henneaux, RT, and the entropic c-function -/

/-- **[The independently supplied `G` fixes the AdS₃/CFT₂ central charge and RT coefficient].**
Let `Gscreen` be the area-per-Compton-cell coupling extracted from the entanglement screen rather
than a Planck-cell count.  The existing `newtonG_from_positionVariance` theorem proves
`Gscreen = ℏc σ₀⁴`.  Consequently

* `c_BH = 3R/(2ℏc σ₀⁴)`;
* `S_RT = area/(4ℏc σ₀⁴)`; and
* `S_RT = c_BH·area/(6R)`.

Thus the same noncircular coupling that reaches the Newton/Einstein hierarchy also fixes the
standard holographic boundary normalization. -/
@[zil_level bridge_theorem]
lemma comptonCell_brownHenneaux_rt_dictionary
    (area R σ₀ c ħ η : ℝ) (hR : R ≠ 0) (hσ : σ₀ ≠ 0)
    (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    let m := inferenceMass σ₀
    let Gscreen :=
      sphereArea (entropicProperDistance m c ħ η) * c ^ 3 /
        (ħ * comptonCellBits m c ħ η)
    brownHenneaux R Gscreen = 3 * R / (2 * (ħ * c * σ₀ ^ 4))
      ∧ rtAreaEntropy area Gscreen = area / (4 * (ħ * c * σ₀ ^ 4))
      ∧ rtAreaEntropy area Gscreen =
        brownHenneaux R Gscreen * area / (6 * R) := by
  dsimp only
  rw [newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK]
  constructor
  · rfl
  constructor
  · rfl
  · unfold rtAreaEntropy brownHenneaux
    field_simp
    ring

/-- **[The entropic c-function coefficient is the Brown–Henneaux/RT coefficient].**
For a parity-symmetric boundary CFT (`c̄ = c`), the fixed-point logarithmic-entropy slope is
`(c+c̄)/6 = c/3`.  With the Compton-cell coupling this is exactly
`R/(2ℏc σ₀⁴)`, and multiplying that slope by `area/(2R)` gives the RT entropy.
This identifies the repository's entropic RG c-function with the same normalization that controls
the bulk minimal-area law. -/
@[zil_level bridge_theorem]
lemma comptonCell_entropicCFunction_rt_dictionary
    (area R β a σ₀ c ħ η : ℝ) (hR : R ≠ 0) (hσ : σ₀ ≠ 0)
    (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    let m := inferenceMass σ₀
    let Gscreen :=
      sphereArea (entropicProperDistance m c ħ η) * c ^ 3 /
        (ħ * comptonCellBits m c ħ η)
    entropicCentralCharge
        (cftLogLengthEntropy (brownHenneaux R Gscreen / 3) β) a =
        R / (2 * (ħ * c * σ₀ ^ 4))
      ∧ rtAreaEntropy area Gscreen =
        entropicCentralCharge
          (cftLogLengthEntropy (brownHenneaux R Gscreen / 3) β) a *
            area / (2 * R) := by
  dsimp only
  rw [newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK]
  have hG : ħ * c * σ₀ ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hħ hc) (pow_ne_zero 4 hσ)
  constructor
  · rw [entropicCentralCharge_fixedPoint, brownHenneaux_third _ _ hG]
  · rw [entropicCentralCharge_fixedPoint, brownHenneaux_third _ _ hG]
    unfold rtAreaEntropy
    field_simp
    ring

/-- **[The modular RT invariant at the independently supplied coupling].**
The complex AdS coordinate norm remains time-reversal invariant after the Newton coupling is
eliminated in favor of the inference variance, and its RT entropy is explicitly
`W²/(4ℏc σ₀⁴)`.  Positivity follows from positive physical constants and does not require a new
entropy postulate. -/
@[zil_level bridge_theorem]
lemma comptonCell_rt_modular_entropy_dictionary
    (W θ σ₀ c ħ η : ℝ) (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    let m := inferenceMass σ₀
    let Gscreen :=
      sphereArea (entropicProperDistance m c ħ η) * c ^ 3 /
        (ħ * comptonCellBits m c ħ η)
    rtAreaEntropy (Complex.normSq (conjFactor true (adSComplexCoord W θ))) Gscreen =
        rtAreaEntropy (W ^ 2) Gscreen
      ∧ rtAreaEntropy (W ^ 2) Gscreen = W ^ 2 / (4 * (ħ * c * σ₀ ^ 4))
      ∧ 0 ≤ rtAreaEntropy (W ^ 2) Gscreen := by
  dsimp only
  rw [newtonG_from_positionVariance σ₀ c ħ η hσ.ne' hc.ne' hħ.ne' hK]
  have hG : 0 < ħ * c * σ₀ ^ 4 := by positivity
  exact ⟨areaEntropy_timeReversal_normSq_identity W θ (ħ * c * σ₀ ^ 4),
    rfl, rtAreaEntropy_nonneg (W ^ 2) (ħ * c * σ₀ ^ 4) (sq_nonneg W) hG⟩

/-! ## §D — gravitational normalization of the GKP–Witten source response -/

/-- The finite GKP–Witten affine source response with the classical bulk gravitational
prefactor `1/G`.  It reuses the existing regularized response rather than defining another
propagator or source functional. -/
noncomputable def gravitationallyNormalizedGKPResponse {n : ℕ}
    (G : ℝ) (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) : ℂ :=
  ((G : ℂ)⁻¹) * gkpWittenAffineSourceResponse Delta J H t

/-- Differentiating the gravitationally normalized response returns the propagator quadratic
with the same `1/G` normalization. -/
lemma gravitationallyNormalizedGKPResponse_hasDerivAt {n : ℕ}
    (G : ℝ) (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) :
    HasDerivAt (gravitationallyNormalizedGKPResponse G Delta J H)
      (((G : ℂ)⁻¹) * realSourceQuadratic Delta H) t := by
  change HasDerivAt
    (fun y => ((G : ℂ)⁻¹) * gkpWittenAffineSourceResponse Delta J H y)
    (((G : ℂ)⁻¹) * realSourceQuadratic Delta H) t
  exact
    (gkpWittenAffineSourceResponse_hasDerivAt Delta J H t).const_mul ((G : ℂ)⁻¹)

/-- **[The Compton-cell coupling fixes the GKP–Witten two-point response].**
After replacing the classical bulk Newton coupling by the independently supplied screen value
`Gscreen = ℏc σ₀⁴`, the second source response is exactly the finite propagator quadratic
multiplied by `1/(ℏc σ₀⁴)`.  This is the source-response counterpart of the Brown–Henneaux and RT
normalizations above. -/
@[zil_level bridge_theorem]
lemma comptonCell_gkpWitten_source_hessian {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J H : Fin n → ℂ)
    (σ₀ c ħ η : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0) :
    let m := inferenceMass σ₀
    let Gscreen :=
      sphereArea (entropicProperDistance m c ħ η) * c ^ 3 /
        (ħ * comptonCellBits m c ħ η)
    HasDerivAt
      (gravitationallyNormalizedGKPResponse Gscreen Delta J H)
      ((((ħ * c * σ₀ ^ 4 : ℝ) : ℂ)⁻¹) * realSourceQuadratic Delta H) 0 := by
  dsimp only
  rw [newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK]
  exact gravitationallyNormalizedGKPResponse_hasDerivAt
    (ħ * c * σ₀ ^ 4) Delta J H 0

/-! ## §E — D3 compactification fixes the Complex Einstein coupling -/

/-- The four-dimensional Einstein coupling written entirely in terms of the
D3 radius `R`, color rank `N`, explicit reduction factor `V`, and light speed
`c`.  It is the compactification image of `κ₄ = 8πG₄/c⁴` when
`G₅ = V G₄` and `G₅ = πR³/(2N²)`. -/
noncomputable def d3ReducedEinsteinCoupling (R N V c : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * R ^ 3 / (N ^ 2 * V * c ^ 4)

/-- The same four-dimensional Einstein coupling parametrized by a boundary
central charge rather than the color rank. -/
noncomputable def boundaryCentralChargeEinsteinCoupling
    (R V c cBoundary : ℝ) : ℝ :=
  (Real.pi ^ 2 * R ^ 3 / (V * c ^ 4)) / cBoundary

/-- The D3-reduced bulk coupling and the boundary-central-charge coupling are
the same normalization:

`4π²R³/(N²Vc⁴) = (π²R³/(Vc⁴))/(N²/4)`.

This is the algebraic AdS/CFT coupling dictionary used by the double-copy
theorem below. -/
@[zil_level bridge_theorem]
lemma d3ReducedEinsteinCoupling_eq_boundaryCentralCharge
    (R N V c : ℝ) (hN : N ≠ 0) (hV : V ≠ 0) (hc : c ≠ 0) :
    d3ReducedEinsteinCoupling R N V c =
      boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N) := by
  unfold d3ReducedEinsteinCoupling
    boundaryCentralChargeEinsteinCoupling centralChargeN4
  field_simp [hN, hV, hc]

/-- **[D3 compactification fixes the Complex Einstein coupling].**
The independently supplied Compton-cell coupling and the D3 reduction imply

`κ₄(σ₀) = 8πℏσ₀⁴/c³ = 4π²R³/(N²Vc⁴)`.

The extra-dimensional factor `V` remains explicit; no dimensionally invalid
identification of `G₄` with `G₅` is made. -/
@[zil_level bridge_theorem]
theorem d3_inferenceEinsteinCoupling_dictionary
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    inferenceEinsteinCoupling ħ c σ₀ =
      d3ReducedEinsteinCoupling R N V c := by
  have hK : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hreduce :=
    (comptonCell_d3_compactification_dictionary
      σ₀ c ħ η V R N G5 hσ.ne' hc.ne' hħ.ne' hK hR hN hG5 hcompact).1
  have hG4 :
      ħ * c * σ₀ ^ 4 =
        (Real.pi * R ^ 3 / (2 * N ^ 2)) / V := by
    apply (eq_div_iff hV).2
    simpa only [mul_comm] using hreduce
  rw [inferenceEinsteinCoupling_eq_newtonForm ħ c σ₀ hc.ne', hG4]
  unfold d3ReducedEinsteinCoupling
  field_simp [hV, hN, hc.ne']
  ring

/-- **[Boundary degrees of freedom normalize the Complex Einstein coupling].**
Multiplying the D3-reduced Einstein coupling by the boundary central charge
`c_CFT=N²/4` cancels the color rank:

`κ₄ c_CFT = π²R³/(Vc⁴)`.

This is an exact compactification/dictionary identity, not an independent
measurement of `N`, `R`, or the reduction factor. -/
@[zil_level bridge_theorem]
theorem d3_centralCharge_complexEinsteinCoupling
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    inferenceEinsteinCoupling ħ c σ₀ * centralChargeN4 N =
      Real.pi ^ 2 * R ^ 3 / (V * c ^ 4) := by
  rw [d3_inferenceEinsteinCoupling_dictionary
    σ₀ c ħ η V R N G5 hσ hc hħ hη hV hR hN hG5 hcompact]
  unfold d3ReducedEinsteinCoupling centralChargeN4
  field_simp [hV, hN, hc.ne']

/-- **[The AdS/CFT-normalized full Complex Einstein system].**
At the D3-reduced coupling, every rapidity slice satisfies the full complex
Einstein equation and complex Bianchi identity; both the real and entropic
sources are conserved.  The imaginary curvature converges to zero in the
reversible limit.

The real Einstein source equation, real Bianchi identity, and conservation of
the reference entropic stress remain explicit geometric premises.  AdS/CFT
fixes the coupling dictionary; it does not replace those dynamics. -/
@[zil_level bridge_theorem]
theorem d3_complexEinstein_conservation_reversibleFamily {ι : Type*}
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g T S₀ : Matrix ι ι ℝ)
    (σ₀ c ħ η₀ V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη₀ : 0 < η₀)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η₀) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η₀)))
    (hReal : einsteinFieldEquation Ric scalarR g T
      (inferenceEinsteinCoupling ħ c σ₀))
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hS₀ : Div S₀ = 0) :
    (∀ η : ℝ,
      complexEinsteinFieldEquation (einsteinTensor Ric scalarR g)
          (d3ReducedEinsteinCoupling R N V c • rapidityEntropicStress S₀ η)
          T (rapidityEntropicStress S₀ η) (d3ReducedEinsteinCoupling R N V c)
        ∧ complexDiv Div
            (complexEinsteinTensor (einsteinTensor Ric scalarR g)
              (d3ReducedEinsteinCoupling R N V c •
                rapidityEntropicStress S₀ η)) = 0
        ∧ Div T = 0
        ∧ Div (rapidityEntropicStress S₀ η) = 0)
      ∧ Filter.Tendsto
        (fun η : ℝ =>
          d3ReducedEinsteinCoupling R N V c • rapidityEntropicStress S₀ η)
        Filter.atTop (nhds 0) := by
  have hκ := d3_inferenceEinsteinCoupling_dictionary
    σ₀ c ħ η₀ V R N G5 hσ hc hħ hη₀ hV hR hN hG5 hcompact
  have hfamily :=
    gFree_complexEinstein_conservationFamily
      Div Ric scalarR g T S₀ c ħ σ₀ hσ hc hħ hReal hBianchi hS₀
  constructor
  · intro η
    simpa only [hκ] using hfamily η
  · simpa only [← hκ, smul_zero] using
      (tendsto_const_nhds.smul
        (rapidityEntropicStress_tendsto_zero S₀) :
          Filter.Tendsto
            (fun η : ℝ =>
              inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
            Filter.atTop
            (nhds (inferenceEinsteinCoupling ħ c σ₀ •
              (0 : Matrix ι ι ℝ))))

/-! ## §F — RT and GKP observables in Complex Einstein normalization -/

/-- **[RT entropy in Complex Einstein normalization].**
At the D3-reduced coupling,

`κ₄ S_RT(A,G₄) = 2πA/c⁴`.

The Newton coupling cancels between `κ₄=8πG₄/c⁴` and
`S_RT=A/(4G₄)`.  This is therefore a useful normalization check linking the
field equation to the holographic entropy, but not a new numerical prediction. -/
@[zil_level bridge_theorem]
theorem d3_rtEntropy_complexEinsteinCoupling
    (area σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    let Gscreen :=
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
        / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)
    d3ReducedEinsteinCoupling R N V c * rtAreaEntropy area Gscreen =
      2 * Real.pi * area / c ^ 4 := by
  dsimp only
  have hK : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hκ := d3_inferenceEinsteinCoupling_dictionary
    σ₀ c ħ η V R N G5 hσ hc hħ hη hV hR hN hG5 hcompact
  rw [newtonG_from_positionVariance σ₀ c ħ η
    hσ.ne' hc.ne' hħ.ne' hK, ← hκ,
    inferenceEinsteinCoupling_eq_newtonForm ħ c σ₀ hc.ne']
  unfold rtAreaEntropy
  field_simp [hσ.ne', hc.ne', hħ.ne']
  ring

/-- **[The GKP–Witten Hessian in Complex Einstein normalization].**
The gravitational source Hessian can be written without a separate `G₄`
parameter:

`1/G₄ = 8π/(κ₄c⁴)`.

Thus the same D3-reduced coupling that appears in the Complex Einstein equation
also fixes the normalization of the boundary two-point response. -/
@[zil_level bridge_theorem]
theorem d3_gkpWittenHessian_complexEinsteinCoupling {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J H : Fin n → ℂ)
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    let Gscreen :=
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
        / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)
    HasDerivAt
      (gravitationallyNormalizedGKPResponse Gscreen Delta J H)
      (((8 * Real.pi /
          (d3ReducedEinsteinCoupling R N V c * c ^ 4) : ℝ) : ℂ) *
        realSourceQuadratic Delta H) 0 := by
  dsimp only
  have hK : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  rw [newtonG_from_positionVariance σ₀ c ħ η
    hσ.ne' hc.ne' hħ.ne' hK]
  have hκ := d3_inferenceEinsteinCoupling_dictionary
    σ₀ c ħ η V R N G5 hσ hc hħ hη hV hR hN hG5 hcompact
  have hG4 : ħ * c * σ₀ ^ 4 ≠ 0 := by positivity
  have hcoef :
      (ħ * c * σ₀ ^ 4)⁻¹ =
        8 * Real.pi / (d3ReducedEinsteinCoupling R N V c * c ^ 4) := by
    rw [← hκ]
    unfold inferenceEinsteinCoupling
    field_simp [hG4, hc.ne', Real.pi_ne_zero]
  have hcoefC :
      (((ħ * c * σ₀ ^ 4 : ℝ) : ℂ)⁻¹) =
        ((8 * Real.pi /
          (d3ReducedEinsteinCoupling R N V c * c ^ 4) : ℝ) : ℂ) := by
    exact_mod_cast hcoef
  have hderiv :=
    comptonCell_gkpWitten_source_hessian
      Delta J H σ₀ c ħ η hσ.ne' hc.ne' hħ.ne' hK
  dsimp only at hderiv
  rw [newtonG_from_positionVariance σ₀ c ħ η
    hσ.ne' hc.ne' hħ.ne' hK] at hderiv
  simpa only [hcoefC] using hderiv

/-- **[Boundary central charge parametrizes the equilibrium Complex Einstein
equation].**  The D3 dictionary gives

`κ₄ = π²R³/(Vc⁴ c_CFT)`.

At vanishing entropic curvature and stress this boundary-normalized complex
equation is exactly the ordinary real Einstein equation. -/
@[zil_level bridge_theorem]
theorem d3_boundaryCentralCharge_complexEinstein_equilibrium {ι : Type*}
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    inferenceEinsteinCoupling ħ c σ₀ =
        boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)
      ∧ (complexEinsteinFieldEquation (einsteinTensor Ric scalarR g)
            0 T (entropicStressTensor 0 0 g)
            (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N))
          ↔ einsteinFieldEquation Ric scalarR g T
            (boundaryCentralChargeEinsteinCoupling R V c
              (centralChargeN4 N))) := by
  have hprod := d3_centralCharge_complexEinsteinCoupling
    σ₀ c ħ η V R N G5 hσ hc hħ hη hV hR hN hG5 hcompact
  have hcft : centralChargeN4 N ≠ 0 :=
    (centralChargeN4_pos N hN).ne'
  constructor
  · unfold boundaryCentralChargeEinsteinCoupling
    exact (eq_div_iff hcft).2 hprod
  · exact complexEinstein_equilibrium_reduces Ric scalarR g T
      (boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N))

/-! ## §G — boundary-central-charge observables and full dynamics -/

/-- **[RT entropy directly from the boundary central charge].**
The D3 compactification dictionary eliminates the bulk Newton coupling:

`S_RT(A) = 2 V c_CFT A / (πR³)`.

This is the boundary-central-charge form of the same area law; the
compactification factor remains explicit. -/
@[zil_level bridge_theorem]
theorem d3_rtEntropy_boundaryCentralCharge
    (area σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    let Gscreen :=
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
        / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)
    rtAreaEntropy area Gscreen =
      2 * V * centralChargeN4 N * area / (Real.pi * R ^ 3) := by
  dsimp only
  have hK : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hreduce :=
    (comptonCell_d3_compactification_dictionary
      σ₀ c ħ η V R N G5 hσ.ne' hc.ne' hħ.ne' hK hR hN hG5 hcompact).1
  have hG4 :
      ħ * c * σ₀ ^ 4 =
        (Real.pi * R ^ 3 / (2 * N ^ 2)) / V := by
    apply (eq_div_iff hV).2
    simpa only [mul_comm] using hreduce
  rw [newtonG_from_positionVariance σ₀ c ħ η
    hσ.ne' hc.ne' hħ.ne' hK, hG4]
  unfold rtAreaEntropy centralChargeN4
  field_simp [hV, hR, hN, Real.pi_ne_zero]

/-- **[GKP–Witten Hessian directly from the boundary central charge].**
The source-response coefficient becomes

`1/G₄ = 8 V c_CFT/(πR³)`.

The finite GKP–Witten Hessian is therefore normalized entirely by boundary
degrees of freedom and the explicit compactification geometry. -/
@[zil_level bridge_theorem]
theorem d3_gkpWittenHessian_boundaryCentralCharge {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J H : Fin n → ℂ)
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    let Gscreen :=
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
        / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)
    HasDerivAt
      (gravitationallyNormalizedGKPResponse Gscreen Delta J H)
      ((((8 * V * centralChargeN4 N /
          (Real.pi * R ^ 3) : ℝ) : ℂ) *
        realSourceQuadratic Delta H)) 0 := by
  have hderiv := d3_gkpWittenHessian_complexEinsteinCoupling
    Delta J H σ₀ c ħ η V R N G5
    hσ hc hħ hη hV hR hN hG5 hcompact
  have hcoef :
      8 * Real.pi / (d3ReducedEinsteinCoupling R N V c * c ^ 4) =
        8 * V * centralChargeN4 N / (Real.pi * R ^ 3) := by
    unfold d3ReducedEinsteinCoupling centralChargeN4
    field_simp [hV, hR, hN, hc.ne', Real.pi_ne_zero]
  simpa only [hcoef] using hderiv

/-- **[The full Complex Einstein system in boundary-CFT normalization].**
With

`κ₄ = π²R³/(Vc⁴c_CFT)`,

every rapidity slice satisfies the complex Einstein equation and complex
Bianchi identity, both sources are conserved, and the imaginary curvature
vanishes in the reversible limit.  The real Einstein equation and conservation
premises remain explicit. -/
@[zil_level bridge_theorem]
theorem d3_boundaryCentralCharge_complexEinstein_conservationFamily
    {ι : Type*}
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g T S₀ : Matrix ι ι ℝ)
    (σ₀ c ħ η₀ V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη₀ : 0 < η₀)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η₀) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η₀)))
    (hReal : einsteinFieldEquation Ric scalarR g T
      (inferenceEinsteinCoupling ħ c σ₀))
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hS₀ : Div S₀ = 0) :
    let κBoundary :=
      boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)
    (∀ η : ℝ,
      complexEinsteinFieldEquation (einsteinTensor Ric scalarR g)
          (κBoundary • rapidityEntropicStress S₀ η)
          T (rapidityEntropicStress S₀ η) κBoundary
        ∧ complexDiv Div
            (complexEinsteinTensor (einsteinTensor Ric scalarR g)
              (κBoundary • rapidityEntropicStress S₀ η)) = 0
        ∧ Div T = 0
        ∧ Div (rapidityEntropicStress S₀ η) = 0)
      ∧ Filter.Tendsto
        (fun η : ℝ => κBoundary • rapidityEntropicStress S₀ η)
        Filter.atTop (nhds 0) := by
  dsimp only
  have hκ :=
    (d3_boundaryCentralCharge_complexEinstein_equilibrium
      Ric scalarR g T σ₀ c ħ η₀ V R N G5
      hσ hc hħ hη₀ hV hR hN hG5 hcompact).1
  have hfamily :=
    gFree_complexEinstein_conservationFamily
      Div Ric scalarR g T S₀ c ħ σ₀ hσ hc hħ hReal hBianchi hS₀
  constructor
  · intro η
    simpa only [hκ] using hfamily η
  · simpa only [← hκ, smul_zero] using
      (tendsto_const_nhds.smul
      (rapidityEntropicStress_tendsto_zero S₀) :
          Filter.Tendsto
            (fun η : ℝ =>
              inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
            Filter.atTop
            (nhds (inferenceEinsteinCoupling ħ c σ₀ •
              (0 : Matrix ι ι ℝ))))

/-! ## H. Light-front AdS/QCD on the independent electrogravitic geometry spine -/

/-- **[Light-front AdS/QCD and the field-equation spine].** The three
de Téramond--Brodsky light-front results are carried together with the
repository's independent geometric sectors:

* quadratic-dilaton soft-wall potential;
* scalar BF stability and equal Regge mass-squared spacings;
* Einstein--Cartan/Palatini projective torsion is removed exactly by `U=0`;
* Einstein--Maxwell has both gauge Bianchi identities, while the gravitational
  contracted second Bianchi derives stress-energy conservation through the
  existing BCJ double-copy carrier.

The last two bullets are repository-level synthesis, not statements attributed
to arXiv:1206.4365v2.  Their dynamical hypotheses remain explicit. -/
@[zil_level bridge_theorem]
theorem lightFrontAdSQCD_electroCartan_bianchiDoubleCopy_spine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κLF ζ J n L orbitalCasimir : ℝ) (hζ : ζ ≠ 0)
    (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (hd : 2 ≤ Fintype.card ι)
    {Ric : Matrix ι ι ℝ} {scalarR : ℝ}
    {g Λ T S : Matrix ι ι ℝ} {κ m_R m_I c S₁ S₂ : ℝ}
    {k A : Fin 4 → ℝ}
    (H : ElectroGravitationalFieldEquation
      Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    lightFrontDilatonPotential (2 * κLF ^ 2 * ζ) (2 * κLF ^ 2) ζ J =
        lightFrontSoftWallPotential κLF ζ J
      ∧ ((-(4 / 2 : ℝ) ^ 2 ≤
            lightFrontAdSMassParameter 0 orbitalCasimir) ↔
          0 ≤ orbitalCasimir)
      ∧ (lightFrontMassSpectrumSq κLF (n + 1) J L -
            lightFrontMassSpectrumSq κLF n J L = 4 * κLF ^ 2
        ∧ lightFrontMassSpectrumSq κLF n (J + 2) L -
            lightFrontMassSpectrumSq κLF n J L = 4 * κLF ^ 2
        ∧ lightFrontMassSpectrumSq κLF n J (L + 2) -
            lightFrontMassSpectrumSq κLF n J L = 4 * κLF ^ 2)
      ∧ (IsTorsionFree
            (entropicConnection Γ (projectiveConnection U)) ↔
          ∀ a, U a = 0)
      ∧ (k lam * faraday k A μ ν + k μ * faraday k A ν lam +
            k ν * faraday k A lam μ = 0)
      ∧ (∑ a, k a * fourCurrent k A a = 0)
      ∧ divT = 0 := by
  refine ⟨lightFrontDilatonPotential_quadratic κLF ζ J hζ,
    lightFront_scalar_bf_iff_orbitalCasimir_nonneg orbitalCasimir,
    lightFrontMassSpectrumSq_reggeSpacings κLF n J L,
    entropicConnection_projective_isTorsionFree_iff Γ U hΓ hd, ?_⟩
  exact electrogravitational_bianchi_double_copy
    H lam μ ν divG divT hEinstein hSecondBianchi

/-! ## I. The D3-normalized AdS double copy -/

/-- **[AdS/CFT-normalized BCJ double copy].**  At the coupling fixed by D3
compactification,

`κAdS = 4π²R³/(N²Vc⁴) = (π²R³/(Vc⁴))/cCFT`, with `cCFT=N²/4`,

the finite cubic-graph gravity amplitude is exactly the corresponding
Yang--Mills cubic amplitude after the BCJ color replacement
`Cγ ↦ Ñγ`.  For an Einstein--Maxwell solution normalized by this same
`κAdS`, the Maxwell/Faraday kinematic Jacobi and current conservation hold,
and the gravitational second Bianchi identity derives
stress-energy conservation.

The theorem therefore joins three independently proved faces at one
normalization:

1. the D3/AdS bulk--boundary coupling dictionary;
2. the finite BCJ amplitude double copy; and
3. the gauge/gravity Bianchi-conservation double copy.

It does not assert that the algebraic color replacement alone constructs an
AdS solution; the compactification and Einstein--Maxwell solution hypotheses
remain explicit. -/
@[zil_level bridge_theorem]
theorem d3_adsCFT_BCJ_doubleCopy
    {Γ ι : Type*} [Fintype Γ]
    (order : ℕ)
    (numerator numeratorTilde denominator : Γ → ℝ)
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η)
    (hV : V ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)))
    {Ric : Matrix ι ι ℝ} {scalarR : ℝ}
    {g Λ Tstress S : Matrix ι ι ℝ} {m_R m_I S₁ S₂ : ℝ}
    {k A : Fin 4 → ℝ}
    (H : ElectroGravitationalFieldEquation
      Ric scalarR g Λ Tstress S
      (d3ReducedEinsteinCoupling R N V c) m_R m_I c S₁ S₂ k A)
    (lam μ ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein :
      divG = d3ReducedEinsteinCoupling R N V c • divT)
    (hSecondBianchi : divG = 0) :
    let κAdS := d3ReducedEinsteinCoupling R N V c
    inferenceEinsteinCoupling ħ c σ₀ = κAdS
      ∧ κAdS =
        boundaryCentralChargeEinsteinCoupling R V c (centralChargeN4 N)
      ∧ cubicDoubleCopyAmplitudeFinite κAdS order
          numerator numeratorTilde denominator =
        cubicGraphAmplitude (κAdS / 2) order
          { color := numeratorTilde
            numerator := numerator
            denominator := denominator }
      ∧ (k lam * faraday k A μ ν + k μ * faraday k A ν lam +
            k ν * faraday k A lam μ = 0)
      ∧ (∑ a, k a * fourCurrent k A a = 0)
      ∧ divT = 0 := by
  dsimp only
  refine ⟨d3_inferenceEinsteinCoupling_dictionary
      σ₀ c ħ η V R N G5 hσ hc hħ hη hV hR hN hG5 hcompact,
    d3ReducedEinsteinCoupling_eq_boundaryCentralCharge
      R N V c hN hV hc.ne',
    cubicDoubleCopy_eq_cubicAmplitude_colorReplacement
      (d3ReducedEinsteinCoupling R N V c) order
        numerator numeratorTilde denominator, ?_⟩
  exact electrogravitational_bianchi_double_copy
    H lam μ ν divG divT hEinstein hSecondBianchi

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.complexLiouvillian_eq_modular_plus_entropic where
  formalizes @ "claim:the-complex-liouvillian-with-real-modular-hamiltonian-splits-exactly-into-tomita-modular-flow-and-the-entropic-commutator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.heisenbergGenerator_complex_decompose",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp.modularGenerator",
  caveat @ "epistemic:an-exact-operator-identity-after-identifying-the-real-hamiltonian-with-the-modular-hamiltonian-not-a-derivation-of-that-physical-identification"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.rt_modular_entropy_invariant_nonneg where
  formalizes @ "claim:the-rt-entropy-of-the-existing-complex-ads-norm-is-time-reversal-invariant-and-nonnegative-at-positive-newton-coupling",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.areaEntropy_timeReversal_normSq_identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy_nonneg",
  caveat @ "epistemic:proves-invariance-and-positivity-on-the-existing-coordinate-carrier-not-global-extremality-or-the-ads-cft-correspondence"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_brownHenneaux_rt_dictionary where
  formalizes @ "claim:the-g-free-compton-cell-newton-coupling-fixes-both-the-brown-henneaux-boundary-central-charge-and-the-ryu-takayanagi-area-normalization",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "paper:ryu-takayanagi-2006-holographic-entanglement-entropy",
  caveat @ "epistemic:exact-propagation-of-the-independent-screen-coupling-into-standard-ads3-cft2-normalizations-not-an-independent-measurement-of-sigma0-or-a-derivation-of-ads-cft"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_entropicCFunction_rt_dictionary where
  formalizes @ "claim:the-parity-symmetric-entropic-c-function-slope-is-the-brown-henneaux-c-over-three-coefficient-and-reconstructs-the-rt-area-entropy-at-the-compton-cell-coupling",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-g-free-compton-cell-newton-coupling-fixes-both-the-brown-henneaux-boundary-central-charge-and-the-ryu-takayanagi-area-normalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem.entropicCentralCharge_fixedPoint",
  caveat @ "epistemic:fixed-point-parity-symmetric-cft-identification-not-a-construction-of-an-rg-flow-or-proof-of-bulk-boundary-duality"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_rt_modular_entropy_dictionary where
  formalizes @ "claim:the-time-reversal-invariant-modular-ads-norm-has-rt-entropy-w-squared-over-four-hbar-c-sigma0-to-the-fourth-at-the-independent-compton-cell-coupling",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-g-free-compton-cell-newton-coupling-fixes-both-the-brown-henneaux-boundary-central-charge-and-the-ryu-takayanagi-area-normalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.areaEntropy_timeReversal_normSq_identity",
  caveat @ "epistemic:an-exact-modular-invariance-and-positivity-statement-on-the-existing-complex-ads-coordinate-carrier-not-a-proof-that-the-carrier-is-a-global-extremal-surface"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_gkpWitten_source_hessian where
  formalizes @ "claim:the-second-gkp-witten-source-response-is-the-propagator-quadratic-normalized-by-one-over-hbar-c-sigma0-to-the-fourth-when-the-bulk-newton-coupling-is-supplied-by-compton-cells",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWitten_affine_source_hessian",
  supported_by @ "paper:gubser-klebanov-polyakov-1998-witten-1998-generating-functional-prescription",
  caveat @ "epistemic:finite-regularized-free-source-hessian-with-the-classical-one-over-g-prefactor-not-an-interacting-continuum-bulk-path-integral-or-holographic-renormalization"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary where
  formalizes @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_newtonForm",
  caveat @ "epistemic:the-d3-string-relations-compton-cell-identification-and-compactification-factor-v-are-explicit-premises-not-derived-dynamical-consequences",
  caveat @ "scope:keeps-g4-and-g5-dimensionally-distinct-and-does-not-fit-r-n-v-or-sigma0-to-observation"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_centralCharge_complexEinsteinCoupling where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_newton_from_string_compactification",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  formalizes @ "claim:the-d3-reduced-complex-einstein-coupling-times-the-boundary-n-equals-four-central-charge-is-pi-squared-r-cubed-over-v-c-fourth",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_bulkCentralCharge_eq_boundary",
  caveat @ "epistemic:the-color-rank-cancellation-is-an-exact-dictionary-identity-not-an-independent-numerical-prediction-or-test-of-ads-cft"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_complexEinstein_conservation_reversibleFamily where
  formalizes @ "claim:the-d3-normalized-coupling-carries-the-full-rapidity-complex-einstein-equation-complex-bianchi-both-source-conservation-laws-and-reversible-vanishing-of-imaginary-curvature",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityEntropicStress_tendsto_zero",
  caveat @ "epistemic:the-real-einstein-source-equation-real-bianchi-identity-and-reference-entropic-stress-conservation-remain-explicit-geometric-dynamical-premises",
  caveat @ "scope:ads-cft-fixes-the-coupling-dictionary-but-does-not-by-itself-construct-a-global-bulk-solution-prove-ads-cft-or-derive-the-real-einstein-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_rtEntropy_complexEinsteinCoupling where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  formalizes @ "claim:the-d3-normalized-complex-einstein-coupling-times-ryu-takayanagi-entropy-is-two-pi-times-area-over-c-fourth",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy",
  caveat @ "epistemic:newton-coupling-cancels-between-kappa-equals-eight-pi-g-over-c-fourth-and-s-rt-equals-area-over-four-g-so-this-is-a-normalization-check-not-an-independent-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_gkpWittenHessian_complexEinsteinCoupling where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_gkpWitten_source_hessian",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  formalizes @ "claim:the-d3-normalized-complex-einstein-coupling-rewrites-the-gkp-witten-source-hessian-prefactor-one-over-g4-as-eight-pi-over-kappa4-c-fourth",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_gkpWitten_source_hessian",
  caveat @ "epistemic:an-exact-normalization-translation-for-the-existing-finite-free-source-response-not-an-interacting-continuum-witten-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_boundaryCentralCharge_complexEinstein_equilibrium where
  formalizes @ "claim:the-boundary-central-charge-parametrizes-kappa4-as-pi-squared-r-cubed-over-v-c-fourth-c-cft-and-the-equilibrium-complex-einstein-equation-is-exactly-the-real-equation-at-that-coupling",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-d3-reduced-complex-einstein-coupling-times-the-boundary-n-equals-four-central-charge-is-pi-squared-r-cubed-over-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinstein_equilibrium_reduces",
  caveat @ "epistemic:the-boundary-parametrization-inherits-the-d3-compton-cell-and-compactification-premises-and-does-not-derive-the-real-einstein-source-equation",
  caveat @ "scope:equilibrium-means-vanishing-entropic-curvature-and-stress-and-does-not-claim-a-global-ads-bulk-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_rtEntropy_boundaryCentralCharge where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_newton_from_string_compactification",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCell_inference_entropic_gravity_system",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  formalizes @ "claim:the-d3-compactified-rt-entropy-is-two-v-times-the-boundary-central-charge-times-area-over-pi-r-cubed",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-d3-reduced-complex-einstein-coupling-times-the-boundary-n-equals-four-central-charge-is-pi-squared-r-cubed-over-v-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  caveat @ "epistemic:an-exact-reexpression-of-the-rt-area-law-and-d3-compactification-dictionary-not-an-independent-boundary-state-count-or-extremal-surface-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_gkpWittenHessian_boundaryCentralCharge where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_gkpWitten_source_hessian",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary",
  formalizes @ "claim:the-d3-compactified-gkp-witten-source-hessian-has-prefactor-eight-v-times-the-boundary-central-charge-over-pi-r-cubed",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-d3-normalized-complex-einstein-coupling-rewrites-the-gkp-witten-source-hessian-prefactor-one-over-g4-as-eight-pi-over-kappa4-c-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_gkpWittenHessian_complexEinsteinCoupling",
  caveat @ "epistemic:a-boundary-normalization-identity-for-the-existing-finite-free-hessian-not-a-construction-of-an-interacting-continuum-generating-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_boundaryCentralCharge_complexEinstein_conservationFamily where
  formalizes @ "claim:the-boundary-central-charge-normalized-coupling-carries-the-full-rapidity-complex-einstein-equation-complex-bianchi-both-conservation-laws-and-reversible-limit",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-boundary-central-charge-parametrizes-kappa4-as-pi-squared-r-cubed-over-v-c-fourth-c-cft-and-the-equilibrium-complex-einstein-equation-is-exactly-the-real-equation-at-that-coupling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily",
  caveat @ "epistemic:inherits-the-d3-compton-cell-compactification-real-einstein-bianchi-and-source-conservation-premises",
  caveat @ "scope:promotes-the-coupling-parametrization-to-the-full-complex-system-but-does-not-prove-ads-cft-global-bulk-existence-or-the-real-einstein-source-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.lightFrontAdSQCD_electroCartan_bianchiDoubleCopy_spine where
  formalizes @ "claim:the-light-front-soft-wall-potential-bf-stability-and-regge-spectrum-share-an-explicit-integration-spine-with-projective-einstein-cartan-torsion-fixing-and-the-einstein-maxwell-bcj-first-and-second-bianchi-conservation-chain",
  requires @ "claim:nonzero-light-front-radius-torsion-free-reference-connection-dimension-at-least-two-and-an-existing-electrogravitic-solution-with-einstein-contracted-second-bianchi-data",
  supported_by @ "paper:de-teramond-brodsky-arxiv-1206-4365v2-light-front-holography",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.entropicConnection_projective_isTorsionFree_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
  epistemic_status @ "ansatz-loaded",
  caveat @ "epistemic:the-paper-supports-the-ads-qcd-eigenvalue-sector-only-while-einstein-cartan-einstein-maxwell-bcj-and-second-bianchi-are-independent-repository-theorems-composed-here",
  caveat @ "scope:does-not-derive-the-electrogravitic-solution-the-second-bianchi-premise-continuum-light-front-eigenfunctions-spectral-completeness-or-qcd-from-gravity"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3ReducedEinsteinCoupling_eq_boundaryCentralCharge where
  formalizes @ "claim:the-d3-reduced-bulk-einstein-coupling-is-algebraically-identical-to-the-boundary-central-charge-parametrization-with-c-cft-equals-n-squared-over-four",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.centralChargeN4",
  caveat @ "epistemic:an-exact-rewrite-between-two-defined-coupling-parametrizations-not-an-independent-test-of-the-d3-ads-cft-dictionary"

zil attach Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_adsCFT_BCJ_doubleCopy where
  formalizes @ "claim:at-the-d3-ads-cft-bulk-boundary-einstein-coupling-the-finite-bcj-gravity-amplitude-is-exactly-the-color-replaced-gauge-amplitude-and-the-einstein-maxwell-bianchi-double-copy-derives-stress-conservation",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-explicit-d3-five-to-four-dimensional-reduction-fixes-the-complex-einstein-coupling-as-four-pi-squared-r-cubed-over-n-squared-v-c-fourth",
  requires @ "assumption:an-einstein-maxwell-solution-exists-at-the-d3-reduced-coupling-and-its-gravitational-second-bianchi-and-einstein-contraction-hold",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3ReducedEinsteinCoupling_eq_boundaryCentralCharge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
  caveat @ "epistemic:the-amplitude-color-replacement-is-an-exact-bcj-identity-while-the-d3-compactification-dictionary-and-einstein-maxwell-solution-are-explicit-physical-premises",
  caveat @ "scope:does-not-claim-that-a-finite-cubic-graph-amplitude-alone-constructs-a-global-ads-solution-proves-ads-cft-or-derives-the-einstein-maxwell-equation"

zil_file_contract physlib.emComplexEinsteinAdSCFT where
  promises "The complex-Einstein and AdS/CFT bridge. The complex Liouvillian splits into modular flow plus the entropic commutator and reduces to pure modular flow in the reversible limit; the RT entropy of the complex AdS norm is invariant and nonnegative. The independently supplied Compton-cell coupling G = hbar c sigma0^4 is propagated into the Brown-Henneaux central charge, RT area coefficient, parity-symmetric entropic c-function slope, and finite GKP-Witten source Hessian. The explicit D3 reduction G5 equals V G4 then fixes the four-dimensional Complex Einstein coupling as four pi squared R cubed over N squared V c fourth, gives its exact product with the boundary central charge, and transports the complete rapidity-indexed Complex Einstein equation, complex Bianchi identity, both conservation laws and reversible imaginary-curvature limit to that AdS/CFT-normalized coupling. At this same bulk-boundary coupling, the finite cubic-graph BCJ gravity amplitude is proved equal to the Yang-Mills cubic amplitude after color-to-kinematics replacement, and the independent Einstein-Maxwell Bianchi double-copy theorem derives stress-energy conservation. The same coupling directly normalizes the RT product kappa S as two pi area over c fourth, rewrites the GKP-Witten Hessian prefactor as eight pi over kappa c fourth, and parametrizes the equilibrium complex-to-real Einstein correspondence by the boundary central charge. Eliminating kappa and G4 expresses RT entropy and the GKP-Witten Hessian directly through c CFT and promotes the full non-equilibrium Complex Einstein, Bianchi, conservation and reversible-limit family to that boundary-central-charge normalization. The de Teramond-Brodsky soft-wall potential, scalar BF stability and Regge spacings are additionally integrated with the independent projective Einstein-Cartan gauge theorem and the existing Einstein-Maxwell BCJ first-and-second-Bianchi conservation spine. These are exact conditional bridges from the stated Compton-cell, D3, light-front, BCJ and real-Einstein premises, not a derivation of AdS/CFT, an empirical determination of sigma0, a construction of a global bulk solution, an interacting continuum Witten functional, or a global HRT extremal surface."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.brownHenneaux",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem.entropicCentralCharge_fixedPoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary.gkpWittenAffineSourceResponse",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinstein_equilibrium_reduces",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDComplexActionUnification.lightFrontDilatonPotential_quadratic",
    "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.entropicConnection_projective_isTorsionFree_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy"]
  forbids_substitutes ["a circular Planck-cell count containing the Newton constant it returns",
    "a derivation of the AdS/CFT correspondence or an empirical determination of sigma0",
    "an interacting continuum bulk path integral, holographic counterterms, or a global HRT extremal surface",
    "identifying the dimensionful four-dimensional and five-dimensional Newton couplings without an explicit compactification factor",
    "deriving the real Einstein source equation or global bulk dynamics from the coupling dictionary alone",
    "claiming-that-a-finite-bcj-color-replacement-by-itself-constructs-an-ads-bulk-solution",
    "attributing Einstein-Cartan Einstein-Maxwell BCJ or gravitational second-Bianchi dynamics to arXiv 1206.4365"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.complexLiouvillian_eq_modular_plus_entropic,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.rt_modular_entropy_invariant_nonneg,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_brownHenneaux_rt_dictionary,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_entropicCFunction_rt_dictionary,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_rt_modular_entropy_dictionary,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.comptonCell_gkpWitten_source_hessian,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_inferenceEinsteinCoupling_dictionary,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_centralCharge_complexEinsteinCoupling,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_complexEinstein_conservation_reversibleFamily,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_rtEntropy_complexEinsteinCoupling,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_gkpWittenHessian_complexEinsteinCoupling,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_boundaryCentralCharge_complexEinstein_equilibrium,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_rtEntropy_boundaryCentralCharge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_gkpWittenHessian_boundaryCentralCharge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_boundaryCentralCharge_complexEinstein_conservationFamily,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.lightFrontAdSQCD_electroCartan_bianchiDoubleCopy_spine,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3ReducedEinsteinCoupling_eq_boundaryCentralCharge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT.d3_adsCFT_BCJ_doubleCopy]

/- ZIL-END -/

#zil_formalization_lint physlib.emComplexEinsteinAdSCFT
