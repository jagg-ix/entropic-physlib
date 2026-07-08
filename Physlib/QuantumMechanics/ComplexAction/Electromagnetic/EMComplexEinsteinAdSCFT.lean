/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy

/-!
# The complex-Einstein/Dirac superoperator and AdS/CFT (Ryu–Takayanagi)

Links the complex-Hamiltonian split of `Electromagnetic.EMSuperoperatorComplexEinsteinDirac` — the combined superoperator's
Liouvillian `𝓛_{H_R − iH_I} = −i[H_R, ·] − [H_I, ·]` (reversible + entropic) — to the **AdS/CFT modular flow**
and the **Ryu–Takayanagi entanglement entropy**. This closes the loop of the arc: the abstract field
adjoint → the GKSL open-system generator → the AdS/CFT causal-diamond modular flow → the RT area law.

The connection is one identification: the reversible part `−i[H_R, ·]` of the combined complex Liouvillian,
with `H_R = K = −log ρ_A` the **modular Hamiltonian**, is exactly the Tomita–Takesaki **modular flow**
`modularGenerator K = −i[K, ·]` of `PTSymmetricQFT.ModularFlowBoundedOp`. The entropic part `−[H_I, ·]` is the
imaginary Einstein `Λ` / imaginary Dirac mass (from `Electromagnetic.EMSuperoperatorComplexEinsteinDirac`). And the modular
Hamiltonian's expectation `⟨K⟩ = S_A = Area/4G` is the Ryu–Takayanagi entropy (`holographicEE`), a
time-reversal (modular) invariant.

* **§A — the modular flow is the reversible part** (`complexLiouvillian_eq_modular_plus_entropic`,
  `combined_reversible_is_modular`). `𝓛_{K − iH_I} = modularGenerator K − [H_I, ·]`: the combined
  superoperator splits into the AdS/CFT modular flow (reversible) and the entropic `Λ`; at `H_I = 0` it is
  the pure modular flow.
* **§B — the RT entropy is a nonnegative modular invariant** (`rt_modular_entropy_invariant_nonneg`). The
  modular-flow horizon RT entropy `S_A = holographicEE(W², G)` is time-reversal invariant
  (`rt_area_timeReversal_invariant`) and nonnegative (`holographicEE_nonneg`) — the modular Hamiltonian's
  expectation `⟨K⟩`, the horizon area, and the entanglement entropy are one invariant.

So the combined Lorentz–EM superoperator's reversible part *is* the AdS/CFT modular flow, its entropic part
*is* the imaginary Einstein `Λ`, and the modular Hamiltonian whose flow it generates has expectation equal
to the Ryu–Takayanagi entanglement entropy.

## References

* S. Ryu, T. Takayanagi, *Holographic Derivation of Entanglement Entropy from AdS/CFT*, Phys. Rev. Lett. 96
  (2006) 181602 (`S_A = Area/4G`); Tomita–Takesaki modular theory (`σ_t(a) = Δ^{it} a Δ^{−it}`, generator
  `−i[K, ·]`).
* Repo dependencies: `Electromagnetic.EMSuperoperatorComplexEinsteinDirac` (`heisenbergGenerator_complex_decompose`);
  `PTSymmetricQFT.ModularFlowBoundedOp` (`modularGenerator`); `AdSCFT.RyuTakayanagiHolographicEntropy`
  (`holographicEE`, `rt_area_timeReversal_invariant`, `holographicEE_nonneg`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §A — the AdS/CFT modular flow is the reversible part of the combined superoperator -/

/-- **[Combined = modular flow + entropic] `𝓛_{K − iH_I} = modularGenerator K − [H_I, ·]`.** With the real
energy taken to be the modular Hamiltonian `K = −log ρ_A`, the combined complex Liouvillian splits into the
Tomita–Takesaki **modular flow** `modularGenerator K = −i[K, ·]` (the reversible AdS/CFT flow) and the
**entropic** part `−[H_I, ·]` (the imaginary Einstein `Λ` / imaginary Dirac mass). -/
theorem complexLiouvillian_eq_modular_plus_entropic (K H_I a : H →L[ℂ] H) :
    heisenbergGenerator (K - Complex.I • H_I) a = modularGenerator K a - (H_I * a - a * H_I) := by
  rw [modularGenerator, heisenbergGenerator_complex_decompose, heisenbergGenerator_apply]

omit [CompleteSpace H] in
/-- **[Reversible limit] At `H_I = 0` the combined superoperator is the pure modular flow.** No entropic
part: the combined complex Liouvillian reduces to the AdS/CFT modular generator `modularGenerator K`. -/
theorem combined_reversible_is_modular (K a : H →L[ℂ] H) :
    heisenbergGenerator (K - Complex.I • 0) a = modularGenerator K a := by
  rw [smul_zero, sub_zero, modularGenerator]

/-! ## §B — the Ryu–Takayanagi entropy is a nonnegative modular invariant -/

/-- **[RT = nonneg modular invariant] `S_A = holographicEE(W², G)`.** The modular-flow horizon Ryu–Takayanagi
entropy — the modular Hamiltonian's expectation `⟨K⟩` and the horizon area / `4G` — is **time-reversal
(modular) invariant** (`rt_area_timeReversal_invariant`) and **nonnegative** (`holographicEE_nonneg`,
`G > 0`). The minimal surface area, the modular Hamiltonian expectation, and the entanglement entropy are one
invariant. -/
theorem rt_modular_entropy_invariant_nonneg (W θ G : ℝ) (hG : 0 < G) :
    holographicEE (Complex.normSq (conjFactor true (adSComplexCoord W θ))) G
        = holographicEE (W ^ 2) G
      ∧ 0 ≤ holographicEE (W ^ 2) G :=
  ⟨rt_area_timeReversal_invariant W θ G, holographicEE_nonneg (W ^ 2) G (sq_nonneg W) hG⟩

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMComplexEinsteinAdSCFT

end
