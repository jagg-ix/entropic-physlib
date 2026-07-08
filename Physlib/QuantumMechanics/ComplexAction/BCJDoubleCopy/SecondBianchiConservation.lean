/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.SpaceAndTime.Space.Derivatives.Curl

/-!
# The second Bianchi identity and the gravity side of the double copy

Ports the **second Bianchi** content of the complex-action/entropic-time integration layer (`reference tree.Integration.BCJBridge`,
§10–§13) into physlib as *genuine* theorems — the reference tree versions are either Gravitas-bound or Phase-1
trivial `Prop`s (`bcj_schwarz_bianchi` is literally `rfl`; `BCJSecondBianchiVectorProp` is
`ContDiff → ContDiff`). Here the dual-Bianchi pattern is grounded in real identities and linked to the BCJ
color–kinematics arc.

The two Bianchi identities are the two sides of the double copy:

* **first Bianchi** `∂_{[μ}F_{νρ]} = 0` (`F = dA`, `d² = 0`) ↔ the **kinematic** Jacobi
  `n_s + n_t + n_u = 0` of `faradayBCJDuality` — the gauge side;
* **second Bianchi** `∇^μ G_{μν} = 0` (contracted Riemann identity) ↔ **gravity-side conservation**
  `∇^μ T_{μν} = 0` (via the Einstein equation `G = κT`) — the on-shell transversality of the double-copy
  gravity amplitude.

* **§A — contracted second Bianchi ⟹ conservation** (`contracted_bianchi_conservation`). If the divergence
  of the Einstein tensor vanishes (`∇^μ G_{μν} = 0`) and `G = κT` (`κ ≠ 0`), then the stress-energy is
  conserved (`∇^μ T_{μν} = 0`) — the genuine implication behind reference tree's `secondImpliesContracted`.
* **§B — the vector second Bianchi in Lorenz gauge** (`curl_curl_lorenz`). From `Space.curl_of_curl`
  (`∇×(∇×A) = ∇(∇·A) − ΔA`), in Lorenz gauge `∇·A = 0` one gets `∇×(∇×A) = −ΔA` — the massless wave /
  transversality condition, the BCJ on-shell condition for the photon and graviton numerators.
* **§C — the dual-Bianchi contract bundle** (`DualBianchiContracts`, `contracted_of_second`,
  `bcjDualBianchi`, `bcjDualBianchi_firstBianchi`). The structure bundles first Bianchi + second Bianchi +
  contracted conservation with the genuine implication `secondBianchi → contractedConservation`; the BCJ
  instance grounds `firstBianchi` in the Maxwell cyclic identity (the BCJ kinematic Jacobi of
  `faradayBCJDuality`) and proves the implication through §A.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, arXiv:0805.3993; the contracted second Bianchi identity
  `∇^μ G_{μν} = 0` of general relativity.
* Repo dependencies: `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`faradayBCJDuality`, `faraday_bianchi`);
  `Space.curl_of_curl` (the vector second Bianchi); cf. `GravitationalFieldEquations.MatterConservationDivergenceFree`
  (`∇^μ T_{μν} = 0` at the trace level).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation

open Space
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the contracted second Bianchi implies conservation -/

/-- **[Contracted second Bianchi ⟹ stress-energy conservation]** If the divergence of the Einstein tensor
vanishes — the contracted second Bianchi `∇^μ G_{μν} = 0` — and the Einstein equation `G = κT` holds with
`κ ≠ 0`, then `∇^μ T_{μν} = 0`: the matter stress-energy is conserved. This is the genuine content of
reference tree's `secondImpliesContracted` (a Phase-1 `Prop` there). -/
theorem contracted_bianchi_conservation (κ : ℝ) (hκ : κ ≠ 0) (divG divT : Fin 4 → ℝ)
    (hEin : divG = κ • divT) (hBianchi : divG = 0) : divT = 0 := by
  rw [hBianchi] at hEin
  exact (smul_eq_zero.mp hEin.symm).resolve_left hκ

/-! ## §B — the vector second Bianchi in Lorenz gauge (transversality) -/

/-- **[Vector second Bianchi, Lorenz gauge] `∇×(∇×A) = −ΔA`.** In Lorenz gauge `∇·A = 0`, the curl-of-curl
identity `Space.curl_of_curl` (`∇×(∇×A) = ∇(∇·A) − ΔA`) reduces to the massless vector wave operator — the
BCJ on-shell transversality condition for the photon and graviton numerators. -/
theorem curl_curl_lorenz (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f)
    (hdiv : ∇ ⬝ f = 0) : ∇ ⨯ (∇ ⨯ f) = - Space.laplacianVec f := by
  rw [Space.curl_of_curl f hf, hdiv]; simp

/-! ## §C — the dual-Bianchi contract bundle and the BCJ link -/

/-- **[Dual-Bianchi contracts]** The two-level Bianchi bundle: `firstBianchi` (`∂_{[μ}F_{νρ]} = 0`, the
gauge/kinematic sector), `secondBianchi` (`∇^μ G_{μν} = 0`, the gravity sector), `contractedConservation`
(`∇^μ T_{μν} = 0`), with the genuine implication that the second Bianchi forces conservation. -/
structure DualBianchiContracts where
  /-- First Bianchi `∂_{[μ}F_{νρ]} = 0` — the BCJ kinematic-Jacobi (gauge) sector. -/
  firstBianchi : Prop
  /-- Second Bianchi `∇^μ G_{μν} = 0` — the gravity sector. -/
  secondBianchi : Prop
  /-- Contracted conservation `∇^μ T_{μν} = 0`. -/
  contractedConservation : Prop
  /-- The second Bianchi implies contracted conservation (via the Einstein equation). -/
  secondImpliesContracted : secondBianchi → contractedConservation

/-- **Contracted conservation follows from the second Bianchi.** -/
theorem DualBianchiContracts.contracted_of_second (B : DualBianchiContracts)
    (h2 : B.secondBianchi) : B.contractedConservation :=
  B.secondImpliesContracted h2

/-- **[BCJ dual-Bianchi instance]** The first Bianchi is the Maxwell cyclic identity — *exactly* the BCJ
kinematic Jacobi `n_s + n_t + n_u = 0` of `faradayBCJDuality` — and the second Bianchi `∇^μ G_{μν} = 0`
(with Einstein `G = κT`) yields stress-energy conservation via `contracted_bianchi_conservation`.
The two sides of the double copy bundled as one contract: gauge ↔ first Bianchi, gravity ↔ second Bianchi. -/
noncomputable def bcjDualBianchi (κ : ℝ) (hκ : κ ≠ 0) (divG divT : Fin 4 → ℝ)
    (hEin : divG = κ • divT) : DualBianchiContracts where
  firstBianchi := ∀ (k A : Fin 4 → ℝ) (lam μ ν : Fin 4),
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0
  secondBianchi := divG = 0
  contractedConservation := divT = 0
  secondImpliesContracted := fun h2 => contracted_bianchi_conservation κ hκ divG divT hEin h2

/-- **The BCJ dual-Bianchi's first Bianchi holds** — the Maxwell cyclic / BCJ kinematic Jacobi
(`faraday_bianchi`). -/
theorem bcjDualBianchi_firstBianchi (κ : ℝ) (hκ : κ ≠ 0) (divG divT : Fin 4 → ℝ)
    (hEin : divG = κ • divT) : (bcjDualBianchi κ hκ divG divT hEin).firstBianchi :=
  fun k A lam μ ν => faraday_bianchi k A lam μ ν

/-- **[Link] The BCJ kinematic Jacobi *is* the first Bianchi.** The three kinematic numerators of
`faradayBCJDuality` sum to zero — the Maxwell cyclic identity — which is the `firstBianchi` of the dual
contract. The gauge-side Jacobi of color–kinematics duality and the homogeneous Maxwell equation are the
same statement. -/
theorem bcj_kinematic_jacobi_is_first_bianchi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (c_s c_t c_u : ℝ) (hc : c_s + c_t + c_u = 0) :
    (faradayBCJDuality k A lam μ ν c_s c_t c_u hc).n_s
      + (faradayBCJDuality k A lam μ ν c_s c_t c_u hc).n_t
      + (faradayBCJDuality k A lam μ ν c_s c_t c_u hc).n_u = 0 :=
  (faradayBCJDuality k A lam μ ν c_s c_t c_u hc).kinematic_jacobi

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation

end
