/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBisognanoWichmannModular
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit
meta import Zil

/-!
# The Bisognano–Wichmann modular flow as an operator Killing flow (Witten §5.3, operator form)

Deep search shows the operator Bisognano–Wichmann content is *almost assembled* in the repo:
`AlgebraicQFT.SummersVacuumModularLinks` carries the wedge boost flow `modularAut t A = Δ^{it} A Δ^{−it}`
(`modularBoost t = e^{2πtK}`, `K = bogoliubovGenerator`) with its multiplicativity, additivity, group law,
derivative-generator `2π·ad_K`, fixed generator, and wedge Haag duality — each gated by
`assumption:bisognano-wichmann-wedge`; and `EntropicTime.KayWaldBisognanoWichmannModular` has the abstract
"Killing flows preserve the bracket" lemma.  What was missing is the **assembly**: the BW flow as an actual
*operator one-parameter `*`-automorphism group* — the repo's `KillingFlow` structure — so that the abstract
modular=Killing lemma applies to it.  This module supplies it:

* `wedgeModularRingHom` / `wedgeModularKillingFlow` — **the BW modular flow bundled as a `KillingFlow`**: each
  `modularAut t` is a ring homomorphism (`modularAut_one/_mul/_add/_zero_map`), `σ_0 = id`
  (`modularAut_zero`), and the one-parameter group law holds (`modularAut_group`) — the operator `Δ^{it}(·)Δ^{−it}`
  as a genuine automorphism flow, not a family of maps.
* `wedgeModular_preserves_bracket` — the KayWald lemma applied: the BW modular flow **preserves the commutator
  bracket** `σ_s([a,b]) = [σ_s a, σ_s b]` — the modular flow is a quantum Killing flow, the operator heart of
  "the modular flow is the boost isometry".
* `bisognanoWichmann_operator_flow` — the capstone: the flow is an automorphism group (`σ_0 = id`, cocycle),
  preserves the bracket, has derivative generator `2π·ad_K` at `t = 0` (`modularAut_hasDerivAt_adK`), its
  conjugation is an involution `J² = 1` (`wedgeReflection_involution`), it fixes its generator
  (`modularAut_fixes_generator`), and the wedge satisfies Tomita–Takesaki Haag duality
  (`wedge_tomita_takesaki_haag_duality`) — **every operator property Bisognano–Wichmann asserts of the vacuum
  wedge modular flow, realized by the boost flow on the finite wedge carrier**.

Honest scope: this realizes the operator *flow side* of Bisognano–Wichmann on the finite (2×2 boost-plane)
wedge carrier — the one-parameter `*`-automorphism group with boost generator, reflection, and Haag duality.
What remains the graph's `assumption:bisognano-wichmann-wedge` is the *state-side identification*: that the
Minkowski **vacuum's intrinsic** modular operator (of `Foundations`/GNS data on the continuum wedge algebra)
is this flow — Bisognano–Wichmann 1975's analytic input, not discharged here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannOperatorFlow

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBisognanoWichmannModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-! ## §1. The BW modular flow as a ring-homomorphism family -/

/-- Each modular automorphism `σ_t = Δ^{it}(·)Δ^{−it}` (`modularAut t`) as a **ring homomorphism** on the
wedge matrix algebra — unital, multiplicative, additive. -/
noncomputable def wedgeModularRingHom (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ →+* Matrix (Fin 2) (Fin 2) ℝ where
  toFun := modularAut t
  map_one' := modularAut_one t
  map_mul' := fun A B => modularAut_mul t A B
  map_zero' := modularAut_zero_map t
  map_add' := fun A B => modularAut_add t A B

/-- **[The BW modular flow is a `KillingFlow`]** — the one-parameter family `t ↦ σ_t` with `σ_0 = id`
(`modularAut_zero`) and the cocycle law `σ_{s+t} = σ_s ∘ σ_t` (`modularAut_group`): the operator
`Δ^{it}(·)Δ^{−it}` bundled as a genuine one-parameter `*`-automorphism group — the repo's quantum Killing
flow structure. -/
noncomputable def wedgeModularKillingFlow : KillingFlow (Matrix (Fin 2) (Fin 2) ℝ) where
  π := wedgeModularRingHom
  flow_zero := RingHom.ext fun A => modularAut_zero A
  cocycle := fun s t => RingHom.ext fun A => (modularAut_group s t A).symm

/-! ## §2. The modular flow preserves the bracket: modular = Killing -/

/-- **[The BW modular flow preserves the commutator bracket]** `σ_s([a,b]) = [σ_s a, σ_s b]` — the KayWald
"modular flow is a Killing flow" lemma applied to the bundled BW flow: the operator heart of Bisognano–Wichmann,
the modular flow acting as the boost isometry on the observable algebra. -/
theorem wedgeModular_preserves_bracket (s : ℝ) (a b : Matrix (Fin 2) (Fin 2) ℝ) :
    wedgeModularKillingFlow.π s (collisionStar a b)
      = collisionStar (wedgeModularKillingFlow.π s a) (wedgeModularKillingFlow.π s b) :=
  modularFlow_is_killing_bracket wedgeModularKillingFlow s a b

/-! ## §3. The operator Bisognano–Wichmann package -/

/-- **[The operator Bisognano–Wichmann flow, assembled]** — the wedge boost flow realizes **every operator
property BW asserts of the vacuum modular flow**: **(i)** it is a one-parameter automorphism group
(`σ_0 = id` and the cocycle law, from the `KillingFlow` bundle); **(ii)** it preserves the commutator bracket
(modular = Killing); **(iii)** its generator at `t = 0` is `2π·ad_K` — the boost generator
(`modularAut_hasDerivAt_adK`); **(iv)** the wedge reflection is an involution `J² = 1`
(`wedgeReflection_involution`); **(v)** the flow fixes its generator (`modularAut_fixes_generator`); **(vi)**
the wedge satisfies Tomita–Takesaki Haag duality (`wedge_tomita_takesaki_haag_duality`).  The state-side
identification with the vacuum's intrinsic modular operator remains the honest graph assumption. -/
theorem bisognanoWichmann_operator_flow (s t : ℝ) (a b A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (wedgeModularKillingFlow.π 0 A = A
        ∧ wedgeModularKillingFlow.π (s + t) A
            = wedgeModularKillingFlow.π s (wedgeModularKillingFlow.π t A))
      ∧ wedgeModularKillingFlow.π s (collisionStar a b)
          = collisionStar (wedgeModularKillingFlow.π s a) (wedgeModularKillingFlow.π s b)
      ∧ HasDerivAt (fun τ => modularAut τ A i j)
          (2 * Real.pi * collisionStar bogoliubovGenerator A i j) 0
      ∧ bogoliubovGenerator * bogoliubovGenerator = 1
      ∧ modularAut t bogoliubovGenerator = bogoliubovGenerator
      ∧ (commutant (wedgeAlgebra wedgeModularHamiltonian)
            = causalComplementAlgebra wedgeModularHamiltonian
          ∧ IsBicommutantClosed (wedgeAlgebra wedgeModularHamiltonian)
          ∧ causalComplementAlgebra wedgeModularHamiltonian
              = modularFixed wedgeModularHamiltonian
          ∧ wedgeModularHamiltonian ∈ wedgeAlgebra wedgeModularHamiltonian) :=
  ⟨⟨modularAut_zero A, modularAut_group s t A |>.symm⟩,
    wedgeModular_preserves_bracket s a b,
    modularAut_hasDerivAt_adK A i j,
    wedgeReflection_involution,
    modularAut_fixes_generator t,
    wedge_tomita_takesaki_haag_duality⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannOperatorFlow

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannOperatorFlow.wedgeModular_preserves_bracket where
  formalizes @ "claim:the-bisognano-wichmann-modular-flow-bundled-as-a-killing-flow-preserves-the-commutator-bracket",
  requires @ "assumption:bisognano-wichmann-wedge",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBisognanoWichmannModular.modularFlow_is_killing_bracket",
  caveat @ "epistemic:finite-wedge-carrier-the-flow-side-of-bw-the-vacuum-state-identification-remains-the-assumption"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannOperatorFlow.bisognanoWichmann_operator_flow where
  formalizes @ "claim:the-wedge-boost-flow-realizes-every-operator-property-bisognano-wichmann-asserts-of-the-vacuum-modular-flow-on-the-finite-carrier",
  requires @ "assumption:bisognano-wichmann-wedge",
  requires @ "claim:the-bisognano-wichmann-modular-flow-bundled-as-a-killing-flow-preserves-the-commutator-bracket",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks.modularAut_hasDerivAt_adK",
  caveat @ "epistemic:operator-flow-side-assembled-the-state-side-vacuum-identification-is-not-discharged"

/- ZIL-END -/
