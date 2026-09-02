/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Physlib.QFT.PathIntegral.FiniteWilsonGaugeModel
public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

/-!
# Single-boson exchange form of the Schwinger-Dyson equation

This file formalizes the finite-index algebraic spine of

Miriam Patricolo, Marcel Gievers, Kilian Fraboulet, Aiman Al-Eryani,
Sarah Heinzelmann, Pietro M. Bonetti, Alessandro Toschi, Demetrio Vilardi,
and Sabine Andergassen,
*Single-boson exchange formulation of the Schwinger-Dyson equation and its application to the
functional renormalization group*, arXiv:2411.11661v5.

The paper rewrites the conventional Schwinger-Dyson self-energy in terms of a screened
single-boson exchange kernel.  The key algebraic step is Eq. (14),

`w_r * lambda_r = U + U o Pi_r o V`,

where `r` is one of the particle-hole, crossed particle-hole, or particle-particle transfer
channels.  Once this identity is available, the self-energy obtained by the one-loop contraction
with the exchange kernel is identical to the conventional Schwinger-Dyson expression.

The formalization below keeps the analytic input as data: finite internal sums model the channel
products of Eq. (6), `selfEnergyFromKernel` models the one-loop contraction of Eq. (7), and
`SingleBosonExchangeData.exchange_eq_weightedSDE` is the precise assumption corresponding to
Eq. (14), with a real coefficient to cover the channel and spin conventions used in Eqs. (5) and
(10).  The lemmas then prove that the SBE and conventional Schwinger-Dyson self-energies, and
their scale-dependent FRG versions, are the same algebraic object.

The later sections add the second orientation of Eq. (14), the U-reducible vertex decomposition
`lambdaBar_r * w_r * lambda_r + M_r` from Eq. (13), the magnetic/density/superconducting
physical-channel self-energy formulas of Eqs. (31), (35), and (32), the Leibniz three-term
FRG flow of Eq. (40), and the exact-projection condition behind the form-factor discussion in
Sec. 2.5.

The appendix material is represented by four additional algebraic interfaces: Appendix A.1 by
the 4-by-4 spin-matrix representation and crossing-symmetry relations; Appendix A.2 by the
particle-hole, crossed particle-hole, and particle-particle momentum/frequency routings and
their conservation laws; Appendix B by the non-local split `U_r = B_r + F_r` and the residual
fermionic correction; Appendix C by finite transfer-sum SDE formulas; and Appendix D by the
single-boson exchange flow equations for `w`, `lambda`, and the rest function.

The physical-channel algebra also includes the SU(2) magnetic/density change of basis
and its inverse, the singlet/triplet superconducting pairing relations, the local Hubbard
amplitude sign rule, and the half-filled Shiba channel exchange used in the discussion of
the repulsive and attractive Hubbard models.

The path-integral layer is linked to the repository's finite Faddeev-Popov construction by a
finite ghost complex.  The SBE identity is then lifted through ghost-weighted insertions, and
through the combined ghost plus Caldeira-Leggett reduced-dynamics weight.

## References

* M. Patricolo, M. Gievers, K. Fraboulet, A. Al-Eryani, S. Heinzelmann,
  P. M. Bonetti, A. Toschi, D. Vilardi, S. Andergassen,
  *Single-boson exchange formulation of the Schwinger-Dyson equation and its application to the
  functional renormalization group*, arXiv:2411.11661v5, Eqs. (2), (5)--(7), (10), (13),
  (14), (26)--(30), (31), (32), (35), (37), (38), (40), Appendix A.1--A.2, Appendix B,
  Appendix C, and Appendix D.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

/-! ## A. Channel algebra -/

/-- The three transfer channels used by the parquet and Schwinger-Dyson decompositions. -/
inductive SDEChannel where
  | particleHole
  | crossedParticleHole
  | particleParticle
deriving DecidableEq, Repr

/-- A two-point kernel, such as a fermion propagator or self-energy matrix. -/
abbrev TwoPoint (ι : Type*) := ι → ι → ℝ

/-- A four-point kernel, such as a bare interaction, bubble, or full two-particle vertex. -/
abbrev FourPoint (ι : Type*) := ι → ι → ι → ι → ℝ

/-- The channel product of Eq. (6), written with finite internal sums. -/
noncomputable def channelProduct {ι : Type*} [Fintype ι] (r : SDEChannel)
    (A B : FourPoint ι) : FourPoint ι :=
  match r with
  | .particleHole =>
      fun i1 i2 i3 i4 => ∑ a : ι, ∑ b : ι, A b i2 a i4 * B i1 a i3 b
  | .crossedParticleHole =>
      fun i1 i2 i3 i4 => ∑ a : ι, ∑ b : ι, A i1 a b i4 * B b i2 i3 a
  | .particleParticle =>
      fun i1 i2 i3 i4 => ∑ a : ι, ∑ b : ι, A i1 i2 a b * B a b i3 i4

/-- The particle-hole channel product, Eq. (6) in the particle-hole channel. -/
lemma channelProduct_particleHole_apply {ι : Type*} [Fintype ι]
    (A B : FourPoint ι) (i1 i2 i3 i4 : ι) :
    channelProduct SDEChannel.particleHole A B i1 i2 i3 i4
      = ∑ a : ι, ∑ b : ι, A b i2 a i4 * B i1 a i3 b := rfl

/-- The crossed particle-hole channel product, Eq. (6) in the crossed particle-hole channel. -/
lemma channelProduct_crossedParticleHole_apply {ι : Type*} [Fintype ι]
    (A B : FourPoint ι) (i1 i2 i3 i4 : ι) :
    channelProduct SDEChannel.crossedParticleHole A B i1 i2 i3 i4
      = ∑ a : ι, ∑ b : ι, A i1 a b i4 * B b i2 i3 a := rfl

/-- The particle-particle channel product, Eq. (6) in the particle-particle channel. -/
lemma channelProduct_particleParticle_apply {ι : Type*} [Fintype ι]
    (A B : FourPoint ι) (i1 i2 i3 i4 : ι) :
    channelProduct SDEChannel.particleParticle A B i1 i2 i3 i4
      = ∑ a : ι, ∑ b : ι, A i1 i2 a b * B a b i3 i4 := rfl

/-! ## B. Schwinger-Dyson and single-boson exchange kernels -/

/-- The weighted conventional Schwinger-Dyson kernel
`U + alpha * (U o Pi_r o V)`, covering the channel conventions of Eqs. (5) and (10). -/
noncomputable def weightedSDEKernel {ι : Type*} [Fintype ι] (r : SDEChannel) (alpha : ℝ)
    (U Pi V : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 =>
    U i1 i2 i3 i4 + alpha * channelProduct r U (channelProduct r Pi V) i1 i2 i3 i4

/-- Pointwise form of the weighted Schwinger-Dyson kernel. -/
lemma weightedSDEKernel_apply {ι : Type*} [Fintype ι] (r : SDEChannel) (alpha : ℝ)
    (U Pi V : FourPoint ι) (i1 i2 i3 i4 : ι) :
    weightedSDEKernel r alpha U Pi V i1 i2 i3 i4 =
      U i1 i2 i3 i4 + alpha * channelProduct r U (channelProduct r Pi V) i1 i2 i3 i4 :=
  rfl

/-- One-loop contraction of a four-point kernel with a propagator, the algebraic form of Eq. (7). -/
noncomputable def selfEnergyFromKernel {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (K : FourPoint ι) : TwoPoint ι :=
  fun i j => ∑ a : ι, ∑ b : ι, G a b * K b i a j

/-- Pointwise form of the self-energy contraction. -/
lemma selfEnergyFromKernel_apply {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    selfEnergyFromKernel G K i j = ∑ a : ι, ∑ b : ι, G a b * K b i a j := rfl

/-- The conventional Schwinger-Dyson self-energy built from `U + alpha * (U o Pi_r o V)`. -/
noncomputable def conventionalSelfEnergy {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (r : SDEChannel) (alpha : ℝ) (U Pi V : FourPoint ι) : TwoPoint ι :=
  selfEnergyFromKernel G (weightedSDEKernel r alpha U Pi V)

/-- The single-boson exchange self-energy built from the screened exchange kernel. -/
noncomputable def sbeSelfEnergy {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (exchangeKernel : FourPoint ι) : TwoPoint ι :=
  selfEnergyFromKernel G exchangeKernel

/-- Data for a single-boson exchange representation of a Schwinger-Dyson channel.  The field
`exchange_eq_weightedSDE` is Eq. (14) with an explicit channel coefficient. -/
structure SingleBosonExchangeData (ι : Type*) [Fintype ι] where
  /-- The transfer channel. -/
  channel : SDEChannel
  /-- The real prefactor fixed by spin and channel conventions. -/
  coefficient : ℝ
  /-- The bare four-fermion interaction `U`. -/
  bareInteraction : FourPoint ι
  /-- The particle-hole, crossed particle-hole, or particle-particle bubble `Pi_r`. -/
  bubble : FourPoint ι
  /-- The full two-particle vertex `V`. -/
  fullVertex : FourPoint ι
  /-- The single-boson exchange kernel, corresponding to `w_r * lambda_r`. -/
  exchangeKernel : FourPoint ι
  /-- The multiboson rest function `M_r` in the SBE decomposition. -/
  restFunction : FourPoint ι
  /-- The full vertex is the sum of the SBE exchange part and the multiboson rest part. -/
  fullVertex_eq_exchange_add_rest :
    fullVertex = fun i1 i2 i3 i4 => exchangeKernel i1 i2 i3 i4 + restFunction i1 i2 i3 i4
  /-- The SBE identity: `w_r * lambda_r = U + alpha * (U o Pi_r o V)`. -/
  exchange_eq_weightedSDE :
    exchangeKernel = weightedSDEKernel channel coefficient bareInteraction bubble fullVertex

/-! ## C. The SBE self-energy equals the conventional Schwinger-Dyson self-energy -/

/-- Eq. (14) as a named lemma for the finite-index SBE data. -/
lemma sbeKernel_eq_weightedSDE {ι : Type*} [Fintype ι]
    (D : SingleBosonExchangeData ι) :
    D.exchangeKernel =
      weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex :=
  D.exchange_eq_weightedSDE

/-- The SBE self-energy is equal to the conventional Schwinger-Dyson self-energy whenever
Eq. (14) holds. -/
lemma sbeSelfEnergy_eq_conventional {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) :
    sbeSelfEnergy G D.exchangeKernel =
      conventionalSelfEnergy G D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex := by
  unfold sbeSelfEnergy conventionalSelfEnergy
  rw [D.exchange_eq_weightedSDE]

/-- Pointwise version of `sbeSelfEnergy_eq_conventional`. -/
lemma sbeSelfEnergy_eq_conventional_apply {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    sbeSelfEnergy G D.exchangeKernel i j =
      conventionalSelfEnergy G D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex i j := by
  rw [sbeSelfEnergy_eq_conventional G D]

/-- The SBE one-loop self-energy depends on the exchange kernel.  Two SBE data sets with the same
exchange kernel give the same self-energy, independently of their rest-function descriptions. -/
lemma sbeSelfEnergy_eq_of_same_exchange {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) {D E : SingleBosonExchangeData ι}
    (h : D.exchangeKernel = E.exchangeKernel) :
    sbeSelfEnergy G D.exchangeKernel = sbeSelfEnergy G E.exchangeKernel := by
  rw [h]

/-- A scale-dependent SBE representation gives the same scale-dependent self-energy as the
conventional Schwinger-Dyson kernel at every scale. -/
lemma sbeFlow_eq_conventionalFlow {κ ι : Type*} [Fintype ι]
    (G : κ → TwoPoint ι) (D : κ → SingleBosonExchangeData ι) :
    (fun k => sbeSelfEnergy (G k) (D k).exchangeKernel) =
      fun k =>
        conventionalSelfEnergy (G k) (D k).channel (D k).coefficient
          (D k).bareInteraction (D k).bubble (D k).fullVertex := by
  funext k
  exact sbeSelfEnergy_eq_conventional (G k) (D k)

/-! ## D. Projection and form-factor truncation checks -/

/-- A projection of four-point kernels, such as a form-factor projection in a truncated-unity FRG
implementation. -/
abbrev KernelProjection (ι : Type*) := FourPoint ι → FourPoint ι

/-- A projected self-energy obtained after projecting the exchange kernel. -/
noncomputable def projectedSelfEnergy {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (P : KernelProjection ι) (K : FourPoint ι) : TwoPoint ι :=
  selfEnergyFromKernel G (P K)

/-- If the projection fixes the exchange kernel, the projected self-energy is unchanged. -/
lemma projectedSelfEnergy_eq_of_preservesKernel {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (P : KernelProjection ι) (K : FourPoint ι) (hP : P K = K) :
    projectedSelfEnergy G P K = selfEnergyFromKernel G K := by
  unfold projectedSelfEnergy
  rw [hP]

/-- A projection that preserves the SBE exchange kernel also preserves the conventional SDE
self-energy obtained from Eq. (14). -/
lemma projectedSbeSelfEnergy_eq_conventional {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (P : KernelProjection ι) (D : SingleBosonExchangeData ι)
    (hP : P D.exchangeKernel = D.exchangeKernel) :
    projectedSelfEnergy G P D.exchangeKernel =
      conventionalSelfEnergy G D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex := by
  calc projectedSelfEnergy G P D.exchangeKernel
      = selfEnergyFromKernel G D.exchangeKernel := projectedSelfEnergy_eq_of_preservesKernel G P _ hP
    _ = sbeSelfEnergy G D.exchangeKernel := rfl
    _ = conventionalSelfEnergy G D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex :=
        sbeSelfEnergy_eq_conventional G D

/-! ## E. Left and right Hedin exchange identities -/

/-- The left-hand SBE kernel `U + alpha * (V o Pi_r o U)`, corresponding to
`lambdaBar_r * w_r` in Eq. (14). -/
noncomputable def weightedLeftSDEKernel {ι : Type*} [Fintype ι] (r : SDEChannel) (alpha : ℝ)
    (U Pi V : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 =>
    U i1 i2 i3 i4 + alpha * channelProduct r (channelProduct r V Pi) U i1 i2 i3 i4

/-- Pointwise form of the left-hand SBE kernel. -/
lemma weightedLeftSDEKernel_apply {ι : Type*} [Fintype ι] (r : SDEChannel) (alpha : ℝ)
    (U Pi V : FourPoint ι) (i1 i2 i3 i4 : ι) :
    weightedLeftSDEKernel r alpha U Pi V i1 i2 i3 i4 =
      U i1 i2 i3 i4 + alpha * channelProduct r (channelProduct r V Pi) U i1 i2 i3 i4 :=
  rfl

/-- Data containing both exchange orientations in Eq. (14):
`w_r * lambda_r = U + U o Pi_r o V` and
`lambdaBar_r * w_r = U + V o Pi_r o U`. -/
structure LeftRightSingleBosonExchangeData (ι : Type*) [Fintype ι] where
  /-- The transfer channel. -/
  channel : SDEChannel
  /-- The real prefactor fixed by spin and channel conventions. -/
  coefficient : ℝ
  /-- The bare four-fermion interaction `U`. -/
  bareInteraction : FourPoint ι
  /-- The channel bubble `Pi_r`. -/
  bubble : FourPoint ι
  /-- The full two-particle vertex `V`. -/
  fullVertex : FourPoint ι
  /-- The right exchange kernel `w_r * lambda_r`. -/
  rightExchangeKernel : FourPoint ι
  /-- The left exchange kernel `lambdaBar_r * w_r`. -/
  leftExchangeKernel : FourPoint ι
  /-- The right SBE identity, `w_r * lambda_r = U + alpha * (U o Pi_r o V)`. -/
  rightExchange_eq_weightedSDE :
    rightExchangeKernel = weightedSDEKernel channel coefficient bareInteraction bubble fullVertex
  /-- The left SBE identity, `lambdaBar_r * w_r = U + alpha * (V o Pi_r o U)`. -/
  leftExchange_eq_weightedSDE :
    leftExchangeKernel = weightedLeftSDEKernel channel coefficient bareInteraction bubble fullVertex

/-- The right Hedin/SBE identity from Eq. (14). -/
lemma rightSbeKernel_eq_weightedSDE {ι : Type*} [Fintype ι]
    (D : LeftRightSingleBosonExchangeData ι) :
    D.rightExchangeKernel =
      weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex :=
  D.rightExchange_eq_weightedSDE

/-- The left Hedin/SBE identity from Eq. (14). -/
lemma leftSbeKernel_eq_weightedSDE {ι : Type*} [Fintype ι]
    (D : LeftRightSingleBosonExchangeData ι) :
    D.leftExchangeKernel =
      weightedLeftSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex :=
  D.leftExchange_eq_weightedSDE

/-- The self-energy built from the left exchange kernel equals the left conventional
Schwinger-Dyson contraction. -/
lemma leftSbeSelfEnergy_eq_conventional {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (D : LeftRightSingleBosonExchangeData ι) :
    sbeSelfEnergy G D.leftExchangeKernel =
      selfEnergyFromKernel G
        (weightedLeftSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex) := by
  unfold sbeSelfEnergy
  rw [D.leftExchange_eq_weightedSDE]

/-! ## F. Single-boson reducible vertex and rest-function separation -/

/-- Pointwise product of two four-point kernels. -/
noncomputable def pointwiseKernelMul {ι : Type*} (A B : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 => A i1 i2 i3 i4 * B i1 i2 i3 i4

/-- Pointwise form of `pointwiseKernelMul`. -/
lemma pointwiseKernelMul_apply {ι : Type*} (A B : FourPoint ι) (i1 i2 i3 i4 : ι) :
    pointwiseKernelMul A B i1 i2 i3 i4 = A i1 i2 i3 i4 * B i1 i2 i3 i4 :=
  rfl

/-- The U-reducible single-boson part `lambdaBar_r * w_r * lambda_r` of Eq. (13). -/
noncomputable def singleBosonReduciblePart {ι : Type*}
    (lambdaBar bosonPropagator lambda : FourPoint ι) : FourPoint ι :=
  pointwiseKernelMul lambdaBar (pointwiseKernelMul bosonPropagator lambda)

/-- Pointwise form of the U-reducible single-boson part. -/
lemma singleBosonReduciblePart_apply {ι : Type*}
    (lambdaBar bosonPropagator lambda : FourPoint ι) (i1 i2 i3 i4 : ι) :
    singleBosonReduciblePart lambdaBar bosonPropagator lambda i1 i2 i3 i4 =
      lambdaBar i1 i2 i3 i4 * (bosonPropagator i1 i2 i3 i4 * lambda i1 i2 i3 i4) :=
  rfl

/-- A vertex decomposition into the U-reducible single-boson part and the multiboson rest
function `M_r`. -/
structure SingleBosonVertexDecomposition (ι : Type*) where
  /-- The left fermion-boson vertex `lambdaBar_r`. -/
  lambdaBar : FourPoint ι
  /-- The screened bosonic propagator `w_r`. -/
  bosonPropagator : FourPoint ι
  /-- The right fermion-boson vertex `lambda_r`. -/
  lambda : FourPoint ι
  /-- The multiboson rest function `M_r`. -/
  restFunction : FourPoint ι
  /-- The full two-particle vertex `V`. -/
  fullVertex : FourPoint ι
  /-- The vertex decomposition `V = lambdaBar_r * w_r * lambda_r + M_r`. -/
  fullVertex_eq_singleBoson_add_rest :
    fullVertex = fun i1 i2 i3 i4 =>
      singleBosonReduciblePart lambdaBar bosonPropagator lambda i1 i2 i3 i4
        + restFunction i1 i2 i3 i4

/-- The full vertex is the U-reducible SBE part plus the multiboson rest function. -/
lemma fullVertex_eq_singleBoson_add_rest {ι : Type*}
    (D : SingleBosonVertexDecomposition ι) :
    D.fullVertex = fun i1 i2 i3 i4 =>
      singleBosonReduciblePart D.lambdaBar D.bosonPropagator D.lambda i1 i2 i3 i4
        + D.restFunction i1 i2 i3 i4 :=
  D.fullVertex_eq_singleBoson_add_rest

/-- If the rest function is zero, the full vertex is exactly the U-reducible SBE part. -/
lemma fullVertex_eq_singleBoson_of_rest_zero {ι : Type*}
    (D : SingleBosonVertexDecomposition ι)
    (hrest : D.restFunction = fun _ _ _ _ => 0) :
    D.fullVertex = singleBosonReduciblePart D.lambdaBar D.bosonPropagator D.lambda := by
  rw [D.fullVertex_eq_singleBoson_add_rest, hrest]
  funext i1 i2 i3 i4
  simp

/-! ## G. Physical-channel self-energy formulas -/

/-- The SU(2)-symmetric physical channels used in Eqs. (31), (35), and (32). -/
inductive PhysicalSDEChannel where
  | magnetic
  | density
  | superconducting
deriving DecidableEq, Repr

/-- The overall sign in the physical-channel SBE self-energy. -/
def PhysicalSDEChannel.sign : PhysicalSDEChannel → ℝ
  | .magnetic => 1
  | .density => 1
  | .superconducting => -1

/-- The density-channel Hartree subtraction coefficient. -/
def PhysicalSDEChannel.densityCounterterm : PhysicalSDEChannel → ℝ
  | .magnetic => 0
  | .density => -2
  | .superconducting => 0

/-- The physical-channel exchange kernel, including the density counterterm of Eq. (35). -/
noncomputable def physicalExchangeKernel {ι : Type*} (c : PhysicalSDEChannel)
    (exchangeKernel densityBare : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 =>
    exchangeKernel i1 i2 i3 i4
      + c.densityCounterterm * densityBare i1 i2 i3 i4

/-- The physical-channel SBE self-energy, covering Eqs. (31), (35), and (32). -/
noncomputable def physicalSelfEnergy {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (c : PhysicalSDEChannel)
    (exchangeKernel densityBare : FourPoint ι) : TwoPoint ι :=
  fun i j => c.sign * selfEnergyFromKernel G (physicalExchangeKernel c exchangeKernel densityBare) i j

/-- Magnetic channel: `Sigma = G * (wM lambdaM)`. -/
lemma physicalSelfEnergy_magnetic_apply {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (exchangeKernel densityBare : FourPoint ι) (i j : ι) :
    physicalSelfEnergy G PhysicalSDEChannel.magnetic exchangeKernel densityBare i j =
      selfEnergyFromKernel G exchangeKernel i j := by
  simp [physicalSelfEnergy, physicalExchangeKernel, selfEnergyFromKernel, PhysicalSDEChannel.sign,
    PhysicalSDEChannel.densityCounterterm]

/-- Density channel: `Sigma = G * (wD lambdaD) - 2 G * U_D`, Eq. (35). -/
lemma physicalSelfEnergy_density_apply {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (exchangeKernel densityBare : FourPoint ι) (i j : ι) :
    physicalSelfEnergy G PhysicalSDEChannel.density exchangeKernel densityBare i j =
      selfEnergyFromKernel G
        (fun a b c d => exchangeKernel a b c d - 2 * densityBare a b c d) i j := by
  simp [physicalSelfEnergy, physicalExchangeKernel, selfEnergyFromKernel, PhysicalSDEChannel.sign,
    PhysicalSDEChannel.densityCounterterm, sub_eq_add_neg]

/-- Superconducting channel: `Sigma = -(wSC lambdaSC) * G`, Eq. (32), with the sign placed in the
physical-channel self-energy convention. -/
lemma physicalSelfEnergy_superconducting_apply {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (exchangeKernel densityBare : FourPoint ι) (i j : ι) :
    physicalSelfEnergy G PhysicalSDEChannel.superconducting exchangeKernel densityBare i j =
      - selfEnergyFromKernel G exchangeKernel i j := by
  simp [physicalSelfEnergy, physicalExchangeKernel, selfEnergyFromKernel, PhysicalSDEChannel.sign,
    PhysicalSDEChannel.densityCounterterm]

/-! ## H. Physical spin-channel linear algebra -/

/-- Magnetic physical component `M = V^{up up} - V^{up down}`, Eq. (26a). -/
def magneticSpinComponent (upUp upDown : ℝ) : ℝ :=
  upUp - upDown

/-- Density physical component `D = V^{up up} + V^{up down}`, Eq. (26b). -/
def densitySpinComponent (upUp upDown : ℝ) : ℝ :=
  upUp + upDown

/-- Inversion of the magnetic/density change of basis: `V^{up up} = (M + D)/2`, Eq. (27). -/
noncomputable def spinUpUpOfMagneticDensity (magnetic density : ℝ) : ℝ :=
  (magnetic + density) / 2

/-- Inversion of the magnetic/density change of basis: `V^{up down} = (D - M)/2`, Eq. (27). -/
noncomputable def spinUpDownOfMagneticDensity (magnetic density : ℝ) : ℝ :=
  (density - magnetic) / 2

/-- The inverse formulas of Eq. (27) recover the magnetic component. -/
lemma magneticSpinComponent_of_inverse (magnetic density : ℝ) :
    magneticSpinComponent
        (spinUpUpOfMagneticDensity magnetic density)
        (spinUpDownOfMagneticDensity magnetic density) = magnetic := by
  unfold magneticSpinComponent spinUpUpOfMagneticDensity spinUpDownOfMagneticDensity
  ring

/-- The inverse formulas of Eq. (27) recover the density component. -/
lemma densitySpinComponent_of_inverse (magnetic density : ℝ) :
    densitySpinComponent
        (spinUpUpOfMagneticDensity magnetic density)
        (spinUpDownOfMagneticDensity magnetic density) = density := by
  unfold densitySpinComponent spinUpUpOfMagneticDensity spinUpDownOfMagneticDensity
  ring

/-- The magnetic/density basis reproduces the original `up-up` component. -/
lemma spinUpUpOfMagneticDensity_eq (upUp upDown : ℝ) :
    spinUpUpOfMagneticDensity
        (magneticSpinComponent upUp upDown)
        (densitySpinComponent upUp upDown) = upUp := by
  unfold spinUpUpOfMagneticDensity magneticSpinComponent densitySpinComponent
  ring

/-- The magnetic/density basis reproduces the original `up-down` component. -/
lemma spinUpDownOfMagneticDensity_eq (upUp upDown : ℝ) :
    spinUpDownOfMagneticDensity
        (magneticSpinComponent upUp upDown)
        (densitySpinComponent upUp upDown) = upDown := by
  unfold spinUpDownOfMagneticDensity magneticSpinComponent densitySpinComponent
  ring

/-- Superconducting singlet component `s = upDown - crossed`, Eq. (28). -/
def singletPairingComponent (upDown crossed : ℝ) : ℝ :=
  upDown - crossed

/-- Superconducting triplet component `t = upDown + crossed`, Eq. (28). -/
def tripletPairingComponent (upDown crossed : ℝ) : ℝ :=
  upDown + crossed

/-- Superconducting channel as the average of singlet and triplet components, Eq. (29). -/
noncomputable def superconductingFromSingletTriplet (singlet triplet : ℝ) : ℝ :=
  (singlet + triplet) / 2

/-- Eq. (29): `(s + t)/2` recovers the `up-down` superconducting component. -/
lemma superconductingFromSingletTriplet_eq_upDown (upDown crossed : ℝ) :
    superconductingFromSingletTriplet
        (singletPairingComponent upDown crossed)
        (tripletPairingComponent upDown crossed) = upDown := by
  unfold superconductingFromSingletTriplet singletPairingComponent tripletPairingComponent
  ring

/-- Eq. (30): if the triplet fermion-boson coupling is fixed to `1`, then the singlet
superconducting coupling is `2 * lambda_upDown - 1`. -/
lemma singletPairingComponent_eq_two_mul_sub_one (lambdaUpDown lambdaCrossed : ℝ)
    (htriplet : tripletPairingComponent lambdaUpDown lambdaCrossed = 1) :
    singletPairingComponent lambdaUpDown lambdaCrossed = 2 * lambdaUpDown - 1 := by
  unfold tripletPairingComponent singletPairingComponent at *
  have hcrossed : lambdaCrossed = 1 - lambdaUpDown := by
    rw [← htriplet]
    ring
  rw [hcrossed]
  ring

/-! ## I. Hubbard sign and channel exchange data -/

/-- The local Hubbard bare interaction amplitude used in Eq. (38), separated from the spin
Kronecker factors and conservation deltas. -/
def hubbardLocalAmplitude (U : ℝ) : ℝ :=
  -U

/-- The Hubbard bare amplitude changes sign when the interaction sign is reversed. -/
lemma hubbardLocalAmplitude_neg (U : ℝ) :
    hubbardLocalAmplitude (-U) = - hubbardLocalAmplitude U := by
  unfold hubbardLocalAmplitude
  ring

/-- A record of the half-filled Shiba channel exchange: the attractive model's density and
superconducting channels correspond to magnetic components of the repulsive model. -/
structure ShibaChannelExchange where
  /-- Magnetic-channel self-energy in the repulsive description. -/
  repulsiveMagnetic : ℝ
  /-- Density-channel self-energy in the attractive description. -/
  attractiveDensity : ℝ
  /-- Superconducting-channel self-energy in the attractive description. -/
  attractiveSuperconducting : ℝ
  /-- The density channel after Shiba transformation agrees with the repulsive magnetic channel. -/
  density_eq_magnetic : attractiveDensity = repulsiveMagnetic
  /-- The superconducting channel after Shiba transformation agrees with the repulsive magnetic channel. -/
  superconducting_eq_magnetic : attractiveSuperconducting = repulsiveMagnetic

/-- The Shiba exchange identifies the attractive density channel with the repulsive magnetic
channel. -/
lemma shiba_density_eq_magnetic (S : ShibaChannelExchange) :
    S.attractiveDensity = S.repulsiveMagnetic :=
  S.density_eq_magnetic

/-- The Shiba exchange identifies the attractive superconducting channel with the repulsive
magnetic channel. -/
lemma shiba_superconducting_eq_magnetic (S : ShibaChannelExchange) :
    S.attractiveSuperconducting = S.repulsiveMagnetic :=
  S.superconducting_eq_magnetic

/-- The two attractive channels identified by the Shiba transformation agree with each other. -/
lemma shiba_density_eq_superconducting (S : ShibaChannelExchange) :
    S.attractiveDensity = S.attractiveSuperconducting := by
  rw [S.density_eq_magnetic, S.superconducting_eq_magnetic]

/-! ## J. FRG flow and form-factor projection consequences -/

/-- Additivity of the one-loop self-energy contraction in its four-point kernel argument. -/
lemma selfEnergyFromKernel_add {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (K L : FourPoint ι) :
    selfEnergyFromKernel G (fun i1 i2 i3 i4 => K i1 i2 i3 i4 + L i1 i2 i3 i4) =
      fun i j => selfEnergyFromKernel G K i j + selfEnergyFromKernel G L i j := by
  funext i j
  simp [selfEnergyFromKernel, mul_add, Finset.sum_add_distrib]

/-- The Leibniz kernel rate `d(w lambda) = dw lambda + w dlambda`. -/
noncomputable def sbeKernelLeibnizRate {ι : Type*}
    (dw w dlambda lambda : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 =>
    pointwiseKernelMul dw lambda i1 i2 i3 i4
      + pointwiseKernelMul w dlambda i1 i2 i3 i4

/-- The self-energy rate written as `dG * exchange + G * dexchange`. -/
noncomputable def sbeSelfEnergyRateByKernel {ι : Type*} [Fintype ι]
    (dG G : TwoPoint ι) (exchangeKernel exchangeRate : FourPoint ι) : TwoPoint ι :=
  fun i j =>
    selfEnergyFromKernel dG exchangeKernel i j
      + selfEnergyFromKernel G exchangeRate i j

/-- The expanded Leibniz form of Eq. (40):
`dSigma = dG * (w lambda) + G * (dw lambda) + G * (w dlambda)`. -/
noncomputable def sbeSelfEnergyLeibnizRate {ι : Type*} [Fintype ι]
    (dG G : TwoPoint ι) (w dw lambda dlambda : FourPoint ι) : TwoPoint ι :=
  fun i j =>
    selfEnergyFromKernel dG (pointwiseKernelMul w lambda) i j
      + (selfEnergyFromKernel G (pointwiseKernelMul dw lambda) i j
        + selfEnergyFromKernel G (pointwiseKernelMul w dlambda) i j)

/-- If the exchange-kernel rate obeys the Leibniz rule, the compact rate
`dG * exchange + G * dexchange` is exactly the three-term FRG self-energy flow of Eq. (40). -/
lemma sbeSelfEnergyRateByKernel_eq_leibniz {ι : Type*} [Fintype ι]
    (dG G : TwoPoint ι) (w dw lambda dlambda : FourPoint ι) :
    sbeSelfEnergyRateByKernel dG G (pointwiseKernelMul w lambda)
        (sbeKernelLeibnizRate dw w dlambda lambda)
      = sbeSelfEnergyLeibnizRate dG G w dw lambda dlambda := by
  funext i j
  unfold sbeSelfEnergyRateByKernel sbeSelfEnergyLeibnizRate sbeKernelLeibnizRate
  rw [selfEnergyFromKernel_add]

/-- If two projected SBE kernels both preserve the same exact exchange kernel, their projected
self-energies agree.  This is the converged form-factor case behind the channel equivalence
discussed in Sec. 2.5. -/
lemma projectedSelfEnergy_eq_projectedSelfEnergy_of_preserve_same_kernel {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) (P Q : KernelProjection ι) (K : FourPoint ι)
    (hP : P K = K) (hQ : Q K = K) :
    projectedSelfEnergy G P K = projectedSelfEnergy G Q K := by
  rw [projectedSelfEnergy_eq_of_preservesKernel G P K hP,
    projectedSelfEnergy_eq_of_preservesKernel G Q K hQ]

/-- Exact SBE channel data with the same exchange kernel give the same conventional
Schwinger-Dyson self-energy. -/
lemma conventionalSelfEnergy_eq_of_same_exchange {ι : Type*} [Fintype ι]
    (G : TwoPoint ι) {D E : SingleBosonExchangeData ι}
    (h : D.exchangeKernel = E.exchangeKernel) :
    conventionalSelfEnergy G D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex =
      conventionalSelfEnergy G E.channel E.coefficient E.bareInteraction E.bubble E.fullVertex := by
  rw [← sbeSelfEnergy_eq_conventional G D, ← sbeSelfEnergy_eq_conventional G E, h]

/-! ## K. Appendix A.1: spin matrices -/

/-- The two spin labels used in the appendix matrix representation. -/
inductive Spin where
  | up
  | down
deriving DecidableEq, Repr

/-- The two-element finite type of spin labels. -/
instance : Fintype Spin where
  elems := {Spin.up, Spin.down}
  complete := by
    intro s
    cases s <;> simp

/-- A row or column label of the appendix 4-by-4 spin matrices. -/
abbrev SpinPair := Spin × Spin

/-- A four-spin component of a two-particle object. -/
abbrev SpinKernel := Spin → Spin → Spin → Spin → ℝ

/-- The 4-by-4 spin matrix representation of a four-spin object. -/
abbrev SpinMatrix := SpinPair → SpinPair → ℝ

/-- Convert a four-spin kernel to the 4-by-4 matrix representation of Appendix A.1. -/
noncomputable def spinMatrix (A : SpinKernel) : SpinMatrix :=
  fun p q => A p.1 p.2 q.1 q.2

/-- Convert a 4-by-4 spin matrix back to a four-spin kernel. -/
noncomputable def spinKernelOfMatrix (M : SpinMatrix) : SpinKernel :=
  fun s1 s2 s3 s4 => M (s1, s2) (s3, s4)

/-- Matrix multiplication on the 4-by-4 spin representation, written as two spin sums. -/
noncomputable def spinMatrixMul (A B : SpinMatrix) : SpinMatrix :=
  fun p r => ∑ q1 : Spin, ∑ q2 : Spin, A p (q1, q2) * B (q1, q2) r

/-- Spin-index contraction of two four-spin kernels. -/
noncomputable def spinContraction (A B : SpinKernel) : SpinKernel :=
  fun s1 s2 s3 s4 => ∑ q1 : Spin, ∑ q2 : Spin, A s1 s2 q1 q2 * B q1 q2 s3 s4

/-- The spin-matrix product is exactly the spin-index summation of Appendix A.1. -/
lemma spinMatrixMul_eq_spinContraction (A B : SpinKernel) :
    spinMatrix (spinContraction A B) = spinMatrixMul (spinMatrix A) (spinMatrix B) := by
  rfl

/-- Crossing antisymmetry of a four-spin vertex, Eq. (44), separated into incoming and outgoing
swaps. -/
def CrossingSymmetricSpinKernel (A : SpinKernel) : Prop :=
  (∀ s1 s2 s3 s4, A s1 s2 s3 s4 = - A s2 s1 s3 s4)
    ∧ (∀ s1 s2 s3 s4, A s1 s2 s3 s4 = - A s1 s2 s4 s3)
    ∧ (∀ s1 s2 s3 s4, A s1 s2 s3 s4 = A s2 s1 s4 s3)

/-- The incoming-spin exchange part of Eq. (44). -/
lemma crossing_incoming_swap {A : SpinKernel} (hA : CrossingSymmetricSpinKernel A)
    (s1 s2 s3 s4 : Spin) :
    A s1 s2 s3 s4 = - A s2 s1 s3 s4 :=
  hA.1 s1 s2 s3 s4

/-- The outgoing-spin exchange part of Eq. (44). -/
lemma crossing_outgoing_swap {A : SpinKernel} (hA : CrossingSymmetricSpinKernel A)
    (s1 s2 s3 s4 : Spin) :
    A s1 s2 s3 s4 = - A s1 s2 s4 s3 :=
  hA.2.1 s1 s2 s3 s4

/-- The simultaneous incoming/outgoing exchange part of Eq. (44). -/
lemma crossing_double_swap {A : SpinKernel} (hA : CrossingSymmetricSpinKernel A)
    (s1 s2 s3 s4 : Spin) :
    A s1 s2 s3 s4 = A s2 s1 s4 s3 :=
  hA.2.2 s1 s2 s3 s4

/-! ## L. Appendix A.2: channel momentum and frequency conventions -/

/-- External two-particle momenta/frequencies `(k1', k2' | k1, k2)`. -/
structure ChannelExternal (α : Type*) where
  /-- The first outgoing momentum/frequency. -/
  k1out : α
  /-- The second outgoing momentum/frequency. -/
  k2out : α
  /-- The first incoming momentum/frequency. -/
  k1in : α
  /-- The second incoming momentum/frequency. -/
  k2in : α

/-- Total outgoing momentum/frequency. -/
def ChannelExternal.outTotal {α : Type*} [Add α] (x : ChannelExternal α) : α :=
  x.k1out + x.k2out

/-- Total incoming momentum/frequency. -/
def ChannelExternal.inTotal {α : Type*} [Add α] (x : ChannelExternal α) : α :=
  x.k1in + x.k2in

/-- Momentum/frequency conservation for an external two-particle configuration. -/
def ChannelExternal.Conserves {α : Type*} [Add α] (x : ChannelExternal α) : Prop :=
  x.outTotal = x.inTotal

/-- Particle-hole channel routing from Fig. 7. -/
def particleHoleExternal {α : Type*} [Add α] (Q k kp : α) : ChannelExternal α :=
  { k1out := kp, k2out := k + Q, k1in := kp + Q, k2in := k }

/-- Crossed particle-hole channel routing from Fig. 7. -/
def crossedParticleHoleExternal {α : Type*} [Add α] (Q k kp : α) : ChannelExternal α :=
  { k1out := k + Q, k2out := kp, k1in := kp + Q, k2in := k }

/-- Particle-particle channel routing from Fig. 7. -/
def particleParticleExternal {α : Type*} [AddGroup α] (Q k kp : α) : ChannelExternal α :=
  { k1out := Q - kp, k2out := kp, k1in := Q - k, k2in := k }

/-- The particle-hole routing conserves total momentum/frequency. -/
lemma particleHoleExternal_conserves {α : Type*} [AddCommGroup α] (Q k kp : α) :
    (particleHoleExternal Q k kp).Conserves := by
  simp [ChannelExternal.Conserves, ChannelExternal.outTotal, ChannelExternal.inTotal,
    particleHoleExternal, add_left_comm, add_comm]

/-- The crossed particle-hole routing conserves total momentum/frequency. -/
lemma crossedParticleHoleExternal_conserves {α : Type*} [AddCommGroup α] (Q k kp : α) :
    (crossedParticleHoleExternal Q k kp).Conserves := by
  simp [ChannelExternal.Conserves, ChannelExternal.outTotal, ChannelExternal.inTotal,
    crossedParticleHoleExternal, add_left_comm, add_comm]

/-- The particle-particle routing conserves total momentum/frequency. -/
lemma particleParticleExternal_conserves {α : Type*} [AddCommGroup α] (Q k kp : α) :
    (particleParticleExternal Q k kp).Conserves := by
  simp [ChannelExternal.Conserves, ChannelExternal.outTotal, ChannelExternal.inTotal,
    particleParticleExternal]

/-- Abstract ceiling/floor half-frequency split used for the symmetrized Matsubara notation. -/
structure SymmetrizedFrequencySplit (Ω : Type*) [Neg Ω] where
  /-- The upper half-frequency representative. -/
  ceilHalf : Ω → Ω
  /-- The lower half-frequency representative. -/
  floorHalf : Ω → Ω
  /-- Eq. (46), first sign-change rule. -/
  ceilHalf_neg : ∀ omega, ceilHalf (-omega) = - floorHalf omega
  /-- Eq. (46), second sign-change rule. -/
  floorHalf_neg : ∀ omega, floorHalf (-omega) = - ceilHalf omega

/-- The first sign-change rule for symmetrized frequencies, Eq. (46). -/
lemma ceilHalf_neg_eq {Ω : Type*} [Neg Ω] (S : SymmetrizedFrequencySplit Ω) (omega : Ω) :
    S.ceilHalf (-omega) = - S.floorHalf omega :=
  S.ceilHalf_neg omega

/-- The second sign-change rule for symmetrized frequencies, Eq. (46). -/
lemma floorHalf_neg_eq {Ω : Type*} [Neg Ω] (S : SymmetrizedFrequencySplit Ω) (omega : Ω) :
    S.floorHalf (-omega) = - S.ceilHalf omega :=
  S.floorHalf_neg omega

/-! ## M. Appendix B: non-local interactions -/

/-- A non-local bare interaction split `U_r = B_r + F_r`, Eq. (84). -/
structure NonLocalInteractionSplit (ι : Type*) where
  /-- The full non-local bare interaction `U_r`. -/
  bareInteraction : FourPoint ι
  /-- The bosonic part `B_r(Q_r)`. -/
  bosonicPart : FourPoint ι
  /-- The remaining fermionic dependence `F_r(Q_r,k_r,k'_r)`. -/
  fermionicRemainder : FourPoint ι
  /-- The split identity `U_r = B_r + F_r`. -/
  bare_eq_bosonic_add_fermionic :
    bareInteraction = fun i1 i2 i3 i4 =>
      bosonicPart i1 i2 i3 i4 + fermionicRemainder i1 i2 i3 i4

/-- Linearity of the first factor in the channel product. -/
lemma channelProduct_add_left {ι : Type*} [Fintype ι] (r : SDEChannel)
    (A B C : FourPoint ι) :
    channelProduct r (fun i1 i2 i3 i4 => A i1 i2 i3 i4 + B i1 i2 i3 i4) C =
      fun i1 i2 i3 i4 => channelProduct r A C i1 i2 i3 i4
        + channelProduct r B C i1 i2 i3 i4 := by
  cases r <;> funext i1 i2 i3 i4 <;>
    simp [channelProduct, add_mul, Finset.sum_add_distrib]

/-- The generalized bosonic SBE kernel using only `B_r`, Eq. (86). -/
noncomputable def generalizedBosonicSDEKernel {ι : Type*} [Fintype ι]
    (r : SDEChannel) (alpha : ℝ) (S : NonLocalInteractionSplit ι)
    (Pi V : FourPoint ι) : FourPoint ι :=
  weightedSDEKernel r alpha S.bosonicPart Pi V

/-- The non-local correction left by the fermionic remainder `F_r`. -/
noncomputable def nonLocalFermionicCorrection {ι : Type*} [Fintype ι]
    (r : SDEChannel) (alpha : ℝ) (S : NonLocalInteractionSplit ι)
    (Pi V : FourPoint ι) : FourPoint ι :=
  fun i1 i2 i3 i4 =>
    S.fermionicRemainder i1 i2 i3 i4
      + alpha * channelProduct r S.fermionicRemainder (channelProduct r Pi V) i1 i2 i3 i4

/-- Splitting `U_r = B_r + F_r` splits the full SDE kernel into the generalized bosonic kernel
plus the fermionic correction. -/
lemma weightedSDEKernel_nonLocal_split {ι : Type*} [Fintype ι]
    (r : SDEChannel) (alpha : ℝ) (S : NonLocalInteractionSplit ι) (Pi V : FourPoint ι) :
    weightedSDEKernel r alpha S.bareInteraction Pi V =
      fun i1 i2 i3 i4 =>
        generalizedBosonicSDEKernel r alpha S Pi V i1 i2 i3 i4
          + nonLocalFermionicCorrection r alpha S Pi V i1 i2 i3 i4 := by
  rw [S.bare_eq_bosonic_add_fermionic]
  funext i1 i2 i3 i4
  have hprod := congrFun
    (congrFun
      (congrFun
        (congrFun
          (channelProduct_add_left r S.bosonicPart S.fermionicRemainder (channelProduct r Pi V))
          i1)
        i2)
      i3)
    i4
  simp [weightedSDEKernel, generalizedBosonicSDEKernel, nonLocalFermionicCorrection, hprod]
  rw [mul_add]
  ac_rfl

/-- If the non-local fermionic correction vanishes, the generalized bosonic SBE kernel is the
full conventional SDE kernel. -/
lemma generalizedBosonicSDEKernel_eq_full_of_correction_zero {ι : Type*} [Fintype ι]
    (r : SDEChannel) (alpha : ℝ) (S : NonLocalInteractionSplit ι) (Pi V : FourPoint ι)
    (hzero : nonLocalFermionicCorrection r alpha S Pi V = fun _ _ _ _ => 0) :
    weightedSDEKernel r alpha S.bareInteraction Pi V =
      generalizedBosonicSDEKernel r alpha S Pi V := by
  rw [weightedSDEKernel_nonLocal_split r alpha S Pi V, hzero]
  funext i1 i2 i3 i4
  simp

/-! ## N. Appendix C: explicit momentum/frequency SDE sums -/

/-- A scalar transfer sum for one external momentum/frequency point. -/
noncomputable def transferSelfEnergy {q : Type*} [Fintype q]
    (G exchange : q → ℝ) : ℝ :=
  ∑ Q : q, exchange Q * G Q

/-- The magnetic-channel transfer form of Eq. (106). -/
noncomputable def magneticTransferSelfEnergy {q : Type*} [Fintype q]
    (G wM lambdaM : q → ℝ) : ℝ :=
  transferSelfEnergy G (fun Q => wM Q * lambdaM Q)

/-- The density-channel transfer form of Eq. (107), including the `-2 U_D` term. -/
noncomputable def densityTransferSelfEnergy {q : Type*} [Fintype q]
    (G wD lambdaD densityBare : q → ℝ) : ℝ :=
  ∑ Q : q, (wD Q * lambdaD Q - 2 * densityBare Q) * G Q

/-- The superconducting-channel transfer form of Eq. (109). -/
noncomputable def superconductingTransferSelfEnergy {q : Type*} [Fintype q]
    (G wSC lambdaSC : q → ℝ) : ℝ :=
  - ∑ Q : q, (wSC Q * lambdaSC Q) * G Q

/-- Pointwise magnetic transfer SDE expansion. -/
lemma magneticTransferSelfEnergy_eq_sum {q : Type*} [Fintype q]
    (G wM lambdaM : q → ℝ) :
    magneticTransferSelfEnergy G wM lambdaM =
      ∑ Q : q, (wM Q * lambdaM Q) * G Q :=
  rfl

/-- Pointwise density transfer SDE expansion. -/
lemma densityTransferSelfEnergy_eq_sum {q : Type*} [Fintype q]
    (G wD lambdaD densityBare : q → ℝ) :
    densityTransferSelfEnergy G wD lambdaD densityBare =
      ∑ Q : q, (wD Q * lambdaD Q - 2 * densityBare Q) * G Q :=
  rfl

/-- Pointwise superconducting transfer SDE expansion. -/
lemma superconductingTransferSelfEnergy_eq_sum {q : Type*} [Fintype q]
    (G wSC lambdaSC : q → ℝ) :
    superconductingTransferSelfEnergy G wSC lambdaSC =
      - ∑ Q : q, (wSC Q * lambdaSC Q) * G Q :=
  rfl

/-! ## O. Appendix D: SBE flow equations -/

/-- The diagrammatic-channel bosonic propagator flow
`dot w_r = w_r * lambda_r o dot Pi_r o lambda_r * w_r`, Eq. (110a), in scalar transfer form. -/
noncomputable def bosonPropagatorFlow {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ) : q → ℝ :=
  fun Q => (w Q) ^ 2 * ∑ p : k, lambda Q p * bubbleDot Q p * lambda Q p

/-- The diagrammatic-channel fermion-boson coupling flow
`dot lambda_r = lambda_r o dot Pi_r o I_r`, Eq. (110b). -/
noncomputable def fermionBosonCouplingFlow {q k : Type*} [Fintype k]
    (lambda bubbleDot : q → k → ℝ) (irreducible : q → k → k → ℝ) : q → k → ℝ :=
  fun Q p => ∑ p' : k, lambda Q p' * bubbleDot Q p' * irreducible Q p' p

/-- The rest-function flow `dot M_r = I_r o dot Pi_r o I_r`, Eq. (110c). -/
noncomputable def restFunctionFlow {q k : Type*} [Fintype k]
    (irreducible : q → k → k → ℝ) (bubbleDot : q → k → ℝ) : q → k → k → ℝ :=
  fun Q p p' => ∑ p'' : k, irreducible Q p p'' * bubbleDot Q p'' * irreducible Q p'' p'

/-- The physical-channel sign for bosonic-propagator flows in Eqs. (111)--(113). -/
def PhysicalSDEChannel.flowSign : PhysicalSDEChannel → ℝ
  | .magnetic => -1
  | .density => 1
  | .superconducting => 1

/-- Physical-channel bosonic propagator flow, combining Eqs. (111a), (112a), and (113a). -/
noncomputable def physicalBosonPropagatorFlow {q k : Type*} [Fintype k]
    (c : PhysicalSDEChannel) (w : q → ℝ) (lambda bubbleDot : q → k → ℝ) : q → ℝ :=
  fun Q => c.flowSign * bosonPropagatorFlow w lambda bubbleDot Q

/-- Magnetic-channel bosonic flow has the minus sign of Eq. (111a). -/
lemma physicalBosonPropagatorFlow_magnetic {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ) (Q : q) :
    physicalBosonPropagatorFlow PhysicalSDEChannel.magnetic w lambda bubbleDot Q =
      - bosonPropagatorFlow w lambda bubbleDot Q := by
  simp [physicalBosonPropagatorFlow, PhysicalSDEChannel.flowSign]

/-- Density-channel bosonic flow has the positive sign of Eq. (112a). -/
lemma physicalBosonPropagatorFlow_density {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ) (Q : q) :
    physicalBosonPropagatorFlow PhysicalSDEChannel.density w lambda bubbleDot Q =
      bosonPropagatorFlow w lambda bubbleDot Q := by
  simp [physicalBosonPropagatorFlow, PhysicalSDEChannel.flowSign]

/-- Superconducting-channel bosonic flow has the positive sign of Eq. (113a). -/
lemma physicalBosonPropagatorFlow_superconducting {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ) (Q : q) :
    physicalBosonPropagatorFlow PhysicalSDEChannel.superconducting w lambda bubbleDot Q =
      bosonPropagatorFlow w lambda bubbleDot Q := by
  simp [physicalBosonPropagatorFlow, PhysicalSDEChannel.flowSign]

/-! ## P. Form-factor truncation and fluctuation diagnostics -/

/-- A function of fermionic momentum/frequency is independent of that argument. -/
def FermionicArgumentIndependent {k : Type*} (f : k → ℝ) : Prop :=
  ∀ p p' : k, f p = f p'

/-- The one-mode, s-wave-style projection that replaces a fermionic function by its value at a
chosen reference momentum/frequency. -/
noncomputable def constantFormFactorProjection {k : Type*} (anchor : k) (f : k → ℝ) : k → ℝ :=
  fun _ => f anchor

/-- The constant form-factor projection is exact on fermionic-argument independent functions. -/
lemma constantFormFactorProjection_eq_of_independent {k : Type*} (anchor : k)
    (f : k → ℝ) (hf : FermionicArgumentIndependent f) :
    constantFormFactorProjection anchor f = f := by
  funext p
  exact hf anchor p

/-- A bosonic-only vertex written as a function with a dummy fermionic argument. -/
def bosonicOnlyVertex {q k : Type*} (w : q → ℝ) : q → k → ℝ :=
  fun Q _ => w Q

/-- A bosonic-only vertex is independent of its fermionic argument. -/
lemma bosonicOnlyVertex_independent {q k : Type*} (w : q → ℝ) (Q : q) :
    FermionicArgumentIndependent (bosonicOnlyVertex (q := q) (k := k) w Q) := by
  intro p p'
  rfl

/-- The s-wave projection is exact on a bosonic-only vertex. -/
lemma constantFormFactorProjection_bosonicOnly {q k : Type*} (anchor : k)
    (w : q → ℝ) (Q : q) :
    constantFormFactorProjection anchor (bosonicOnlyVertex (q := q) (k := k) w Q)
      = bosonicOnlyVertex (q := q) (k := k) w Q :=
  constantFormFactorProjection_eq_of_independent anchor _
    (bosonicOnlyVertex_independent w Q)

/-- The transfer self-energy with a form-factor projection of the fermionic argument in
`lambda(Q, p)`. -/
noncomputable def projectedTransferSelfEnergy {q k : Type*} [Fintype q]
    (anchor external : k) (G w : q → ℝ) (lambda : q → k → ℝ) : ℝ :=
  ∑ Q : q, (w Q * constantFormFactorProjection anchor (lambda Q) external) * G Q

/-- The unprojected transfer self-energy with an explicit external fermionic argument. -/
noncomputable def exactTransferSelfEnergyWithFermion {q k : Type*} [Fintype q]
    (external : k) (G w : q → ℝ) (lambda : q → k → ℝ) : ℝ :=
  ∑ Q : q, (w Q * lambda Q external) * G Q

/-- If the fermion-boson coupling is independent of its fermionic argument, the one-mode
form-factor projection gives the exact transfer self-energy. -/
lemma projectedTransferSelfEnergy_eq_exact_of_independent {q k : Type*} [Fintype q]
    (anchor external : k) (G w : q → ℝ) (lambda : q → k → ℝ)
    (hlambda : ∀ Q : q, FermionicArgumentIndependent (lambda Q)) :
    projectedTransferSelfEnergy anchor external G w lambda =
      exactTransferSelfEnergyWithFermion external G w lambda := by
  unfold projectedTransferSelfEnergy exactTransferSelfEnergyWithFermion
  refine Finset.sum_congr rfl ?_
  intro Q _
  rw [constantFormFactorProjection_eq_of_independent anchor (lambda Q) (hlambda Q)]

/-- Bias between two one-mode form-factor choices for the same transfer expression. -/
noncomputable def transferProjectionBias {q k : Type*} [Fintype q]
    (anchorA anchorB external : k) (G w : q → ℝ) (lambda : q → k → ℝ) : ℝ :=
  projectedTransferSelfEnergy anchorA external G w lambda
    - projectedTransferSelfEnergy anchorB external G w lambda

/-- If the fermion-boson coupling is independent of its fermionic argument, the projection
bias between two one-mode choices vanishes. -/
lemma transferProjectionBias_eq_zero_of_independent {q k : Type*} [Fintype q]
    (anchorA anchorB external : k) (G w : q → ℝ) (lambda : q → k → ℝ)
    (hlambda : ∀ Q : q, FermionicArgumentIndependent (lambda Q)) :
    transferProjectionBias anchorA anchorB external G w lambda = 0 := by
  unfold transferProjectionBias
  rw [projectedTransferSelfEnergy_eq_exact_of_independent anchorA external G w lambda hlambda,
    projectedTransferSelfEnergy_eq_exact_of_independent anchorB external G w lambda hlambda]
  ring

/-- Quasiparticle weight from Eq. (41), using the derivative of the real part of the self-energy
at zero real frequency. -/
noncomputable def quasiparticleWeight (dReSigmaAtZero : ℝ) : ℝ :=
  1 / (1 - dReSigmaAtZero)

/-- If the real-frequency self-energy slope vanishes, the quasiparticle weight is one. -/
lemma quasiparticleWeight_zero_slope :
    quasiparticleWeight 0 = 1 := by
  norm_num [quasiparticleWeight]

/-- A finite fluctuation-diagnostics integrand with support on one transfer mode. -/
def singleModeIntegrand {q : Type*} [DecidableEq q] (Q0 : q) (amplitude : ℝ) : q → ℝ :=
  fun Q => if Q = Q0 then amplitude else 0

/-- A single-mode fluctuation diagnostic sums to the amplitude of its selected transfer mode. -/
lemma fluctuationDiagnostic_singleMode_sum {q : Type*} [Fintype q] [DecidableEq q]
    (Q0 : q) (amplitude : ℝ) :
    (∑ Q : q, singleModeIntegrand Q0 amplitude Q) = amplitude := by
  simp [singleModeIntegrand]

/-- A self-energy model is sign-independent in the Hubbard interaction when it depends on `U`
only through `U^2`. -/
noncomputable def interactionSignIndependentSelfEnergy (profile : ℝ → ℝ) (U : ℝ) : ℝ :=
  profile (U ^ 2)

/-- The squared-interaction self-energy model is unchanged under `U -> -U`. -/
lemma interactionSignIndependentSelfEnergy_neg (profile : ℝ → ℝ) (U : ℝ) :
    interactionSignIndependentSelfEnergy profile (-U)
      = interactionSignIndependentSelfEnergy profile U := by
  unfold interactionSignIndependentSelfEnergy
  ring_nf

/-! ## Q. Appendix D flow closure for the exchange vertex -/

/-- Transfer-space single-boson exchange vertex `lambda_L * w * lambda_R`. -/
noncomputable def transferExchangeVertex {q k : Type*}
    (w : q → ℝ) (lambdaLeft lambdaRight : q → k → ℝ) : q → k → k → ℝ :=
  fun Q p p' => lambdaLeft Q p * w Q * lambdaRight Q p'

/-- Product-rule algebra for the flow of `lambda_L * w * lambda_R`.  This is the
finite-index part of the differentiated SBE exchange vertex in Appendix D. -/
noncomputable def transferExchangeVertexFlow {q k : Type*}
    (w dotw : q → ℝ)
    (lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight : q → k → ℝ) : q → k → k → ℝ :=
  fun Q p p' =>
    dotLambdaLeft Q p * w Q * lambdaRight Q p'
      + lambdaLeft Q p * dotw Q * lambdaRight Q p'
      + lambdaLeft Q p * w Q * dotLambdaRight Q p'

/-- Pointwise expansion of the differentiated transfer-space exchange vertex. -/
lemma transferExchangeVertexFlow_apply {q k : Type*}
    (w dotw : q → ℝ)
    (lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight : q → k → ℝ)
    (Q : q) (p p' : k) :
    transferExchangeVertexFlow w dotw lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight Q p p' =
      dotLambdaLeft Q p * w Q * lambdaRight Q p'
        + lambdaLeft Q p * dotw Q * lambdaRight Q p'
        + lambdaLeft Q p * w Q * dotLambdaRight Q p' :=
  rfl

/-- The full SBE vertex flow is the exchange-vertex flow plus the multiboson rest-function flow. -/
noncomputable def fullSBEVertexFlow {q k : Type*}
    (w dotw : q → ℝ)
    (lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight : q → k → ℝ)
    (dotRest : q → k → k → ℝ) : q → k → k → ℝ :=
  fun Q p p' =>
    transferExchangeVertexFlow w dotw lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight Q p p'
      + dotRest Q p p'

/-- Pointwise split of the full SBE vertex flow into exchange and rest contributions. -/
lemma fullSBEVertexFlow_eq_exchange_add_rest {q k : Type*}
    (w dotw : q → ℝ)
    (lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight : q → k → ℝ)
    (dotRest : q → k → k → ℝ) (Q : q) (p p' : k) :
    fullSBEVertexFlow w dotw lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight dotRest Q p p' =
      transferExchangeVertexFlow w dotw lambdaLeft dotLambdaLeft lambdaRight dotLambdaRight Q p p'
        + dotRest Q p p' :=
  rfl

/-- Appendix D exchange-vertex flow obtained by inserting Eqs. (110a) and (110b) into the
product-rule flow for `lambda * w * lambda`. -/
noncomputable def appendixDExchangeVertexFlow {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ)
    (irreducible : q → k → k → ℝ) : q → k → k → ℝ :=
  transferExchangeVertexFlow w (bosonPropagatorFlow w lambda bubbleDot) lambda
    (fermionBosonCouplingFlow lambda bubbleDot irreducible) lambda
    (fermionBosonCouplingFlow lambda bubbleDot irreducible)

/-- Pointwise form of the Appendix D exchange-vertex flow after substituting the boson and
fermion-boson coupling flows. -/
lemma appendixDExchangeVertexFlow_apply {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ)
    (irreducible : q → k → k → ℝ) (Q : q) (p p' : k) :
    appendixDExchangeVertexFlow w lambda bubbleDot irreducible Q p p' =
      fermionBosonCouplingFlow lambda bubbleDot irreducible Q p * w Q * lambda Q p'
        + lambda Q p * bosonPropagatorFlow w lambda bubbleDot Q * lambda Q p'
        + lambda Q p * w Q * fermionBosonCouplingFlow lambda bubbleDot irreducible Q p' :=
  rfl

/-- Appendix D full-vertex flow obtained by adjoining Eq. (110c) to the exchange-vertex flow. -/
noncomputable def appendixDFullVertexFlow {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ)
    (irreducible : q → k → k → ℝ) : q → k → k → ℝ :=
  fullSBEVertexFlow w (bosonPropagatorFlow w lambda bubbleDot) lambda
    (fermionBosonCouplingFlow lambda bubbleDot irreducible) lambda
    (fermionBosonCouplingFlow lambda bubbleDot irreducible)
    (restFunctionFlow irreducible bubbleDot)

/-- The Appendix D full-vertex flow is the exchange flow plus the multiboson rest flow. -/
lemma appendixDFullVertexFlow_eq_exchange_add_rest {q k : Type*} [Fintype k]
    (w : q → ℝ) (lambda bubbleDot : q → k → ℝ)
    (irreducible : q → k → k → ℝ) (Q : q) (p p' : k) :
    appendixDFullVertexFlow w lambda bubbleDot irreducible Q p p' =
      appendixDExchangeVertexFlow w lambda bubbleDot irreducible Q p p'
        + restFunctionFlow irreducible bubbleDot Q p p' :=
  rfl

/-! ## R. Path-integral insertion bridge -/

/-- Internal configuration space for the one-loop Schwinger-Dyson contraction. -/
abbrev SDEContractionConfig (ι : Type*) := ι × ι

/-- Complex-valued path-integral observable associated to the SDE contraction
`G_ab K_{b i a j}` at fixed external indices `i,j`. -/
def sdeContractionObservable {ι : Type*}
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : SDEContractionConfig ι → ℂ :=
  fun ab => ((G ab.1 ab.2 * K ab.2 i ab.1 j : ℝ) : ℂ)

/-- Equal kernels give equal SDE contraction observables. -/
lemma sdeContractionObservable_eq_of_kernel_eq {ι : Type*}
    (G : TwoPoint ι) {K K' : FourPoint ι} (i j : ι) (hK : K = K') :
    sdeContractionObservable G K i j = sdeContractionObservable G K' i j := by
  rw [hK]

/-- Unnormalised path-integral SDE insertion using the shared
`MeasurePathIntegralModel.unnormalizedExpectation` API. -/
noncomputable def pathIntegralSDEUnnormalized
    {ι : Type*} [MeasurableSpace (SDEContractionConfig ι)]
    (M : MeasurePathIntegralModel (SDEContractionConfig ι))
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : ℂ :=
  M.unnormalizedExpectation (sdeContractionObservable G K i j)

/-- Kernel equality lifts to equality of unnormalised path-integral SDE insertions. -/
lemma pathIntegralSDEUnnormalized_eq_of_kernel_eq
    {ι : Type*} [MeasurableSpace (SDEContractionConfig ι)]
    (M : MeasurePathIntegralModel (SDEContractionConfig ι))
    (G : TwoPoint ι) {K K' : FourPoint ι} (i j : ι) (hK : K = K') :
    pathIntegralSDEUnnormalized M G K i j =
      pathIntegralSDEUnnormalized M G K' i j := by
  rw [hK]

/-- The SBE identity, Eq. (14), lifts from kernels to the path-integral insertion level. -/
lemma pathIntegralSBEUnnormalized_eq_conventional
    {ι : Type*} [Fintype ι] [MeasurableSpace (SDEContractionConfig ι)]
    (M : MeasurePathIntegralModel (SDEContractionConfig ι))
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    pathIntegralSDEUnnormalized M G D.exchangeKernel i j =
      pathIntegralSDEUnnormalized M G
        (weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex)
        i j := by
  exact pathIntegralSDEUnnormalized_eq_of_kernel_eq M G i j D.exchange_eq_weightedSDE

/-- Pull an SDE contraction observable back to a finite Wilson counting space.  The map `decode`
chooses which internal SDE contraction pair is represented by each finite path-integral mode. -/
def finiteWilsonSDEObservable {ι : Type*} (L : FiniteWilsonGaugeModel)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : Fin L.nPlaquettes → ℂ :=
  fun p => sdeContractionObservable G K i j (decode p)

/-- Source-coupled unnormalised finite Wilson expectation of an SDE insertion. -/
noncomputable def finiteWilsonSDESourceExpectation {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : ℂ :=
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  M.sourceCoupledUnnormalizedExpectation source (finiteWilsonSDEObservable L decode G K i j)

/-- The finite Wilson SDE source expectation is the finite counting sum supplied by the
path-integral infrastructure. -/
lemma finiteWilsonSDESourceExpectation_eq_finset_sum {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    finiteWilsonSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode G K i j =
      ∑ p : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight source p *
        finiteWilsonSDEObservable L decode G K i j p := by
  unfold finiteWilsonSDESourceExpectation
  exact L.sourceCoupledUnnormalizedExpectation_eq_finset_sum
    hbar hbar_pos hPlaquette_nonneg source (finiteWilsonSDEObservable L decode G K i j)

/-- Eq. (14) also identifies the source-coupled finite Wilson SBE insertion with the conventional
Schwinger-Dyson insertion. -/
lemma finiteWilsonSBESourceExpectation_eq_conventional
    {ι : Type*} [Fintype ι]
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    finiteWilsonSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode G D.exchangeKernel i j =
      finiteWilsonSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode G
          (weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex)
        i j := by
  rw [D.exchange_eq_weightedSDE]

/-- Differentiating the finite source-coupled SDE expectation inserts one additional finite
observable, using the source-derivative lemma from `FiniteWilsonGaugeModel`. -/
lemma finiteWilsonSDESourceDerivative_hasDerivAt_zero {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    HasDerivAt
      (fun t : ℂ =>
        finiteWilsonSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
          (fun p => t * source p) decode G K i j)
      ((L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).unnormalizedExpectation
        (fun p => source p * finiteWilsonSDEObservable L decode G K i j p)) 0 := by
  unfold finiteWilsonSDESourceExpectation
  simpa using
    L.sourceCoupledUnnormalizedExpectation_linearSource_hasDerivAt_zero
      hbar hbar_pos hPlaquette_nonneg source (finiteWilsonSDEObservable L decode G K i j)

/-- The connected generating functional differentiates to the normalised finite Wilson SDE
insertion.  This is the path-integral source version of extracting the SDE self-energy
observable. -/
lemma finiteWilsonSDEConnectedGeneratingFunctional_hasDerivAt_zero {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    HasDerivAt
      (fun t : ℂ =>
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).connectedGeneratingFunctional
          (fun p => t * finiteWilsonSDEObservable L decode G K i j p))
      ((L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).normalizedExpectation
        (finiteWilsonSDEObservable L decode G K i j)) 0 := by
  simpa using
    L.connectedGeneratingFunctional_linearSource_hasDerivAt_zero
      hbar hbar_pos hPlaquette_nonneg (finiteWilsonSDEObservable L decode G K i j)

/-! ## S. Caldeira-Leggett decoherence weighting -/

/-- A Caldeira-Leggett environment assigns each finite SDE insertion mode the suppression
`exp(-2 M gamma k_B T tau xi^2)`, with `xi` the mode's path separation. -/
noncomputable def caldeiraLeggettSBEWeight {η : Type*}
    (mass γ kB T τ : ℝ) (separation : η → ℝ) : η → ℝ :=
  fun p => caldeiraLeggettSuppression mass γ kB T τ (separation p)

/-- The SBE Caldeira-Leggett weight is exactly the repo's entropic Kuiken damping for the
imaginary action `hbar * phi`. -/
lemma caldeiraLeggettSBEWeight_eq_kuiken {η : Type*}
    (mass γ kB T τ hbar : ℝ) (hhbar : hbar ≠ 0) (separation : η → ℝ) (p : η) :
    caldeiraLeggettSBEWeight mass γ kB T τ separation p =
      Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight
        hbar
        (hbar * caldeiraLeggettDecoherence mass γ kB T τ (separation p)) := by
  exact caldeiraLeggettSuppression_eq_kuiken mass γ kB T τ (separation p) hbar hhbar

/-- Caldeira-Leggett weighting cannot amplify a finite SDE insertion mode when the environment
parameters are non-negative. -/
lemma caldeiraLeggettSBEWeight_le_one {η : Type*}
    (mass γ kB T τ : ℝ)
    (hmass : 0 ≤ mass) (hγ : 0 ≤ γ) (hkB : 0 ≤ kB) (hT : 0 ≤ T) (hτ : 0 ≤ τ)
    (separation : η → ℝ) (p : η) :
    caldeiraLeggettSBEWeight mass γ kB T τ separation p ≤ 1 :=
  caldeiraLeggettSuppression_le_one mass γ kB T τ (separation p) hmass hγ hkB hT hτ

/-- Caldeira-Leggett weighting of an SDE contraction observable.  This is the reduced
open-system version of the finite SDE insertion after tracing out an oscillator bath. -/
noncomputable def caldeiraLeggettSDEObservable {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : Fin L.nPlaquettes → ℂ :=
  fun p =>
    ((caldeiraLeggettSBEWeight mass γ kB T τ separation p : ℝ) : ℂ) *
      finiteWilsonSDEObservable L decode G K i j p

/-- If the path separation vanishes modewise, the Caldeira-Leggett weighted SDE observable
reduces to the original finite SDE observable. -/
lemma caldeiraLeggettSDEObservable_eq_original_of_zero_separation {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (hsep : ∀ p : Fin L.nPlaquettes, separation p = 0)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    caldeiraLeggettSDEObservable L decode mass γ kB T τ separation G K i j =
      finiteWilsonSDEObservable L decode G K i j := by
  funext p
  simp [caldeiraLeggettSDEObservable, caldeiraLeggettSBEWeight, hsep p,
    caldeiraLeggettSuppression_diagonal]

/-- Source-coupled finite Wilson expectation of a Caldeira-Leggett weighted SDE insertion. -/
noncomputable def finiteWilsonCaldeiraLeggettSDESourceExpectation {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : ℂ :=
  let PI := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  PI.sourceCoupledUnnormalizedExpectation source
    (caldeiraLeggettSDEObservable L decode mass γ kB T τ separation G K i j)

/-- The Caldeira-Leggett weighted finite Wilson SDE expectation is a finite source-coupled
path-integral sum. -/
lemma finiteWilsonCaldeiraLeggettSDESourceExpectation_eq_finset_sum {ι : Type*}
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    finiteWilsonCaldeiraLeggettSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode mass γ kB T τ separation G K i j =
      ∑ p : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight source p *
          caldeiraLeggettSDEObservable L decode mass γ kB T τ separation G K i j p := by
  unfold finiteWilsonCaldeiraLeggettSDESourceExpectation
  exact L.sourceCoupledUnnormalizedExpectation_eq_finset_sum
    hbar hbar_pos hPlaquette_nonneg source
    (caldeiraLeggettSDEObservable L decode mass γ kB T τ separation G K i j)

/-- Eq. (14) continues to identify the SBE and conventional Schwinger-Dyson insertions after
Caldeira-Leggett decoherence weighting. -/
lemma finiteWilsonCaldeiraLeggettSBE_eq_conventional
    {ι : Type*} [Fintype ι]
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    finiteWilsonCaldeiraLeggettSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode mass γ kB T τ separation G D.exchangeKernel i j =
      finiteWilsonCaldeiraLeggettSDESourceExpectation L hbar hbar_pos hPlaquette_nonneg
        source decode mass γ kB T τ separation G
          (weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex)
        i j := by
  rw [D.exchange_eq_weightedSDE]

/-! ## T. Faddeev-Popov ghost-complex weighting -/

/-- A finite Faddeev-Popov ghost complex.  The first map is the finite gauge-variation
operator `delta G / delta alpha`; the second map records the next BRST differential, with
nilpotence stated as `d_next (d_FP alpha) = 0`. -/
structure FaddeevPopovGhostComplex (n : ℕ) where
  /-- The finite Faddeev-Popov gauge-variation matrix. -/
  gaugeVariation : Matrix (Fin n) (Fin n) ℝ
  /-- The next finite BRST differential after the gauge-variation map. -/
  nextVariation : Matrix (Fin n) (Fin n) ℝ
  /-- The ghost-complex condition `d_next ∘ d_FP = 0`. -/
  square_zero : ∀ alpha : Fin n → ℝ, nextVariation.mulVec (gaugeVariation.mulVec alpha) = 0

/-- The gauge variation induced by a finite ghost complex, reusing the repository's
Faddeev-Popov operator from the QED path-integral construction. -/
def ghostComplexGaugeVariation {n : ℕ} (C : FaddeevPopovGhostComplex n)
    (A alpha : Fin n → ℝ) : Fin n → ℝ :=
  abelianGaugeVariation C.gaugeVariation A alpha

/-- The ghost-complex gauge variation is field-independent in the abelian finite model. -/
lemma ghostComplexGaugeVariation_field_independent {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A A' alpha : Fin n → ℝ) :
    ghostComplexGaugeVariation C A alpha = ghostComplexGaugeVariation C A' alpha :=
  abelian_FP_field_independent C.gaugeVariation A A' alpha

/-- The finite Faddeev-Popov determinant associated with the ghost complex. -/
def ghostComplexFPDeterminant {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A : Fin n → ℝ) : ℝ :=
  fpDeterminant C.gaugeVariation A

/-- In the abelian finite model, the ghost-complex determinant is independent of the gauge field. -/
lemma ghostComplexFPDeterminant_field_independent {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A A' : Fin n → ℝ) :
    ghostComplexFPDeterminant C A = ghostComplexFPDeterminant C A' :=
  abelian_FP_decouples C.gaugeVariation A A'

/-- Applying the next BRST differential after the ghost-complex gauge variation gives zero. -/
lemma ghostComplex_square_zero {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (alpha : Fin n → ℝ) :
    C.nextVariation.mulVec (C.gaugeVariation.mulVec alpha) = 0 :=
  C.square_zero alpha

/-- Ghost-complex weighting of a finite SDE contraction observable.  Each finite path-integral
mode is multiplied by the Faddeev-Popov determinant supplied by the ghost complex. -/
noncomputable def ghostComplexSDEObservable {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : Fin L.nPlaquettes → ℂ :=
  fun p =>
    ((ghostComplexFPDeterminant C (gaugeField p) : ℝ) : ℂ) *
      finiteWilsonSDEObservable L decode G K i j p

/-- Abelian ghost-complex weighting reduces to multiplication by a fixed determinant. -/
lemma ghostComplexSDEObservable_eq_constant_fp {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ) (A0 : Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    ghostComplexSDEObservable C L gaugeField decode G K i j =
      fun p => ((ghostComplexFPDeterminant C A0 : ℝ) : ℂ) *
        finiteWilsonSDEObservable L decode G K i j p := by
  funext p
  have hfp : ghostComplexFPDeterminant C (gaugeField p) = ghostComplexFPDeterminant C A0 :=
    ghostComplexFPDeterminant_field_independent C (gaugeField p) A0
  simp [ghostComplexSDEObservable, hfp]

/-- Source-coupled finite Wilson expectation of a ghost-complex weighted SDE insertion. -/
noncomputable def finiteWilsonGhostComplexSDESourceExpectation {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : ℂ :=
  let PI := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  PI.sourceCoupledUnnormalizedExpectation source
    (ghostComplexSDEObservable C L gaugeField decode G K i j)

/-- The ghost-complex weighted finite Wilson SDE expectation is the corresponding finite
source-coupled path-integral sum. -/
lemma finiteWilsonGhostComplexSDESourceExpectation_eq_finset_sum {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) :
    finiteWilsonGhostComplexSDESourceExpectation C L hbar hbar_pos hPlaquette_nonneg
        source gaugeField decode G K i j =
      ∑ p : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight source p *
          ghostComplexSDEObservable C L gaugeField decode G K i j p := by
  unfold finiteWilsonGhostComplexSDESourceExpectation
  exact L.sourceCoupledUnnormalizedExpectation_eq_finset_sum hbar hbar_pos
    hPlaquette_nonneg source (ghostComplexSDEObservable C L gaugeField decode G K i j)

/-- Eq. (14) continues to identify the SBE and conventional Schwinger-Dyson insertions after
ghost-complex Faddeev-Popov weighting. -/
lemma finiteWilsonGhostComplexSBE_eq_conventional
    {ι : Type*} [Fintype ι] {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    finiteWilsonGhostComplexSDESourceExpectation C L hbar hbar_pos hPlaquette_nonneg
        source gaugeField decode G D.exchangeKernel i j =
      finiteWilsonGhostComplexSDESourceExpectation C L hbar hbar_pos hPlaquette_nonneg
        source gaugeField decode G
          (weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex)
        i j := by
  rw [D.exchange_eq_weightedSDE]

/-- Combined ghost-complex and Caldeira-Leggett weighting of a finite SDE contraction
observable.  The first factor is the Faddeev-Popov determinant; the second factor is the
thermal-bath decoherence suppression. -/
noncomputable def ghostCaldeiraLeggettSDEObservable {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : Fin L.nPlaquettes → ℂ :=
  fun p =>
    ((ghostComplexFPDeterminant C (gaugeField p) : ℝ) : ℂ) *
      caldeiraLeggettSDEObservable L decode mass γ kB T τ separation G K i j p

/-- Source-coupled finite Wilson expectation with both ghost-complex and Caldeira-Leggett
weights. -/
noncomputable def finiteWilsonGhostCaldeiraLeggettSDESourceExpectation {ι : Type*} {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (K : FourPoint ι) (i j : ι) : ℂ :=
  let PI := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  PI.sourceCoupledUnnormalizedExpectation source
    (ghostCaldeiraLeggettSDEObservable C L gaugeField decode mass γ kB T τ separation G K i j)

/-- Eq. (14) is stable under the combined ghost-complex and Caldeira-Leggett path-integral
weights. -/
lemma finiteWilsonGhostCaldeiraLeggettSBE_eq_conventional
    {ι : Type*} [Fintype ι] {n : ℕ}
    (C : FaddeevPopovGhostComplex n)
    (L : FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ p : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction p)
    (source : Fin L.nPlaquettes → ℂ)
    (gaugeField : Fin L.nPlaquettes → Fin n → ℝ)
    (decode : Fin L.nPlaquettes → SDEContractionConfig ι)
    (mass γ kB T τ : ℝ) (separation : Fin L.nPlaquettes → ℝ)
    (G : TwoPoint ι) (D : SingleBosonExchangeData ι) (i j : ι) :
    finiteWilsonGhostCaldeiraLeggettSDESourceExpectation C L hbar hbar_pos hPlaquette_nonneg
        source gaugeField decode mass γ kB T τ separation G D.exchangeKernel i j =
      finiteWilsonGhostCaldeiraLeggettSDESourceExpectation C L hbar hbar_pos hPlaquette_nonneg
        source gaugeField decode mass γ kB T τ separation G
          (weightedSDEKernel D.channel D.coefficient D.bareInteraction D.bubble D.fullVertex)
        i j := by
  rw [D.exchange_eq_weightedSDE]

end Physlib.QFT.HamiltonianRenormalisation

end
