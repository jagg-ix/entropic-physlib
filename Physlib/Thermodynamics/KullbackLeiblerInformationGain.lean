/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.InformationChannelStress

/-!
# Information gain, KL divergence, entropy production, and involution kernels

Formalizes the finite/algebraic theorem kernel of A. O. Lopes and J. K.
Mengue, *On information gain, Kullback-Leibler divergence, entropy production
and the involution kernel*, arXiv:2003.02030v2.

The paper's full measurable-space results use probability kernels,
Radon-Nikodym derivatives, compact alphabets, Ruelle operators, and Lipschitz
involution kernels.  This module records the checked finite core that the rest
of physlib can directly consume:

* the Radon-Nikodym formula behind Theorem 10,
  `IG(pi, nuhat) = D_KL(pi || nuhat dQ)`;
* information gain as a KL / mutual-information payload measured in nats;
* the Markov entropy-production formula of Example 55;
* the finite potential-difference form of Proposition 50,
  `ep(mu) = integral (A - Aminus) dmu`;
* Corollary 52's zero-production statement for symmetric potentials;
* a bridge from specific information-gain rates to
  `InformationChannelStress`.

No measurable-space theorem is asserted without its analytic hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.Thermodynamics.KullbackLeiblerInformationGain

open Physlib.Thermodynamics.InformationChannelStress

/-! ## Finite KL divergence and probability-kernel information gain -/

/-- Finite Kullback-Leibler divergence in nats:
`D_KL(p || q) = sum_i p_i log (p_i / q_i)`. -/
def finiteKLDivergence {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- Two-coordinate finite KL divergence, useful for joint laws. -/
def finiteKLDivergence₂ {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * Real.log (p x y / q x y)

/-- The `X`-marginal of a finite joint mass. -/
def xMarginal {X Y : Type*} [Fintype Y] (joint : X → Y → ℝ) (x : X) : ℝ :=
  ∑ y, joint x y

/-- The `Y`-marginal of a finite joint mass. -/
def yMarginal {X Y : Type*} [Fintype X] (joint : X → Y → ℝ) (y : Y) : ℝ :=
  ∑ x, joint x y

/-- A finite probability kernel `nuhat` and a `Y`-marginal `Q` produce the joint
reference mass `nuhat^y(dx) dQ(y)`. -/
def finiteKernelJoint {X Y : Type*} (kernel : Y → X → ℝ) (Q : Y → ℝ)
    (x : X) (y : Y) : ℝ :=
  kernel y x * Q y

/-- Finite information gain relative to a probability kernel.  This is the
finite Radon-Nikodym form of paper Theorem 10:
`IG(pi, nuhat) = D_KL(pi || nuhat dQ)`. -/
def finiteKernelInformationGain {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X → Y → ℝ) (kernel : Y → X → ℝ) (Q : Y → ℝ) : ℝ :=
  finiteKLDivergence₂ joint (finiteKernelJoint kernel Q)

/-- Finite kernel entropy, defined by the paper's identity
`H^{nuhat}(pi) = -D_KL(pi || nuhat dQ)`. -/
def finiteKernelEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X → Y → ℝ) (kernel : Y → X → ℝ) (Q : Y → ℝ) : ℝ :=
  -finiteKernelInformationGain joint kernel Q

/-- Definition 21 / Theorem 10 in finite Radon-Nikodym form:
`IG(pi, nuhat) = -H^{nuhat}(pi)`. -/
theorem finiteKernelInformationGain_eq_neg_entropy
    {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X → Y → ℝ) (kernel : Y → X → ℝ) (Q : Y → ℝ) :
    finiteKernelInformationGain joint kernel Q =
      -finiteKernelEntropy joint kernel Q := by
  simp [finiteKernelEntropy]

/-- When the observed joint law is exactly the kernel-disintegrated reference
law, the finite information gain vanishes.  This is the finite checked form of
the paper statement that `IG(pi, nuhat) = 0` for `d pi = nuhat^y(dx) dQ(y)`. -/
theorem finiteKernelInformationGain_zero_of_kernel_joint
    {X Y : Type*} [Fintype X] [Fintype Y]
    (kernel : Y → X → ℝ) (Q : Y → ℝ)
    (href_ne : ∀ x y, finiteKernelJoint kernel Q x y ≠ 0) :
    finiteKernelInformationGain (finiteKernelJoint kernel Q) kernel Q = 0 := by
  unfold finiteKernelInformationGain finiteKLDivergence₂
  apply Finset.sum_eq_zero
  intro x _hx
  apply Finset.sum_eq_zero
  intro y _hy
  rw [div_self (href_ne x y)]
  simp

/-- Mutual information as KL divergence of a joint law from the product of its
marginals.  This is the finite version of paper Eq. (10). -/
def finiteMutualInformation {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X → Y → ℝ) : ℝ :=
  finiteKLDivergence₂ joint
    (fun x y => xMarginal joint x * yMarginal joint y)

/-- Information gain relative to the `X`-marginal is exactly mutual
information, by the paper's identification of mutual information with KL from
joint to product marginals. -/
theorem finiteInformationGain_eq_mutualInformation
    {X Y : Type*} [Fintype X] [Fintype Y] (joint : X → Y → ℝ) :
    finiteKLDivergence₂ joint
        (fun x y => xMarginal joint x * yMarginal joint y)
      = finiteMutualInformation joint := rfl

/-! ## Specific information gain as a channel rate -/

/-- Specific information gain / relative entropy rate: a block KL payload divided
by the block length.  In the paper this is the finite-block precursor of
`lim_n (1/n) H_{\Lambda_n}(eta | mu)`. -/
def specificInformationGainRate (blockKL blockLength : ℝ) : ℝ :=
  blockKL / blockLength

/-- A specific information-gain rate, measured in nats per step, as a
capacity-limited information channel. -/
def specificInformationGainChannel
    (capacityBitsPerTime blockKL blockLength : ℝ)
    (hC : 0 < capacityBitsPerTime)
    (hRate : 0 ≤ specificInformationGainRate blockKL blockLength) :
    InformationChannel :=
  channelFromKLRate capacityBitsPerTime
    (specificInformationGainRate blockKL blockLength) hC hRate

/-- The paper's specific information gain rate is within channel capacity exactly
when its nat-rate is bounded by `capacity * log 2`. -/
theorem specificInformationGainChannel_withinCapacity_iff
    (capacityBitsPerTime blockKL blockLength : ℝ)
    (hC : 0 < capacityBitsPerTime)
    (hRate : 0 ≤ specificInformationGainRate blockKL blockLength) :
    WithinCapacity
        (specificInformationGainChannel capacityBitsPerTime blockKL blockLength hC hRate)
      ↔ specificInformationGainRate blockKL blockLength
          ≤ capacityBitsPerTime * Real.log 2 := by
  unfold specificInformationGainChannel
  exact klChannel_withinCapacity_iff_natsRate_le capacityBitsPerTime
    (specificInformationGainRate blockKL blockLength) hC hRate

/-! ## Involution-kernel entropy production: finite potential form -/

/-- Finite potential-difference entropy production:
`ep(mu) = sum_x mu_x (A(x) - Aminus(x))`.

This is the finite/integral-free underlying space of paper Proposition 50.  The
involution kernel itself is the analytic tool that constructs `Aminus`; once
`Aminus` is available, the entropy-production formula is this expectation. -/
def finitePotentialEntropyProduction {S : Type*} [Fintype S]
    (mass : S → ℝ) (potential reversedPotential : S → ℝ) : ℝ :=
  ∑ s, mass s * (potential s - reversedPotential s)

/-- A potential is symmetric, in the paper's sense, when the involution-kernel
dual potential agrees with the original one after the conjugation. -/
def SymmetricPotential {S : Type*}
    (potential reversedPotential : S → ℝ) : Prop :=
  ∀ s, potential s = reversedPotential s

/-- Finite Proposition 50: entropy production is the expected potential
difference.  This theorem is named so downstream files can cite the paper formula
instead of rewriting it. -/
theorem finiteEntropyProduction_eq_potentialDifference
    {S : Type*} [Fintype S]
    (mass : S → ℝ) (potential reversedPotential : S → ℝ) :
    finitePotentialEntropyProduction mass potential reversedPotential =
      ∑ s, mass s * (potential s - reversedPotential s) := rfl

/-- Finite Corollary 52: if the potential is symmetric, entropy production is
zero. -/
theorem finiteEntropyProduction_zero_of_symmetric
    {S : Type*} [Fintype S]
    (mass : S → ℝ) (potential reversedPotential : S → ℝ)
    (hsym : SymmetricPotential potential reversedPotential) :
    finitePotentialEntropyProduction mass potential reversedPotential = 0 := by
  unfold finitePotentialEntropyProduction SymmetricPotential at *
  apply Finset.sum_eq_zero
  intro s _hs
  rw [hsym s]
  ring

/-! ## Markov entropy production, paper Example 55 -/

/-- Forward edge mass of a stationary Markov chain: `pi_i p_ij`. -/
def markovForwardEdgeMass {S : Type*}
    (stationary : S → ℝ) (transition : S → S → ℝ) (i j : S) : ℝ :=
  stationary i * transition i j

/-- Reversed edge mass: `pi_j p_ji`. -/
def markovReverseEdgeMass {S : Type*}
    (stationary : S → ℝ) (transition : S → S → ℝ) (i j : S) : ℝ :=
  stationary j * transition j i

/-- Markov detailed balance, `pi_i p_ij = pi_j p_ji`. -/
def MarkovDetailedBalance {S : Type*}
    (stationary : S → ℝ) (transition : S → S → ℝ) : Prop :=
  ∀ i j, markovForwardEdgeMass stationary transition i j =
    markovReverseEdgeMass stationary transition i j

/-- Markov entropy production from paper Example 55:
`sum_ij pi_i p_ij log ((pi_i p_ij)/(pi_j p_ji))`. -/
def markovEntropyProduction {S : Type*} [Fintype S]
    (stationary : S → ℝ) (transition : S → S → ℝ) : ℝ :=
  finiteKLDivergence₂
    (markovForwardEdgeMass stationary transition)
    (markovReverseEdgeMass stationary transition)

/-- The Markov formula is a KL divergence of the forward edge law against the
time-reversed edge law. -/
theorem markovEntropyProduction_eq_edgeKL
    {S : Type*} [Fintype S]
    (stationary : S → ℝ) (transition : S → S → ℝ) :
    markovEntropyProduction stationary transition =
      finiteKLDivergence₂
        (markovForwardEdgeMass stationary transition)
        (markovReverseEdgeMass stationary transition) := rfl

/-- Detailed balance forces zero entropy production, provided the reversed edge
masses in the log-ratio are non-zero.  This is the checked finite version of the
paper's reversible/detailed-balance case. -/
theorem markovEntropyProduction_zero_of_detailedBalance
    {S : Type*} [Fintype S]
    (stationary : S → ℝ) (transition : S → S → ℝ)
    (hdb : MarkovDetailedBalance stationary transition)
    (hrev_ne : ∀ i j, markovReverseEdgeMass stationary transition i j ≠ 0) :
    markovEntropyProduction stationary transition = 0 := by
  unfold markovEntropyProduction finiteKLDivergence₂ MarkovDetailedBalance at *
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro j _hj
  rw [hdb i j]
  rw [div_self (hrev_ne i j)]
  simp

/-- Symmetric transition weights with a constant stationary weight satisfy
detailed balance. -/
theorem detailedBalance_of_constant_stationary_symmetric_transition
    {S : Type*}
    (stationary : S → ℝ) (transition : S → S → ℝ)
    (hstationary_const : ∀ i j, stationary i = stationary j)
    (htransition_symm : ∀ i j, transition i j = transition j i) :
    MarkovDetailedBalance stationary transition := by
  intro i j
  unfold markovForwardEdgeMass markovReverseEdgeMass
  rw [hstationary_const i j, htransition_symm i j]

end Physlib.Thermodynamics.KullbackLeiblerInformationGain

end
