/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Lindblad.GreensFunction
public import Physlib.QuantumMechanics.QuantumChannel.Basic

/-!
# Weinberg 2012: collapse of the state vector

This file formalizes the finite-state algebraic core of Steven Weinberg,
*Collapse of the state vector*, Phys. Rev. A **85**, 062116 (2012).

The paper's analytic setting is a probability density `P(ψ,t)` on Hilbert-space
state vectors with evolution

`dP(ψ',t)/dt = ∫ K(ψ',ψ) P(ψ,t) dψ`  -- Weinberg eq. (3).

Here we isolate the parts that have a clean theorem-level finite version:

* the kernel action `K P`;
* column-sum conservation as total-probability conservation, Weinberg eq. (20);
* left zero modes as conserved Born weights, Weinberg eqs. (18)-(19);
* the zero-mode collapse formula, Weinberg eqs. (14), (16), with a dual
  pointer/weight basis;
* deterministic quantum jumps as the finite version of Weinberg eqs. (27)-(30);
* density-matrix closure, Weinberg eqs. (31)-(34): if bilinear observables are
  invariant under the left action of `K`, then their density elements obey a
  closed linear equation;
* the existing Lindblad jump-rate infrastructure supplies a canonical
  non-negative Weinberg jump rate.


-/

set_option autoImplicit false

open BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse

open Physlib.QuantumMechanics.Lindblad.GreensFunction

/-- A finite probability density over the state-vector sample space. -/
abbrev ProbabilityDensity (Ω : Type*) := Ω → ℝ

/-- A finite collapse generator.  The first argument is the arrival state `ψ'`;
the second argument is the source state `ψ`, matching Weinberg's `K_{ψ',ψ}`. -/
abbrev CollapseKernel (Ω : Type*) := Ω → Ω → ℝ

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The finite version of Weinberg eq. (3): `(K P)(ψ') = Σ_ψ K_{ψ',ψ} P(ψ)`. -/
def kernelAction (K : CollapseKernel Ω) (P : ProbabilityDensity Ω) :
    ProbabilityDensity Ω :=
  fun ψ' => ∑ ψ : Ω, K ψ' ψ * P ψ

/-- The left action of `K` on an observable/function `g`, finite version of
`∫ dψ' g(ψ') K_{ψ',ψ}`. -/
def leftAction (K : CollapseKernel Ω) (g : Ω → ℝ) : Ω → ℝ :=
  fun ψ => ∑ ψ' : Ω, g ψ' * K ψ' ψ

/-- A left zero mode of the collapse generator, Weinberg eq. (18). -/
def leftZeroMode (K : CollapseKernel Ω) (g : Ω → ℝ) : Prop :=
  ∀ ψ : Ω, leftAction K g ψ = 0

/-- Column-sum conservation of the kernel, Weinberg eq. (20). -/
def columnConservative (K : CollapseKernel Ω) : Prop :=
  ∀ ψ : Ω, ∑ ψ' : Ω, K ψ' ψ = 0

/-- Total probability mass. -/
def totalMass (P : ProbabilityDensity Ω) : ℝ := ∑ ψ : Ω, P ψ

/-- Expectation of an observable/function `g` against a density `P`. -/
def expectation (g : Ω → ℝ) (P : ProbabilityDensity Ω) : ℝ :=
  ∑ ψ : Ω, g ψ * P ψ

/-- **Adjointness of the finite kernel action.**  This is the algebra behind
Weinberg eqs. (18)-(19): the expectation of `g` against `K P` is the expectation
of the left action of `K` on `g` against `P`. -/
lemma expectation_kernelAction_eq_leftAction
    (K : CollapseKernel Ω) (g : Ω → ℝ) (P : ProbabilityDensity Ω) :
    expectation g (kernelAction K P) = ∑ ψ : Ω, leftAction K g ψ * P ψ := by
  unfold expectation kernelAction leftAction
  calc
    ∑ ψ' : Ω, g ψ' * (∑ ψ : Ω, K ψ' ψ * P ψ)
        = ∑ ψ' : Ω, ∑ ψ : Ω, g ψ' * (K ψ' ψ * P ψ) := by
          exact Finset.sum_congr rfl fun ψ' _ => Finset.mul_sum _ _ _
    _ = ∑ ψ : Ω, ∑ ψ' : Ω, g ψ' * (K ψ' ψ * P ψ) := Finset.sum_comm
    _ = ∑ ψ : Ω, (∑ ψ' : Ω, g ψ' * K ψ' ψ) * P ψ := by
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun ψ' _ => by ring

/-- **Weinberg eq. (20): column conservation implies conservation of total
probability at the infinitesimal level.** -/
lemma totalMass_kernelAction_eq_zero_of_columnConservative
    (K : CollapseKernel Ω) (P : ProbabilityDensity Ω) (hK : columnConservative K) :
    totalMass (kernelAction K P) = 0 := by
  unfold totalMass kernelAction columnConservative at *
  calc
    ∑ ψ' : Ω, ∑ ψ : Ω, K ψ' ψ * P ψ
        = ∑ ψ : Ω, ∑ ψ' : Ω, K ψ' ψ * P ψ := Finset.sum_comm
    _ = ∑ ψ : Ω, (∑ ψ' : Ω, K ψ' ψ) * P ψ := by
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [Finset.sum_mul]
    _ = 0 := by
          simp [hK]

/-- **Weinberg eqs. (18)-(19): a left zero mode has conserved expectation.**
For the Born-rule choice `g_n(ψ)=|φ_n|²`, this is Weinberg's statement that
`P_n = ∫ |φ_n|² P(φ,t)dφ` is independent of time. -/
lemma expectation_kernelAction_eq_zero_of_leftZeroMode
    (K : CollapseKernel Ω) (g : Ω → ℝ) (P : ProbabilityDensity Ω)
    (hg : leftZeroMode K g) :
    expectation g (kernelAction K P) = 0 := by
  rw [expectation_kernelAction_eq_leftAction]
  unfold leftZeroMode at hg
  simp [hg]

/-! ## Born-rule zero-mode collapse -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Finite version of Weinberg's zero-mode collapse formula (eqs. (14), (16)):
the final distribution is a sum of pointer distributions weighted by the initial
Born coefficients. -/
def collapsedDistribution (pointer : A → Ω → ℝ) (weight : A → Ω → ℝ)
    (P : ProbabilityDensity Ω) : ProbabilityDensity Ω :=
  fun ψ => ∑ a : A, pointer a ψ * expectation (weight a) P

/-- Pointer distributions and Born weights are dual if `∫ g_a f_b = δ_ab`. -/
def dualPointerWeight (pointer : A → Ω → ℝ) (weight : A → Ω → ℝ) : Prop :=
  ∀ a b : A, ∑ ψ : Ω, weight a ψ * pointer b ψ = if a = b then 1 else 0

/-- **Born weights of the collapsed distribution are the initial Born weights.**
This is the finite theorem-level version of Weinberg's eqs. (14), (16): the
collapse basis `f_a` and Born weights `g_a` reproduce the Born coefficient
`∫ g_a(ψ)P(ψ,0)dψ`. -/
lemma collapsedDistribution_has_born_weights
    (pointer : A → Ω → ℝ) (weight : A → Ω → ℝ) (P : ProbabilityDensity Ω)
    (hdual : dualPointerWeight pointer weight) (a : A) :
    expectation (weight a) (collapsedDistribution pointer weight P)
      = expectation (weight a) P := by
  unfold expectation collapsedDistribution dualPointerWeight at *
  calc
    ∑ ψ : Ω, weight a ψ * (∑ b : A, pointer b ψ *
          (∑ φ : Ω, weight b φ * P φ))
        = ∑ ψ : Ω, ∑ b : A, weight a ψ *
          (pointer b ψ * (∑ φ : Ω, weight b φ * P φ)) := by
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ b : A, ∑ ψ : Ω, weight a ψ *
          (pointer b ψ * (∑ φ : Ω, weight b φ * P φ)) := Finset.sum_comm
    _ = ∑ b : A, (∑ ψ : Ω, weight a ψ * pointer b ψ) *
          (∑ φ : Ω, weight b φ * P φ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun ψ _ => by ring
    _ = ∑ b : A, (if a = b then (1 : ℝ) else 0) *
          (∑ φ : Ω, weight b φ * P φ) := by
          exact Finset.sum_congr rfl fun b _ => by rw [hdual a b]
    _ = ∑ φ : Ω, weight a φ * P φ := by
          simp

/-- **Weinberg Born-rule package.**  If the Born weights are left zero modes of
the kernel and the pointer basis is dual to them, then (i) each Born coefficient
is conserved under the collapse generator and (ii) the zero-mode collapse
distribution has exactly those Born coefficients. -/
lemma born_weights_conserved_and_recovered
    (K : CollapseKernel Ω) (pointer : A → Ω → ℝ) (weight : A → Ω → ℝ)
    (P : ProbabilityDensity Ω)
    (hzero : ∀ a : A, leftZeroMode K (weight a))
    (hdual : dualPointerWeight pointer weight) (a : A) :
    expectation (weight a) (kernelAction K P) = 0
      ∧ expectation (weight a) (collapsedDistribution pointer weight P)
          = expectation (weight a) P := by
  exact ⟨expectation_kernelAction_eq_zero_of_leftZeroMode K (weight a) P (hzero a),
    collapsedDistribution_has_born_weights pointer weight P hdual a⟩

/-! ## Weinberg quantum jumps -/

/-- Deterministic finite quantum-jump kernel, the no-random-parameter version of
Weinberg eq. (27):

`K_{ψ',ψ} = Γ (1_{ψ'=Jψ} - 1_{ψ'=ψ})`.

The sign convention matches `dP/dt = K P`: probability leaves `ψ` at rate `Γ`
and arrives at `J ψ` at rate `Γ`. -/
def deterministicJumpKernel (Γ : ℝ) (J : Ω → Ω) : CollapseKernel Ω :=
  fun ψ' ψ => Γ * ((if ψ' = J ψ then 1 else 0) - (if ψ' = ψ then 1 else 0))

/-- A deterministic jump kernel conserves total probability, the finite form of
`∫ K_{ψ',ψ}dψ' = 0`. -/
lemma deterministicJumpKernel_columnConservative (Γ : ℝ) (J : Ω → Ω) :
    columnConservative (deterministicJumpKernel Γ J) := by
  intro ψ
  unfold deterministicJumpKernel
  calc
    ∑ ψ' : Ω, Γ * ((if ψ' = J ψ then (1 : ℝ) else 0) -
        (if ψ' = ψ then (1 : ℝ) else 0))
        = Γ * (∑ ψ' : Ω, ((if ψ' = J ψ then (1 : ℝ) else 0) -
            (if ψ' = ψ then (1 : ℝ) else 0))) := by
          rw [Finset.mul_sum]
    _ = Γ * ((∑ ψ' : Ω, if ψ' = J ψ then (1 : ℝ) else 0) -
          (∑ ψ' : Ω, if ψ' = ψ then (1 : ℝ) else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
          simp

/-- **Finite Weinberg eq. (28).**  The left action of a deterministic jump kernel
on `g` is `Γ (g(Jψ)-g(ψ))`. -/
lemma deterministicJumpKernel_leftAction
    (Γ : ℝ) (J : Ω → Ω) (g : Ω → ℝ) (ψ : Ω) :
    leftAction (deterministicJumpKernel Γ J) g ψ = Γ * (g (J ψ) - g ψ) := by
  unfold leftAction deterministicJumpKernel
  simp [Finset.sum_sub_distrib, mul_sub, mul_comm]

/-- **Finite Weinberg eqs. (29)-(30).**  If a jump multiplies `g` by `η` under
pullback, then `g` is a left eigenfunction of the jump kernel with eigenvalue
`-Γ(1-η)`. -/
lemma deterministicJumpKernel_leftEigen_of_jumpMultiplier
    (Γ η : ℝ) (J : Ω → Ω) (g : Ω → ℝ)
    (hη : ∀ ψ : Ω, g (J ψ) = η * g ψ) (ψ : Ω) :
    leftAction (deterministicJumpKernel Γ J) g ψ = -(Γ * (1 - η)) * g ψ := by
  rw [deterministicJumpKernel_leftAction, hη ψ]
  ring

/-! ## Density-matrix closure, Weinberg eqs. (31)-(34) -/

variable {I : Type*} [Fintype I]

/-- A finite real-valued analogue of the bilinear density-matrix coordinate
`ψ_i ψ_j*` in Weinberg eq. (31). -/
abbrev DensityCoordinate (I Ω : Type*) := I → I → Ω → ℝ

/-- Density element associated to a bilinear coordinate. -/
def densityElement (B : DensityCoordinate I Ω) (P : ProbabilityDensity Ω) (i j : I) : ℝ :=
  expectation (B i j) P

/-- Weinberg eq. (33): the bilinear density coordinates are invariant under the
left action of `K`, with structure coefficients `κ`. -/
def densityClosure (K : CollapseKernel Ω) (B : DensityCoordinate I Ω)
    (κ : I → I → I → I → ℝ) : Prop :=
  ∀ i j : I, ∀ ψ : Ω,
    leftAction K (B i j) ψ = ∑ i' : I, ∑ j' : I, κ i j i' j' * B i' j' ψ

/-- **Weinberg eq. (33) implies eq. (34).**  If the bilinear coordinates close
under the left action of the collapse kernel, then the induced density elements
obey a closed linear equation with coefficients `κ`. -/
lemma densityElement_kernelAction_of_densityClosure
    (K : CollapseKernel Ω) (B : DensityCoordinate I Ω) (κ : I → I → I → I → ℝ)
    (P : ProbabilityDensity Ω) (hκ : densityClosure K B κ) (i j : I) :
    densityElement B (kernelAction K P) i j
      = ∑ i' : I, ∑ j' : I, κ i j i' j' * densityElement B P i' j' := by
  unfold densityElement
  rw [expectation_kernelAction_eq_leftAction]
  unfold densityClosure at hκ
  calc
    ∑ ψ : Ω, leftAction K (B i j) ψ * P ψ
        = ∑ ψ : Ω, (∑ i' : I, ∑ j' : I, κ i j i' j' * B i' j' ψ) * P ψ := by
          exact Finset.sum_congr rfl fun ψ _ => by rw [hκ i j ψ]
    _ = ∑ i' : I, ∑ j' : I, κ i j i' j' * (∑ ψ : Ω, B i' j' ψ * P ψ) := by
          calc
            ∑ ψ : Ω, (∑ i' : I, ∑ j' : I, κ i j i' j' * B i' j' ψ) * P ψ
                = ∑ ψ : Ω, ∑ i' : I, ∑ j' : I,
                    (κ i j i' j' * B i' j' ψ) * P ψ := by
                  refine Finset.sum_congr rfl fun ψ _ => ?_
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun i' _ => ?_
                  rw [Finset.sum_mul]
            _ = ∑ i' : I, ∑ ψ : Ω, ∑ j' : I,
                    (κ i j i' j' * B i' j' ψ) * P ψ := by
                  rw [Finset.sum_comm]
            _ = ∑ i' : I, ∑ j' : I, ∑ ψ : Ω,
                    (κ i j i' j' * B i' j' ψ) * P ψ := by
                  refine Finset.sum_congr rfl fun i' _ => ?_
                  rw [Finset.sum_comm]
            _ = ∑ i' : I, ∑ j' : I, κ i j i' j' *
                    (∑ ψ : Ω, B i' j' ψ * P ψ) := by
                  refine Finset.sum_congr rfl fun i' _ => ?_
                  refine Finset.sum_congr rfl fun j' _ => ?_
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun ψ _ => by ring

/-! ## Link to the existing Lindblad jump-rate infrastructure -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- The existing Lindblad rate `Γ = ‖Lψ‖²` supplies a canonical non-negative
Weinberg jump rate. -/
def lindbladWeinbergJumpKernel (L : H →L[ℂ] H) (ψ₀ : H) (J : Ω → Ω) :
    CollapseKernel Ω :=
  deterministicJumpKernel (lindbladRate L ψ₀) J

/-- The Lindblad-sourced Weinberg jump rate is non-negative by the existing
`L†L` positivity theorem. -/
lemma lindbladWeinbergJumpKernel_rate_nonneg
    (L : H →L[ℂ] H) (ψ₀ : H) :
    0 ≤ lindbladRate L ψ₀ :=
  lindbladRate_nonneg L ψ₀

/-- A Lindblad-sourced Weinberg jump kernel conserves total probability. -/
lemma lindbladWeinbergJumpKernel_columnConservative
    (L : H →L[ℂ] H) (ψ₀ : H) (J : Ω → Ω) :
    columnConservative (lindbladWeinbergJumpKernel L ψ₀ J) :=
  deterministicJumpKernel_columnConservative (lindbladRate L ψ₀) J

end Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse

end
