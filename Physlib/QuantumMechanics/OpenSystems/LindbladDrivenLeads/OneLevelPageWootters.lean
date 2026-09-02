/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelGibbsModular
public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.Lindblad.FullLindbladODE
meta import Zil

/-!
# The one-level carrier as a Page–Wootters conditional clock

This file identifies the matrix-level one-level carrier with the operator-level `Page–Wootters`
`DissipativeConditionalClock` on `EuclideanSpace ℂ Qubit`, closing the CLM↔MState step of the
constrained-carrier synthesis. The bridge is `Matrix.toEuclideanCLM`, the `*`-algebra isomorphism
`Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)`.

* **Intertwining** (`vonNeumannGen_toEuclideanCLM`): the Page–Wootters von Neumann generator
  `−(i/ℏ)[H_S, ρ]` on the operator algebra is the image under `toEuclideanCLM` of the matrix
  commutator `−(i/ℏ)(Aρ − ρA)` — the conditional Hamiltonian dynamics *is* the matrix von Neumann
  equation.
* **Frozen modular clock** (`oneLevelModularClock_vonNeumannGen_stationary`): with `H_S` the modular
  Hamiltonian of the thermal stationary state, the conditional Hamiltonian generator vanishes at
  `σ_f` — the modular clock is frozen at Gibbs equilibrium (reusing the matrix commutation
  `modularHamiltonian_commute_stationaryState`). More generally it vanishes on every diagonal state
  (`vonNeumannGen_diagonal`), so the Hamiltonian sector never moves populations.
* **The two experimental limits** (od6 Priority 4). With no dissipation (`𝓛_S = 0`,
  `oneLevelReversibleClock`) the conditional dynamics is the pure unitary modular flow — the
  Page–Wootters relational-photon regime. With no Hamiltonian (`H_S = 0`, `oneLevelDissipativeClock`)
  the generator is pure GKSL dissipation — the quantum-dot / superconducting-qubit relaxation regime.
  Both are instances of the same clock, discharged from the skeleton's degeneration lemmas.
The dissipative sector's non-negative rate functional `τ_ent = ∫ (1/ℏ)∑ⱼ‖Lⱼψ‖²` is the skeleton's
`dissipationRate` (already `≥ 0`, vanishing only where every jump annihilates `ψ`), the discrete form
of Spohn's `dS/dτ ≥ 0`; here it is carried by the `H_S = 0` limit above.

The closure below instantiates the explicit loss/gain GKSL superoperator, proves its exact complex-time
semigroup and infinitesimal-generator equations, identifies its nonnegative-real orbit with the full
bundled CPTP channel, and supplies a nonzero Page–Wootters constraint `H_S-H_C` with the nonzero
correlated physical history `|0,0⟩+|1,1⟩`.

Honest scope: the constrained carrier packages the exact conditional GKSL evolution and an explicit
physical history in the kernel of a nontrivial clock-system constraint. It does not claim that tracing
or conditioning this finite bipartite history dynamically derives the GKSL dissipator; that dilation /
conditioning theorem remains a separate open-system reconstruction. `βε = 0` (infinite temperature)
stays excluded from the thermal-frozen statement, as in the Gibbs–modular junction.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Physlib.QuantumMechanics.RelationalTime (DissipativeConditionalClock)
open QuantumMechanics.FiniteTarget (modularHamiltonianClm modularHamiltonianMat modularHamiltonianMat_mat)
open Physlib.QuantumMechanics.Lindblad (lindbladSingleJumpDissipator)
open Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.Thermodynamics.QuantumRelativeEntropyArrow
open QuantumInfo.Finite
open scoped RealInnerProductSpace

/-- The `*`-algebra isomorphism `Matrix Qubit Qubit ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] …)`. -/
local notation "𝔈" => (Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ))

/-! ## The `toEuclideanCLM` bridge intertwines commutators -/

/-- `toEuclideanCLM` sends matrix multiplication to operator composition. -/
theorem toEuclideanCLM_comp (A B : Matrix Qubit Qubit ℂ) :
    (𝔈 A) ∘L (𝔈 B) = 𝔈 (A * B) := by
  rw [map_mul]
  rfl

/-- **The `toEuclideanCLM` bridge intertwines the commutator**: the operator commutator of the images
is the image of the matrix commutator. -/
theorem toEuclideanCLM_commutator (A B : Matrix Qubit Qubit ℂ) :
    (𝔈 A) ∘L (𝔈 B) - (𝔈 B) ∘L (𝔈 A) = 𝔈 (A * B - B * A) := by
  rw [toEuclideanCLM_comp, toEuclideanCLM_comp, ← map_sub]

/-! ## The one-level Page–Wootters conditional clock -/

/-- The one-level Page–Wootters conditional clock: the modular Hamiltonian of the stationary state as
the Hermitian generator, together with a chosen GKSL dissipator `𝓛`. -/
def oneLevelModularClock (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)) :
    DissipativeConditionalClock (EuclideanSpace ℂ Qubit) where
  ℏ := ℏ
  ℏ_pos := hℏ
  H_S := modularHamiltonianClm d.stationaryState
  lindblad := 𝓛

/-- **The conditional von Neumann generator is the matrix von Neumann equation.** Under the
`toEuclideanCLM` bridge, the Page–Wootters Hamiltonian generator of the one-level clock at the image
of a density matrix `ρ` is the image of `−(i/ℏ)[K, ρ]`, where `K = -log σ_f` is the modular
Hamiltonian. -/
theorem oneLevelModularClock_vonNeumannGen (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit))
    (ρ : Matrix Qubit Qubit ℂ) :
    (oneLevelModularClock d ℏ hℏ 𝓛).vonNeumannGen (𝔈 ρ)
      = 𝔈 (-(Complex.I / (ℏ : ℂ)) •
          ((modularHamiltonianMat d.stationaryState).mat * ρ
            - ρ * (modularHamiltonianMat d.stationaryState).mat)) := by
  rw [DissipativeConditionalClock.vonNeumannGen]
  show (-(Complex.I / (ℏ : ℂ))) •
      ((modularHamiltonianClm d.stationaryState) ∘L (𝔈 ρ)
        - (𝔈 ρ) ∘L (modularHamiltonianClm d.stationaryState)) = _
  rw [modularHamiltonianClm, toEuclideanCLM_commutator, ← map_smul]

/-- **The Hamiltonian sector leaves diagonal populations invariant.** Because the modular Hamiltonian
is diagonal, its conditional von Neumann generator vanishes on every diagonal density matrix. -/
theorem oneLevelModularClock_vonNeumannGen_diagonal (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit))
    (g : Qubit → ℂ) :
    (oneLevelModularClock d ℏ hℏ 𝓛).vonNeumannGen (𝔈 (Matrix.diagonal g)) = 0 := by
  rw [oneLevelModularClock_vonNeumannGen]
  have hcomm : Commute (modularHamiltonianMat d.stationaryState).mat (Matrix.diagonal g) := by
    have h1 : (modularHamiltonianMat d.stationaryState).mat
        = -(HermitianMat.diagonal ℂ
              (fun i => Real.log (![1 - d.occupation, d.occupation] i))).mat := by
      rw [modularHamiltonianMat_mat, stationaryState_M_log d]
    rw [h1, HermitianMat.diagonal_mat]
    exact (Matrix.commute_diagonal _ _).neg_left
  rw [hcomm.eq, sub_self, smul_zero, map_zero]

/-- **The modular clock is frozen at Gibbs equilibrium.** The conditional Hamiltonian generator of the
one-level clock vanishes at the stationary state — reversible modular time accrues no evolution at
equilibrium, in contrast with the strictly-flowing dissipative entropic clock. -/
theorem oneLevelModularClock_vonNeumannGen_stationary (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)) :
    (oneLevelModularClock d ℏ hℏ 𝓛).vonNeumannGen (𝔈 d.stationaryState.m) = 0 := by
  rw [stationaryState_m_diagonal]
  exact oneLevelModularClock_vonNeumannGen_diagonal d ℏ hℏ 𝓛 _

/-! ## The two experimental limits (od6 Priority 4) -/

/-- **The reversible (dissipationless) limit** `𝓛_S = 0`: the pure unitary modular flow — the
Page–Wootters relational-clock regime (Moreva-type photon experiments). -/
def oneLevelReversibleClock (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    DissipativeConditionalClock (EuclideanSpace ℂ Qubit) :=
  oneLevelModularClock d ℏ hℏ 0

/-- In the reversible limit the full GKSL generator collapses to the von Neumann (modular) generator. -/
theorem oneLevelReversibleClock_gksLGen (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (ρ : EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit) :
    (oneLevelReversibleClock d ℏ hℏ).gksLGen ρ = (oneLevelReversibleClock d ℏ hℏ).vonNeumannGen ρ :=
  DissipativeConditionalClock.gksLGen_eq_vonNeumannGen_of_lindblad_zero _ ρ rfl

/-- **The reversible clock is frozen at Gibbs equilibrium**: its full generator vanishes at `σ_f`. -/
theorem oneLevelReversibleClock_gksLGen_stationary (d : OneLevelChannelData) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (oneLevelReversibleClock d ℏ hℏ).gksLGen (𝔈 d.stationaryState.m) = 0 := by
  rw [oneLevelReversibleClock_gksLGen]
  exact oneLevelModularClock_vonNeumannGen_stationary d ℏ hℏ 0

/-- **The dissipation-only limit** `H_S = 0` (phase-averaged): the conditional generator is pure GKSL
dissipation — the quantum-dot / superconducting-qubit population-relaxation regime. -/
def oneLevelDissipativeClock (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)) :
    DissipativeConditionalClock (EuclideanSpace ℂ Qubit) where
  ℏ := ℏ
  ℏ_pos := hℏ
  H_S := 0
  lindblad := 𝓛

/-- In the dissipation-only limit the full GKSL generator is exactly the dissipator. -/
theorem oneLevelDissipativeClock_gksLGen (ℏ : ℝ) (hℏ : 0 < ℏ)
    (𝓛 : (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
          →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit))
    (ρ : EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit) :
    (oneLevelDissipativeClock ℏ hℏ 𝓛).gksLGen ρ = 𝓛 ρ := by
  rw [DissipativeConditionalClock.gksLGen,
    DissipativeConditionalClock.vonNeumannGen_eq_zero_of_H_S_zero _ ρ rfl, zero_add]
  rfl

/-! ## Explicit loss/gain GKSL generator -/

/-- The fermionic loss jump `σ⁻ = |0⟩⟨1|`. -/
def oneLevelLossJump : Matrix Qubit Qubit ℂ :=
  !![(0 : ℂ), 1; 0, 0]

/-- The fermionic gain jump `σ⁺ = |1⟩⟨0|`. -/
def oneLevelGainJump : Matrix Qubit Qubit ℂ :=
  !![(0 : ℂ), 0; 1, 0]

/-- The actual one-level loss/gain GKSL generator, in the convention
`𝓓₂[J](ρ) = 2JρJ† - J†Jρ - ρJ†J`.

It reuses the repository's standard single-jump dissipator
`𝓓[J](ρ) = JρJ† - ½{J†J,ρ}` and hence is exactly
`2 lossRate · 𝓓[σ⁻] + 2 gainRate · 𝓓[σ⁺]`. -/
def oneLevelGKSLMatrix (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  ((2 * lossRate r : ℝ) : ℂ) • lindbladSingleJumpDissipator oneLevelLossJump ρ +
    ((2 * gainRate r : ℝ) : ℂ) • lindbladSingleJumpDissipator oneLevelGainJump ρ

set_option maxHeartbeats 800000 in
/-- Entrywise normal form of the one-level GKSL generator. Populations relax
at rate `2γ`, while coherences decay at rate `γ`. -/
theorem oneLevelGKSLMatrix_eq (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLMatrix r ρ =
      !![
        (((2 * lossRate r : ℝ) : ℂ) * ρ 1 1 -
          ((2 * gainRate r : ℝ) : ℂ) * ρ 0 0),
        -((r.gamma : ℂ) * ρ 0 1);
        -((r.gamma : ℂ) * ρ 1 0),
        (((2 * gainRate r : ℝ) : ℂ) * ρ 0 0 -
          ((2 * lossRate r : ℝ) : ℂ) * ρ 1 1)
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneLevelGKSLMatrix, oneLevelLossJump, oneLevelGainJump,
      lindbladSingleJumpDissipator, QuantumMechanics.FiniteTarget.anticommutator,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      lossRate, gainRate] <;>
    ring

/-! ## Pure-dephasing separation -/

/-- The number-projector jump used for pure dephasing.  Its amplitude is
`√γφ`; the doubled dissipator convention below makes the off-diagonal decay
rate exactly `γφ`. -/
def oneLevelPureDephasingJump (γφ : ℝ) : Matrix Qubit Qubit ℂ :=
  !![(0 : ℂ), 0; 0, ((Real.sqrt γφ : ℝ) : ℂ)]

/-- Pure number dephasing in the same doubled-dissipator convention as the
loss/gain generator. -/
def oneLevelPureDephasingMatrix (γφ : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  (2 : ℂ) • lindbladSingleJumpDissipator
    (oneLevelPureDephasingJump γφ) ρ

set_option maxHeartbeats 800000 in
/-- Pure dephasing leaves both populations untouched and damps each coherence
at rate `γφ`.  This is the formal separation required before a linewidth may
be compared with population relaxation. -/
theorem oneLevelPureDephasingMatrix_eq (γφ : ℝ) (hγφ : 0 ≤ γφ)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelPureDephasingMatrix γφ ρ =
      !![(0 : ℂ), -((γφ : ℂ) * ρ 0 1);
          -((γφ : ℂ) * ρ 1 0), 0] := by
  have hsqrt : Real.sqrt γφ ^ 2 = γφ := Real.sq_sqrt hγφ
  have hsqrtC : (((Real.sqrt γφ : ℝ) : ℂ) ^ 2) = (γφ : ℂ) := by
    exact_mod_cast hsqrt
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneLevelPureDephasingMatrix, oneLevelPureDephasingJump,
      lindbladSingleJumpDissipator, QuantumMechanics.FiniteTarget.anticommutator,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring_nf <;> simp [hsqrtC]

/-- Loss/gain relaxation plus an independently calibrated pure-dephasing
rate. -/
def oneLevelGKSLWithPureDephasingMatrix
    (r : RateData) (γφ : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  oneLevelGKSLMatrix r ρ + oneLevelPureDephasingMatrix γφ ρ

/-- Entrywise normal form of the dephasing-aware generator.  The population
rate remains `2γ`, whereas the coherence rate is `γ+γφ`. -/
theorem oneLevelGKSLWithPureDephasingMatrix_eq
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLWithPureDephasingMatrix r γφ ρ =
      !![
        (((2 * lossRate r : ℝ) : ℂ) * ρ 1 1 -
          ((2 * gainRate r : ℝ) : ℂ) * ρ 0 0),
        -(((r.gamma + γφ : ℝ) : ℂ) * ρ 0 1);
        -(((r.gamma + γφ : ℝ) : ℂ) * ρ 1 0),
        (((2 * gainRate r : ℝ) : ℂ) * ρ 0 0 -
          ((2 * lossRate r : ℝ) : ℂ) * ρ 1 1)
      ] := by
  rw [oneLevelGKSLWithPureDephasingMatrix, oneLevelGKSLMatrix_eq,
    oneLevelPureDephasingMatrix_eq γφ hγφ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Pure dephasing does not enter the excited-population equation. -/
theorem oneLevelGKSLWithPureDephasing_population_eq
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLWithPureDephasingMatrix r γφ ρ 1 1 =
      oneLevelGKSLMatrix r ρ 1 1 := by
  rw [oneLevelGKSLWithPureDephasingMatrix_eq r γφ hγφ,
    oneLevelGKSLMatrix_eq]
  rfl

/-- Pure dephasing adds to, rather than masquerades as, the loss/gain
coherence decay rate. -/
theorem oneLevelGKSLWithPureDephasing_coherence_eq
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLWithPureDephasingMatrix r γφ ρ 0 1 =
      -(((r.gamma + γφ : ℝ) : ℂ) * ρ 0 1) := by
  rw [oneLevelGKSLWithPureDephasingMatrix_eq r γφ hγφ]
  rfl

/-- The explicit matrix generator is complex-linear. -/
def oneLevelGKSLLinearMap (r : RateData) :
    Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ where
  toFun := oneLevelGKSLMatrix r
  map_add' := by
    intro ρ σ
    rw [oneLevelGKSLMatrix_eq, oneLevelGKSLMatrix_eq, oneLevelGKSLMatrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' := by
    intro c ρ
    rw [oneLevelGKSLMatrix_eq, oneLevelGKSLMatrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Transport of the concrete matrix GKSL generator to the operator algebra
used by `DissipativeConditionalClock`. -/
def oneLevelGKSLClmLinearMap (r : RateData) :
    (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit)
      →ₗ[ℂ] (EuclideanSpace ℂ Qubit →L[ℂ] EuclideanSpace ℂ Qubit) where
  toFun A :=
    𝔈 (oneLevelGKSLLinearMap r
      ((Matrix.toEuclideanCLM (n := Qubit) (𝕜 := ℂ)).symm A))
  map_add' := by
    intro A B
    simp
  map_smul' := by
    intro c A
    simp

/-- The transported operator-algebra generator acts exactly as the matrix
loss/gain generator under `toEuclideanCLM`. -/
@[simp]
theorem oneLevelGKSLClmLinearMap_toEuclideanCLM (r : RateData)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLClmLinearMap r (𝔈 ρ) = 𝔈 (oneLevelGKSLMatrix r ρ) := by
  simp [oneLevelGKSLClmLinearMap, oneLevelGKSLLinearMap]

/-- The Page–Wootters dissipation-only clock instantiated with the actual
one-level loss/gain GKSL generator. -/
def oneLevelExplicitDissipativeClock (r : RateData) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    DissipativeConditionalClock (EuclideanSpace ℂ Qubit) :=
  oneLevelDissipativeClock ℏ hℏ (oneLevelGKSLClmLinearMap r)

/-- The instantiated Page–Wootters generator is exactly the concrete
loss/gain GKSL matrix generator under the matrix/operator bridge. -/
theorem oneLevelExplicitDissipativeClock_gksLGen
    (r : RateData) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (ρ : Matrix Qubit Qubit ℂ) :
    (oneLevelExplicitDissipativeClock r ℏ hℏ).gksLGen (𝔈 ρ) =
      𝔈 (oneLevelGKSLMatrix r ρ) := by
  rw [oneLevelExplicitDissipativeClock, oneLevelDissipativeClock_gksLGen]
  exact oneLevelGKSLClmLinearMap_toEuclideanCLM r ρ

/-! ## Exact continuous-time orbit -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The exact complex-time orbit of the one-level GKSL generator. On the
physical half-line `z = t ≥ 0`, it will be identified with the bundled CPTP
generalized-amplitude-damping channel. -/
def oneLevelGKSLOrbit (r : RateData) (z : ℂ) :
    Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ where
  toFun ρ :=
    let e₁ := Complex.exp (-(r.gamma : ℂ) * z)
    let e₂ := Complex.exp (-2 * (r.gamma : ℂ) * z)
    fun i j =>
      if i = 0 then
        if j = 0 then
          ((1 - r.occupation : ℝ) : ℂ) * (ρ 0 0 + ρ 1 1) +
            ((r.occupation : ℂ) * ρ 0 0 -
              ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1) * e₂
        else
          e₁ * ρ 0 1
      else
        if j = 0 then
          e₁ * ρ 1 0
        else
          (r.occupation : ℂ) * (ρ 0 0 + ρ 1 1) -
            ((r.occupation : ℂ) * ρ 0 0 -
              ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1) * e₂
  map_add' := by
    intro ρ σ
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' := by
    intro c ρ
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem oneLevelGKSLOrbit_apply_zero_zero
    (r : RateData) (z : ℂ) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r z ρ 0 0 =
      ((1 - r.occupation : ℝ) : ℂ) * (ρ 0 0 + ρ 1 1) +
        ((r.occupation : ℂ) * ρ 0 0 -
          ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1) *
            Complex.exp (-2 * (r.gamma : ℂ) * z) := by
  simp [oneLevelGKSLOrbit, LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem oneLevelGKSLOrbit_apply_zero_one
    (r : RateData) (z : ℂ) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r z ρ 0 1 =
      Complex.exp (-(r.gamma : ℂ) * z) * ρ 0 1 := by
  simp [oneLevelGKSLOrbit, LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem oneLevelGKSLOrbit_apply_one_zero
    (r : RateData) (z : ℂ) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r z ρ 1 0 =
      Complex.exp (-(r.gamma : ℂ) * z) * ρ 1 0 := by
  simp [oneLevelGKSLOrbit, LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem oneLevelGKSLOrbit_apply_one_one
    (r : RateData) (z : ℂ) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r z ρ 1 1 =
      (r.occupation : ℂ) * (ρ 0 0 + ρ 1 1) -
        ((r.occupation : ℂ) * ρ 0 0 -
          ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1) *
            Complex.exp (-2 * (r.gamma : ℂ) * z) := by
  simp [oneLevelGKSLOrbit, LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
/-- The exact GKSL orbit starts at the identity. -/
@[simp]
theorem oneLevelGKSLOrbit_zero (r : RateData) :
    oneLevelGKSLOrbit r 0 = LinearMap.id := by
  apply LinearMap.ext
  intro ρ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneLevelGKSLOrbit] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- **Semigroup composition.** Complex-time evolution by `z+w` equals
evolution by `w` followed by evolution by `z`. -/
theorem oneLevelGKSLOrbit_add (r : RateData) (z w : ℂ)
    (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r (z + w) ρ =
      oneLevelGKSLOrbit r z (oneLevelGKSLOrbit r w ρ) := by
  have h₁ :
      Complex.exp (-((r.gamma : ℂ) * (z + w))) =
        Complex.exp (-((r.gamma : ℂ) * z)) *
          Complex.exp (-((r.gamma : ℂ) * w)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h₂ :
      Complex.exp (-((2 : ℂ) * (r.gamma : ℂ) * (z + w))) =
        Complex.exp (-((2 : ℂ) * (r.gamma : ℂ) * z)) *
          Complex.exp (-((2 : ℂ) * (r.gamma : ℂ) * w)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oneLevelGKSLOrbit]
  all_goals first | rw [h₁] | rw [h₂]
  all_goals ring

/-- The population `(0,0)` component has the concrete GKSL derivative at the
origin. -/
theorem oneLevelGKSLOrbit_hasDerivAt_zero_zero
    (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    HasDerivAt (fun z : ℂ => oneLevelGKSLOrbit r z ρ 0 0)
      (oneLevelGKSLMatrix r ρ 0 0) 0 := by
  have h₁ : HasDerivAt
      (fun z : ℂ => Complex.exp (-(r.gamma : ℂ) * z))
      (-(r.gamma : ℂ)) 0 := by
    have hlin : HasDerivAt (fun z : ℂ => -(r.gamma : ℂ) * z)
        (-(r.gamma : ℂ)) 0 := by
      simpa using
        (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (-(r.gamma : ℂ))
    simpa using hlin.cexp
  have h₂ : HasDerivAt
      (fun z : ℂ => Complex.exp (-2 * (r.gamma : ℂ) * z))
      (-2 * (r.gamma : ℂ)) 0 := by
    have hlin : HasDerivAt (fun z : ℂ => -2 * (r.gamma : ℂ) * z)
        (-2 * (r.gamma : ℂ)) 0 := by
      simpa using
        (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (-2 * (r.gamma : ℂ))
    simpa using hlin.cexp
  rw [oneLevelGKSLMatrix_eq]
  convert
    (h₂.const_mul
      ((r.occupation : ℂ) * ρ 0 0 -
        ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1)).const_add
      (((1 - r.occupation : ℝ) : ℂ) * (ρ 0 0 + ρ 1 1)) using 1
  all_goals try simp [oneLevelGKSLOrbit, lossRate, gainRate]
  all_goals first | rfl | ring

set_option backward.isDefEq.respectTransparency false in
/-- The coherence `(0,1)` component has the concrete GKSL derivative at the
origin. -/
theorem oneLevelGKSLOrbit_hasDerivAt_zero_one
    (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    HasDerivAt (fun z : ℂ => oneLevelGKSLOrbit r z ρ 0 1)
      (oneLevelGKSLMatrix r ρ 0 1) 0 := by
  have hlin : HasDerivAt (fun z : ℂ => -(r.gamma : ℂ) * z)
      (-(r.gamma : ℂ)) 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (-(r.gamma : ℂ))
  have h := hlin.cexp.mul_const (ρ 0 1)
  rw [oneLevelGKSLMatrix_eq]
  simpa [oneLevelGKSLOrbit] using h

set_option backward.isDefEq.respectTransparency false in
/-- The coherence `(1,0)` component has the concrete GKSL derivative at the
origin. -/
theorem oneLevelGKSLOrbit_hasDerivAt_one_zero
    (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    HasDerivAt (fun z : ℂ => oneLevelGKSLOrbit r z ρ 1 0)
      (oneLevelGKSLMatrix r ρ 1 0) 0 := by
  have hlin : HasDerivAt (fun z : ℂ => -(r.gamma : ℂ) * z)
      (-(r.gamma : ℂ)) 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (-(r.gamma : ℂ))
  have h := hlin.cexp.mul_const (ρ 1 0)
  rw [oneLevelGKSLMatrix_eq]
  simpa [oneLevelGKSLOrbit] using h

/-- The population `(1,1)` component has the concrete GKSL derivative at the
origin. -/
theorem oneLevelGKSLOrbit_hasDerivAt_one_one
    (r : RateData) (ρ : Matrix Qubit Qubit ℂ) :
    HasDerivAt (fun z : ℂ => oneLevelGKSLOrbit r z ρ 1 1)
      (oneLevelGKSLMatrix r ρ 1 1) 0 := by
  have hlin : HasDerivAt (fun z : ℂ => -2 * (r.gamma : ℂ) * z)
      (-2 * (r.gamma : ℂ)) 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (-2 * (r.gamma : ℂ))
  have h₂ := hlin.cexp
  rw [oneLevelGKSLMatrix_eq]
  convert
    (h₂.const_mul
      ((r.occupation : ℂ) * ρ 0 0 -
        ((1 - r.occupation : ℝ) : ℂ) * ρ 1 1)).const_sub
      ((r.occupation : ℂ) * (ρ 0 0 + ρ 1 1)) using 1
  all_goals try simp [oneLevelGKSLOrbit, lossRate, gainRate]
  all_goals first | rfl | ring

set_option backward.isDefEq.respectTransparency false in
/-- On nonnegative real time, the exact GKSL semigroup is precisely the
already-bundled finite-time generalized-amplitude-damping CPTP channel. -/
theorem oneLevelGKSLOrbit_eq_oneLevelChannelAt
    (r : RateData) (t : ℝ) (ht : 0 ≤ t) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLOrbit r (t : ℂ) ρ =
      (r.oneLevelChannelAt t ht).map ρ := by
  change oneLevelGKSLOrbit r (t : ℂ) ρ =
    (oneLevelChannel (OneLevelChannelData.ofRateTime r t ht)).map ρ
  rw [oneLevelChannel_map_eq]
  have h₁ :
      Complex.exp (-(r.gamma : ℂ) * (t : ℂ)) =
        (Real.exp (-r.gamma * t) : ℂ) := by
    calc
      Complex.exp (-(r.gamma : ℂ) * (t : ℂ)) =
          Complex.exp ((-r.gamma * t : ℝ) : ℂ) := by
            congr 1
            push_cast
            ring
      _ = (Real.exp (-r.gamma * t) : ℂ) := (Complex.ofReal_exp _).symm
  have hsqrt :
      Real.sqrt (Real.exp (-2 * r.gamma * t)) =
        Real.exp (-r.gamma * t) := by
    rw [show Real.exp (-2 * r.gamma * t) =
      Real.exp (-r.gamma * t) ^ 2 by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hcoh :
      Complex.exp (-(r.gamma : ℂ) * (t : ℂ)) =
        (Real.sqrt (Real.exp (-2 * r.gamma * t)) : ℂ) := by
    rw [h₁, hsqrt]
  have hcoh'' :
      Complex.exp (-((r.gamma : ℂ) * (t : ℂ))) =
        (Real.sqrt (Real.exp (-(2 * r.gamma * t))) : ℂ) := by
    convert hcoh using 1 <;> ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [oneLevelGKSLOrbit, OneLevelChannelData.ofRateTime,
      OneLevelChannelData.survival, RateData.dampingProbability]
    ring
  · simp [oneLevelGKSLOrbit, OneLevelChannelData.ofRateTime,
      OneLevelChannelData.survival, RateData.dampingProbability]
    exact Or.inl hcoh''
  · simp [oneLevelGKSLOrbit, OneLevelChannelData.ofRateTime,
      OneLevelChannelData.survival, RateData.dampingProbability]
    exact Or.inl hcoh''
  · simp [oneLevelGKSLOrbit, OneLevelChannelData.ofRateTime,
      OneLevelChannelData.survival, RateData.dampingProbability]
    ring

/-! ## The bundled positive-time CPTP semigroup and interval Spohn law -/

/-- The exact one-level channels, indexed by nonnegative time, form a genuine
positive-time CPTP semigroup.  The proof does not reconstruct composition from
the Kraus coefficients: it transports the already-proved complex-time orbit
law through `oneLevelGKSLOrbit_eq_oneLevelChannelAt`. -/
noncomputable def RateData.oneLevelPositiveTimeSemigroup (r : RateData) :
    CPTPPositiveTimeSemigroup Qubit where
  channel := fun t => r.oneLevelChannelAt (t : ℝ) t.2
  channel_zero := by
    apply CPTPMap.ext
    apply LinearMap.ext
    intro ρ
    have h := oneLevelGKSLOrbit_eq_oneLevelChannelAt r 0 (by positivity) ρ
    simpa [CPTPMap.id_map] using h.symm
  channel_add := by
    intro s t
    apply CPTPMap.ext
    apply LinearMap.ext
    intro ρ
    change (r.oneLevelChannelAt ((s + t : NNReal) : ℝ) (s + t).2).map ρ =
      (r.oneLevelChannelAt (s : ℝ) s.2).map
        ((r.oneLevelChannelAt (t : ℝ) t.2).map ρ)
    rw [← oneLevelGKSLOrbit_eq_oneLevelChannelAt r ((s + t : NNReal) : ℝ) (s + t).2 ρ,
      ← oneLevelGKSLOrbit_eq_oneLevelChannelAt r (s : ℝ) s.2,
      ← oneLevelGKSLOrbit_eq_oneLevelChannelAt r (t : ℝ) t.2 ρ]
    simpa using
      (oneLevelGKSLOrbit_add r (((s : NNReal) : ℝ) : ℂ)
        (((t : NNReal) : ℝ) : ℂ) ρ)

set_option backward.isDefEq.respectTransparency false in
/-- The exact one-level channel family as a strongly continuous CPTP
semigroup. Continuity is proved entrywise from the explicit exponential orbit
and transported through the matrix-induced topology on mixed states. -/
noncomputable def RateData.oneLevelCPTPC0Semigroup (r : RateData) :
    CPTPC0Semigroup Qubit where
  toCPTPPositiveTimeSemigroup := r.oneLevelPositiveTimeSemigroup
  strong_continuous := by
    intro ρ
    rw [continuous_induced_rng]
    apply Continuous.subtype_mk
    change Continuous (fun t : NNReal =>
      (r.oneLevelPositiveTimeSemigroup.channel t ρ).m)
    apply continuous_matrix
    intro i j
    have hfun :
        (fun t : NNReal =>
          (r.oneLevelPositiveTimeSemigroup.channel t ρ).m i j) =
        (fun t : NNReal =>
          oneLevelGKSLOrbit r (((t : ℝ) : ℂ)) ρ.m i j) := by
      funext t
      rw [CPTPMap.mat_coe_eq_apply_mat]
      exact congrFun (congrFun
        (oneLevelGKSLOrbit_eq_oneLevelChannelAt
          r (t : ℝ) t.2 ρ.m).symm i) j
    change Continuous (fun t : NNReal =>
      (r.oneLevelPositiveTimeSemigroup.channel t ρ).m i j)
    rw [hfun]
    fin_cases i <;> fin_cases j <;>
      simp [oneLevelGKSLOrbit] <;> fun_prop

/-- Restrict a complex-time entry derivative of the exact orbit to the
nonnegative real half-line and obtain the right difference quotient required
by `CPTPC0Semigroup.HasInfinitesimalGenerator`. -/
private theorem oneLevelGKSLOrbit_entry_rightSlope
    (r : RateData) (ρ : Matrix Qubit Qubit ℂ) (i j : Qubit)
    (h : HasDerivAt (fun z : ℂ => oneLevelGKSLOrbit r z ρ i j)
      (oneLevelGKSLMatrix r ρ i j) 0) :
    Filter.Tendsto
      (fun t : NNReal => (((t : ℝ) : ℂ)⁻¹) •
        (oneLevelGKSLOrbit r (((t : ℝ) : ℂ)) ρ i j - ρ i j))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (oneLevelGKSLMatrix r ρ i j)) := by
  have hzero : oneLevelGKSLOrbit r 0 ρ i j = ρ i j := by
    have hz := congrArg (fun L => L ρ) (oneLevelGKSLOrbit_zero r)
    exact congrFun (congrFun hz i) j
  have hs := h.comp_ofReal.tendsto_slope_zero_right
  change Filter.Tendsto
    (fun t : ℝ => t⁻¹ •
      (oneLevelGKSLOrbit r ((0 + t : ℝ) : ℂ) ρ i j -
        oneLevelGKSLOrbit r (0 : ℂ) ρ i j))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds (oneLevelGKSLMatrix r ρ i j)) at hs
  let Fnn : Filter NNReal := nhdsWithin 0 (Set.Ioi 0)
  let Fr : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hmap : Filter.map (fun t : NNReal => (t : ℝ)) Fnn = Fr := by
    simpa [Fnn, Fr] using NNReal.map_coe_nhdsGT (0 : NNReal)
  have hsmap : Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (oneLevelGKSLOrbit r ((0 + t : ℝ) : ℂ) ρ i j -
          oneLevelGKSLOrbit r (0 : ℂ) ρ i j))
      (Filter.map (fun t : NNReal => (t : ℝ)) Fnn)
      (nhds (oneLevelGKSLMatrix r ρ i j)) := hmap.symm ▸ hs
  have hscomp := Filter.tendsto_map'_iff.mp hsmap
  simpa [Fnn, Function.comp_def, hzero] using hscomp

/-- **Right infinitesimal-generator identification.** The genuine one-level
`C₀` CPTP semigroup has exactly the explicit loss/gain GKSL matrix operator as
its right generator on every mixed state. -/
theorem RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator
    (r : RateData) :
    r.oneLevelCPTPC0Semigroup.HasInfinitesimalGenerator
      (oneLevelGKSLMatrix r) := by
  intro ρ
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hentry : ∀ t : NNReal,
      (r.oneLevelCPTPC0Semigroup.channel t ρ).m i j =
        oneLevelGKSLOrbit r (((t : ℝ) : ℂ)) ρ.m i j := by
    intro t
    rw [CPTPMap.mat_coe_eq_apply_mat]
    exact congrFun (congrFun
      (oneLevelGKSLOrbit_eq_oneLevelChannelAt
        r (t : ℝ) t.2 ρ.m).symm i) j
  change Filter.Tendsto
    (fun t : NNReal => (((t : ℝ) : ℂ)⁻¹) •
      ((r.oneLevelCPTPC0Semigroup.channel t ρ).m i j - ρ.m i j))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (oneLevelGKSLMatrix r ρ.m i j))
  simp_rw [hentry]
  fin_cases i <;> fin_cases j
  · exact oneLevelGKSLOrbit_entry_rightSlope r ρ.m 0 0
      (oneLevelGKSLOrbit_hasDerivAt_zero_zero r ρ.m)
  · exact oneLevelGKSLOrbit_entry_rightSlope r ρ.m 0 1
      (oneLevelGKSLOrbit_hasDerivAt_zero_one r ρ.m)
  · exact oneLevelGKSLOrbit_entry_rightSlope r ρ.m 1 0
      (oneLevelGKSLOrbit_hasDerivAt_one_zero r ρ.m)
  · exact oneLevelGKSLOrbit_entry_rightSlope r ρ.m 1 1
      (oneLevelGKSLOrbit_hasDerivAt_one_one r ρ.m)

/-- The reference state used by the continuous one-level semigroup.  It is
the same diagonal state `diag(1-f,f)` as every finite-time channel's fixed
state; the zero-time parameter is used only to reuse the existing constructor. -/
def RateData.continuousStationaryState (r : RateData) : MState Qubit :=
  (OneLevelChannelData.ofRateTime r 0 (by positivity)).stationaryState

/-- The continuous one-level semigroup fixes `diag(1-f,f)` at every
nonnegative time. -/
theorem RateData.oneLevelPositiveTimeSemigroup_stationary_fixed (r : RateData) :
    r.oneLevelPositiveTimeSemigroup.IsFixedPoint r.continuousStationaryState := by
  intro t
  have hstate :
      (OneLevelChannelData.ofRateTime r (t : ℝ) t.2).stationaryState =
        r.continuousStationaryState := by
    apply MState.ext_m
    rw [OneLevelChannelData.stationaryState_m]
    unfold RateData.continuousStationaryState
    rw [OneLevelChannelData.stationaryState_m]
    rfl
  change oneLevelChannel (OneLevelChannelData.ofRateTime r (t : ℝ) t.2)
    r.continuousStationaryState = r.continuousStationaryState
  rw [← hstate]
  exact oneLevelChannel_stationaryState_fixed
    (OneLevelChannelData.ofRateTime r (t : ℝ) t.2)

/-- Quantum relative entropy to the thermal fixed state is antitone along the
actual continuous one-level CPTP semigroup. -/
theorem RateData.oneLevelContinuousRelativeEntropy_antitone
    (r : RateData) (ρ : MState Qubit) :
    Antitone (fun t => entropicProperTime
      (r.oneLevelPositiveTimeSemigroup.stateAt ρ t)
      r.continuousStationaryState) :=
  r.oneLevelPositiveTimeSemigroup.relativeEntropy_antitone ρ
    r.continuousStationaryState
    r.oneLevelPositiveTimeSemigroup_stationary_fixed

/-- **Continuous interval Spohn cocycle for the actual one-level channel.**
Production on adjacent ordered intervals adds exactly, with the stationary
state fixed by the same physical semigroup. -/
theorem RateData.oneLevelIntervalSpohnProduction_cocycle
    (r : RateData) (ρ : MState Qubit) {s t u : NNReal}
    (hst : s ≤ t) (htu : t ≤ u) :
    r.oneLevelPositiveTimeSemigroup.intervalSpohnProduction ρ
        r.continuousStationaryState s t +
      r.oneLevelPositiveTimeSemigroup.intervalSpohnProduction ρ
        r.continuousStationaryState t u =
      r.oneLevelPositiveTimeSemigroup.intervalSpohnProduction ρ
        r.continuousStationaryState s u :=
  r.oneLevelPositiveTimeSemigroup.intervalSpohnProduction_cocycle ρ
    r.continuousStationaryState
    r.oneLevelPositiveTimeSemigroup_stationary_fixed hst htu

/-! ## Full coherence-carrying operator Spohn derivative -/

/-- Squared Bloch radius of a qubit with excited occupation `N` and
off-diagonal norm square `C`. -/
noncomputable def qubitBlochRadiusSq (N C : ℝ) : ℝ :=
  (1 - 2 * N) ^ 2 + 4 * C

/-- Bloch radius associated to an occupation/coherence pair. -/
noncomputable def qubitBlochRadius (N C : ℝ) : ℝ :=
  Real.sqrt (qubitBlochRadiusSq N C)

/-- Upper spectral weight `(1 + |r|)/2` of a qubit state. -/
noncomputable def qubitUpperEigenvalue (N C : ℝ) : ℝ :=
  (1 + qubitBlochRadius N C) / 2

/-- Closed real form of the qubit Umegaki relative entropy to
`diag(1-f,f)`.  Coherence enters through the Bloch radius and therefore
through the von Neumann entropy, rather than being discarded by pinching. -/
noncomputable def qubitOperatorRelativeEntropy (f N C : ℝ) : ℝ :=
  -Real.binEntropy (qubitUpperEigenvalue N C) -
    ((1 - N) * Real.log (1 - f) + N * Real.log f)

/-- The qubit von Neumann entropy is binary entropy at the upper Bloch
eigenvalue.  The proof is independent of the arbitrary finite reindexing used
by `HermitianMat.eigenvalues`: binary entropy is symmetric under `λ ↦ 1-λ`. -/
theorem Sᵥₙ_qubit_eq_binEntropy_bloch (ρ : MState Qubit) :
    Sᵥₙ ρ = Real.binEntropy
      (qubitUpperEigenvalue (excitedOccupation ρ)
        (Complex.normSq (ρ.m 0 1))) := by
  rw [Sᵥₙ_qubit]
  have hs := eigenvalues_sum ρ
  have hp := eigenvalues_prod ρ
  have hrad :
      qubitBlochRadiusSq (excitedOccupation ρ) (Complex.normSq (ρ.m 0 1)) =
        (ρ.M.H.eigenvalues 0 - ρ.M.H.eigenvalues 1) ^ 2 := by
    simp only [qubitBlochRadiusSq]
    nlinarith
  rcases le_total (ρ.M.H.eigenvalues 1) (ρ.M.H.eigenvalues 0) with hge | hle
  · simp only [qubitUpperEigenvalue, qubitBlochRadius, hrad,
      Real.sqrt_sq (sub_nonneg.mpr hge)]
    congr 1
    linarith
  · simp only [qubitUpperEigenvalue, qubitBlochRadius, hrad,
      Real.sqrt_sq_eq_abs, abs_of_nonpos (sub_nonpos.mpr hle)]
    rw [show (1 + -(ρ.M.H.eigenvalues 0 - ρ.M.H.eigenvalues 1)) / 2 =
      1 - ρ.M.H.eigenvalues 0 by linarith, Real.binEntropy_one_sub]

/-- Pairing a density matrix with the logarithm of the diagonal stationary
state depends on its occupation but not directly on its coherence. -/
theorem inner_stationaryState_log_eq (d : OneLevelChannelData)
    (ρ : MState Qubit) :
    ⟪ρ.M, d.stationaryState.M.log⟫ =
      (1 - excitedOccupation ρ) * Real.log (1 - d.occupation) +
        excitedOccupation ρ * Real.log d.occupation := by
  rw [stationaryState_M_log d]
  have hinner : ∀ τ : MState Qubit, ∀ L : Qubit → ℝ,
      ⟪τ.M, HermitianMat.diagonal ℂ L⟫ =
        (τ.m 0 0 * ((L 0 : ℝ) : ℂ) +
          τ.m 1 1 * ((L 1 : ℝ) : ℂ)).re := by
    intro τ L
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.diagonal_mat,
      Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
    rfl
  rw [hinner, m_zero_zero_eq, m_one_one_eq]
  simp

/-- **Exact operator formula.**  For a faithful one-level reference state,
the real value of the repository's Umegaki relative entropy equals the full
occupation-and-coherence Bloch formula. -/
theorem entropicProperTime_qubit_stationary_toReal
    (d : OneLevelChannelData) (ρ : MState Qubit)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) :
    (entropicProperTime ρ d.stationaryState).toReal =
      qubitOperatorRelativeEntropy d.occupation (excitedOccupation ρ)
        (Complex.normSq (ρ.m 0 1)) := by
  letI : d.stationaryState.M.NonSingular :=
    HermitianMat.nonSingular_iff_ker_bot.mpr
      (stationaryState_ker_bot d hf0 hf1)
  rw [entropicProperTime_toReal_modular_form,
    Sᵥₙ_qubit_eq_binEntropy_bloch, inner_stationaryState_log_eq]
  rfl

/-- Coherence norm square along the exact one-level orbit. -/
noncomputable def RateData.oneLevelCoherenceNormSqAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  Real.exp (-2 * r.gamma * t) * Complex.normSq (ρ.m 0 1)

/-- Squared Bloch radius along the exact analytic one-level orbit. -/
noncomputable def RateData.oneLevelBlochRadiusSqAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  qubitBlochRadiusSq (r.predictedOccupation (excitedOccupation ρ) t)
    (r.oneLevelCoherenceNormSqAt ρ t)

/-- Bloch radius along the exact analytic one-level orbit. -/
noncomputable def RateData.oneLevelBlochRadiusAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  Real.sqrt (r.oneLevelBlochRadiusSqAt ρ t)

/-- Upper eigenvalue along the exact analytic one-level orbit. -/
noncomputable def RateData.oneLevelUpperEigenvalueAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  (1 + r.oneLevelBlochRadiusAt ρ t) / 2

/-- Full real operator-relative-entropy trajectory.  Unlike the earlier
binary KL trajectory, this retains arbitrary initial qubit coherence. -/
noncomputable def RateData.oneLevelOperatorRelativeEntropyTrajectory
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  -Real.binEntropy (r.oneLevelUpperEigenvalueAt ρ t) -
    ((1 - r.predictedOccupation (excitedOccupation ρ) t) *
        Real.log (1 - r.occupation) +
      r.predictedOccupation (excitedOccupation ρ) t *
        Real.log r.occupation)

/-- Exact occupation derivative along the one-level orbit. -/
noncomputable def RateData.oneLevelOccupationDerivativeAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  -2 * r.gamma *
    (r.predictedOccupation (excitedOccupation ρ) t - r.occupation)

/-- Exact coherence-norm-square derivative along the one-level orbit. -/
noncomputable def RateData.oneLevelCoherenceNormSqDerivativeAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  -2 * r.gamma * r.oneLevelCoherenceNormSqAt ρ t

/-- Exact squared-Bloch-radius derivative along the one-level orbit. -/
noncomputable def RateData.oneLevelBlochRadiusSqDerivativeAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  2 * (1 - 2 * r.predictedOccupation (excitedOccupation ρ) t) *
      (-2 * r.oneLevelOccupationDerivativeAt ρ t) +
    4 * r.oneLevelCoherenceNormSqDerivativeAt ρ t

/-- Exact upper-eigenvalue derivative, valid when the Bloch radius is nonzero. -/
noncomputable def RateData.oneLevelUpperEigenvalueDerivativeAt
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  (r.oneLevelBlochRadiusSqDerivativeAt ρ t /
      (2 * r.oneLevelBlochRadiusAt ρ t)) / 2

/-- **Coherence-sensitive operator Spohn production.**  The first summand is
the spectral/von-Neumann contribution and the second is the diagonal modular
energy contribution. -/
noncomputable def RateData.oneLevelOperatorSpohnProduction
    (r : RateData) (ρ : MState Qubit) (t : ℝ) : ℝ :=
  (Real.log (1 - r.oneLevelUpperEigenvalueAt ρ t) -
      Real.log (r.oneLevelUpperEigenvalueAt ρ t)) *
      r.oneLevelUpperEigenvalueDerivativeAt ρ t +
    r.oneLevelOccupationDerivativeAt ρ t *
      (Real.log r.occupation - Real.log (1 - r.occupation))

/-- The actual `C₀` channel's excited occupation is the exact exponential
population orbit for every input state, including coherent states. -/
theorem RateData.oneLevelCPTPC0Semigroup_excitedOccupation
    (r : RateData) (ρ : MState Qubit) (t : NNReal) :
    excitedOccupation (r.oneLevelCPTPC0Semigroup.channel t ρ) =
      r.predictedOccupation (excitedOccupation ρ) (t : ℝ) := by
  change excitedOccupation
      (oneLevelChannel (OneLevelChannelData.ofRateTime r (t : ℝ) t.2) ρ) = _
  rw [excitedOccupation_oneLevelChannel]
  simp only [OneLevelChannelData.ofRateTime, OneLevelChannelData.survival,
    RateData.dampingProbability, RateData.predictedOccupation]
  ring

/-- The actual `C₀` channel's off-diagonal entry is the exact coherence orbit. -/
theorem RateData.oneLevelCPTPC0Semigroup_coherence
    (r : RateData) (ρ : MState Qubit) (t : NNReal) :
    (r.oneLevelCPTPC0Semigroup.channel t ρ).m 0 1 =
      ((Real.exp (-r.gamma * (t : ℝ)) : ℝ) : ℂ) * ρ.m 0 1 := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (r.oneLevelChannelAt (t : ℝ) t.2).map ρ.m 0 1 = _
  rw [← oneLevelGKSLOrbit_eq_oneLevelChannelAt r (t : ℝ) t.2]
  simp only [oneLevelGKSLOrbit_apply_zero_one]
  have h : Complex.exp (-(r.gamma : ℂ) * ((t : ℝ) : ℂ)) =
      ((Real.exp (-r.gamma * (t : ℝ)) : ℝ) : ℂ) := by
    calc
      Complex.exp (-(r.gamma : ℂ) * ((t : ℝ) : ℂ)) =
          Complex.exp ((-r.gamma * (t : ℝ) : ℝ) : ℂ) := by
            congr 1
            push_cast
            ring
      _ = ((Real.exp (-r.gamma * (t : ℝ)) : ℝ) : ℂ) :=
        (Complex.ofReal_exp _).symm
  rw [h]

/-- The coherence norm square of the actual channel state equals the analytic
coherence carrier used by the derivative theorem. -/
theorem RateData.oneLevelCPTPC0Semigroup_coherenceNormSq
    (r : RateData) (ρ : MState Qubit) (t : NNReal) :
    Complex.normSq ((r.oneLevelCPTPC0Semigroup.channel t ρ).m 0 1) =
      r.oneLevelCoherenceNormSqAt ρ (t : ℝ) := by
  rw [r.oneLevelCPTPC0Semigroup_coherence ρ t,
    Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [RateData.oneLevelCoherenceNormSqAt]
  rw [← Real.exp_add]
  congr 2
  ring

/-- The positive one-level coherence-decay factor tends to zero along
nonnegative time. -/
@[zil_level structural]
lemma RateData.oneLevelDecayFactor_tendsto_zero (r : RateData) :
    Filter.Tendsto (fun t : NNReal => Real.exp (-r.gamma * (t : ℝ)))
      Filter.atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hpos : Filter.Tendsto (fun t : NNReal => r.gamma * (t : ℝ))
      Filter.atTop Filter.atTop :=
    (NNReal.tendsto_coe_atTop.2 Filter.tendsto_id).const_mul_atTop r.gamma_pos
  simpa only [Function.comp_def, neg_mul] using
    Filter.tendsto_neg_atTop_atBot.comp hpos

/-- The complete density matrix of every exact one-level `C₀` orbit converges
entrywise to the stationary matrix.  Both populations and arbitrary initial
coherence are included. -/
@[zil_level bridge_theorem]
theorem RateData.oneLevelCPTPC0Semigroup_m_tendsto_stationary
    (r : RateData) (ρ : MState Qubit) :
    Filter.Tendsto (fun t : NNReal =>
      (r.oneLevelCPTPC0Semigroup.channel t ρ).m)
      Filter.atTop (nhds r.continuousStationaryState.m) := by
  have hN : Filter.Tendsto (fun t : NNReal =>
      excitedOccupation (r.oneLevelCPTPC0Semigroup.channel t ρ))
      Filter.atTop (nhds r.occupation) := by
    rw [show (fun t : NNReal =>
        excitedOccupation (r.oneLevelCPTPC0Semigroup.channel t ρ)) =
      (fun t : NNReal => r.predictedOccupation (excitedOccupation ρ) (t : ℝ)) by
        funext t
        exact r.oneLevelCPTPC0Semigroup_excitedOccupation ρ t]
    exact (r.predictedOccupation_tendsto (excitedOccupation ρ)).comp
      (NNReal.tendsto_coe_atTop.2 Filter.tendsto_id)
  have hcoh : Filter.Tendsto (fun t : NNReal =>
      (r.oneLevelCPTPC0Semigroup.channel t ρ).m 0 1)
      Filter.atTop (nhds 0) := by
    have h := (Filter.Tendsto.ofReal r.oneLevelDecayFactor_tendsto_zero).mul_const
      (ρ.m 0 1)
    simpa [r.oneLevelCPTPC0Semigroup_coherence ρ] using h
  unfold RateData.continuousStationaryState
  rw [OneLevelChannelData.stationaryState_m]
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · have hreal : Filter.Tendsto (fun t : NNReal =>
        1 - excitedOccupation (r.oneLevelCPTPC0Semigroup.channel t ρ))
        Filter.atTop (nhds (1 - r.occupation)) := tendsto_const_nhds.sub hN
    have h := Filter.Tendsto.ofReal hreal
    simpa [m_zero_zero_eq, OneLevelChannelData.ofRateTime] using h
  · simpa [OneLevelChannelData.ofRateTime] using hcoh
  · have h := Complex.continuous_conj.continuousAt.tendsto.comp hcoh
    simpa [Function.comp_def, m_one_zero_eq, OneLevelChannelData.ofRateTime] using h
  · have h := Filter.Tendsto.ofReal hN
    simpa [m_one_one_eq, OneLevelChannelData.ofRateTime] using h

/-- **Global one-level relaxation.** Every qubit density operator converges in
the mixed-state topology to the exact semigroup's stationary state.  This is a
full coherence-carrying state theorem, not only convergence of the scalar
occupation. -/
@[zil_level physical_theorem]
theorem RateData.oneLevelCPTPC0Semigroup_tendsto_stationary
    (r : RateData) (ρ : MState Qubit) :
    Filter.Tendsto (fun t : NNReal =>
      r.oneLevelCPTPC0Semigroup.channel t ρ)
      Filter.atTop (nhds r.continuousStationaryState) := by
  apply MState.toMat_IsEmbedding.tendsto_nhds_iff.mpr
  change Filter.Tendsto (fun t : NNReal =>
    (r.oneLevelCPTPC0Semigroup.channel t ρ).M)
    Filter.atTop (nhds r.continuousStationaryState.M)
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  exact r.oneLevelCPTPC0Semigroup_m_tendsto_stationary ρ

/-- **No scalar surrogate:** at every physical time the closed trajectory is
exactly the real value of Umegaki relative entropy for the actual state of the
bundled `C₀` CPTP semigroup. -/
theorem RateData.oneLevelOperatorRelativeEntropyTrajectory_eq
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1) (t : NNReal) :
    (entropicProperTime (r.oneLevelCPTPC0Semigroup.channel t ρ)
      r.continuousStationaryState).toReal =
        r.oneLevelOperatorRelativeEntropyTrajectory ρ (t : ℝ) := by
  have h := entropicProperTime_qubit_stationary_toReal
    (OneLevelChannelData.ofRateTime r 0 (by positivity))
    (r.oneLevelCPTPC0Semigroup.channel t ρ) hf0 hf1
  rw [r.oneLevelCPTPC0Semigroup_excitedOccupation ρ t,
    r.oneLevelCPTPC0Semigroup_coherenceNormSq ρ t] at h
  simpa [RateData.continuousStationaryState,
    qubitOperatorRelativeEntropy, qubitUpperEigenvalue,
    qubitBlochRadius, RateData.oneLevelOperatorRelativeEntropyTrajectory,
    RateData.oneLevelUpperEigenvalueAt, RateData.oneLevelBlochRadiusAt,
    RateData.oneLevelBlochRadiusSqAt, OneLevelChannelData.ofRateTime] using h

/-- The real Umegaki gap of the actual coherent channel orbit is antitone on
the physical nonnegative-time half-line by quantum data processing. -/
theorem RateData.oneLevelOperatorRelativeEntropy_antitoneOn
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1) :
    AntitoneOn (r.oneLevelOperatorRelativeEntropyTrajectory ρ) (Set.Ici 0) := by
  have hanti := r.oneLevelContinuousRelativeEntropy_antitone ρ
  letI : r.continuousStationaryState.M.NonSingular := by
    apply HermitianMat.nonSingular_iff_ker_bot.mpr
    unfold RateData.continuousStationaryState
    exact stationaryState_ker_bot _ hf0 hf1
  intro s hs t ht hst
  change (0 : ℝ) ≤ s at hs
  change (0 : ℝ) ≤ t at ht
  let s' : NNReal := ⟨s, hs⟩
  let t' : NNReal := ⟨t, ht⟩
  have hle : s' ≤ t' := by
    change s ≤ t
    exact hst
  have h := hanti hle
  have hreal := ENNReal.toReal_mono entropicProperTime_ne_top h
  change (entropicProperTime (r.oneLevelCPTPC0Semigroup.channel t' ρ)
      r.continuousStationaryState).toReal ≤
    (entropicProperTime (r.oneLevelCPTPC0Semigroup.channel s' ρ)
      r.continuousStationaryState).toReal at hreal
  rw [r.oneLevelOperatorRelativeEntropyTrajectory_eq ρ hf0 hf1 s',
    r.oneLevelOperatorRelativeEntropyTrajectory_eq ρ hf0 hf1 t'] at hreal
  exact hreal

/-- **Full coherence-carrying operator-relative-entropy derivative.**  A
nonzero initial coherence makes the positive-time channel state strictly
inside the Bloch ball.  Consequently the square-root spectral map and binary
entropy are differentiable, and the exact Umegaki gap satisfies
`D'(t) = -σ_op(t)` for every `t > 0`. -/
theorem RateData.oneLevelOperatorRelativeEntropy_hasDerivAt
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    (hcoh : ρ.m 0 1 ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
      (-r.oneLevelOperatorSpohnProduction ρ t) t := by
  let N₀ := excitedOccupation ρ
  let N := r.predictedOccupation N₀ t
  let C₀ := Complex.normSq (ρ.m 0 1)
  let C := r.oneLevelCoherenceNormSqAt ρ t
  let A := r.oneLevelBlochRadiusSqAt ρ t
  let q := r.oneLevelBlochRadiusAt ρ t
  let lam := r.oneLevelUpperEigenvalueAt ρ t
  have hN₀0 : 0 ≤ N₀ := excitedOccupation_nonneg ρ
  have hN₀1 : N₀ ≤ 1 := excitedOccupation_le_one ρ
  have hC₀0 : 0 ≤ C₀ := Complex.normSq_nonneg _
  have hC₀pos : 0 < C₀ := Complex.normSq_pos.mpr hcoh
  have hu0 : 0 < Real.exp (-2 * r.gamma * t) := Real.exp_pos _
  have huexp : -2 * r.gamma * t < 0 := by nlinarith [r.gamma_pos]
  have hu1 : Real.exp (-2 * r.gamma * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact huexp
  have hCpos : 0 < C := by
    dsimp [C, RateData.oneLevelCoherenceNormSqAt, C₀]
    positivity
  have hdet0 : 0 ≤ N₀ * (1 - N₀) - C₀ := by
    have hp := eigenvalues_prod ρ
    rw [show N₀ * (1 - N₀) - C₀ =
      ρ.M.H.eigenvalues 0 * ρ.M.H.eigenvalues 1 by
        simpa [N₀, C₀] using hp.symm]
    exact mul_nonneg (ρ.eigenvalue_nonneg 0) (ρ.eigenvalue_nonneg 1)
  have hdet : 0 < N * (1 - N) - C := by
    have hidN : N = (1 - Real.exp (-2 * r.gamma * t)) * r.occupation +
        Real.exp (-2 * r.gamma * t) * N₀ := by
      simp only [N, N₀, RateData.predictedOccupation]
      ring
    have hidC : C = Real.exp (-2 * r.gamma * t) * C₀ := by rfl
    rw [hidN, hidC]
    nlinarith [mul_pos (sub_pos.mpr hu1)
        (mul_pos hf0 (sub_pos.mpr hf1)),
      mul_nonneg hu0.le hdet0,
      mul_nonneg (mul_nonneg hu0.le (sub_nonneg.mpr hu1.le))
        (sq_nonneg (r.occupation - N₀))]
  have hAeq : A = 1 - 4 * (N * (1 - N) - C) := by
    simp only [A, RateData.oneLevelBlochRadiusSqAt,
      qubitBlochRadiusSq, N, C]
    ring
  have hApos : 0 < A := by
    dsimp [A, RateData.oneLevelBlochRadiusSqAt, qubitBlochRadiusSq]
    positivity
  have hAlt : A < 1 := by rw [hAeq]; linarith
  have hqpos : 0 < q := Real.sqrt_pos.2 hApos
  have hqlt : q < 1 := by
    dsimp [q, RateData.oneLevelBlochRadiusAt]
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hAlt
  have hlam0 : 0 < lam := by
    dsimp [lam, RateData.oneLevelUpperEigenvalueAt]
    linarith
  have hlam1 : lam < 1 := by
    dsimp [lam, RateData.oneLevelUpperEigenvalueAt]
    linarith
  have hN := r.predictedOccupation_hasDerivAt N₀ t
  have hlin : HasDerivAt (fun s : ℝ => -2 * r.gamma * s)
      (-2 * r.gamma) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 * r.gamma)
  have hC : HasDerivAt (fun s => r.oneLevelCoherenceNormSqAt ρ s)
      (r.oneLevelCoherenceNormSqDerivativeAt ρ t) t := by
    have h := hlin.exp.mul_const C₀
    simpa [RateData.oneLevelCoherenceNormSqAt,
      RateData.oneLevelCoherenceNormSqDerivativeAt, C, C₀] using
      h.congr_deriv (by
        dsimp [C, RateData.oneLevelCoherenceNormSqAt, C₀]
        ring)
  have hA : HasDerivAt (fun s => r.oneLevelBlochRadiusSqAt ρ s)
      (r.oneLevelBlochRadiusSqDerivativeAt ρ t) t := by
    have hbase := (hN.const_mul (-2)).const_add 1
    have hsquare := hbase.pow 2
    have hsum := hsquare.add (hC.const_mul 4)
    refine (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [RateData.oneLevelBlochRadiusSqAt, qubitBlochRadiusSq,
        N₀, pow_two, Pi.add_apply, Pi.mul_apply]
      ring
    · simp only [RateData.oneLevelBlochRadiusSqDerivativeAt,
        RateData.oneLevelOccupationDerivativeAt, N₀]
      ring
  have hq : HasDerivAt (fun s => r.oneLevelBlochRadiusAt ρ s)
      (r.oneLevelBlochRadiusSqDerivativeAt ρ t /
        (2 * r.oneLevelBlochRadiusAt ρ t)) t := by
    simpa [RateData.oneLevelBlochRadiusAt] using hA.sqrt hApos.ne'
  have hlam : HasDerivAt (fun s => r.oneLevelUpperEigenvalueAt ρ s)
      (r.oneLevelUpperEigenvalueDerivativeAt ρ t) t := by
    simpa [RateData.oneLevelUpperEigenvalueAt,
      RateData.oneLevelUpperEigenvalueDerivativeAt] using
        (hq.const_add 1).div_const 2
  have hentropy : HasDerivAt
      (fun s => Real.binEntropy (r.oneLevelUpperEigenvalueAt ρ s))
      ((Real.log (1 - lam) - Real.log lam) *
        r.oneLevelUpperEigenvalueDerivativeAt ρ t) t := by
    convert (Real.hasDerivAt_binEntropy hlam0.ne' hlam1.ne).comp t hlam using 1 <;> rfl
  have hdiag : HasDerivAt
      (fun s => (1 - r.predictedOccupation N₀ s) *
          Real.log (1 - r.occupation) +
        r.predictedOccupation N₀ s * Real.log r.occupation)
      (r.oneLevelOccupationDerivativeAt ρ t *
        (Real.log r.occupation - Real.log (1 - r.occupation))) t := by
    have h := ((hN.neg.const_add 1).mul_const
      (Real.log (1 - r.occupation))).add
      (hN.mul_const (Real.log r.occupation))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [RateData.oneLevelOccupationDerivativeAt, N₀]
    ring
  have h := hentropy.neg.sub hdiag
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [RateData.oneLevelOperatorSpohnProduction, lam]
  ring

/-- The coherence-sensitive operator Spohn production is nonnegative at every
strictly positive physical time.  The proof combines the exact derivative
above with data-processing antitonicity of the actual CPTP orbit. -/
theorem RateData.oneLevelOperatorSpohnProduction_nonneg
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    (hcoh : ρ.m 0 1 ≠ 0) {t : ℝ} (ht : 0 < t) :
    0 ≤ r.oneLevelOperatorSpohnProduction ρ t := by
  have hder := r.oneLevelOperatorRelativeEntropy_hasDerivAt
    ρ hf0 hf1 hcoh ht
  have heq : derivWithin (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
      (Set.Ici 0) t = -r.oneLevelOperatorSpohnProduction ρ t :=
    hder.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht.le)
  have hnonpos :=
    (r.oneLevelOperatorRelativeEntropy_antitoneOn ρ hf0 hf1).derivWithin_nonpos
      (x := t)
  rw [heq] at hnonpos
  linarith

/-- The coherent one-level orbit instantiates the operator differential Spohn
interface on strictly positive time. -/
theorem RateData.oneLevelOperator_isOperatorDifferentialSpohnTrajectoryOn
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    (hcoh : ρ.m 0 1 ≠ 0) :
    IsOperatorDifferentialSpohnTrajectoryOn r.continuousStationaryState
      (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
      (r.oneLevelOperatorSpohnProduction ρ) (Set.Ioi 0) := by
  constructor
  · intro t ht
    let t' : NNReal := ⟨t, ht.le⟩
    refine ⟨r.oneLevelCPTPC0Semigroup.channel t' ρ, ?_, ?_⟩
    · letI : r.continuousStationaryState.M.NonSingular := by
        apply HermitianMat.nonSingular_iff_ker_bot.mpr
        unfold RateData.continuousStationaryState
        exact stationaryState_ker_bot _ hf0 hf1
      exact entropicProperTime_ne_top
    · exact (r.oneLevelOperatorRelativeEntropyTrajectory_eq
        ρ hf0 hf1 t').symm
  · intro t ht
    exact r.oneLevelOperatorRelativeEntropy_hasDerivAt
      ρ hf0 hf1 hcoh ht

/-- **Operator Spohn H-theorem for the exact coherent one-level channel.**
The Umegaki gap has an actual density-operator witness, its derivative is the
negative explicit coherence-sensitive production, that production is
nonnegative, and the gap is antitone on positive physical time. -/
theorem RateData.oneLevelOperatorSpohnHTheorem
    (r : RateData) (ρ : MState Qubit)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    (hcoh : ρ.m 0 1 ≠ 0) :
    IsOperatorDifferentialSpohnTrajectoryOn r.continuousStationaryState
        (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
        (r.oneLevelOperatorSpohnProduction ρ) (Set.Ioi 0) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ),
        0 ≤ r.oneLevelOperatorSpohnProduction ρ t) ∧
      AntitoneOn (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
        (Set.Ioi 0) := by
  have hflow := r.oneLevelOperator_isOperatorDifferentialSpohnTrajectoryOn
    ρ hf0 hf1 hcoh
  have hproduction : ∀ t ∈ Set.Ioi (0 : ℝ),
      0 ≤ r.oneLevelOperatorSpohnProduction ρ t := fun t ht =>
    r.oneLevelOperatorSpohnProduction_nonneg ρ hf0 hf1 hcoh ht
  exact ⟨hflow, hproduction,
    operator_differential_spohn_gap_antitoneOn
      r.continuousStationaryState
      (r.oneLevelOperatorRelativeEntropyTrajectory ρ)
      (r.oneLevelOperatorSpohnProduction ρ) (Set.Ioi 0)
      (convex_Ioi 0) hflow hproduction⟩

/-! ## Exact diagonal differential Spohn trajectory -/

/-- The finite Gibbs carrier whose equilibrium weights are the one-level
Bernoulli law `(f, 1-f)`.  The energy is the exact negative log weight, at
inverse temperature one, so the partition function is exactly one. -/
noncomputable def oneLevelBinaryGibbsSystem (f : ℝ)
    (hf0 : 0 < f) (hf1 : f < 1) :
    FiniteGibbsVariationalSystem (Fin 2) where
  energy := fun i => -Real.log (binaryDist f i)
  beta := 1
  partition := 1
  beta_pos := by norm_num
  partition_pos := by norm_num
  partition_eq := by
    rw [Fin.sum_univ_two]
    simp [binaryDist, Real.exp_log hf0, Real.exp_log (sub_pos.mpr hf1)]

/-- The packaged Gibbs weights recover the stationary Bernoulli distribution
definitionally up to the elementary `exp (log x) = x` identities. -/
theorem oneLevelBinaryGibbsSystem_gibbsWeight_eq (f : ℝ)
    (hf0 : 0 < f) (hf1 : f < 1) :
    (oneLevelBinaryGibbsSystem f hf0 hf1).gibbsWeight = binaryDist f := by
  funext i
  fin_cases i <;>
    simp [oneLevelBinaryGibbsSystem,
      FiniteGibbsVariationalSystem.gibbsWeight, binaryDist,
      Real.exp_log hf0, Real.exp_log (sub_pos.mpr hf1)]

/-- On an interior binary state, the Gibbs free-energy deficit of the exact
one-level carrier is precisely the already-formalized binary KL divergence. -/
theorem oneLevelBinaryGibbsSystem_freeEnergyGap_eq_binaryKL
    {N f : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    finiteGibbsFreeEnergyGap (oneLevelBinaryGibbsSystem f hf0 hf1)
        (binaryDist N) = binaryKL N f := by
  have hp : ∀ i, 0 < binaryDist N i := by
    intro i
    fin_cases i <;> simp [binaryDist] <;> linarith
  rw [finiteGibbsFreeEnergyGap_eq_relativeEntropy_div
      (oneLevelBinaryGibbsSystem f hf0 hf1) (binaryDist N)
      hp (binaryDist_sum N),
    oneLevelBinaryGibbsSystem_gibbsWeight_eq]
  change finiteRelativeEntropy (binaryDist N) (binaryDist f) / 1 = binaryKL N f
  rw [div_one]
  rfl

/-- The diagonal state orbit is not merely represented by the same scalar
formula: it is exactly the orbit of the bundled `C₀` CPTP semigroup. -/
theorem RateData.oneLevelCPTPC0Semigroup_occState
    (r : RateData) {N₀ : ℝ} (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1) (t : NNReal) :
    r.oneLevelCPTPC0Semigroup.channel t (occState N₀ hN₀0.le hN₀1.le) =
      occState (r.predictedOccupation N₀ (t : ℝ))
        (r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 t.2).1.le
        (r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 t.2).2.le := by
  change oneLevelChannel (OneLevelChannelData.ofRateTime r (t : ℝ) t.2)
      (occState N₀ hN₀0.le hN₀1.le) = _
  rw [oneLevelChannel_occState]
  apply occState_congr
  simp only [OneLevelChannelData.ofRateTime, OneLevelChannelData.survival,
    RateData.dampingProbability, RateData.predictedOccupation]
  ring

/-- The exact diagonal production density is nonnegative at every physical
time, including equilibrium where it vanishes. -/
theorem RateData.oneLevelExactDiagonal_entropyProductionRate_nonneg
    (r : RateData) {N₀ : ℝ} (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ entropyProductionRate r.gamma
      (r.predictedOccupation N₀ t) r.occupation := by
  obtain ⟨hN0, hN1⟩ :=
    r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 ht
  by_cases hEq : r.predictedOccupation N₀ t = r.occupation
  · simp [entropyProductionRate, hEq]
  · exact (entropyProductionRate_pos r.gamma_pos hN0 hN1 hf0 hf1 hEq).le

/-- **Exact differential Spohn trajectory.**  On nonnegative physical time,
the diagonal orbit of the genuine one-level `C₀` CPTP semigroup instantiates
the repository's corrected differential Spohn interface with the concrete
production density `σ = 2γ(N-f)(log odds(N)-log odds(f))`. -/
theorem RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn
    (r : RateData) {N₀ : ℝ} (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1) :
    IsFiniteDifferentialSpohnTrajectoryOn
      (oneLevelBinaryGibbsSystem r.occupation hf0 hf1)
      (fun t => binaryDist (r.predictedOccupation N₀ t))
      (fun t => entropyProductionRate r.gamma
        (r.predictedOccupation N₀ t) r.occupation)
      (Set.Ici 0) := by
  intro t ht
  have hNt := r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 ht
  have hnear : ∀ᶠ s in nhds t,
      r.predictedOccupation N₀ s ∈ Set.Ioo (0 : ℝ) 1 :=
    (r.predictedOccupation_hasDerivAt N₀ t).continuousAt.eventually_mem
      (IsOpen.mem_nhds isOpen_Ioo hNt)
  have heq :
      (fun s => finiteGibbsFreeEnergyGap
        (oneLevelBinaryGibbsSystem r.occupation hf0 hf1)
        (binaryDist (r.predictedOccupation N₀ s))) =ᶠ[nhds t]
      (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation) :=
    hnear.mono fun s hs =>
      oneLevelBinaryGibbsSystem_freeEnergyGap_eq_binaryKL
        hs.1 hs.2 hf0 hf1
  exact (binaryKL_predictedOccupation_hasDerivAt
    r hN₀0 hN₀1 hf0 hf1 ht).congr_of_eventuallyEq heq

/-- The exact diagonal Gibbs free-energy deficit is antitone on physical
nonnegative time, now derived through the generic differential Spohn API. -/
theorem RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn
    (r : RateData) {N₀ : ℝ} (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1)
    (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1) :
    AntitoneOn
      (fun t => finiteGibbsFreeEnergyGap
        (oneLevelBinaryGibbsSystem r.occupation hf0 hf1)
        (binaryDist (r.predictedOccupation N₀ t)))
      (Set.Ici 0) :=
  finite_differential_spohn_freeEnergyGap_antitoneOn
    (oneLevelBinaryGibbsSystem r.occupation hf0 hf1)
    (fun t => binaryDist (r.predictedOccupation N₀ t))
    (fun t => entropyProductionRate r.gamma
      (r.predictedOccupation N₀ t) r.occupation)
    (Set.Ici 0) (convex_Ici 0)
    (r.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn
      hN₀0 hN₀1 hf0 hf1)
    (fun t ht => r.oneLevelExactDiagonal_entropyProductionRate_nonneg
      hN₀0 hN₀1 hf0 hf1 ht)

/-! ## Nontrivial Page–Wootters Hamiltonian constraint -/

/-- The two-level energy function: the ground state has energy zero and the
excited state has energy `E`. -/
def oneLevelQubitEnergy (E : ℝ) (i : Qubit) : ℂ :=
  if i = 0 then 0 else (E : ℂ)

/-- Clock-system constraint energy `E_system - E_clock`. Equal-energy
clock/system basis pairs therefore lie in its kernel. -/
def oneLevelClockSystemEnergy (E : ℝ) (ij : Qubit × Qubit) : ℂ :=
  oneLevelQubitEnergy E ij.1 - oneLevelQubitEnergy E ij.2

/-- A nontrivial Page–Wootters Hamiltonian constraint on the clock-system
Hilbert space, represented by the diagonal operator `H_S - H_C`. -/
def oneLevelHamiltonianConstraint (E : ℝ) :
    Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint
      (EuclideanSpace ℂ (Qubit × Qubit)) where
  H_total :=
    Matrix.toEuclideanCLM (n := Qubit × Qubit) (𝕜 := ℂ)
      (Matrix.diagonal (oneLevelClockSystemEnergy E))

/-- The correlated two-time history vector `|0,0⟩ + |1,1⟩`. -/
def oneLevelCorrelatedHistory : EuclideanSpace ℂ (Qubit × Qubit) :=
  EuclideanSpace.single (0, 0) 1 + EuclideanSpace.single (1, 1) 1

/-- Every equal-energy clock/system basis vector satisfies the Hamiltonian
constraint. -/
theorem oneLevelHamiltonianConstraint_basis_same_isPhysical
    (E : ℝ) (i : Qubit) :
    (oneLevelHamiltonianConstraint E).IsPhysical
      (EuclideanSpace.single (i, i) (1 : ℂ)) := by
  unfold Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint.IsPhysical
    oneLevelHamiltonianConstraint
  apply (WithLp.equiv 2 ((Qubit × Qubit) → ℂ)).injective
  simp [Matrix.ofLp_toEuclideanCLM, oneLevelClockSystemEnergy]

/-- The correlated history vector is a physical Page–Wootters state. -/
theorem oneLevelCorrelatedHistory_isPhysical (E : ℝ) :
    (oneLevelHamiltonianConstraint E).IsPhysical
      oneLevelCorrelatedHistory := by
  exact Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint.isPhysical_add
    (oneLevelHamiltonianConstraint E)
    (oneLevelHamiltonianConstraint_basis_same_isPhysical E 0)
    (oneLevelHamiltonianConstraint_basis_same_isPhysical E 1)

/-- The correlated history vector is nonzero. -/
theorem oneLevelCorrelatedHistory_ne_zero :
    oneLevelCorrelatedHistory ≠ 0 := by
  intro h
  have h00 := congrArg (fun v =>
    (WithLp.equiv 2 ((Qubit × Qubit) → ℂ) v) (0, 0)) h
  simp [oneLevelCorrelatedHistory] at h00

/-- For nonzero level spacing, the Page–Wootters total Hamiltonian itself is
nonzero, so physicality is not inherited from the trivial constraint. -/
theorem oneLevelHamiltonianConstraint_nonzero
    (E : ℝ) (hE : E ≠ 0) :
    (oneLevelHamiltonianConstraint E).H_total ≠ 0 := by
  intro h
  have happ := congrArg (fun T =>
    T (EuclideanSpace.single ((1 : Qubit), (0 : Qubit)) (1 : ℂ))) h
  have h10 := congrArg (fun v =>
    (WithLp.equiv 2 ((Qubit × Qubit) → ℂ) v)
      ((1 : Qubit), (0 : Qubit))) happ
  simp [oneLevelHamiltonianConstraint, Matrix.ofLp_toEuclideanCLM,
    oneLevelClockSystemEnergy,
    oneLevelQubitEnergy, PiLp.ofLp_single] at h10
  exact hE h10

/-- The completed one-level dissipative Page–Wootters carrier: an actual GKSL
conditional clock together with a nonzero Hamiltonian constraint and a
nonzero correlated physical history state. -/
structure OneLevelDissipativePageWoottersCarrier where
  rate : RateData
  ℏ : ℝ
  ℏ_pos : 0 < ℏ
  energy : ℝ
  energy_ne_zero : energy ≠ 0

namespace OneLevelDissipativePageWoottersCarrier

/-- The carrier's explicit loss/gain conditional clock. -/
def clock (P : OneLevelDissipativePageWoottersCarrier) :
    DissipativeConditionalClock (EuclideanSpace ℂ Qubit) :=
  oneLevelExplicitDissipativeClock P.rate P.ℏ P.ℏ_pos

/-- The carrier's nontrivial clock-system Hamiltonian constraint. -/
def constraint (P : OneLevelDissipativePageWoottersCarrier) :
    Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint
      (EuclideanSpace ℂ (Qubit × Qubit)) :=
  oneLevelHamiltonianConstraint P.energy

/-- **Completed constrained-carrier synthesis.** Its conditional generator is
the explicit one-level GKSL generator, while its nonzero correlated history
state satisfies a nonzero Page–Wootters Hamiltonian constraint. -/
theorem constrained_gksl_history
    (P : OneLevelDissipativePageWoottersCarrier)
    (ρ : Matrix Qubit Qubit ℂ) :
    P.clock.gksLGen (𝔈 ρ) = 𝔈 (oneLevelGKSLMatrix P.rate ρ)
      ∧ P.constraint.IsPhysical oneLevelCorrelatedHistory
      ∧ oneLevelCorrelatedHistory ≠ 0
      ∧ P.constraint.H_total ≠ 0 := by
  exact ⟨oneLevelExplicitDissipativeClock_gksLGen
      P.rate P.ℏ P.ℏ_pos ρ,
    oneLevelCorrelatedHistory_isPhysical P.energy,
    oneLevelCorrelatedHistory_ne_zero,
    oneLevelHamiltonianConstraint_nonzero P.energy P.energy_ne_zero⟩

end OneLevelDissipativePageWoottersCarrier

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.toEuclideanCLM_commutator where
  supported_by @ "lean:MState.Hermitian",
  formalizes @ "claim:the-matrix-to-operator-star-algebra-isomorphism-toeuclideanclm-intertwines-the-matrix-commutator-with-the-operator-commutator-the-clm-to-mstate-bridge",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelModularClock_vonNeumannGen where
  formalizes @ "claim:the-page-wootters-conditional-von-neumann-generator-of-the-one-level-clock-is-the-image-under-toeuclideanclm-of-the-matrix-von-neumann-equation-with-the-modular-hamiltonian",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.toEuclideanCLM_commutator",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelModularClock_vonNeumannGen_stationary where
  formalizes @ "claim:the-page-wootters-conditional-modular-clock-of-the-one-level-carrier-is-frozen-at-the-gibbs-stationary-state-its-hamiltonian-generator-vanishes-there",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.modularHamiltonian_commute_stationaryState",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelReversibleClock_gksLGen where
  formalizes @ "claim:in-the-dissipationless-limit-the-one-level-page-wootters-clock-collapses-to-the-pure-unitary-modular-flow-the-relational-photon-experimental-regime",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelDissipativeClock_gksLGen where
  formalizes @ "claim:in-the-hamiltonian-free-limit-the-one-level-page-wootters-clock-collapses-to-pure-gksl-dissipation-the-quantum-dot-population-relaxation-experimental-regime",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-abstract-hamiltonian-free-reduction-the-explicit-instantiation-and-semigroup-integration-are-closed-by-onelevelgkslmatrix-and-onelevelgkslorbit-below"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLMatrix_eq where
  formalizes @ "claim:the-one-level-loss-gain-gksl-generator-has-population-relaxation-rate-two-gamma-and-coherence-decay-rate-gamma",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.lindbladSingleJumpDissipator",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelPureDephasingMatrix_eq where
  formalizes @ "claim:the-explicit-number-projector-pure-dephasing-jump-leaves-both-one-level-populations-unchanged-and-damps-only-the-off-diagonal-coherences-at-rate-gamma-phi",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.lindbladSingleJumpDissipator",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLWithPureDephasingMatrix_eq where
  formalizes @ "claim:loss-gain-relaxation-plus-independent-pure-dephasing-has-population-rate-two-gamma-and-coherence-rate-gamma-plus-gamma-phi-with-no-pure-dephasing-term-in-the-population-equation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLMatrix_eq",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelPureDephasingMatrix_eq",
  epistemic_status @ "conditional-model",
  requires @ "assumption:gamma-phi-is-an-independently-calibrated-nonnegative-pure-dephasing-rate"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelExplicitDissipativeClock_gksLGen where
  formalizes @ "claim:the-page-wootters-dissipative-clock-is-instantiated-by-the-actual-one-level-loss-gain-gksl-superoperator-under-the-matrix-operator-star-algebra-bridge",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLMatrix_eq",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_add where
  formalizes @ "claim:the-explicit-one-level-loss-gain-gksl-orbit-is-a-continuous-complex-time-semigroup-with-exponential-population-and-coherence-modes",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_hasDerivAt_zero_zero",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_eq_oneLevelChannelAt where
  formalizes @ "claim:on-every-nonnegative-real-time-the-exact-continuous-one-level-gksl-semigroup-equals-the-full-bundled-generalized-amplitude-damping-cptp-channel",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_map_eq",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator where
  formalizes @ "claim:the-explicit-one-level-positive-time-channel-family-is-a-genuine-strongly-continuous-cptp-semigroup-whose-right-infinitesimal-generator-is-exactly-the-concrete-loss-gain-gksl-matrix-operator",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_eq_oneLevelChannelAt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_hasDerivAt_zero_zero",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:finite-dimensional-one-level-c0-semigroup-not-an-unbounded-continuum-generator-theorem"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelPositiveTimeSemigroup_stationary_fixed where
  formalizes @ "claim:the-exact-rate-derived-one-level-cptp-channels-form-a-positive-time-semigroup-and-fix-the-single-diagonal-state-diag-one-minus-f-f-at-every-nonnegative-time",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_add",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_stationaryState_fixed",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelContinuousRelativeEntropy_antitone where
  formalizes @ "claim:quantum-relative-entropy-to-the-stationary-state-is-antitone-along-the-actual-continuous-one-level-cptp-semigroup",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-data-processing-h-theorem-for-the-explicit-channel-family-not-by-itself-a-microscopic-derivation-of-the-rate-parameters"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelIntervalSpohnProduction_cocycle where
  formalizes @ "claim:the-relative-entropy-production-of-the-actual-continuous-one-level-cptp-semigroup-is-exactly-additive-on-adjacent-ordered-time-intervals",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_cocycle",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-pointwise-full-coherence-carrying-finite-qubit-operator-derivative-is-closed-below-arbitrary-dimensional-frechet-matrix-log-and-type-iii-differentiability-remain-separate"

zil attach QuantumMechanics.LindbladDrivenLeads.entropicProperTime_qubit_stationary_toReal where
  formalizes @ "claim:the-real-umegaki-relative-entropy-of-an-arbitrary-qubit-state-to-the-faithful-one-level-stationary-state-is-exactly-the-coherence-sensitive-bloch-spectral-formula",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.Sᵥₙ_qubit_eq_binEntropy_bloch",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.inner_stationaryState_log_eq",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq where
  formalizes @ "claim:the-coherence-sensitive-real-relative-entropy-trajectory-is-pointwise-exactly-the-umegaki-relative-entropy-of-the-actual-state-of-the-bundled-one-level-c0-cptp-semigroup",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_excitedOccupation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_coherenceNormSq",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_tendsto_stationary where
  formalizes @ "claim:every-coherence-carrying-qubit-density-operator-of-the-exact-one-level-c0-cptp-semigroup-converges-to-the-stationary-state",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation_tendsto",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_coherence",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelDecayFactor_tendsto_zero",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-calibrated-one-level-loss-gain-cptp-semigroup",
  caveat @ "claim:global-over-the-finite-qubit-state-space-not-an-unbounded-continuum-semigroup-relaxation-theorem"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt where
  formalizes @ "claim:for-a-genuinely-coherent-initial-qubit-and-faithful-thermal-reference-the-full-operator-umegaki-relative-entropy-along-the-exact-one-level-c0-cptp-orbit-has-derivative-minus-the-explicit-coherence-sensitive-spohn-production-at-every-strictly-positive-time",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq",
  supported_by @ "lean:Real.hasDerivAt_binEntropy",
  epistemic_status @ "conditional-model",
  requires @ "assumption:nonzero-initial-coherence",
  requires @ "assumption:strictly-interior-stationary-occupation",
  caveat @ "claim:finite-qubit-positive-time-theorem-not-an-arbitrary-dimensional-frechet-derivative-of-the-matrix-log-or-a-type-iii-result"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction_nonneg where
  formalizes @ "claim:the-explicit-full-coherence-one-level-operator-spohn-production-is-nonnegative-at-every-strictly-positive-time",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelContinuousRelativeEntropy_antitone",
  epistemic_status @ "conditional-model",
  caveat @ "claim:rate-parameters-and-the-one-level-gksl-model-are-supplied-this-is-not-an-independent-microscopic-calibration"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnHTheorem where
  formalizes @ "claim:the-exact-coherent-one-level-channel-instantiates-the-operator-differential-spohn-interface-with-an-actual-finite-umegaki-state-witness-an-exact-derivative-nonnegative-production-and-antitone-gap",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction_nonneg",
  epistemic_status @ "conditional-model",
  caveat @ "claim:full-noncommutative-finite-qubit-coherence-is-retained-but-unbounded-continuum-and-type-iii-spohn-differentiability-remain-separate"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_occState where
  formalizes @ "claim:the-exact-diagonal-bernoulli-relaxation-is-the-state-orbit-of-the-bundled-one-level-c0-cptp-semigroup-not-a-disconnected-scalar-surrogate",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_occState",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn where
  formalizes @ "claim:on-positive-time-the-exact-diagonal-one-level-c0-channel-orbit-satisfies-the-differential-spohn-identity-free-energy-gap-prime-equals-minus-the-concrete-binary-kl-production-density",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.binaryKL_predictedOccupation_hasDerivAt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_occState",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-diagonal-specialization-the-separate-operator-spohn-theorem-above-retains-full-finite-qubit-coherence"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn where
  discloses @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn",
  formalizes @ "claim:the-exact-one-level-diagonal-gibbs-free-energy-deficit-is-antitone-on-the-physical-nonnegative-time-half-line-by-the-differential-spohn-interface",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_entropyProductionRate_nonneg",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.OneLevelDissipativePageWoottersCarrier.constrained_gksl_history where
  formalizes @ "claim:the-one-level-loss-gain-gksl-clock-has-a-nontrivial-page-wootters-carrier-with-nonzero-total-hamiltonian-and-nonzero-correlated-physical-history-state",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelHamiltonianConstraint_nonzero",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-carrier-packages-the-exact-conditional-gksl-evolution-and-a-physical-kernel-state-it-does-not-derive-the-dissipator-by-partial-trace-or-clock-conditioning"

/- ZIL-END -/
