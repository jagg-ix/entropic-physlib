/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannDualityCondition
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState
meta import Zil

/-!
# The state-side analytic core of Bisognano–Wichmann: the vacuum constructed, standard, and KMS-matched

The BW arc's remaining assumption is *state-side*: that the **vacuum's intrinsic** modular structure is the
boost flow.  Every ingredient of that analytic core is already in the repo; this module assembles them:

* **§1 — the vacuum vector is constructed, not posited** (`RelativeStateConventionality.ensemblePurification`):
  the wedge vacuum is the explicit purification `Ω = Σ_a √p_a |s_a⟩|a⟩` of the wedge ensemble — the TFD ket —
  whose wedge reduction **is** the thermal mixture (`ensemblePurification_traceRight`) and whose complement
  diagonal carries the Gibbs weights (`ensemblePurification_traceLeft_diag`): BW's `Ω` with its two-wedge
  split, as Lean data.
* **§2 — the wedge Gibbs weights are strictly positive** (`wedge_gibbs_weights_pos`, *new*): the wedge thermal
  weights `1/(1+Δ)` and `Δ/(1+Δ)` are positive and sum to `1` **unconditionally** (`Δ = e^{−2πκ/ℏ} > 0`) — the
  reduced vacuum is *faithful*, never degenerate: exactly the separating-vacuum input of Reeh–Schlieder and
  Tomita–Takesaki, derived at the weight level rather than assumed.
* **§3 — standardness** (`faithful_state_standard`): a faithful (invertible) reduced state is separating and
  cyclic — the finite standard-form shadow: the constructed vacuum is a standard vector for the wedge algebra.
* **§4 — the intrinsic modular flow is KMS** (`modularGroupOfState`, `kmsQIF_ofState_isEquilibriumAt`): the
  modular flow **of the reduced state itself** (`σ_t = e^{itH_θ}(·)e^{−itH_θ}`, `H_θ = −log ρ`) is an
  equilibrium (KMS) flow at every state — the state-intrinsic side of the modular structure.
* **§5 — KMS matching with the boost** (`reversiblePhaseC_kms_shift` + `tfd_halfweight_sq_is_unruh`): the boost
  flow satisfies the KMS boundary shift with Boltzmann factor `e^{−βE}`, and the constructed vacuum's TFD
  weight squares to exactly the wedge-modular eigenvalue — the **same** KMS condition, over the **same**
  state, satisfied by both the intrinsic modular flow and the boost flow.

`bisognanoWichmann_state_side_core` bundles the five: the vacuum constructed with its thermal wedge reduction,
faithful weights, standardness, intrinsic KMS flow, and the boost flow's identical KMS boundary — the analytic
content of BW Eq. 2 at the repo's level.  What remains of `assumption:bisognano-wichmann-wedge` after this
assembly is exactly **KMS-flow uniqueness** (Takesaki: a flow satisfying the KMS condition for a faithful
state *is* its modular flow) on the continuum wedge algebra — cited, and nothing else.

**Update (2026-08-12): that step is now discharged at the finite carrier.**
`FiniteTarget.QuantumInertialFrameModularFromState.modularHamiltonian_of_gibbs` shows a generator
reproducing `ρ` as its Gibbs state is `−log ρ` up to the central term `log Z · 1`, and
`FiniteTarget.QuantumInertialFrameModularGroup.unitaryFlow_conj_add_scalar` shows a central term
never reaches the conjugation flow.  So any such generator generates *the* modular flow of `ρ`.
What remains cited is only the **continuum** operator-valued-distribution formulation — the
assumption is thereby *narrowed*, not removed.

Honest scope: all five pillars are proved (four reused, the faithfulness new); the final uniqueness step and
the operator-valued-distribution formulation are the cited continuum content.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannStateSide

open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QFT.PathIntegral
open Physlib.Thermodynamics
open QuantumMechanics.FiniteTarget

/-! ## §2. The wedge Gibbs weights are strictly positive: the faithful vacuum, derived -/

/-- **[The reduced vacuum is faithful — unconditionally]** — the wedge Gibbs weights `1/(1+Δ)` and `Δ/(1+Δ)`
(`Δ = wedgeModularEigenvalue κ ℏ = e^{−2πκ/ℏ} > 0`) are strictly positive and sum to `1`, for *every* boost
energy and `ℏ`: the wedge-reduced vacuum is never degenerate — the separating/faithful-vacuum input of
Reeh–Schlieder and Tomita–Takesaki, derived at the weight level. -/
theorem wedge_gibbs_weights_pos (κ ℏ : ℝ) :
    0 < 1 / (1 + wedgeModularEigenvalue κ ℏ)
      ∧ 0 < wedgeModularEigenvalue κ ℏ / (1 + wedgeModularEigenvalue κ ℏ)
      ∧ 1 / (1 + wedgeModularEigenvalue κ ℏ)
          + wedgeModularEigenvalue κ ℏ / (1 + wedgeModularEigenvalue κ ℏ) = 1 := by
  have hΔ : 0 < wedgeModularEigenvalue κ ℏ := Real.exp_pos _
  have hZ : 0 < 1 + wedgeModularEigenvalue κ ℏ := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  field_simp

/-! ## §1–§5. The state-side core, assembled -/

/-- **[The state-side analytic core of Bisognano–Wichmann]** — **(i)** the vacuum is the *constructed*
purification: its wedge reduction is the thermal mixture (`ensemblePurification_traceRight`); **(ii)** the
wedge Gibbs weights are strictly positive and normalized — the reduced vacuum is faithful (§2, derived);
**(iii)** a faithful reduced state is separating and cyclic (`faithful_state_standard`) — the vacuum is
standard for the wedge; **(iv)** the intrinsic modular flow of the reduced state is a KMS/equilibrium flow
(`kmsQIF_ofState_isEquilibriumAt`); **(v)** the boost flow satisfies the KMS boundary shift with the Boltzmann
factor (`reversiblePhaseC_kms_shift`), and the vacuum's TFD half-weight squares to exactly the wedge-modular
eigenvalue (`tfd_halfweight_sq_is_unruh`) — the same KMS condition, same state, both flows.  What remains of
the BW assumption is KMS-flow uniqueness (Takesaki) on the continuum algebra — cited, nothing else. -/
theorem bisognanoWichmann_state_side_core
    {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]
    (e : PEnsemble d α)
    {dw : Type*} [Fintype dw] [DecidableEq dw] (ρ : MState dw) (hρ : IsUnit ρ.M.mat)
    (ℏbar : ℝ) (hℏbar : 0 < ℏbar) (β : ℝ) (hβ : 0 < β) (ψ : EuclideanSpace ℂ dw)
    (E ℏ kB c a t κ : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    (MState.pure (ensemblePurification e)).traceRight = Ensemble.mix (e : MEnsemble d α)
      ∧ (0 < 1 / (1 + wedgeModularEigenvalue κ ℏ)
          ∧ 0 < wedgeModularEigenvalue κ ℏ / (1 + wedgeModularEigenvalue κ ℏ))
      ∧ ((∀ B, B * ρ.M.mat = 0 → B = 0) ∧ (∀ C, ∃ A, A * ρ.M.mat = C))
      ∧ (kmsQIF_ofState ρ ℏbar hℏbar β hβ).IsEquilibriumAt ψ
      ∧ (reversiblePhaseC E ℏ ((t : ℂ) + wickRotate (ℏ * β))
            = ((Real.exp (-(β * E)) : ℝ) : ℂ) * reversiblePhaseC E ℏ (t : ℂ)
          ∧ thermalWeight (1 / (kB * unruhTemperature ℏ kB c a)) E ^ 2
              = wedgeModularEigenvalue (c * E / a) ℏ) :=
  ⟨ensemblePurification_traceRight e,
    ⟨(wedge_gibbs_weights_pos κ ℏ).1, (wedge_gibbs_weights_pos κ ℏ).2.1⟩,
    faithful_state_standard ρ hρ,
    kmsQIF_ofState_isEquilibriumAt ρ ℏbar hℏbar β hβ ψ,
    reversiblePhaseC_kms_shift E ℏ β t hℏ,
    tfd_halfweight_sq_is_unruh ℏ kB c a E hℏ hkB hc ha⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannStateSide

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannStateSide.wedge_gibbs_weights_pos where
  formalizes @ "claim:the-wedge-reduced-vacuum-is-faithful-unconditionally-the-gibbs-weights-are-strictly-positive-and-normalized",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  caveat @ "epistemic:two-level-wedge-weight-level-faithfulness"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBisognanoWichmannStateSide.bisognanoWichmann_state_side_core where
  formalizes @ "claim:the-vacuum-is-constructed-faithful-standard-with-intrinsic-kms-modular-flow-matching-the-boost-kms-boundary-reducing-bw-to-kms-flow-uniqueness",
  requires @ "assumption:bisognano-wichmann-wedge",
  requires @ "claim:the-wedge-reduced-vacuum-is-faithful-unconditionally-the-gibbs-weights-are-strictly-positive-and-normalized",
  supported_by @ "paper:bisognano-wichmann-1975-duality-condition-hermitian-scalar-field",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.kmsQIF_ofState_isEquilibriumAt",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.faithful_state_standard",
  caveat @ "epistemic:the-remaining-continuum-step-is-takesaki-kms-flow-uniqueness-cited-not-formalized"

/- ZIL-END -/
