/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.EntropyProductionWorldline
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Physlib.Thermodynamics.SecondLaw.BipartiteEntropyProduction

/-! # SecondLaw — part `SergiOperatorTimeFree`. Full docstring in the umbrella module `Physlib.Thermodynamics.SecondLaw`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.Wick.Consistency

namespace Physlib.Thermodynamics.SecondLaw

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Phase D/D2/D3/E/Herm — Sergi operator layer

The operator-level Sergi superoperator, normalised generator, linear-entropy
no-go theorem, and HermitianMat lift live in
`Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity`.
This file resumes with the Wigner/mixed structure that still connects to the
SecondLaw namespace.

-/

/-! ## Phase G — Wigner-partial Sergi system

The Wigner-partial Sergi structure and its pointwise trace theorem live in
`Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity`, next
to the matrix Sergi generator they instantiate.

-/

/-! ## Phase C — Non-Hamiltonian flow + measure-compressibility arrow

The finite-dimensional Sergi-Ferrario flow structure, canonical symplectic
specialisation, and scalar compressibility bridge live in
`Physlib.ClassicalMechanics.HamiltonsEquations`.  This file keeps the
thermodynamic constructor below, which turns the imported compressibility
structure into an `EntropyArrowWorldline`.

-/

/-- **Constructor: classical non-Hamiltonian measure-compression →
`EntropyArrowWorldline`.**

Sergi & Ferrario's compressive flow (`κ ≤ 0`) yields an
`EntropyArrowWorldline` whose `S_I_monotone` field is *derived* — a
**classical** companion to the quantum `EntropyArrowWorldline.ofSergiConstantDecay`
constructor (Phase F).  The entropic arrow now has THREE independent
derivations on the branch:

* Zhang bipartite-unitary (quantum information / unitary invariance)
* Sergi constant-decay (non-Hermitian QM, anti-Hermitian H_I ⪰ 0)
* Sergi-Ferrario measure-compression (classical, antisymmetric B + κ ≤ 0) -/
noncomputable def EntropyArrowWorldline.ofNonHamiltonianMeasureBridge
    (M : NonHamiltonianMeasureBridge) : EntropyArrowWorldline where
  ℏ := M.ℏ
  ℏ_pos := M.ℏ_pos
  S_I_along := M.S_I_along
  τ_ent_along := M.τ_ent_along
  τ_ent_eq := M.τ_ent_along_eq_S_I_div_hbar
  S_I_monotone := fun {_ _} h => M.S_I_along_monotone h
  S_I_at_zero_nonneg := by rw [M.S_I_along_at_zero]

/-! ## Phase H/I — Madelung and Liouville Sergi bridges

The Madelung amplitude-decay bridge and the Liouville-space realisation of
the normalised Sergi generator live in
`Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity`.
`SecondLaw` keeps the entropy-arrow constructors that use those underlying spaces.

-/

/-! ## §∞ — The second law as a theorem: entropic time derived from entropy production (time-free)

The thesis sharpened to its load-bearing form. In `EntropyArrowWorldline` the entropy production
`S_I : ℝ → ℝ` is indexed by an *external* time `t`, and the arrow rides on an *assumed* `S_I_monotone`
field. That smuggles a clock in. Here we remove it: **entropic time is a pure derived computation on the
entropy produced, and the second law is a theorem** — no external time parameter, no assumed monotonicity.

Given any entropy production `S_I` (a number computed from a process — a relative entropy, a von Neumann
entropy gap, a GKLS dissipation) and `ℏ > 0`, the entropic time is the readout

  `τ_ent := S_I / ℏ`     (`entropicTimeOf`),

and the second law is the theorem package `secondLaw_timeFree`: `τ_ent ≥ 0` (the arrow), entropy-order is
*exactly* entropic-time order, and `τ_ent = 0 ⟺ S_I = 0` (reversible). Each is derived from `S_I ≥ 0`,
which is itself a theorem at every grounding:

* relative entropy `D(ρ‖σ) ≥ 0` — the entropic clock is the state divergence (`entropicTime_relEnt_nonneg`);
* the GKLS dissipation `∑ⱼ Tr(Lⱼ†Lⱼρ).re ≥ 0` (`gklsEntropicRate_nonneg`, the Lindblad second law) —
  entropic time computed from the jump operators and the state (`entropicTime_gkls_nonneg`);
* the bipartite von Neumann entropy gap `ΔS ≥ 0` (Zhang) — `secondLaw_bipartite_entropicTime_nonneg`.

There is no `t` anywhere in this section: entropic time is *computed from* entropy production, exactly the
EPT thesis that time is a side effect of entropy increase, not an independent axis.
-/

open Physlib.QuantumMechanics.Lindblad
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity

/-- **Entropic time as a derived computation on entropy production** (time-free): `τ_ent := S_I / ℏ`.
A pure readout of the entropy produced by a process — not a function of any external clock. -/
abbrev entropicTimeOf (S_I ℏ : ℝ) : ℝ :=
  Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime S_I ℏ

/-- Zero entropy produced ⟹ zero entropic time. -/
@[simp] theorem entropicTimeOf_zero_entropy (ℏ : ℝ) : entropicTimeOf 0 ℏ = 0 := by
  exact entropicProperTime_reversible ℏ

/-- **Second-law arrow (time-free), a theorem.** Non-negative entropy production yields non-negative
entropic time — derived from `S_I ≥ 0`, with no time parameter and no assumed monotonicity field. -/
theorem entropicTimeOf_nonneg {S_I ℏ : ℝ} (hS : 0 ≤ S_I) (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf S_I ℏ := by
  exact entropicProperTime_nonneg S_I ℏ hS hℏ

/-- **Entropy order is exactly entropic-time order** (time-free): `τ_ent` has no ordering information
beyond the entropy produced. -/
theorem entropicTimeOf_le_iff {S_I₁ S_I₂ ℏ : ℝ} (hℏ : 0 < ℏ) :
    entropicTimeOf S_I₁ ℏ ≤ entropicTimeOf S_I₂ ℏ ↔ S_I₁ ≤ S_I₂ := by
  unfold entropicTimeOf
  unfold Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime
  exact div_le_div_iff_of_pos_right hℏ

/-- **Reversibility (time-free): zero entropic time ⟺ zero entropy production.** -/
theorem entropicTimeOf_eq_zero_iff {S_I ℏ : ℝ} (hℏ : 0 < ℏ) :
    entropicTimeOf S_I ℏ = 0 ↔ S_I = 0 := by
  unfold entropicTimeOf
  unfold Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity.entropicProperTime
  exact div_eq_zero_iff.trans (or_iff_left (ne_of_gt hℏ))

/-- **The second law as a theorem (time-free).** For any non-negative entropy production `S_I` and
`ℏ > 0`: the entropic time `τ_ent = S_I/ℏ` is non-negative (the arrow), ordered exactly by `S_I` (entropy
order = time order), and zero iff the process is reversible (`S_I = 0`). Entropic time is a pure derived
computation on the entropy produced — no external time, no assumed monotonicity. This is the theorem the
`EntropyArrowWorldline` structure approximated with an indexed `S_I : ℝ → ℝ` and an `S_I_monotone` field. -/
theorem secondLaw_timeFree {S_I ℏ : ℝ} (hS : 0 ≤ S_I) (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf S_I ℏ
      ∧ (∀ S_I' : ℝ, entropicTimeOf S_I ℏ ≤ entropicTimeOf S_I' ℏ ↔ S_I ≤ S_I')
      ∧ (entropicTimeOf S_I ℏ = 0 ↔ S_I = 0) :=
  ⟨entropicTimeOf_nonneg hS hℏ, fun _ => entropicTimeOf_le_iff hℏ, entropicTimeOf_eq_zero_iff hℏ⟩

/-- **Grounding 1 — entropic time from quantum relative entropy (time-free).** The relative entropy
`D(ρ‖σ) ≥ 0` computes a non-negative entropic time `D(ρ‖σ)/ℏ` — the entropic clock *is* the state
divergence, with no external time. -/
theorem entropicTime_relEnt_nonneg (ρ σ : MState d) {ℏ : ℝ} (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf (entropicProperTime ρ σ).toReal ℏ :=
  entropicTimeOf_nonneg (QuantumInfo.Finite.entropicProperTime_toReal_nonneg ρ σ) hℏ

/-- **Reversible coincidence:** the relative-entropy entropic time vanishes at `ρ = σ` — no divergence,
no entropic time. -/
theorem entropicTime_relEnt_self (ρ : MState d) (ℏ : ℝ) :
    entropicTimeOf (entropicProperTime ρ ρ).toReal ℏ = 0 := by
  rw [entropicProperTime_self]; simp [entropicTimeOf]

/-- **Grounding 2 — entropic time from GKLS dissipation (time-free), depending on the recent theorem.**
The Lindblad / GKLS entropy-production rate `∑ⱼ Tr(Lⱼ†Lⱼρ).re ≥ 0` (`gklsEntropicRate_nonneg`, the
Lindblad–Spohn second law) computes a non-negative entropic time `λ/ℏ ≥ 0` — derived directly from the
jump operators `L` and the state `ρ`, with no time parameter. -/
theorem entropicTime_gkls_nonneg {ι : Type*} [Fintype ι]
    (L : ι → Matrix d d ℂ) (ρ : MState d) {ℏ : ℝ} (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf (gklsEntropicRate L ρ) ℏ :=
  entropicTimeOf_nonneg (gklsEntropicRate_nonneg L ρ) hℏ

/-- **Grounding 3 — the second law as a theorem from the bipartite von Neumann entropy gap (time-free).**
Zhang's `ΔS ≥ 0` (`entropyGap_nonneg`, unitary invariance + sub-additivity) computes a non-negative
entropic time `ΔS/ℏ` — derived from the information lost to entanglement under partial trace, with no
external time. -/
theorem secondLaw_bipartite_entropicTime_nonneg
    {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (E : BipartiteUnitaryEvent d₁ d₂) :
    0 ≤ entropicTimeOf E.entropyGap E.ℏ :=
  entropicTimeOf_nonneg E.entropyGap_nonneg E.ℏ_pos

/-! ## §∞.2 — Kinematic entropic time, Misra conjugate-time operator, timelike↔spacelike Wick exchange

The time-free entropic time `entropicTimeOf` linked to the relativistic-kinematic structure of the metric
`S`-norm:

* the entropy production is the **kinematic entropic time** `binEntropy((1 − m)/2)` with boost velocity
  `m = tanh θ` (rapidity θ), composing by relativistic velocity addition (`kinematic_velocity_addition`);
* the irreversible (dissipative) generator includes the **Misra conjugate internal-time operator**
  `i[L,T] = I` (`liouvillian_age_ccr`) — the time *observable* on the continuous spectrum;
* the **Wick rotation** `L(i·q) = −L(q)` exchanges the timelike (kinematic, reversible) and spacelike
  (entropic, irreversible) sectors (`wick_exchanges_sectors`) — the metric-signature flip between the
  reversible boost clock and the irreversible entropic clock.
-/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-- **The kinematic entropic time drives the time-free second law.** Its entropic time
`entropicTimeOf (binEntropy((1 − tanh θ)/2)) ℏ ≥ 0` is the second-law arrow of a boost at rapidity θ —
derived from `kinematicEntropy_nonneg`, time-free. -/
theorem secondLaw_kinematicEntropy {θ ℏ : ℝ} (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf (kinematicEntropy θ) ℏ :=
  entropicTimeOf_nonneg (kinematicEntropy_nonneg θ) hℏ

/-- **The kinematic / Misra / Wick link.** For the time-free second law: the boost velocity `m = tanh θ`
composes relativistically; the kinematic entropic time `binEntropy((1 − m)/2) ≥ 0` is a valid entropy
production (the second-law arrow); the irreversible generator includes the Misra `i[L,T] = I`; and the Wick
rotation `L(i·q) = −L(q)` exchanges timelike↔spacelike — the reversible (kinematic) and irreversible
(entropic) sectors of the metric `S`-norm. -/
theorem secondLaw_kinematic_misra_wick {θ ℏ : ℝ} (hℏ : 0 < ℏ) (a b : ℝ)
    (f : ℝ → ℂ) (lam : ℝ) (hf : DifferentiableAt ℝ f lam) (q : ℂ) :
    (Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b))
      ∧ (0 ≤ entropicTimeOf (kinematicEntropy θ) ℏ)
      ∧ (Complex.I * (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian
            (Physlib.QuantumMechanics.RelationalTime.ageOperator f) lam
          - Physlib.QuantumMechanics.RelationalTime.ageOperator
            (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian f) lam) = f lam)
      ∧ (lorentzianForm (Complex.I * q) = - lorentzianForm q) :=
  ⟨kinematic_velocity_addition a b, secondLaw_kinematicEntropy hℏ,
   Physlib.QuantumMechanics.RelationalTime.liouvillian_age_ccr f lam hf,
   wick_exchanges_sectors q⟩


end Physlib.Thermodynamics.SecondLaw

end
