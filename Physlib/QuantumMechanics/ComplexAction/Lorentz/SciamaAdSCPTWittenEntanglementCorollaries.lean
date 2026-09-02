/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Mathlib.LinearAlgebra.Matrix.PosDef
meta import Zil

/-!
# Four further Witten targets: vacuum fluctuations, trivial self-modular, the trace obstruction, Unruh thermality
(Witten, arXiv:1803.04993 §2.4, §3.2, §6, §5.4)

Continues the Witten arc (`SciamaAdSCPTArakiMonotonicityDistinguishability` covered §3.3–3.5) with the four
critical targets not yet formalized:

* **§2.4 — the important corollary of Reeh–Schlieder** (`vacuum_fluctuation_ne_zero`): over a separating
  vector, the vacuum two-point function of `a†a` never vanishes for nonzero local `a`:
  `⟨Ω, a†a Ω⟩ = ⟪aΩ, aΩ⟫ ≠ 0` — **every local observable fluctuates in the vacuum**.  Local number
  operators cannot annihilate the vacuum; a local detector always has a nonzero vacuum response.
* **§3.2 — the relative modular operator of a state with itself is trivial**
  (`relModular_self_trivial`): the diagonal relative modular eigenvalues are `Δᵢ = pᵢ/pᵢ = 1` and the
  self relative entropy vanishes — `Δ_{Ψ|Ψ} = Δ_Ψ` acts trivially on its defining state, the base point of
  the Araki construction.
* **§6 — the trace obstruction to Type III** (`normTrace_faithful`, `matrix_algebra_admits_faithful_trace`):
  the finite matrix algebra carries a **faithful, normalized, cyclic trace** (`τ(a†a) = 0 → a = 0`,
  `τ(1) = 1`, `τ(ab) = τ(ba)`) — precisely the structure a Type III factor lacks (Witten §6.4: no trace, no
  density matrices, no von Neumann entropy).  Finite dimensions are never Type III; the UV-divergent
  entanglement entropy of adjoining QFT regions (§6.5) is the continuum signature of that lack.
* **§5.4 — the accelerating observer** (`unruh_boltzmann_is_wedgeModular`): the Boltzmann weight at the
  **Unruh temperature** `T_U = ℏa/2πk_Bc` equals the **wedge-modular eigenvalue**,
  `e^{−E/k_BT_U} = Δ = e^{−2πκ/ℏ}` at `κ = cE/a` — Unruh's formulation of Bisognano–Wichmann: the wedge
  modular flow is the accelerated observer's proper-time evolution, and the vacuum looks exactly thermal at
  `T_U`.  (The wedge KMS shift itself is `WickClock.reversiblePhaseC_kms_shift`; the Hawking-horizon twin is
  `KayWaldHawkingKMSHorizon.hawkingBoltzmannWeight_is_wedgeModular`.)

Honest scope: §2.4 at the abstract separating-vector level (the spectrum-condition input remains the
cyclicity hypothesis, as in `SciamaAdSCPTReehSchliederCollapseObstruction`); §3.2 and the trace at the
finite/diagonal level matching the repo's Araki layer; §5.4 at the eigenvalue level — the operator
Bisognano–Wichmann theorem (`assumption:bisognano-wichmann-wedge` in the graph) is not discharged, this is
its eigenvalue-level face.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTArakiMonotonicityDistinguishability
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.Thermodynamics
open scoped InnerProductSpace Matrix ComplexOrder

/-! ## §1. Witten §2.4: every local observable fluctuates in the vacuum -/

/-- **[The vacuum fluctuation of a nonzero local operator never vanishes]** `⟨Ω, a†aΩ⟩ = ⟪aΩ, aΩ⟫ ≠ 0` for
nonzero `a ∈ M` over a separating `Ω` — Witten's "important corollary" of Reeh–Schlieder: local number-like
observables cannot annihilate the vacuum; a local detector always has a nonzero vacuum response. -/
theorem vacuum_fluctuation_ne_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {M : Set (H →L[ℂ] H)} {Ω : H} (hsep : IsSeparating M Ω)
    {a : H →L[ℂ] H} (haM : a ∈ M) (ha : a ≠ 0) :
    ⟪a Ω, a Ω⟫_ℂ ≠ 0 := by
  rw [inner_self_ne_zero]
  intro h0
  exact ha (hsep a haM h0)

/-! ## §2. Witten §3.2: the relative modular operator of a state with itself is trivial -/

/-- **[`Δ_{Ψ|Ψ}` is trivial]** — the diagonal relative modular eigenvalues of a state against itself are all
`1` (`Δᵢ = pᵢ/pᵢ = 1`), and the self relative entropy vanishes: the base point of Araki's construction. -/
theorem relModular_self_trivial {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) :
    (∀ i, p i / p i = 1) ∧ finiteRelativeEntropy p p = 0 :=
  ⟨fun i => div_self (hp i), finiteRelativeEntropy_self p⟩

/-! ## §3. Witten §6: the trace obstruction — finite dimensions are never Type III -/

/-- **[The normalized trace is faithful] `τ(a†a) = 0 → a = 0`.**  The Frobenius positivity of the matrix
trace: no nonzero matrix has vanishing `τ(a†a)`. -/
theorem normTrace_faithful {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℂ)
    (h : normTrace (Aᴴ * A) = 0) : A = 0 := by
  rw [normTrace, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (by simp [Fintype.card_ne_zero])
  · exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h

/-- **[The matrix algebra admits a faithful normalized cyclic trace]** — `τ(ab) = τ(ba)`, `τ(1) = 1`, and
`τ(a†a) = 0 → a = 0`: exactly the structure a **Type III factor lacks** (Witten §6.4 — no trace, hence no
density matrices and no von Neumann entropy).  Finite-dimensional algebras are never Type III; the
UV-divergent entanglement entropy of adjoining QFT regions is the continuum signature of that lack. -/
theorem matrix_algebra_admits_faithful_trace {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    (∀ a b : Matrix n n ℂ, normTrace (a * b) = normTrace (b * a))
      ∧ normTrace (1 : Matrix n n ℂ) = 1
      ∧ (∀ A : Matrix n n ℂ, normTrace (Aᴴ * A) = 0 → A = 0) :=
  ⟨normTrace_cyclic, normTrace_one, fun A h => normTrace_faithful A h⟩

/-! ## §4. Witten §5.4: the accelerating observer — Unruh thermality is the wedge modular eigenvalue -/

/-- **[The Unruh Boltzmann weight IS the wedge modular eigenvalue]**
`e^{−E/k_BT_U} = Δ = e^{−2πκ/ℏ}` at `κ = cE/a`, with `T_U = ℏa/2πk_Bc` — Unruh's formulation of
Bisognano–Wichmann at the eigenvalue level: the wedge modular flow is the accelerated observer's proper-time
evolution, and the Minkowski vacuum looks exactly thermal at the Unruh temperature. -/
theorem unruh_boltzmann_is_wedgeModular (ℏ kB c a E : ℝ)
    (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    kuikenWeight (kB * unruhTemperature ℏ kB c a) E
      = Physlib.QFT.PathIntegral.wedgeModularEigenvalue (c * E / a) ℏ := by
  unfold kuikenWeight unruhTemperature Physlib.QFT.PathIntegral.wedgeModularEigenvalue
  congr 1
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries.vacuum_fluctuation_ne_zero where
  formalizes @ "claim:over-a-separating-vacuum-every-nonzero-local-observable-has-nonvanishing-vacuum-fluctuation",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating.IsSeparating",
  caveat @ "epistemic:abstract-separating-vector-level-the-spectrum-condition-input-remains-the-cyclicity-hypothesis"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries.matrix_algebra_admits_faithful_trace where
  formalizes @ "claim:the-finite-matrix-algebra-admits-a-faithful-normalized-cyclic-trace-the-structure-a-type-three-factor-lacks",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.normTrace",
  caveat @ "epistemic:finite-witness-of-the-obstruction-no-type-classification-of-infinite-factors-is-formalized"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenEntanglementCorollaries.unruh_boltzmann_is_wedgeModular where
  formalizes @ "claim:the-unruh-boltzmann-weight-equals-the-wedge-modular-eigenvalue-at-boost-parameter-c-e-over-a",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
  supported_by @ "lean:Physlib.Thermodynamics.unruhTemperature",
  caveat @ "epistemic:eigenvalue-level-face-of-bisognano-wichmann-the-operator-theorem-remains-the-graph-assumption"

/- ZIL-END -/
