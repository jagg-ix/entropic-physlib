/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star

meta import Zil

/-!
# Coupling quantum fields to gravity violates the superposition principle (Ipek–Caticha)

Formalizes the central *prediction* of Ipek–Caticha (arXiv:2006.05036): coupling the entropic-dynamics quantum
field to dynamical gravity makes the evolution **nonlinear**, violating the quantum superposition principle. The
mechanism is the metric backreaction: in flat space the functional Schrödinger generator `−iĤ` is a *fixed linear*
operator (Eq. 108 with fixed `g`), but with dynamical gravity the metric is *sourced by the state* `Ψ` (Eq. 104,
the geometry responds to `⟨Ĥ⟩` / the probability `ρ`), so the effective generator acquires a term proportional to
`|Ψ|² = ρ` (the Born rule) and becomes nonlinear.

Modeling the single-mode wave function `Ψ ∈ ℂ`:

* the **flat-space generator** `𝓛₀(ψ) = E·ψ` is **additive and homogeneous** (`flatGenerator_additive`,
  `flatGenerator_smul`) — a linear operator, so superposition holds;
* the **gravitational backreaction** `𝓑(ψ) = λ·|ψ|²·ψ` is sourced by the probability `ρ = |ψ|²`
  (`gravBackreaction_born`: on `Ψ = ρ^{1/2}e^{iΦ}` it is `λρ·Ψ`, reusing the Born rule
  `edWaveFunction_modulus_sq`);
* the **gravity-coupled generator** `𝓛(ψ) = E·ψ + λ|ψ|²ψ` **violates superposition** for `λ ≠ 0`
  (`gravGenerator_superposition_violation`): `𝓛(ψ₁+ψ₂) ≠ 𝓛(ψ₁) + 𝓛(ψ₂)` — the `|ψ|²` backreaction is not
  additive;
* in the **no-gravity limit** `λ = 0` the generator reduces to the flat linear one (`gravGenerator_flat_limit`), so
  superposition is restored — the violation is *exactly* the gravitational coupling.

So the Ipek–Caticha prediction is this structural dichotomy: fixed background ⟹ linear generator ⟹ superposition;
dynamical gravity ⟹ state-sourced `|Ψ|²` term ⟹ nonlinear generator ⟹ superposition violated. The nonlinearity is
driven by the Born-rule probability `ρ = |Ψ|²`, the same `ρ` that sources the geometry.

* **§A — the flat-space generator is linear (superposition holds)** (`flatGenerator`, `flatGenerator_additive`,
  `flatGenerator_smul`).
* **§B — the gravitational backreaction is the Born-rule probability** (`gravBackreaction`,
  `gravBackreaction_born`).
* **§C — the gravity-coupled generator violates superposition** (`gravGenerator`,
  `gravGenerator_superposition_violation`, `gravGenerator_flat_limit`).

**Honest layering.** The linearity of the flat generator, the Born-rule form of the backreaction, and the failure
of additivity are exact `ℂ` algebra on a single-mode wave function, reusing `edWaveFunction` and its Born rule. The
full functional Schrödinger equation, the metric source equation (Eq. 104), and the field-theoretic
superspace are the referenced content. The single-mode `λ|ψ|²ψ` term is a faithful minimal model of the
state-dependent (nonlinear) generator, not the full backreaction functional. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 104, 108; nonlinearity / superposition violation). Repo carrier:
  `EntropicTime.EntropicDynamicsWaveFunctionReconstruction` (`edWaveFunction`, `edWaveFunction_modulus_sq`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open scoped Topology

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation


/-- **The flat-space Schrödinger generator** `𝓛₀(ψ) = E·ψ` — multiplication by the fixed (background) Hamiltonian
coefficient `E`, the linear generator of the functional Schrödinger evolution on a fixed metric (Ipek–Caticha
Eq. 108 with fixed `g`). -/
noncomputable def flatGenerator (E : ℝ) (ψ : ℂ) : ℂ := (E : ℂ) * ψ

/-- **[The flat generator is additive] `𝓛₀(ψ₁+ψ₂) = 𝓛₀(ψ₁) + 𝓛₀(ψ₂)`.** The fixed-background generator respects
superposition — linear combinations of solutions evolve as the combination. -/
lemma flatGenerator_additive (E : ℝ) (ψ₁ ψ₂ : ℂ) :
    flatGenerator E (ψ₁ + ψ₂) = flatGenerator E ψ₁ + flatGenerator E ψ₂ := by
  unfold flatGenerator; ring

/-- **[The flat generator is homogeneous] `𝓛₀(c·ψ) = c·𝓛₀(ψ)`.** -/
lemma flatGenerator_smul (E : ℝ) (c ψ : ℂ) :
    flatGenerator E (c * ψ) = c * flatGenerator E ψ := by
  unfold flatGenerator; ring


/-- **The gravitational backreaction term** `𝓑(ψ) = λ·|ψ|²·ψ` — the state-sourced contribution to the generator
when the metric responds to the quantum state (Ipek–Caticha Eq. 104), proportional to the probability `ρ = |ψ|²`. -/
noncomputable def gravBackreaction (lam : ℝ) (ψ : ℂ) : ℂ :=
  (lam : ℂ) * (Complex.normSq ψ : ℂ) * ψ

/-- **[The backreaction is sourced by the Born-rule probability] `𝓑(Ψ) = λρ·Ψ`.** On the entropic-dynamics wave
function `Ψ = ρ^{1/2}e^{iΦ}` the backreaction term is `λρ·Ψ`, since `|Ψ|² = ρ` is the Born rule
(`edWaveFunction_modulus_sq`) — the geometry is sourced by the probability, so the nonlinearity is too. -/
lemma gravBackreaction_born (lam ρ Φ : ℝ) (hρ : 0 ≤ ρ) :
    gravBackreaction lam (edWaveFunction ρ Φ) = ((lam * ρ : ℝ) : ℂ) * edWaveFunction ρ Φ := by
  unfold gravBackreaction
  have hn : Complex.normSq (edWaveFunction ρ Φ) = ρ := by
    rw [Complex.normSq_eq_norm_sq]
    exact edWaveFunction_modulus_sq ρ Φ hρ
  rw [hn]
  push_cast
  ring


/-- **The gravity-coupled Schrödinger generator** `𝓛(ψ) = E·ψ + λ|ψ|²ψ` — the flat generator plus the
state-sourced backreaction, the effective (nonlinear) generator when quantum matter is coupled to dynamical
gravity. -/
noncomputable def gravGenerator (E lam : ℝ) (ψ : ℂ) : ℂ :=
  flatGenerator E ψ + gravBackreaction lam ψ

/-- **[The gravity-coupled generator violates superposition] for `λ ≠ 0`.** There exist states `ψ₁, ψ₂` with
`𝓛(ψ₁+ψ₂) ≠ 𝓛(ψ₁) + 𝓛(ψ₂)`: the `|ψ|²` backreaction breaks additivity (witnessed by `ψ₁ = ψ₂ = 1`, defect `6λ`).
Coupling quantum fields to gravity destroys the linear superposition principle — the central Ipek–Caticha
prediction. -/
lemma gravGenerator_superposition_violation (E lam : ℝ) (hlam : lam ≠ 0) :
    ∃ ψ₁ ψ₂ : ℂ, gravGenerator E lam (ψ₁ + ψ₂) ≠ gravGenerator E lam ψ₁ + gravGenerator E lam ψ₂ := by
  refine ⟨1, 1, ?_⟩
  have hdiff : gravGenerator E lam ((1 : ℂ) + 1)
      - (gravGenerator E lam 1 + gravGenerator E lam 1) = ((6 * lam : ℝ) : ℂ) := by
    unfold gravGenerator flatGenerator gravBackreaction
    have h2 : Complex.normSq ((1 : ℂ) + 1) = 4 := by
      rw [show (1 : ℂ) + 1 = ((2 : ℝ) : ℂ) by norm_num, Complex.normSq_ofReal]; norm_num
    have h1 : Complex.normSq (1 : ℂ) = 1 := Complex.normSq_one
    rw [h2, h1]
    push_cast
    ring
  intro h
  rw [h, sub_self] at hdiff
  have h6 : (6 * lam : ℝ) = 0 := by exact_mod_cast hdiff.symm
  exact hlam (by linarith)

/-- **[The no-gravity limit restores superposition] `𝓛|_{λ=0} = 𝓛₀`.** At zero gravitational coupling the
generator is the flat linear one, so superposition holds — the violation is exactly the gravitational backreaction. -/
lemma gravGenerator_flat_limit (E : ℝ) (ψ : ℂ) : gravGenerator E 0 ψ = flatGenerator E ψ := by
  unfold gravGenerator gravBackreaction
  simp

/-! ## D. Uniqueness of the local cubic backreaction -/

/-- A local backreaction is gauge-covariant cubic when complex rescaling by `c` changes it by
`c |c|²`.  Its unit-modulus part is the `U(1)` gauge weight one, while its positive radial part
is cubic homogeneity. -/
def IsGaugeCovariantCubic (B : ℂ → ℂ) : Prop :=
  ∀ c ψ, B (c * ψ) = c * (Complex.normSq c : ℂ) * B ψ

/-- Every gauge-covariant cubic local law is fixed by its value at the unit state. -/
lemma gaugeCovariantCubic_eq (B : ℂ → ℂ) (hB : IsGaugeCovariantCubic B) (ψ : ℂ) :
    B ψ = B 1 * (Complex.normSq ψ : ℂ) * ψ := by
  have h := hB ψ 1
  simpa only [mul_one] using h.trans (by ring)

/-- The Ipek--Caticha Born-density backreaction has the required gauge covariance and cubic
homogeneity. -/
lemma gravBackreaction_isGaugeCovariantCubic (lam : ℝ) :
    IsGaugeCovariantCubic (gravBackreaction lam) := by
  intro c ψ
  simp only [gravBackreaction, map_mul]
  push_cast
  ring

/-- **Unique irreversible local law in the stated class.**  A gauge-covariant cubic
backreaction normalized by `B(1) = λ` is exactly `λ |ψ|² ψ`.  The result is a uniqueness
theorem inside this explicit locality/covariance/homogeneity class, not a claim that those
physical requirements themselves have been derived. -/
lemma gaugeCovariantCubic_unique (B : ℂ → ℂ) (lam : ℝ)
    (hB : IsGaugeCovariantCubic B) (hB1 : B 1 = (lam : ℂ)) :
    B = gravBackreaction lam := by
  funext ψ
  rw [gaugeCovariantCubic_eq B hB ψ, hB1]
  rfl

/-- The irreversible sign choice of the cubic backreaction. -/
noncomputable def irreversibleGravBackreaction (γ : ℝ) (ψ : ℂ) : ℂ :=
  gravBackreaction (-γ) ψ

/-- The instantaneous Born-norm rate associated with a vector field `B`. -/
noncomputable def bornNormSqRate (B : ℂ → ℂ) (ψ : ℂ) : ℝ :=
  2 * (star ψ * B ψ).re

/-- The irreversible cubic law decreases Born norm at the explicit quartic rate. -/
lemma irreversibleGravBackreaction_rate (γ : ℝ) (ψ : ℂ) :
    bornNormSqRate (irreversibleGravBackreaction γ) ψ =
      -2 * γ * (Complex.normSq ψ) ^ 2 := by
  simp [bornNormSqRate, irreversibleGravBackreaction, gravBackreaction,
    Complex.mul_re, Complex.normSq_apply]
  ring

/-- A nonnegative irreversible coupling makes the Born-norm rate nonpositive. -/
lemma irreversibleGravBackreaction_rate_nonpos (γ : ℝ) (hγ : 0 ≤ γ) (ψ : ℂ) :
    bornNormSqRate (irreversibleGravBackreaction γ) ψ ≤ 0 := by
  rw [irreversibleGravBackreaction_rate]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num : -2 ≤ (0 : ℝ)) hγ)
    (sq_nonneg _)

/-- **Unique irreversible backreaction in the stated class.**  Gauge-covariant cubic
homogeneity plus the dissipative normalization `B(1) = -γ` fixes the law to
`-γ |ψ|² ψ`; for `γ ≥ 0` its Born-norm rate is nonpositive. -/
lemma irreversibleGaugeCovariantCubic_unique (B : ℂ → ℂ) (γ : ℝ)
    (hB : IsGaugeCovariantCubic B) (hB1 : B 1 = (-(γ : ℝ) : ℂ)) :
    B = irreversibleGravBackreaction γ := by
  unfold irreversibleGravBackreaction
  apply gaugeCovariantCubic_unique B (-γ) hB
  simpa using hB1

/-! ## E. Nonlinear evolution on a continuum configuration carrier -/

/-- The pointwise nonlinear CAT/EPT generator on complex continuous fields over `X`.
On compact `X`, `C(X, ℂ)` is an infinite-dimensional Banach space whenever `X` has infinitely
many points. -/
noncomputable def continuumGravGenerator {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℂ)) (lam : ℝ) (ψ : C(X, ℂ)) : C(X, ℂ) :=
  E * ψ + (lam : ℂ) • ((starL' ℝ) ψ * ψ * ψ)

/-- The continuum generator evaluates pointwise to the spatial energy plus Born-density
backreaction. -/
lemma continuumGravGenerator_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℂ)) (lam : ℝ) (ψ : C(X, ℂ)) (x : X) :
    continuumGravGenerator E lam ψ x =
      E x * ψ x + (lam : ℂ) * (Complex.normSq (ψ x) : ℂ) * ψ x := by
  simp [continuumGravGenerator, Complex.normSq_eq_conj_mul_self]
  ring

/-- For a constant real energy, the continuum generator is exactly the existing scalar
Ipek--Caticha generator at every point. -/
lemma continuumGravGenerator_const_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (E lam : ℝ) (ψ : C(X, ℂ)) (x : X) :
    continuumGravGenerator (ContinuousMap.const X (E : ℂ)) lam ψ x =
      gravGenerator E lam (ψ x) := by
  rw [continuumGravGenerator_apply]
  simp [gravGenerator, flatGenerator, gravBackreaction]

/-- The nonlinear continuum CAT/EPT generator is continuously differentiable as a real
Banach-space vector field. -/
lemma continuumGravGenerator_contDiff {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℂ)) (lam : ℝ) :
    ContDiff ℝ 1 (continuumGravGenerator E lam) := by
  unfold continuumGravGenerator
  fun_prop

/-- **Local existence for the full nonlinear continuum generator.**  Every continuous
initial field on a compact carrier has a differentiable solution on a nontrivial time
interval.  This is a genuine Banach-space evolution theorem, not a finite-mode truncation. -/
lemma exists_local_continuumGrav_solution {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Infinite X]
    (E : C(X, ℂ)) (lam : ℝ) (ψ₀ : C(X, ℂ)) (t₀ : ℝ) :
    ∃ ψ : ℝ → C(X, ℂ), ψ t₀ = ψ₀ ∧ ∃ ε > 0,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt ψ (continuumGravGenerator E lam (ψ t)) t := by
  exact (continuumGravGenerator_contDiff E lam).contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- Two continuum CAT/EPT solutions through the same initial field agree near the initial
time.  Together with `exists_local_continuumGrav_solution`, this is local well-posedness. -/
lemma continuumGrav_solution_eventuallyEq {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Infinite X]
    (E : C(X, ℂ)) (lam : ℝ) (ψ₀ : C(X, ℂ)) (t₀ : ℝ)
    (ψ χ : ℝ → C(X, ℂ))
    (hψ₀ : ψ t₀ = ψ₀) (hχ₀ : χ t₀ = ψ₀)
    (hψ : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt ψ (continuumGravGenerator E lam (ψ t)) t)
    (hχ : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt χ (continuumGravGenerator E lam (χ t)) t) :
    ψ =ᶠ[𝓝 t₀] χ := by
  obtain ⟨K, s, hs, hlip⟩ :=
    (continuumGravGenerator_contDiff E lam).contDiffAt.exists_lipschitzOnWith
  have hψAt := hψ.self_of_nhds
  have hχAt := hχ.self_of_nhds
  have hψs : ∀ᶠ t in 𝓝 t₀, ψ t ∈ s :=
    hψAt.continuousAt.eventually (hψ₀.symm ▸ hs)
  have hχs : ∀ᶠ t in 𝓝 t₀, χ t ∈ s :=
    hχAt.continuousAt.eventually (hχ₀.symm ▸ hs)
  apply ODE_solution_unique_of_eventually
    (v := fun _ ↦ continuumGravGenerator E lam)
    (s := fun _ ↦ s) (K := K)
    (Filter.Eventually.of_forall fun _ ↦ hlip)
    (hψ.and hψs) (hχ.and hχs)
  exact hψ₀.trans hχ₀.symm

/-! ## F. Global positive-time flow for the unique irreversible cubic sector -/

/-- Algebraic positive-time solution before its safe all-real-time extension. -/
noncomputable def rawIrreversibleCubicFlow (γ t : ℝ) (ψ : ℂ) : ℂ :=
  ψ / (Real.sqrt (1 + 2 * γ * t * Complex.normSq ψ) : ℂ)

/-- Safe positive denominator, using `max t 0` outside the physical time half-line. -/
noncomputable def cubicDampingDenominator (γ t : ℝ) (ψ : ℂ) : ℝ :=
  Real.sqrt (1 + 2 * γ * max t 0 * Complex.normSq ψ)

/-- Exact positive-time solution of `ψ' = -γ |ψ|² ψ`, continuously extended to all real
parameters by freezing it at time zero before `t = 0`. -/
noncomputable def irreversibleCubicFlow (γ t : ℝ) (ψ : ℂ) : ℂ :=
  ψ / (cubicDampingDenominator γ t ψ : ℂ)

/-- Nonnegative damping makes the safely extended cubic-flow radicand strictly positive. -/
lemma cubicDampingRadicand_pos (γ t : ℝ) (hγ : 0 ≤ γ) (ψ : ℂ) :
    0 < 1 + 2 * γ * max t 0 * Complex.normSq ψ := by
  have ht : 0 ≤ max t 0 := le_max_right _ _
  have hq := Complex.normSq_nonneg ψ
  have hp : 0 ≤ 2 * γ * max t 0 * Complex.normSq ψ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) ht) hq
  linarith

/-- The cubic-flow denominator is nonzero in the irreversible regime. -/
lemma cubicDampingDenominator_pos (γ t : ℝ) (hγ : 0 ≤ γ) (ψ : ℂ) :
    0 < cubicDampingDenominator γ t ψ :=
  Real.sqrt_pos.2 (cubicDampingRadicand_pos γ t hγ ψ)

/-- On positive time the safe extension is the exact algebraic cubic solution. -/
lemma irreversibleCubicFlow_eq_raw (γ t : ℝ) (ht : 0 ≤ t) (ψ : ℂ) :
    irreversibleCubicFlow γ t ψ = rawIrreversibleCubicFlow γ t ψ := by
  simp [irreversibleCubicFlow, rawIrreversibleCubicFlow,
    cubicDampingDenominator, max_eq_left ht]

@[simp] lemma irreversibleCubicFlow_zero (γ : ℝ) (ψ : ℂ) :
    irreversibleCubicFlow γ 0 ψ = ψ := by
  simp [irreversibleCubicFlow, cubicDampingDenominator]

/-- Exact Born-norm decay law along the irreversible cubic flow. -/
lemma irreversibleCubicFlow_normSq (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    Complex.normSq (irreversibleCubicFlow γ t ψ) =
      Complex.normSq ψ / (1 + 2 * γ * t * Complex.normSq ψ) := by
  rw [irreversibleCubicFlow_eq_raw γ t ht, rawIrreversibleCubicFlow,
    Complex.normSq_div, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt]
  have hq := Complex.normSq_nonneg ψ
  have hp : 0 ≤ 2 * γ * t * Complex.normSq ψ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) ht) hq
  linarith

/-- The exact irreversible cubic flow cannot increase pointwise Born norm. -/
lemma irreversibleCubicFlow_normSq_le (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ψ : ℂ) :
    Complex.normSq (irreversibleCubicFlow γ t ψ) ≤ Complex.normSq ψ := by
  rw [irreversibleCubicFlow_normSq γ t hγ ht]
  have hq := Complex.normSq_nonneg ψ
  have hden : 1 ≤ 1 + 2 * γ * t * Complex.normSq ψ := by
    have hp : 0 ≤ 2 * γ * t * Complex.normSq ψ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) ht) hq
    linarith
  exact div_le_self hq hden

/-- The damping denominators multiply under successive nonnegative time increments.  This
is the algebraic identity behind the nonlinear flow law. -/
lemma cubicDampingDenominator_mul
    (γ s t : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ψ : ℂ) :
    cubicDampingDenominator γ s (irreversibleCubicFlow γ t ψ) *
        cubicDampingDenominator γ t ψ =
      cubicDampingDenominator γ (s + t) ψ := by
  have hst : 0 ≤ s + t := add_nonneg hs ht
  have hd₁ := cubicDampingDenominator_pos γ s hγ
    (irreversibleCubicFlow γ t ψ)
  have hd₂ := cubicDampingDenominator_pos γ t hγ ψ
  have hd₃ := cubicDampingDenominator_pos γ (s + t) hγ ψ
  have hsquares :
      (cubicDampingDenominator γ s (irreversibleCubicFlow γ t ψ) *
          cubicDampingDenominator γ t ψ) ^ 2 =
        cubicDampingDenominator γ (s + t) ψ ^ 2 := by
    rw [mul_pow]
    simp only [cubicDampingDenominator, max_eq_left hs, max_eq_left ht,
      max_eq_left hst]
    have hr₁ : 0 ≤ 1 + 2 * γ * s *
        Complex.normSq (irreversibleCubicFlow γ t ψ) := by
      simpa [max_eq_left hs] using
        (cubicDampingRadicand_pos γ s hγ
          (irreversibleCubicFlow γ t ψ)).le
    have hr₂ : 0 ≤ 1 + 2 * γ * t * Complex.normSq ψ := by
      simpa [max_eq_left ht] using
        (cubicDampingRadicand_pos γ t hγ ψ).le
    have hr₃ : 0 ≤ 1 + 2 * γ * (s + t) * Complex.normSq ψ := by
      simpa [max_eq_left hst] using
        (cubicDampingRadicand_pos γ (s + t) hγ ψ).le
    have hden : 0 < 1 + 2 * γ * t * Complex.normSq ψ := by
      have hq := Complex.normSq_nonneg ψ
      have hp : 0 ≤ 2 * γ * t * Complex.normSq ψ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) ht) hq
      linarith
    have hnormmul :
        Complex.normSq (irreversibleCubicFlow γ t ψ) *
            (1 + 2 * γ * t * Complex.normSq ψ) =
          Complex.normSq ψ := by
      rw [irreversibleCubicFlow_normSq γ t hγ ht]
      exact div_mul_cancel₀ _ hden.ne'
    rw [Real.sq_sqrt hr₁, Real.sq_sqrt hr₂, Real.sq_sqrt hr₃]
    calc
      _ = (1 + 2 * γ * t * Complex.normSq ψ) +
          2 * γ * s *
            (Complex.normSq (irreversibleCubicFlow γ t ψ) *
              (1 + 2 * γ * t * Complex.normSq ψ)) := by ring
      _ = (1 + 2 * γ * t * Complex.normSq ψ) +
          2 * γ * s * Complex.normSq ψ := by rw [hnormmul]
      _ = _ := by ring
  have hsquares' :
      (cubicDampingDenominator γ s (irreversibleCubicFlow γ t ψ) *
          cubicDampingDenominator γ t ψ) *
        (cubicDampingDenominator γ s (irreversibleCubicFlow γ t ψ) *
          cubicDampingDenominator γ t ψ) =
      cubicDampingDenominator γ (s + t) ψ *
        cubicDampingDenominator γ (s + t) ψ := by
    simpa [pow_two] using hsquares
  nlinarith [mul_pos hd₁ hd₂]

/-- **Exact nonlinear positive-time flow law.**  Successive irreversible cubic evolution
for times `t` and `s` agrees with one evolution for elapsed time `s + t`. -/
lemma irreversibleCubicFlow_add
    (γ s t : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ψ : ℂ) :
    irreversibleCubicFlow γ (s + t) ψ =
      irreversibleCubicFlow γ s (irreversibleCubicFlow γ t ψ) := by
  have hdenC :
      (cubicDampingDenominator γ s (irreversibleCubicFlow γ t ψ) : ℂ) *
          cubicDampingDenominator γ t ψ =
        cubicDampingDenominator γ (s + t) ψ := by
    exact_mod_cast cubicDampingDenominator_mul γ s t hγ hs ht ψ
  rw [irreversibleCubicFlow, irreversibleCubicFlow, irreversibleCubicFlow]
  rw [div_div]
  rw [show (cubicDampingDenominator γ t ψ : ℂ) *
      cubicDampingDenominator γ s
        (ψ / (cubicDampingDenominator γ t ψ : ℂ)) =
      cubicDampingDenominator γ (s + t) ψ by
    rw [mul_comm]
    simpa [irreversibleCubicFlow] using hdenC]

/-- The algebraic formula differentiates to the unique irreversible cubic vector field. -/
lemma rawIrreversibleCubicFlow_hasDerivAt
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    HasDerivAt (fun s : ℝ => rawIrreversibleCubicFlow γ s ψ)
      (irreversibleGravBackreaction γ (rawIrreversibleCubicFlow γ t ψ)) t := by
  let q := Complex.normSq ψ
  let r : ℝ → ℝ := fun s => 1 + 2 * γ * s * q
  have hlin := (hasDerivAt_id t).const_mul (2 * γ * q) |>.const_add 1
  have hr : HasDerivAt r (2 * γ * q) t := by
    have hfun : r = fun s => 1 + (2 * γ * q) * s := by
      funext s
      dsimp [r]
      ring
    refine (hlin.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv ?_
    ring
  have hrt : 0 < r t := by
    dsimp [r, q]
    have hq := Complex.normSq_nonneg ψ
    have hp : 0 ≤ 2 * γ * t * Complex.normSq ψ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hγ) ht) hq
    linarith
  have hs := hr.sqrt hrt.ne'
  have hsi := hs.inv (Real.sqrt_pos.2 hrt).ne'
  have hc := hsi.ofReal_comp.mul_const ψ
  have hfun :
      (fun s : ℝ => rawIrreversibleCubicFlow γ s ψ) =
        fun s => (((Real.sqrt (r s))⁻¹ : ℝ) : ℂ) * ψ := by
    funext s
    simp only [rawIrreversibleCubicFlow, div_eq_mul_inv]
    dsimp [r, q]
    push_cast
    ring
  have hc' :
      HasDerivAt (fun s : ℝ => rawIrreversibleCubicFlow γ s ψ)
        ((((-(2 * γ * q / (2 * Real.sqrt (r t)))) /
          Real.sqrt (r t) ^ 2 : ℝ) : ℂ) * ψ) t := by
    exact hc.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfun s)
  refine hc'.congr_deriv ?_
  rw [irreversibleGravBackreaction, gravBackreaction,
    rawIrreversibleCubicFlow]
  have hsqrt : Real.sqrt (r t) ^ 2 = r t := Real.sq_sqrt hrt.le
  have hsqrt0 : Real.sqrt (r t) ≠ 0 := (Real.sqrt_pos.2 hrt).ne'
  change
    (((-(2 * γ * q / (2 * Real.sqrt (r t)))) /
        Real.sqrt (r t) ^ 2 : ℝ) : ℂ) * ψ =
      ((-γ : ℝ) : ℂ) *
        (Complex.normSq
          (ψ / (Real.sqrt (1 + 2 * γ * t * Complex.normSq ψ) : ℂ)) : ℂ) *
        (ψ / (Real.sqrt (1 + 2 * γ * t * Complex.normSq ψ) : ℂ))
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  change
    (((-(2 * γ * q / (2 * Real.sqrt (r t)))) /
        Real.sqrt (r t) ^ 2 : ℝ) : ℂ) * ψ =
      ((-γ : ℝ) : ℂ) *
        ((Complex.normSq ψ /
          (Real.sqrt (r t) * Real.sqrt (r t)) : ℝ) : ℂ) *
        (ψ / (Real.sqrt (r t) : ℂ))
  rw [show Real.sqrt (r t) * Real.sqrt (r t) = r t by
    simpa [pow_two] using hsqrt]
  push_cast
  field_simp [hsqrt0, ne_of_gt hrt]
  have hsqrtC : ((Real.sqrt (r t) : ℝ) : ℂ) ^ 2 = (r t : ℂ) := by
    exact_mod_cast hsqrt
  rw [hsqrtC]
  dsimp [q]
  ring

/-- The safely extended flow solves the cubic ODE on the closed positive-time half-line,
including the right derivative at the initial time. -/
lemma irreversibleCubicFlow_hasDerivWithinAt
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    HasDerivWithinAt (fun s : ℝ => irreversibleCubicFlow γ s ψ)
      (irreversibleGravBackreaction γ (irreversibleCubicFlow γ t ψ))
      (Set.Ici 0) t := by
  have h : HasDerivWithinAt (fun s : ℝ => rawIrreversibleCubicFlow γ s ψ)
      (irreversibleGravBackreaction γ (rawIrreversibleCubicFlow γ t ψ))
      (Set.Ici 0) t :=
    (rawIrreversibleCubicFlow_hasDerivAt γ t hγ ht ψ).hasDerivWithinAt
  rw [irreversibleCubicFlow_eq_raw γ t ht]
  apply h.congr
  · intro s hs
    exact irreversibleCubicFlow_eq_raw γ s hs ψ
  · exact irreversibleCubicFlow_eq_raw γ t ht ψ

/-- Pointwise exact irreversible flow on a compact continuum configuration carrier. -/
noncomputable def continuumIrreversibleCubicFlow {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ψ : C(X, ℂ)) : C(X, ℂ) :=
  ⟨fun x => irreversibleCubicFlow γ t (ψ x), by
    apply Continuous.div₀
    · exact ψ.continuous
    · unfold cubicDampingDenominator
      fun_prop
    · intro x
      exact_mod_cast (cubicDampingDenominator_pos γ t hγ (ψ x)).ne'⟩

@[simp] lemma continuumIrreversibleCubicFlow_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ψ : C(X, ℂ)) (x : X) :
    continuumIrreversibleCubicFlow γ hγ t ψ x =
      irreversibleCubicFlow γ t (ψ x) := rfl

@[simp] lemma continuumIrreversibleCubicFlow_zero {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (ψ : C(X, ℂ)) :
    continuumIrreversibleCubicFlow γ hγ 0 ψ = ψ := by
  ext x
  simp

/-- The pointwise nonlinear flow law lifts without truncation to the compact continuum
configuration carrier. -/
lemma continuumIrreversibleCubicFlow_add {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) :
    continuumIrreversibleCubicFlow γ hγ (s + t) ψ =
      continuumIrreversibleCubicFlow γ hγ s
        (continuumIrreversibleCubicFlow γ hγ t ψ) := by
  ext x
  exact irreversibleCubicFlow_add γ s t hγ hs ht (ψ x)

/-- The continuum flow solves the pointwise cubic ODE at every carrier point. -/
lemma continuumIrreversibleCubicFlow_hasDerivWithinAt_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t) (ψ : C(X, ℂ)) (x : X) :
    HasDerivWithinAt (fun s : ℝ => continuumIrreversibleCubicFlow γ hγ s ψ x)
      (irreversibleGravBackreaction γ
        (continuumIrreversibleCubicFlow γ hγ t ψ x)) (Set.Ici 0) t :=
  irreversibleCubicFlow_hasDerivWithinAt γ t hγ ht (ψ x)

/-- The continuum flow has a pointwise no-blowup bound for all positive times. -/
lemma continuumIrreversibleCubicFlow_normSq_le {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t) (ψ : C(X, ℂ)) (x : X) :
    Complex.normSq (continuumIrreversibleCubicFlow γ hγ t ψ x) ≤
      Complex.normSq (ψ x) :=
  irreversibleCubicFlow_normSq_le γ t hγ ht (ψ x)

/-- **Continuum Banach-carrier contraction.**  The global nonlinear flow is contractive in
the supremum norm on `C(X, ℂ)`, strengthening the pointwise Born-norm estimate to the
infinite-dimensional Banach carrier. -/
lemma continuumIrreversibleCubicFlow_norm_le {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t) (ψ : C(X, ℂ)) :
    ‖continuumIrreversibleCubicFlow γ hγ t ψ‖ ≤ ‖ψ‖ := by
  apply (ContinuousMap.norm_le
    (f := continuumIrreversibleCubicFlow γ hγ t ψ)
    (C := ‖ψ‖) (norm_nonneg ψ)).2
  intro x
  have hsq := continuumIrreversibleCubicFlow_normSq_le γ hγ t ht ψ x
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (continuumIrreversibleCubicFlow γ hγ t ψ x),
    norm_nonneg (ψ x), ContinuousMap.norm_coe_le_norm ψ x]

/-- **Global positive-time nonlinear continuum solution.**  The unique irreversible
gauge-covariant cubic sector has an explicit solution at every positive time on an infinite
compact configuration carrier, with the exact ODE and a pointwise Born-norm no-blowup bound. -/
lemma exists_global_continuumIrreversibleCubic_solution {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Infinite X]
    (γ : ℝ) (hγ : 0 ≤ γ) (ψ₀ : C(X, ℂ)) :
    ∃ ψ : ℝ → C(X, ℂ), ψ 0 = ψ₀ ∧
      (∀ t, 0 ≤ t → ∀ x,
        HasDerivWithinAt (fun s => ψ s x)
          (irreversibleGravBackreaction γ (ψ t x)) (Set.Ici 0) t) ∧
      (∀ t, 0 ≤ t → ∀ x,
        Complex.normSq (ψ t x) ≤ Complex.normSq (ψ₀ x)) := by
  refine ⟨fun t => continuumIrreversibleCubicFlow γ hγ t ψ₀, ?_, ?_, ?_⟩
  · exact continuumIrreversibleCubicFlow_zero γ hγ ψ₀
  · intro t ht x
    exact continuumIrreversibleCubicFlow_hasDerivWithinAt_apply γ hγ t ht ψ₀ x
  · intro t ht x
    exact continuumIrreversibleCubicFlow_normSq_le γ hγ t ht ψ₀ x

/-! ## G. Hamiltonian phase coupled to the global irreversible flow -/

/-- The spatially homogeneous Hamiltonian phase generated by real energy `E`. -/
noncomputable def hamiltonianPhase (E t : ℝ) : ℂ :=
  Complex.exp (((-(E * t) : ℝ) : ℂ) * Complex.I)

/-- The combined complex generator: Hamiltonian phase rotation plus the unique
gauge-covariant irreversible cubic backreaction. -/
noncomputable def irreversibleComplexCubicGenerator (E γ : ℝ) (ψ : ℂ) : ℂ :=
  (-Complex.I * (E : ℂ)) * ψ + irreversibleGravBackreaction γ ψ

/-- Exact global positive-time flow of the homogeneous complex CAT/EPT generator. -/
noncomputable def irreversibleComplexCubicFlow (E γ t : ℝ) (ψ : ℂ) : ℂ :=
  hamiltonianPhase E t * irreversibleCubicFlow γ t ψ

@[simp] lemma hamiltonianPhase_zero (E : ℝ) : hamiltonianPhase E 0 = 1 := by
  simp [hamiltonianPhase]

/-- Hamiltonian phases compose under addition of elapsed times. -/
lemma hamiltonianPhase_add (E s t : ℝ) :
    hamiltonianPhase E (s + t) =
      hamiltonianPhase E s * hamiltonianPhase E t := by
  rw [hamiltonianPhase, hamiltonianPhase, hamiltonianPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Hamiltonian phase has unit Born norm. -/
lemma hamiltonianPhase_normSq (E t : ℝ) :
    Complex.normSq (hamiltonianPhase E t) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [hamiltonianPhase, Complex.norm_exp]

/-- The phase factor solves the real-time homogeneous Schrödinger equation. -/
lemma hamiltonianPhase_hasDerivAt (E t : ℝ) :
    HasDerivAt (hamiltonianPhase E)
      ((-Complex.I * (E : ℂ)) * hamiltonianPhase E t) t := by
  have hreal : HasDerivAt (fun s : ℝ => -(E * s)) (-E) t := by
    simpa only [id_eq, mul_one, neg_mul] using
      (hasDerivAt_id t).const_mul (-E)
  have harg :
      HasDerivAt (fun s : ℝ => (((-(E * s) : ℝ) : ℂ) * Complex.I))
        (((-E : ℝ) : ℂ) * Complex.I) t :=
    hreal.ofReal_comp.mul_const Complex.I
  have hexp := harg.cexp
  change HasDerivAt
    (fun s : ℝ => Complex.exp (((-(E * s) : ℝ) : ℂ) * Complex.I))
    ((-Complex.I * (E : ℂ)) *
      Complex.exp (((-(E * t) : ℝ) : ℂ) * Complex.I)) t
  apply hexp.congr_deriv
  push_cast
  ring

/-- Multiplication by a unit-Born-norm phase commutes with the irreversible cubic
backreaction. -/
lemma irreversibleGravBackreaction_phase_covariant
    (γ : ℝ) (c ψ : ℂ) (hc : Complex.normSq c = 1) :
    irreversibleGravBackreaction γ (c * ψ) =
      c * irreversibleGravBackreaction γ ψ := by
  change gravBackreaction (-γ) (c * ψ) =
    c * gravBackreaction (-γ) ψ
  rw [(gravBackreaction_isGaugeCovariantCubic (-γ)) c ψ, hc]
  simp

/-- The exact cubic flow commutes with multiplication by a unit-Born-norm phase. -/
lemma irreversibleCubicFlow_phase_mul
    (γ t : ℝ) (c ψ : ℂ) (hc : Complex.normSq c = 1) :
    irreversibleCubicFlow γ t (c * ψ) =
      c * irreversibleCubicFlow γ t ψ := by
  simp only [irreversibleCubicFlow, cubicDampingDenominator, map_mul, hc, one_mul]
  field_simp

@[simp] lemma irreversibleComplexCubicFlow_zero (E γ : ℝ) (ψ : ℂ) :
    irreversibleComplexCubicFlow E γ 0 ψ = ψ := by
  simp [irreversibleComplexCubicFlow]

/-- Adding the Hamiltonian phase leaves the exact irreversible Born-norm decay law
unchanged. -/
lemma irreversibleComplexCubicFlow_normSq
    (E γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    Complex.normSq (irreversibleComplexCubicFlow E γ t ψ) =
      Complex.normSq ψ / (1 + 2 * γ * t * Complex.normSq ψ) := by
  rw [irreversibleComplexCubicFlow, map_mul, hamiltonianPhase_normSq,
    irreversibleCubicFlow_normSq γ t hγ ht]
  simp

/-- The full complex cubic flow cannot increase Born norm. -/
lemma irreversibleComplexCubicFlow_normSq_le
    (E γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    Complex.normSq (irreversibleComplexCubicFlow E γ t ψ) ≤
      Complex.normSq ψ := by
  calc
    Complex.normSq (irreversibleComplexCubicFlow E γ t ψ) =
        Complex.normSq (irreversibleCubicFlow γ t ψ) := by
      rw [irreversibleComplexCubicFlow_normSq E γ t hγ ht,
        irreversibleCubicFlow_normSq γ t hγ ht]
    _ ≤ Complex.normSq ψ :=
      irreversibleCubicFlow_normSq_le γ t hγ ht ψ

/-- **Exact global nonlinear complex evolution.**  On positive time, the explicit
phase-damped flow differentiates to the sum of its Schrödinger generator and the unique
irreversible cubic backreaction. -/
lemma irreversibleComplexCubicFlow_hasDerivWithinAt
    (E γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ψ : ℂ) :
    HasDerivWithinAt (fun s : ℝ => irreversibleComplexCubicFlow E γ s ψ)
      (irreversibleComplexCubicGenerator E γ
        (irreversibleComplexCubicFlow E γ t ψ))
      (Set.Ici 0) t := by
  have hp := (hamiltonianPhase_hasDerivAt E t).hasDerivWithinAt
    (s := Set.Ici 0)
  have hc := irreversibleCubicFlow_hasDerivWithinAt γ t hγ ht ψ
  have hmul := hp.mul hc
  apply hmul.congr_deriv
  rw [irreversibleComplexCubicGenerator, irreversibleComplexCubicFlow]
  rw [irreversibleGravBackreaction_phase_covariant γ
    (hamiltonianPhase E t) (irreversibleCubicFlow γ t ψ)
    (hamiltonianPhase_normSq E t)]
  ring

/-- **Full complex nonlinear flow law.**  Hamiltonian phase rotation and irreversible
cubic damping together form an exact positive-time nonlinear flow. -/
lemma irreversibleComplexCubicFlow_add
    (E γ s t : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ψ : ℂ) :
    irreversibleComplexCubicFlow E γ (s + t) ψ =
      irreversibleComplexCubicFlow E γ s
        (irreversibleComplexCubicFlow E γ t ψ) := by
  rw [irreversibleComplexCubicFlow, irreversibleComplexCubicFlow,
    irreversibleComplexCubicFlow]
  rw [hamiltonianPhase_add]
  rw [irreversibleCubicFlow_add γ s t hγ hs ht]
  rw [irreversibleCubicFlow_phase_mul γ s
    (hamiltonianPhase E t) (irreversibleCubicFlow γ t ψ)
    (hamiltonianPhase_normSq E t)]
  ring

/-- The exact complex nonlinear flow lifted pointwise to a compact continuum carrier. -/
noncomputable def continuumIrreversibleComplexCubicFlow {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ψ : C(X, ℂ)) : C(X, ℂ) :=
  ContinuousMap.const X (hamiltonianPhase E t) *
    continuumIrreversibleCubicFlow γ hγ t ψ

@[simp] lemma continuumIrreversibleComplexCubicFlow_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ψ : C(X, ℂ)) (x : X) :
    continuumIrreversibleComplexCubicFlow E γ hγ t ψ x =
      irreversibleComplexCubicFlow E γ t (ψ x) := rfl

@[simp] lemma continuumIrreversibleComplexCubicFlow_zero {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (ψ : C(X, ℂ)) :
    continuumIrreversibleComplexCubicFlow E γ hγ 0 ψ = ψ := by
  ext x
  simp

/-- The continuum complex flow solves the combined nonlinear ODE pointwise. -/
lemma continuumIrreversibleComplexCubicFlow_hasDerivWithinAt_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) (x : X) :
    HasDerivWithinAt
      (fun s : ℝ => continuumIrreversibleComplexCubicFlow E γ hγ s ψ x)
      (irreversibleComplexCubicGenerator E γ
        (continuumIrreversibleComplexCubicFlow E γ hγ t ψ x))
      (Set.Ici 0) t :=
  irreversibleComplexCubicFlow_hasDerivWithinAt E γ t hγ ht (ψ x)

/-- The Hamiltonian-plus-irreversible continuum flow is contractive in the Banach
supremum norm. -/
lemma continuumIrreversibleComplexCubicFlow_norm_le {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t) (ψ : C(X, ℂ)) :
    ‖continuumIrreversibleComplexCubicFlow E γ hγ t ψ‖ ≤ ‖ψ‖ := by
  apply (ContinuousMap.norm_le
    (f := continuumIrreversibleComplexCubicFlow E γ hγ t ψ)
    (C := ‖ψ‖) (norm_nonneg ψ)).2
  intro x
  have hsq := irreversibleComplexCubicFlow_normSq_le E γ t hγ ht (ψ x)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  have hpoint :
      ‖continuumIrreversibleComplexCubicFlow E γ hγ t ψ x‖ ≤ ‖ψ x‖ := by
    rw [continuumIrreversibleComplexCubicFlow_apply]
    nlinarith [norm_nonneg (irreversibleComplexCubicFlow E γ t (ψ x)),
      norm_nonneg (ψ x)]
  exact hpoint.trans (ContinuousMap.norm_coe_le_norm ψ x)

/-- **Global continuum Hamiltonian-plus-irreversible solution.**  The explicitly
constructed trajectory exists for every positive time, solves the full homogeneous complex
cubic equation pointwise, and cannot grow in the continuum Banach norm. -/
lemma exists_global_continuumIrreversibleComplexCubic_solution {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Infinite X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (ψ₀ : C(X, ℂ)) :
    ∃ ψ : ℝ → C(X, ℂ), ψ 0 = ψ₀ ∧
      (∀ t, 0 ≤ t → ∀ x,
        HasDerivWithinAt (fun s => ψ s x)
          (irreversibleComplexCubicGenerator E γ (ψ t x))
          (Set.Ici 0) t) ∧
      (∀ t, 0 ≤ t → ‖ψ t‖ ≤ ‖ψ₀‖) := by
  refine ⟨fun t => continuumIrreversibleComplexCubicFlow E γ hγ t ψ₀,
    ?_, ?_, ?_⟩
  · exact continuumIrreversibleComplexCubicFlow_zero E γ hγ ψ₀
  · intro t ht x
    exact continuumIrreversibleComplexCubicFlow_hasDerivWithinAt_apply
      E γ hγ t ht ψ₀ x
  · intro t ht
    exact continuumIrreversibleComplexCubicFlow_norm_le E γ hγ t ht ψ₀

/-! ## H. Spatially varying state-independent energy -/

/-- Pointwise Hamiltonian phase generated by a continuous real energy field. -/
noncomputable def continuumHamiltonianPhase {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (t : ℝ) : C(X, ℂ) :=
  ⟨fun x => hamiltonianPhase (E x) t, by
    unfold hamiltonianPhase
    fun_prop⟩

@[simp] lemma continuumHamiltonianPhase_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (t : ℝ) (x : X) :
    continuumHamiltonianPhase E t x = hamiltonianPhase (E x) t := rfl

/-- Exact nonlinear flow with a fixed spatially varying multiplication-energy field. -/
noncomputable def continuumSpatialEnergyCubicFlow {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ)
    (ψ : C(X, ℂ)) : C(X, ℂ) :=
  continuumHamiltonianPhase E t *
    continuumIrreversibleCubicFlow γ hγ t ψ

@[simp] lemma continuumSpatialEnergyCubicFlow_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ)
    (ψ : C(X, ℂ)) (x : X) :
    continuumSpatialEnergyCubicFlow E γ hγ t ψ x =
      irreversibleComplexCubicFlow (E x) γ t (ψ x) := rfl

@[simp] lemma continuumSpatialEnergyCubicFlow_zero {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicFlow E γ hγ 0 ψ = ψ := by
  ext x
  simp [continuumSpatialEnergyCubicFlow, continuumHamiltonianPhase]

/-- The spatial-energy construction contains the homogeneous-energy flow as its constant
field specialization. -/
lemma continuumSpatialEnergyCubicFlow_const {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicFlow (ContinuousMap.const X E) γ hγ t ψ =
      continuumIrreversibleComplexCubicFlow E γ hγ t ψ := by
  rfl

/-- The full nonlinear positive-time flow law holds for every fixed continuous energy
field. -/
lemma continuumSpatialEnergyCubicFlow_add {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicFlow E γ hγ (s + t) ψ =
      continuumSpatialEnergyCubicFlow E γ hγ s
        (continuumSpatialEnergyCubicFlow E γ hγ t ψ) := by
  ext x
  exact irreversibleComplexCubicFlow_add (E x) γ s t hγ hs ht (ψ x)

/-- The spatial-energy continuum flow solves the combined complex nonlinear ODE at every
configuration point. -/
lemma continuumSpatialEnergyCubicFlow_hasDerivWithinAt_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) (x : X) :
    HasDerivWithinAt
      (fun s : ℝ => continuumSpatialEnergyCubicFlow E γ hγ s ψ x)
      (irreversibleComplexCubicGenerator (E x) γ
        (continuumSpatialEnergyCubicFlow E γ hγ t ψ x))
      (Set.Ici 0) t :=
  irreversibleComplexCubicFlow_hasDerivWithinAt (E x) γ t hγ ht (ψ x)

/-- **Spatial-energy continuum contraction.**  A fixed continuous real multiplication
energy changes only phase, so the exact nonlinear flow remains contractive in the continuum
supremum norm. -/
lemma continuumSpatialEnergyCubicFlow_norm_le {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ‖ ≤ ‖ψ‖ := by
  apply (ContinuousMap.norm_le
    (f := continuumSpatialEnergyCubicFlow E γ hγ t ψ)
    (C := ‖ψ‖) (norm_nonneg ψ)).2
  intro x
  have hsq :=
    irreversibleComplexCubicFlow_normSq_le (E x) γ t hγ ht (ψ x)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  have hpoint :
      ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ x‖ ≤ ‖ψ x‖ := by
    rw [continuumSpatialEnergyCubicFlow_apply]
    nlinarith [norm_nonneg
      (irreversibleComplexCubicFlow (E x) γ t (ψ x)),
      norm_nonneg (ψ x)]
  exact hpoint.trans (ContinuousMap.norm_coe_le_norm ψ x)

/-- The complex multiplication coefficient `-i E(x)` for a continuous real energy field. -/
noncomputable def schrodingerEnergyCoefficient {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (E : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => -Complex.I * (E x : ℂ), by fun_prop⟩

/-- The new spatial-energy generator is exactly the pre-existing continuum gravitational
generator with coefficient `-i E(x)` and irreversible coupling `-γ`. -/
lemma continuumGravGenerator_schrodinger_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (ψ : C(X, ℂ)) (x : X) :
    continuumGravGenerator (schrodingerEnergyCoefficient E) (-γ) ψ x =
      irreversibleComplexCubicGenerator (E x) γ (ψ x) := by
  rw [continuumGravGenerator_apply]
  simp [schrodingerEnergyCoefficient, irreversibleComplexCubicGenerator,
    irreversibleGravBackreaction, gravBackreaction]

/-- **Explicit global instance of the existing continuum generator.**  For every fixed
continuous real multiplication-energy field and nonnegative irreversible coupling, the
existing `continuumGravGenerator` has an explicit solution at every positive time, satisfies
its pointwise ODE, obeys the nonlinear flow law, and contracts the Banach norm.  The
conclusion is pointwise in the ODE; it does not assert a Banach-strong derivative for a
state-dependent Hamiltonian. -/
lemma exists_global_continuumGravGenerator_stateIndependent_solution {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [Infinite X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (ψ₀ : C(X, ℂ)) :
    ∃ ψ : ℝ → C(X, ℂ), ψ 0 = ψ₀ ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → ψ (s + t) =
        continuumSpatialEnergyCubicFlow E γ hγ s (ψ t)) ∧
      (∀ t, 0 ≤ t → ∀ x,
        HasDerivWithinAt (fun s => ψ s x)
          (continuumGravGenerator (schrodingerEnergyCoefficient E)
            (-γ) (ψ t) x) (Set.Ici 0) t) ∧
      (∀ t, 0 ≤ t → ‖ψ t‖ ≤ ‖ψ₀‖) := by
  refine ⟨fun t => continuumSpatialEnergyCubicFlow E γ hγ t ψ₀,
    ?_, ?_, ?_, ?_⟩
  · exact continuumSpatialEnergyCubicFlow_zero E γ hγ ψ₀
  · intro s t hs ht
    exact continuumSpatialEnergyCubicFlow_add E γ hγ s t hs ht ψ₀
  · intro t ht x
    rw [continuumGravGenerator_schrodinger_apply]
    exact continuumSpatialEnergyCubicFlow_hasDerivWithinAt_apply
      E γ hγ t ht ψ₀ x
  · intro t ht
    exact continuumSpatialEnergyCubicFlow_norm_le E γ hγ t ht ψ₀

/-! ## I. Nonlinear C₀-semiflow and asymptotic stability -/

/-- Every orbit of the fixed spatial-energy flow is strongly continuous in the continuum
supremum-norm topology. -/
lemma continuumSpatialEnergyCubicFlow_continuous {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) (ψ : C(X, ℂ)) :
    Continuous (fun t : ℝ => continuumSpatialEnergyCubicFlow E γ hγ t ψ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × X =>
    hamiltonianPhase (E p.2) p.1 *
      irreversibleCubicFlow γ p.1 (ψ p.2))
  apply Continuous.mul
  · unfold hamiltonianPhase
    fun_prop
  · unfold irreversibleCubicFlow cubicDampingDenominator
    apply Continuous.div₀
    · exact ψ.continuous.comp continuous_snd
    · apply Complex.continuous_ofReal.comp
      apply Real.continuous_sqrt.comp
      fun_prop
    · intro p
      exact_mod_cast
        (cubicDampingDenominator_pos γ p.1 hγ (ψ p.2)).ne'

/-- **Joint C₀ continuity.**  Evolution depends continuously on both nonnegative time and
the initial field in the continuum supremum-norm topology. -/
lemma continuumSpatialEnergyCubicFlow_joint_continuous {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) :
    Continuous (Function.uncurry fun t : AddSubmonoid.nonneg ℝ =>
      continuumSpatialEnergyCubicFlow E γ hγ t.1) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (AddSubmonoid.nonneg ℝ × C(X, ℂ)) × X =>
    hamiltonianPhase (E p.2) p.1.1.1 *
      irreversibleCubicFlow γ p.1.1.1 (p.1.2 p.2))
  apply Continuous.mul
  · unfold hamiltonianPhase
    fun_prop
  · unfold irreversibleCubicFlow cubicDampingDenominator
    apply Continuous.div₀
    · fun_prop
    · apply Complex.continuous_ofReal.comp
      apply Real.continuous_sqrt.comp
      fun_prop
    · intro p
      exact_mod_cast
        (cubicDampingDenominator_pos γ p.1.1.1 hγ (p.1.2 p.2)).ne'

/-- The fixed continuous spatial-energy CAT/EPT evolution packaged as Mathlib's canonical
jointly continuous nonnegative-time `Flow`.  The carrier is the full Banach space
`C(X, ℂ)`, not a finite-mode truncation. -/
noncomputable def continuumSpatialEnergyCubicSemiflow {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ) :
    Flow (AddSubmonoid.nonneg ℝ) C(X, ℂ) where
  toFun t ψ := continuumSpatialEnergyCubicFlow E γ hγ t.1 ψ
  cont' := continuumSpatialEnergyCubicFlow_joint_continuous E γ hγ
  map_add' s t ψ :=
    continuumSpatialEnergyCubicFlow_add E γ hγ s.1 t.1 s.2 t.2 ψ
  map_zero' ψ := continuumSpatialEnergyCubicFlow_zero E γ hγ ψ

@[simp] lemma continuumSpatialEnergyCubicSemiflow_apply {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : AddSubmonoid.nonneg ℝ) (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicSemiflow E γ hγ t ψ =
      continuumSpatialEnergyCubicFlow E γ hγ t.1 ψ := rfl

/-- **Contractive nonlinear C₀-semiflow.**  Every nonnegative-time map of the packaged
continuum flow is norm-contracting. -/
lemma continuumSpatialEnergyCubicSemiflow_contracts {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : AddSubmonoid.nonneg ℝ) (ψ : C(X, ℂ)) :
    ‖continuumSpatialEnergyCubicSemiflow E γ hγ t ψ‖ ≤ ‖ψ‖ :=
  continuumSpatialEnergyCubicFlow_norm_le E γ hγ t.1 t.2 ψ

/-- Positive damping gives a state-independent inverse-time upper bound on the exact
pointwise Born norm. -/
lemma irreversibleComplexCubicFlow_normSq_le_inv_time
    (E γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (ψ : ℂ) :
    Complex.normSq (irreversibleComplexCubicFlow E γ t ψ) ≤
      1 / (2 * γ * t) := by
  rw [irreversibleComplexCubicFlow_normSq E γ t hγ.le ht.le]
  let q := Complex.normSq ψ
  let a := 2 * γ * t
  have hq : 0 ≤ q := Complex.normSq_nonneg ψ
  have ha : 0 < a := by
    dsimp [a]
    positivity
  change q / (1 + a * q) ≤ 1 / a
  by_cases hq0 : q = 0
  · rw [hq0]
    simp only [mul_zero, add_zero, zero_div]
    positivity
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    calc
      q / (1 + a * q) ≤ q / (a * q) := by
        exact div_le_div_of_nonneg_left hq (mul_pos ha hqpos)
          (by linarith)
      _ = 1 / a := by field_simp

/-- Uniform continuum decay bound, independent of the initial-state norm. -/
lemma continuumSpatialEnergyCubicFlow_norm_le_invTimeSqrt {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ) (t : ℝ) (ht : 0 < t)
    (ψ : C(X, ℂ)) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ.le t ψ‖ ≤
      Real.sqrt (1 / (2 * γ * t)) := by
  apply (ContinuousMap.norm_le
    (f := continuumSpatialEnergyCubicFlow E γ hγ.le t ψ)
    (C := Real.sqrt (1 / (2 * γ * t))) (Real.sqrt_nonneg _)).2
  intro x
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq,
    continuumSpatialEnergyCubicFlow_apply]
  exact irreversibleComplexCubicFlow_normSq_le_inv_time
    (E x) γ t hγ ht (ψ x)

/-- **Uniform asymptotic stability.**  For strictly positive irreversible coupling, every
continuum orbit converges to the zero field in supremum norm as positive time tends to
infinity. -/
lemma continuumSpatialEnergyCubicFlow_tendsto_zero {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ) (ψ : C(X, ℂ)) :
    Filter.Tendsto
      (fun t : ℝ => ‖continuumSpatialEnergyCubicFlow E γ hγ.le t ψ‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact continuumSpatialEnergyCubicFlow_norm_le_invTimeSqrt
      E γ hγ t ht ψ
  · have hinv :
        Filter.Tendsto (fun t : ℝ => 1 / (2 * γ * t))
          Filter.atTop (nhds 0) := by
      have hden : Filter.Tendsto (fun t : ℝ => (2 * γ) * t)
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (mul_pos zero_lt_two hγ)
          Filter.tendsto_id
      convert tendsto_inv_atTop_zero.comp hden using 1
      funext t
      simp only [Function.comp_apply, one_div]
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hinv using 1
    · funext t
      simp only [Function.comp_apply]
    · simp

/-! ## J. Strict contraction and the zero-field global attractor -/

/-- **Sharp initial-norm decay envelope.**  The continuum norm is bounded by the scalar
cubic-decay formula evaluated at the initial supremum norm.  This is sharper than both the
non-growth estimate and the state-independent inverse-time bound. -/
lemma continuumSpatialEnergyCubicFlow_norm_le_initial {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ‖ ≤
      ‖ψ‖ / Real.sqrt (1 + 2 * γ * t * ‖ψ‖ ^ 2) := by
  let M := ‖ψ‖
  let a := 2 * γ * t
  have hM : 0 ≤ M := norm_nonneg ψ
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hden : 0 < 1 + a * M ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (1 + a * M ^ 2) :=
    Real.sqrt_pos.2 hden
  have hC : 0 ≤ M / Real.sqrt (1 + a * M ^ 2) :=
    div_nonneg hM hsqrt.le
  apply (ContinuousMap.norm_le
    (f := continuumSpatialEnergyCubicFlow E γ hγ t ψ)
    (C := M / Real.sqrt (1 + a * M ^ 2)) hC).2
  intro x
  let q := Complex.normSq (ψ x)
  have hq : 0 ≤ q := Complex.normSq_nonneg (ψ x)
  have hpoint := ContinuousMap.norm_coe_le_norm ψ x
  have hqM : q ≤ M ^ 2 := by
    dsimp [q, M]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (ψ x), norm_nonneg ψ]
  have hdenq : 0 < 1 + a * q := by positivity
  have hfrac : q / (1 + a * q) ≤ M ^ 2 / (1 + a * M ^ 2) := by
    rw [div_le_div_iff₀ hdenq hden]
    nlinarith
  have hflow := irreversibleComplexCubicFlow_normSq
    (E x) γ t hγ ht (ψ x)
  change Complex.normSq
    (continuumSpatialEnergyCubicFlow E γ hγ t ψ x) =
      q / (1 + a * q) at hflow
  have hsqrt_sq : Real.sqrt (1 + a * M ^ 2) ^ 2 =
      1 + a * M ^ 2 := Real.sq_sqrt hden.le
  rw [Complex.normSq_eq_norm_sq] at hflow
  have hsq :
      ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ x‖ ^ 2 ≤
        (M / Real.sqrt (1 + a * M ^ 2)) ^ 2 := by
    rw [hflow]
    calc
      q / (1 + a * q) ≤ M ^ 2 / (1 + a * M ^ 2) := hfrac
      _ = (M / Real.sqrt (1 + a * M ^ 2)) ^ 2 := by
        field_simp [hsqrt.ne']
        rw [show Real.sqrt (1 + M ^ 2 * a) ^ 2 =
          1 + M ^ 2 * a by simpa [mul_comm] using hsqrt_sq]
  nlinarith [norm_nonneg
    (continuumSpatialEnergyCubicFlow E γ hγ t ψ x)]

/-- Positive damping makes every positive-time map strictly norm-contracting away from the
zero field. -/
lemma continuumSpatialEnergyCubicFlow_norm_lt {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t)
    (ψ : C(X, ℂ)) (hψ : ψ ≠ 0) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ.le t ψ‖ < ‖ψ‖ := by
  have hM : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hrad : 1 < 1 + 2 * γ * t * ‖ψ‖ ^ 2 := by
    have : 0 < 2 * γ * t * ‖ψ‖ ^ 2 := by positivity
    linarith
  have hsqrt : 1 < Real.sqrt (1 + 2 * γ * t * ‖ψ‖ ^ 2) := by
    apply (Real.lt_sqrt (by norm_num : 0 ≤ (1 : ℝ))).2
    simpa using hrad
  exact (continuumSpatialEnergyCubicFlow_norm_le_initial
    E γ t hγ.le ht.le ψ).trans_lt (div_lt_self hM hsqrt)

/-- **Unique positive-time fixed point.**  For positive damping and any strictly positive
time, the packaged nonlinear continuum semiflow fixes exactly the zero field. -/
lemma continuumSpatialEnergyCubicSemiflow_fixed_iff_zero {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ)
    (t : AddSubmonoid.nonneg ℝ) (ht : 0 < t.1) (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicSemiflow E γ hγ.le t ψ = ψ ↔
      ψ = 0 := by
  constructor
  · intro hfix
    by_contra hψ
    have hlt := continuumSpatialEnergyCubicFlow_norm_lt
      E γ t.1 hγ ht ψ hψ
    rw [← continuumSpatialEnergyCubicSemiflow_apply] at hlt
    rw [hfix] at hlt
    exact lt_irrefl _ hlt
  · rintro rfl
    change continuumSpatialEnergyCubicFlow E γ hγ.le t.1 0 = 0
    ext x
    rw [continuumSpatialEnergyCubicFlow_apply]
    simp [irreversibleComplexCubicFlow, irreversibleCubicFlow]

/-- Norm convergence upgrades to convergence of the continuum field itself. -/
lemma continuumSpatialEnergyCubicFlow_tendsto_zero_field {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ) (ψ : C(X, ℂ)) :
    Filter.Tendsto
      (fun t : ℝ => continuumSpatialEnergyCubicFlow E γ hγ.le t ψ)
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact continuumSpatialEnergyCubicFlow_tendsto_zero E γ hγ ψ

/-- **Singleton zero global attractor.**  In the exact fixed-spatial-energy sector with
positive damping, zero is invariant, is the unique fixed field for every positive-time map,
and attracts every initial continuum field in supremum norm. -/
lemma continuumSpatialEnergyCubicSemiflow_zero_globalAttractor {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ) :
    (∀ t : AddSubmonoid.nonneg ℝ,
        continuumSpatialEnergyCubicSemiflow E γ hγ.le t 0 = 0) ∧
      (∀ (t : AddSubmonoid.nonneg ℝ), 0 < t.1 → ∀ ψ,
        continuumSpatialEnergyCubicSemiflow E γ hγ.le t ψ = ψ ↔
          ψ = 0) ∧
      (∀ ψ : C(X, ℂ), Filter.Tendsto
        (fun t : ℝ => continuumSpatialEnergyCubicFlow E γ hγ.le t ψ)
        Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    change continuumSpatialEnergyCubicFlow E γ hγ.le t.1 0 = 0
    ext x
    rw [continuumSpatialEnergyCubicFlow_apply]
    simp [irreversibleComplexCubicFlow, irreversibleCubicFlow]
  · intro t ht ψ
    exact continuumSpatialEnergyCubicSemiflow_fixed_iff_zero
      E γ hγ t ht ψ
  · intro ψ
    exact continuumSpatialEnergyCubicFlow_tendsto_zero_field E γ hγ ψ

/-! ## K. Exact decay, persistence, and uniform absorption -/

/-- **Exact continuum norm law.**  Compactness makes the initial supremum norm attain its
maximum, so the scalar cubic-decay identity upgrades the preceding upper envelope to an
equality on the full continuum carrier. -/
lemma continuumSpatialEnergyCubicFlow_norm_eq_initial {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ‖ =
      ‖ψ‖ / Real.sqrt (1 + 2 * γ * t * ‖ψ‖ ^ 2) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      simp [ContinuousMap.norm_eq_iSup_norm]
  | inr hX =>
      letI := hX
      obtain ⟨x₀, -, hx₀⟩ :=
        isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
          ψ.continuous.norm.continuousOn
      have hψnorm : ‖ψ‖ = ‖ψ x₀‖ := by
        apply le_antisymm
        · apply (ContinuousMap.norm_le (f := ψ) (C := ‖ψ x₀‖)
            (norm_nonneg _)).2
          intro x
          exact hx₀ (Set.mem_univ x)
        · exact ContinuousMap.norm_coe_le_norm ψ x₀
      apply le_antisymm
      · exact continuumSpatialEnergyCubicFlow_norm_le_initial
          E γ t hγ ht ψ
      · have hpoint :
            ‖continuumSpatialEnergyCubicFlow E γ hγ t ψ x₀‖ =
              ‖ψ x₀‖ /
                Real.sqrt (1 + 2 * γ * t * ‖ψ x₀‖ ^ 2) := by
          have hsq := irreversibleComplexCubicFlow_normSq
            (E x₀) γ t hγ ht (ψ x₀)
          rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
          rw [continuumSpatialEnergyCubicFlow_apply]
          have hden : 0 < 1 + 2 * γ * t * ‖ψ x₀‖ ^ 2 := by positivity
          have hsqrt : 0 < Real.sqrt
              (1 + 2 * γ * t * ‖ψ x₀‖ ^ 2) :=
            Real.sqrt_pos.2 hden
          have hsqrt_sq :
              Real.sqrt (1 + 2 * γ * t * ‖ψ x₀‖ ^ 2) ^ 2 =
                1 + 2 * γ * t * ‖ψ x₀‖ ^ 2 :=
            Real.sq_sqrt hden.le
          have heq :
              ‖irreversibleComplexCubicFlow (E x₀) γ t (ψ x₀)‖ ^ 2 =
                (‖ψ x₀‖ /
                  Real.sqrt (1 + 2 * γ * t * ‖ψ x₀‖ ^ 2)) ^ 2 := by
            rw [hsq]
            rw [div_pow, hsqrt_sq]
          nlinarith [norm_nonneg
            (irreversibleComplexCubicFlow (E x₀) γ t (ψ x₀)),
            norm_nonneg (ψ x₀),
            div_nonneg (norm_nonneg (ψ x₀)) hsqrt.le]
        rw [hψnorm]
        exact hpoint ▸
          ContinuousMap.norm_coe_le_norm
            (continuumSpatialEnergyCubicFlow E γ hγ t ψ) x₀

/-- A nonzero continuum field cannot reach zero at finite nonnegative time.  Thus the
zero-field attractor is approached asymptotically rather than by finite-time collapse. -/
lemma continuumSpatialEnergyCubicFlow_eq_zero_iff {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) :
    continuumSpatialEnergyCubicFlow E γ hγ t ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro hflow
    by_contra hψ
    have hM : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hden : 0 < Real.sqrt
        (1 + 2 * γ * t * ‖ψ‖ ^ 2) := by
      apply Real.sqrt_pos.2
      positivity
    have hnorm := congrArg norm hflow
    rw [norm_zero] at hnorm
    rw [continuumSpatialEnergyCubicFlow_norm_eq_initial
      E γ t hγ ht ψ] at hnorm
    exact (div_pos hM hden).ne' hnorm
  · rintro rfl
    ext x
    simp [continuumSpatialEnergyCubicFlow_apply,
      irreversibleComplexCubicFlow, irreversibleCubicFlow]

/-- Every nonzero orbit has a strictly decreasing norm between any two distinct
nonnegative times. -/
lemma continuumSpatialEnergyCubicFlow_norm_strictAnti {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t)
    (ψ : C(X, ℂ)) (hψ : ψ ≠ 0) :
    ‖continuumSpatialEnergyCubicFlow E γ hγ.le (s + t) ψ‖ <
      ‖continuumSpatialEnergyCubicFlow E γ hγ.le t ψ‖ := by
  rw [continuumSpatialEnergyCubicFlow_add E γ hγ.le s t hs.le ht ψ]
  apply continuumSpatialEnergyCubicFlow_norm_lt E γ s hγ hs
  exact (continuumSpatialEnergyCubicFlow_eq_zero_iff
    E γ t hγ.le ht ψ).not.mpr hψ

/-- **Uniform absorption.**  For every positive radius, one finite time sends every
initial continuum field—even without an initial norm bound—into that radius around zero.
The explicit absorbing time is `1 / (2 γ ε²)`. -/
lemma continuumSpatialEnergyCubicFlow_uniformly_absorbs {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (E : C(X, ℝ)) (γ : ℝ) (hγ : 0 < γ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T > 0, ∀ t ≥ T, ∀ ψ : C(X, ℂ),
      ‖continuumSpatialEnergyCubicFlow E γ hγ.le t ψ‖ ≤ ε := by
  refine ⟨1 / (2 * γ * ε ^ 2), by positivity, ?_⟩
  intro t ht ψ
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  refine (continuumSpatialEnergyCubicFlow_norm_le_invTimeSqrt
    E γ hγ t htpos ψ).trans ?_
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hε.le
  · have hden : 0 < 2 * γ * t := by positivity
    rw [div_le_iff₀ hden]
    have hpos : 0 < 2 * γ * ε ^ 2 := by positivity
    have hbase : 1 ≤ t * (2 * γ * ε ^ 2) :=
      (div_le_iff₀ hpos).mp (by simpa using ht)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hbase

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravGenerator_superposition_violation where
  formalizes @ "claim:coupling-the-entropic-dynamics-quantum-field-to-dynamical-gravity-makes-the-generator-l-of-psi-equals-e-psi-plus-lambda-psi-modulus-squared-psi-nonlinear-so-l-of-psi-one-plus-psi-two-is-not-l-psi-one-plus-l-psi-two-the-central-ipek-caticha-prediction-that-gravity-breaks-quantum-superposition",
  supported_by @ "paper:ipek-caticha-entropic-dynamics-quantum-gravity-functional-schrodinger-constraints"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravBackreaction_born where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
  formalizes @ "claim:the-gravitational-backreaction-term-is-sourced-by-the-born-rule-probability-rho-equals-psi-modulus-squared-the-same-mod-psi-squared-that-sources-the-geometry-drives-the-nonlinearity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravGenerator_flat_limit where
  formalizes @ "claim:at-zero-gravitational-coupling-lambda-equals-zero-the-generator-reduces-to-the-flat-linear-operator-so-superposition-is-restored-the-violation-is-exactly-the-gravitational-coupling",
  requires @ "claim:coupling-the-entropic-dynamics-quantum-field-to-dynamical-gravity-makes-the-generator-l-of-psi-equals-e-psi-plus-lambda-psi-modulus-squared-psi-nonlinear-so-l-of-psi-one-plus-psi-two-is-not-l-psi-one-plus-l-psi-two-the-central-ipek-caticha-prediction-that-gravity-breaks-quantum-superposition"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.flatGenerator_additive where
  formalizes @ "claim:the-uncoupled-flat-generator-is-additive-over-superpositions-linear-quantum-mechanics-holds-exactly-in-the-absence-of-gravitational-backreaction"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gaugeCovariantCubic_unique where
  supported_by @ "lean:CPTPMap.funext",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gaugeCovariantCubic_eq",
  formalizes @ "claim:within-the-local-u1-gauge-covariant-cubic-class-the-normalization-b-of-one-equals-lambda-uniquely-fixes-the-irreversible-backreaction-to-lambda-times-modulus-psi-squared-times-psi",
  caveat @ "claim:this-is-uniqueness-inside-an-explicit-local-covariance-and-homogeneity-class-not-a-derivation-that-nature-must-select-that-class"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleGaugeCovariantCubic_unique where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gaugeCovariantCubic_unique",
  formalizes @ "claim:within-the-local-u1-gauge-covariant-cubic-class-the-dissipative-normalization-b-of-one-equals-minus-gamma-uniquely-fixes-b-to-minus-gamma-times-modulus-psi-squared-times-psi"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleGravBackreaction_rate_nonpos where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleGravBackreaction_rate",
  formalizes @ "claim:for-nonnegative-gamma-the-unique-irreversible-cubic-backreaction-has-nonpositive-instantaneous-born-norm-rate"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_local_continuumGrav_solution where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumGravGenerator_contDiff",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-full-pointwise-nonlinear-ipek-caticha-generator-on-continuous-complex-fields-over-a-compact-continuum-carrier-has-a-local-banach-space-solution",
  caveat @ "claim:local-existence-does-not-imply-global-no-blowup-or-a-solution-of-the-coupled-einstein-constraint-system"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumGrav_solution_eventuallyEq where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:the-continuum-nonlinear-ipek-caticha-initial-value-problem-is-locally-unique",
  requires @ "claim:the-full-pointwise-nonlinear-ipek-caticha-generator-on-continuous-complex-fields-over-a-compact-continuum-carrier-has-a-local-banach-space-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumIrreversibleCubic_solution where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_hasDerivWithinAt_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_normSq_le",
  formalizes @ "claim:the-unique-nonnegative-damping-cubic-irreversible-sector-on-continuous-complex-fields-over-an-infinite-compact-continuum-carrier-has-an-explicit-solution-for-every-positive-time-that-solves-the-pointwise-ode-and-cannot-increase-born-norm",
  requires @ "claim:within-the-local-u1-gauge-covariant-cubic-class-the-dissipative-normalization-b-of-one-equals-minus-gamma-uniquely-fixes-b-to-minus-gamma-times-modulus-psi-squared-times-psi",
  caveat @ "claim:global-positive-time-closure-here-is-for-the-exact-pure-cubic-irreversible-sector"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_add where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleCubicFlow_add",
  formalizes @ "claim:the-explicit-nonlinear-irreversible-cubic-propagator-obeys-the-positive-time-flow-composition-law-on-the-infinite-dimensional-continuum-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_norm_le where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_normSq_le",
  formalizes @ "claim:the-explicit-nonlinear-irreversible-cubic-flow-is-a-contraction-in-the-continuum-continuous-field-supremum-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumIrreversibleComplexCubic_solution where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleComplexCubicFlow_hasDerivWithinAt_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleComplexCubicFlow_norm_le",
  formalizes @ "claim:the-homogeneous-hamiltonian-phase-plus-unique-irreversible-cubic-cat-ept-generator-has-an-explicit-global-positive-time-continuum-solution-that-solves-the-combined-complex-ode-and-contracts-the-banach-norm",
  requires @ "claim:within-the-local-u1-gauge-covariant-cubic-class-the-dissipative-normalization-b-of-one-equals-minus-gamma-uniquely-fixes-b-to-minus-gamma-times-modulus-psi-squared-times-psi",
  caveat @ "claim:the-hamiltonian-energy-is-a-spatially-homogeneous-real-parameter-this-does-not-yet-prove-global-existence-for-a-state-dependent-hamiltonian-or-the-coupled-einstein-constraint-system"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_add where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleComplexCubicFlow_add",
  formalizes @ "claim:for-every-fixed-continuous-real-multiplication-energy-field-the-hamiltonian-phase-plus-irreversible-cubic-propagator-obeys-the-exact-positive-time-nonlinear-flow-law"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le where
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:spatially-varying-fixed-real-energy-changes-only-phase-so-the-exact-nonlinear-continuum-flow-remains-a-contraction-in-the-continuous-field-supremum-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumGravGenerator_stateIndependent_solution where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_add",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le",
  formalizes @ "claim:the-existing-continuum-ipek-caticha-generator-with-coefficient-minus-i-times-a-fixed-continuous-real-energy-field-and-coupling-minus-gamma-has-an-explicit-global-positive-time-pointwise-solution-flow-and-banach-norm-contraction",
  requires @ "claim:for-every-fixed-continuous-real-multiplication-energy-field-the-hamiltonian-phase-plus-irreversible-cubic-propagator-obeys-the-exact-positive-time-nonlinear-flow-law",
  caveat @ "claim:this-is-a-global-pointwise-ode-solution-for-a-fixed-multiplication-energy-field-not-a-banach-strong-solution-for-a-state-dependent-hamiltonian-a-spatial-differential-operator-or-the-coupled-einstein-system"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_joint_continuous where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.cubicDampingDenominator_pos",
  formalizes @ "claim:the-fixed-spatial-energy-nonlinear-cat-ept-propagator-depends-jointly-continuously-on-nonnegative-time-and-the-initial-continuum-field-in-the-supremum-norm-topology"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_contracts where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le",
  formalizes @ "claim:the-exact-fixed-spatial-energy-evolution-is-a-genuine-mathlib-continuous-nonlinear-semiflow-on-the-full-continuum-banach-carrier-and-every-time-map-is-norm-contracting",
  requires @ "claim:the-fixed-spatial-energy-nonlinear-cat-ept-propagator-depends-jointly-continuously-on-nonnegative-time-and-the-initial-continuum-field-in-the-supremum-norm-topology"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_tendsto_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le_invTimeSqrt",
  formalizes @ "claim:for-strictly-positive-irreversible-coupling-every-fixed-spatial-energy-continuum-orbit-converges-uniformly-to-the-zero-field-as-positive-time-tends-to-infinity",
  requires @ "claim:the-exact-fixed-spatial-energy-evolution-is-a-genuine-mathlib-continuous-nonlinear-semiflow-on-the-full-continuum-banach-carrier-and-every-time-map-is-norm-contracting",
  caveat @ "claim:the-asymptotic-zero-limit-is-a-property-of-the-selected-pure-cubic-damping-law-with-a-fixed-real-multiplication-energy-not-a-general-state-dependent-hamiltonian-or-spatial-pde-decay-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le_initial where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleComplexCubicFlow_normSq",
  formalizes @ "claim:the-fixed-spatial-energy-cat-ept-flow-obeys-the-sharp-initial-norm-envelope-norm-psi-t-less-than-or-equal-to-norm-psi-zero-divided-by-sqrt-one-plus-two-gamma-t-times-norm-psi-zero-squared",
  requires @ "claim:the-exact-fixed-spatial-energy-evolution-is-a-genuine-mathlib-continuous-nonlinear-semiflow-on-the-full-continuum-banach-carrier-and-every-time-map-is-norm-contracting"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_fixed_iff_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_lt",
  formalizes @ "claim:for-strictly-positive-irreversible-coupling-every-strictly-positive-time-map-of-the-fixed-spatial-energy-cat-ept-semiflow-fixes-exactly-the-zero-continuum-field",
  requires @ "claim:the-fixed-spatial-energy-cat-ept-flow-obeys-the-sharp-initial-norm-envelope-norm-psi-t-less-than-or-equal-to-norm-psi-zero-divided-by-sqrt-one-plus-two-gamma-t-times-norm-psi-zero-squared"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_zero_globalAttractor where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_fixed_iff_zero",
  formalizes @ "claim:zero-is-invariant-is-the-unique-positive-time-fixed-field-and-attracts-every-continuum-field-in-supremum-norm-for-the-exact-fixed-spatial-energy-cat-ept-semiflow",
  requires @ "claim:for-strictly-positive-irreversible-coupling-every-strictly-positive-time-map-of-the-fixed-spatial-energy-cat-ept-semiflow-fixes-exactly-the-zero-continuum-field",
  caveat @ "claim:this-singleton-global-attractor-is-for-the-exact-selected-cubic-damping-law-with-a-fixed-real-multiplication-energy-not-for-a-state-dependent-hamiltonian-spatial-pde-or-coupled-einstein-evolution"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_eq_initial where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le_initial",
  formalizes @ "claim:on-a-compact-continuum-carrier-the-fixed-spatial-energy-cat-ept-flow-norm-is-exactly-the-initial-norm-divided-by-sqrt-one-plus-two-gamma-t-times-the-initial-norm-squared",
  requires @ "claim:the-fixed-spatial-energy-cat-ept-flow-obeys-the-sharp-initial-norm-envelope-norm-psi-t-less-than-or-equal-to-norm-psi-zero-divided-by-sqrt-one-plus-two-gamma-t-times-norm-psi-zero-squared"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_eq_zero_iff where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_eq_initial",
  formalizes @ "claim:a-continuum-field-reaches-zero-at-a-finite-nonnegative-time-under-the-fixed-spatial-energy-cat-ept-flow-if-and-only-if-it-was-initially-zero",
  requires @ "claim:on-a-compact-continuum-carrier-the-fixed-spatial-energy-cat-ept-flow-norm-is-exactly-the-initial-norm-divided-by-sqrt-one-plus-two-gamma-t-times-the-initial-norm-squared"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_strictAnti where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_add",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_eq_zero_iff",
  formalizes @ "claim:with-positive-irreversible-coupling-the-continuum-norm-of-every-nonzero-fixed-spatial-energy-cat-ept-orbit-strictly-decreases-between-distinct-nonnegative-times",
  requires @ "claim:a-continuum-field-reaches-zero-at-a-finite-nonnegative-time-under-the-fixed-spatial-energy-cat-ept-flow-if-and-only-if-it-was-initially-zero"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_uniformly_absorbs where
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:for-every-positive-radius-the-explicit-time-one-divided-by-two-gamma-radius-squared-sends-every-initial-continuum-field-into-that-radius-around-zero",
  requires @ "claim:for-strictly-positive-irreversible-coupling-every-fixed-spatial-energy-continuum-orbit-converges-uniformly-to-the-zero-field-as-positive-time-tends-to-infinity",
  caveat @ "claim:uniform-absorption-of-the-entire-unbounded-carrier-is-a-special-consequence-of-the-selected-cubic-damping-law-not-a-generic-property-of-state-dependent-hamiltonian-spatial-pde-or-coupled-einstein-evolution"

zil_file_contract physlib.ipekCatichaSuperpositionViolation where
  promises "The Ipek-Caticha prediction that coupling quantum fields to gravity violates the superposition principle. The uncoupled flat generator is additive. The Born-density backreaction is the unique normalized law inside the stated local gauge-covariant cubic class; with normalization -gamma and gamma nonnegative it is uniquely irreversible and has nonpositive Born-norm rate. The full state-dependent energy-plus-cubic law has local Banach-space existence and uniqueness. For every fixed continuous real multiplication-energy field, the exact global positive-time solution forms a jointly continuous contractive nonlinear semiflow on the full continuum Banach carrier. Its continuum norm obeys an exact scalar decay law. With positive damping, zero is its unique positive-time fixed field, nonzero fields persist at every finite time with strictly decreasing norm, and an explicit time uniformly absorbs the entire carrier into every prescribed positive radius."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.flatGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravBackreaction",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction"]
  forbids_substitutes ["the full semiclassical Einstein equation with the expectation-value stress tensor and the measurement/collapse dynamics of the nonlinear evolution, which are the cited semiclassical-gravity infrastructure",
    "any claim that the observable magnitude of the superposition violation is predicted; only the algebraic nonlinearity of the generator at nonzero coupling is carried",
    "Banach-strong differentiability, global existence, no blowup, or uniqueness for a state-dependent Hamiltonian, a spatial differential operator, or outside the explicit local gauge-covariant cubic class"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravGenerator_superposition_violation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravBackreaction_born,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gravGenerator_flat_limit,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.flatGenerator_additive,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.gaugeCovariantCubic_unique,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleGaugeCovariantCubic_unique,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.irreversibleGravBackreaction_rate_nonpos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_local_continuumGrav_solution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumGrav_solution_eventuallyEq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumIrreversibleCubic_solution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_add,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumIrreversibleCubicFlow_norm_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumIrreversibleComplexCubic_solution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_add,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.exists_global_continuumGravGenerator_stateIndependent_solution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_joint_continuous,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_contracts,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_le_initial,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_fixed_iff_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicSemiflow_zero_globalAttractor,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_eq_initial,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_eq_zero_iff,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_norm_strictAnti,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation.continuumSpatialEnergyCubicFlow_uniformly_absorbs]

/- ZIL-END -/
