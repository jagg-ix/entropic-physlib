/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.SecondLaw
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Boltzmann H-theorem and the entropic-time arrow from coarse-graining

This module derives the **H-theorem** — the monotone decrease of the
Kullback–Leibler distance to equilibrium — from Mathlib's chain rule for
KL divergence, and connects it to the entropic-time arrow of
`Physlib.Thermodynamics.SecondLaw`.

## The physics

No formalism derives irreversibility from reversible micro-dynamics without a
coarse-graining choice. We make that single physical input explicit and prove
that everything else follows. A `CoarseGrainingStep` records two Markov
channels on the same system:

* `κ` — the actual, information-preserving (reversible / unitary) environment
 channel that correlates system and environment;
* `η` — the equilibrium / thermalising channel that resets the environment to
 its reference state.

The split is exactly the data-processing structure:

* **Reversible leg.** Applying the *same* channel to both the state and the
 reference preserves KL: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν`
 (`klDiv_reversible_invariant`, from `klDiv_compProd_left`). Reversible
 dynamics alone produces *no* entropy.

* **Coarse-graining leg.** Replacing `κ` by the equilibrium channel `η` can only
 *decrease* the KL distance to equilibrium
 (`hTheorem_step`), and the decrease equals the conditional KL
 `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` (`tauEnt_eq_entropyProduced`). That conditional
 term is the genuine, irreducible physical input — the entropy produced by
 the coarse-graining choice `κ ≠ η`.

The KL chain rule `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`
makes "fine ≥ coarse" (the data-processing inequality) a one-line consequence
in `ℝ≥0∞`, where `a ≤ a + b` holds unconditionally.

## Entropic time

Along a coarse-graining step the **entropic proper time** advance is the
dissipated KL, `tauEnt := D_initial − D_current ≥ 0` (`tauEnt_nonneg`,
derived from `h_dissipated`, itself derived from the H-theorem — not posited).
A step assembles into an `EntropyArrowWorldline` whose monotone entropy
production `S_I` is a **theorem**, closing the loop with the second-law arrow
of `Physlib.Thermodynamics.SecondLaw`.

## Origin and references

* L. Boltzmann, *Weitere Studien über das Wärmegleichgewicht unter
 Gasmolekülen* (1872) — the original H-theorem.
* G. Lindblad, *Completely positive maps and entropy inequalities*,
 Commun. Math. Phys. **40** (1975) 147 — monotonicity of relative entropy
 under CPTP maps (the quantum data-processing inequality).
* A. Uhlmann, *Relative entropy and the Wigner–Yanase–Dyson–Lieb concavity*,
 Commun. Math. Phys. **54** (1977) 21.

The KL infrastructure used here is Mathlib's
`InformationTheory.KullbackLeibler` (`klDiv_compProd_left`,
`klDiv_compProd_eq_add`). This is an independent Lean formalisation; it does
not depend on any external project.
-/

set_option autoImplicit false

namespace Physlib.Thermodynamics.BoltzmannHTheorem

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

@[expose] public section

/-! ## §1 — The two legs of the H-theorem at the level of KL divergence

We work with two measures `μ ν` on a system space and two Markov kernels
`κ η` into an environment space, matching the hypotheses of Mathlib's chain
rule. -/

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {κ η : Kernel 𝓧 𝓨}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]

/-- **Reversible leg.** Applying the *same* environment channel `κ` to both the
state and the reference preserves the KL divergence. Reversible / unitary
dynamics produces no entropy: there is nothing to dissipate when numerator and
denominator are processed identically. (This is `klDiv_compProd_left`, named
for its physical role.) -/
theorem klDiv_reversible_invariant :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν :=
  klDiv_compProd_left μ ν κ

/-- **Chain rule (data-processing decomposition).** The joint KL splits into the
marginal KL plus a non-negative conditional KL. The second term is the entropy
produced by the channel. -/
theorem klDiv_compProd_decomposition :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) :=
  klDiv_compProd_eq_add μ ν κ η

/-- **Data-processing inequality (coarse ≤ fine).** The marginal KL is a lower
bound for the joint KL: extending by a channel can only *increase* the
divergence relative to the base marginals. In `ℝ≥0∞` this is `a ≤ a + b`, with
no non-negativity side-condition. -/
theorem klDiv_marginal_le :
    klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [klDiv_compProd_decomposition]
  exact le_self_add

/-- **The H-theorem step (in `ℝ≥0∞`).** Replacing the reversible channel `κ` by
the equilibrium channel `η` on the state side decreases the KL distance to
equilibrium. The gap is the conditional KL `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`, the
coarse-graining entropy production. -/
theorem hTheorem_step :
    klDiv (μ ⊗ₘ η) (ν ⊗ₘ η) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [klDiv_compProd_left μ ν η, klDiv_compProd_decomposition]
  exact le_self_add

/-- **The H-theorem step (real-valued).** Under finiteness of the fine KL, the
`toReal` distances obey the same inequality — the form usable as a numeric
dissipation witness. -/
theorem hTheorem_step_toReal (hfin : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ η) (ν ⊗ₘ η)).toReal ≤ (klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal :=
  ENNReal.toReal_mono hfin hTheorem_step

/-! ## §2 — A coarse-graining step and the derived dissipation

We package the physical input as a structure and derive the H-theorem witness
`h_dissipated` as a theorem, rather than with it as a hypothesis. -/

/-- **A coarse-graining (H-theorem) step.** The single physical input is the
pair of channels `κ ≠ η`: the reversible environment channel `κ` and the
equilibrium channel `η`. Everything downstream is derived. -/
structure CoarseGrainingStep where
  /-- System state space. -/
  α : Type*
  /-- Environment space. -/
  β : Type*
  /-- Measurable structure on the system. -/
  [mα : MeasurableSpace α]
  /-- Measurable structure on the environment. -/
  [mβ : MeasurableSpace β]
  /-- The state measure. -/
  μ : Measure α
  /-- The reference measure (equilibrium marginal). -/
  ν : Measure α
  /-- The reversible / information-preserving environment channel. -/
  κ : Kernel α β
  /-- The equilibrium / thermalising channel. -/
  η : Kernel α β
  /-- The state is a finite measure. -/
  [hμ : IsFiniteMeasure μ]
  /-- The reference is a finite measure. -/
  [hν : IsFiniteMeasure ν]
  /-- `κ` is a Markov kernel. -/
  [hκ : IsMarkovKernel κ]
  /-- `η` is a Markov kernel. -/
  [hη : IsMarkovKernel η]
  /-- The fine (pre-coarsening) KL distance to equilibrium is finite. -/
  fine_kl_finite : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞

attribute [instance] CoarseGrainingStep.mα CoarseGrainingStep.mβ
  CoarseGrainingStep.hμ CoarseGrainingStep.hν
  CoarseGrainingStep.hκ CoarseGrainingStep.hη

namespace CoarseGrainingStep

variable (S : CoarseGrainingStep)

/-- KL distance to equilibrium of the fine (correlated) state, real-valued. -/
noncomputable def klInitial : ℝ := (klDiv (S.μ ⊗ₘ S.κ) (S.ν ⊗ₘ S.η)).toReal

/-- KL distance to equilibrium of the coarse-grained state, real-valued. -/
noncomputable def klCurrent : ℝ := (klDiv (S.μ ⊗ₘ S.η) (S.ν ⊗ₘ S.η)).toReal

/-- **The H-theorem witness, DERIVED.** The KL distance to equilibrium does not
increase under the coarse-graining step. This is the field `h_dissipated` of a
posited Markov flow turned into a theorem. -/
theorem h_dissipated : S.klCurrent ≤ S.klInitial :=
  hTheorem_step_toReal S.fine_kl_finite

/-- **Entropic proper-time advance** along the step: the dissipated KL. -/
noncomputable def tauEnt : ℝ := S.klInitial - S.klCurrent

/-- **Non-negativity of entropic proper time, DERIVED** from the H-theorem
(not a posited sign hypothesis). -/
theorem tauEnt_nonneg : 0 ≤ S.tauEnt := by
  unfold tauEnt
  linarith [S.h_dissipated]

/-- The coarse-graining entropy production: the conditional KL between the
fine and the equilibrium-channel joint states. -/
noncomputable def entropyProduced : ℝ := (klDiv (S.μ ⊗ₘ S.κ) (S.μ ⊗ₘ S.η)).toReal

/-- Entropy production is non-negative (`toReal` of a `ℝ≥0∞`). -/
theorem entropyProduced_nonneg : 0 ≤ S.entropyProduced := ENNReal.toReal_nonneg

/-- **The completion.** The entropic proper-time advance is *exactly* the
coarse-graining entropy production: `τ_ent = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`. The
KL decrease is the data-processing / coarse-graining term — the single genuine
physical input `κ ≠ η`, and nothing else. -/
theorem tauEnt_eq_entropyProduced : S.tauEnt = S.entropyProduced := by
  have hsum : klDiv (S.μ ⊗ₘ S.κ) (S.ν ⊗ₘ S.η)
      = klDiv S.μ S.ν + klDiv (S.μ ⊗ₘ S.κ) (S.μ ⊗ₘ S.η) :=
    klDiv_compProd_eq_add S.μ S.ν S.κ S.η
  have hfin := S.fine_kl_finite
  rw [hsum] at hfin
  obtain ⟨hμν, hgap⟩ := ENNReal.add_ne_top.mp hfin
  unfold tauEnt klInitial klCurrent entropyProduced
  rw [hsum, ENNReal.toReal_add hμν hgap, klDiv_compProd_left S.μ S.ν S.η]
  ring

end CoarseGrainingStep

/-! ## §3 — Bridge to the entropic-time arrow

A single coarse-graining step assembles into an `EntropyArrowWorldline`: the
entropy production `S_I` rises by the dissipated KL `τ_ent ≥ 0`, so its
monotonicity (the second-law arrow) is a derived theorem. -/

open Physlib.Thermodynamics.SecondLaw

/-- **Bridge.** A coarse-graining step yields an `EntropyArrowWorldline` whose
entropy production is `0` before the step and `S.tauEnt` after it. Monotonicity
of `S_I` — the operationalised second law — is *proved* from
`CoarseGrainingStep.tauEnt_nonneg`, not assumed. -/
noncomputable def CoarseGrainingStep.toEntropyArrowWorldline
    (S : CoarseGrainingStep) (ℏ : ℝ) (ℏ_pos : 0 < ℏ) :
    EntropyArrowWorldline where
  ℏ := ℏ
  ℏ_pos := ℏ_pos
  S_I_along t := if t < 1 then 0 else S.tauEnt
  τ_ent_along t := (if t < 1 then 0 else S.tauEnt) / ℏ
  τ_ent_eq _ := rfl
  S_I_monotone := by
    intro t₁ t₂ h
    split_ifs with h₁ h₂ h₂
    · exact le_refl _
    · exact S.tauEnt_nonneg
    · exact absurd (lt_of_le_of_lt h h₂) h₁
    · exact le_refl _
  S_I_at_zero_nonneg := by norm_num

/-! ## §4 — A concrete, non-vacuous step

The trivial step (`μ = ν`, `κ = η`: equilibrium already reached, reversible
channel) witnesses that the structure is inhabited. Its dissipated KL is `0`. -/

/-- A concrete coarse-graining step on the one-point space with identical
state/reference and identical channels. Witnesses non-vacuity. -/
noncomputable def trivialStep : CoarseGrainingStep where
  α := Unit
  β := Unit
  μ := Measure.dirac ()
  ν := Measure.dirac ()
  κ := Kernel.const Unit (Measure.dirac ())
  η := Kernel.const Unit (Measure.dirac ())
  fine_kl_finite := by
    rw [klDiv_self]
    exact ENNReal.zero_ne_top

/-- The trivial (already-equilibrated, reversible) step dissipates no KL: its
entropic proper-time advance is zero. -/
theorem trivialStep_tauEnt_zero : trivialStep.tauEnt = 0 := by
  have h1 : klDiv (trivialStep.μ ⊗ₘ trivialStep.κ) (trivialStep.ν ⊗ₘ trivialStep.η) = 0 := by
    rw [show trivialStep.ν ⊗ₘ trivialStep.η = trivialStep.μ ⊗ₘ trivialStep.κ from rfl,
      klDiv_self]
  have h2 : klDiv (trivialStep.μ ⊗ₘ trivialStep.η) (trivialStep.ν ⊗ₘ trivialStep.η) = 0 := by
    rw [show trivialStep.ν ⊗ₘ trivialStep.η = trivialStep.μ ⊗ₘ trivialStep.η from rfl,
      klDiv_self]
  unfold CoarseGrainingStep.tauEnt CoarseGrainingStep.klInitial
    CoarseGrainingStep.klCurrent
  rw [h1, h2]
  simp

/-! ## §5 — Data-processing inequality for measurable maps

§1 adjoins a *common* channel to a fixed pair of marginals (the reversible
leg). Here is the complementary, genuinely contractive face of data
processing: pushing both the state and the reference forward through *any*
measurable map `f` can only decrease their KL divergence,

  `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`   (`klDiv_map_le`).

Physically: coarse-graining the configuration space never manufactures
distinguishing information. This is the measure-theoretic form of monotone
relative entropy under the forgetful maps that define a coarse description —
the same monotonicity that underlies the entropic arrow of §3.

The proof composes three facts, each reduced to existing Mathlib API:

* **Relabelling invariance** (`klDiv_map_measurableEquiv`): a measurable
  bijection leaves KL unchanged, because the Radon–Nikodym derivative
  transports along it (`MeasurableEmbedding.rnDeriv_map`).
* **Marginal monotonicity** (`klDiv_fst_le`, `klDiv_snd_le`): forgetting a
  coordinate does not increase KL. Disintegrating `ρ = ρ.fst ⊗ₘ ρ.condKernel`
  and applying the chain rule `klDiv_compProd_eq_add` exhibits the gap as a
  conditional KL, non-negative in `ℝ≥0∞` (`le_self_add`).
* **A map is a marginal**: `μ.map f` is the second marginal of the graph join
  `μ ⊗ₘ (deterministic f)`, on which the reversible-leg identity
  `klDiv_compProd_left` returns `klDiv μ ν`.

Marginalisation has a `StandardBorelSpace`/`Nonempty` hypothesis on the
*forgotten* coordinate, which is where Mathlib's measure disintegration lives. -/

section DataProcessing

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mΩ : MeasurableSpace Ω}

/-- **KL divergence is invariant under a measurable equivalence.** Relabelling
the underlying space by a measurable bijection `e` leaves the divergence
unchanged: the Radon–Nikodym derivative transports along `e`, and both the
absolute-continuity condition and the integral defining KL are preserved. -/
theorem klDiv_map_measurableEquiv (e : α ≃ᵐ β) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  haveI : IsFiniteMeasure (μ.map e) := μ.isFiniteMeasure_map e
  haveI : IsFiniteMeasure (ν.map e) := ν.isFiniteMeasure_map e
  classical
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]
  refine if_ctx_congr ⟨fun h => ?_, fun h => ?_⟩ (fun _ => ?_) (fun _ => rfl)
  · -- forward: `μ.map e ≪ ν.map e → μ ≪ ν`, by pushing forward along `e.symm`
    have h2 := e.symm.measurableEmbedding.absolutelyContinuous_map h
    have hid : (⇑e.symm ∘ ⇑e) = id := funext fun x => e.symm_apply_apply x
    rwa [Measure.map_map e.symm.measurable e.measurable,
      Measure.map_map e.symm.measurable e.measurable, hid, Measure.map_id,
      Measure.map_id] at h2
  · -- converse: `μ ≪ ν → μ.map e ≪ ν.map e`
    exact e.measurableEmbedding.absolutelyContinuous_map h
  · -- under absolute continuity, the two integrals agree by change of variables
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    rw [hx]

/-- **Marginalisation does not increase KL (first coordinate).** Forgetting the
second coordinate of a joint measure can only decrease the divergence:
`klDiv ρ.fst σ.fst ≤ klDiv ρ σ`. The gap is the conditional KL of the
disintegrating kernels, non-negative in `ℝ≥0∞`. -/
theorem klDiv_fst_le [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ σ : Measure (α × Ω)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    klDiv ρ.fst σ.fst ≤ klDiv ρ σ := by
  have hρ : ρ.fst ⊗ₘ ρ.condKernel = ρ := ρ.disintegrate ρ.condKernel
  have hσ : σ.fst ⊗ₘ σ.condKernel = σ := σ.disintegrate σ.condKernel
  calc klDiv ρ.fst σ.fst
      ≤ klDiv ρ.fst σ.fst
          + klDiv (ρ.fst ⊗ₘ ρ.condKernel) (ρ.fst ⊗ₘ σ.condKernel) := le_self_add
    _ = klDiv (ρ.fst ⊗ₘ ρ.condKernel) (σ.fst ⊗ₘ σ.condKernel) :=
          (klDiv_compProd_eq_add _ _ _ _).symm
    _ = klDiv ρ σ := by rw [hρ, hσ]

/-- **Marginalisation does not increase KL (second coordinate).** The symmetric
statement for `klDiv ρ.snd σ.snd ≤ klDiv ρ σ`, obtained from `klDiv_fst_le` by
relabelling coordinates with `Prod.swap`. -/
theorem klDiv_snd_le [StandardBorelSpace α] [Nonempty α]
    (ρ σ : Measure (α × Ω)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    klDiv ρ.snd σ.snd ≤ klDiv ρ σ := by
  let e : (α × Ω) ≃ᵐ (Ω × α) := MeasurableEquiv.prodComm
  haveI : IsFiniteMeasure (ρ.map e) := ρ.isFiniteMeasure_map e
  haveI : IsFiniteMeasure (σ.map e) := σ.isFiniteMeasure_map e
  have hρ : ρ.snd = (ρ.map e).fst := by
    rw [Measure.snd, Measure.fst, Measure.map_map measurable_fst e.measurable]; rfl
  have hσ : σ.snd = (σ.map e).fst := by
    rw [Measure.snd, Measure.fst, Measure.map_map measurable_fst e.measurable]; rfl
  rw [hρ, hσ]
  exact (klDiv_fst_le (ρ.map e) (σ.map e)).trans_eq (klDiv_map_measurableEquiv e ρ σ)

/-- **Data-processing inequality for a measurable map.** Pushing both measures
forward through any measurable `f` cannot increase the KL divergence:

  `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`.

Coarse-graining the configuration space never creates distinguishing
information. The map is realised as the second marginal of its graph join
`μ ⊗ₘ (deterministic f)`, reducing the claim to `klDiv_snd_le` and the
reversible-leg identity `klDiv_compProd_left`. -/
theorem klDiv_map_le [StandardBorelSpace α] [Nonempty α]
    {f : α → β} (hf : Measurable f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  have hμ : μ.map f = (μ ⊗ₘ Kernel.deterministic f hf).snd := by
    rw [Measure.snd_compProd, Measure.deterministic_comp_eq_map hf]
  have hν : ν.map f = (ν ⊗ₘ Kernel.deterministic f hf).snd := by
    rw [Measure.snd_compProd, Measure.deterministic_comp_eq_map hf]
  rw [hμ, hν]
  exact (klDiv_snd_le _ _).trans_eq
    (klDiv_compProd_left μ ν (Kernel.deterministic f hf))

end DataProcessing

end

end Physlib.Thermodynamics.BoltzmannHTheorem
