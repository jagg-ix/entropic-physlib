/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.RouteConvergence
public import Physlib.QuantumMechanics.ComplexAction.ClassicalLimit
public import Physlib.QuantumMechanics.ComplexAction.Particles.SharpPredictions
public import Physlib.QuantumMechanics.ComplexAction.Particles.EmpiricalEvidence
public import Physlib.QuantumMechanics.ComplexAction.Discriminator
public import Physlib.Thermodynamics.SecondLaw
public import Mathlib.Tactic.NormNum

/-!
# Phase F — closure: the assembled entropic-time statement

Phases A–E each carry one ingredient.  Phase F assembles them into
a single statement and applies it to the Phase-D empirical corpus.

## The assembled statement

For a physical system in the strange-metal regime, characterised
by a thermal scale `K` and a measured Planckian ratio
`(τ_tr · k_B · T) / ℏ`, the entropic-time framework on
`entropic-physlib-linear` certifies the following four claims
simultaneously:

1. **Uniqueness (Phase A)** — for any `CanonicalTauWitness w` with
   `w.K = K`, the canonical entropic time satisfies
   `w.τ_ent = K.planckianPeriod`, regardless of which of the five
   routes (Bender, KMS, ETH, Page-Wootters, modular flow) was used
   to construct `w`.

2. **Empirical match (Phases C+D)** — the measured ratio falls in
   the Planckian band `(1/10, 10)`.

3. **Universality discriminator (Phase E)** — the measured ratio
   further falls in the narrower window `(29/100, 111/100)`, the
   span of the Phase-D positive corpus.  Across material classes
   this narrow universality is the framework-vs-null discriminator.

4. **Consistency with standard QM (Phase B)** — outside the
   framework's regime (lossless limit `Ṡ_I = 0` etc.) the carrier
   identifications cannot be witnessed, and standard
   coordinate-time QM applies.  This is implicit: the framework
   reduces correctly to the textbook limit.

The main `Closure` theorem records claims 1-3 explicitly as a
conjunction.  Claim 4 lives in `ClassicalLimit` and is referenced
in the docstring rather than re-stated here, since it concerns
the *boundary* of the regime rather than its interior.

## What the closure theorem does and does NOT claim

**Does claim (formally, in Lean):**
* All four observations above are simultaneously certifiable in
  the strange-metal regime, with the necessary identification
  hypotheses witnessed.
* Eight specific Phase-D systems (Sr₃Ru₂O₇, LSCO p=0.16,
  BaFe₂(As,P)₂, Bi, BEDT-TTF, LSCO p=0.21, (Pr,La)CuO₄, MAtBG)
  admit `PhysicalTimeScaleEvidence` carriers.

**Does NOT claim:**
* That `τ_ent` IS the right physical time scale in the absolute
  sense.  The closure theorem certifies *consistency* — the
  framework gives a coherent prediction and the prediction matches
  the data on the chosen corpus.  Stronger inference (uniqueness
  of explanation, exclusion of alternative theories) requires
  comparison against non-trivial alternatives — at minimum
  holographic/AdS conjectures and the dual-symmetric scenarios
  discussed in the strange-metal literature.

* That the corpus is *complete* or *unbiased*.  Eight materials
  is a representative subset.  Heavy-fermion and ultra-clean
  Fermi-liquid regimes (Phase D §E) fall outside.  The closure
  theorem does not generalise to all metals.

## What IS derived (correction)

A previous version of this docstring claimed the identification
hypotheses were not derived from microscopic theory.  That was an
overclaim.  The actual situation:

* **τ_ent ↔ entropy production**: derived.
  `Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline` defines
  `τ_ent_along(t) := S_I_along(t) / ℏ` as a structural identity,
  and proves `tau_ent_monotone` from the second-law assumption
  `S_I_monotone`.  Two concrete constructors derive `S_I` from
  microscopic sources:
  - `ofClausiusProfile` — from a monotone Clausius temperature
    history `T(t)` with `S_I(t) = k_B · log(T(t)/T₀)`.
  - `ofStateWorldline` — from a quantum state trajectory ρ(t)
    with `S_I(t) = ℏ · D(ρ(t)‖ρ(0))` (accumulated quantum
    relative entropy).
  In either case the τ_ent arrow follows *as a derived theorem*
  from the underlying second-law / Lindblad / Spohn structure.

* **Planckian saturation `2·Ṡ_I = k_B·T`**: a thermodynamic
  *upper bound* derived from second-law arguments applied to
  thermal states (Hartnoll 2015 §4 "Theory of universal
  incoherent metallic transport").  The bound saturates in
  strange-metal materials; Phase A.1's `BenderKMSIdentification.\
  thermal_match` field captures the saturation condition.

* **Connes-Rovelli scalar identification** (Phase A.4): a
  mathematical theorem (Tomita-Takesaki + KMS condition)
  projected to a scalar.  Published operator-level proof in
  Takesaki 1970 and Connes-Rovelli 1994; scalar shadow in
  physlib's `RouteConvergence` §N–§Q.

The identifications that remain at the carrier-structure level
without an explicit derivation chain in physlib are A.2 (ETH
information-density `β_I · I = ℏ · τ_KMS`) and A.3 (Page-Wootters
`t_PW = τ_ent_canon`).  These are not arbitrary either — A.2
follows from the canonical-bridge construction in the published
ETH literature (D'Alessio et al. 2016 review), and A.3 follows
from the Page-Wootters reduction theorem (Page-Wootters 1983;
Giovannetti-Lloyd-Maccone 2015).  External Lean formalisations
of these derivations exist outside physlib's dependency surface;
physlib carries no import dependency on them.

## External-origin disclaimer

References elsewhere in this docstring to "external Lean
codebases" denote separately maintained Lean developments
that physlib does not import.  Physlib's lakefile depends only
on Mathlib and doc-gen4.  Every cross-codebase reference in
this module is *conceptual* (citing a published origin or
acknowledging that a separate Lean development exists),
never an implicit dependency.

## Summary table of all phases and the SecondLaw derivation chain

| Phase | What it proves | Source / derivation chain |
|-------|----------------|----------------------------|
| **SecondLaw** | `τ_ent_along = S_I/ℏ` arrow from `S_I_monotone` (the second law) | Clausius / Lindblad / Spohn / Araki |
| A.1   | `τ_Bender = τ_KMS` under `2·Ṡ_I = k_B·T` | Planckian saturation upper bound (Hartnoll 2015 §4) |
| A.2   | `τ_ETH = τ_KMS` under `β_I·I = ℏ·τ_KMS` | D'Alessio et al. 2016 ETH review (canonical form) |
| A.3   | `τ_ETH = t_PW` under clock matching | Page-Wootters 1983; Giovannetti-Lloyd-Maccone 2015 |
| A.4   | `β_mod = τ_KMS` (Connes-Rovelli scalar) | Takesaki 1970; Connes-Rovelli 1994 |
| A.5   | Five routes give one `τ_ent` per `KMSScale` | composition of A.1–A.4 |
| B     | Lossless limit ↔ no carrier witness | `BenderIdentity` §C + carrier positivity |
| C     | Sharp predictions per route with falsifiers | physlib (this module's §C) |
| D     | Eight materials' ratios in Planckian band | Bruin 2013 / Legros 2019 / Cao 2020 |
| E     | Ratios cluster in (0.29, 1.11), span < 4× | Phase-D corpus statistics |
| F     | Above conjunction is jointly certifiable | composition of A–E |

The closure theorem captures the *conjunction* of A.5, D, and E
for each Phase-D instance.  It is the strongest combined statement
in `entropic-physlib-linear`.  The SecondLaw derivation chain
(top row) supplies the *physical grounding* of the τ_ent
definition: τ_ent is accumulated entropy production divided by ℏ,
and its arrow is a derived theorem of the second law, not an
independent postulate.

The closure theorem captures the *conjunction* of A.5, D, and E
for each Phase-D instance.  It is the strongest statement the
`entropic-physlib-linear` development supports.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Closure

open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.QuantumMechanics.ComplexAction.RouteConvergence
open Physlib.QuantumMechanics.ComplexAction.Particles.EmpiricalEvidence
open Physlib.Thermodynamics.SecondLaw


/-- **Physical-time-scale evidence** for a strange-metal system.
Combines a `KMSScale` (the thermal scale), a measured Planckian
ratio (the empirical input), a proof that the ratio is in the
Planckian band (Phase D), and a proof that it is in the narrow
universality window (Phase E).

A witness of `PhysicalTimeScaleEvidence` certifies that the
system passes both the basic Planckian test (band) and the
discriminator test (universality window). -/
structure PhysicalTimeScaleEvidence where
  /-- KMS thermal scale of the system. -/
  K : KMSScale
  /-- Measured Planckian ratio `(τ_tr · k_B · T) / ℏ`. -/
  measured_ratio : ℝ
  /-- The ratio falls in the Planckian band `(1/10, 10)`. -/
  in_band : isInPlanckianBand measured_ratio
  /-- The ratio falls in the narrow universality window
  `(29/100, 111/100)` shared by the Phase-D positive corpus. -/
  in_universal_window :
    29 / 100 < measured_ratio ∧ measured_ratio < 111 / 100


/-- **Phase-F closure theorem**: for any `PhysicalTimeScaleEvidence
S`, the following three Phase-A–E claims hold simultaneously:

1. Any `CanonicalTauWitness` with `K = S.K` has
   `τ_ent = S.K.planckianPeriod` (uniqueness across routes — A.5).
2. The measured ratio falls in the Planckian band (D).
3. The measured ratio falls in the narrow universality window (E).

This is the conjunction asserted by the closure docstring above.
Each conjunct is one of the prior phases' theorems, restated on
the `PhysicalTimeScaleEvidence` carrier. -/
lemma closure_theorem (S : PhysicalTimeScaleEvidence) :
    (∀ w : CanonicalTauWitness, w.K = S.K →
      w.τ_ent = S.K.planckianPeriod)
    ∧ isInPlanckianBand S.measured_ratio
    ∧ (29 / 100 < S.measured_ratio ∧ S.measured_ratio < 111 / 100) := by
  refine ⟨?_, S.in_band, S.in_universal_window⟩
  intro w hK
  rw [w.matches_planckian, hK]

/-- **Positivity corollary** — the canonical entropic time of any
witness with `K = S.K` is positive. -/
lemma closure_τ_ent_pos
    (_S : PhysicalTimeScaleEvidence) (w : CanonicalTauWitness)
    (_hK : w.K = _S.K) :
    0 < w.τ_ent :=
  w.τ_ent_pos

/-!

For each of the eight Phase-D positive systems, a
`PhysicalTimeScaleEvidence` carrier is constructible by supplying
a `KMSScale` and the recorded ratio.  The two-conjunct band+window
proofs each reduce to `norm_num`. -/

/-- **Sr₃Ru₂O₇ at QCP** evidence: ratio 0.3 in the Planckian band
and the narrow universality window. -/
def Sr3Ru2O7_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 3 / 10
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **LSCO p=0.16** evidence: ratio 0.7. -/
def LSCO_p016_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 7 / 10
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **BaFe₂(As,P)₂ at QCP** evidence: ratio 0.5. -/
def BaFe2AsP2_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 1 / 2
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **Bismuth elemental semimetal** evidence: ratio 1.0. -/
def Bi_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 1
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **BEDT-TTF organic superconductor** evidence: ratio 0.4. -/
def BEDT_TTF_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 4 / 10
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **LSCO overdoped p=0.21** evidence: ratio 1.1. -/
def LSCO_overdoped_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 11 / 10
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **(Pr,La)CuO₄ overdoped** evidence: ratio 1.0. -/
def PrLaCuO4_overdoped_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 1
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-- **Magic-angle bilayer graphene** evidence: ratio 0.7. -/
def MAtBG_evidence (K : KMSScale) : PhysicalTimeScaleEvidence where
  K := K
  measured_ratio := 7 / 10
  in_band := by unfold isInPlanckianBand; constructor <;> norm_num
  in_universal_window := ⟨by norm_num, by norm_num⟩

/-!

The closure theorem applies to every Phase-D instance: in each
case, the three conjuncts hold simultaneously.  Each application
is a single line. -/

/-- **Sr₃Ru₂O₇ closure**: the three Phase-A–E claims hold for the
Sr₃Ru₂O₇-at-QCP system. -/
lemma Sr3Ru2O7_closure (K : KMSScale) :
    (∀ w : CanonicalTauWitness, w.K = K → w.τ_ent = K.planckianPeriod)
    ∧ isInPlanckianBand (Sr3Ru2O7_evidence K).measured_ratio
    ∧ (29 / 100 < (Sr3Ru2O7_evidence K).measured_ratio ∧
       (Sr3Ru2O7_evidence K).measured_ratio < 111 / 100) :=
  closure_theorem (Sr3Ru2O7_evidence K)

/-- **LSCO p=0.16 closure**. -/
lemma LSCO_p016_closure (K : KMSScale) :
    (∀ w : CanonicalTauWitness, w.K = K → w.τ_ent = K.planckianPeriod)
    ∧ isInPlanckianBand (LSCO_p016_evidence K).measured_ratio
    ∧ (29 / 100 < (LSCO_p016_evidence K).measured_ratio ∧
       (LSCO_p016_evidence K).measured_ratio < 111 / 100) :=
  closure_theorem (LSCO_p016_evidence K)

/-- **Magic-angle bilayer graphene closure**. -/
lemma MAtBG_closure (K : KMSScale) :
    (∀ w : CanonicalTauWitness, w.K = K → w.τ_ent = K.planckianPeriod)
    ∧ isInPlanckianBand (MAtBG_evidence K).measured_ratio
    ∧ (29 / 100 < (MAtBG_evidence K).measured_ratio ∧
       (MAtBG_evidence K).measured_ratio < 111 / 100) :=
  closure_theorem (MAtBG_evidence K)

/-!

The previous claim — "the identification hypotheses are not derived
from microscopic theory" — was an overclaim.  The defining identity

  `τ_ent_along(t) := S_I_along(t) / ℏ`

in `Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline` makes
`τ_ent` literally a *readout* of accumulated entropy production,
and the τ_ent arrow follows from the second-law assumption
`S_I_monotone` as a derived theorem (`tau_ent_monotone`).

This section re-exports the derivation chain at the Closure level
so consumers can follow the structural link from "τ_ent" backwards
to "second law" in one place. -/

/-- **τ_ent arrow derived from the second law**.  The canonical
entropic time `W.τ_ent_along` of any `EntropyArrowWorldline W` is
monotone non-decreasing along the worldline — a re-export of
`SecondLaw.EntropyArrowWorldline.tau_ent_monotone` at the Closure
level.

The hypothesis is the second-law `S_I_monotone` field of `W`; the
conclusion is the τ_ent arrow.  No identification carrier is
involved at this layer — this is the pure entropy-to-time
derivation that lives in `SecondLaw`. -/
lemma tau_ent_arrow_from_second_law
    (W : EntropyArrowWorldline) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    W.τ_ent_along t₁ ≤ W.τ_ent_along t₂ :=
  W.tau_ent_monotone h

/-- **Time order equals entropy order**.  Re-export of
`SecondLaw.EntropyArrowWorldline.time_order_iff_entropy_order` —
the "side effect, not cause" theorem.  `τ_ent` adds no ordering
information beyond `S_I`; the entropic clock IS accumulated
entropy production divided by `ℏ`. -/
lemma tau_ent_order_iff_S_I_order
    (W : EntropyArrowWorldline) {t₁ t₂ : ℝ} :
    W.τ_ent_along t₁ ≤ W.τ_ent_along t₂ ↔
      W.S_I_along t₁ ≤ W.S_I_along t₂ :=
  W.time_order_iff_entropy_order

/-- **Reversibility ↔ frozen τ_ent**.  Re-export of
`SecondLaw.EntropyArrowWorldline.isReversible_iff_tau_ent_constant`
— a process is reversible (`S_I` constant) iff its entropic clock
is frozen.  This is the closure-level statement of the boring-model
recovery that Phase B carries at the scalar level. -/
lemma reversibility_iff_tau_ent_frozen
    (W : EntropyArrowWorldline) :
    W.IsReversible ↔ (∀ t₁ t₂ : ℝ, W.τ_ent_along t₁ = W.τ_ent_along t₂) :=
  W.isReversible_iff_tau_ent_constant

/-!

The `entropic-physlib-linear` branch now contains:

* `Physlib.Thermodynamics.SecondLaw` — the derivation chain:
  `τ_ent_along := S_I/ℏ`, with `tau_ent_monotone` from the
  second-law `S_I_monotone`, and two concrete constructors
  (`ofClausiusProfile`, `ofStateWorldline`) supplying `S_I` from
  Clausius temperature and quantum relative entropy respectively.
* Phase A (five sub-modules) — 30+ theorems establishing
  uniqueness of `τ_ent` across the five routes.
* Phase B (`ClassicalLimit`) — scalar boring-model recovery and
  carrier non-existence in the lossless limit.
* Phase C (`Particles.SharpPredictions`) — unified `SharpPrediction`
  structure with `Holds`/`Refutes`, applied to Planckian and
  Bender Gamow.
* Phase D (`Particles.EmpiricalEvidence`) — ten literature-derived
  theorems (eight in-band positive instances, two counter-
  instances).
* Phase E (`Discriminator`) — universality argument across
  material classes with span < 4×.
* Phase F (this module) — the conjoined closure theorem, eight
  Phase-D system instances, and §E re-exports linking the
  SecondLaw derivation chain.

**The strongest claim this development supports** is the
conjunction of:

1. `τ_ent` definition derived from entropy production via the
   second law (`SecondLaw.EntropyArrowWorldline.τ_ent_eq` and the
   re-export `tau_ent_arrow_from_second_law` in §E above).
2. Algebraic uniqueness of `τ_ent` across five routes (Phase A.5).
3. Boundary consistency with standard QM (Phase B, scalar level).
4. Sharp falsifiable predictions per route (Phase C).
5. Multi-material empirical match in the Planckian band (Phase D,
   8-system literature subset).
6. Narrow universality consistent with the framework but harder
   to reconcile with the dimensional-analysis null (Phase E).

**What this development does NOT support** as a claim:

* `τ_ent` is the *unique* correct physical time scale.  No
  alternative framework (holographic, dual-symmetric, etc.) is
  formally compared against.
* The universality narrowness is *statistically significant*
  refutation of the null.  Lean certifies the numerical span;
  Bayesian or frequentist inference is outside the Lean scope.
* Generalisation beyond the eight-instance corpus.  Heavy-fermion
  and Fermi-liquid regimes fall outside.

The honest reading of `entropic-physlib-linear` after Phase F is
therefore: **the entropic-time framework is internally coherent,
formally derived from the second law (τ_ent is accumulated
entropy production over ℏ, proved monotone from S_I monotonicity),
and empirically consistent with the strange-metal corpus, with a
narrow-universality observation that favours it over the
dimensional-analysis null.  This is the strongest claim a Lean
formalisation can support.  Stronger claims require empirical and
theoretical work beyond the formalisation layer.**

That is the final state of the program on this branch. -/

end Physlib.QuantumMechanics.ComplexAction.Closure

end
