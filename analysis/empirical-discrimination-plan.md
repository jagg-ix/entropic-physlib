# Empirical discrimination plan — what is attempted, why, and what is refused

Written 2026-08-12 against branch `entropic-physlib-linear-full`.
Companion to `analysis/uncovered-modules.md` (build coverage) and `analysis/AUDIT.md` (graph
hygiene). This document is about **evidence**, not coverage.

---

## 1. The goal, stated so it can be checked

The objective is to put CAT/EPT on solid ground. At this stage of a framework, "solid" cannot
mean *proved*. It means:

> **a core that has survived deliberate attempts to kill it, with the claims that failed
> removed rather than defended.**

That definition matters because it makes progress measurable in a direction the program has not
been moving. Two claims have been killed or narrowed so far, and both count as progress:

| claim | how it was tested | outcome |
|---|---|---|
| `S_I` accumulates as a **dissipative** rate | Compton-anchor coherence bound gives a `1/e` coherence time `ħ/mc² ≈ 8×10⁻²⁷ s` for Rb-87; interferometers recombine over milliseconds | **refuted.** A phase-like reading survives |
| `G = ħc/m²` at any mass | `comptonCellG_eq_iff_planck_mass`: equals Newton's constant **iff** `m² = ħc/G` | **narrowed to the Planck mass.** Overshoot elsewhere is `1/α_G` — `5.7×10⁴⁴` at the electron |

Neither was a new formalization. Both were consequences drawn from existing structure and
checked against numbers already published.

---

## 2. The diagnosis this plan corrects

The repository holds **3212 `formalizes` claims. 34 carry an `experimental_bound`** — about 1%.
The remaining 99% cannot fail, so they cannot contribute to the goal in §1.

Three target-selection patterns produced that ratio. They are recorded here as things to
**stop doing**, not as criticism of the work, which is internally sound.

**(a) "Extend / link / connect" targets produce composition theorems, which cannot fail.**
A representative chain from this arc: coin angle → clock → mass → Yukawa → `G` → inverse-square
→ Jacobson coupling → length unit → cone → EEP → curved-space validity. Every module's own scope
note says, near-verbatim, *"what is added is composition."* That is honest labelling of a real
limit: **a chain is exactly as testable as its weakest input**, here the calibration
`S_I = ħγC`, which is `conditional-model`. Ten compositions later it is still that one
calibration, only harder to see.

**(b) Formalizing uncontested standard physics tests the library, not the theory.**
Kobe 1999 photon zitterbewegung, van Kampen Itô/Stratonovich, Chen–Vishwanath SPT. Real physics,
uncontested since publication. Formalizing them exercises `physlib` and does find defects — two
genuine overclaims were found and fixed this way on 2026-08-11 — but **no outcome could have
supported or damaged CAT/EPT.** Budget this as library work, not evidence.

**(c) The discriminating thread was dropped.**
The ENZ / γ_eff gain-threshold work was the empirical one: real data, real anomalies, a
measurable threshold. It ended with the correct target identified (the gain/decay threshold, not
`λ_ent = γ_Drude`) and was then abandoned for formalization.

---

## 3. Constraints — what this plan refuses, and why

**C1. No new "extend X with Y" modules until §5 Tier 1 is run.**
*Why:* composition adds to the 3212 without touching the 34. It is the exact mechanism that
produced the 1% ratio.

**C2. No formalizing an uncontested paper as evidence work.**
*Why:* the outcome is independent of whether CAT/EPT is true. Permitted as explicitly-labelled
library work with its own budget; not counted toward the goal.

**C3. Before any formalization, answer: "what measurement would make me withdraw this?"**
*Why:* if there is no answer, the result is coverage. This is the single filter that separates
the three targets that moved solidity from the dozens that did not.

**C4. Do not run a law whose preconditions are unmet, and do not tune windows until the answer
improves.**
*Why:* on 2026-08-11 the Mpemba crossing law was pushed onto trapped-ion data and produced a
**52σ "discrepancy"** that was an artifact of two unmet preconditions — branches that are not
single exponentials, and a trace-distance estimator with a noise floor near 0.135 that *rises*
at late times. Intermediate window choices produced +4.4σ and +22σ, all meaningless. The
evaluator now gates on preconditions and reports NOT APPLICABLE. **Gates are part of the
deliverable.**

**C5. A test that only reproduces standard physics is consistency, not discrimination.**
*Why:* the FQHE 2/5 and 3/7 plateau claims and `sin²θ_W → 3/8` recover Jain-hierarchy and SU(5)
results. Passing shows CAT/EPT is not broken; it cannot separate it from textbook physics.
Deprioritised for this goal.

**C6. Claims whose own bound says "no direct measurement" are not in the queue.**
*Why:* seven of the 34 self-declare this — black-hole entropy, wormhole mass, Unruh temperature,
rest-frame zitterbewegung, horizon bit erasure, icosahedral structure. The labelling is honest;
they are simply not runnable now.

**C7. Exact factors between single-scale prescriptions carry no evidential weight, and the
coefficient that closes such a gap is a fit, not a resolution.**
*Why:* any two conditions of the form `M² = ħc·k/G` differ by `√(k₂/k₁)` **by construction** —
exactness is guaranteed before any computation, so "the ratio is exactly √(2π)" is not a finding.
The one-bit episode (2026-08-12) produced, in sequence: a "remarkable" exact `√(2π)`; a
"circumference resolution" whose coefficient was chosen *because* it closed the gap, with the
geometric name retrofitted (the radius had been "natural" one commit earlier); an unsupported
association of the factor with the Unruh normalization; and a "three inequivalent readings" claim,
two of whose readings were related by the proven `S = N/4` unit conversion.  All four came from
ignoring this constraint.  Corollary: a naturalness claim first made *after* seeing the number is
post hoc and must be flagged as such.

---

## 4. Why these targets and not others

Ranking is by **(distinctive × runnable)**, where

* *distinctive* = failure would force retraction of something specific to CAT/EPT;
* *runnable* = the number needed is already published, and was not fitted to the claim.

That ordering deliberately puts the load-bearing calibration first rather than the most
elaborate structure. The calibration `S_I = ħγC` and the Compton-cell identification carry the
most downstream weight, so they are where a failure is most informative and where survival is
worth most.

---

## 5. Targets

### Tier 1 — runnable now, each could kill a load-bearing claim

**T1. `G` from screen bit counting vs CODATA-2022.**
* Lean: `Thermodynamics.newton_law_of_gravity_from_verlinde`;
  `ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance` (the `σ₀` route);
  `ComptonClock.WalkConeDistanceChain.comptonCellG_eq_iff_planck_mass` (the new constraint).
* Bound already recorded: *"an independently measured inference variance σ₀ and Compton screen
  cell count must reproduce G without fitting G"*, and *"screen bit counting must reproduce the
  Cavendish value"*.
* Datum: `G = 6.67430(15)×10⁻¹¹ m³ kg⁻¹ s⁻²`.
* **Sharpened 2026-08-11:** the count must land at the Planck mass; any other mass overshoots by
  `1/α_G`. This converts a vague requirement into arithmetic.
* Falsifies if: σ₀ and the cell count, fixed independently, do not reproduce `G`.

**T2. Compton-clock anchor vs atom-recoil `h/m` metrology.**
* Lean: `ComptonClock.EntropicClockComptonAnchor.comptonAnchored_actionRate_eq_restEnergy`,
  `comptonAnchored_entropicTime_eq_physicalTime`.
* Bound already recorded: atom-recoil `h/m` fixes `mc²/ħ` to **0.2 ppb** (Parker 2018;
  Lan–Müller subharmonic Compton clock).
* Why first-rank: this is the calibration every composition chain in §2(a) rests on. Testing it
  tests the whole stack at its weakest link rather than at its most decorated one.
* Falsifies if: entropic time and physical time disagree beyond 0.2 ppb under the anchor.

**T3. Muon `g−2` two-channel consistency.**
* Lean: `ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha.schmidtNumberFromAlpha_eq_schmidtNumberFromGamma`.
* Structure: the same `K` must come out of **two independent routes** — precision α, and
  storage-ring beam kinematics at γ = 29.3 — both landing in `1.0005 < K < 1.0006`, against
  `a_μ` measured to 127 ppb (Fermilab final, 2025).
* **Corrected 2026-08-12 — this entry was wrong as first written.** It claimed "neither channel was
  fitted to the other, so disagreement is a real failure." `AnomalyRapidity.magicAnomalyFromGamma_gamma`
  now *proves* otherwise: at the magic point `γ = √(1+1/a)`, so the kinematic channel returns `a`
  identically. **At γ = 29.3 the two channels cannot disagree.** T3 as stated is untestable.
* Superseded by **T5**, which supplies the off-magic form that can fail.

### Tier 1b — RETRACTED: the muon two-route claim is forced, not testable

**T5. Off-magic two-route agreement on `K = coth η`.** *(added 2026-08-12)*
* Lean: `MuonAnomaly.AnomalyRapidity.magicAnomalyFromGamma_gamma`,
  `MuonAnomaly.AnomalyRapidity.anomaly_agreement_iff_magic` (both new);
  `MuonAnomaly.SchmidtNumberFromAlpha.schmidtNumberFromAlpha`;
  `MuonAnomaly.AnomalyRapidity.schmidtNumberFromGamma`.
* **Why this one is distinctive.** `K = coth η` has **two independent determinations**: the
  entanglement content (Schmidt number of the QED dressing, `K = √(1+α/2π)`) and pure beam
  kinematics (`K(γ) = γ/√(γ²−1)`, which is `coth η` at `γ = cosh η`).  Standard QED has no Schmidt
  number behind `a_μ` at all, so *one rapidity governing both* is a claim only CAT/EPT makes.
* **Why the existing agreement proves nothing, now as a theorem rather than a caveat.**
  `magicAnomalyFromGamma_gamma` : at the magic point `γ = √(1+1/a)`, so `γ²−1 = 1/a` and the
  kinematic route returns `a` **identically**.  Checked numerically: `a = 1.16592×10⁻³` gives
  `γ = 29.3034`, which is the reported 29.3 — the machine was built to that condition.
* **Where the content actually is.** `anomaly_agreement_iff_magic` : scaling the operating-point
  Lorentz factor by `s > 0` leaves the reconstruction equal to `a` **iff `s² = 1`**.  Agreement at
  the magic momentum is a tautology; agreement at *any* detuned momentum is a real constraint.
* **Sensitivity.** The reconstruction drifts at roughly twice the fractional detuning — a 0.1%
  detune moves the reconstructed anomaly by 0.2%, about four orders of magnitude above the 127 ppb
  precision of the Fermilab 2025 `a_μ`.  The test is not marginal; it is brutal.
* **Data.** Fermilab off-magic / detuned runs, which exist — the repo already carries the bound
  *"residual electric-field systematic `C_e` must scale with the off-magic detuning."*
* **RETRACTED 2026-08-12, same day it was written.** The question "does `K(γ)` track `K(α)`
  off-magic?" is not a theoretical choice. It is **derivable, and the derivation kills the test**:

  1. `a = K² − 1` (`anomaly_eq_schmidt_sq_sub_one`), so `a` is a property of the muon's dressing.
  2. `a_μ` is momentum-independent — required by this repository's own bound
     (*"the anomaly frequency must be energy-independent across the beam momentum spread"*,
     Fermilab 2025 at 127 ppb) and measured.
  3. Hence `K = √(1+a)` is **momentum-independent**.
  4. But `K(γ) = γ/√(γ²−1)` is **momentum-dependent by construction**.
  5. A momentum-independent quantity meets a momentum-dependent one at exactly one `γ`, namely
     `γ_magic = √(1+1/a)`.

  So `anomaly_agreement_iff_magic` is the *derivation* of the agreement, not a hypothesis awaiting
  data. Off-magic `K(γ)` must drift, by pure kinematics. **No off-magic run can test anything.**
* **Why it is not distinctive either.** The `α` route *defines* `K`; the `γ` route *is* the
  Thomas–BMT magic condition, textbook kinematics. CAT/EPT's contribution is relabelling
  `√(1+1/a)` as `cosh η`, and a relabelling has no measurable consequence. The residual content —
  momentum-independence of `a` — is shared with standard QED.
* **What the theorems are still worth.** They prove the magic-point agreement is vacuous, so it can
  never be cited as evidence. A subtraction, which §1 counts as progress.
* **The actual prerequisite, already named in `SchmidtNumberFromAlpha`'s own docstring:**
  *"a first-principles QFT Schmidt-spectrum calculation, direct entanglement tomography, or a
  genuinely independent determination of the anomaly from `K`."*  `γ_magic = cosh η` becomes a
  prediction the moment `η` is fixed independently — compute the Schmidt spectrum of the muon's QED
  dressing and get `coth η = √(1+α/2π)` **out** rather than putting it in. Then the magic momentum
  is predicted rather than fitted. **That calculation is the real T5.**

### Tier 2 — the only parameter-free distinctive claim

**T4. The ħ-free entropic clock, `τ_ent = log(A₀/A(t))`.**
* Lean: `Optics.EntropicEfoldReadout.tau_ent_eq_efolds`, `log_amplitude_ratio_eq_efolds`,
  `efolds_scaling_invariant`.
* No `ħ`, no calibration constant, no free parameter — the one distinctive claim with nothing to
  tune, and therefore nothing to hide a failure behind.
* Needs: an evaluator plus one relaxation dataset whose amplitude decays to zero (or whose floor
  is subtracted). Preconditions are much weaker than the crossing law's.

### Tier 3 — the only route to a distinctive prediction, scoped

**A. Compute the Schmidt spectrum of the muon's QED dressing.** *(scoped 2026-08-12)*

**Why this and nothing else.**  Every other target in this plan is a consistency test.  T5 was
retracted because the two-route agreement is derivable.  What makes the muon arc non-distinctive is
one fact: `AnomalousMagneticMoment.schwingerAnomaly α := α/(2π)` is a **definition** — Schwinger's
result is put in — and `SchmidtNumberFromAlpha.schmidtNumberFromAlpha α := √(1 + α/2π)` is built
from it.  No Schmidt spectrum is computed anywhere in the repository.  Compute it and get
`K = √(1+α/2π)` **out**, and the arc becomes a prediction in one step: `γ_magic = cosh η` is then
predicted rather than fitted.

**What must be computed.**  The physical muon is the bare muon dressed by the photon field.  Trace
out the field, obtain the reduced muon density matrix, and compute its purity; `K` is the inverse
purity.  The claim to be derived is `K² − 1 = a`, i.e. purity `= 1/(1 + α/2π)` at one loop.

**The obstruction, which is severe and must be faced first.**  The entanglement of a charged
particle with its own photon cloud is **infrared divergent**.  The soft-photon cloud has divergent
mean occupation — the infrared catastrophe — so as the IR cutoff is removed the reduced state tends
to maximally mixed, its purity to zero, and `K → ∞`.  A naive Schmidt number of the dressed muon is
therefore *not* `1.00058`; it is divergent.  Any attempt that reports a finite `K` without saying
what regulated it has hidden a cutoff, and matching `α/2π` by choosing that cutoff is a fit, not a
derivation.

**Why it is nonetheless not hopeless.**  The anomaly is `F₂(0)`, and **`F₂(0)` is IR-finite** — the
infrared divergence of the one-loop vertex lives in `F₁`, not in the spin-flip form factor.  So
there is a structurally sound target: show the Schmidt number is controlled by the **spin-flip
sector alone**, where the IR divergence is absent, rather than by the full dressing.  That is a
specific, checkable requirement rather than a hope.

**The decisive criterion, to be fixed before computing.**  Does the resulting `K` depend on the IR
regulator?
* *Depends on it* → the identification `K² − 1 = a` fails, and the muon arc's Schmidt reading is a
  cutoff artifact.  **This outcome is a genuine result and should be published as one.**
* *Independent of it, and equal to `√(1+α/2π)`* → a distinctive prediction, and the first in the
  program.
* *Independent of it, and equal to something else* → the identification is wrong but the structure
  survives; the anomaly is not the Schmidt defect.

**Honest assessment.**  This is a research problem in QED, not a formalization task, and the prior
should be that it fails — the IR structure is the natural enemy of a finite entanglement measure for
a charged particle.  It is listed because it is the *only* identified route to od7's Distinctive
column, and because all three outcomes above are informative.  Formalization has a role only after
the calculation exists: `physlib` can then certify the algebra, not supply it.

### Explicitly not the path
FQHE plateau claims; `sin²θ_W → 3/8`; the seven "no direct measurement" claims (C5, C6).

---

## 6. Method — reuse, do not reinvent

`scripts/mpemba_crosscarrier_evaluator.py` is the template and already encodes the discipline:

1. **Calibration set** — numbers the source publishes independently of the claim.
2. **Held-out set** — everything the law predicts; never fitted.
3. **Precondition gate** — check the theorem's hypotheses against the data *before* applying it;
   report NOT APPLICABLE rather than a number (C4).
4. **Data-quality gate** — noise floors, non-monotonicity, unit consistency.
5. **Verdict** — survives / falsified / not applicable, with the reason.

Adding a carrier or a target means writing a loader. The law and the gates do not change; that is
what "frozen" means.

---

## 7. Honest limits of this plan

* **Tier 1 is consistency testing of distinctive claims, not novel prediction.** Passing does not
  confirm CAT/EPT; it keeps it alive. Failing kills a load-bearing claim. That asymmetry is the
  whole reason to run them first, and it should not be oversold in either direction.
* **No entry in this plan addresses od7's Distinctive column.**  T5 was written as one and
  retracted the same day: the two-route agreement is forced by momentum-independence of `a`, not
  contingent.  Every remaining target is a consistency test.  The one identified route to a genuine
  distinctive prediction is target **A**, scoped in §5 Tier 3: compute the Schmidt spectrum of the
  muon's QED dressing.  It is a research problem in QED, not a formalization task, its prior should
  be failure on infrared grounds, and all three of its outcomes are informative.
* **One carrier is not cross-carrier validation.** The strategy of freezing a law and running it
  across unrelated carriers only pays off from the second carrier onward.
* **This plan is scoped to `physlib`.** If empirical work is deliberately housed in sibling
  repositories, the 1% ratio in §2 is a property of the formal layer by design and should be
  re-read accordingly — though od7 scores the Empirical column low across the whole program,
  which suggests it is not.

---

## 9. The diagnosis, after auditing every target

**Five of five proposed targets are untestable by construction.** Not five unlucky picks — one
structural property, found by applying §3 C3 ("what measurement would make me withdraw this?")
strictly to each.

| target | why it cannot fail |
|---|---|
| **T1** `G` from screen bit counting | `inferenceWidth C := 1/√(screenMass C)` — σ₀ is *defined from* the screen mass, itself defined from the cell count. The "independently measured σ₀" the bound demands does not exist; `A` and `N` are not measured for any real system |
| **T2** Compton anchor vs `h/m` | `comptonAnchored_entropicTime_eq_physicalTime` takes the calibration `K` as a **hypothesis**. Given the calibration the times agree — an identity, not a prediction |
| **T3** muon two-channel | `γ_magic = √(1+1/a)`, so the kinematic channel returns `a` identically (`magicAnomalyFromGamma_gamma`). The channels cannot disagree at γ = 29.3 |
| **T5** off-magic agreement | derivable: `a` is momentum-independent and `K(γ)` is not, so they meet at exactly one `γ`. Forced, not contingent |
| **T4** ħ-free clock | `entropicEfolds ρ t := ρt`. The log-amplitude identity holds for any exponential decay in any theory; the invariance is automatic for a dimensionless product; the difference law is distributivity. The one residue is the crossing law, already gated out on preconditions |

### What the pattern is

**CAT/EPT's claims are identities given a calibration, and the calibration is never independently
fixed.** In each case the theorem is exact and the physics enters through a hypothesis — `hlin`,
`K`, `σ₀`, the magic point — that no measurement constrains. This is why the program can be
internally coherent, formally broad, and simultaneously untestable: those are not in tension, they
are the same fact.

### What this does and does not mean

It is **not** a refutation. Nothing here shows any CAT/EPT claim is false. It shows the claims are
not of the shape that can be true-or-false against data as currently stated.

The fair description is that CAT/EPT is at present a **reformulation**: a re-expression of existing
physics in entropic, hyperbolic and Schmidt variables, internally consistent and unusually well
formalized. That is a real thing to have built, and reformulations have a strong track record —
Hamiltonian mechanics and the path integral both began that way. But a reformulation does not become
a theory until it **computes something the original formulation could not**.

### The single consequence for planning

Exactly one identified target computes rather than identifies: **A** (§5 Tier 3), the Schmidt
spectrum of the muon's QED dressing. Everything else in this document is bookkeeping in new
variables. If A fails on infrared grounds — the honest prior — then the correct position is to
present CAT/EPT as a formal unification framework, which is what od7 already concluded, rather than
as a physical theory awaiting confirmation.

**Recommended stance:** stop proposing empirical targets until one quantity is computed from first
principles. Adding targets of the identity-given-calibration shape consumes effort and produces the
appearance of an empirical program that the structure does not support.

---

## 10. The corrected path

§9 says the targets fail as a class. The correction is not a better target list — it is a different
question, a different unit of progress, and a tool the repository already has.

### 10.1 The criterion was wrong, not just loosely applied

C3 asks *"what measurement would make me withdraw this?"* All five targets passed a loose reading:
each **named** a real measurement (CODATA `G`, atom-recoil `h/m`, `a_μ` at 127 ppb, a decay trace).
What none of them did was let that measurement touch the hypothesis carrying the physics. Replace
C3 with:

> **C3′. Name the hypothesis in this theorem that no measurement constrains. Then ask whether it
> can be computed instead of assumed.**

Applied to the five: `hlin` (T4), `K` (T2), `σ₀` (T1), the magic point (T3, T5). Every one is
visible in the statement. C3′ would have rejected all five in minutes, without building anything.

### 10.2 The unit of progress changes

Stop counting **tests proposed**. Start counting **free calibrations eliminated**.

That is the quantity §9 identifies as blocking, it is monotone — a calibration once computed stays
computed — and unlike "propose an empirical target" it cannot be satisfied by restating an identity.
It also has an honest floor: a framework with zero free calibrations that reproduces known physics
is a reformulation with no free parameters, which is a substantially stronger position than the
current one even without a novel prediction.

### 10.3 The tool already exists

`Physlib/Meta/ZilGraph` computes `transitivePrimitivePremise` — the bare-postulate footprint each
claim rests on — and `ZilGraphReport` ranks those premises by **blast radius**, the number of claims
depending on each. The last full-root run recorded 54 primitive premises with a maximum blast radius
of 12. That ranking *is* the work queue: the highest-blast-radius premise is the one whose
computation buys the most.

This also reframes the audit work already done. `comptonCellG_eq_iff_planck_mass`,
`magicAnomalyFromGamma_gamma` and `bell_boost_fraction_bounds` did not fail to be tests — they
**narrowed or removed calibrations**, which under 10.2 is the progress metric. Four subtractions are
recorded in §1; that is the real tally, and it was accumulating while the target list produced
nothing.

### 10.4 The ledger, run — and it corrects the intuition

`#zil_graph_report` at full root, 2026-08-12. **81 primitive premises** (54 at the last recorded
run; the rise is coverage, not regression — the root closure went 2148 → 2376 modules this week, so
the graph now sees claims it previously could not). `decl_dependencies: 684`,
`max_blast_radius: 12`.

Ranked by reach (dependents), with `exact` = how many are `consistency-identity` claims:

| reach | exact | premise |
|---:|---:|---|
| 12 | 0 | `assumption:doubled-boost-mode` |
| 8 | 0 | `assumption:bisognano-wichmann-wedge` |
| 8 | 0 | `assumption:caticha-cafaro-inference-mass-is-inverse-position-variance` |
| 7 | 0 | `model:the-irreversible-generator-is-the-log-k-rapidity-scaling-of-a-fixed-reference-operator` |
| 6 | 2 | `assumption:the-selected-complex-tempered-kernel-is-a-fundamental-solution` |

**Target A is not at the top, and `K` does not appear at all.** The intuition that led to A — compute
the Schmidt number — was wrong about leverage. This is precisely why §10.3 says run the ledger
rather than pick by feel.

**The first iteration is `assumption:bisognano-wichmann-wedge` (reach 8).** It is the best target on
the list for a reason no other entry shares: **Bisognano–Wichmann is a theorem**, not a postulate.
For a Wightman field the modular group of a wedge algebra implements the boost. So unlike A — an
open calculation with an infrared obstruction that may not close — this premise is known-true and
the work is porting a proof. `physlib` already carries part of the machinery
(`QFT.PathIntegral.WickClock.wedgeBoostModularKms`, `modularAutomorphismStandardSubspace`), and six
modules rest on the assumption, including three `SciamaAdSCPTBisognanoWichmann*` files and
`SciamaAdSCPTUnruhFourClocks`.

Second is `caticha-cafaro-inference-mass-is-inverse-position-variance` (reach 8) — this is `m = 1/σ₀²`,
the same calibration that made T1 circular. Caticha and Cafaro derive it in entropic dynamics, so it
is a porting job rather than open research.

`doubled-boost-mode` has the largest reach (12) but `exact = 0`: every dependent is honestly
conditional, so discharging it buys reach without buying honesty. Lower priority than its rank
suggests.

**Also surfaced: `buried_conditionality` moved 0 → 1** —
`ComplexEinstein.ElectroGravitationalFieldEquations.metricStationary_iff_residualCoordinate_zero`,
an exact claim transitively resting on a weaker-status one. It is not new breakage; it became
*visible* when the coverage work brought its module into scope. That is the coverage work paying
off in exactly the intended way.

### 10.5 The loop

1. Discharge the top computable premise. **First: Bisognano–Wichmann.**
2. Re-run the ledger; blast radii shift as premises are discharged.
3. A premise proved *uncomputable* is also a result — it bounds what the framework can ever claim.
4. Re-rank and repeat.

### 10.6 What success looks like, stated in advance

* **Best case:** a premise is computed, its blast radius collapses, and the claims resting on it stop
  being conditional. Repeat until the free-calibration count is small enough that the framework's
  content is forced rather than chosen.
* **Realistic case:** the top premises resist computation. Then the honest output is the ledger
  itself — *"CAT/EPT reproduces this much physics on these N irreducible assumptions"* — which is a
  publishable characterization of a reformulation and does not overclaim.
* **Failure mode to avoid:** returning to target-proposing because the ledger is hard. §9 exists to
  make that return visible if it happens.

---

## 11. First iteration, scoped: discharge `bisognano-wichmann-wedge`

Ledger rank 2 by reach (8), rank 1 by tractability, because **Bisognano–Wichmann is a theorem**.
Tracing what the assumption still covers turns out to be unusually encouraging: most of it is
already discharged, and the residue is one finite-dimensional statement.

### 11.1 What is already proved

* **Operator side — done.** `SciamaAdSCPTBisognanoWichmannOperatorFlow` bundles the modular flow as
  a genuine one-parameter `*`-automorphism group on the finite wedge carrier: ring-homomorphism
  property, `σ₀ = id`, group law, derivative generator `2π·ad_K`, bracket preservation, `J² = 1`,
  and wedge Haag duality.
* **State side — four of five pillars done.** `SciamaAdSCPTBisognanoWichmannStateSide` constructs
  the vacuum as an explicit purification, proves the wedge Gibbs weights strictly positive
  (faithfulness), derives standardness from faithfulness (`faithful_state_standard`), builds the
  state's own modular flow (`modularGroupOfState`, `H_θ = −log ρ`) and shows both it and the boost
  flow satisfy the *same* KMS condition on the *same* state.

### 11.2 What is actually left

The module states it exactly: *"what remains of `assumption:bisognano-wichmann-wedge` after this
assembly is exactly **KMS-flow uniqueness** (Takesaki: a flow satisfying the KMS condition for a
faithful state is its modular flow) — cited, and nothing else."*

In the continuum that is a hard analytic theorem. **At the repository's finite-dimensional carrier
it is linear algebra**, and that is the discharge worth doing: it removes the assumption at the
level the repo actually works at, leaving only the continuum operator-valued-distribution extension
as genuinely cited — a far weaker residual than "BW's analytic input".

### 11.3 The two lemmas

1. **Scalar-shift invariance of the flow.** `exp(it(H + c·1)) a exp(−it(H + c·1)) = exp(itH) a exp(−itH)`
   — the scalar phases cancel in the conjugation. `H` and `c·1` commute, so
   `NormedSpace.exp_add_of_commute` applies; `unitaryFlow_add` and `unitaryFlow_mul_neg` are already
   present in `QuantumInertialFrameModularGroup`.
2. **Gibbs generators are unique up to a scalar.** If a self-adjoint `H'` has Gibbs state `ρ`
   (faithful), then `H' = −log ρ + c·1 = modularHamiltonianClm ρ + c·1`.

Together: any KMS flow for `ρ` is generated by `−log ρ` up to a scalar, and by (1) the scalar does
not reach the flow — so the flow **is** `modularGroupOfState ρ`. That is KMS-flow uniqueness,
finite-dimensionally.

### 11.4 Result — done, 2026-08-12

Both lemmas are proved and the step closes.

| | |
|---|---|
| `unitaryFlow_conj_add_scalar` | a central term never reaches the conjugation flow |
| `HermitianMat.log_exp` | the `log`/`exp` round trip |
| `modularHamiltonian_of_gibbs` | a Gibbs generator is `−log ρ` up to `log Z · 1` |

Together: any generator reproducing `ρ` as its Gibbs state differs from `−log ρ` by a central term
that the flow cannot see, so it generates *the* modular flow of `ρ` — KMS-flow uniqueness at the
finite carrier.

**RETRACTED, same day: this eliminated zero calibrations.**  An earlier revision of this section
claimed it as "the first calibration eliminated under §10.2". The ledger re-run says otherwise:

| | before | after |
|---|---|---|
| primitive premises | 81 | **81** |
| `assumption:bisognano-wichmann-wedge` | reach 8 | **reach 8, still primitive** |
| `max_blast_radius` | 12 | 12 |
| `decl_dependencies` | 684 | 686 — only the two new lemmas |

Two reasons, and the second is the real one.

1. *Mechanical.* Nothing `formalizes` the token, so it stays primitive, and the `requires` edges in
   `SummersVacuumModularLinks` and the Sciama modules still point at it. The narrowing was written in
   prose; the graph learned nothing.
2. *Substantive.* `SciamaAdSCPTBisognanoWichmannStateSide` says KMS-flow uniqueness is all that
   remained — but that is the **continuum** uniqueness on the wedge algebra. What was proved is the
   **finite-dimensional** one. The eight dependents are continuum wedge-algebra claims, so their
   conditionality is untouched.

The number could be moved by attaching `formalizes @ "assumption:bisognano-wichmann-wedge"` to
`modularHamiltonian_of_gibbs`. That would be false — a finite-carrier proof does not establish a
continuum premise — and it is exactly the move this audit exists to prevent.

**The pattern, one level up.** This is the identity-given-calibration failure of §9 committed while
applying the fix for it: a theorem proved at the carrier where it is provable, standing in for a
claim that lives at the carrier where it is not. The metric caught it; the prose would not have.

What the iteration did produce, which is real but smaller: `HermitianMat.log_exp` (an API transport
from Mathlib), `unitaryFlow_conj_add_scalar` (already load-bearing for
`ModularGeneratorPartitionFreedom`), and a correct finite-dimensional theorem.

**Lesson for the loop (§10.5).** "Discharge the top premise" must mean *at the carrier the dependents
use*. Before starting an iteration, check which carrier the reach-N dependents actually live on — a
premise provable only in finite dimensions, whose dependents are continuum claims, is not a
dischargeable target at all.

**A correction worth keeping.** On 2026-08-11 I reported the `log_exp` round trip as missing from the
API and as "a genuine contribution, not a quick lemma." It was already in Mathlib as `CFC.log_exp`,
with `HermitianMat.log` definitionally the same operation; `mat_cfc` — which my failed attempts were
reinventing — also already existed. The work was transport, not proof. The error was asserting
absence without searching, and it cost three failed attempts.

### 11.5 Why this was the right first iteration

* It is **known true**, so unlike target A there is no risk the calculation simply does not close.
* Reach 8 — six modules plus the `SummersVacuumModularLinks` claims stop being conditional.
* The machinery exists; this is assembly, not new theory.
* It is honest about what remains: the continuum step stays cited, and the ledger entry should be
  *narrowed*, not deleted.

Expected outcome: the premise's `exact` count is 0, so this buys **conditionality reduction rather
than honesty repair** — six modules move from conditional to derived at the finite carrier. Under
§10.2 that is exactly one calibration eliminated, which is the unit of progress.

---

## 12. Correction: sector-by-sector testing is the wrong test for a unification

Everything above tests CAT/EPT **inside** one sector at a time, and repeatedly concludes "reduces to
standard physics, therefore no discrimination". That inference is wrong, and it invalidated the
framing of §9's conclusion — though not §9's findings about T1–T5 themselves.

**A unification must be observationally standard in each sector it unifies.** That is the
correspondence principle, not a defect. Maxwell's unification predicted nothing new in electrostatics
and nothing new in magnetostatics; it predicted electromagnetic waves. Tested inside either sector it
would have scored "no discrimination", and the test would have been measuring the wrong thing.

The discriminating content of a unification is **cross-sector**: a quantity fixed on one side
constraining the other.

### 12.1 Where CAT/EPT's cross-sector content actually is

* **`ComptonClock.EntropicProperDistance.entropicProperDistance`** —
  `r = λ_C · log(schmidtNumber η)`. A **proper distance** fixed by an **entanglement** quantity.
  Neither quantum mechanics nor general relativity alone says a Schmidt number sets a length.
* **`ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius`** — the Clausius balance on
  every null direction outputs `G_ab + Λg_ab = 8πG·T_ab`. Thermodynamics → Einstein.

### 12.2 Why the rigidity result matters here

`Curvature.ActionPlaneMetricRigidity` shows the action-plane metric is forced, so the `η` appearing in
the boost is not a free parameter. The identification *entanglement rapidity = kinematic rapidity* is
therefore **structural rather than calibrated** — which is exactly the failure mode §9 found
everywhere else. The rigidity is what makes the bridge non-trivial instead of a relabelling.

### 12.3 What the bridge test still requires

An instance where both sides are fixed **independently**: `K` from entanglement tomography, `r` from a
geometric measurement, neither derived from the other. This is the same requirement that killed T3
and T5, where the second route turned out to be constructed from the first, so **the independence
check comes first, before any evaluator is built.**

### 12.4 Reordered queue

1. **The cross-sector bridge** — `r = λ_C log K`, with an independence check on the two
   determinations before anything else. This is the claim CAT/EPT uniquely makes.
2. **Target A** (§5 Tier 3) — demoted. It is a within-sector calculation; valuable, but it is not
   where a unification's content lives.
3. The remaining ledger premises, each with the carrier check of §11.4.

**What still stands from §9.** T1–T5 were untestable by construction and that finding is unchanged.
What was too narrow was the conclusion that *no* entry addresses the Distinctive column: the right
entry was never inside a sector, and this document did not contain it until now.

---

## 13. Audit: is the full-GR closure really incomplete?

od7 (2026-07-29) scored "Dynamical GR closure: still incomplete" with six gaps, while admitting it
*could not enumerate the branch*. Re-proved by grep + ZIL lookup on 2026-08-12. **Verdict: the
six-item "incomplete" is outdated. The Einstein–matter Cauchy-solver architecture od7 said was
missing exists as proven theorems, conditional on residuals the modules name themselves.**

### What exists (CanonicalTetradGravity)

| piece | theorem | date |
|---|---|---|
| local existence through arbitrary Cauchy data — full complex Einstein equation **and** sourced Hamiltonian **and** momentum constraints **and** harmonic gauge, at every time | `HarmonicGaugeLocalEinstein.exists_local_harmonicEinstein_evolution` | **2026-07-30, one day after od7** |
| uniqueness on the common interval | `local_harmonicEinstein_evolution_unique` | same |
| gauge (subsidiary-condition) propagation | `harmonicGauge_propagates` | same |
| constraint propagation | `ADMConstraintPropagation` | 2026-07-24 |
| maximal development, Choquet-Bruhat–Geroch style: extension embeddings, fixed-Cauchy equivalence, direct-limit gluing | `WaldMaximalDevelopment` + `DevelopmentDirectLimit` | **2026-07-24 — five days *before* od7**, which missed them because it could not see the branch |

od7's item 3 (constraint preservation) and item 5 (gauge-independent convergence, via maximal-development
uniqueness) are answered at the carrier. Item 2 (sourced TT) gained a carrier on 08-02. What remains:

### The named residuals (from the modules' own scope notes and ZIL caveats)

1. **The Lipschitz premise — the one real analytic gap.** At the `Ḣ¹` continuum carrier, local
   Lipschitz regularity of the reduced Einstein vector field is an explicit *input* (a structure
   field), because `H¹` is not a multiplication algebra in 3D. Discharging it = the quasilinear
   Sobolev/Moser estimates — the actual hard analysis of Choquet-Bruhat. The module says this
   itself, under "Honest analytic boundary".
2. **Smooth structure.** The maximal development glues *topological* causal-Einstein carriers; the
   quotient smooth Lorentzian atlas, and upgrading the fixed-Cauchy equivalence to a
   metric-preserving diffeomorphism, are named as remaining in the ZIL caveats.
3. **TT Green's operator** hypothesized, not constructed (08-11 audit); matter sector general
   (phase-space energy/momentum densities, perfect fluid, Maxwell) but not exhaustive.
4. Numerical relativity — outside `physlib`'s scope (OpenWave).

### Consequences

* **The SEP frontier is not blocked on "no GR dynamics".** It is blocked on residual 1 plus the
  genuinely new work of a Nordtvedt-type self-energy analysis. §12's WEP result stands unchanged.
* od7's scorecard row "Full GR dynamics: Formal 4/10" understates the current state; the honest
  description is *conditionally complete Cauchy architecture with one named analytic input*.
* The method lesson repeats §11.4's: "carrier check" cuts both ways — od7's pessimism, like my
  earlier optimism, came from not measuring the repo as it actually stood.

---

## 14. The target inventory is now a query, not a recollection

§2's "34 claims carry an `experimental_bound`" and §5's target list were assembled by hand-grepping —
the same retrieval-by-guesswork that §13 shows misled both od7 and this document.  The graph is now
directly queryable (`Physlib/Meta/ZilQuery.lean`):

    #zil_query relation = "experimental_bound" limit 40
    #zil_query status = "conditional-model|ansatz" limit 40
    #zil_query subject ~ "cauchy|development", decl ~ "tetrad|reversible"

Run on 2026-08-12: **39 `experimental_bound` edges** — the hand-built 34 plus exactly the five added
this session (`anomaly_agreement_iff_magic`, `bell_boost_fraction_bounds`,
`visibility_deficit_depends_only_on_differential`, `radarDistance_eq_entropicProperDistance_iff`,
`eotvos_null`).  Hand count and graph agree, and from here the graph is the source of truth: any
future revision of the target list should start from the query, not from memory.  301 edges carry an
honestly-conditional status (`conditional-model`/`ansatz`-family), retrievable in one query.

---

## 15. First leverage run: the ledger's top is tight

The query layer's first substantive use (2026-08-12): sweep the ledger's top premises for
cross-vocabulary derivations — the "81 primitive premises is an upper bound" concern of the
assumption ledger, now checkable by alternation search instead of exact token match.

| premise | reach | result |
|---|---|---|
| `doubled-boost-mode` | 12 | **genuinely primitive** — 10 edges, all `requires`; nothing establishes it |
| `caticha-cafaro-inference-mass` | 8 | **splits, and the physical half stays primitive** (below) |
| `log-k-rapidity-scaling` model | 7 | **genuinely primitive** — theorems prove properties *of* the scaled generator; none establishes that the generator *is* that scaling |
| `displacement-entropy` (the WEP postulate) | — | **no derivation under any wording** — the §12 WEP result is exactly one bare postulate deep, now verified by search rather than assumed |

**The near-miss, documented because it looks like a discharge and is not.**
`EntropicMassNewtonianDynamics.mass_variance_product` (`m·σ² = 1`) is a definitional restatement —
`inferenceMass σ₀ := (σ₀²)⁻¹` multiplied by `σ₀²`.  `CramerRaoInferenceMass.gaussian_cramerRao_inferenceMass`
is genuine analysis (a real Cramér–Rao bound: no estimator beats variance `σ²`, so Fisher information
`1/σ²` is the precision limit) — but it establishes only the **mathematical half**: Fisher
information = 1/variance.  The premise's content is the **physical half**: *inertial mass equals
that Fisher scale*.  Aliasing the premise to the Cramér–Rao claim would repeat §11.4's
carrier-substitution error.  The correct ledger reading: the premise's mathematical scaffolding is
established; the identification itself remains the postulate.

**Net under §10.2: zero calibrations eliminated — and that is the finding.**  For the top of the
ledger, 81 is tight, not an upper bound.  This is §10.6's "realistic case" arriving on schedule: the
honest output is the ledger itself, now verified at its head — *CAT/EPT reproduces this much physics
on these irreducible assumptions, and the top four have no hidden derivations under any vocabulary.*
