# The gold corpus — a reviewed tier above the raw formalization graph

**Date**: 2026-08-29.  **Why**: the full-root graph carries ~2,806 `formalizes` attachments of
which **850 were unsupported** (no `supported_by` edge; reduced by the factual
derivational-support pass of `analysis/unsupported-claims-worklist.md`).  The publication review is right that
the program must not imply all of these are publication-ready.  This document defines the
**gold corpus**: the subset of formalized claims that clears every *machine-checkable* bar the
repository has, so that the remaining gap to "publication-ready" is exactly one human step —
the statement-level and bibliographic verification that `AI-POLICY.md` reserves to the human
author and that no build can supply.

## Membership criterion (machine-checkable part)

A declaration `D` is in the **machine-vetted corpus** iff all of:

1. **Kernel-checked and axiom-clean**: `D` appears in a `#physlib_axiom_clean_all` list of a
   rooted `Physlib/Meta/*Audit*` module (the audit fails the build if `D` acquires an axiom,
   `sorry`, or a native-decide dependency).
2. **Non-vacuity where the audit provides it**: the audit module's inhabitation/`#check`
   witnesses elaborate (audits state these next to the axiom-clean lists).
3. **Attached and statused**: `D` carries a `formalizes` edge and an in-vocabulary
   `epistemic_status` (the conformance suite enforces the vocabulary).
4. **No undisclosed buried conditionality**: `D` is not a *proof-level* finding of the
   weakest-link auditor with a missing `caveat` disclosure
   (`analysis/buried-conditionality-triage.md` — currently the entropic-gravity quartet and
   two singletons fail this and are excluded until caveats land).

Membership is **not** a claim of scientific novelty or of correct citation — criterion 5 is
human:

5. **Human statement-level sign-off**: a domain expert has read the Lean statement against the
   intended science and verified the bibliography (`AI-POLICY.md`).  The machine-vetted corpus
   is the *queue* for this review, not its output.

## Current machine-vetted inventory (2026-08-29)

* **127 audit modules**, 122 with `#physlib_axiom_clean_all` lists, certifying
  **2,898 declaration entries** (the spine audit alone carries 1,869; the median focused audit
  certifies ~15–40).
* The two publication case studies are fully inside the machine-vetted tier:
  * *Causal reconstruction*: `CausalPreorderAudit`, `CausalConeLightRayPreservationAudit`,
    `CausalConeLorentzReconstructionAudit`, `CausalConeAlexandrovZeemanAudit` (19 decls),
    `CausalAutomorphismConformalInvariantsAudit`, `ComptonClockMalamentProperTime*Audit` —
    the affine-stage boundary is stated in the contract of
    `CausalConeAlexandrovZeeman.lean`.
  * *Entropy production / irreversibility*: `ChannelEntropyProductionAudit` (unitary-CPTP
    entropy preservation, mixing counterexample, relative-entropy contraction) and the strict
    finite-Markov results of `FiniteMarkovEntropyProductionStrict`.
* The corpus explicitly **excludes** (criterion 4, pending caveat edges): the
  `TransverseMomentumEffectiveMass` quartet and
  `metricStationary_iff_residualCoordinate_zero`, `LightSheet.bekensteinRate_nonpos`,
  `LightSheet.entropyFlux_eq_bekenstein_deficit`.

## How to use it

For a publication draft: draw *positive* claims only from the machine-vetted corpus, then run
criterion 5 on exactly the drafted subset — the review queue is the draft's citation list, not
850 attachments.  The unsupported-attachment count (850) is a *coverage* metric for the graph,
not a defect list: an unsupported attachment is a formalization without literature anchoring,
which is fine for infrastructure lemmas and disqualifying for headline claims.

## Regeneration

The inventory is one command over the audit modules:
`grep -A40 '#physlib_axiom_clean_all' Physlib/Meta/*Audit*.lean` (or the parser in this
document's provenance scratch); the exclusion list tracks
`analysis/buried-conditionality-triage.md`.  Re-run both after any audit or attachment change.
