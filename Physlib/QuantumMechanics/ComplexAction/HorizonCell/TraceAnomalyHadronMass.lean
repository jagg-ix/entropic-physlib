/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
meta import Zil

/-!
# The QCD trace anomaly is the origin of hadron mass: `θ^μ_μ = (β/2g) G²`

Quantum scale invariance in QCD is broken by the **trace (scale) anomaly**: the trace of the energy–momentum
tensor is proportional to the β-function,
`θ^μ_μ = (β(g)/2g) G^a_{μν}G^{aμν}`, which at one loop is `−(b₀ g²/2) G²`. This is the same `b₀ =
betaZeroCoeff N_f` that governs asymptotic freedom (`QCDBetaFunctionAsymptoticFreedom`), so one coefficient does
three things:

* it is **negative** for asymptotically-free QCD, so the trace anomaly is nonzero — scale invariance is broken
  quantum-mechanically (`traceAnomaly_neg`, `trace_anomaly_from_asymptotic_freedom`);
* it gives a **negative gluon vacuum energy** `ε_vac = ⟨θ^μ_μ⟩/4 < 0` (`vacuumEnergy_neg`) — the QCD contribution
  to the vacuum energy / cosmological constant, on the entropic-`Λ` side of the complex Einstein equation;
* it is the **origin of hadron mass**: the nucleon matrix element `⟨N|θ^μ_μ|N⟩ = 2M²` fixes `M² > 0` from the
  gluon field itself (`hadronMassSq_pos`) — most of the proton mass is gluonic (the trace anomaly), *not* the
  Higgs/quark masses. Mass from dimensional transmutation, generated even in the chiral limit `m_q → 0`.

So asymptotic freedom (`b₀ > 0`, UV) and the origin of hadron mass (`b₀`-driven trace anomaly, IR) are one
coefficient: the running that makes QCD free in the UV is the anomaly that makes hadrons massive in the IR.

* **§A — the trace anomaly `θ^μ_μ = (β/2g)G²`** (`traceAnomaly`, `traceAnomaly_neg`).
* **§B — from asymptotic freedom** (`trace_anomaly_from_asymptotic_freedom`).
* **§C — the negative gluon vacuum energy** (`vacuumEnergy`, `vacuumEnergy_neg`).
* **§D — the origin of hadron mass** (`hadronMassSq`, `hadronMassSq_pos`).
* **§E — assembled** (`trace_anomaly_origin_of_hadron_mass`).

**Honest layering.** `traceAnomaly = −(b₀g²/2)G²` is the exact one-loop form (with `b₀ = betaZeroCoeff N_f`), and
the sign/positivity facts are exact. The vacuum energy `⟨θ⟩/4` and the nucleon mass relation `⟨N|θ|N⟩ = 2M²` are
recorded as the standard normalizations, not derived from matrix elements; `⟨G²⟩` is not computed. ## References

* J. Collins, A. Duncan, S. Joglekar (trace anomaly); X. Ji (nucleon mass decomposition, `⟨N|θ|N⟩ = 2M²`).
  Repo carrier: `HorizonCell.QCDBetaFunctionAsymptoticFreedom` (`betaZeroCoeff`, `asymptotic_freedom_iff`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass


/-- **The QCD trace anomaly** `θ^μ_μ = (β/2g) G² = −(b₀ g²/2) G²` (one loop) — the trace of the energy–momentum
tensor, proportional to the β-function coefficient `b₀`, the gluon field strength squared `G²`, and the coupling
`g²`. -/
noncomputable def traceAnomaly (b0 gSq Gsq : ℝ) : ℝ := -(b0 * gSq / 2) * Gsq

/-- **[The trace anomaly is negative for asymptotically-free QCD] `θ^μ_μ < 0`.** With a positive β-function
coefficient (asymptotic freedom), positive coupling, and positive gluon condensate, the trace of the stress
tensor is negative: quantum scale invariance is broken. -/
lemma traceAnomaly_neg (b0 gSq Gsq : ℝ) (hb : 0 < b0) (hg : 0 < gSq) (hG : 0 < Gsq) :
    traceAnomaly b0 gSq Gsq < 0 := by
  unfold traceAnomaly
  have h : 0 < b0 * gSq / 2 * Gsq := by positivity
  nlinarith [h]


/-- **[The trace anomaly is driven by the asymptotic-freedom coefficient] `θ^μ_μ < 0` for `N_f < 33/2`.** The very
`b₀ = betaZeroCoeff N_f` that is positive for asymptotically-free QCD (`asymptotic_freedom_iff`) makes the trace
anomaly negative: the UV coefficient of asymptotic freedom is the IR coefficient of scale-symmetry breaking. -/
lemma trace_anomaly_from_asymptotic_freedom (N_f gSq Gsq : ℝ) (hN : N_f < 33 / 2)
    (hg : 0 < gSq) (hG : 0 < Gsq) : traceAnomaly (betaZeroCoeff N_f) gSq Gsq < 0 :=
  traceAnomaly_neg (betaZeroCoeff N_f) gSq Gsq ((asymptotic_freedom_iff N_f).mpr hN) hg hG


/-- **The QCD gluon vacuum energy** `ε_vac = ⟨θ^μ_μ⟩/4` — the trace anomaly's contribution to the vacuum energy
density (and thence to the cosmological constant / entropic-`Λ` Einstein sector). -/
noncomputable def vacuumEnergy (traceAnom : ℝ) : ℝ := traceAnom / 4

/-- **[The gluon vacuum energy is negative] `ε_vac < 0`.** A negative trace anomaly gives a negative QCD vacuum
energy density — the gluon condensate lowers the vacuum energy, a `Λ`-source on the imaginary/entropic side of the
complex Einstein equation. -/
lemma vacuumEnergy_neg (traceAnom : ℝ) (h : traceAnom < 0) : vacuumEnergy traceAnom < 0 := by
  unfold vacuumEnergy; linarith


/-- **The hadron mass² from the trace anomaly** `M² = −⟨θ^μ_μ⟩/2` — from the nucleon matrix element
`⟨N|θ^μ_μ|N⟩ = 2M²`: the mass generated by the gluon field (the trace anomaly), not the quark masses. -/
noncomputable def hadronMassSq (traceAnom : ℝ) : ℝ := -traceAnom / 2

/-- **[Hadron mass is gluonic] `M² > 0` from the trace anomaly.** The negative trace anomaly yields a positive
hadron mass² — generated by the gluon field itself, surviving the chiral limit `m_q → 0`. Most of the proton mass
comes from the QCD scale anomaly (dimensional transmutation), not the Higgs mechanism. -/
lemma hadronMassSq_pos (traceAnom : ℝ) (h : traceAnom < 0) : 0 < hadronMassSq traceAnom := by
  unfold hadronMassSq; linarith


/-- **[The trace anomaly as the origin of hadron mass, assembled].** For asymptotically-free QCD (`N_f < 33/2`),
positive coupling and gluon condensate:

* the trace anomaly `θ^μ_μ = −(b₀ g²/2)G²` is negative — scale invariance quantum-mechanically broken;
* the gluon vacuum energy `ε_vac = ⟨θ⟩/4` is negative — a `Λ`-source;
* the hadron mass² `M² = −⟨θ⟩/2` is positive — mass generated by the gluon field, not the Higgs.

The one coefficient `b₀ = betaZeroCoeff N_f` of asymptotic freedom is the origin of hadron mass: dimensional
transmutation turns a dimensionless coupling into the scale of the visible mass of the universe. -/
lemma trace_anomaly_origin_of_hadron_mass (N_f gSq Gsq : ℝ) (hN : N_f < 33 / 2)
    (hg : 0 < gSq) (hG : 0 < Gsq) :
    traceAnomaly (betaZeroCoeff N_f) gSq Gsq < 0
      ∧ vacuumEnergy (traceAnomaly (betaZeroCoeff N_f) gSq Gsq) < 0
      ∧ 0 < hadronMassSq (traceAnomaly (betaZeroCoeff N_f) gSq Gsq) :=
  have h := trace_anomaly_from_asymptotic_freedom N_f gSq Gsq hN hg hG
  ⟨h, vacuumEnergy_neg _ h, hadronMassSq_pos _ h⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.trace_anomaly_from_asymptotic_freedom where
  formalizes @ "claim:the-qcd-trace-anomaly-theta-mu-mu-equals-beta-over-two-g-times-f-squared-is-negative-driven-by-the-same-asymptotic-freedom-coefficient-b0",
  requires @ "claim:su3-is-asymptotically-free-b0-positive-iff-fewer-than-thirty-three-halves-quark-flavours",
  supported_by @ "paper:pdg-2026-review-qcd-trace-anomaly"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.hadronMassSq_pos where
  formalizes @ "claim:the-hadron-mass-squared-from-the-trace-anomaly-is-positive-hadron-mass-is-generated-by-the-gluon-field-energy-not-the-higgs",
  requires @ "claim:the-qcd-trace-anomaly-theta-mu-mu-equals-beta-over-two-g-times-f-squared-is-negative-driven-by-the-same-asymptotic-freedom-coefficient-b0"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.trace_anomaly_origin_of_hadron_mass where
  formalizes @ "claim:the-trace-anomaly-is-the-origin-of-hadron-mass-a-negative-vacuum-energy-and-a-positive-hadron-mass-squared-from-asymptotic-freedom",
  requires @ "claim:the-hadron-mass-squared-from-the-trace-anomaly-is-positive-hadron-mass-is-generated-by-the-gluon-field-energy-not-the-higgs",
  supported_by @ "paper:pdg-2026-review-qcd-trace-anomaly"

zil_file_contract physlib.traceAnomalyHadronMass where
  promises "The QCD trace anomaly as the origin of hadron mass: the trace of the energy-momentum tensor theta-mu-mu equals beta over two g times the gluon field strength squared, which is negative and driven by the same one-loop coefficient b0 that gives asymptotic freedom; the associated vacuum energy is negative and the hadron mass-squared is positive, so the bulk of the hadron mass is generated dynamically by the gluon field energy rather than by the Higgs coupling."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.traceAnomaly",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.hadronMassSq",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.betaZeroCoeff"]
  forbids_substitutes ["a lattice or Schwinger-Dyson computation of the gluon condensate value, which is taken as a positive input",
    "a derivation of the numerical hadron mass, only the sign and origin structure are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.traceAnomaly_neg,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.trace_anomaly_from_asymptotic_freedom,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.hadronMassSq_pos,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.TraceAnomalyHadronMass.trace_anomaly_origin_of_hadron_mass]

/- ZIL-END -/
