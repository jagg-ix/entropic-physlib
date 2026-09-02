/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance

meta import Zil

/-!
# The action-plane metric has no free parameter, and the connection cannot supply the one it kills

Every CAT/EPT target audited so far has failed the same way: the theorem is exact and the physics
enters through a calibration nothing measures (`analysis/empirical-discrimination-plan.md` §9).  The
Nagao–Nielsen action-plane geometry is the opposite shape, and this module makes the difference
explicit by counting parameters.

**The count.**  A general real symmetric quadratic form on the action plane
`q = S_R/ħ + i S_I/ħ` has three coefficients,
`nnSymmetricForm a b c q = a·(Re q)² + 2b·(Re q)(Im q) + c·(Im q)²`.

* Boost invariance kills two of them: `nnSymmetricForm_invariant_iff` forces `b = 0` and `c = −a`.
* Unit timelike normalization kills the third: `nnLorentzForm_unique_normalized` then gives
  `nnSymmetricForm a b c = nnLorentzForm` exactly.

So the metric on the action plane is **forced**, not chosen — three free parameters down to zero.
That is a calibration *eliminated* in the sense §10.2 asks for, and it is a uniqueness theorem
rather than an identity assumed under a hypothesis.

**Why the third step is not redundant.**  One might expect the connection to fix the remaining
scale, making the normalization idle.  It cannot:
`Curvature.MetricIntervalIsometryInvariance.weylRescale_connection_invariant_interval_scales` proves
a constant Weyl rescaling `g ↦ λg` leaves the Levi-Civita connection **invariant** while scaling the
interval by `λ`.  The connection is blind to exactly the one parameter that survives boost
invariance.  §B records this complementarity: the two conditions are independent, and together
they exhaust the freedom.

**The coordinate dictionary.**  The invariance is under `nnActionBoost η`, built from `lorentzBoost η`
on `(Re q, Im q)` — so the CAT/EPT action plane, the Lorentz boost and the hyperbolic rapidity are
one structure read three ways.  The entanglement reading is the third: `K = coth η`
(`MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber`) reparametrizes the same `η` on
`η > 0`.  §C records that the rigidity is a statement about the *group*, so it is untouched by which
coordinate names the group element — a reparametrization cannot restore a parameter that invariance
removed.

Scope.  This is the **flat** action plane; the spine says so explicitly, and it is not a replacement
for the repository's curved-spacetime connection.  What carries to curved spacetime is local:
`ComptonClock.WalkEquivalenceCurvedChain` supplies the local inertial frame in which this geometry is
the applicable one, and nothing here derives a curved-space extension.  The parameter count is exact;
the claim that the action plane is the right carrier for CAT/EPT is not established here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneMetricRigidity

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

/-! ### §A — three parameters to zero -/

/-- **Boost invariance alone leaves exactly one parameter.**  Of the three coefficients of a general
symmetric form on the action plane, invariance under the hyperbolic action boost forces the mixed
term to vanish and the diagonal entries to be opposite, leaving the overall scale `a` free.

Stated as the surviving family: every boost-invariant form is `a · nnLorentzForm`. -/
theorem boostInvariant_family {a b c : ℝ}
    (hinv : ∀ η q, nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q) :
    ∀ q, nnSymmetricForm a b c q = a * nnLorentzForm q := by
  obtain ⟨hb, hc⟩ := nnSymmetricForm_invariant_iff.mp hinv
  intro q
  unfold nnSymmetricForm nnLorentzForm
  rw [hb, hc]
  ring

/-- **Normalization removes the last parameter.**  Adding the unit timelike condition to boost
invariance leaves no freedom at all: the form *is* `nnLorentzForm`.  Three coefficients, two killed
by the symmetry and one by the normalization — the action-plane metric is forced.

This is the shape the audit of §9 found missing everywhere else: a uniqueness theorem, not an
identity holding under an unmeasured hypothesis. -/
theorem actionPlaneMetric_no_free_parameter {a b c : ℝ}
    (hinv : ∀ η q, nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q)
    (hnorm : nnSymmetricForm a b c 1 = 1) :
    ∀ q, nnSymmetricForm a b c q = metricInterval nnMinkowskiMetric (nnActionVector q) := by
  intro q
  rw [nnLorentzForm_unique_normalized hinv hnorm q, nnLorentzForm_eq_metricInterval q]

/-! ### §B — the connection cannot supply the parameter the normalization kills -/

/-- **The two conditions are independent, and together exhaust the freedom.**  A constant Weyl
rescaling `g ↦ λg` leaves the Levi-Civita connection unchanged while scaling the interval by `λ`, so
the connection is blind to precisely the overall scale that survives boost invariance (§A).  The
normalization is therefore doing real work: no amount of connection data could have fixed it.

The two clauses are the two halves of the complementarity — the connection sees nothing of `λ`, and
the interval sees exactly `λ`. -/
theorem scale_invisible_to_connection {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    christoffelFromMetric (lam⁻¹ • gInv) (fun κ => lam • dg κ) = christoffelFromMetric gInv dg
      ∧ metricInterval (lam • g) v = lam * metricInterval g v :=
  weylRescale_connection_invariant_interval_scales gInv dg hlam g v

/-! ### §C — the dictionary: one structure, three coordinate readings -/

/-- **The rigidity is a statement about the group, not the coordinate.**  The invariance quantifies
over *every* boost parameter, so any relabelling of the group — the Lorentz rapidity `η`, the
hyperbolic reading, or the entanglement reading `K = coth η` — quantifies over the same set and
yields the same conclusion.

Concretely: if the form is invariant under the boosts named by a surjection `r` onto the rapidities,
it is invariant, hence forced.  A reparametrization cannot restore a parameter that invariance
removed, which is why the CAT/EPT, Lorentz and hyperbolic presentations share one rigidity. -/
theorem rigidity_reparametrization_stable {a b c : ℝ} {ι : Type*} (r : ι → ℝ)
    (hsurj : Function.Surjective r)
    (hinv : ∀ (i : ι) (q : ℂ),
      nnSymmetricForm a b c (nnActionBoost (r i) q) = nnSymmetricForm a b c q)
    (hnorm : nnSymmetricForm a b c 1 = 1) :
    ∀ q, nnSymmetricForm a b c q = nnLorentzForm q := by
  refine nnLorentzForm_unique_normalized (fun η q => ?_) hnorm
  obtain ⟨i, rfl⟩ := hsurj η
  exact hinv i q

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneMetricRigidity.actionPlaneMetric_no_free_parameter where
  formalizes @ "claim:boost-invariance-plus-unit-timelike-normalization-leaves-the-nagao-nielsen-action-plane-metric-with-no-free-parameter-so-the-metric-is-forced-rather-than-calibrated",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnSymmetricForm_invariant_iff",
  caveat @ "this-eliminates-a-choice-rather-than-assuming-one-but-it-is-a-statement-about-the-flat-action-plane-only-and-does-not-establish-that-the-action-plane-is-the-right-carrier-for-cat-ept"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneMetricRigidity.scale_invisible_to_connection where
  formalizes @ "claim:the-levi-civita-connection-is-blind-to-the-overall-conformal-scale-that-survives-boost-invariance-so-the-normalization-condition-is-independent-and-not-redundant",
  epistemic_status @ "consistency-identity",
  requires @ "claim:boost-invariance-plus-unit-timelike-normalization-leaves-the-nagao-nielsen-action-plane-metric-with-no-free-parameter-so-the-metric-is-forced-rather-than-calibrated",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.weylRescale_connection_invariant_interval_scales",
  caveat @ "the-complementarity-is-exact-for-a-constant-weyl-rescaling-a-position-dependent-conformal-factor-is-not-covered-here"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneMetricRigidity

end
