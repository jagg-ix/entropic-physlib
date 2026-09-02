/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem
public import Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree
meta import Zil

/-!
# Linking Sorkin's Regge evolution to the time-free entropic clock

The Regge initial-value/evolution arc (`ReggeInitialValueProblem`) carries an entropic weight
`exp(−S_I/ℏ)` whose imaginary Regge action `S_I` grows along the evolution. The repository's time-free
second law (`Thermodynamics.SecondLaw`) reads entropic proper time straight off the entropy produced,
`entropicTimeOf S_I ℏ = S_I/ℏ`. This module identifies the two: the Regge couche's entropic time *is*
`entropicTimeOf` of its imaginary Regge action, and the couche path weight is `exp(−τ_ent)`.

* `coucheEntropicTime` — the couche's entropic time, `entropicTimeOf` of the imaginary Regge action.
* `couche_entropicWeight_eq_exp_neg_entropicTime` — the couche path weight is `exp(−τ_ent)` (reusing
  `reggeAction_complexActionWeight_norm`).
* `coucheEntropicTime_nonneg` / `coucheEntropicTime_mono` / `couche_reversible_iff` — the couche
  entropic time obeys the time-free second law: non-negative for a non-negative entropic action,
  monotone in it, and zero exactly in the reversible (real-defect) limit — reusing
  `entropicTimeOf_nonneg`, `entropicTimeOf_le_iff`, `entropicTimeOf_eq_zero_iff`.

So the discrete Regge evolution's arrow of time (`couche_entropicWeight_antitone`) is exactly the
time-free entropic clock of `Thermodynamics.SecondLaw`, applied to Sorkin's complex Regge action.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`]. Reuses `LeviCivita.ReggeInitialValueProblem` /
  `LeviCivita.ComplexReggeAction` (`reggeAction_complexActionWeight_norm`, `sorkinReggeAction`) and
  `Thermodynamics.SecondLaw` (`entropicTimeOf`, `secondLaw_timeFree`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency
open Physlib.Thermodynamics.SecondLaw

/-- **The couche's entropic time** — `entropicTimeOf` (`= S_I/ℏ`) of the imaginary (entropic) Regge
action of the couche. -/
noncomputable def coucheEntropicTime {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) : ℝ :=
  entropicTimeOf (sorkinReggeAction area (fun b => (defect b).im)) ℏ

/-- **The couche path weight is `exp(−τ_ent)`**: the entropic modulus of Sorkin's complex Regge weight
is `exp` of minus the couche entropic time (reusing `reggeAction_complexActionWeight_norm`). -/
lemma couche_entropicWeight_eq_exp_neg_entropicTime {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) :
    ‖complexActionWeight (complexReggeAction area defect).re
        (complexReggeAction area defect).im ℏ‖
      = Real.exp (- coucheEntropicTime area defect ℏ) := by
  rw [reggeAction_complexActionWeight_norm]
  rfl

/-- **The couche entropic time is non-negative** for a non-negative entropic Regge action — the arrow
of the time-free second law (reusing `entropicTimeOf_nonneg`). -/
lemma coucheEntropicTime_nonneg {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (hS : 0 ≤ sorkinReggeAction area (fun b => (defect b).im)) :
    0 ≤ coucheEntropicTime area defect ℏ :=
  entropicTimeOf_nonneg hS hℏ

/-- **The couche entropic time is monotone in the entropic Regge action**: more entropic action along
the evolution ⟹ more entropic time (reusing `entropicTimeOf_le_iff`) — the same arrow as the weight
antitonicity `couche_entropicWeight_antitone`. -/
lemma coucheEntropicTime_mono {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect₁ defect₂ : Bone → ℂ) (ℏ : ℝ) (hℏ : 0 < ℏ)
    (h : sorkinReggeAction area (fun b => (defect₁ b).im)
        ≤ sorkinReggeAction area (fun b => (defect₂ b).im)) :
    coucheEntropicTime area defect₁ ℏ ≤ coucheEntropicTime area defect₂ ℏ :=
  (entropicTimeOf_le_iff hℏ).mpr h

/-- **Reversibility**: the couche entropic time vanishes exactly when the entropic Regge action does —
the real-defect (classical, no entropic damping) limit (reusing `entropicTimeOf_eq_zero_iff`). -/
lemma couche_reversible_iff {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) (hℏ : 0 < ℏ) :
    coucheEntropicTime area defect ℏ = 0
      ↔ sorkinReggeAction area (fun b => (defect b).im) = 0 :=
  entropicTimeOf_eq_zero_iff hℏ

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.couche_entropicWeight_eq_exp_neg_entropicTime where
  formalizes @ "claim:the-regge-couche-path-weight-equals-exp-minus-the-couche-entropic-time-which-is-the-time-free-second-laws-entropic-time-of-the-imaginary-regge-action",
  supported_by @ "object:Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime_nonneg where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeInitialValueProblem.couche_entropicWeight_antitone",
  formalizes @ "claim:the-couche-entropic-time-is-non-negative-for-a-non-negative-entropic-regge-action-the-arrow-of-the-time-free-second-law"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime_mono where
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.entropicTimeOf_eq_zero_iff",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.entropicTimeOf_le_iff",
  formalizes @ "claim:the-couche-entropic-time-is-monotone-in-the-entropic-regge-action-more-entropic-action-along-the-evolution-means-more-entropic-time",
  requires @ "claim:the-couche-entropic-time-is-non-negative-for-a-non-negative-entropic-regge-action-the-arrow-of-the-time-free-second-law"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.couche_reversible_iff where
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.entropicTimeOf_eq_zero_iff",
  formalizes @ "claim:the-couche-entropic-time-vanishes-exactly-when-the-entropic-regge-action-does-the-real-defect-classical-no-damping-reversible-limit"

zil_file_contract physlib.reggeEntropicTimeLink where
  promises "Identifies Sorkin's Regge evolution with the repository's time-free entropic clock. The Regge couche carries an entropic weight exp(-S_I/hbar) whose imaginary Regge action S_I grows along the evolution; the time-free second law reads entropic proper time straight off the entropy produced, entropicTimeOf S_I hbar = S_I/hbar. The couche entropic time is entropicTimeOf of the imaginary Regge action, so the couche path weight is exactly exp(-tau_ent) (couche_entropicWeight_eq_exp_neg_entropicTime). This entropic time is non-negative (coucheEntropicTime_nonneg) and monotone in the entropic Regge action -- the arrow of time (coucheEntropicTime_mono) -- and vanishes exactly in the real-defect classical limit (couche_reversible_iff). Sorkin's discrete gravitational evolution is thus driven by the entropic clock."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction.complexReggeAction"]
  forbids_substitutes ["the time-free second law's construction of entropic proper time from entropy production, which is the cited thermodynamic carrier",
    "any claim that the Regge evolution is dynamically driven, only the identification of its couche weight with the entropic clock is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.couche_entropicWeight_eq_exp_neg_entropicTime,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime_nonneg,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.coucheEntropicTime_mono,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeEntropicTimeLink.couche_reversible_iff]

/- ZIL-END -/
