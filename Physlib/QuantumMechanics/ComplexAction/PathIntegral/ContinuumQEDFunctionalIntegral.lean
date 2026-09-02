/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction

/-!
# Continuum QED functional integral: cutoff-limit construction

This file gives the strongest construction that is honest at the current
physlib level.

It does **not** assert an unconditional construction of interacting QED4.
That is the hard constructive-QFT input: one must supply a renormalized cutoff
family whose correlation functionals converge for the intended observable
class.  Once that input is supplied, Lean constructs the continuum functional
integral, proves it is the unique cutoff limit, exposes partition/source/
normalised expectations, and transports cutoff Ward identities to the continuum.

In symbols, for cutoff models `M_n` and observable `O`,

`Z_QED[O] := lim_{n -> infinity} ∫ O(A,psi,psibar) exp(iS_n/hbar - S_{I,n}/hbar) dmu_n`.

The constructor below packages exactly the missing analytic obligations:

* cutoff Bochner integrability for admissible observables;
* existence of the renormalized continuum limit for those observables;
* gauge/Ward compatibility at each cutoff.

This turns the earlier open statement
`PathIntegral.QEDFunctionalIntegralConstruction.interactingContinuumLimitOpen` into a usable
API: any future proof of the cutoff convergence obligations immediately yields
the full continuum QED functional integral in this file.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral

open Filter Topology MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

/-! ## Cutoff data and analytic obligations -/

/-- A renormalized cutoff system for continuum QED.

`Field` is the continuum field-configuration carrier.  The structure does not
pretend that the interacting QED4 continuum measure has already been
constructed.  Instead it records the exact hypotheses needed to construct the
continuum functional integral from cutoff path-integral models. -/
structure QEDContinuumCutoffSystem (Field : Type*) [MeasurableSpace Field] where
  /-- UV/IR/lattice cutoff path-integral models. -/
  model : ℕ → MeasurePathIntegralModel Field
  /-- The class of observables/correlation insertions for which the continuum
  limit is asserted. -/
  admissible : (Field → ℂ) → Prop
  /-- The vacuum observable is admissible. -/
  admissible_one : admissible (fun _ => 1)
  /-- Every cutoff functional is a genuine Bochner integral on admissible
  observables. -/
  cutoff_integrable :
    ∀ {O : Field → ℂ}, admissible O →
      ∀ n : ℕ, Integrable (fun x => (model n).weight x * O x) (model n).μ
  /-- The renormalized continuum limit exists for each admissible observable.
  This is the nontrivial constructive-QFT obligation. -/
  cutoff_tendsto :
    ∀ {O : Field → ℂ}, admissible O →
      ∃ L : ℂ,
        Tendsto (fun n : ℕ => (model n).unnormalizedExpectation O) atTop (𝓝 L)
  /-- A representative gauge transformation on field configurations. -/
  gaugeTransform : Field → Field
  /-- Pullback by the gauge transformation preserves admissibility. -/
  admissible_gauge :
    ∀ {O : Field → ℂ}, admissible O → admissible (fun x => O (gaugeTransform x))
  /-- Cutoff Ward identity / gauge invariance for admissible observables. -/
  cutoff_gauge_invariant :
    ∀ {O : Field → ℂ}, admissible O →
      ∀ n : ℕ,
        (model n).unnormalizedExpectation (fun x => O (gaugeTransform x))
          = (model n).unnormalizedExpectation O

namespace QEDContinuumCutoffSystem

variable {Field : Type*} [MeasurableSpace Field]

/-- The `n`th cutoff functional `∫ O weight_n dmu_n`. -/
def cutoffFunctional (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (n : ℕ) : ℂ :=
  (S.model n).unnormalizedExpectation O

/-- The continuum QED functional integral as the selected renormalized cutoff
limit for an admissible observable. -/
def continuumFunctional
    (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (hO : S.admissible O) : ℂ :=
  Classical.choose (S.cutoff_tendsto hO)

/-- The constructed continuum functional is the cutoff limit. -/
lemma continuumFunctional_spec
    (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (hO : S.admissible O) :
    Tendsto (fun n : ℕ => S.cutoffFunctional O n) atTop
      (𝓝 (S.continuumFunctional O hO)) := by
  exact Classical.choose_spec (S.cutoff_tendsto hO)

/-- The continuum value is unique: any proposed value with the same cutoff
limit is equal to the constructed functional. -/
lemma continuumFunctional_eq_of_tendsto
    (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (hO : S.admissible O)
    (L : ℂ)
    (hL : Tendsto (fun n : ℕ => S.cutoffFunctional O n) atTop (𝓝 L)) :
    S.continuumFunctional O hO = L :=
  tendsto_nhds_unique (S.continuumFunctional_spec O hO) hL

/-- The continuum functional is an instance of the previously recorded open
interacting-continuum-limit statement.  The content is precisely the supplied
cutoff convergence proof. -/
lemma continuumFunctional_is_interactingContinuumLimitOpen
    (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (hO : S.admissible O) :
    interactingContinuumLimitOpen (fun n : ℕ => S.cutoffFunctional O n)
      (S.continuumFunctional O hO) :=
  S.continuumFunctional_spec O hO

/-- Cutoff Bochner integrability, restated for the named cutoff functional. -/
lemma cutoffFunctional_integrable
    (S : QEDContinuumCutoffSystem Field) (O : Field → ℂ) (hO : S.admissible O)
    (n : ℕ) :
    Integrable (fun x => (S.model n).weight x * O x) (S.model n).μ :=
  S.cutoff_integrable hO n

/-! ## Constructed continuum QED functional integral -/

/-- The full continuum QED functional integral generated by a cutoff system.

This is a genuine construction from the cutoff convergence obligations:
`amplitude O hO` is the unique continuum limit of the renormalized cutoff
functionals for `O`. -/
structure PathIntegral.ContinuumQEDFunctionalIntegral
    (S : QEDContinuumCutoffSystem Field) where
  /-- Continuum amplitude/correlation functional. -/
  amplitude : (O : Field → ℂ) → S.admissible O → ℂ
  /-- The amplitude is the renormalized cutoff limit. -/
  amplitude_tendsto :
    ∀ (O : Field → ℂ) (hO : S.admissible O),
      Tendsto (fun n : ℕ => S.cutoffFunctional O n) atTop (𝓝 (amplitude O hO))
  /-- Cutoff-level integrability remains available as part of the construction. -/
  cutoff_integrable :
    ∀ (O : Field → ℂ) (_hO : S.admissible O) (n : ℕ),
      Integrable (fun x => (S.model n).weight x * O x) (S.model n).μ

/-- Construct the continuum QED functional integral from a cutoff system. -/
def construct (S : QEDContinuumCutoffSystem Field) :
    PathIntegral.ContinuumQEDFunctionalIntegral S where
  amplitude := fun O hO => S.continuumFunctional O hO
  amplitude_tendsto := fun O hO => S.continuumFunctional_spec O hO
  cutoff_integrable := fun O hO n => S.cutoffFunctional_integrable O hO n

namespace PathIntegral.ContinuumQEDFunctionalIntegral

variable (S : QEDContinuumCutoffSystem Field)

/-- The constructed object agrees with the selected continuum functional. -/
@[simp] lemma construct_amplitude
    (O : Field → ℂ) (hO : S.admissible O) :
    (construct S).amplitude O hO = S.continuumFunctional O hO :=
  rfl

/-- Vacuum partition functional `Z = Z[1]`. -/
def partition (I : PathIntegral.ContinuumQEDFunctionalIntegral S) : ℂ :=
  I.amplitude (fun _ => 1) S.admissible_one

/-- Normalized continuum expectation `⟨O⟩ = Z[O]/Z[1]`. -/
def normalizedExpectation
    (I : PathIntegral.ContinuumQEDFunctionalIntegral S) (O : Field → ℂ) (hO : S.admissible O) : ℂ :=
  I.amplitude O hO / I.partition

/-- Source-coupled observable `exp(J)`. -/
def sourceObservable (J : Field → ℂ) : Field → ℂ :=
  fun x => Complex.exp (J x)

/-- Source-coupled continuum partition `Z[J]`. -/
def sourcePartition
    (I : PathIntegral.ContinuumQEDFunctionalIntegral S) (J : Field → ℂ)
    (hJ : S.admissible (sourceObservable J)) : ℂ :=
  I.amplitude (sourceObservable J) hJ

/-- Connected generating functional `W[J] = log Z[J]`. -/
def connectedGeneratingFunctional
    (I : PathIntegral.ContinuumQEDFunctionalIntegral S) (J : Field → ℂ)
    (hJ : S.admissible (sourceObservable J)) : ℂ :=
  Complex.log (sourcePartition S I J hJ)

/-- If the partition is nonzero, normalized expectation times partition
recovers the unnormalized continuum amplitude. -/
lemma normalizedExpectation_mul_partition
    (I : PathIntegral.ContinuumQEDFunctionalIntegral S) (O : Field → ℂ) (hO : S.admissible O)
    (hZ : I.partition ≠ 0) :
    normalizedExpectation S I O hO * partition S I = I.amplitude O hO := by
  unfold normalizedExpectation
  field_simp [hZ]

/-- Gauge/Ward identity survives the continuum limit. -/
lemma gauge_invariant
    (I : PathIntegral.ContinuumQEDFunctionalIntegral S) (O : Field → ℂ) (hO : S.admissible O) :
    I.amplitude (fun x => O (S.gaugeTransform x)) (S.admissible_gauge hO)
      = I.amplitude O hO := by
  have hLimitToO :
      Tendsto
        (fun n : ℕ => S.cutoffFunctional (fun x => O (S.gaugeTransform x)) n)
        atTop (𝓝 (I.amplitude O hO)) := by
    have hseq :
        (fun n : ℕ => S.cutoffFunctional (fun x => O (S.gaugeTransform x)) n)
          = fun n : ℕ => S.cutoffFunctional O n := by
      funext n
      exact S.cutoff_gauge_invariant hO n
    simpa [hseq] using I.amplitude_tendsto O hO
  exact tendsto_nhds_unique
    (I.amplitude_tendsto (fun x => O (S.gaugeTransform x)) (S.admissible_gauge hO))
    hLimitToO

/-- The constructed continuum functional is independent of the particular
limit witness: any other functional with the same cutoff-limit property agrees
on every admissible observable. -/
lemma ext_of_same_cutoff_limits
    (I J : PathIntegral.ContinuumQEDFunctionalIntegral S)
    (O : Field → ℂ) (hO : S.admissible O) :
    I.amplitude O hO = J.amplitude O hO :=
  tendsto_nhds_unique (I.amplitude_tendsto O hO) (J.amplitude_tendsto O hO)

end PathIntegral.ContinuumQEDFunctionalIntegral

/-! ## Constant cutoff sanity check -/

/-- A constant cutoff system: useful for checking that the continuum API
reduces to an already-constructed regularized path-integral model.

This is not the full interacting QED4 construction; it is the exact embedding
of any existing regularized model into the continuum-cutoff API. -/
def constantCutoffSystem
    (m : MeasurePathIntegralModel Field)
    (admissible : (Field → ℂ) → Prop)
    (admissible_one : admissible (fun _ => 1))
    (cutoff_integrable :
      ∀ {O : Field → ℂ}, admissible O →
        Integrable (fun x => m.weight x * O x) m.μ)
    (gaugeTransform : Field → Field)
    (admissible_gauge :
      ∀ {O : Field → ℂ}, admissible O → admissible (fun x => O (gaugeTransform x)))
    (cutoff_gauge_invariant :
      ∀ {O : Field → ℂ}, admissible O →
        m.unnormalizedExpectation (fun x => O (gaugeTransform x))
          = m.unnormalizedExpectation O) :
    QEDContinuumCutoffSystem Field where
  model := fun _ => m
  admissible := admissible
  admissible_one := admissible_one
  cutoff_integrable := fun hO _ => cutoff_integrable hO
  cutoff_tendsto := fun _hO =>
    ⟨m.unnormalizedExpectation _, tendsto_const_nhds⟩
  gaugeTransform := gaugeTransform
  admissible_gauge := admissible_gauge
  cutoff_gauge_invariant := fun hO _ => cutoff_gauge_invariant hO

/-- For a constant cutoff system, the constructed continuum functional is the
already-existing regularized path-integral expectation. -/
lemma constantCutoffSystem_continuumFunctional_eq
    (m : MeasurePathIntegralModel Field)
    (admissible : (Field → ℂ) → Prop)
    (admissible_one : admissible (fun _ => 1))
    (cutoff_integrable :
      ∀ {O : Field → ℂ}, admissible O →
        Integrable (fun x => m.weight x * O x) m.μ)
    (gaugeTransform : Field → Field)
    (admissible_gauge :
      ∀ {O : Field → ℂ}, admissible O → admissible (fun x => O (gaugeTransform x)))
    (cutoff_gauge_invariant :
      ∀ {O : Field → ℂ}, admissible O →
        m.unnormalizedExpectation (fun x => O (gaugeTransform x))
          = m.unnormalizedExpectation O)
    (O : Field → ℂ) (hO : admissible O) :
    (constantCutoffSystem m admissible admissible_one cutoff_integrable gaugeTransform
        admissible_gauge cutoff_gauge_invariant).continuumFunctional O hO
      = m.unnormalizedExpectation O := by
  apply continuumFunctional_eq_of_tendsto
  exact tendsto_const_nhds

end QEDContinuumCutoffSystem

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.ContinuumQEDFunctionalIntegral

end

end
