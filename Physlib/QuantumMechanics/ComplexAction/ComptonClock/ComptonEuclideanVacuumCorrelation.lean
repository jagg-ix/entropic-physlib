/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance

meta import Zil

/-!
# A spectral derivation of the Compton exponential correlation profile

This file isolates a setting in which the exact exponential profile used by the Compton-clock
arc is derived from a specified state, field insertion, and Euclidean Hamiltonian evolution.
The carrier is the vacuum--one-particle sector of one free massive scalar mode:

* `freeScalarVacuum` is the vacuum basis vector;
* `truncatedScalarField` exchanges the vacuum and one-particle sectors;
* `euclideanGapEvolution` fixes the vacuum and damps the one-particle sector by
  `exp (-E r / (hbar c))`;
* the vacuum two-point function is the vacuum matrix element of
  `field * exp (-r H/(hbar c)) * field`.

For the relativistic one-particle gap `E = m c^2`, the two-point function is exactly
`exp (-r/lambda_C)`. This is genuine spectral content of this explicit finite-sector model,
not a consequence of Reeh--Schlieder and not a derivation of an AQFT Bell-concurrence law.
The latter requires local observable algebras and the Summers mass-gap bound, which are kept
outside the exact equality proved here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonEuclideanVacuumCorrelation

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-! # A. The specified vacuum, field insertion, and Euclidean evolution -/

/-- The vacuum--one-particle state space of one truncated scalar mode. -/
abbrev TruncatedScalarState : Type := Fin 2 → ℂ

/-- The vacuum basis vector `|0>` in the vacuum--one-particle sector. -/
def freeScalarVacuum : TruncatedScalarState := fun i => if i = 0 then 1 else 0

/-- The truncated scalar field insertion, exchanging `|0>` and `|1>`.

It is the restriction of the oscillator field's creation-plus-annihilation action to the
vacuum--one-particle sector. -/
def truncatedScalarField (ψ : TruncatedScalarState) : TruncatedScalarState := fun i =>
  if i = 0 then ψ 1 else ψ 0

/-- Euclidean evolution for a two-sector Hamiltonian with vacuum energy zero and
one-particle gap `E`: `|0>` is fixed and `|1>` is multiplied by `exp (-E r/(hbar c))`. -/
noncomputable def euclideanGapEvolution (E c ħ r : ℝ)
    (ψ : TruncatedScalarState) : TruncatedScalarState := fun i =>
  if i = 0 then ψ 0 else ((Real.exp (-(E * r / (ħ * c))) : ℝ) : ℂ) * ψ 1

/-- Vacuum expectation of a state produced by an operator word, `⟨0|ψ⟩`. -/
def freeScalarVacuumExpectation (ψ : TruncatedScalarState) : ℂ := ψ 0

/-- The Euclidean vacuum two-point function
`⟨0| field exp (-r H/(hbar c)) field |0⟩` for the specified scalar mode. -/
noncomputable def euclideanVacuumTwoPoint (E c ħ r : ℝ) : ℂ :=
  freeScalarVacuumExpectation
    (truncatedScalarField
      (euclideanGapEvolution E c ħ r (truncatedScalarField freeScalarVacuum)))

/-! # B. Spectral evaluation and the Compton scale -/

/-- The specified vacuum matrix element is exactly the exponential of the one-particle gap. -/
lemma euclideanVacuumTwoPoint_eq (E c ħ r : ℝ) :
    euclideanVacuumTwoPoint E c ħ r =
      ((Real.exp (-(E * r / (ħ * c))) : ℝ) : ℂ) := by
  simp [euclideanVacuumTwoPoint, freeScalarVacuumExpectation, truncatedScalarField,
    euclideanGapEvolution, freeScalarVacuum]

/-- The free scalar mode's Compton-gap two-point function. -/
noncomputable def comptonVacuumTwoPoint (m c ħ r : ℝ) : ℂ :=
  euclideanVacuumTwoPoint (m * c ^ 2) c ħ r

/-- A relativistic gap `E = m c^2` turns the spectral decay length into the reduced
Compton wavelength: the explicit two-point function is `exp (-r/lambda_C)`. -/
lemma comptonVacuumTwoPoint_eq (m c ħ r : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonVacuumTwoPoint m c ħ r =
      ((Real.exp (-(r / comptonWavelength m c ħ)) : ℝ) : ℂ) := by
  rw [comptonVacuumTwoPoint, euclideanVacuumTwoPoint_eq]
  congr 2
  unfold comptonWavelength
  field_simp

/-- At the entropic coordinate `r = lambda_C log K`, the derived scalar-mode two-point
function evaluates to `1/K = tanh eta`. This is a statement about the explicit Euclidean
spectral model, not an AQFT Bell functional. -/
lemma comptonVacuumTwoPoint_at_entropicDistance (m c ħ η : ℝ) (hη : 0 < η)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonVacuumTwoPoint m c ħ (entropicProperDistance m c ħ η) =
      ((Real.tanh η : ℝ) : ℂ) := by
  have hlam : comptonWavelength m c ħ ≠ 0 := by
    unfold comptonWavelength
    exact div_ne_zero hħ (mul_ne_zero hm hc)
  rw [comptonVacuumTwoPoint_eq m c ħ _ hm hc hħ]
  exact_mod_cast entropicProperDistance_vacuumBell m c ħ η hη hlam

/-! # C. Uniqueness of the logarithmic correlation coordinate -/

/-- For a positive decay length and Schmidt number, the entropic distance is the unique
coordinate at which an exponential profile has suppression `1/K`. -/
lemma exp_decay_eq_inv_schmidt_iff (η ell r : ℝ) (hη : 0 < η) (hell : 0 < ell) :
    Real.exp (-(r / ell)) = 1 / schmidtNumber η ↔
      r = ell * Real.log (schmidtNumber η) := by
  have hK : 0 < schmidtNumber η := by
    have hs : 0 < Real.sinh η := Real.sinh_pos_iff.mpr hη
    unfold schmidtNumber
    positivity
  have hinvK : 1 / schmidtNumber η = Real.exp (-Real.log (schmidtNumber η)) := by
    rw [Real.exp_neg, Real.exp_log hK]
    simp [one_div]
  constructor
  · intro h
    rw [hinvK] at h
    have hexp : -(r / ell) = -Real.log (schmidtNumber η) := Real.exp_injective h
    field_simp [hell.ne'] at hexp ⊢
    linarith
  · intro h
    rw [h, mul_div_cancel_left₀ _ hell.ne', hinvK]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonEuclideanVacuumCorrelation

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonEuclideanVacuumCorrelation

zil attach euclideanVacuumTwoPoint_eq where
  formalizes @ "claim:the-specified-vacuum-one-particle-scalar-mode-two-point-function-is-\
the-exponential-of-its-euclidean-hamiltonian-gap",
  epistemic_status @ "conditional-model",
  caveat @ "epistemic:this-is-an-explicit-vacuum-one-particle-sector-model-not-the-\
reeh-schlieder-theorem-or-an-aqft-bell-correlation"

zil attach comptonVacuumTwoPoint_eq where
  formalizes @ "claim:for-a-free-scalar-mode-with-relativistic-gap-m-c-squared-the-\
explicit-euclidean-vacuum-two-point-function-decays-as-exp-minus-r-over-the-reduced-\
compton-wavelength",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonEuclideanVacuumCorrelation.euclideanVacuumTwoPoint_eq",
  caveat @ "epistemic:the-exact-equality-is-a-euclidean-single-mode-spectral-result-\
not-a-concurrence-or-chsh-equality-for-spacelike-separated-aqft-regions"

zil attach exp_decay_eq_inv_schmidt_iff where
  formalizes @ "claim:for-positive-decay-length-and-schmidt-rapidity-r-equals-lambda-\
log-k-is-the-unique-coordinate-where-the-exponential-profile-equals-one-over-k",
  epistemic_status @ "consistency-identity",
  caveat @ "epistemic:uniqueness-identifies-the-coordinate-within-an-exponential-\
profile-but-does-not-derive-that-profile-for-aqft-bell-observables"

zil_file_contract physlib.comptonEuclideanVacuumCorrelation where
  promises "A specified vacuum-one-particle scalar-mode carrier derives rather than \
assumes an exact exponential Euclidean two-point profile. The vacuum basis state, \
truncated field insertion, and diagonal Euclidean Hamiltonian evolution are explicit; \
evaluating their vacuum matrix element gives exp(-E r/(hbar c)), and the relativistic \
gap E = m c^2 gives exp(-r/lambda_C). At r = lambda_C log K the result is 1/K = \
tanh eta, and that logarithmic coordinate is unique among real r for a positive decay \
length."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
FrequencyTrinity.comptonWavelength",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
EntropicProperDistance.entropicProperDistance"]
  forbids_substitutes ["an exact concurrence or CHSH decay law for spacelike-separated \
AQFT local algebras",
    "a derivation from Reeh-Schlieder alone",
    "a continuum interacting-field or multiparticle spectral theorem"]
  witnessed_by [euclideanVacuumTwoPoint_eq,
    comptonVacuumTwoPoint_eq,
    comptonVacuumTwoPoint_at_entropicDistance,
    exp_decay_eq_inv_schmidt_iff]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonEuclideanVacuumCorrelation

/- ZIL-END -/
