/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementNoGoEvasion

/-!
# The entropic-dynamics solution of the measurement problem, assembled (Caticha 2208.02156 §6)

Composes the two results of Caticha (*Entropic Dynamics and Quantum "Measurement"*, arXiv:2208.02156) — the
generic Born rule from position measurement and unitarity (§4, `CatichaMeasurementGenericBornRule`) and the
epistemic (ontic-independent) response that evades the ψ-ontology no-go theorems (§5,
`CatichaMeasurementNoGoEvasion`) — into the paper's central conclusion (§6): entropic dynamics reproduces the
quantum measurement probabilities without collapse and without an ontic dynamics.

The outcome probability of a measurement `𝓜` on the initial epistemic state `ψ`, computed as the *marginal over the
ontic states* `λ` of the ED (epistemic) response — where the response is the position Born probability of the
unitary device's outcome `x = Û_M s` — equals the quantum Born probability `|⟨s | ψ⟩|²`, **independent of the ontic
distribution**:

`p(k | 𝓜, 𝓟) = ∑_λ p(λ | 𝓟) · |⟨x | Û_M ψ⟩|² = |⟨s | ψ⟩|²` (Eq. 31).

Two things happen at once, the paper's "two points": (i) the *unitary device reduces the measurement to a position
measurement* (the generic Born rule, `generic_born_rule`), so the response is the QM amplitude `|⟨s | ψ⟩|²`; and
(ii) since that response is *epistemic* — it depends on `ψ`, not on the ontic `λ` — marginalizing over the ontic
distribution returns it unchanged (`ed_marginal_ontic_independent`), so the outcome is independent of the ontic
prior. The former is why the answer is the Born rule; the latter is why ED is not an ontological model and evades
the no-go theorems.

* the **ED measurement reproduces QM** `p(k | 𝓜, 𝓟) = |⟨s | ψ⟩|²` (`ed_measurement_reproduces_qm`) — the composed
 result: the marginal of the position-Born epistemic response is the quantum Born probability, no collapse, no
 postulate;
* the **outcome is independent of the ontic prior** (`ed_outcome_prior_independent`) — any two normalized ontic
 distributions give the *same* outcome, in direct contrast with the ontological `λ`-dependent response
 (`ontological_outcome_prior_dependent`): ED reproduces QM precisely because its response is epistemic.

So the ED solution of the measurement problem is this single formal statement: the quantum measurement probability
`|⟨s | ψ⟩|²` is obtained as the marginal, over an *arbitrary* ontic distribution, of the epistemic response fixed by
the unitary reduction to a position measurement — QM reproduced, ontic-mechanism-free.

* **§A — the composed result** (`ed_measurement_reproduces_qm`).
* **§B — ontic-prior independence** (`ed_outcome_prior_independent`).

The composed identity and the prior independence are exact algebra, chaining
`generic_born_rule` (§4) and `ed_marginal_ontic_independent` (§5). No new axioms.

## References

* A. Caticha, arXiv:2208.02156 (§4–§6, Eqs. 16, 31). Repo dependencies:
 `EntropicTime.CatichaMeasurementGenericBornRule`, `EntropicTime.CatichaMeasurementNoGoEvasion`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementNoGoEvasion
open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementProblemSolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## §A — the composed result -/

/-- **[The ED measurement reproduces the quantum Born probability] `p(k | 𝓜, 𝓟) = |⟨s | ψ⟩|²`.** The outcome
probability of the measurement `𝓜` on `ψ`, computed as the marginal over the ontic states `λ` (normalized prior
`pLambda`) of the ED epistemic response — the position Born probability `|⟨x | Û_M ψ⟩|²` of the unitary device's
outcome `x = Û_M s` — equals the quantum Born probability `|⟨s | ψ⟩|²` (Caticha Eq. 31). Composed from the generic
Born rule (`generic_born_rule`, the response is `|⟨s | ψ⟩|²` because `Û_M` reduces the measurement to a position
measurement) and the ontic independence of the epistemic response (`ed_marginal_ontic_independent`, marginalizing
over `λ` leaves it unchanged). No collapse, no postulate. -/
theorem ed_measurement_reproduces_qm {Λ : Type*} [Fintype Λ] (U : E →ₗᵢ[ℂ] E) (s ψ : E)
    (pLambda : Λ → ℝ) (hnorm : ∑ l, pLambda l = 1) :
    marginalOutcome pLambda (fun _ => ‖⟪U s, U ψ⟫_ℂ‖ ^ 2) = ‖⟪s, ψ⟫_ℂ‖ ^ 2 := by
  rw [ed_marginal_ontic_independent pLambda hnorm, generic_born_rule]

/-! ## §B — ontic-prior independence -/

/-- **[The ED outcome is independent of the ontic prior].** Any two normalized ontic distributions `p₁, p₂` give the
*same* measurement outcome, because the epistemic response marginalizes to the quantum Born probability `|⟨s | ψ⟩|²`
regardless of the prior — in direct contrast with an ontological, `λ`-dependent response
(`ontological_outcome_prior_dependent`). This ontic-prior independence is exactly why ED evades the ψ-ontology
no-go theorems while reproducing QM. -/
theorem ed_outcome_prior_independent {Λ : Type*} [Fintype Λ] (U : E →ₗᵢ[ℂ] E) (s ψ : E)
    (p₁ p₂ : Λ → ℝ) (h₁ : ∑ l, p₁ l = 1) (h₂ : ∑ l, p₂ l = 1) :
    marginalOutcome p₁ (fun _ => ‖⟪U s, U ψ⟫_ℂ‖ ^ 2)
      = marginalOutcome p₂ (fun _ => ‖⟪U s, U ψ⟫_ℂ‖ ^ 2) := by
  rw [ed_measurement_reproduces_qm U s ψ p₁ h₁, ed_measurement_reproduces_qm U s ψ p₂ h₂]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementProblemSolution

end
