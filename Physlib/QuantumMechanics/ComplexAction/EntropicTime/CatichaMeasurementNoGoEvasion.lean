/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entropic dynamics evades the ψ-ontology no-go theorems (Caticha, ED and "Measurement" §5)

Formalizes the mechanism by which entropic dynamics evades the ψ-ontology (Bell/Spekkens/Harrigan) no-go theorems
(Caticha, arXiv:2208.02156, §5, Eqs. 24–31). In the ontological-models framework the outcome probability is obtained
by marginalizing over the ontic state `λ`,

`p(k | 𝓜, 𝓟) = ∑_λ p(λ | 𝓟) · p(k | 𝓜, 𝓟, λ)` (Eqs. 24–25),

using two assumptions: **causality** `p(λ | 𝓜, 𝓟) = p(λ | 𝓟)` (Eq. 26, `λ` independent of the *later* device
choice `𝓜`), and the **ontological response** `p(k | 𝓜, 𝓟, λ) = p(k | 𝓜, λ)` (Eq. 27, the outcome depends only on
the *ontic* `λ`). ED satisfies the first but **violates** the second: in ED the response depends on the *epistemic*
wave function `ψ`, `p(k | 𝓜, 𝓟, λ) = p(k | 𝓜, ψ)` (Eq. 30), *not* on the ontic positions `λ`. Hence ED is not an
"ontological model" and is immune to the no-go theorems.

The exact kernel, on a finite ontic-state space with a normalized prior:

* the **outcome is the marginal** `∑_λ p(λ)·r(λ)` (`marginalOutcome`) — the law of total probability (Eqs. 24–25);
* the **ED (epistemic) response marginalizes to itself** `∑_λ p(λ)·r = r` for a response constant in `λ`
 (`ed_marginal_ontic_independent`, Eqs. 30→31) — because the ED response depends only on `ψ`, the outcome
 `p(k | 𝓜, ψ)` is *independent of the ontic distribution* `p(λ | 𝓟)`: the ontic states have no causal influence on
 the outcome;
* the **ontological (λ-dependent) response is prior-dependent** (`ontological_outcome_prior_dependent`) — a response
 that genuinely depends on the ontic `λ` gives an outcome that changes with the ontic prior, so it *does* include the
 ontic-dynamics structure that the no-go theorems constrain.

So the evasion is exactly the difference between a response that depends on the ontic `λ` (ontological models,
constrained by the no-go theorems) and one that depends only on the epistemic `ψ` (ED): the latter marginalizes to
`p(k | 𝓜, ψ)` regardless of the ontic distribution, so ED reproduces QM without being an ontological model — "an
epistemic mechanics without an ontic mechanism".

* **§A — the marginal outcome and the ED evasion** (`marginalOutcome`, `ed_marginal_ontic_independent`).
* **§B — the ontological response is prior-dependent** (`ontological_outcome_prior_dependent`).

The marginal, the ontic-independence of a constant response, and the prior-dependence of a
`λ`-dependent response are exact finite-sum algebra. The full ontological-models framework and the analysis of the
specific no-go theorems are the referenced content; here the algebraic distinction that defines the evasion is
proved. No new axioms.

## References

* A. Caticha, arXiv:2208.02156 (§5, Eqs. 24–31); J.S. Bell, R.W. Spekkens, N. Harrigan (ontological models). Repo
 companion: `EntropicTime.CatichaMeasurementGenericBornRule` (the ED Born rule).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementNoGoEvasion

/-! ## §A — the marginal outcome and the ED evasion -/

/-- **The marginal outcome probability** `p(k | 𝓜, 𝓟) = ∑_λ p(λ | 𝓟) · r(λ)` (Caticha Eqs. 24–25) — the law of
total probability: the outcome is the ontic prior `p(λ | 𝓟)` weighted by the response `r(λ) = p(k | 𝓜, 𝓟, λ)`. -/
noncomputable def marginalOutcome {Λ : Type*} [Fintype Λ] (pLambda r : Λ → ℝ) : ℝ :=
  ∑ l, pLambda l * r l

/-- **[The ED response marginalizes to itself: ontic independence] `∑_λ p(λ)·r = r`.** In ED the response depends
only on the *epistemic* wave function `ψ`, so it is constant in the ontic state `λ` (Caticha Eq. 30). Marginalizing
it against the normalized ontic prior returns the response unchanged (Eq. 31): the outcome `p(k | 𝓜, ψ)` is
*independent of the ontic distribution* — the ontic states have no causal influence on the outcome. -/
theorem ed_marginal_ontic_independent {Λ : Type*} [Fintype Λ] (pLambda : Λ → ℝ)
    (hnorm : ∑ l, pLambda l = 1) (r : ℝ) :
    marginalOutcome pLambda (fun _ => r) = r := by
  unfold marginalOutcome
  rw [← Finset.sum_mul, hnorm, one_mul]

/-! ## §B — the ontological response is prior-dependent -/

/-- **[The ontological (λ-dependent) response is prior-dependent].** A response that genuinely depends on the ontic
state `λ` (the ontological-model assumption, Caticha Eq. 27) gives an outcome that *changes* with the ontic prior:
here two normalized priors on a two-state ontic space give different outcomes for the same `λ`-dependent response.
This is the ontic-dynamics structure the no-go theorems constrain — and exactly what ED avoids by making its
response depend on `ψ`, not `λ` (`ed_marginal_ontic_independent`). -/
theorem ontological_outcome_prior_dependent :
    (∑ l, (![(1 : ℝ), 0]) l = 1) ∧ (∑ l, (![(0 : ℝ), 1]) l = 1)
      ∧ marginalOutcome ![(1 : ℝ), 0] ![(0 : ℝ), 1]
          ≠ marginalOutcome ![(0 : ℝ), 1] ![(0 : ℝ), 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [marginalOutcome, Fin.sum_univ_two]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementNoGoEvasion

end
