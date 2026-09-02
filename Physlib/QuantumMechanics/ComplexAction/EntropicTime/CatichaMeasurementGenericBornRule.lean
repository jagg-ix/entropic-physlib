/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Transporting the position Born rule to generic measurements by unitarity

Formalizes the central result of Caticha (*Entropic Dynamics and Quantum "Measurement"*, arXiv:2208.02156, §4,
Eqs. 12–16): in entropic dynamics **all measurements are position measurements**, and the Born rule for a *generic*
measurement is transported from the explicitly supplied Born rule for positions together with the *unitarity* of the
measurement device. A complex device `𝓜` is a linear, inner-product-preserving (unitary) evolution `Û_M` that
carries the measurement-basis state `|s_k⟩` to the position-basis state `|x_k⟩`:

`Û_M |s_k⟩ = |x_k⟩`  (Eq. 12).

For an initial epistemic state `|ψ⟩ = Σ c_k |s_k⟩`, the state reaching the position detectors is `Û_M|ψ⟩ = Σ c_k
|x_k⟩` (Eq. 15, by linearity), and the *position* Born rule applied to it gives the outcome probability
`p_k = |⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|² = |c_k|²` (Eq. 16) — the generic Born rule, with no collapse and no
additional measurement-basis probability postulate beyond the supplied position rule.

The exact kernel, on a complex inner-product space with `Û_M` a linear isometry:

* the **measurement amplitude is preserved** `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩` (`measurement_amplitude_eq`) — unitarity of
  the device carries the position amplitude at `x_k = Û_M s_k` back to the amplitude `⟨s_k, ψ⟩`;
* the **generic Born rule** `|⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|²` (`generic_born_rule`) — the probability of the
  *position* outcome `x_k = Û_M s_k` in the evolved state equals the Born probability in the `|s_k⟩` basis: measuring
  `𝓜` is reduced to measuring position;
* the **coefficient form** `p_k = |c_k|²` (`generic_born_rule_coeff`) — with `c_k = ⟨s_k, ψ⟩` the expansion
  coefficient (Eqs. 11, 16), the outcome probability is the modulus-squared of the coefficient.

Thus the Born rule for a generic "observable" is reduced to the position Born rule: the unitary device carries the
measurement basis to a position basis, and the supplied position rule (`‖ψ‖² = ρ`, the ED
`hamiltonKilling_born_rule`) does the rest. The "measured value" is not a preexisting property — it is the
outcome the dynamical, unitary process assigns.

* **§A — the measurement amplitude is preserved** (`measurement_amplitude_eq`).
* **§B — the generic Born rule** (`generic_born_rule`).
* **§C — the coefficient form `p_k = |c_k|²`** (`generic_born_rule_coeff`).

**Honest layering.** The amplitude preservation, the generic-basis equality, and the coefficient form are exact
inner-product algebra, reusing `LinearIsometry.inner_map_map` and `OrthonormalBasis.repr_apply_apply`. They do
not derive the modulus-squared position probability rule from unitarity alone. The
amplification/von-Neumann pointer model (Eqs. 18–23) and the no-go-theorem evasion (§5) are the referenced content.


## References

* A. Caticha, arXiv:2208.02156 (§4, Eqs. 12–16); D.T. Johnson, A. Caticha. Repo companion:
  `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`hamiltonKilling_born_rule`, the position Born rule).


-/

set_option autoImplicit false

open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


/-- **[The measurement amplitude is preserved] `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩`.** The unitary measurement device `Û_M`
(a linear isometry) preserves inner products, so the position amplitude at `x_k = Û_M s_k` in the evolved state
`Û_M ψ` equals the amplitude `⟨s_k, ψ⟩` in the initial state — the algebraic heart of "all measurements are
position measurements" (Caticha Eqs. 12–15). -/
lemma measurement_amplitude_eq (U : E →ₗᵢ[ℂ] E) (s ψ : E) :
    ⟪U s, U ψ⟫_ℂ = ⟪s, ψ⟫_ℂ :=
  U.inner_map_map s ψ


/-- **[The generic Born rule] `|⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|²`.** The probability of the *position* outcome
`x_k = Û_M s_k` in the evolved state `Û_M ψ` (position Born rule) equals the Born probability in the measurement
basis `|s_k⟩` (Caticha Eq. 16) — the generic Born rule transported from the position Born rule by unitarity,
with no collapse. -/
lemma generic_born_rule (U : E →ₗᵢ[ℂ] E) (s ψ : E) :
    ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2 := by
  rw [U.inner_map_map]


/-- **[The coefficient form of the generic Born rule] `p_k = |c_k|²`.** With the measurement states `|s_k⟩` an
orthonormal basis and `c_k = ⟨s_k, ψ⟩ = b.repr ψ k` the expansion coefficient of `|ψ⟩ = Σ c_k |s_k⟩` (Caticha
Eqs. 11, 16), the outcome probability at the position `x_k = Û_M s_k` is the modulus-squared of the coefficient. -/
lemma generic_born_rule_coeff {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (U : E →ₗᵢ[ℂ] E) (ψ : E) (k : ι) :
    ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = ‖b.repr ψ k‖ ^ 2 := by
  rw [U.inner_map_map, ← OrthonormalBasis.repr_apply_apply]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule

end
