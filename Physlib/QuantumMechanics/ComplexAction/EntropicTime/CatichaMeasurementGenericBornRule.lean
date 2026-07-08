/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The generic Born rule from position measurement and unitarity (Caticha, ED and "Measurement")

Formalizes the central result of Caticha (*Entropic Dynamics and Quantum "Measurement"*, arXiv:2208.02156, §4,
Eqs. 12–16): in entropic dynamics **all measurements are position measurements**, and the Born rule for a *generic*
measurement is **derived** — not postulated — from the Born rule for positions together with the *unitarity* of the
measurement device. A complex device `𝓜` is a linear, inner-product-preserving (unitary) evolution `Û_M` that
includes the measurement-basis state `|s_k⟩` to the position-basis state `|x_k⟩`:

`Û_M |s_k⟩ = |x_k⟩` (Eq. 12).

For an initial epistemic state `|ψ⟩ = Σ c_k |s_k⟩`, the state reaching the position detectors is `Û_M|ψ⟩ = Σ c_k
|x_k⟩` (Eq. 15, by linearity), and the *position* Born rule applied to it gives the outcome probability
`p_k = |⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|² = |c_k|²` (Eq. 16) — the generic Born rule, with no collapse and no extra
postulate.

The exact kernel, on a complex inner-product space with `Û_M` a linear isometry:

* the **measurement amplitude is preserved** `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩` (`measurement_amplitude_eq`) — unitarity of
 the device includes the position amplitude at `x_k = Û_M s_k` back to the amplitude `⟨s_k, ψ⟩`;
* the **generic Born rule** `|⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|²` (`generic_born_rule`) — the probability of the
 *position* outcome `x_k = Û_M s_k` in the evolved state equals the Born probability in the `|s_k⟩` basis: measuring
 `𝓜` is reduced to measuring position;
* the **coefficient form** `p_k = |c_k|²` (`generic_born_rule_coeff`) — with `c_k = ⟨s_k, ψ⟩` the expansion
 coefficient (Eqs. 11, 16), the outcome probability is the modulus-squared of the coefficient.

So the Born rule for a generic "observable" is a theorem of ED: the unitary device reduces every measurement to a
position measurement, and the position Born rule (`‖ψ‖² = ρ`, the ED `hamiltonKilling_born_rule`) does the rest. The
"measured value" is not a preexisting property — it is the outcome the dynamical, unitary process assigns.

* **§A — the measurement amplitude is preserved** (`measurement_amplitude_eq`).
* **§B — the generic Born rule** (`generic_born_rule`).
* **§C — the coefficient form `p_k = |c_k|²`** (`generic_born_rule_coeff`).

The amplitude preservation, the generic Born rule, and the coefficient form are exact
inner-product algebra, reusing `LinearIsometry.inner_map_map` and `OrthonormalBasis.repr_apply_apply`. The
amplification/von-Neumann pointer model (Eqs. 18–23) and the no-go-theorem evasion (§5) are the referenced content.
No new axioms.

## References

* A. Caticha, arXiv:2208.02156 (§4, Eqs. 12–16); D.T. Johnson, A. Caticha. Repo companion:
 `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`hamiltonKilling_born_rule`, the position Born rule).

No new axioms.
-/

set_option autoImplicit false

open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## §A — the measurement amplitude is preserved -/

/-- **[The measurement amplitude is preserved] `⟨Û_M s, Û_M ψ⟩ = ⟨s, ψ⟩`.** The unitary measurement device `Û_M`
(a linear isometry) preserves inner products, so the position amplitude at `x_k = Û_M s_k` in the evolved state
`Û_M ψ` equals the amplitude `⟨s_k, ψ⟩` in the initial state — the algebraic heart of "all measurements are
position measurements" (Caticha Eqs. 12–15). -/
theorem measurement_amplitude_eq (U : E →ₗᵢ[ℂ] E) (s ψ : E) :
    ⟪U s, U ψ⟫_ℂ = ⟪s, ψ⟫_ℂ :=
  U.inner_map_map s ψ

/-! ## §B — the generic Born rule -/

/-- **[The generic Born rule] `|⟨x_k | Û_M ψ⟩|² = |⟨s_k | ψ⟩|²`.** The probability of the *position* outcome
`x_k = Û_M s_k` in the evolved state `Û_M ψ` (position Born rule) equals the Born probability in the measurement
basis `|s_k⟩` (Caticha Eq. 16) — the generic Born rule *derived* from the position Born rule and unitarity, with no
collapse. -/
theorem generic_born_rule (U : E →ₗᵢ[ℂ] E) (s ψ : E) :
    ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2 := by
  rw [U.inner_map_map]

/-! ## §C — the coefficient form -/

/-- **[The coefficient form of the generic Born rule] `p_k = |c_k|²`.** With the measurement states `|s_k⟩` an
orthonormal basis and `c_k = ⟨s_k, ψ⟩ = b.repr ψ k` the expansion coefficient of `|ψ⟩ = Σ c_k |s_k⟩` (Caticha
Eqs. 11, 16), the outcome probability at the position `x_k = Û_M s_k` is the modulus-squared of the coefficient. -/
theorem generic_born_rule_coeff {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (U : E →ₗᵢ[ℂ] E) (ψ : E) (k : ι) :
    ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = ‖b.repr ψ k‖ ^ 2 := by
  rw [U.inner_map_map, ← OrthonormalBasis.repr_apply_apply]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule

end
