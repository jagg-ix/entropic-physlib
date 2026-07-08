/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The classical limit `ℏ → 0` of Nambu quantization (Axenides–Floratos §5, Eq. 5.7)

The second quantization requirement (Axenides, Floratos, JHEP 04 (2010) 036, requirement β, Eq. 5.7) is the
**existence of a classical limit**: as `ℏ → 0` the deformed bracket `[Xⁱ, Xʲ] = iℏ ε^{ijk} Pᵏ(X; ℏ)` must
collapse to the classical Poisson structure, with the polynomials tending to the classical gradient,

  `lim_{ℏ → 0} Pᵏ(x; ℏ) = ∂ᵏ H₂`.

Modelling `κ = iℏ` as a real parameter and the operators/polynomials as elements of a normed `ℝ`-algebra
`𝔸`, this file proves the two analytic facts that make up the classical limit:

* `commutator_classicalLimit`: the commutator `[Xⁱ, Xʲ] = κ • C` vanishes as `κ → 0` — the quantized
  coordinates **commute classically** (the deformation collapses to a commutative algebra of functions).
* `deformedBracket_classicalLimit`: even with an `ℏ`-dependent structure `Pᵏ(κ)` (continuous at `0`), the
  full bracket `κ • P(κ) → 0` as `κ → 0`.
* `polynomial_classicalLimit`: `Pᵏ(κ) → ∂ᵏH₂` as `κ → 0`, i.e. the deformation polynomial tends to the
  classical gradient `g = ∂ᵏH₂ = Pᵏ(0)` (Eq. 5.7).

Together: the bracket vanishes (commutativity is restored) while `Pᵏ` converges to the classical gradient —
the quantized Nambu algebra degenerates smoothly onto the classical Poisson structure.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §5, requirement β, Eq. 5.7.

No additional assumptions.
-/

set_option autoImplicit false

open Filter Topology

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.ClassicalLimit

variable {𝔸 : Type*} [NormedAddCommGroup 𝔸]

section
variable [NormedSpace ℝ 𝔸]

/-- **[Coordinates commute classically]** the commutator `[Xⁱ, Xʲ] = κ • C` tends to `0` as `κ = iℏ → 0`:
the quantum deformation collapses to a commutative (classical) algebra in the limit. -/
theorem commutator_classicalLimit (C : 𝔸) :
    Tendsto (fun κ : ℝ => κ • C) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_id.tendsto (0 : ℝ)).smul (tendsto_const_nhds (x := C))

/-- **[The deformed bracket vanishes]** even with an `ℏ`-dependent structure `P(κ)` continuous at `0`, the
full bracket `κ • P(κ)` tends to `0` as `κ → 0`. -/
theorem deformedBracket_classicalLimit (P : ℝ → 𝔸) (hP : ContinuousAt P 0) :
    Tendsto (fun κ : ℝ => κ • P κ) (𝓝 0) (𝓝 0) := by
  have h := (continuous_id.tendsto (0 : ℝ)).smul hP
  simpa using h

end

/-- **[Polynomial tends to the classical gradient]** `Pᵏ(κ) → ∂ᵏH₂` as `κ = iℏ → 0` (Eq. 5.7): the
deformation polynomial, continuous at `0` with classical value `g = Pᵏ(0) = ∂ᵏH₂`, converges to that
gradient. -/
theorem polynomial_classicalLimit (P : ℝ → 𝔸) (g : 𝔸) (hP : ContinuousAt P 0) (hP0 : P 0 = g) :
    Tendsto P (𝓝 0) (𝓝 g) := by
  rw [← hP0]; exact hP

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.ClassicalLimit

end
