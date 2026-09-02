/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Hermite-function `L²(ℝ)` orthonormal basis

The harmonic-oscillator eigenfunctions `ψ_n(x) = (2ⁿ n! √π ξ)^{−1/2} Hₙ(x/ξ) e^{−x²/2ξ²}` are exactly the
(scaled) **physicists' Hermite functions**. physlib already proves, separately, that they are
*orthonormal* (`eigenfunction_orthonormal`) and that their span is *dense* in `L²(ℝ)`
(`eigenfunction_completeness`). This module assembles those two facts into a single Mathlib
`HilbertBasis ℕ ℂ HilbertSpace` — the Hermite-function orthonormal basis of `L²(ℝ)` — so that the whole
`HilbertBasis` API (component expansion, Parseval, the `ℓ²` representation isometry) becomes available.

This is the **keystone** that the Bender–Dunne / time-of-arrival density argument needs: the paper
(`ComplexAction.TimeOperator.BenderDunneOperatorAnalytic`) constructs its dense domain from a complete
orthonormal set of Hermite functions, and completeness *in `L²`* is exactly what a `HilbertBasis` certifies.

* **`eigenfunctionHilbertBasis`** — the `HilbertBasis ℕ ℂ HilbertSpace` built by `HilbertBasis.mk` from the
  orthonormal family and the dense span; **`eigenfunctionHilbertBasis_apply`** (`b n = mk (eigenfunction n)`).
* **`eigenfunction_hasSum_repr`** — every `f ∈ L²(ℝ)` is the (unconditionally convergent) sum of its
  Hermite components `∑ₙ ⟨ψₙ, f⟩ ψₙ`, the concrete completeness statement.

**Honest layering — the single carried hypothesis.** `eigenfunction_orthonormal` is unconditional.
`eigenfunction_completeness` carries one input: **Plancherel's theorem** in the raw-`Real.fourierIntegral`
form `‖𝓕 f‖₂ = ‖f‖₂` (physlib flagged this as absent from Mathlib when written). Mathlib **now** has Plancherel
as the `L²` isometry `MeasureTheory.Lp.fourierTransformₗᵢ` / `norm_fourier_eq`, but only bridged to the *raw*
`Real.fourierIntegral` at the Schwartz level (`SchwartzMap.toLp_fourier_eq`); the raw↔`Lp` agreement on general
`L¹ ∩ L²` functions is the one remaining glue. So the basis is stated taking that raw-form Plancherel as an
explicit hypothesis — the *same* one physlib's own completeness already carries, introducing no new gap. No
axioms are used.

## References

* Bunao & Galapon, arXiv:1509.00340. Assembles `HarmonicOscillator.Eigenfunction.eigenfunction_orthonormal`
  and `HarmonicOscillator.Completeness.eigenfunction_completeness` into a `Mathlib` `HilbertBasis`.


-/

set_option autoImplicit false

namespace QuantumMechanics.OneDimension.HarmonicOscillator

open Nat Physlib HilbertSpace MeasureTheory Constants
open scoped FourierTransform

variable (Q : HarmonicOscillator)

/-- The **Hermite-function orthonormal basis of `L²(ℝ)`** — the harmonic-oscillator eigenfunctions
`ψ_n = (2ⁿn!√πξ)^{−1/2} Hₙ(x/ξ) e^{−x²/2ξ²}` (the scaled physicists' Hermite functions) packaged as a Mathlib
`HilbertBasis`, from the orthonormal family (`eigenfunction_orthonormal`) and the dense span
(`eigenfunction_completeness`). Carries the raw-form Plancherel hypothesis that
`eigenfunction_completeness` requires (see module docstring). -/
noncomputable def eigenfunctionHilbertBasis
    (plancherel : ∀ {f : ℝ → ℂ} (_ : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) :
    HilbertBasis ℕ ℂ HilbertSpace :=
  HilbertBasis.mk Q.eigenfunction_orthonormal (Q.eigenfunction_completeness plancherel).ge

/-- **The `n`-th basis vector is the `n`-th Hermite eigenfunction** `bₙ = mk(ψₙ)`. -/
@[simp] lemma eigenfunctionHilbertBasis_apply
    (plancherel : ∀ {f : ℝ → ℂ} (_ : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) (n : ℕ) :
    Q.eigenfunctionHilbertBasis plancherel n = HilbertSpace.mk (Q.eigenfunction_memHS n) := by
  simp only [eigenfunctionHilbertBasis, HilbertBasis.coe_mk]

/-- **Every `L²(ℝ)` function expands in the Hermite basis** `f = ∑ₙ ⟨ψₙ, f⟩ ψₙ` (unconditionally convergent) —
the concrete completeness statement: the Hermite functions are not merely dense but a genuine orthonormal basis,
so the Fourier–Hermite series of any `f ∈ L²(ℝ)` converges back to `f`. -/
lemma eigenfunction_hasSum_repr
    (plancherel : ∀ {f : ℝ → ℂ} (_ : Integrable f volume) (_ : MemLp f 2),
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) (f : HilbertSpace) :
    HasSum (fun n => (Q.eigenfunctionHilbertBasis plancherel).repr f n •
      HilbertSpace.mk (Q.eigenfunction_memHS n)) f := by
  have h := (Q.eigenfunctionHilbertBasis plancherel).hasSum_repr f
  simpa only [eigenfunctionHilbertBasis_apply] using h

end QuantumMechanics.OneDimension.HarmonicOscillator
