/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Kähler structure of the statistical cotangent bundle

The cotangent bundle of the statistical simplex carries three compatible structures — a symplectic form `Ω`, the
information metric `G`, and a **complex structure** `J = −G⁻¹Ω` with `J² = −1` — making it a **Kähler manifold**.
In the complex coordinates `ψ = √ρ e^{iΦ}` the complex structure is simply multiplication by `i`, and the pairing
`G + iΩ` becomes the **Hermitian inner product** `⟨ψ|φ⟩ = \bar ψ φ`, whose diagonal `⟨ψ|ψ⟩` is the Born norm
`|ψ|²`. These are the ingredients from which the Hilbert space and the linear Schrödinger flow emerge.

References: A. Caticha, arXiv:2107.08502 (§§3–4, 6). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.KahlerStructure

/-- **The complex structure** `J` on the state space, in `ψ` coordinates: multiplication by `i`. -/
def jAction (z : ℂ) : ℂ := Complex.I * z

/-- **The complex structure squares to `−1`** `J² = −1` — the defining Kähler identity, making the statistical
cotangent bundle a complex (Kähler) manifold. -/
theorem jAction_sq (z : ℂ) : jAction (jAction z) = -z := by
  unfold jAction
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- **The Hermitian inner product** `⟨ψ|φ⟩ = \bar ψ φ` — the pairing `½(G + iΩ)` of the metric and symplectic
structures in `ψ` coordinates. -/
def hermitianInner (z w : ℂ) : ℂ := (starRingEnd ℂ) z * w

/-- **The inner product is conjugate-symmetric** `⟨ψ|φ⟩ = conj ⟨φ|ψ⟩`. -/
theorem hermitianInner_conj_symm (z w : ℂ) :
    (starRingEnd ℂ) (hermitianInner z w) = hermitianInner w z := by
  unfold hermitianInner
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- **The diagonal of the inner product is the Born norm** `⟨ψ|ψ⟩ = |ψ|²`. The metric-plus-symplectic pairing,
evaluated on a single state, returns exactly the Born probability. -/
theorem hermitianInner_self (z : ℂ) : hermitianInner z z = (Complex.normSq z : ℂ) := by
  unfold hermitianInner
  rw [mul_comm, Complex.mul_conj]

/-- **The Born norm is real and equals `|ψ|²`** `Re ⟨ψ|ψ⟩ = |ψ|²`. -/
theorem hermitianInner_self_re (z : ℂ) : (hermitianInner z z).re = Complex.normSq z := by
  rw [hermitianInner_self, Complex.ofReal_re]

end Physlib.QuantumMechanics.KahlerStructure

end
