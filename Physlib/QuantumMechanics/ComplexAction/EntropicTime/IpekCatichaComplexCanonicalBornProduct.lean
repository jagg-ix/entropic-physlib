/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

/-!
# The complex canonical variables `(Ψ, Ψ*)` and the Born-rule product `ΨΨ* = ρ` (Ipek–Caticha)

Formalizes the change of variables from the probability–phase pair `(ρ, Φ)` to the complex variables `Ψ, Ψ*`
(Ipek–Caticha arXiv:2006.05036, Eq. 97),

`Ψ = ρ^{1/2} e^{iΦ}`, `Ψ* = ρ^{1/2} e^{−iΦ}`,

which form the canonical pair `(Ψ, iΨ*)` (Eq. 98) whose linear dynamics is the reason Hilbert spaces enter the
theory. The algebraic core, on the entropic-dynamics wave function `edWaveFunction`:

* the **conjugate is the phase-reversed wave function** `Ψ* = \overline{Ψ} = ρ^{1/2}e^{−iΦ}`
 (`edWaveFunction_conj`) — `Ψ*` is `Ψ` with the phase `Φ ↦ −Φ`, the second canonical variable;
* the **Born-rule product** `Ψ(Φ)·Ψ(−Φ) = ρ` (`edWaveFunction_mul_conj`) and `Ψ·\overline{Ψ} = ρ`
 (`edWaveFunction_mul_star`) — the probability is the product of the wave function and its conjugate (Eq. 97),
 the product form of the Born rule `ρ = |Ψ|²` complementary to `‖Ψ‖² = ρ` (`edWaveFunction_modulus_sq`).

So the complex wave function `Ψ = ρ^{1/2}e^{iΦ}` packages the probability and phase into one canonical variable whose
conjugate `Ψ*` is the phase reversal, with `ΨΨ* = ρ` recovering the Born-rule probability — the `(Ψ, iΨ*)` pair on
which the linear (Hilbert-space) form of entropic dynamics is built.

* **§A — the conjugate wave function** (`edWaveFunction_conj`).
* **§B — the Born-rule product** (`edWaveFunction_mul_conj`, `edWaveFunction_mul_star`).

The conjugate identity and the Born-rule product are exact `ℂ` algebra on `edWaveFunction`,
reusing the definition and `Real.mul_self_sqrt`. The functional canonical bracket `{Ψ, iΨ*} = δ` (Eq. 98) and the
emergence of the linear Schrödinger flow are the referenced content. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 97, 98). Repo structure:
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction` (`edWaveFunction`, `edWaveFunction_modulus_sq`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct

/-! ## §A — the conjugate wave function -/

/-- **[The conjugate is the phase-reversed wave function] `Ψ* = \overline{Ψ} = ρ^{1/2}e^{−iΦ}`.** Complex
conjugation of the entropic-dynamics wave function `Ψ = ρ^{1/2}e^{iΦ}` reverses the phase `Φ ↦ −Φ`, giving the
second canonical variable `Ψ*` (Ipek–Caticha Eq. 97). -/
theorem edWaveFunction_conj (ρ Φ : ℝ) :
    (starRingEnd ℂ) (edWaveFunction ρ Φ) = edWaveFunction ρ (-Φ) := by
  unfold edWaveFunction
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-! ## §B — the Born-rule product -/

/-- **[The Born-rule product] `Ψ(Φ)·Ψ(−Φ) = ρ`.** The product of the wave function and its phase reversal is the
probability `ρ` (Ipek–Caticha Eq. 97): `ρ^{1/2}e^{iΦ}·ρ^{1/2}e^{−iΦ} = ρ·e^{0} = ρ`. -/
theorem edWaveFunction_mul_conj (ρ Φ : ℝ) (hρ : 0 ≤ ρ) :
    edWaveFunction ρ Φ * edWaveFunction ρ (-Φ) = (ρ : ℂ) := by
  unfold edWaveFunction
  rw [mul_mul_mul_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt hρ, ← Complex.exp_add,
    show (Φ : ℂ) * Complex.I + ((-Φ : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

/-- **[The Born-rule product with the conjugate] `Ψ·\overline{Ψ} = ρ`.** The wave function times its complex
conjugate is the probability — the product form of the Born rule `ρ = |Ψ|²`, complementary to the modulus form
`‖Ψ‖² = ρ` (`edWaveFunction_modulus_sq`). -/
theorem edWaveFunction_mul_star (ρ Φ : ℝ) (hρ : 0 ≤ ρ) :
    edWaveFunction ρ Φ * (starRingEnd ℂ) (edWaveFunction ρ Φ) = (ρ : ℂ) := by
  rw [edWaveFunction_conj]
  exact edWaveFunction_mul_conj ρ Φ hρ

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct

end
