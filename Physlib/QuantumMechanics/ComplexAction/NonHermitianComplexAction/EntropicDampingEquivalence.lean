/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.EntropicDamping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Nagao–Nielsen complex action ↔ EPT entropic damping are the same weight

The Nagao–Nielsen Complex Action Theory and this development's entropic-time (EPT) damping
*look* like different formalisms, because the path weight is written differently:

* **Nagao–Nielsen** weight a path by the **complex phase** `e^{iS/ℏ}`, with a complex
  action `S = S_R + i·S_I` (*Formulation of Complex Action Theory*, Prog. Theor. Phys.
  **126**(6) 2011, §1, Eq. (1.1)).
* **EPT** (`RelationalTime.EntropicDamping`, §2) weights an open conditional state by the
  **real** Cameron–Martin factor `amplitude = e^{−S_I/2ℏ}`, with probability damping
  `probability = e^{−S_I/ℏ}` — a manifestly real, dissipative weight.

These are the **same object**: `e^{iS/ℏ} = e^{iS_R/ℏ}·e^{−S_I/ℏ}` factors into a
**unit-modulus phase** `e^{iS_R/ℏ}` (the reversible/unitary part) times the **EPT real
weight** `e^{−S_I/ℏ}`. The imaginary part of the Nagao–Nielsen action is exactly the EPT
imaginary action, and the EPT damping is precisely the modulus of the Nagao–Nielsen weight.

* `nnPathWeight` — the Nagao–Nielsen weight `e^{iS/ℏ}`.
* `nnPathWeight_eq_phase_mul_damping` — `e^{iS/ℏ} = e^{iS_R/ℏ}·(e^{−S_I/ℏ} : ℂ)`: the
  factorization into phase × EPT real weight.
* `norm_nnPhase` — `‖e^{iS_R/ℏ}‖ = 1`: the phase is reversible (unit modulus).
* `norm_nnPathWeight` — `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}`: the modulus is the EPT weight.
* `nnPathWeight_norm_eq_probability` / `nnHalfWeight_norm_eq_amplitude` — the bridge to the
  EPT structures: `‖e^{iS/ℏ}‖ = D.probability` and `‖e^{iS/2ℏ}‖ = D.amplitude` for any
  `ImaginaryActionDamping D` whose imaginary action is `S_I`.

So the two formalisms agree on the only thing physically observable from the weight — its
modulus, the survival/probability factor — and differ only by the unitary phase that EPT
folds into the reversible part. This is the compatibility statement.

References: K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor.
Phys. **126**(6) (2011) 1021–1049, §1, Eq. (1.1), doi:10.1143/PTP.126.1021. Page & Wootters
1983, Phys. Rev. D **27**, 2885 (the EPT damping's unitary base).
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

open QuantumMechanics.RelationalTime

/-- **The Nagao–Nielsen path weight** `e^{iS/ℏ}` with complex action `S = S_R + i·S_I`. -/
noncomputable def nnPathWeight (S_R S_I ℏ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((S_R : ℂ) + Complex.I * (S_I : ℂ)) / (ℏ : ℂ))

/-- The real part of the Nagao–Nielsen exponent is `−S_I/ℏ` (the `i² = −1` turns the
imaginary action into real damping). -/
theorem nnExponent_re (S_R S_I ℏ : ℝ) :
    (Complex.I * ((S_R : ℂ) + Complex.I * (S_I : ℂ)) / (ℏ : ℂ)).re = -(S_I / ℏ) := by
  rw [show Complex.I * ((S_R : ℂ) + Complex.I * (S_I : ℂ))
      = -(S_I : ℂ) + (S_R : ℂ) * Complex.I by rw [mul_add, ← mul_assoc, Complex.I_mul_I]; ring,
    Complex.div_ofReal_re]
  simp [neg_div]

/-- **Factorization: `e^{iS/ℏ} = e^{iS_R/ℏ}·(e^{−S_I/ℏ} : ℂ)`.** The Nagao–Nielsen complex
weight is a unit-modulus phase times the EPT real damping weight. -/
theorem nnPathWeight_eq_phase_mul_damping (S_R S_I ℏ : ℝ) :
    nnPathWeight S_R S_I ℏ
      = Complex.exp (Complex.I * (S_R : ℂ) / (ℏ : ℂ)) * (Real.exp (-(S_I / ℏ)) : ℂ) := by
  rw [nnPathWeight, show Complex.I * ((S_R : ℂ) + Complex.I * (S_I : ℂ)) / (ℏ : ℂ)
      = Complex.I * (S_R : ℂ) / (ℏ : ℂ) + ((-(S_I / ℏ) : ℝ) : ℂ) by
        rw [mul_add, ← mul_assoc, Complex.I_mul_I]; push_cast; ring,
    Complex.exp_add, Complex.ofReal_exp]

/-- **The Nagao–Nielsen phase `e^{iS_R/ℏ}` is reversible**: unit modulus. -/
theorem norm_nnPhase (S_R ℏ : ℝ) : ‖Complex.exp (Complex.I * (S_R : ℂ) / (ℏ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp, show Complex.I * (S_R : ℂ) / (ℏ : ℂ)
      = ((S_R / ℏ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simp

/-- **The modulus of the Nagao–Nielsen weight is the EPT real weight**:
`‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}`. This is the physically observable survival factor — identical
in both formalisms. -/
theorem norm_nnPathWeight (S_R S_I ℏ : ℝ) :
    ‖nnPathWeight S_R S_I ℏ‖ = Real.exp (-(S_I / ℏ)) := by
  rw [nnPathWeight, Complex.norm_exp, nnExponent_re]

/-! ## Bridge to the EPT damping structures (`ImaginaryActionDamping`) -/

/-- **`‖e^{iS/ℏ}‖ = D.probability`.** For any EPT imaginary-action damping `D`, the modulus
of the Nagao–Nielsen weight (with imaginary action `D.S_I`, Planck constant `D.ℏ`) is
exactly the EPT probability-damping factor `e^{−S_I/ℏ}`. -/
theorem nnPathWeight_norm_eq_probability (D : ImaginaryActionDamping) (S_R : ℝ) :
    ‖nnPathWeight S_R D.S_I D.ℏ‖ = D.probability := by
  rw [norm_nnPathWeight, ImaginaryActionDamping.probability]

/-- **`‖e^{iS/2ℏ}‖ = D.amplitude`.** The half-exponent Nagao–Nielsen weight reproduces the
EPT dissipative *amplitude* factor `e^{−S_I/2ℏ}` (whose square is the probability). -/
theorem nnHalfWeight_norm_eq_amplitude (D : ImaginaryActionDamping) (S_R : ℝ) :
    ‖Complex.exp (Complex.I * ((S_R : ℂ) + Complex.I * (D.S_I : ℂ)) / (2 * (D.ℏ : ℂ)))‖
      = D.amplitude := by
  rw [Complex.norm_exp, ImaginaryActionDamping.amplitude,
    show Complex.I * ((S_R : ℂ) + Complex.I * (D.S_I : ℂ))
      = -(D.S_I : ℂ) + (S_R : ℂ) * Complex.I by rw [mul_add, ← mul_assoc, Complex.I_mul_I]; ring]
  congr 1
  rw [show (2 * (D.ℏ : ℂ)) = ((2 * D.ℏ : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
  simp [neg_div]

end Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

end
