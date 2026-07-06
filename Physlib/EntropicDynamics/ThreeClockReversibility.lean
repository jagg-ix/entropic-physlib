/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Three clocks by the sign of the spectral rate: reversible vs entropic

The reversibility axis of the three time concepts in quantum theory, made exact through the spectral law
`‖exp(λt)‖ = exp(Re λ · t)`:

| clock | reversible? | spectral signature |
|---|---|---|
| unitary parameter time (`H_R`, Stone) | yes | `Re λ = 0` |
| modular / thermal time (`K = −ln ρ`, Connes–Rovelli) | yes (isospectral) | `Re λ = 0` |
| **entropic time** (`Σ Lⱼ†Lⱼ`, GKLS) | **no** | **`Re λ < 0`** |

The complex spectral rate `λ` splits **orthogonally**: `Re λ` fixes the magnitude (decay — the entropic axis) and
`Im λ` the phase (oscillation — the unitary/modular axis). Reversibility is exactly `Re λ = 0`; the entropic clock
is the distinct, irreversible one, on the negative-real axis conjugate to the imaginary (modular/unitary) axis.

References: A. Connes, C. Rovelli, Class. Quantum Grav. 11 (1994) 2899; G. Lindblad 1976. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.EntropicDynamics.ThreeClockReversibility

/-- **The flow magnitude depends only on the real (entropic) part** `‖exp(λt)‖ = exp(Re λ · t)`. `Re λ` (entropic
decay) sets the magnitude; `Im λ` (unitary/modular oscillation) sets only the phase — the two clocks act on
orthogonal components of the spectral rate. -/
theorem flow_norm_from_re (l : ℂ) (t : ℝ) : ‖Complex.exp (l * t)‖ = Real.exp (l.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **Norm-preserving (reversible) iff the rate is imaginary** `‖exp λ‖ = 1 ↔ Re λ = 0` — the unitary/modular
clocks preserve the norm; any `Re λ ≠ 0` breaks reversibility. -/
theorem flow_unitary_iff_re_zero (l : ℂ) : ‖Complex.exp l‖ = 1 ↔ l.re = 0 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]

/-- **Strictly contracting (irreversible) iff the rate has negative real part** `‖exp λ‖ < 1 ↔ Re λ < 0` — the
entropic-clock signature. -/
theorem flow_contracts_iff_re_neg (l : ℂ) : ‖Complex.exp l‖ < 1 ↔ l.re < 0 := by
  rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp]

/-- **A real generator gives a reversible (unitary) flow** `‖exp(−iκt)‖ = 1`. The unitary time (`H_R`) and the
modular time (`K = −ln ρ`, Hermitian, real spectrum) both have real eigenvalues `κ`, hence a purely imaginary rate
`−iκ` (`Re = 0`) and a norm-preserving flow. -/
theorem reversible_generator_flow_unitary (κ t : ℝ) :
    ‖Complex.exp (-Complex.I * (κ : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- **A dissipative generator gives an irreversible (contracting) flow** `‖exp(λt)‖ < 1` for `Re λ < 0`, `t > 0`.
The entropic clock (`Σ L†L` in the effective generator) has `Re λ < 0`, so the flow strictly loses norm — the arrow
of time of the entropic clock. -/
theorem entropic_generator_flow_contracts (l : ℂ) (t : ℝ) (hl : l.re < 0) (ht : 0 < t) :
    ‖Complex.exp (l * t)‖ < 1 := by
  rw [flow_norm_from_re, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hl ht)

end Physlib.EntropicDynamics.ThreeClockReversibility

end
