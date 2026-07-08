/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Non-perturbative effects in matrix models and D-branes (Alexandrov §VII)

The asymptotic string-perturbation series is non-perturbatively ambiguous; the ambiguities are
**D-instanton** effects, computed in the matrix model from the string equation and matched, from the string
side, by open-string disk amplitudes on Zamolodchikov's `(1,1)` Liouville D-brane (Alexandrov,
hep-th/0311273, Ch. VII). The winding (Sine–Liouville / black-hole) case builds on Ch. IV
(`[[project_alexandrov_mqm_thesis]]`, `MatrixQuantumMechanics.WindingBlackHole`).

* **§A — Painlevé-I non-perturbative ambiguity** (Eqs. VII.3–VII.5). For the `(2,3)` model (pure gravity) the
  free energy obeys Painlevé-I `u² − ⅙u'' = μ`. The difference `ε = ũ − u` of two solutions obeys exactly
  `ε'' = 12uε + 6ε²` (`painleveI_perturbation`); to leading order this is the linearized instanton equation
  `ε'' = 12uε` (Eq. VII.5).
* **§B — D-instanton coefficient: matrix model = Liouville** (Eqs. VII.10, VII.51). The non-perturbative
  coefficient `r_{m,n} = −4 sin(πm/p) sin(πn/(p+1))` from the matrix model equals the Liouville D-brane result
  `−2C sin(πm/p) sin(πn/(p+1))` at `C = 2` (`rLiouville_eq_rMatrixModel`).
* **§C — Liouville central charge** (Eqs. VII.39–VII.41). With background charge `Q = b + 1/b`,
  `c_L = 1 + 6Q² = 13 + 6(b² + b⁻²)` (`liouville_centralCharge_background`); for the `(p,q)` minimal model
  (`b = √(p/q)`, so `Q² = (p+q)²/(pq)`) the matter+Liouville central charge is `26`
  (`minimalModel_total_central_charge`).
* **§D — black-hole D-instanton phase** (Eqs. VII.25–VII.27). At the black-hole radius `R = 3/2` the instanton
  condition `sin(2φ/3) = √2 sin(φ/3)` reduces, via the double-angle identity, to `cos(φ/3) = √2/2`
  (`blackHole_instanton_phase`) — giving `φ₀ = 3π/4`.

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. VII, Eqs. (VII.3)–(VII.5), (VII.10), (VII.25)–(VII.27), (VII.39)–(VII.41),
  (VII.51).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.NonperturbativeDBranes

/-! ## §A — Painlevé-I non-perturbative ambiguity (Eqs. VII.3–VII.5) -/

/-- **[Painlevé-I instanton equation, Eqs. VII.3 → VII.5]** If `u` and `ũ = u + ε` both solve Painlevé-I
`u² − ⅙u'' = μ` (with second derivatives `uPP`, `uPP + εPP`), then the difference obeys exactly
`ε'' = 12uε + 6ε²`. To leading order in the (exponentially small) ambiguity `ε` this is the linearized
equation `ε'' = 12uε` (Eq. VII.5) governing the non-perturbative correction. -/
theorem painleveI_perturbation (u ε μ uPP εPP : ℝ)
    (hu : u ^ 2 - (1 / 6) * uPP = μ)
    (hue : (u + ε) ^ 2 - (1 / 6) * (uPP + εPP) = μ) :
    εPP = 12 * u * ε + 6 * ε ^ 2 := by
  linear_combination 6 * hu - 6 * hue

/-! ## §B — D-instanton coefficient: matrix model = Liouville (Eqs. VII.10, VII.51) -/

/-- **The matrix-model non-perturbative coefficient** `r_{m,n} = −4 sin(πm/p) sin(πn/(p+1))` (Eq. VII.10) for
the `(p,p+1)` unitary minimal model — labelled by Kac indices `(m,n)`. -/
noncomputable def rMatrixModel (m n p : ℝ) : ℝ :=
  -4 * Real.sin (Real.pi * m / p) * Real.sin (Real.pi * n / (p + 1))

/-- **The Liouville D-brane non-perturbative coefficient** `r_{m,n} = −2C sin(πm/p) sin(πn/(p+1))` (Eq. VII.51)
from the `(1,1)×(m,n)` D-instanton disk amplitude. -/
noncomputable def rLiouville (C m n p : ℝ) : ℝ :=
  -2 * C * Real.sin (Real.pi * m / p) * Real.sin (Real.pi * n / (p + 1))

/-- **[Matrix model = Liouville D-instanton, Eqs. VII.10 = VII.51]** the two computations of the
non-perturbative coefficient agree when the Liouville normalization constant is `C = 2`. -/
theorem rLiouville_eq_rMatrixModel (m n p : ℝ) :
    rLiouville 2 m n p = rMatrixModel m n p := by
  unfold rLiouville rMatrixModel
  ring

/-! ## §C — Liouville central charge (Eqs. VII.39–VII.41) -/

/-- **[Liouville central charge, Eqs. VII.39–VII.40]** with background charge `Q = b + 1/b`,
`c_L = 1 + 6Q² = 13 + 6(b² + b⁻²)`. -/
theorem liouville_centralCharge_background (b : ℝ) (hb : b ≠ 0) :
    1 + 6 * (b + 1 / b) ^ 2 = 13 + 6 * (b ^ 2 + 1 / b ^ 2) := by
  field_simp
  ring

/-- **[Total central charge = 26, Eqs. VII.39–VII.41]** for the `(p,q)` minimal model coupled to gravity
(`b = √(p/q)`, so `Q² = (p+q)²/(pq)`) the matter central charge `c = 1 − 6(p−q)²/(pq)` and the Liouville
central charge `c_L = 1 + 6Q²` sum to the critical value `26`. -/
theorem minimalModel_total_central_charge (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (1 - 6 * (p - q) ^ 2 / (p * q)) + (1 + 6 * ((p + q) ^ 2 / (p * q))) = 26 := by
  field_simp [hp.ne', hq.ne']
  ring

/-! ## §D — black-hole D-instanton phase (Eqs. VII.25–VII.27) -/

/-- **[Black-hole instanton phase, Eqs. VII.25 → VII.27]** at the black-hole radius `R = 3/2` the
instanton-quantization condition `sin(2φ/3) = √2 sin(φ/3)` (Eq. VII.25) reduces, by the double-angle identity
`sin 2x = 2 sin x cos x`, to `cos(φ/3) = √2/2` (Eq. VII.27) whenever `sin(φ/3) ≠ 0`. -/
theorem blackHole_instanton_phase (φ : ℝ) (hsin : Real.sin (φ / 3) ≠ 0) :
    Real.sin (2 * φ / 3) = Real.sqrt 2 * Real.sin (φ / 3)
      ↔ Real.cos (φ / 3) = Real.sqrt 2 / 2 := by
  rw [show (2 : ℝ) * φ / 3 = 2 * (φ / 3) from by ring, Real.sin_two_mul]
  constructor
  · intro h
    have hc : 2 * Real.cos (φ / 3) = Real.sqrt 2 :=
      mul_left_cancel₀ hsin (by linear_combination h)
    linarith
  · intro h
    rw [h]; ring

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.NonperturbativeDBranes

end
