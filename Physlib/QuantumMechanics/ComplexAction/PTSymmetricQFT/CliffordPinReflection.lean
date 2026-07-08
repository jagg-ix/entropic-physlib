/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.CliffordAlgebra
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover

/-!
# Greaves–Thomas Appendix B: Clifford algebras and the Pin reflection cover

Formalizes Appendix B of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) — the Clifford-algebra
description of the covering groups — and links it to the repo's existing Dirac Clifford algebra
(`Relativity.CliffordAlgebra`) and to the `SL(2,ℂ)` cover of §7 (`PTSymmetricQFT.SL2CCover`).

Appendix B.1/B.3: the real Clifford algebra `Cℓ_ℝ` is built from `T M` by the relation `vw + wv = 2η(v,w)`
(`Cℓ` is its complexification, with `η_ℂ`). The Pin group consists of products of unit vectors, and the
covering map `π : P → L(C)` sends a unit vector `v` to the **reflection in the hyperplane orthogonal to
`v`**, `π(v) : x ↦ x − 2·η(x,v)/η(v,v)·v`.

* **§A — the Clifford form is the Minkowski norm** (`minkBilin`, `diracForm_eq_minkBilin_self`,
  `diracForm_eq_det_bracket`). The repo's `Relativity.CliffordAlgebra.diracForm` is `η(x,x) =
  x₀²−x₁²−x₂²−x₃²`; this is exactly the `SL(2,ℂ)` cover's Minkowski norm `det⟨x⟩` of
  `PTSymmetricQFT.SL2CCover.det_bracket` — the Clifford form of Appendix B and the determinant of the
  Hermitian encoding of §7 are the same quadratic form.
* **§B — the Clifford relation `vw + wv = 2η(v,w)`** (`polar_diracForm`, `clifford_relation`,
  `clifford_sq`). The defining Appendix-B.1 relation, from `CliffordAlgebra.ι_mul_ι_add_swap`: the
  anticommutator of two generators is `2η(v,w)` (the polar form of `diracForm`), and `v² = η(v,v)`.
* **§C — the Pin reflection covering map** (`reflect`, `reflect_isometry`, `reflect_involutive`,
  `reflect_preserves_diracForm`). `π(v)` is an involution and an isometry of `η` — a Lorentz
  transformation — realizing the covering map `P → L(C)`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, Appendix B (Clifford algebras, the Pin group,
  the reflection covering map `π(v)`).
* Repo dependencies: `Relativity.CliffordAlgebra` (`diracForm`, the Dirac `γ`-matrix Clifford algebra);
  `PTSymmetricQFT.SL2CCover.det_bracket` (the `SL(2,ℂ)` Minkowski norm); `CliffordAlgebra.ι_mul_ι_add_swap`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover
open spaceTime.γ

/-! ## §A — the Clifford quadratic form is the Minkowski norm -/

/-- **The Minkowski bilinear form** `η(x,y) = x₀y₀ − x₁y₁ − x₂y₂ − x₃y₃` — half the polar form of the
Clifford `diracForm`. -/
def minkBilin (x y : Fin 4 → ℝ) : ℝ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- **The Clifford `diracForm` is the Minkowski norm** `diracForm x = η(x,x)`. -/
theorem diracForm_eq_minkBilin_self (x : Fin 4 → ℝ) : diracForm x = minkBilin x x := by
  simp only [diracForm_apply, minkBilin]

/-- **[Link to §7] The Clifford form equals the `SL(2,ℂ)` cover's Minkowski norm** `diracForm x = det⟨x⟩`.
The Appendix-B Clifford quadratic form and the determinant of the §7 Hermitian encoding
(`PTSymmetricQFT.SL2CCover.bracket`) are one and the same. -/
theorem diracForm_eq_det_bracket (x : Fin 4 → ℝ) :
    ((diracForm x : ℝ) : ℂ) = (bracket x).det := by
  rw [det_bracket]; push_cast [diracForm_apply]; ring

/-! ## §B — the Clifford relation `vw + wv = 2η(v,w)` -/

/-- **The polar form of `diracForm` is `2η`** `polar(v,w) = 2η(v,w)`. -/
theorem polar_diracForm (v w : Fin 4 → ℝ) :
    QuadraticMap.polar diracForm v w = 2 * minkBilin v w := by
  simp only [QuadraticMap.polar, diracForm_apply, minkBilin, Pi.add_apply]; ring

/-- **[Appendix B.1/B.3] The Clifford relation** `vw + wv = 2η(v,w)`. The anticommutator of two Clifford
generators is twice the Minkowski inner product — the defining relation of `Cℓ_ℝ` (and `Cℓ` over `η_ℂ`),
from `CliffordAlgebra.ι_mul_ι_add_swap`. -/
theorem clifford_relation (v w : Fin 4 → ℝ) :
    CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm w
      + CliffordAlgebra.ι diracForm w * CliffordAlgebra.ι diracForm v
      = algebraMap ℝ (CliffordAlgebra diracForm) (2 * minkBilin v w) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, polar_diracForm]

/-- **The diagonal Clifford relation** `v² = η(v,v)` — a unit vector squares to `±1`, the basis of the Pin
group. -/
theorem clifford_sq (v : Fin 4 → ℝ) :
    CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm v
      = algebraMap ℝ (CliffordAlgebra diracForm) (diracForm v) :=
  CliffordAlgebra.ι_sq_scalar diracForm v

/-! ## §C — the Pin reflection covering map -/

/-- **[Appendix B covering map] The reflection in the hyperplane orthogonal to `v`**
`π(v) : x ↦ x − 2·η(x,v)/η(v,v)·v` — the image of a unit vector under the Pin covering map `P → L(C)`. -/
noncomputable def reflect (v x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x - (2 * minkBilin x v / minkBilin v v) • v

/-- **`π(v)` is an isometry of `η`** `η(π(v)x, π(v)y) = η(x,y)` — the reflection preserves the Minkowski
inner product, so `π(v)` is a Lorentz transformation. -/
theorem reflect_isometry (v x y : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    minkBilin (reflect v x) (reflect v y) = minkBilin x y := by
  have hv' : v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 ≠ 0 := by simp only [pow_two]; exact hv
  simp only [minkBilin, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hv']
  ring

/-- **`π(v)` is an involution** `π(v) ∘ π(v) = id` — reflecting twice returns the original (`π(v)² = 1`). -/
theorem reflect_involutive (v x : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    reflect v (reflect v x) = x := by
  have hv' : v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 ≠ 0 := by simp only [pow_two]; exact hv
  funext i
  simp only [reflect, minkBilin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> · field_simp [hv']; ring

/-- **`π(v)` preserves the Clifford form** `diracForm (π(v)x) = diracForm x` — the reflection is a Lorentz
isometry of the Minkowski norm `= det⟨x⟩`, the covering-map property `π : P → L(C)`. -/
theorem reflect_preserves_diracForm (v x : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    diracForm (reflect v x) = diracForm x := by
  rw [diracForm_eq_minkBilin_self, diracForm_eq_minkBilin_self, reflect_isometry v x x hv]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection

end
