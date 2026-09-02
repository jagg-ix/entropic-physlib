/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungGeometricResolution
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Projective Schrödinger = Riccati / Möbius flow on CP¹

Makes the Möbius structure of `ElectronMadelungGeometricResolution` §D **dynamical**. The qubit spinor `χ(t)`
evolves by the linear Schrödinger equation `χ̇ = A·χ` (with `A = −(i/ℏ)H` the `2×2` generator). Projected to the
`CP¹` ray coordinate `w = χ₀/χ₁ = weylRatio χ`, the evolution becomes:

* **infinitesimally, the Riccati equation** — `ẇ = −A₁₀ w² + (A₀₀ − A₁₁) w + A₀₁` (`projective_schrodinger_riccati`,
  the quotient rule on `χ₀/χ₁`), a quadratic (Riccati) vector field on `CP¹`;
* **finitely, the Möbius action** — the evolution operator `U` (a `2×2` matrix) acts on the ray by a Möbius
  transformation `w ↦ (U₀₀w + U₀₁)/(U₁₀w + U₁₁)` (`weylRatio_mulVec_mobius`): the induced action on
  `weylRatio` is exactly the `SL(2,ℂ)` boundary Möbius map of `WeylSpinorPoincareSphere`.

So the projective Schrödinger equation on `CP¹` is the Riccati flow whose one-parameter group is the Möbius
action — the same Möbius that acts on the Bloch base, the twistor direction, and the Riemann sphere in §D, now
realized as the **time evolution** of the electron qubit. The static conformal symmetry of the resolution *is*
the dynamics.

* **§A — the Riccati equation** (`riccatiFlow`, `projective_schrodinger_riccati`).
* **§B — the Möbius flow** (`weylRatio_mulVec_mobius`).
* **§C — assembled** (`projective_schrodinger_riccati_mobius`).

**Honest layering.** §A is the exact quotient-rule calculus (`HasDerivAt.div`) giving the Riccati vector field;
§B reuses `sl2c_weylRatio` (the boundary Möbius) with the `2×2` `mulVec` expansion. The content is the
identification: the projective Schrödinger flow's generator is Riccati and its integral flow is Möbius, the same
`SL(2,ℂ)` of the geometric resolution. No claim of existence/uniqueness of the ODE solution is made. No new
axioms.

## References

* J. F. Riccati; the Möbius group as the flow of a Riccati equation. Repo carriers:
  `AdSCFT.WeylSpinorPoincareSphere` (`weylRatio`, `sl2c_weylRatio`),
  `HorizonCell.ElectronMadelungGeometricResolution`.


-/

set_option autoImplicit false

open scoped Matrix MatrixGroups
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius


/-- **The Riccati vector field** on `CP¹` for a `2×2` Schrödinger generator `A` (`A = −(i/ℏ)H`):
`ẇ = −A₁₀ w² + (A₀₀ − A₁₁) w + A₀₁` — the quadratic (Riccati) field the ray coordinate obeys. -/
def riccatiFlow (A00 A01 A10 A11 w : ℂ) : ℂ :=
  -A10 * w ^ 2 + (A00 - A11) * w + A01

/-- **[The projective Schrödinger equation is a Riccati equation].** If the qubit spinor components `χ₀, χ₁`
evolve by the linear Schrödinger equation `χ̇ = A·χ` (`χ̇₀ = A₀₀χ₀ + A₀₁χ₁`, `χ̇₁ = A₁₀χ₀ + A₁₁χ₁`) and
`χ₁ ≠ 0`, then the `CP¹` ray coordinate `w = χ₀/χ₁` obeys the **Riccati equation**
`ẇ = riccatiFlow A (χ₀/χ₁) = −A₁₀ w² + (A₀₀−A₁₁) w + A₀₁`. The Schrödinger flow, projected to the ray, is a
quadratic vector field. -/
lemma projective_schrodinger_riccati (χ₀ χ₁ : ℝ → ℂ) (A00 A01 A10 A11 : ℂ) (t : ℝ)
    (h₀ : HasDerivAt χ₀ (A00 * χ₀ t + A01 * χ₁ t) t)
    (h₁ : HasDerivAt χ₁ (A10 * χ₀ t + A11 * χ₁ t) t) (hχ₁ : χ₁ t ≠ 0) :
    HasDerivAt (fun s => χ₀ s / χ₁ s) (riccatiFlow A00 A01 A10 A11 (χ₀ t / χ₁ t)) t := by
  have quotient_derivative := h₀.div h₁ hχ₁
  have riccati_derivative_eq : riccatiFlow A00 A01 A10 A11 (χ₀ t / χ₁ t)
      = ((A00 * χ₀ t + A01 * χ₁ t) * χ₁ t - χ₀ t * (A10 * χ₀ t + A11 * χ₁ t)) / χ₁ t ^ 2 := by
    unfold riccatiFlow
    field_simp
    ring
  rw [riccati_derivative_eq]
  change HasDerivAt (χ₀ / χ₁) _ t
  exact quotient_derivative


/-- **[The finite Schrödinger flow on `CP¹` is a Möbius transformation].** The evolution operator `M`
(a `2×2` matrix, `M ∈ SL(2,ℂ)`) acts on the ray coordinate by the boundary Möbius map: the `CP¹` coordinate of
the evolved spinor `M·χ` is the Möbius image of `weylRatio χ`,
`weylRatio (M·χ) = M • weylRatio χ = (M₀₀χ₀+M₀₁χ₁)/(M₁₀χ₀+M₁₁χ₁)`. The Riccati flow integrates to the `SL(2,ℂ)`
Möbius action of `WeylSpinorPoincareSphere`. -/
lemma weylRatio_mulVec_mobius (M : SL(2, ℂ)) (χ : Fin 2 → ℂ) (hχ₁ : χ 1 ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * χ 1 ≠ 0) :
    weylRatio ((M : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ χ) = M.toGL • weylRatio χ := by
  have hmv0 : ((M : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ χ) 0
      = (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * χ 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hmv1 : ((M : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ χ) 1
      = (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * χ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * χ 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [weylRatio, if_neg (by rw [hmv1]; exact hden), hmv0, hmv1,
    show weylRatio χ = ((χ 0 / χ 1 : ℂ) : OnePoint ℂ) from by rw [weylRatio, if_neg hχ₁],
    sl2c_weylRatio M (χ 0) (χ 1) hχ₁ hden]


/-- **[Projective Schrödinger = Riccati generator, Möbius flow].** For the qubit spinor evolving by
`χ̇ = A·χ` with `χ₁ ≠ 0`, and an evolution operator `M ∈ SL(2,ℂ)`:

* the ray coordinate `w = χ₀/χ₁` obeys the **Riccati equation** `ẇ = −A₁₀w² + (A₀₀−A₁₁)w + A₀₁`;
* the finite flow is the **Möbius action** `weylRatio (M·χ) = M • weylRatio χ`.

The projective Schrödinger equation on `CP¹` is the Riccati flow integrating to the `SL(2,ℂ)` Möbius group — the
static conformal symmetry of the Madelung resolution realized as the electron qubit's time evolution. -/
lemma projective_schrodinger_riccati_mobius
    (χ₀ χ₁ : ℝ → ℂ) (A00 A01 A10 A11 : ℂ) (t : ℝ)
    (h₀ : HasDerivAt χ₀ (A00 * χ₀ t + A01 * χ₁ t) t)
    (h₁ : HasDerivAt χ₁ (A10 * χ₀ t + A11 * χ₁ t) t) (hχ₁ : χ₁ t ≠ 0)
    (M : SL(2, ℂ)) (ψ : Fin 2 → ℂ) (hψ₁ : ψ 1 ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * ψ 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * ψ 1 ≠ 0) :
    HasDerivAt (fun s => χ₀ s / χ₁ s) (riccatiFlow A00 A01 A10 A11 (χ₀ t / χ₁ t)) t
      ∧ weylRatio ((M : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ψ) = M.toGL • weylRatio ψ :=
  ⟨projective_schrodinger_riccati χ₀ χ₁ A00 A01 A10 A11 t h₀ h₁ hχ₁,
    weylRatio_mulVec_mobius M ψ hψ₁ hden⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius

end
