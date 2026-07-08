/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Navier–Stokes two-fiber decomposition: polar fibration and the curl ⊣ Biot–Savart retraction

Ports the genuine, assumption-free **mathematical kernel** of two Navier–Stokes categorical files
(`CategoryTheoryLib`, `NSTwoFiberCategoricalBridge`). As with `Hopf.DualSphereSobolevPerfectSquare` /
`Hopf.DualSphereFiberDecomposition`, the source files' own underlying spaces are *placeholders*
(`TopModuleCat.of ℝ ℝ`, so the analytic morphisms are `True`-bodied), and they encode `Bool`-valued
`LabeledClaim` status records; those are not portable. What *is* genuine:

* **the polar (spherical) fibration** `ℝ³ \ {0} ≃ ℝ₊ × S²` (`polarDecomposition`), `v ↦ (‖v‖, v/‖v‖)` — the
  magnitude–direction decomposition that splits a nonzero vorticity vector into its length and its
  point on the geometric sphere `S²` (the direction fiber `ξ = ω/|ω|` of `Hopf.DualSphereFiberDecomposition`);
* **the velocity ⟷ vorticity two-fiber retraction**: on `T³` the Biot–Savart map is a left inverse of the
  curl, `BS ∘ curl = id` (the Helmholtz decomposition for divergence-free periodic fields). A left
  inverse makes `curl` injective and `BS` surjective (velocity is *determined* by its vorticity), and the
  composite `curl ∘ BS` is an **idempotent** — the Leray projector onto realizable vorticities
  (`twoFiber_curl_injective`, `twoFiber_biotSavart_surjective`, `twoFiber_leray_idempotent`).

* **§A — the polar fibration** (`polarDecomposition`).
* **§B — the curl ⊣ Biot–Savart retraction** (`twoFiber_curl_injective`,
  `twoFiber_biotSavart_surjective`, `twoFiber_leray_idempotent`, `twoFiber_decomposition`).

## References

* The polar/spherical decomposition `ℝⁿ \ {0} ≅ ℝ₊ × Sⁿ⁻¹`; the Helmholtz/Leray decomposition on `T³`.
  Source (kernel only; underlying spaces are `ℝ`-stubs + `Bool` status records):
  `NavierStokes/CategoryTheoryLib.lean`, `NavierStokes/NSTwoFiberCategoricalBridge.lean`. Companion
  kernels: `Hopf.DualSphereFiberDecomposition`, `Hopf.DualSphereSobolevPerfectSquare`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.TwoFiberPolarDecomposition

/-! ## §A — the polar fibration `ℝ³ \ {0} ≃ ℝ₊ × S²` -/

/-- **The polar (spherical) decomposition** `ℝ³ \ {0} ≃ ℝ₊ × S²`, `v ↦ (‖v‖, v/‖v‖)`. A nonzero vector
splits uniquely into its magnitude `‖v‖ > 0` and its direction `v/‖v‖` on the unit sphere — the
magnitude–direction fibration whose direction fiber is the geometric vorticity sphere. -/
noncomputable def polarDecomposition :
    {v : EuclideanSpace ℝ (Fin 3) // v ≠ 0} ≃
      {r : ℝ // 0 < r} × {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1} where
  toFun v :=
    ⟨⟨‖v.1‖, norm_pos_iff.mpr v.2⟩,
     ⟨(‖v.1‖⁻¹ : ℝ) • v.1, by
       rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
       exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr v.2)⟩⟩
  invFun p :=
    ⟨(p.1.1 : ℝ) • p.2.1, smul_ne_zero (ne_of_gt p.1.2) (by
      rw [← norm_ne_zero_iff, p.2.2]; norm_num)⟩
  left_inv v := by
    apply Subtype.ext
    show (‖v.1‖ : ℝ) • ((‖v.1‖ : ℝ)⁻¹ • v.1) = v.1
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr v.2), one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      show ‖(p.1.1 : ℝ) • p.2.1‖ = p.1.1
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt p.1.2), p.2.2, mul_one]
    · apply Subtype.ext
      show ‖(p.1.1 : ℝ) • p.2.1‖⁻¹ • ((p.1.1 : ℝ) • p.2.1) = p.2.1
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt p.1.2), p.2.2, mul_one, smul_smul,
        inv_mul_cancel₀ (ne_of_gt p.1.2), one_smul]

/-! ## §B — the curl ⊣ Biot–Savart two-fiber retraction -/

variable {V Ω : Type*} (curl : V → Ω) (biotSavart : Ω → V)

/-- **[Curl is injective] velocity is determined by its vorticity.** If Biot–Savart is a left inverse of
the curl (`BS ∘ curl = id`, Helmholtz on `T³`), then the curl is injective — two divergence-free fields
with the same vorticity coincide. -/
theorem twoFiber_curl_injective (h : Function.LeftInverse biotSavart curl) :
    Function.Injective curl :=
  h.injective

/-- **[Biot–Savart is surjective] every velocity is realized.** The Biot–Savart map (left inverse of the
curl) is surjective onto the velocity fiber. -/
theorem twoFiber_biotSavart_surjective (h : Function.LeftInverse biotSavart curl) :
    Function.Surjective biotSavart :=
  h.surjective

/-- **[The Leray projector is idempotent] `(curl ∘ BS)² = curl ∘ BS`.** The composite `curl ∘ Biot–Savart`
is a projector onto the curl-realizable vorticities — the Leray/Helmholtz projector. -/
theorem twoFiber_leray_idempotent (h : Function.LeftInverse biotSavart curl) (ω : Ω) :
    curl (biotSavart (curl (biotSavart ω))) = curl (biotSavart ω) := by
  rw [h (biotSavart ω)]

/-- **[The Navier–Stokes two-fiber retraction, assembled].** With Biot–Savart a left inverse of the curl
(Helmholtz on `T³`): the curl is injective (velocity determined by vorticity), Biot–Savart is surjective,
and `curl ∘ Biot–Savart` is idempotent (the Leray projector). -/
theorem twoFiber_decomposition (h : Function.LeftInverse biotSavart curl) :
    Function.Injective curl
      ∧ Function.Surjective biotSavart
      ∧ ∀ ω, curl (biotSavart (curl (biotSavart ω))) = curl (biotSavart ω) :=
  ⟨h.injective, h.surjective, fun ω => twoFiber_leray_idempotent curl biotSavart h ω⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.TwoFiberPolarDecomposition

end
