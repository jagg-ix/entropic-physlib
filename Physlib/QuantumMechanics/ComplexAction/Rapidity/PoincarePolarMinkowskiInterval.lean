/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Proving the polar coordinate is a Minkowski interval, not a spherical coordinate

`TimeOperator.HyperbolicPoincareLorentzMisra` *asserted* that the Bogoliubov/Poincaré polar coordinate
`S₃ = u² − v² = ξ/E` is hyperbolic (Lorentzian) rather than spherical. This file **proves** that
recognition from the data `E² = ξ² + Δ²`, **without assuming the conclusion**.

## The honest starting point (no overclaim)

The normalized polarisation spinor genuinely lies on a **sphere**: `S₁² + S₂² + S₃² = S₀²`
(`Hopf.StokesSpinorIsomorphism.poincare_sphere`, already proven). So `S₃` *is* a legitimate spherical
coordinate, ranging over `[−1, 1]`. Membership in `[−1, 1]` alone does **not** decide the geometry —
a spherical coordinate `cos 2φ` and a Minkowski velocity `tanh η` both live there. What decides it
is the **invariant** the physical transformation preserves and the **composition law** the
coordinate obeys. We prove four discriminators, each derived from `E² − ξ² = Δ²`:

1. **The gap is the Minkowski invariant.** `lorentzianForm (E + iξ) = E² − ξ² = Δ²`
   (`TimeOperator.HyperbolicPoincareLorentzMisra.bogoliubov_energyVector_lorentzianForm`). The physical invariant
   is the *gap* (`Δ`, the BCS/Dirac mass), and it is the Minkowski form `E² − ξ²`, **not** the
   Euclidean form `E² + ξ²`. The boost preserves it (`lorentzBoost_preserves_form`); a rotation
   preserves the Euclidean form instead (`rotation_preserves_euclidean`). So the gap-fixing symmetry
   is the boost `SO(1,1)`, not the rotation `SO(2)`.
2. **Strictly inside the light cone.** For a genuine gap `Δ ≠ 0`, `|ξ/E| < 1` *strictly*
   (`velocity_abs_lt_one`) — the timelike (massive) condition; the coordinate reaches the boundary
   `|ξ/E| = 1` *only* in the massless limit `Δ = 0` (`velocity_eq_one_iff_massless`). A free
   spherical coordinate reaches its poles `±1`; this one cannot, because the gap holds it inside the
   cone.
3. **Rapidity derived, not assumed.** `∃ η, ξ = Δ sinh η ∧ E = Δ cosh η` (`exists_rapidity`, via
   `arsinh`): the energy vector is provably a **boost of the rest frame** `(Δ, 0)`, and
   `ξ/E = tanh η` (`velocity_eq_tanh`).
4. **Relativistic velocity-addition law.** Under a boost, `ξ/E = tanh η` composes by
   `(β₁ + β₂)/(1 + β₁β₂)` (`tanh_add`), staying sub-luminal (`velocity_addition_lt_one`) — the
   non-compact hyperbolic law, structurally distinct from compact spherical rotation.

## Main results

* `rotation_preserves_euclidean` — a rotation preserves `E² + ξ²` (sphere), not the gap.
* `velocity_abs_lt_one` / `velocity_eq_one_iff_massless` — strict light-cone confinement by the gap.
* `exists_rapidity` / `velocity_eq_tanh` — the rapidity (boost from rest) derived from the data.
* `tanh_add` / `velocity_addition_lt_one` — the relativistic velocity-addition composition law.
* `polar_coordinate_is_minkowski_interval` — the bundled proof (i)+(ii)+(iii).
* `minkowski_not_spherical_composition` — the bundled discriminator (gap = Minkowski invariant under
  the boost, Euclidean under rotation; velocity-addition composition).

## References

* H. Poincaré (sphere) and the Poincaré disk model. N. N. Bogoljubov (1958).
* `TimeOperator.HyperbolicPoincareLorentzMisra`, `Hopf.StokesSpinorIsomorphism`, `Bogoliubov.Transformation`
  (this development); `Real.arsinh`, `Real.cosh_sq_sub_sinh_sq` (Mathlib).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

namespace Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval


/-- **A Euclidean rotation** of a `(E, ξ)` pair by angle `φ`. -/
def euclidRotation (φ E ξ : ℝ) : ℝ × ℝ :=
  (Real.cos φ * E - Real.sin φ * ξ, Real.sin φ * E + Real.cos φ * ξ)

/-- **A rotation preserves the Euclidean form** `E² + ξ²` (the sphere invariant), **not** the gap
`E² − ξ²`. Since the Bogoliubov invariant is the gap (`bogoliubov_energyVector_lorentzianForm`,
`E² − ξ² = Δ²`), the rotation is the *wrong* symmetry — the gap-preserving one is the Lorentz boost
(`lorentzBoost_preserves_form`). This is the geometry-deciding contrast: Minkowski `E² − ξ²` vs
Euclidean `E² + ξ²`. -/
lemma rotation_preserves_euclidean (φ E ξ : ℝ) :
    (euclidRotation φ E ξ).1 ^ 2 + (euclidRotation φ E ξ).2 ^ 2 = E ^ 2 + ξ ^ 2 := by
  simp only [euclidRotation]
  linear_combination (E ^ 2 + ξ ^ 2) * Real.sin_sq_add_cos_sq φ


/-- **Strictly sub-luminal for a genuine gap** `|ξ/E| < 1` (`Δ ≠ 0`): the timelike (massive)
condition. The positive gap `Δ² = E² − ξ² > 0` forces `ξ² < E²` *strictly* — the coordinate is in
the **open** interval `(−1, 1)`, never reaching the poles `±1`. A free spherical coordinate *does*
reach its poles; this one is held inside the light cone by the gap. -/
lemma velocity_abs_lt_one (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    |ξ / bogoliubovEnergy ξ Δ| < 1 := by
  have hE : 0 < bogoliubovEnergy ξ Δ := by
    unfold bogoliubovEnergy; exact Real.sqrt_pos.mpr (by positivity)
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  rw [abs_div, abs_of_pos hE, div_lt_one hE, ← Real.sqrt_sq_eq_abs]
  unfold bogoliubovEnergy
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith [hΔ2]

/-- **On the null boundary in the massless limit** `|ξ/E| = 1` (`Δ = 0`, `ξ ≠ 0`): with no gap the
energy vector is light-like, `E = |ξ|`, and `ξ/E = ±1` — the poles. So `|ξ/E| < 1 ⟺ Δ ≠ 0`
(timelike ⟺ massive): the bound is the **light cone**, not a sphere. -/
lemma velocity_eq_one_iff_massless (ξ : ℝ) (hξ : ξ ≠ 0) :
    |ξ / bogoliubovEnergy ξ 0| = 1 := by
  unfold bogoliubovEnergy
  rw [show ξ ^ 2 + (0 : ℝ) ^ 2 = ξ ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_div, abs_abs,
    div_self (abs_ne_zero.mpr hξ)]


/-- **The rapidity exists, derived from the data** (not assumed): for `Δ > 0` there is a rapidity
`η` with `ξ = Δ sinh η` and `E = Δ cosh η`. So `(E, ξ)` is a **Lorentz boost of the rest vector**
`(Δ, 0)` — the hyperbolic structure is *constructed*, with `η = arsinh(ξ/Δ)`. -/
lemma exists_rapidity (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ η : ℝ, ξ = Δ * Real.sinh η ∧ bogoliubovEnergy ξ Δ = Δ * Real.cosh η := by
  have hΔ0 : Δ ≠ 0 := hΔ.ne'
  refine ⟨Real.arsinh (ξ / Δ), ?_, ?_⟩
  · rw [Real.sinh_arsinh]; field_simp
  · have hsinξ : Δ * Real.sinh (Real.arsinh (ξ / Δ)) = ξ := by
      rw [Real.sinh_arsinh]; field_simp
    have hcs : Real.cosh (Real.arsinh (ξ / Δ)) ^ 2
        = 1 + Real.sinh (Real.arsinh (ξ / Δ)) ^ 2 := by
      have := Real.cosh_sq_sub_sinh_sq (Real.arsinh (ξ / Δ)); linarith
    have key : ξ ^ 2 + Δ ^ 2 = (Δ * Real.cosh (Real.arsinh (ξ / Δ))) ^ 2 := by
      rw [mul_pow, hcs, mul_add, mul_one,
        show Δ ^ 2 * Real.sinh (Real.arsinh (ξ / Δ)) ^ 2
          = (Δ * Real.sinh (Real.arsinh (ξ / Δ))) ^ 2 by ring, hsinξ]
      ring
    unfold bogoliubovEnergy
    rw [key, Real.sqrt_sq (mul_nonneg hΔ.le (Real.cosh_pos _).le)]

/-- **The polar coordinate is the hyperbolic tangent of the rapidity** `ξ/E = tanh η` (the boost
velocity). -/
lemma velocity_eq_tanh (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ η : ℝ, ξ / bogoliubovEnergy ξ Δ = Real.tanh η := by
  obtain ⟨η, hξ, hE⟩ := exists_rapidity ξ Δ hΔ
  exact ⟨η, by rw [hE, hξ, Real.tanh_eq_sinh_div_cosh, mul_div_mul_left _ _ hΔ.ne']⟩


/-- **The relativistic velocity-addition law** `tanh(η₁ + η₂) = (β₁ + β₂)/(1 + β₁β₂)` (`βᵢ = tanh
ηᵢ`): under a boost (rapidity addition) the polar coordinate composes by the Lorentz `SO(1,1)` law —
the hyperbolic composition. A spherical coordinate composes by trigonometric angle-addition instead. -/
lemma tanh_add (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) := by
  have hca : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  have hcb : Real.cosh b ≠ 0 := (Real.cosh_pos b).ne'
  have hd : Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b ≠ 0 := by
    rw [← Real.cosh_add]; exact (Real.cosh_pos _).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_add, Real.cosh_add]
  field_simp

/-- **Velocity addition stays sub-luminal**: if `|β₁| < 1` and `|β₂| < 1` then
`|(β₁ + β₂)/(1 + β₁β₂)| < 1`. Composing boosts never reaches the light cone `±1` — the hyperbolic
orbit is non-compact and the open interval is *closed under composition*. A spherical rotation, by
contrast, freely reaches its poles. -/
lemma velocity_addition_lt_one {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    |(β₁ + β₂) / (1 + β₁ * β₂)| < 1 := by
  rw [abs_lt] at h₁ h₂ ⊢
  have hp₁ : 0 < 1 + β₁ := by linarith [h₁.1]
  have hp₂ : 0 < 1 + β₂ := by linarith [h₂.1]
  have hm₁ : 0 < 1 - β₁ := by linarith [h₁.2]
  have hm₂ : 0 < 1 - β₂ := by linarith [h₂.2]
  have hden : 0 < 1 + β₁ * β₂ := by nlinarith [mul_pos hp₁ hp₂, mul_pos hm₁ hm₂]
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith [mul_pos hp₁ hp₂]
  · rw [div_lt_iff₀ hden]; nlinarith [mul_pos hm₁ hm₂]


/-- **The polar coordinate is a Minkowski interval — proven from `E² = ξ² + Δ²`.** For a genuine
gap `Δ > 0`:

* **(i)** it is the velocity of the timelike energy vector, `lorentzianForm (E + iξ) = Δ²` (the gap
  is the invariant mass);
* **(ii)** it is *strictly* inside the light cone, `|ξ/E| < 1` (timelike — not a sphere pole);
* **(iii)** it is `tanh η` for a rapidity `η` derived from the data, with `(E, ξ)` a boost of the
  rest frame `(Δ, 0)`.

None of this is assumed: each part is derived from `E² − ξ² = Δ²`. -/
lemma polar_coordinate_is_minkowski_interval (ξ Δ : ℝ) (hΔ : 0 < Δ) :
    lorentzianForm ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) = Δ ^ 2
      ∧ |ξ / bogoliubovEnergy ξ Δ| < 1
      ∧ ∃ η : ℝ, ξ / bogoliubovEnergy ξ Δ = Real.tanh η
          ∧ ξ = Δ * Real.sinh η ∧ bogoliubovEnergy ξ Δ = Δ * Real.cosh η := by
  refine ⟨bogoliubov_energyVector_lorentzianForm ξ Δ, velocity_abs_lt_one ξ Δ hΔ.ne', ?_⟩
  obtain ⟨η, hξ, hE⟩ := exists_rapidity ξ Δ hΔ
  exact ⟨η, by rw [hE, hξ, Real.tanh_eq_sinh_div_cosh, mul_div_mul_left _ _ hΔ.ne'], hξ, hE⟩

/-- **The geometry-deciding discriminator (Minkowski, not spherical).** Three facts that together
fix the geometry as hyperbolic:

* the **boost** preserves the gap `E² − ξ²` (the Bogoliubov invariant `= Δ²`);
* a **rotation** preserves the Euclidean `E² + ξ²` instead — so it is *not* the gap-fixing symmetry;
* the polar coordinate `β = ξ/E` composes by the **relativistic velocity-addition** (boost) law.

Hence the symmetry preserving the physical gap is the boost `SO(1,1)` and the coordinate is a
hyperbolic (Minkowski) velocity — not a spherical angle. -/
lemma minkowski_not_spherical_composition :
    (∀ θ t x : ℝ, (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2)
      ∧ (∀ φ E ξ : ℝ,
          (euclidRotation φ E ξ).1 ^ 2 + (euclidRotation φ E ξ).2 ^ 2 = E ^ 2 + ξ ^ 2)
      ∧ (∀ a b : ℝ,
          Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b)) :=
  ⟨lorentzBoost_preserves_form, rotation_preserves_euclidean, tanh_add⟩

end Physlib.QuantumMechanics.ComplexAction.Rapidity.PoincarePolarMinkowskiInterval

end

end
