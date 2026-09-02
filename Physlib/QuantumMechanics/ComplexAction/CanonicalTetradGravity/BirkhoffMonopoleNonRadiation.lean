/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Birkhoff's theorem: the spherical exterior is static — the monopole does not radiate

Jebsen (1921) / Birkhoff (1923): a spherically symmetric solution of the vacuum
Einstein equations is static and equal to the Schwarzschild exterior.  Corollary —
the *monopole non-radiation theorem*: whatever a spherically symmetric source does
(pulsate, collapse, annihilate its constituents into radiation as in
`PairAnnihilationGravitationalWave`), the exterior field cannot change: the `ℓ = 0`
mode emits no gravitational radiation.

For the spherically symmetric metric `ds² = −e^{2Φ(t,r)}c²dt² + e^{2Λ(t,r)}dr² + r²dΩ²`
the vacuum Einstein equations reduce to (d'Inverno §14.6, Wald §6.1):

* `G_tr = (2/r)·e^{…}·∂_tΛ = 0`  — the time-freeze equation,
* `G_tt ∝ (1/r²)·∂_r[r(1 − e^{−2Λ})] = 0`  — the mass equation,
* `G_tt − G_rr ∝ ∂_r(Φ + Λ) = 0`  — the lapse equation.

The reduction (the curvature computation for the ansatz) is the isolated analytic
input, exactly as the Green inversion `hGreen` in `GWRetardedGreen`; what is
formalized is everything downstream — the *integration* of the reduced system:

* **§A — the freeze.** `birkhoff_time_freeze`: the raw `G_tr` component kills `∂_tΛ`
  with no degenerate branch (`e^x ≠ 0`).  `mass_time_independent` /
  `mass_radius_independent`: the Misner–Sharp mass `m = (r/2)(1 − e^{−2Λ})` has both
  partial derivatives zero.
* **§B — Schwarzschild.** `birkhoff_mass_constant`: `m` is one constant `M` on all of
  spacetime (mean value theorem twice); `birkhoff_schwarzschild_form`:
  `e^{−2Λ(t,r)} = 1 − 2M/r` — static, one-parameter; and in terms of the repo's
  Schwarzschild radius, `e^{−2Λ} = 1 − r_s/r` (`birkhoff_schwarzschild_radius_form`,
  welding `SemiClassical.schwarzschildRadius`).
* **§C — staticity of the lapse.** `birkhoff_lapse_profile`: `Φ(t,r) = Φ(t,r₀) +
  Λ(t,r₀) − Λ(t,r)` — the radial profile of the lapse is `−Λ` rigidly;
  `birkhoff_lapse_time_gauge`: the residual time-dependence `Φ(t,r) − Φ(t,r₀)` is
  frozen — what remains is a global `t`-reparametrization, pure gauge.
* **§D — no monopole radiation.** `monopole_non_radiation`: two spherically
  symmetric vacuum histories with the same mass constant have *identical* exteriors
  for all time.  A star may pulsate, a dust ball may annihilate into a radiation
  ball (`annihilation_doubles_poisson_source` changes the interior source *profile*,
  not the conserved exterior mass) — the exterior metric cannot tell: zero
  gravitational signal escapes at `ℓ = 0`.  Gravitational radiation begins at the
  quadrupole.

Honest layering: the reduction of the Einstein tensor to the three displayed
components for the spherical ansatz is *quoted*, not computed (the analytic input);
the time-reparametrization `t̃ = ∫e^{g(t)}dt` absorbing the gauge of §C is described,
not constructed; the quadrupole formula (the mode that *does* radiate) is not
formalized.

## References

* J. T. Jebsen, Ark. Mat. Astron. Fys. 15 (1921) 18; G. D. Birkhoff, *Relativity and
  Modern Physics*, Harvard (1923), p. 253.
* R. d'Inverno, *Introducing Einstein's Relativity*, Oxford (1992), §14.6; R. M.
  Wald, *General Relativity*, Chicago (1984), §6.1.
* C. W. Misner, D. H. Sharp, Phys. Rev. 136 (1964) B571 (the mass function).
* Repo modules used: `SemiClassical.SchwarzschildVerlinde` (`schwarzschildRadius`),
  `CanonicalTetradGravity.GWRetardedGreen` (the radiating counterpoint),
  `CanonicalTetradGravity.PairAnnihilationGravitationalWave` (the spherical source
  whose annihilation this theorem silences).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.BirkhoffMonopoleNonRadiation

open Physlib.Relativity.SemiClassical


/-- **The Misner–Sharp mass function** `m(t,r) = (r/2)(1 − e^{−2Λ(t,r)})` — the mass
enclosed at radius `r`, read off the radial metric function `Λ`. -/
noncomputable def massFunction (Λ : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  2⁻¹ * (r * (1 - Real.exp (-2 * Λ t r)))

/-! ## §A — the freeze: both partials of the mass function vanish -/

/-- **[The `G_tr` equation kills `∂_tΛ` outright]** `(2/r)·e^x·∂_tΛ = 0 → ∂_tΛ = 0`
for `r ≠ 0` — the exponential prefactor of the Einstein-tensor component never
vanishes, so the time-freeze has no degenerate branch. -/
theorem birkhoff_time_freeze (r x dΛ : ℝ) (hr : r ≠ 0)
    (h : 2 / r * Real.exp x * dΛ = 0) : dΛ = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (div_ne_zero two_ne_zero hr)
    · exact absurd h'' (Real.exp_ne_zero x)
  · exact h'

/-- **[`∂_t m = 0`]** the time-freeze `∂_tΛ = 0` propagates through the mass
function: the enclosed mass at every radius is time-independent. -/
theorem mass_time_independent (Λ : ℝ → ℝ → ℝ) (t r : ℝ)
    (h : HasDerivAt (fun s => Λ s r) 0 t) :
    HasDerivAt (fun s => massFunction Λ s r) 0 t := by
  have h1 : HasDerivAt (fun s => -2 * Λ s r) (-2 * 0) t := h.const_mul (-2)
  have h2 : HasDerivAt (fun s => Real.exp (-2 * Λ s r))
      (Real.exp (-2 * Λ t r) * (-2 * 0)) t := h1.exp
  have h3 : HasDerivAt (fun s => 1 - Real.exp (-2 * Λ s r))
      (-(Real.exp (-2 * Λ t r) * (-2 * 0))) t := h2.const_sub 1
  have h4 := (h3.const_mul r).const_mul (2 : ℝ)⁻¹
  simpa [massFunction] using h4

/-- **[`∂_r m = 0`]** the `G_tt` vacuum equation `∂_r[r(1 − e^{−2Λ})] = 0` says the
mass function is radius-independent — no mass in the vacuum region. -/
theorem mass_radius_independent (Λ : ℝ → ℝ → ℝ) (t r : ℝ)
    (h : HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ t ρ))) 0 r) :
    HasDerivAt (fun ρ => massFunction Λ t ρ) 0 r := by
  simpa [massFunction] using h.const_mul (2 : ℝ)⁻¹

/-! ## §B — the Schwarzschild exterior -/

/-- **[Birkhoff, mass step] `m(t,r) = M` — one constant on all of spacetime.** Both
partial derivatives of the mass function vanish (the reduced vacuum equations), so
by the mean value theorem — first along `t` at fixed `r`, then along `r` — the
enclosed mass is a single constant: the *only* datum the exterior remembers. -/
theorem birkhoff_mass_constant (Λ : ℝ → ℝ → ℝ)
    (hE1 : ∀ t r, HasDerivAt (fun s => Λ s r) 0 t)
    (hE2 : ∀ t r, HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ t ρ))) 0 r)
    (t r t₀ r₀ : ℝ) :
    massFunction Λ t r = massFunction Λ t₀ r₀ := by
  have hstep1 : massFunction Λ t r = massFunction Λ t₀ r := by
    have hdiff : Differentiable ℝ (fun s => massFunction Λ s r) :=
      fun s => (mass_time_independent Λ s r (hE1 s r)).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff
      (fun s => (mass_time_independent Λ s r (hE1 s r)).deriv) t t₀
  have hstep2 : massFunction Λ t₀ r = massFunction Λ t₀ r₀ := by
    have hdiff : Differentiable ℝ (fun ρ => massFunction Λ t₀ ρ) :=
      fun ρ => (mass_radius_independent Λ t₀ ρ (hE2 t₀ ρ)).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff
      (fun ρ => (mass_radius_independent Λ t₀ ρ (hE2 t₀ ρ)).deriv) r r₀
  exact hstep1.trans hstep2

/-- **[Birkhoff] `e^{−2Λ(t,r)} = 1 − 2M/r`** — the radial metric function is the
*static* Schwarzschild factor, for all `t`, with the one constant
`M = massFunction Λ t₀ r₀`: spherical symmetry plus vacuum leaves no functional
freedom, hence no dynamics, in the exterior. -/
theorem birkhoff_schwarzschild_form (Λ : ℝ → ℝ → ℝ)
    (hE1 : ∀ t r, HasDerivAt (fun s => Λ s r) 0 t)
    (hE2 : ∀ t r, HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ t ρ))) 0 r)
    (t r t₀ r₀ : ℝ) (hr : r ≠ 0) :
    Real.exp (-2 * Λ t r) = 1 - 2 * massFunction Λ t₀ r₀ / r := by
  have hM := birkhoff_mass_constant Λ hE1 hE2 t r t₀ r₀
  rw [← hM]
  unfold massFunction
  field_simp
  ring

/-- **[Birkhoff in Schwarzschild-radius form] `e^{−2Λ} = 1 − r_s/r`** — when the mass
constant is `GM/c²` (geometric mass), the exterior factor is `1 − r_s/r` with
`r_s = 2GM/c²` the `schwarzschildRadius` of the Verlinde arc: the same one-parameter
exterior used in the holographic-screen bookkeeping. -/
theorem birkhoff_schwarzschild_radius_form (Λ : ℝ → ℝ → ℝ)
    (hE1 : ∀ t r, HasDerivAt (fun s => Λ s r) 0 t)
    (hE2 : ∀ t r, HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ t ρ))) 0 r)
    (t r t₀ r₀ M G c : ℝ) (hr : r ≠ 0)
    (hM : massFunction Λ t₀ r₀ = G * M / c ^ 2) :
    Real.exp (-2 * Λ t r) = 1 - schwarzschildRadius M G c / r := by
  rw [birkhoff_schwarzschild_form Λ hE1 hE2 t r t₀ r₀ hr, hM, schwarzschildRadius]
  ring_nf

/-! ## §C — staticity of the lapse -/

/-- **[The lapse profile is `−Λ` rigidly] `Φ(t,r) = Φ(t,r₀) + Λ(t,r₀) − Λ(t,r)`.**
Integrating the lapse equation `∂_r(Φ + Λ) = 0` along `r`: the radial dependence of
`Φ` is exactly `−Λ`; only an `r`-independent offset `g(t) = Φ(t,r₀) + Λ(t,r₀)`
remains. -/
theorem birkhoff_lapse_profile (Φ Λ : ℝ → ℝ → ℝ)
    (hE3 : ∀ t r, HasDerivAt (fun ρ => Φ t ρ + Λ t ρ) 0 r) (t r r₀ : ℝ) :
    Φ t r = Φ t r₀ + Λ t r₀ - Λ t r := by
  have hdiff : Differentiable ℝ (fun ρ => Φ t ρ + Λ t ρ) :=
    fun ρ => (hE3 t ρ).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun ρ => (hE3 t ρ).deriv) r r₀
  linarith

/-- **[The residual time-dependence is pure gauge] `∂_t(Φ(t,r) − Φ(t,r₀)) = 0`.**
The lapse profile equals `Λ(t,r₀) − Λ(t,r)` (`birkhoff_lapse_profile`), and `Λ` is
frozen (`hE1`), so the *only* time-dependence left in `Φ` is the `r`-independent
offset — absorbable into a global reparametrization `t̃ = ∫e^{g(t)}dt`: the metric is
static, not merely stationary. -/
theorem birkhoff_lapse_time_gauge (Φ Λ : ℝ → ℝ → ℝ)
    (hE1 : ∀ t r, HasDerivAt (fun s => Λ s r) 0 t)
    (hE3 : ∀ t r, HasDerivAt (fun ρ => Φ t ρ + Λ t ρ) 0 r) (t r r₀ : ℝ) :
    HasDerivAt (fun s => Φ s r - Φ s r₀) 0 t := by
  have h : HasDerivAt (fun s => Λ s r₀ - Λ s r) (0 - 0) t :=
    (hE1 t r₀).sub (hE1 t r)
  have heq : (fun s => Φ s r - Φ s r₀) = fun s => Λ s r₀ - Λ s r := by
    funext s
    have := birkhoff_lapse_profile Φ Λ hE3 s r r₀
    linarith
  rw [heq]
  simpa using h

/-! ## §D — the monopole does not radiate -/

/-- **[Monopole non-radiation]** two spherically symmetric vacuum exteriors with the
same mass constant are *identical for all time*.  Whatever the interior does —
pulsation, collapse, or the pair annihilation of
`PairAnnihilationGravitationalWave` (which doubles the interior source *profile*,
`annihilation_doubles_poisson_source`, while conserving the total mass) — the
exterior metric function cannot change: no gravitational signal escapes in the
`ℓ = 0` mode.  Gravitational radiation begins at the quadrupole. -/
theorem monopole_non_radiation (Λ₁ Λ₂ : ℝ → ℝ → ℝ)
    (hE1₁ : ∀ t r, HasDerivAt (fun s => Λ₁ s r) 0 t)
    (hE2₁ : ∀ t r, HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ₁ t ρ))) 0 r)
    (hE1₂ : ∀ t r, HasDerivAt (fun s => Λ₂ s r) 0 t)
    (hE2₂ : ∀ t r, HasDerivAt (fun ρ => ρ * (1 - Real.exp (-2 * Λ₂ t ρ))) 0 r)
    (t₁ r₁ t₂ r₂ : ℝ)
    (hM : massFunction Λ₁ t₁ r₁ = massFunction Λ₂ t₂ r₂) :
    ∀ t r, r ≠ 0 → Real.exp (-2 * Λ₁ t r) = Real.exp (-2 * Λ₂ t r) := by
  intro t r hr
  rw [birkhoff_schwarzschild_form Λ₁ hE1₁ hE2₁ t r t₁ r₁ hr,
    birkhoff_schwarzschild_form Λ₂ hE1₂ hE2₂ t r t₂ r₂ hr, hM]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.BirkhoffMonopoleNonRadiation

end
