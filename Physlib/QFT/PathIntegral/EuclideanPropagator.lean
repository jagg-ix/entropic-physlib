/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.Coercivity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Euclidean propagator, Yukawa screening, and heat-kernel propagators

Propagator content built from `path_integral_damping`:

* `euclidean_propagator k² m² λ = 1/(k² + m² + λ)` — Euclidean propagator
  with an entropic-damping shift `λ > 0` (Eq. 75).
* `effective_mass m² λ = √(m² + λ)` — entropic mass shift, monotone in
  `λ` (`effective_mass_increases`, Eq. 76).
* `yukawa_potential M r = exp(−M·r)/r` — Yukawa profile, with the
  screening-length-decreases theorem
  (`screening_length_decreases`).
* `heat_kernel_propagator t m² = exp(−m²·t)` and the entropically-damped
  variant `damped_heat_propagator t m² λ = exp(−(m² + λ)·t)`, with
  positivity, the unit bound (`damped_heat_propagator_le_one`), and the
  factorisation `damped_heat = heat_kernel · exp(−λ·t)`.

All theorems are proof-complete under the standard library assumptions.

## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
- **Grosche 1988** — *Path integration via summation of perturbation expansions*
- **Grosche 1993** — *Path integrals, hyperbolic spaces, Selberg trace formulae*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Real

/-! ## §1 — Euclidean propagator (Eq. 75) -/

/-- **Euclidean propagator** with entropic damping `λ`:
`G_E(k) = 1 / (k² + m² + λ)`.  The shift `λ > 0` shifts every pole off
the real axis and makes the propagator strictly positive. -/
def euclidean_propagator (k_sq m_sq lam : ℝ) : ℝ :=
  1 / (k_sq + m_sq + lam)

/-- The denominator of the Euclidean propagator is strictly positive
when `k², m² ≥ 0` and `λ > 0`. -/
theorem euclidean_propagator_denominator_pos
    (k_sq m_sq lam : ℝ) (hk : 0 ≤ k_sq) (hm : 0 ≤ m_sq) (hLam : 0 < lam) :
    0 < k_sq + m_sq + lam := by linarith

/-- **Eq. 75 — Euclidean propagator positivity.**  Under non-negative momentum
and mass and positive entropic damping `λ`, the Euclidean propagator is
strictly positive (in particular well-defined / non-singular). -/
theorem euclidean_propagator_pos
    (k_sq m_sq lam : ℝ) (hk : 0 ≤ k_sq) (hm : 0 ≤ m_sq) (hLam : 0 < lam) :
    0 < euclidean_propagator k_sq m_sq lam := by
  unfold euclidean_propagator
  exact div_pos one_pos
    (euclidean_propagator_denominator_pos k_sq m_sq lam hk hm hLam)

/-! ## §2 — Effective mass and Yukawa screening (Eq. 76) -/

/-- **Effective mass** `M_eff = √(m² + λ)` — the entropically shifted mass. -/
def effective_mass (m_sq lam : ℝ) : ℝ := Real.sqrt (m_sq + lam)

/-- **Yukawa profile** `G_E(r) = exp(−M·r)/r`. -/
def yukawa_potential (M r : ℝ) : ℝ := Real.exp (- M * r) / r

/-- **Eq. 76 — effective mass increases with entropic damping.**  Larger
entropic damping `λ` gives a larger effective mass. -/
theorem effective_mass_increases
    (m_sq lam₁ lam₂ : ℝ) (hm : 0 ≤ m_sq) (h1 : 0 ≤ lam₁) (h2 : lam₁ < lam₂) :
    effective_mass m_sq lam₁ < effective_mass m_sq lam₂ := by
  unfold effective_mass
  apply Real.sqrt_lt_sqrt
  · exact add_nonneg hm h1
  · linarith

/-- **Eq. 76 — screening length decreases with entropic damping.**  At a
fixed range `r > 0`, larger entropic damping suppresses the Yukawa profile
more strongly. -/
theorem screening_length_decreases
    (m_sq lam₁ lam₂ r : ℝ)
    (hm : 0 ≤ m_sq) (h1 : 0 < lam₁) (h2 : lam₁ < lam₂) (hr : 0 < r) :
    yukawa_potential (effective_mass m_sq lam₂) r <
      yukawa_potential (effective_mass m_sq lam₁) r := by
  unfold yukawa_potential
  have hmass : effective_mass m_sq lam₁ < effective_mass m_sq lam₂ :=
    effective_mass_increases m_sq lam₁ lam₂ hm (le_of_lt h1) h2
  have hnum : Real.exp (-(effective_mass m_sq lam₂) * r) <
      Real.exp (-(effective_mass m_sq lam₁) * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [hmass, hr]
  have hr_inv : 0 < 1 / r := one_div_pos.mpr hr
  have hmul := mul_lt_mul_of_pos_right hnum hr_inv
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-! ## §3 — Heat-kernel propagators -/

/-- **Heat-kernel propagator** `K(t) = exp(−m²·t)` — the standard
imaginary-time scalar propagator. -/
def heat_kernel_propagator (t m_sq : ℝ) : ℝ :=
  Real.exp (-(m_sq * t))

/-- **Entropically-damped heat propagator** `exp(−(m² + λ)·t)` — the heat kernel
shifted by the entropic damping `λ`. -/
def damped_heat_propagator (t m_sq lam : ℝ) : ℝ :=
  Real.exp (-(m_sq + lam) * t)

/-- The damped heat propagator is strictly positive. -/
theorem damped_heat_propagator_pos (t m_sq lam : ℝ) :
    0 < damped_heat_propagator t m_sq lam :=
  Real.exp_pos _

/-- The damped heat propagator is bounded by `1` under `t, m², λ ≥ 0`. -/
theorem damped_heat_propagator_le_one
    (t m_sq lam : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    damped_heat_propagator t m_sq lam ≤ 1 := by
  unfold damped_heat_propagator
  have hnonpos : -(m_sq + lam) * t ≤ 0 := by nlinarith
  calc Real.exp (-(m_sq + lam) * t)
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
    _ = 1 := Real.exp_zero

/-- **Heat-kernel factorisation**: the damped heat propagator factorises
into the bare heat kernel times the entropic damping `exp(−λ·t)`. -/
theorem damped_heat_factorization (t m_sq lam : ℝ) :
    damped_heat_propagator t m_sq lam =
      heat_kernel_propagator t m_sq * Real.exp (-(lam * t)) := by
  unfold damped_heat_propagator heat_kernel_propagator
  have hsplit : -(m_sq + lam) * t = (-(m_sq * t)) + (-(lam * t)) := by ring
  rw [hsplit, Real.exp_add]

/-- **Stokes diffusion kernel = entropic heat kernel.**

The per-Fourier-mode Stokes diffusion semigroup of the incompressible
Navier–Stokes equations is `S_k(t) = exp(−ν·k²·t)`, with kinematic
viscosity `ν > 0` and wave number `k` (so `k² ≥ 0`).  This is exactly
the `heat_kernel_propagator` with squared mass `m² := ν · k²` — the
Euclidean / Wick-rotated kernel of QFT specialised to the
diffusive sector of NS. -/
theorem stokesKernel_eq_heatKernel (ν k_sq t : ℝ) :
    Real.exp (-(ν * k_sq) * t) = heat_kernel_propagator t (ν * k_sq) := by
  unfold heat_kernel_propagator
  congr 1; ring

/-- **NS Stokes kernel positivity** (a direct consequence of the
heat-kernel identification + exponential positivity). -/
theorem stokesKernel_pos (ν k_sq t : ℝ) :
    0 < Real.exp (-(ν * k_sq) * t) := Real.exp_pos _

/-- **NS Stokes kernel with entropic damping**: the additional
non-negative damping `λ > 0` shifts the Stokes diffusion to
`exp(−(ν·k² + λ)·t)`, exactly `damped_heat_propagator t (ν·k²) λ`. -/
theorem stokesKernel_with_entropic_damping_eq_dampedHeat
    (ν k_sq lam t : ℝ) :
    Real.exp (-(ν * k_sq + lam) * t) =
      damped_heat_propagator t (ν * k_sq) lam := rfl

/-! ## §4 — QFT-consistency umbrella -/

/-- **QFT consistency theorem.**  Path integrals with complex action
`S = S_R + i·S_I`, satisfying a coercivity bound `S_I ≥ C·‖φ‖²` and an
entropic damping `λ > 0`, are simultaneously:

* exponentially UV-damped at the path level
  (`coercivity_implies_exponential_damping`);
* equipped with a strictly positive Euclidean propagator
  (`euclidean_propagator_pos`);
* monotone-screened by the entropic damping
  (`effective_mass_increases`).

No new axioms; this theorem simultaneously establishes the three
independent consequences. -/
theorem qft_consistency
    {Φ : Type*} [NormedAddCommGroup Φ]
    (S_I : Φ → ℝ) (ℏ k_sq m_sq lam : ℝ)
    (hℏ : 0 < ℏ) (hk : 0 ≤ k_sq) (hm : 0 ≤ m_sq) (hLam : 0 < lam)
    (coer : CoercivityCondition (Φ := Φ))
    (h_bound : ∀ φ : Φ, coer.C * ‖φ‖ ^ 2 ≤ S_I φ) :
    (∀ φ : Φ, path_integral_damping ℏ (S_I φ) ≤
                Real.exp (- coer.C * ‖φ‖ ^ 2 / ℏ)) ∧
    (0 < euclidean_propagator k_sq m_sq lam) ∧
    (∀ lam' > lam, effective_mass m_sq lam < effective_mass m_sq lam') := by
  refine ⟨?_, euclidean_propagator_pos k_sq m_sq lam hk hm hLam, ?_⟩
  · exact fun φ =>
      coercivity_implies_exponential_damping S_I ℏ hℏ coer φ (h_bound φ)
  · intro lam' hLam'
    exact effective_mass_increases m_sq lam lam' hm (le_of_lt hLam) hLam'

end Physlib.QFT.PathIntegral

end
