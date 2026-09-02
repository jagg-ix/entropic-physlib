/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
public import Physlib.Mathematics.LeftRiemannSum

/-!
# The BKM surrogate integral under a palinstrophy budget

Ports `NavierStokes/NSFourierAgmonBridge.lean` of the reference tree onto the physlib
carriers: the trajectory functionals live on the Fourier-field hierarchy of
`NSFieldFourierSobolevHierarchy` and the time integration on the fixed-step kernel of
`Mathematics.LeftRiemannSum`, over `ℝ`.

For a trajectory `t ↦ v(t)` of finite Fourier fields, the Beale–Kato–Majda vorticity
integral is modelled by the **surrogate** `∫(Ω + P)` — enstrophy plus palinstrophy, the
`H¹ + H²` budget richer than the tautological `∫Ω` certificate — and the entropic clocks are
`τ = (ν/ℏ)∫Ω` and its palinstrophy analogue.  The two statements:

* `bkmSurrogate_le_budget` — **the budget bound**: if the entropic palinstrophy time is
  bounded by an external budget `M`, then

    `∫(Ω + P) ≤ (ℏ/ν)·(τ + M)`.

  The budget hypothesis does real work: the enstrophy half is the definitional clock
  identity, but the palinstrophy half has no internal bound — exactly the source's
  non-tautological certificate.
* `bkmSurrogate_le_of_bandlimited` — **the band-limited collapse** (carried out here; the
  source lists it as future work): for a trajectory whose modes never exceed `k_max`, the
  Bernstein cutoff `P ≤ k_max²·Ω` of the hierarchy module integrates to
  `∫P ≤ k_max²·∫Ω`, the budget instantiates internally, and the bound closes in the
  entropic proper time alone:

    `∫(Ω + P) ≤ (ℏ/ν)·(1 + k_max²)·τ`.

**Honest layering.**  Exact kernel algebra over the fixed-step Riemann sums; "BKM
surrogate" names the structural role of the `Ω + P` budget, not the analytic
Beale–Kato–Majda `‖ω‖_{L^∞}` criterion, whose function-space form is future material — as is
the passage from the fixed-step kernel to the interval integral.

## References

* J. T. Beale, T. Kato, A. Majda, *Remarks on the breakdown of smooth solutions for the 3-D
  Euler equations*, Comm. Math. Phys. **94** (1984).  Source:
  `NavierStokes/NSFourierAgmonBridge.lean` (reference tree, own authorship), re-authored on
  the physlib hierarchy and kernel with the band-limited collapse proved.
-/

set_option autoImplicit false

open Physlib.Mathematics.LeftRiemannSum

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

namespace NSFieldFourier

variable (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ)

/-- The integrated enstrophy `∫₀ᵀ Ω dt` along a trajectory, by the fixed-step kernel. -/
noncomputable def integratedEnstrophy (T : ℝ) : ℝ :=
  leftRiemannSum N (fun t => enstrophy (traj t)) T

/-- The integrated palinstrophy `∫₀ᵀ P dt` along a trajectory. -/
noncomputable def integratedPalinstrophy (T : ℝ) : ℝ :=
  leftRiemannSum N (fun t => palinstrophy (traj t)) T

/-- **The entropic proper time** `τ = (ν/ℏ)·∫Ω` of the trajectory. -/
noncomputable def entropicProperTime (T : ℝ) : ℝ :=
  ν/ℏ * integratedEnstrophy N traj T

/-- **The entropic palinstrophy time** `(ν/ℏ)·∫P` — the quantity the external budget
bounds. -/
noncomputable def entropicPalinstrophyTime (T : ℝ) : ℝ :=
  ν/ℏ * integratedPalinstrophy N traj T

/-- **The BKM surrogate integral** `∫(Ω + P)` — the `H¹ + H²` vorticity budget. -/
noncomputable def bkmSurrogateIntegral (T : ℝ) : ℝ :=
  integratedEnstrophy N traj T + integratedPalinstrophy N traj T

/-- The integrated enstrophy in terms of the entropic proper time,
`∫Ω = (ℏ/ν)·τ`. -/
theorem integratedEnstrophy_eq_properTime (hν : ν ≠ 0) (hℏ : ℏ ≠ 0) (T : ℝ) :
    integratedEnstrophy N traj T = ℏ/ν * entropicProperTime N traj ν ℏ T := by
  unfold entropicProperTime
  field_simp

/-- **The budget bound**: under an external bound `M` on the entropic palinstrophy time,
the BKM surrogate integral is controlled by the entropic proper time plus the budget,
`∫(Ω + P) ≤ (ℏ/ν)·(τ + M)`.  The budget hypothesis is essential — the palinstrophy half
has no internal bound. -/
theorem bkmSurrogate_le_budget (hν : 0 < ν) (hℏ : 0 < ℏ) {T M : ℝ}
    (hM : entropicPalinstrophyTime N traj ν ℏ T ≤ M) :
    bkmSurrogateIntegral N traj T
      ≤ ℏ/ν * (entropicProperTime N traj ν ℏ T + M) := by
  have hP : integratedPalinstrophy N traj T ≤ ℏ/ν * M := by
    have h1 : integratedPalinstrophy N traj T
        = ℏ/ν * entropicPalinstrophyTime N traj ν ℏ T := by
      unfold entropicPalinstrophyTime
      field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hM (by positivity)
  calc bkmSurrogateIntegral N traj T
      = integratedEnstrophy N traj T + integratedPalinstrophy N traj T := rfl
    _ ≤ ℏ/ν * entropicProperTime N traj ν ℏ T + ℏ/ν * M := by
        rw [integratedEnstrophy_eq_properTime N traj ν ℏ hν.ne' hℏ.ne']
        exact add_le_add le_rfl hP
    _ = ℏ/ν * (entropicProperTime N traj ν ℏ T + M) := by ring

/-- **The band-limited collapse**: for a trajectory whose modes never exceed `k_max`, the
Bernstein cutoff `P ≤ k_max²·Ω` integrates, the palinstrophy budget instantiates internally
as `k_max²·τ`, and the surrogate bound closes in the entropic proper time alone:
`∫(Ω + P) ≤ (ℏ/ν)·(1 + k_max²)·τ`. -/
theorem bkmSurrogate_le_of_bandlimited (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax) (T : ℝ) :
    bkmSurrogateIntegral N traj T
      ≤ ℏ/ν * (1 + (kmax : ℝ)^2) * entropicProperTime N traj ν ℏ T := by
  have hpoint : ∀ t, palinstrophy (traj t) ≤ (kmax : ℝ)^2 * enstrophy (traj t) :=
    fun t => palinstrophy_le_sq_enstrophy (traj t) kmax (hfreq t)
  have hint : integratedPalinstrophy N traj T
      ≤ (kmax : ℝ)^2 * integratedEnstrophy N traj T := by
    calc integratedPalinstrophy N traj T
        ≤ leftRiemannSum N (fun t => (kmax : ℝ)^2 * enstrophy (traj t)) T :=
          leftRiemannSum_le_of_pointwise N hN _ _ T hpoint
      _ = (kmax : ℝ)^2 * integratedEnstrophy N traj T :=
          leftRiemannSum_const_mul N _ _ T
  calc bkmSurrogateIntegral N traj T
      = integratedEnstrophy N traj T + integratedPalinstrophy N traj T := rfl
    _ ≤ integratedEnstrophy N traj T + (kmax : ℝ)^2 * integratedEnstrophy N traj T :=
        add_le_add le_rfl hint
    _ = (1 + (kmax : ℝ)^2) * integratedEnstrophy N traj T := by ring
    _ = ℏ/ν * (1 + (kmax : ℝ)^2) * entropicProperTime N traj ν ℏ T := by
        rw [integratedEnstrophy_eq_properTime N traj ν ℏ hν.ne' hℏ.ne']
        ring

/-! ## The frozen entropic clock

Ports the verified core of `NavierStokes/NSFrozenClockBridge.lean` (reference tree, own
authorship): the entropic clock `τ(T) = (ν/ℏ)∫Ω` is *nonlinear* in the horizon — solution-
dependent through `Ω` — whereas T-coercive (Céa-estimate) frameworks require a *linear*
rescaled time `τ_μ = μ·T`.  Freezing the enstrophy at a ceiling `Ω₀` linearizes the clock,
and under a pointwise enstrophy ceiling the band-limited BKM surrogate bound becomes
genuinely **bilinear** in `(Ω₀, T)`.  In a Galerkin iteration the ceiling is the previous
iterate, `Ω₀ := Ω_prev`, and the clock condition is checked per iterate. -/

/-- **The frozen entropic clock** `τ_frozen(T) = (ν/ℏ)·Ω₀·T` — the entropic proper time with
the enstrophy frozen at the constant level `Ω₀`; linear in `T` with T-coercive stiffness
`μ = (ν/ℏ)·Ω₀`, in contrast with the solution-dependent `entropicProperTime`. -/
noncomputable def frozenEntropicTime (ν ℏ Ω₀ T : ℝ) : ℝ :=
  ν/ℏ * Ω₀ * T

/-- The frozen clock is linear in the horizon — the T-coercive structure `τ_μ = μ·T` that
the nonlinear entropic clock lacks. -/
theorem frozenEntropicTime_linear (Ω₀ T₁ T₂ : ℝ) :
    frozenEntropicTime ν ℏ Ω₀ (T₁ + T₂)
      = frozenEntropicTime ν ℏ Ω₀ T₁ + frozenEntropicTime ν ℏ Ω₀ T₂ := by
  unfold frozenEntropicTime
  ring

/-- **A pointwise enstrophy ceiling freezes the clock**: if `Ω(t) ≤ Ω₀` along the
trajectory, the entropic proper time is dominated by the frozen clock,
`τ(T) ≤ (ν/ℏ)·Ω₀·T` — pointwise bound into the kernel, then the constant sum undershoots
the product. -/
theorem entropicProperTime_le_frozen (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    {Ω₀ : ℝ} (hΩ₀ : 0 ≤ Ω₀) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t, enstrophy (traj t) ≤ Ω₀) :
    entropicProperTime N traj ν ℏ T ≤ frozenEntropicTime ν ℏ Ω₀ T := by
  unfold entropicProperTime frozenEntropicTime integratedEnstrophy
  have h1 : leftRiemannSum N (fun t => enstrophy (traj t)) T
      ≤ leftRiemannSum N (fun _ => Ω₀) T :=
    leftRiemannSum_le_of_pointwise N hN _ _ T hbound
  have h2 : leftRiemannSum N (fun _ => Ω₀) T ≤ Ω₀ * T :=
    leftRiemannSum_const_le N hN hΩ₀ hT
  have hcoeff : (0:ℝ) ≤ ν/ℏ := by positivity
  calc ν/ℏ * leftRiemannSum N (fun t => enstrophy (traj t)) T
      ≤ ν/ℏ * (Ω₀ * T) := mul_le_mul_of_nonneg_left (h1.trans h2) hcoeff
    _ = ν/ℏ * Ω₀ * T := by ring

/-- **The frozen-clock BKM bound from the clock condition** (the source's core form): if
the actual entropic proper time is dominated by the frozen clock — the Galerkin-freezing
condition, checked per iterate — the band-limited surrogate obeys the bilinear bound
`∫(Ω + P) ≤ (1 + k_max²)·Ω₀·T`, with the `ℏ/ν` prefactor cancelling against the clock's
`ν/ℏ`. -/
theorem bkmSurrogate_le_frozenClock_of_time (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax) {Ω₀ T : ℝ}
    (hτ : entropicProperTime N traj ν ℏ T ≤ frozenEntropicTime ν ℏ Ω₀ T) :
    bkmSurrogateIntegral N traj T ≤ (1 + (kmax : ℝ)^2) * Ω₀ * T := by
  have h1 := bkmSurrogate_le_of_bandlimited N traj ν ℏ hN hν hℏ kmax hfreq T
  have hcoeff : (0:ℝ) ≤ ℏ/ν * (1 + (kmax : ℝ)^2) := by positivity
  calc bkmSurrogateIntegral N traj T
      ≤ ℏ/ν * (1 + (kmax : ℝ)^2) * entropicProperTime N traj ν ℏ T := h1
    _ ≤ ℏ/ν * (1 + (kmax : ℝ)^2) * frozenEntropicTime ν ℏ Ω₀ T :=
        mul_le_mul_of_nonneg_left hτ hcoeff
    _ = (1 + (kmax : ℝ)^2) * Ω₀ * T := by
        unfold frozenEntropicTime
        field_simp

/-- **The frozen-clock BKM bound from an enstrophy ceiling**: a band-limited trajectory
whose enstrophy never exceeds `Ω₀` has `∫(Ω + P) ≤ (1 + k_max²)·Ω₀·T` — bilinear in the
ceiling and the horizon, the genuine T-coercive estimate structure. -/
theorem bkmSurrogate_le_frozenClock (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmax : ℕ) (hfreq : ∀ t i, (traj t).freq i ≤ kmax)
    {Ω₀ : ℝ} (hΩ₀ : 0 ≤ Ω₀) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t, enstrophy (traj t) ≤ Ω₀) :
    bkmSurrogateIntegral N traj T ≤ (1 + (kmax : ℝ)^2) * Ω₀ * T :=
  bkmSurrogate_le_frozenClock_of_time N traj ν ℏ hN hν hℏ kmax hfreq
    (entropicProperTime_le_frozen N traj ν ℏ hN hν hℏ hΩ₀ hT hbound)

end NSFieldFourier

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

end
