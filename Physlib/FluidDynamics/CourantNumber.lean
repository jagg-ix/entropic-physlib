/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.Dimension
/-!

# The Courant number and the CFL condition

For an explicit time-stepping scheme of a linear 1D advection problem with
constant speed `a`, grid spacing `Δx`, and time step `Δt`, the engineering
Courant–Friedrichs–Lewy bound `Δt ≤ Δx / a` ensures that the discrete
domain of dependence contains the continuous one (Courant–Friedrichs–Lewy
1928, Section II §1–§3). Equivalently, the dimensionless **Courant
number** `C := a·Δt/Δx` satisfies `C ≤ 1`. Multi-dimensional wave
equations have stricter bounds (e.g. `C ≤ 1/√d` for the `d`-dimensional
wave equation; see Courant–Friedrichs–Lewy 1928 Section II §4 for the
2D case).

## Admissible time parameterizations

Coordinate time `t` is one choice of evolution parameter. For a positive
monotone reparameterization `τ(t)` with rate `λ(t) := dτ/dt > 0`, a
discrete step of duration `Δτ = λ·Δt` reads the *same* physical
propagation distance over the step if the propagation speed is rescaled
contravariantly:

  `a_τ := a / λ`,    so that    `a_τ · Δτ = a · Δt`.

Under this transformation the Courant number is invariant:
`a_τ · Δτ / Δx = a · Δt / Δx`. Hence the CFL bound holds in `t` iff it
holds in `τ`:

  `Δt ≤ Δx / a`    ⟺    `Δτ ≤ Δx / a_τ`.

This is `cflCondition_reparam_iff` below. The reparameterization `τ` is
**admissible** as a CFL-stable evolution parameter when:

1. `λ(t) = dτ/dt > 0` (`τ` is a strictly monotone clock — equivalently,
   `Δτ > 0` over each step);
2. the propagation speed in the `τ`-frame is taken to be `a_τ = a/λ`
   (equivalently, `a_τ · Δτ = a · Δt` — the contravariant
   transformation);
3. `Δx > 0` and `a > 0` (so that both forms of CFL make sense via
   `cfl_iff_courant_le_one`).

Specific applications — proper time on a worldline, Tolman-redshifted
time on a lapse, modular (KMS) time, and the dissipative entropic clock
`τ_ent = ℏ⁻¹·S_I` — instantiate this iff once a `λ > 0` is fixed.

For an explicit time-stepping scheme of an advection problem with wave/advection
speed `a`, grid spacing `Δx`, and time step `Δt`, the Courant–Friedrichs–Lewy
(CFL) condition `Δt ≤ Δx / a` bounds the time step required for numerical
stability. Equivalently, the dimensionless **Courant number** `C := a·Δt/Δx`
satisfies `C ≤ 1`.

- `CFLCondition`, `courantNumber`
- `cfl_iff_courant_le_one` — equivalence with `C ≤ 1`
- `courantNumber_rescale_invariant` — invariance under
  `(Δt, a) ↦ (λ·Δt, a/λ)`
- `cflCondition_reparam_iff` — CFL preserved under positive monotone
  reparameterization of time, when speed transforms contravariantly
- `courantNumber_dimensionless` — `[C] = 1`

## ii. Key results

- `courantNumber`, `CFLCondition`
- `cfl_iff_courant_le_one`
- `courantNumber_rescale_invariant`
- `courantNumber_dimensionless`

## iii. Table of contents

- A. The Courant number and the CFL condition
- B. Rescaling invariance
- C. Dimensional analysis

## iv. References

- **Courant, Friedrichs & Lewy 1928** — *Über die partiellen
  Differenzengleichungen der mathematischen Physik*, Mathematische
  Annalen 100, 32–74. English translation by Phyllis Fox: *On the Partial
  Difference Equations of Mathematical Physics*, IBM Journal of Research
  and Development 11(2), 215–234 (1967). The original convergence
  statement (discrete domain of dependence contains the continuous one).
- **Lax 1956** — *Survey of Stability of Difference Schemes for Solving
  Initial Value Problems for Hyperbolic Equations*, in *Proc. Symp. Appl.
  Math.* VI (Numerical Analysis), 251–258. The von-Neumann / Lax
  equivalence theorem under which the CFL condition is read as a
  *stability* bound for consistent difference schemes.
- **LeVeque, *Finite Volume Methods for Hyperbolic Problems*** —
  Cambridge University Press, 2002. Textbook treatment of CFL stability
  and dimensionless Courant numbers across spatial dimensions.
-/

@[expose] public section

namespace FluidDynamics

open Dimension

/-! ## A. The Courant number and the CFL condition -/

/-- The **CFL condition** `Δt ≤ Δx / a` for advection speed `a`, grid spacing
`Δx`, and time step `Δt`. -/
def CFLCondition (Δt Δx a : ℝ) : Prop := Δt ≤ Δx / a

/-- The **Courant number** `C = a·Δt/Δx`. -/
noncomputable def courantNumber (Δt Δx a : ℝ) : ℝ := a * Δt / Δx

/-- The CFL condition is equivalent to `C ≤ 1` (for positive spacing and speed). -/
theorem cfl_iff_courant_le_one
    (Δt Δx a : ℝ) (hΔx : 0 < Δx) (ha : 0 < a) :
    CFLCondition Δt Δx a ↔ courantNumber Δt Δx a ≤ 1 := by
  unfold CFLCondition courantNumber
  constructor
  · intro h
    have hmul : a * Δt ≤ Δx := by
      have hmul' : a * Δt ≤ a * (Δx / a) := mul_le_mul_of_nonneg_left h ha.le
      have hscale : a * (Δx / a) = Δx := by field_simp
      rw [hscale] at hmul'
      exact hmul'
    have hinv_nonneg : 0 ≤ 1 / Δx := one_div_nonneg.mpr hΔx.le
    have hbound : (a * Δt) * (1 / Δx) ≤ Δx * (1 / Δx) :=
      mul_le_mul_of_nonneg_right hmul hinv_nonneg
    calc
      a * Δt / Δx = (a * Δt) * (1 / Δx) := by ring
      _ ≤ Δx * (1 / Δx) := hbound
      _ = 1 := by field_simp
  · intro h
    have hmulInv : (a * Δt) * (1 / Δx) ≤ 1 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    have hmul : a * Δt ≤ Δx := by
      have hscaled : ((a * Δt) * (1 / Δx)) * Δx ≤ 1 * Δx :=
        mul_le_mul_of_nonneg_right hmulInv hΔx.le
      have hleft : ((a * Δt) * (1 / Δx)) * Δx = a * Δt := by field_simp
      rw [hleft] at hscaled
      simpa using hscaled
    have hinv_nonneg : 0 ≤ 1 / a := one_div_nonneg.mpr ha.le
    have hscaled : (a * Δt) * (1 / a) ≤ Δx * (1 / a) :=
      mul_le_mul_of_nonneg_right hmul hinv_nonneg
    calc
      Δt = (a * Δt) * (1 / a) := by field_simp
      _ ≤ Δx * (1 / a) := hscaled
      _ = Δx / a := by ring

/-! ## B. Rescaling invariance -/

/-- The Courant number is invariant under the rescaling `(Δt, a) ↦ (λ·Δt, a/λ)`:
slowing the clock by `λ` while scaling the speed by `1/λ` leaves `C` unchanged.

complex-action/entropic-time comparator: `claim_level := 2` (admissibility / reparameterization
invariance). Does not prove: uniqueness of entropic `λ`; that entropic
time is **the** admissible clock; multi-dimensional CFL bounds. The
same conclusion holds for `λ := 1` (identity reparameterization),
i.e. for any positive constant `λ`, so the theorem cannot single out
entropic time among the continuum of admissible rescalings.
-/
theorem courantNumber_rescale_invariant
    (Δt Δx a lam : ℝ) (hlam : 0 < lam) :
    courantNumber (lam * Δt) Δx (a / lam) = courantNumber Δt Δx a := by
  unfold courantNumber
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  calc
    (a / lam) * (lam * Δt) / Δx
        = (a * (lam / lam) * Δt) / Δx := by ring
    _ = (a * 1 * Δt) / Δx := by rw [div_self hlam_ne]
    _ = a * Δt / Δx := by ring

/-- The Courant number is invariant under every positive rescaling of `(Δt, a)`. -/
theorem cfl_rescale_summary
    (Δt Δx a lam : ℝ) (hlam : 0 < lam) :
    courantNumber Δt Δx a = courantNumber (lam * Δt) Δx (a / lam)
    ∧ (∀ c : ℝ, 0 < c →
        courantNumber Δt Δx a = courantNumber (c * Δt) Δx (a / c)) :=
  ⟨(courantNumber_rescale_invariant Δt Δx a lam hlam).symm,
   fun c hc => (courantNumber_rescale_invariant Δt Δx a c hc).symm⟩

/-! ## C. Dimensional analysis -/

/-- The Courant number `(speed · time) / length = (L·T⁻¹ · T) / L` is
dimensionless. -/
theorem courantNumber_dimensionless :
    (L𝓭 / T𝓭) * T𝓭 / L𝓭 = (1 : Dimension) := by
  ext <;> simp

end FluidDynamics
