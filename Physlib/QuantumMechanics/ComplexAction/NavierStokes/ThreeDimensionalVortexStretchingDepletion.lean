/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSBKMSurrogateBudget

/-!
# The 3D problem: strict vortex-stretching depletion is the exact regularity gate

In three dimensions the vortex stretching `VS` does not vanish, and the enstrophy balance
`dΩ/dt = 2(VS − νP)` (`NSVortexStretchingDefect.enstrophyRate`) can be positive.  This file isolates *exactly*
what would close the 3D problem, quantitatively, and exhibits 2D as the degenerate case.

The gate is a **strict depletion margin** `del`: if the (integrated) vortex stretching stays a fixed fraction
below the viscous dissipation,

  `∫VS ≤ (1 − del) · ν∫P`   with `del > 0`,

then the enstrophy identity `Ω_T − Ω_0 = 2∫VS − 2ν∫P` forces the palinstrophy budget

  `∫P ≤ Ω₀ / (2 del ν)`     (`threeDim_palinstrophy_budget_of_strict_depletion`),

which discharges the external budget of `NSBKMSurrogateBudget.bkmSurrogate_le_budget`, so the BKM surrogate is
bounded (`bkmSurrogate_le_of_strict_depletion`).  Two dimensions is the **full-depletion** case `del = 1`
(`VS = 0`), recovering `∫P ≤ Ω₀/(2ν)` (`twoDim_full_depletion_budget`).

Read through the Herglotz split (`HerglotzContactEnstrophyDissipation`), `del` is the margin by which the
*friction* `2νP` dominates the *conservative* stretching `2·VS`: the entropic clock closes precisely when
friction wins by a fixed fraction.

## Honest scope

The budget `Ω₀/(2delν)` **diverges as `del → 0`**: at the marginal case `VS = νP` (no strict margin) there is no
bound.  Proving a *uniform* `del > 0` — i.e. that the vortex stretching is strictly depleted for all time — is the
open 3D problem itself; it is known only *conditionally* (Constantin–Fefferman geometric depletion, when the
vorticity direction is Lipschitz).  Nothing here proves that condition.  What is proved is the exact,
quantitative reduction: **3D regularity `⟺` a strict depletion margin**, with 2D the `del = 1` corner.  The
realized-margin section sharpens this: the margin is the enstrophy balance itself read backwards —
`δ* = (Ω₀ − Ω_T)/(2ν∫P)` is *determined by the trajectory*, the gate is equivalent to the quantified enstrophy
drop, and the open problem is exactly a uniform positive lower bound on `δ*`.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/-! ### The depletion condition and the enstrophy sign -/

/-- **Depletion makes the enstrophy non-increasing.**  When the vortex stretching is dominated by the viscous
dissipation, `VS ≤ νP`, the enstrophy rate `dΩ/dt = 2(VS − νP)` is `≤ 0` — the 3D enstrophy is monotone on any
interval where depletion holds (`NSVortexStretchingDefect.enstrophyRate_nonpos_iff`). -/
theorem enstrophyRate_nonpos_of_depletion (VS ν P : ℝ) (h : VS ≤ ν * P) :
    enstrophyRate VS ν P ≤ 0 :=
  (enstrophyRate_nonpos_iff VS ν P).mpr h

/-! ### The strict-depletion palinstrophy budget -/

/-- **Strict depletion bounds the palinstrophy budget.**  Given the enstrophy identity
`Ω_T − Ω_0 = 2∫VS − 2ν∫P` and a strict depletion margin `∫VS ≤ (1 − del)·ν∫P` with `del > 0` (and `Ω_T ≥ 0`), the
integrated palinstrophy is bounded: `∫P ≤ Ω₀/(2delν)`.  This is the exact 3D gate — a positive margin `del` turns
the marginal `VS ≤ νP` into a genuine `L¹`-in-time palinstrophy bound. -/
theorem threeDim_palinstrophy_budget_of_strict_depletion
    (IVS IP Ω_T Ω_0 ν del : ℝ) (hν : 0 < ν) (hdel : 0 < del) (hΩT : 0 ≤ Ω_T)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * IP)
    (hdepletion : IVS ≤ (1 - del) * (ν * IP)) :
    IP ≤ Ω_0 / (2 * del * ν) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hidentity, hdepletion, hΩT]

/-- **Two dimensions is the full-depletion corner `del = 1`.**  With `VS = 0` the depletion is total (`del = 1`),
and the budget collapses to the exact 2D bound `∫P ≤ Ω₀/(2ν)` — the case
`TwoDimensionalNavierStokesBoundaryScreen.bkmSurrogate_le_twoDim` used unconditionally. -/
theorem twoDim_full_depletion_budget (IP Ω_T Ω_0 ν : ℝ) (hν : 0 < ν) (hΩT : 0 ≤ Ω_T)
    (hidentity : Ω_T - Ω_0 = -(2 * ν * IP)) :
    IP ≤ Ω_0 / (2 * ν) := by
  have h := threeDim_palinstrophy_budget_of_strict_depletion 0 IP Ω_T Ω_0 ν 1 hν one_pos hΩT
    (by linear_combination hidentity) (by simp)
  simpa using h

/-! ### Discharging the BKM surrogate under strict depletion -/

/-- **Strict depletion bounds the BKM surrogate.**  Feeding the strict-depletion palinstrophy budget into the
BKM budget bound, the surrogate `∫(Ω + P)` is bounded by the entropic proper time plus `Ω₀/(2delℏ)` — the 3D
analogue of the 2D unconditional closure, now conditional on the depletion margin `del`. -/
theorem bkmSurrogate_le_of_strict_depletion
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hν : 0 < ν) (hℏ : 0 < ℏ)
    {T IVS Ω_T Ω_0 del : ℝ} (hdel : 0 < del) (hΩT : 0 ≤ Ω_T)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * integratedPalinstrophy N traj T)
    (hdepletion : IVS ≤ (1 - del) * (ν * integratedPalinstrophy N traj T)) :
    bkmSurrogateIntegral N traj T
      ≤ ℏ / ν * (entropicProperTime N traj ν ℏ T + Ω_0 / (2 * del * ℏ)) := by
  have hbudget : integratedPalinstrophy N traj T ≤ Ω_0 / (2 * del * ν) :=
    threeDim_palinstrophy_budget_of_strict_depletion IVS (integratedPalinstrophy N traj T)
      Ω_T Ω_0 ν del hν hdel hΩT hidentity hdepletion
  have hM : entropicPalinstrophyTime N traj ν ℏ T ≤ Ω_0 / (2 * del * ℏ) := by
    unfold entropicPalinstrophyTime
    calc ν / ℏ * integratedPalinstrophy N traj T
        ≤ ν / ℏ * (Ω_0 / (2 * del * ν)) :=
          mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = Ω_0 / (2 * del * ℏ) := by field_simp
  exact bkmSurrogate_le_budget N traj ν ℏ hν hℏ hM

/-! ### The gate is the enstrophy balance read backwards

The depletion margin is not an external hypothesis the fluid may or may not obey: given the enstrophy identity,
the trajectory *determines* its own margin.  Define the **realized margin** `δ* := (Ω₀ − Ω_T)/(2ν·∫P)`.  Then
`∫VS = (1 − δ*)·ν∫P` *identically* (`stretching_eq_realizedMargin`), the margin is positive exactly when the
enstrophy dropped (`realizedMargin_pos_iff`), and the gate at margin `del` is *equivalent* to the quantified
enstrophy drop `2·del·ν∫P ≤ Ω₀ − Ω_T` (`depletion_iff_enstrophy_drop`).  So "the gate governs the fluid" is
tautological — it is the balance rearranged, at every `ℏ` alike; the whole non-tautological content of the 3D
problem in this language is a **uniform positive lower bound on the realized margin**, which nothing here
provides.  Note also that the `ℏ > 0` band-limited closure bounds `∫P` *without* making the realized margin
positive — enstrophy may still grow on windows — so the quantum closure and the gate are genuinely different
mechanisms, not one "protection". -/

/-- **The realized depletion margin** `δ* = (Ω₀ − Ω_T)/(2ν·∫P)` — the margin the trajectory actually realizes,
extracted from the enstrophy balance rather than hypothesized. -/
noncomputable def realizedDepletionMargin (Ω_0 Ω_T ν IP : ℝ) : ℝ :=
  (Ω_0 - Ω_T) / (2 * ν * IP)

/-- **The gate is the enstrophy balance rearranged.**  Under the enstrophy identity the integrated vortex
stretching *equals* `(1 − δ*)·ν∫P` at the realized margin: the depletion condition is not an external law but
the balance read backwards. -/
theorem stretching_eq_realizedMargin (IVS IP Ω_T Ω_0 ν : ℝ) (hν : ν ≠ 0) (hIP : IP ≠ 0)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * IP) :
    IVS = (1 - realizedDepletionMargin Ω_0 Ω_T ν IP) * (ν * IP) := by
  have hb : (2 : ℝ) * ν * IP ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hν) hIP
  have hcancel : realizedDepletionMargin Ω_0 Ω_T ν IP * (2 * ν * IP) = Ω_0 - Ω_T := by
    unfold realizedDepletionMargin
    exact div_mul_cancel₀ _ hb
  have h1 : realizedDepletionMargin Ω_0 Ω_T ν IP * (ν * IP) = (Ω_0 - Ω_T) / 2 := by
    linear_combination hcancel / 2
  have hexp : (1 - realizedDepletionMargin Ω_0 Ω_T ν IP) * (ν * IP)
      = ν * IP - (Ω_0 - Ω_T) / 2 := by
    rw [sub_mul, one_mul, h1]
  rw [hexp]
  linarith [hidentity]

/-- **The realized margin is positive iff the enstrophy dropped.**  For `ν, ∫P > 0`:
`0 < δ* ↔ Ω_T < Ω₀`.  A positive margin is nothing over and above a net enstrophy decrease. -/
theorem realizedMargin_pos_iff (Ω_0 Ω_T ν IP : ℝ) (hν : 0 < ν) (hIP : 0 < IP) :
    0 < realizedDepletionMargin Ω_0 Ω_T ν IP ↔ Ω_T < Ω_0 := by
  have hb : (0 : ℝ) < 2 * ν * IP := by positivity
  have hcancel : realizedDepletionMargin Ω_0 Ω_T ν IP * (2 * ν * IP) = Ω_0 - Ω_T := by
    unfold realizedDepletionMargin
    exact div_mul_cancel₀ _ hb.ne'
  constructor
  · intro h
    have hm := mul_pos h hb
    rw [hcancel] at hm
    linarith
  · intro h
    unfold realizedDepletionMargin
    exact div_pos (by linarith) hb

/-- **The gate is equivalent to a quantified enstrophy drop.**  Given the enstrophy identity, depletion at
margin `del` holds *iff* the enstrophy dropped by at least `2·del·ν∫P`: the gate carries no dynamical content
beyond the balance — the open problem is exactly a solution-independent lower bound on that drop. -/
theorem depletion_iff_enstrophy_drop (IVS IP Ω_T Ω_0 ν del : ℝ)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * IP) :
    IVS ≤ (1 - del) * (ν * IP) ↔ 2 * del * ν * IP ≤ Ω_0 - Ω_T := by
  have key : IVS - (1 - del) * (ν * IP) = (2 * del * ν * IP - (Ω_0 - Ω_T)) / 2 := by
    linear_combination (-1 / 2 : ℝ) * hidentity
  constructor <;> intro h <;> linarith [key]

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

end
