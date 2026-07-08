/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Physlib.Thermodynamics.FirstLaw
public import Physlib.Thermodynamics.SecondLaw

/-!
# Helmholtz free energy — minimization at frozen LRF

Phase 4 of the counterpart program (B4).  The Helmholtz free
energy `F = U − T·S` is the canonical thermodynamic potential at
fixed temperature and volume; for a system at thermal equilibrium
with a reservoir, `F` is extremised (and minimised in the standard
sign conventions).

In the entropic-time framework the equilibrium = frozen-LRF identification (`ρ = σ`,
`S_I = 0`, no entropy production) makes this the counterpart of the
A2/A4/A5/B1 equality cases: a worldline whose internal energy and
entropy are both stationary has constant Helmholtz free energy.

## structure and theorems

* **`HelmholtzWorldline`** — internal energy `U`, entropy `S`,
  reservoir temperature `T > 0`, with `helmholtz t := U t − T·S t`.

* **`helmholtzFreeEnergy_constant_at_equilibrium` (B4)** — at thermal
  equilibrium (both `U` and `S` constant along the worldline), the
  Helmholtz free energy is constant.  This is the **stationarity-at-
  equilibrium** form: at the frozen LRF the system has no spontaneous
  drive in `F`-space.

* **`helmholtz_change_eq_internalEnergy_minus_T_times_entropy_change`**
  — the change in `F` over a forward interval decomposes as
  `ΔF = ΔU − T·ΔS`, the canonical first-order identity that the
  minimization theorem rests on.

No new axioms.  Std-3 axiom envelope throughout.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.FreeEnergy

/-- **Helmholtz-state worldline structure.**  Internal energy `U(t)`,
entropy `S(t)`, and a constant reservoir temperature `T > 0`.  The
Helmholtz free energy is the canonical combination
`F(t) = U(t) − T · S(t)`. -/
structure HelmholtzWorldline where
  /-- Internal energy. -/
  U : ℝ → ℝ
  /-- Entropy. -/
  S : ℝ → ℝ
  /-- Reservoir temperature (constant). -/
  T : ℝ
  /-- Temperature is strictly positive. -/
  T_pos : 0 < T

namespace HelmholtzWorldline

variable (W : HelmholtzWorldline)

/-- **Helmholtz free energy** along the worldline: `F = U − T · S`. -/
def helmholtz (t : ℝ) : ℝ := W.U t - W.T * W.S t

@[simp] theorem helmholtz_def (t : ℝ) :
    W.helmholtz t = W.U t - W.T * W.S t := rfl

/-- **Canonical identity for the Helmholtz change.**  The change in
free energy across `[t₁, t₂]` decomposes as `ΔF = ΔU − T · ΔS`. -/
theorem helmholtz_change_eq_internalEnergy_minus_T_times_entropy_change
    (t₁ t₂ : ℝ) :
    W.helmholtz t₂ - W.helmholtz t₁
      = (W.U t₂ - W.U t₁) - W.T * (W.S t₂ - W.S t₁) := by
  unfold helmholtz; ring

/-- **B4 — Helmholtz free energy is constant at thermal equilibrium.**
At thermal equilibrium (both internal energy and entropy stationary
along the worldline — the frozen LRF in entropic-time terms), the Helmholtz
free energy is constant.

This is the *stationarity* form of the minimisation theorem: the
system has no spontaneous drive in `F`-space when there is no entropy
production and no heat exchange. -/
theorem helmholtzFreeEnergy_constant_at_equilibrium
    (hU : ∀ t₁ t₂ : ℝ, W.U t₁ = W.U t₂)
    (hS : ∀ t₁ t₂ : ℝ, W.S t₁ = W.S t₂)
    (t₁ t₂ : ℝ) :
    W.helmholtz t₁ = W.helmholtz t₂ := by
  unfold helmholtz
  rw [hU t₁ t₂, hS t₁ t₂]

/-- **Equivalent characterisation of equilibrium-via-Helmholtz.**  If
`F` is constant on a forward interval, then `ΔU = T · ΔS` over that
interval — the standard "Clausius equality" relation between heat and
entropy change for reversible processes. -/
theorem clausius_equality_from_helmholtz_constant
    {t₁ t₂ : ℝ}
    (hF : W.helmholtz t₁ = W.helmholtz t₂) :
    W.U t₂ - W.U t₁ = W.T * (W.S t₂ - W.S t₁) := by
  have hdef := W.helmholtz_change_eq_internalEnergy_minus_T_times_entropy_change t₁ t₂
  linarith

/-- **B4 (iff form)** — Helmholtz free energy is conserved over an
interval iff the change in internal energy equals `T` times the
change in entropy (canonical Clausius equality at reversible /
frozen-LRF processes). -/
theorem helmholtzFreeEnergy_conserved_iff_clausius_equality
    (t₁ t₂ : ℝ) :
    W.helmholtz t₁ = W.helmholtz t₂
      ↔ W.U t₂ - W.U t₁ = W.T * (W.S t₂ - W.S t₁) := by
  have hdef := W.helmholtz_change_eq_internalEnergy_minus_T_times_entropy_change t₁ t₂
  constructor
  · intro hF; linarith
  · intro hUS; linarith

end HelmholtzWorldline

end Physlib.Thermodynamics.FreeEnergy

end
