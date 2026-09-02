/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

/-!
# The inertial vacuum versus the accelerated thermal bath (Sciama–Candelas–Deutsch §2)

The paper's central contrast.  An **inertial** detector's response is

`Π_inertial(ω) = (−ω/2π) θ(−ω)`,

which contains **only negative frequencies**: a ground-state inertial detector is never excited — it is a
faithful vacuum.  The **uniformly accelerated** detector instead responds at *all* frequencies with the
Planck spectrum `Π_accelerated(ω) > 0` (`SciamaUnruhPowerSpectrum`), so it *is* excited — it sees a thermal
bath.  Same vacuum, different motion.

* `inertialPowerSpectrum` — `(−ω/2π) θ(−ω)`.
* `inertialPowerSpectrum_pos_freq_zero` — `Π_inertial(ω) = 0` for `ω > 0` (ground-state stability).
* `inertialPowerSpectrum_neg_freq` — `Π_inertial(ω) = −ω/2π > 0` for `ω < 0` (spontaneous de-excitation).
* `unruhPowerSpectrum_pos` — `Π_accelerated(ω) > 0` for `ω > 0` (the accelerated detector *is* excited).
* `sciama_vacuum_vs_thermal_contrast` — at `ω > 0`: inertial `= 0`, accelerated `> 0`.

Honest scope: the sign/positivity structure distinguishing the vacuum (inertial) from the thermal
(accelerated) response; the field-theoretic evaluation of the response integrals is upstream.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaInertialVacuumContrast

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

/-- **The inertial-detector power spectrum** `(−ω/2π) θ(−ω)` — supported only on negative frequencies. -/
def inertialPowerSpectrum (ω : ℝ) : ℝ := if ω < 0 then -ω / (2 * Real.pi) else 0

/-- **[Ground-state stability] `Π_inertial(ω) = 0` for `ω > 0`.**  An inertial detector in its ground state is
never excited by the vacuum — it registers the vacuum as empty. -/
theorem inertialPowerSpectrum_pos_freq_zero (ω : ℝ) (h : 0 < ω) : inertialPowerSpectrum ω = 0 := by
  unfold inertialPowerSpectrum
  rw [if_neg (by linarith : ¬ ω < 0)]

/-- **[Spontaneous de-excitation] `Π_inertial(ω) = −ω/2π` for `ω < 0`.**  The inertial detector responds at
negative frequency — an excited state decays. -/
theorem inertialPowerSpectrum_neg_freq (ω : ℝ) (h : ω < 0) :
    inertialPowerSpectrum ω = -ω / (2 * Real.pi) := by
  unfold inertialPowerSpectrum
  rw [if_pos h]

/-- **[Accelerated detector is excited] `Π_accelerated(ω) > 0` for `ω > 0`.**  Unlike the inertial detector,
the uniformly accelerated one has positive response at positive frequency — it gets excited, i.e. sees a
thermal bath. -/
theorem unruhPowerSpectrum_pos (α ω : ℝ) (hα : 0 < α) (hω : 0 < ω) : 0 < unruhPowerSpectrum α ω := by
  unfold unruhPowerSpectrum
  apply div_pos
  · positivity
  · have h1 : 1 < Real.exp (2 * Real.pi * ω / α) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by positivity)
    linarith

/-- **[Vacuum vs thermal] the paper's central contrast.**  At positive frequency the inertial detector's
response vanishes (vacuum) while the accelerated detector's is strictly positive (thermal) — the same
Minkowski vacuum, read as empty by inertial motion and as a heat bath by accelerated motion. -/
theorem sciama_vacuum_vs_thermal_contrast (α ω : ℝ) (hα : 0 < α) (hω : 0 < ω) :
    inertialPowerSpectrum ω = 0 ∧ 0 < unruhPowerSpectrum α ω :=
  ⟨inertialPowerSpectrum_pos_freq_zero ω hω, unruhPowerSpectrum_pos α ω hα hω⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaInertialVacuumContrast

end
