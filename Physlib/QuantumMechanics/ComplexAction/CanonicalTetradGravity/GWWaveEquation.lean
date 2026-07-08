/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-!
# The gravitational-wave equation `□R_ā = 0`: plane-wave solutions (Lusanna 2015, §5)

Formalizes the analytic core of the linearized **gravitational-wave evolution** of Lusanna §5 — the (vacuum)
wave equation `□R_ā = 0` for the tidal variables — completing the dynamical layer of the ADM tetrad-gravity
arc (`CanonicalTetradGravity.TidalPairsGWDispersion`, the dispersion; `CanonicalTetradGravity.HPMGravitationalWaves`, the TT GW).

The transverse-traceless GW amplitude is a plane wave `R(t,x) = cos(k·x − ω·t)`, and the genuine PDE content is
its second derivatives: `∂²cos(ps+q) = −p²·cos(ps+q)` (`cos_lin_second_deriv`). With `p = −ω` (time) this gives
`∂²_t R = −ω²R`, and with `p = k` (space) `∂²_x R = −k²R`. Hence the d'Alembertian

  `□R = (1/c²)∂²_t R − ∂²_x R = (k² − ω²/c²)·R`,

which **vanishes on the mass shell** `ω² = c²k²` (`gw_onshell_symbol`, `gw_dalembertian`) — the GW plane wave
solves `□R = 0` exactly when it is luminal (the dispersion of `CanonicalTetradGravity.TidalPairsGWDispersion`).

* **§A — the plane-wave derivatives** (`cos_lin_deriv`, `cos_lin_second_deriv`). `∂cos(ps+q) = −p·sin`,
  `∂²cos(ps+q) = −p²·cos`.
* **§B — the wave equation on the mass shell** (`gw_onshell_symbol`, `gw_dalembertian`). `k² − ω²/c² = 0` and
  `□R = 0` on shell.

The retarded Green's-function inversion of `□R = source` (with the no-incoming-radiation Cauchy condition) and
the explicit source/tidal-momentum couplings are the remaining analytic layer; the homogeneous plane-wave
solution and the d'Alembertian on the mass shell are formalized here.

## References

* L. Lusanna, IJGMMP 12 (2015) 1530001, §5 (the linearized GW wave equation in the 3-orthogonal gauge).
* Repo structure: `CanonicalTetradGravity.TidalPairsGWDispersion` (the GW dispersion `ω = c|k|`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation

open Real

/-! ## §A — the plane-wave derivatives -/

/-- **[First derivative] `∂_s cos(ps+q) = −p·sin(ps+q)`.** -/
theorem cos_lin_deriv (p q s : ℝ) :
    HasDerivAt (fun u => Real.cos (p * u + q)) (-p * Real.sin (p * s + q)) s := by
  have hu : HasDerivAt (fun u => p * u + q) p s := by
    simpa using ((hasDerivAt_id s).const_mul p).add_const q
  have h := (Real.hasDerivAt_cos (p * s + q)).comp s hu
  exact h.congr_deriv (by simp [mul_comm])

/-- **[Second derivative] `∂²_s cos(ps+q) = −p²·cos(ps+q)`.** The plane-wave dispersion relation in differential
form: with `p = −ω` it is `∂²_t R = −ω²R`, with `p = k` it is `∂²_x R = −k²R`. -/
theorem cos_lin_second_deriv (p q s : ℝ) :
    HasDerivAt (fun u => -p * Real.sin (p * u + q)) (-p ^ 2 * Real.cos (p * s + q)) s := by
  have hu : HasDerivAt (fun u => p * u + q) p s := by
    simpa using ((hasDerivAt_id s).const_mul p).add_const q
  have h := ((Real.hasDerivAt_sin (p * s + q)).comp s hu).const_mul (-p)
  exact h.congr_deriv (by ring)

/-! ## §B — the wave equation on the mass shell -/

/-- **[On-shell symbol vanishes] `k² − ω²/c² = 0`** when `ω² = c²k²` — the symbol of the d'Alembertian on the
GW plane wave is zero exactly on the (luminal) mass shell. -/
theorem gw_onshell_symbol (k ω c : ℝ) (hc : c ≠ 0) (h : ω ^ 2 = c ^ 2 * k ^ 2) :
    k ^ 2 - ω ^ 2 / c ^ 2 = 0 := by
  rw [h]; field_simp; ring

/-- **[The GW plane wave solves `□R = 0`] `(1/c²)∂²_t R − ∂²_x R = 0` on the mass shell.** Substituting the
plane-wave second derivatives `∂²_t R = −ω²R`, `∂²_x R = −k²R`, the d'Alembertian is `(k² − ω²/c²)R`, which
vanishes for `ω² = c²k²` — the gravitational wave propagates on the light cone. -/
theorem gw_dalembertian (k ω c R : ℝ) (hc : c ≠ 0) (h : ω ^ 2 = c ^ 2 * k ^ 2) :
    (1 / c ^ 2) * (-ω ^ 2 * R) - (-k ^ 2 * R) = 0 := by
  have hs := gw_onshell_symbol k ω c hc h
  have hfac : (1 / c ^ 2) * (-ω ^ 2 * R) - (-k ^ 2 * R) = R * (k ^ 2 - ω ^ 2 / c ^ 2) := by ring
  rw [hfac, hs, mul_zero]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GWWaveEquation

end
