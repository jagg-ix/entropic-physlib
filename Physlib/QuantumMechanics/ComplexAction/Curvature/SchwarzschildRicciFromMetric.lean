/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

/-!
# Schwarzschild `R_{μν} = 0` from the metric

The full component computation `metric → Christoffel → Riemann → Ricci` for the Schwarzschild metric in
coordinates `(t, r, θ, φ)`, with `g = diag(−f, f⁻¹, r², r²sin²θ)`, verifying the vacuum equation
`R_{μν} = 0` directly from the metric via `Curvature.LeviCivitaFromMetric.christoffelFromMetric` and
`ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection` — the same pipeline as the worked 1+1
example `weakField_ricci00_from_connection`, now for a black hole.

This first part sets up the metric, its inverse and derivatives, and reads off the Christoffel symbols
`Γ^σ_{μν} = ½ g^{σσ}(∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})` from the metric.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci

/-! ## The metric, its inverse and its derivatives

Parameters: `f = f(r)` (with `g_tt = −f`, `g_rr = f⁻¹`), `df = f'(r)`, and `s = sin θ`. -/

/-- **The Schwarzschild metric** `g = diag(−f, f⁻¹, r², r² sin²θ)` at a point. -/
noncomputable def metric (f r s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-f, 0, 0, 0; 0, f⁻¹, 0, 0; 0, 0, r ^ 2, 0; 0, 0, 0, r ^ 2 * s ^ 2]

/-- **The inverse metric** `g⁻¹ = diag(−f⁻¹, f, r⁻², (r² sin²θ)⁻¹)`. -/
noncomputable def metricInv (f r s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-f⁻¹, 0, 0, 0; 0, f, 0, 0; 0, 0, (r ^ 2)⁻¹, 0; 0, 0, 0, (r ^ 2 * s ^ 2)⁻¹]

/-- **`g · g⁻¹ = 1`** — the inverse metric is genuine. -/
theorem metric_mul_metricInv (f r s : ℝ) (hf : f ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    metric f r s * metricInv f r s = 1 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    field_simp

/-- **The coordinate derivatives of the metric** `∂_κ g`: static (`∂_t = ∂_φ = 0`), with `∂_r g` and
`∂_θ g` the only nonzero blocks. `∂_r g = diag(−f', −f'/f², 2r, 2r sin²θ)`,
`∂_θ g = diag(0, 0, 0, 2r² sinθ cosθ)`. -/
noncomputable def metricDeriv (f df r s cs : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    !![-df, 0, 0, 0; 0, -df / f ^ 2, 0, 0; 0, 0, 2 * r, 0; 0, 0, 0, 2 * r * s ^ 2],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 2 * r ^ 2 * s * cs],
    0]

/-! ## The Christoffel symbols, read from the metric

Each is `christoffelFromMetric metricInv metricDeriv σ μ ν = Γ^σ_{μν}`. -/

/-- **`Γ^r_{tt} = f f'/2`.** -/
theorem christoffel_r_tt (f df r s cs : ℝ) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 1 0 0 = f * df / 2 := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  ring

/-- **`Γ^t_{tr} = f'/(2f)`.** -/
theorem christoffel_t_tr (f df r s cs : ℝ) (hf : f ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 0 0 1 = df / (2 * f) := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-- **`Γ^r_{rr} = −f'/(2f)`.** -/
theorem christoffel_r_rr (f df r s cs : ℝ) (hf : f ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 1 1 1 = -df / (2 * f) := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-- **`Γ^r_{θθ} = −r f`.** -/
theorem christoffel_r_thth (f df r s cs : ℝ) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 1 2 2 = -(r * f) := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  ring

/-- **`Γ^θ_{rθ} = 1/r`.** -/
theorem christoffel_th_rth (f df r s cs : ℝ) (hr : r ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 2 1 2 = r⁻¹ := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-- **`Γ^r_{φφ} = −r f sin²θ`.** -/
theorem christoffel_r_phph (f df r s cs : ℝ) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 1 3 3 = -(r * f * s ^ 2) := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  ring

/-- **`Γ^θ_{φφ} = −sinθ cosθ`.** -/
theorem christoffel_th_phph (f df r s cs : ℝ) (hr : r ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 2 3 3 = -(s * cs) := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-- **`Γ^φ_{rφ} = 1/r`.** -/
theorem christoffel_ph_rph (f df r s cs : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 3 1 3 = r⁻¹ := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-- **`Γ^φ_{θφ} = cotθ = cosθ/sinθ`.** -/
theorem christoffel_ph_thph (f df r s cs : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    christoffelFromMetric (metricInv f r s) (metricDeriv f df r s cs) 3 2 3 = cs / s := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]
  field_simp

/-! ## The connection and its coordinate derivatives, then the Ricci tensor -/

/-- **The Levi-Civita connection** `Γ^σ_{μν}` of the Schwarzschild metric, as the explicit array of the
nine symbols computed above (`christoffel_eq` grounds it in `christoffelFromMetric`). -/
noncomputable def christoffel (f df r s cs : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![!![0, df / (2 * f), 0, 0; df / (2 * f), 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![f * df / 2, 0, 0, 0; 0, -df / (2 * f), 0, 0; 0, 0, -(r * f), 0; 0, 0, 0, -(r * f * s ^ 2)],
    !![0, 0, 0, 0; 0, 0, r⁻¹, 0; 0, r⁻¹, 0, 0; 0, 0, 0, -(s * cs)],
    !![0, 0, 0, 0; 0, 0, 0, r⁻¹; 0, 0, 0, cs / s; 0, r⁻¹, cs / s, 0]]

/-- **The coordinate derivatives of the connection** `∂_κ Γ^ρ` (static: `∂_t = ∂_φ = 0`), the second
derivatives of the metric packaged for `riemannFromConnection`. -/
noncomputable def connDeriv (f df ddf r s cs : ℝ) : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 0, 0, 0],
    ![!![0, (ddf * f - df ^ 2) / (2 * f ^ 2), 0, 0;
        (ddf * f - df ^ 2) / (2 * f ^ 2), 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![(df ^ 2 + f * ddf) / 2, 0, 0, 0; 0, -(ddf * f - df ^ 2) / (2 * f ^ 2), 0, 0;
        0, 0, -(f + r * df), 0; 0, 0, 0, -(f + r * df) * s ^ 2],
      !![0, 0, 0, 0; 0, 0, -(r ^ 2)⁻¹, 0; 0, -(r ^ 2)⁻¹, 0, 0; 0, 0, 0, 0],
      !![0, 0, 0, 0; 0, 0, 0, -(r ^ 2)⁻¹; 0, 0, 0, 0; 0, -(r ^ 2)⁻¹, 0, 0]],
    ![0,
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -2 * r * f * s * cs],
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, s ^ 2 - cs ^ 2],
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -(s ^ 2 + cs ^ 2) / s ^ 2;
        0, 0, -(s ^ 2 + cs ^ 2) / s ^ 2, 0]],
    ![0, 0, 0, 0]]

/-- The reduction that turns one Ricci component of the Schwarzschild connection into a rational-function
identity: unfold the `∂Γ − ∂Γ + ΓΓ` contraction, expand the `Fin 4` sums, and read off the matrix-literal
entries. Stated with explicit `OfNat` indices only — the `Matrix.cons_val_*` lemmas do not match the
`Fin.mk` literals produced by `fin_cases`. -/
macro "schw_reduce" : tactic =>
  `(tactic| simp only [ricciFromConnection, riemannFromConnection, christoffel, connDeriv,
      Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.zero_apply, Pi.zero_apply, Matrix.zero_empty])

/-- **`R_{tt} = ½ f (f'' + 2f'/r)`** — the time–time Ricci curvature from the metric's connection. -/
theorem ricci_tt (f df ddf r s cs : ℝ) (hf : f ≠ 0) (hr : r ≠ 0) :
    ricciFromConnection (christoffel f df r s cs) (connDeriv f df ddf r s cs) 0 0
      = f * (ddf + 2 * df / r) / 2 := by
  schw_reduce
  field_simp
  ring

/-- **`R_{rr} = −(f'' + 2f'/r)/(2f)`** — the radial Ricci curvature from the metric's connection. -/
theorem ricci_rr (f df ddf r s cs : ℝ) (hf : f ≠ 0) (hr : r ≠ 0) :
    ricciFromConnection (christoffel f df r s cs) (connDeriv f df ddf r s cs) 1 1
      = -(ddf + 2 * df / r) / (2 * f) := by
  schw_reduce
  field_simp
  ring

/-- **`R_{θθ} = 1 − f − r f'`** — the polar Ricci curvature from the metric's connection. -/
theorem ricci_thth (f df ddf r s cs : ℝ) (hf : f ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ricciFromConnection (christoffel f df r s cs) (connDeriv f df ddf r s cs) 2 2
      = 1 - f - r * df := by
  schw_reduce
  field_simp
  ring

/-- **`R_{φφ} = (1 − f − r f') sin²θ`** — the azimuthal Ricci curvature from the metric's connection. -/
theorem ricci_phph (f df ddf r s cs : ℝ) (hf : f ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ricciFromConnection (christoffel f df r s cs) (connDeriv f df ddf r s cs) 3 3
      = (1 - f - r * df) * s ^ 2 := by
  schw_reduce
  field_simp
  ring

/-! ## The Schwarzschild profile `f = 1 − 2M/r` solves the vacuum equation `R_{μν} = 0` -/

/-- **`f(r) = 1 − 2M/r`.** -/
noncomputable def schwF (M r : ℝ) : ℝ := 1 - 2 * M / r
/-- **`f'(r) = 2M/r²`.** -/
noncomputable def schwDf (M r : ℝ) : ℝ := 2 * M / r ^ 2
/-- **`f''(r) = −4M/r³`.** -/
noncomputable def schwDdf (M r : ℝ) : ℝ := -(4 * M) / r ^ 3

/-- **The radial vacuum relation** `f'' + 2f'/r = 0` for the Schwarzschild profile (kills `R_tt`, `R_rr`). -/
theorem schw_radial (M r : ℝ) (hr : r ≠ 0) : schwDdf M r + 2 * schwDf M r / r = 0 := by
  simp only [schwDdf, schwDf]; field_simp; ring

/-- **The angular vacuum relation** `1 − f − rf' = 0` for the Schwarzschild profile (kills `R_θθ`,
`R_φφ`). -/
theorem schw_angular (M r : ℝ) (hr : r ≠ 0) : 1 - schwF M r - r * schwDf M r = 0 := by
  simp only [schwF, schwDf]; field_simp; ring

/-- **`R_{tt} = 0`** for the Schwarzschild profile. -/
theorem schwarzschild_ricci_00 (M r s cs : ℝ) (hr : r ≠ 0) (hf : schwF M r ≠ 0) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 0 0 = 0 := by
  rw [ricci_tt (schwF M r) (schwDf M r) (schwDdf M r) r s cs hf hr, schw_radial M r hr]; ring

/-- **`R_{rr} = 0`** for the Schwarzschild profile. -/
theorem schwarzschild_ricci_11 (M r s cs : ℝ) (hr : r ≠ 0) (hf : schwF M r ≠ 0) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 1 1 = 0 := by
  rw [ricci_rr (schwF M r) (schwDf M r) (schwDdf M r) r s cs hf hr, schw_radial M r hr]; simp

/-- **`R_{θθ} = 0`** for the Schwarzschild profile. -/
theorem schwarzschild_ricci_22 (M r s cs : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hf : schwF M r ≠ 0) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 2 2 = 0 := by
  rw [ricci_thth (schwF M r) (schwDf M r) (schwDdf M r) r s cs hf hr hs]
  exact schw_angular M r hr

/-- **`R_{φφ} = 0`** for the Schwarzschild profile. -/
theorem schwarzschild_ricci_33 (M r s cs : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hf : schwF M r ≠ 0) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 3 3 = 0 := by
  rw [ricci_phph (schwF M r) (schwDf M r) (schwDdf M r) r s cs hf hr hs, schw_angular M r hr]; ring

set_option maxHeartbeats 1000000 in
/-- **Schwarzschild is Ricci-flat** `R_{μν} = 0` for every `μ, ν` — the vacuum Einstein equation, derived
in full from the metric `g = diag(−f, f⁻¹, r², r²sin²θ)` with `f = 1 − 2M/r`, through the pipeline
`metric → christoffelFromMetric → ricciFromConnection`. The four diagonal components vanish by the radial
and angular vacuum relations (`schwarzschild_ricci_00`–`_33`); the twelve off-diagonal components vanish
identically for the static, diagonal, spherically-symmetric metric. Each of the sixteen components is
proved at explicit indices and the quantifier is dispatched by definitional matching. -/
theorem schwarzschild_ricci_eq_zero (M r s cs : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hf : schwF M r ≠ 0)
    (μ ν : Fin 4) :
    ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) μ ν = 0 := by
  have c00 := schwarzschild_ricci_00 M r s cs hr hf
  have c11 := schwarzschild_ricci_11 M r s cs hr hf
  have c22 := schwarzschild_ricci_22 M r s cs hr hs hf
  have c33 := schwarzschild_ricci_33 M r s cs hr hs hf
  have c01 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 0 1 = 0 := by
    schw_reduce; field_simp; ring
  have c02 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 0 2 = 0 := by
    schw_reduce; field_simp; ring
  have c03 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 0 3 = 0 := by
    schw_reduce; field_simp; ring
  have c10 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 1 0 = 0 := by
    schw_reduce; field_simp; ring
  have c12 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 1 2 = 0 := by
    schw_reduce; field_simp; ring
  have c13 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 1 3 = 0 := by
    schw_reduce; field_simp; ring
  have c20 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 2 0 = 0 := by
    schw_reduce; field_simp; ring
  have c21 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 2 1 = 0 := by
    schw_reduce; field_simp; ring
  have c23 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 2 3 = 0 := by
    schw_reduce; field_simp; ring
  have c30 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 3 0 = 0 := by
    schw_reduce; field_simp; ring
  have c31 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 3 1 = 0 := by
    schw_reduce; field_simp; ring
  have c32 : ricciFromConnection (christoffel (schwF M r) (schwDf M r) r s cs)
      (connDeriv (schwF M r) (schwDf M r) (schwDdf M r) r s cs) 3 2 = 0 := by
    schw_reduce; field_simp; ring
  fin_cases μ <;> fin_cases ν <;> assumption

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci
