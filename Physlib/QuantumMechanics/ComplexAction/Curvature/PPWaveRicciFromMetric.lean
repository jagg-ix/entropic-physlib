/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

/-!
# The pp-wave `R_{μν} = 0` from the metric — a Kerr–Schild vacuum

The full `metric → Christoffel → Riemann → Ricci` computation for the plane-fronted gravitational wave
(pp-wave), the simplest Kerr–Schild vacuum in Harada's table (arXiv:2506.20878, Table I / Eq. 6). In
light-cone coordinates `(v, u, x, y)` (with `k = du`, `H = H(u, x, y)`),

  `ds² = −2 du dv + dx² + dy² + H du²`,   `g = η + H k_μ k_ν dx^μ dx^ν`,

so the metric is the flat null metric `η` (non-diagonal) plus the Kerr–Schild term `H du²`. Computed from
the metric through `Curvature.LeviCivitaFromMetric.christoffelFromMetric` and
`ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection`, the only nonvanishing Ricci component is

  `R_{uu} = −½ (H_{xx} + H_{yy})`   (`ricci_uu`),

so the vacuum equation `R_{μν} = 0` is exactly the transverse **Laplace equation** `H_{xx} + H_{yy} = 0`
(`ppWave_vacuum_iff`, Harada Eq. 31). Companion to `Curvature.SchwarzschildRicci` — same pipeline, now on
a *null* (non-diagonal) background.

Parameters: `H` and its partials `Hu, Hx, Hy, Huu, Hux, Huy, Hxx, Hxy, Hyy` at a point.
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.PPWaveRicci

/-! ## The metric, its inverse and its derivatives -/

/-- **The pp-wave metric** `g = !![0,−1,0,0; −1,H,0,0; 0,0,1,0; 0,0,0,1]` in `(v,u,x,y)`. -/
noncomputable def metric (H : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; -1, H, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **The inverse metric** `g⁻¹ = !![−H,−1,0,0; −1,0,0,0; 0,0,1,0; 0,0,0,1]` (`det = −1`, invertible for
every `H`). -/
noncomputable def metricInv (H : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-H, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **`g · g⁻¹ = 1`.** -/
theorem metric_mul_metricInv (H : ℝ) : metric H * metricInv H = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The coordinate derivatives of the metric** `∂_κ g`: only `g_{uu} = H` varies, so `∂_u g`, `∂_x g`,
`∂_y g` each place the corresponding first partial in the `(u,u)` slot (`∂_v g = 0`). -/
noncomputable def metricDeriv (Hu Hx Hy : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    !![0, 0, 0, 0; 0, Hu, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, Hx, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, Hy, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]]

/-- **`Γ^v_{uu} = −½ H_u`**, read from the metric. -/
theorem christoffel_v_uu (H Hu Hx Hy : ℝ) :
    christoffelFromMetric (metricInv H) (metricDeriv Hu Hx Hy) 0 1 1 = -Hu / 2 := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]; ring

/-- **`Γ^x_{uu} = −½ H_x`**, read from the metric. -/
theorem christoffel_x_uu (H Hu Hx Hy : ℝ) :
    christoffelFromMetric (metricInv H) (metricDeriv Hu Hx Hy) 2 1 1 = -Hx / 2 := by
  simp [christoffelFromMetric, metricInv, metricDeriv, Fin.sum_univ_four]; ring

/-! ## The connection, its derivatives, and the Ricci tensor -/

/-- **The Levi-Civita connection** `Γ` of the pp-wave (nonzero: `Γ^v_{uu}, Γ^v_{ux}, Γ^v_{uy}, Γ^x_{uu},
Γ^y_{uu}`). -/
noncomputable def christoffel (Hu Hx Hy : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![!![0, 0, 0, 0; 0, -Hu / 2, -Hx / 2, -Hy / 2; 0, -Hx / 2, 0, 0; 0, -Hy / 2, 0, 0],
    0,
    !![0, 0, 0, 0; 0, -Hx / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, -Hy / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]]

/-- **The coordinate derivatives of the connection** `∂_κ Γ` (`∂_v = 0`; the second partials of `H`). -/
noncomputable def connDeriv (Huu Hux Huy Hxx Hxy Hyy : ℝ) :
    Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 0, 0, 0],
    ![!![0, 0, 0, 0; 0, -Huu / 2, -Hux / 2, -Huy / 2; 0, -Hux / 2, 0, 0; 0, -Huy / 2, 0, 0],
      0,
      !![0, 0, 0, 0; 0, -Hux / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![0, 0, 0, 0; 0, -Huy / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]],
    ![!![0, 0, 0, 0; 0, -Hux / 2, -Hxx / 2, -Hxy / 2; 0, -Hxx / 2, 0, 0; 0, -Hxy / 2, 0, 0],
      0,
      !![0, 0, 0, 0; 0, -Hxx / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![0, 0, 0, 0; 0, -Hxy / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]],
    ![!![0, 0, 0, 0; 0, -Huy / 2, -Hxy / 2, -Hyy / 2; 0, -Hxy / 2, 0, 0; 0, -Hyy / 2, 0, 0],
      0,
      !![0, 0, 0, 0; 0, -Hxy / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
      !![0, 0, 0, 0; 0, -Hyy / 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]]]

/-- The reduction that turns one Ricci component of the pp-wave connection into raw arithmetic:
unfold the `∂Γ − ∂Γ + ΓΓ` contraction, expand the `Fin 4` sums, and read off the matrix-literal
entries. Stated with explicit `OfNat` indices only — the `Matrix.cons_val_*` lemmas do not match
the `Fin.mk` literals produced by `fin_cases`. -/
macro "ppwave_reduce" : tactic =>
  `(tactic| simp only [ricciFromConnection, riemannFromConnection, christoffel, connDeriv,
      Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.zero_apply, Pi.zero_apply, Matrix.zero_empty])

/-- **`R_{uu} = −½ (H_{xx} + H_{yy})`** — the single nonvanishing Ricci component, from the metric. -/
theorem ricci_uu (Hu Hx Hy Huu Hux Huy Hxx Hxy Hyy : ℝ) :
    ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 1 1
      = -(Hxx + Hyy) / 2 := by
  ppwave_reduce
  ring

/-- **The pp-wave is Ricci-flat iff `H` is transverse-harmonic** `R_{μν} = 0 ⟺ H_{xx} + H_{yy} = 0` — the
vacuum Einstein equation is the transverse Laplace equation (Harada Eq. 31). The sixteen components are
proved at explicit indices (fifteen are `ring` identities — the `ΓΓ` terms cancel; `(u,u)` is `ricci_uu`)
and the quantifier is dispatched by definitional matching. -/
theorem ppWave_vacuum_iff (Hu Hx Hy Huu Hux Huy Hxx Hxy Hyy : ℝ) :
    (∀ μ ν, ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) μ ν = 0)
      ↔ Hxx + Hyy = 0 := by
  constructor
  · intro h
    have h11 := h 1 1
    rw [ricci_uu] at h11
    linarith
  · intro h μ ν
    have c00 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 0 0 = 0 := by ppwave_reduce; ring
    have c01 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 0 1 = 0 := by ppwave_reduce; ring
    have c02 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 0 2 = 0 := by ppwave_reduce; ring
    have c03 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 0 3 = 0 := by ppwave_reduce; ring
    have c10 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 1 0 = 0 := by ppwave_reduce; ring
    have c11 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 1 1 = 0 := by
      rw [ricci_uu]; linarith
    have c12 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 1 2 = 0 := by ppwave_reduce; ring
    have c13 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 1 3 = 0 := by ppwave_reduce; ring
    have c20 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 2 0 = 0 := by ppwave_reduce; ring
    have c21 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 2 1 = 0 := by ppwave_reduce; ring
    have c22 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 2 2 = 0 := by ppwave_reduce; ring
    have c23 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 2 3 = 0 := by ppwave_reduce; ring
    have c30 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 3 0 = 0 := by ppwave_reduce; ring
    have c31 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 3 1 = 0 := by ppwave_reduce; ring
    have c32 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 3 2 = 0 := by ppwave_reduce; ring
    have c33 : ricciFromConnection (christoffel Hu Hx Hy) (connDeriv Huu Hux Huy Hxx Hxy Hyy) 3 3 = 0 := by ppwave_reduce; ring
    fin_cases μ <;> fin_cases ν <;> assumption

end Physlib.QuantumMechanics.ComplexAction.Curvature.PPWaveRicci
