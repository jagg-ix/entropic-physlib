/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Physlib.Relativity.SemiClassical.SchwarzschildHorizonEntropicTime
public import Physlib.Thermodynamics.VerlindeNewtonGravity

/-!
# The interior Schwarzschild metric of Barletta–Dragomir–Magliaro's foliated space-time

Formalizes the algebraic core of the Schwarzschild application (§1) of E. Barletta, S. Dragomir, M. Magliaro,
*Schmidt boundaries of foliated space-times*, Class. Quantum Grav. 31 (2014) 205012. The paper builds the
Schmidt `b`-boundary of a foliated Lorentzian manifold (frame bundles, `b`-completion, transverse Lorentzian
geometry — machinery beyond a proof assistant) and applies it to the interior Schwarzschild region
`𝔐 = ℝ × (0, 2m) × S²`, where the metric is written (their Eq. 2) as

  `g = b(r)⁻² (dx⁰)² − b(r)² dr² + a(r)² (dθ² + sin²θ dφ²)`,   `b(r) = (2m/r − 1)^{−1/2}`,  `a(r) = r`.

The lapse `b(r)⁻² = 2m/r − 1` is exactly minus the Schwarzschild function `1 − 2m/r`: inside the horizon
(`0 < r < 2m`) it is positive, `b(r)` is real, and the roles of `t` and `r` are interchanged (`r` becomes
timelike) — this is the region on whose `r → 0` singularity the `b`-boundary attaches. This module formalizes
the tractable, self-contained part:

* **§A — the interior lapse functions.** `barlettaBInvSq = 2m/r − 1`, `barlettaBSq = r/(2m − r)`,
  `barlettaA = r`, with `barlettaBSq_mul_bInvSq`: `b² · b⁻² = 1` on `0 < r < 2m`.
* **§B — the horizon and the interior signature flip.** `barlettaBInvSq_zero_iff_horizon` (`b⁻² = 0 ⟺ r = 2m`)
  and `barlettaBInvSq_pos_iff` (`0 < b⁻² ⟺ r < 2m`): inside the horizon the lapse is positive and `b(r)` is
  real, so `𝔐 = ℝ × (0, 2m) × S²` is Lorentzian with `t` and `r` swapped.
* **§C — the diagonal metric (Eq. 2) and its volume determinant.** `barlettaMetric` and
  `barlettaMetric_det`: `det g = −r⁴ sin²θ` (via `b²b⁻² = 1`), so the volume element is `√|g| = r² sinθ` — the
  standard Schwarzschild volume form, regular for `r > 0` and degenerating at the `r → 0` singularity.

* **§D — the horizon area and the ER=EPR entropy–energy test.** The horizon 2-sphere `r = 2m` bounding the
  interior is the Schwarzschild radius `R_g = 2GM/c²` (`barlettaHorizonRadius_eq_schwarzschildRadius`), of area
  `A = 4πR_g² = 16πG²M²/c⁴` (`schwarzschildArea_eq_sphereArea`); its Bekenstein–Hawking entropy `bhEntropy`
  (Dai–Minic–Stojkovic–Fu, *Testing the ER=EPR conjecture*, Phys. Rev. D 102 (2020) 066004, Eq. 8)
  `S_BH = k_B c³ A/(4Gℏ) = k_B·4πGM²/(ℏc)` (`bhEntropy_eq_mass`) equals one bit `k_B ln 2` exactly at the
  wormhole mass `M = √(ℏc ln2/(4πG))` (`erEpr_wormholeMass`, their Eq. 10).

Reuses (GREP-first) Mathlib `Matrix.det_diagonal` / `Fin.prod_univ_four` / `Matrix.diagonal`, and physlib's
`Relativity.SemiClassical.schwarzschildRadius` / `schwarzschildArea` and `Thermodynamics.sphereArea`.

## References

* E. Barletta, S. Dragomir, M. Magliaro, Class. Quantum Grav. 31 (2014) 205012, Eq. 1–2, §1; K. Schmidt,
  Gen. Rel. Grav. 1 (1971) 269 (`b`-boundary); D.-C. Dai, D. Minic, D. Stojkovic, C. Fu, Phys. Rev. D 102
  (2020) 066004, Eq. 8–10 (ER=EPR entropy–energy test). Carriers: `Relativity.SemiClassical`
  (`schwarzschildRadius`, `schwarzschildArea`), `Thermodynamics.sphereArea`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric

/-! ### §A The interior lapse functions and their identities -/

/-- **[Barletta's inverse-square lapse] `b(r)⁻² = 2m/r − 1`** — the coefficient of `(dx⁰)²` in the interior
Schwarzschild metric (Eq. 2); minus the Schwarzschild function `1 − 2m/r`. -/
noncomputable def barlettaBInvSq (m r : ℝ) : ℝ := 2 * m / r - 1

/-- **[Barletta's square lapse] `b(r)² = r/(2m − r)`** — the coefficient of `−dr²` in Eq. 2, real and positive
on the interior `0 < r < 2m`. -/
noncomputable def barlettaBSq (m r : ℝ) : ℝ := r / (2 * m - r)

/-- **[Barletta's transverse radius] `a(r) = r`** — the coefficient function of the `S²` block. -/
def barlettaA (r : ℝ) : ℝ := r

/-- **[The two lapse forms are reciprocal] `b(r)² · b(r)⁻² = 1`** on `0 < r < 2m` (`r ≠ 0`, `r ≠ 2m`) — so
`b(r)²` and `b(r)⁻²` are genuine reciprocals, as the notation demands. -/
theorem barlettaBSq_mul_bInvSq (m r : ℝ) (hr : r ≠ 0) (h2m : r ≠ 2 * m) :
    barlettaBSq m r * barlettaBInvSq m r = 1 := by
  have h2mr : 2 * m - r ≠ 0 := fun h => h2m (by linarith)
  simp only [barlettaBSq, barlettaBInvSq]
  field_simp

/-! ### §B The horizon and the interior signature flip -/

/-- **[The horizon is `r = 2m`] `b(r)⁻² = 0 ⟺ r = 2m`** (for `r > 0`) — the lapse vanishes exactly on the
Schwarzschild horizon. -/
theorem barlettaBInvSq_zero_iff_horizon (m r : ℝ) (hr : 0 < r) :
    barlettaBInvSq m r = 0 ↔ r = 2 * m := by
  rw [barlettaBInvSq, sub_eq_zero, div_eq_one_iff_eq hr.ne', eq_comm]

/-- **[Inside the horizon the metric signature flips] `0 < b(r)⁻² ⟺ r < 2m`** (for `r > 0`). On the interior
`0 < r < 2m` the lapse `2m/r − 1` is positive, so `b(r)` is real and in Barletta's Eq. 2 the `t`-direction is
spacelike while `r` is timelike: `𝔐 = ℝ × (0, 2m) × S²` is a Lorentzian manifold with `t` and `r`
interchanged. -/
theorem barlettaBInvSq_pos_iff (m r : ℝ) (hr : 0 < r) :
    0 < barlettaBInvSq m r ↔ r < 2 * m := by
  rw [barlettaBInvSq, sub_pos, lt_div_iff₀ hr, one_mul]

/-! ### §C The diagonal metric (Eq. 2) and its volume determinant -/

/-- **[Barletta's interior Schwarzschild metric (Eq. 2)] `g = diag(b⁻², −b², a², a²sin²θ)`** in coordinates
`(x⁰, r, θ, φ)`. -/
noncomputable def barlettaMetric (m r θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![barlettaBInvSq m r, -barlettaBSq m r, (barlettaA r) ^ 2,
    (barlettaA r) ^ 2 * Real.sin θ ^ 2]

/-- **[The `(dx⁰)²` component is the lapse] `g₀₀ = b(r)⁻²`.** The metric's time–time entry is Barletta's
inverse-square lapse. -/
theorem barlettaMetric_tt (m r θ : ℝ) : barlettaMetric m r θ 0 0 = barlettaBInvSq m r := by
  rw [barlettaMetric, Matrix.diagonal_apply_eq, Matrix.cons_val_zero]

/-- **[The Schwarzschild volume determinant] `det g = −r⁴ sin²θ`** on `0 < r < 2m`. The reciprocal identity
`b²b⁻² = 1` collapses the lapse factors, leaving the standard Schwarzschild determinant, so the volume element
is `√|g| = r² sinθ` — regular for `r > 0` and degenerating at the `r → 0` curvature singularity where the
`b`-boundary attaches. -/
theorem barlettaMetric_det (m r θ : ℝ) (hr : r ≠ 0) (h2m : r ≠ 2 * m) :
    (barlettaMetric m r θ).det = -(r ^ 4 * Real.sin θ ^ 2) := by
  have hbb : barlettaBInvSq m r * barlettaBSq m r = 1 := by
    rw [mul_comm]; exact barlettaBSq_mul_bInvSq m r hr h2m
  rw [barlettaMetric, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [barlettaA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  linear_combination (-(r ^ 4 * Real.sin θ ^ 2)) * hbb

/-! ### §D The horizon area and the ER=EPR entropy–energy test (Phys. Rev. D 102 (2020) 066004) -/

open Physlib.Relativity.SemiClassical Physlib.Thermodynamics

/-- **[Barletta's horizon radius is the Schwarzschild radius] `r = 2m = R_g = 2GM/c²`.** The 2-sphere
`r = 2m` bounding the interior region is exactly the Schwarzschild horizon (physlib's `schwarzschildRadius`),
with the geometric mass `m = GM/c²`. -/
theorem barlettaHorizonRadius_eq_schwarzschildRadius (M G c : ℝ) :
    2 * (G * M / c ^ 2) = schwarzschildRadius M G c := by
  simp only [schwarzschildRadius]; ring

/-- **[The horizon area is `4πR_g²`] `schwarzschildArea = sphereArea(R_g)`.** The area of the horizon
2-sphere (from Barletta's angular block `a² = r²`) is `A = 4πR_g² = 16πG²M²/c⁴`, connecting physlib's
`schwarzschildArea` to `sphereArea` of the radius. -/
theorem schwarzschildArea_eq_sphereArea (M G c : ℝ) (hc : c ≠ 0) :
    schwarzschildArea M G c = sphereArea (schwarzschildRadius M G c) := by
  simp only [schwarzschildArea, sphereArea, schwarzschildRadius]
  field_simp
  ring

/-- **[Bekenstein–Hawking entropy, Eq. 8] `S_BH = k_B c³ A/(4Gℏ)`** — the entanglement entropy of the ER=EPR
wormhole, read off the horizon area `A = schwarzschildArea`. -/
noncomputable def bhEntropy (M G c ℏ kB : ℝ) : ℝ :=
  kB * c ^ 3 * schwarzschildArea M G c / (4 * G * ℏ)

/-- **[The Bekenstein–Hawking entropy in mass form] `S_BH = k_B·4πGM²/(ℏc)`.** Substituting the horizon area
`A = 16πG²M²/c⁴` into Eq. 8 collapses the constants. -/
theorem bhEntropy_eq_mass (M G c ℏ kB : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) :
    bhEntropy M G c ℏ kB = kB * (4 * Real.pi * G * M ^ 2 / (ℏ * c)) := by
  simp only [bhEntropy, schwarzschildArea]
  field_simp
  ring

/-- **[ER=EPR wormhole mass, Eq. 10] one bit of entanglement fixes the mass `M = √(ℏc ln2/(4πG))`.** The
Dai–Minic–Stojkovic–Fu test: substituting the positive mass that algebraically inverts the one-bit entropy
condition gives `M = √(ℏc ln2/(4πG)) ≈ 5.1 × 10⁻⁹ kg`. The inversion is not independently predictive, but
its enormous mismatch with an `e⁺e⁻` mass is the quantitative tension exposed once the one-bit ER=EPR
identification is assumed. -/
theorem erEpr_wormholeMass (G c ℏ kB : ℝ) (hG : 0 < G) (hc : 0 < c) (hℏ : 0 < ℏ) :
    bhEntropy (Real.sqrt (ℏ * c * Real.log 2 / (4 * Real.pi * G))) G c ℏ kB = kB * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (0 : ℝ) ≤ ℏ * c * Real.log 2 / (4 * Real.pi * G) := by positivity
  rw [bhEntropy_eq_mass _ G c ℏ kB hG.ne' hc.ne' hℏ.ne', Real.sq_sqrt hK]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric

end
