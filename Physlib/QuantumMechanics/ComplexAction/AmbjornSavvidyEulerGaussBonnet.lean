/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyHigherDimensional

/-!
# The general Regge action, the Euler character, and the Gauss–Bonnet density (Ambjørn–Savvidy 1996, §6–§7)

The final sections of Ambjørn–Savvidy (hep-th/9606140): the **general `d`-dimensional Hilbert–Einstein (Regge)
action** `Σ v^{(d-2)}·ω²` (Eqs. 89–92), the discrete **Euler–Poincaré character** in terms of simplex counts and
deficit angles (Eqs. 81, 83, 86), and the continuum **Gauss–Bonnet density** `R²_{μνλρ} − 4R²_{μν} + R²` (Eq. 87)
whose integral is `128π²·χ(M₄)`.

* **§A — the general `d`-dimensional Regge action (Eqs. 89–92).** **`generalDim_hilbertEinstein_eq_regge`**
  (`Σ v^{(d-2)}·ω² = reggeEinsteinHilbert`).
* **§B — the discrete Euler character (Eqs. 81, 83).** **`eulerCharacteristic2D_closed`** (`χ = N₀ − N₂/2`),
  `discreteEuler4D`.
* **§C — the Euler character from deficits (Eq. 86).** `euler4D_fromDeficit` (`χ(M₄) = Ω⁴_tot − ½ω²_tot`).
* **§D — the continuum Gauss–Bonnet density (Eq. 87).** `eulerDensity4D`
  (`R²_{μνλρ} − 4R²_{μν} + R²`, the Gauss–Bonnet / Euler class, cf. `Curvature.GaussBonnetPontryaginSelfDual`),
  `eulerCharacteristic4D_continuum`.

**Honest layering.** Exact `ring` / `Finset.sum` identities for the general Regge action, the Euler counting and
the density combination. The intrinsicness of the deficit invariants (via the vertex Gauss–Bonnet relations
Eqs. 80, 82) and the analytic `χ = (1/128π²)∫(R²_{μνλρ} − 4R²_{μν} + R²)` are the paper's differential-geometry
content, recorded not re-derived. The `2D` closed-surface Euler counting `N₀ − N₁ + N₂ = N₀ − N₂/2` (from
`N₁ = 3N₂/2`) is exact.

## References

* J. Ambjørn, G. K. Savvidy, hep-th/9606140, Eqs. 81, 83, 86, 87, 91. Concludes `AmbjornSavvidyHigherDimensional`;
  the Euler density links to `Curvature.GaussBonnetPontryaginSelfDual`.


-/

set_option autoImplicit false

open scoped Real BigOperators
open Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyEulerGaussBonnet


/-- **The general `d`-dimensional Hilbert–Einstein (Regge) action is `Σ v^{(d-2)}·ω²`** (Eq. 91) — the volume of
the codimension-2 simplices times the deficit angles, in *any* dimension, is the Regge action
(`AmbjornSavvidySteinerWeyl.reggeEinsteinHilbert`). The Regge/Einstein–Hilbert form `Σ σ·ω` is dimension-universal.
-/
lemma generalDim_hilbertEinstein_eq_regge {ι : Type*} (v ω : ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, v i * ω i = reggeEinsteinHilbert v ω s := rfl


/-- **The Euler character of a closed triangulated surface is `N₀ − N₂/2`** (Eq. 81) — from the Euler formula
`χ = N₀ − N₁ + N₂` and the closed-surface edge relation `N₁ = 3N₂/2` (each triangle has 3 edges, each edge borders
2 triangles). -/
lemma eulerCharacteristic2D_closed (N₀ N₁ N₂ : ℝ) (h : N₁ = 3 * N₂ / 2) :
    N₀ - N₁ + N₂ = N₀ - N₂ / 2 := by rw [h]; ring

/-- **The discrete `4D` Euler character** `χ(M₄) = N₀ − N₂/2 + N₄` (Eq. 83) — vertices, triangles and
four-simplices. -/
noncomputable def discreteEuler4D (N₀ N₂ N₄ : ℝ) : ℝ := N₀ - N₂ / 2 + N₄


/-- **The `4D` Euler character from the total deficits** `χ(M₄) = Ω⁴_tot − ½ω²_tot` (Eq. 86) — the total solid
deficit angle minus half the total (`2D`) deficit angle. -/
noncomputable def euler4D_fromDeficit (solidDeficitTot deficitTot : ℝ) : ℝ :=
  solidDeficitTot - deficitTot / 2


/-- **The `4D` Gauss–Bonnet / Euler density** `R²_{μνλρ} − 4R²_{μν} + R²` (Eq. 87) — the curvature-squared
combination whose integral is `128π²·χ(M₄)`; the Euler class (the second Lovelock term / Gauss–Bonnet invariant,
cf. `Curvature.GaussBonnetPontryaginSelfDual`). -/
noncomputable def eulerDensity4D (riemannSq ricciSq scalarSq : ℝ) : ℝ :=
  riemannSq - 4 * ricciSq + scalarSq

/-- **The continuum Euler–Poincaré character** `χ(M₄) = (1/128π²) ∫(R²_{μνλρ} − 4R²_{μν} + R²)` (Eq. 87) — the
Gauss–Bonnet integral normalized by `128π²`. -/
noncomputable def eulerCharacteristic4D_continuum (integralEulerDensity : ℝ) : ℝ :=
  integralEulerDensity / (128 * π ^ 2)

/-- **At zero curvature the Euler density vanishes** — a flat metric contributes nothing to the Gauss–Bonnet
integral. -/
@[simp] lemma eulerDensity4D_flat : eulerDensity4D 0 0 0 = 0 := by
  simp [eulerDensity4D]

end Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyEulerGaussBonnet
