/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality

/-!
# Alternative actions for quantum gravity: Steiner–Weyl expansion and the gonihedric principle (Ambjørn–Savvidy 1996)

Ambjørn & Savvidy, *Alternative actions for quantum gravity and the intrinsic rigidity of the spacetime*
(hep-th/9606140): the **Steiner–Weyl expansion** of the parallel-manifold hyper-volume generates a sequence of
integral invariants `μ_k` on (piecewise-linear) manifolds — the discrete Einstein–Hilbert action of Regge is one
of them (`μ₂`) — and the **gonihedric principle** produces alternative actions from the deficit angles. This module
formalizes the exact-algebra core and links it to the Regge action of `ComplexReggeActionCausality`.

The Steiner–Weyl expansion for a hyper-surface with principal curvatures `R_i` is the polynomial in the parallel
distance `ρ` (Eqs. 8–9): `μ₀(M^ρ) = ∫ ∏(R_i + ρ) = Σ_k ρ^k μ_k`, whose coefficients are the elementary symmetric
functions of the `R_i` — the integral invariants. In `2D` (Eqs. 15–18) the parallel-surface area is the quadratic
`S(M₂^ρ) = S(M₂) + ρ·A(M₂) + ρ²·χ(M₂)`: the triangle areas, the edge lengths `× (π − α)`, and the vertex deficit
angles `(2π − Σβ)` (Gauss–Bonnet). The gonihedric measures on a vertex's spherical polygon (Eqs. 27–29) are the
area `2π − Σβ`, the curvature `Σ(π − β)`, and the perimeter `Σ(π − α)`.

* **§A — the Steiner–Weyl expansion (Eqs. 8–9).** `steinerParallel2D`/`3D`; **`steinerParallel2D_expand`**,
  **`steinerParallel3D_expand`** (coefficients = elementary symmetric functions = integral invariants).
* **§B — the discrete `2D` area (Eqs. 15–18).** `discreteSteinerArea`; **`steinerParallel2D_eq_discrete`**.
* **§C — deficit angle and the gonihedric measures (Eqs. 14, 27–29).** `deficitAngle`, `gonihedricCurvature`,
  `gonihedricPerimeter`; **`gonihedric_curvature_sub_deficit`**.
* **§D — discrete invariants and the Regge action (Eqs. 16–17, 4).** `discreteArea`, `discreteLength`,
  `reggeEinsteinHilbert`; **`gaussBonnet_totalDeficit`**.

**Honest layering.** Exact `ring` / `Finset.sum` identities for the Steiner polynomial, the discrete area, the
deficit/gonihedric measures and the Gauss–Bonnet total. The Steiner expansion for general piecewise-linear
manifolds, the higher-derivative curvature terms and the solid-angle rigidity of `Eq. 4` are the paper's
simplicial-geometry analysis; `reggeEinsteinHilbert = Σ σ·ω` is the first (Regge / Einstein–Hilbert) term, linking
to `ComplexReggeActionCausality`.

## References

* J. Ambjørn, G. K. Savvidy, hep-th/9606140, Eqs. 4, 8–9, 14–18, 27–29. Simplicial-gravity companion to
  `ComplexReggeActionCausality`.


-/

set_option autoImplicit false

open scoped Real BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl


/-- The **`2D` parallel-surface integrand** `∏(R_i + ρ) = (R₁ + ρ)(R₂ + ρ)` (Eq. 8, `n = 3`). -/
noncomputable def steinerParallel2D (R₁ R₂ ρ : ℝ) : ℝ := (R₁ + ρ) * (R₂ + ρ)

/-- **The `2D` Steiner–Weyl expansion (Eq. 9)** `(R₁ + ρ)(R₂ + ρ) = R₁R₂ + (R₁ + R₂)ρ + ρ²` — the coefficients are
the Gauss curvature `R₁R₂` (`μ₂`), the mean curvature `R₁ + R₂` (`μ₁`) and `1` (`μ₀`). -/
lemma steinerParallel2D_expand (R₁ R₂ ρ : ℝ) :
    steinerParallel2D R₁ R₂ ρ = R₁ * R₂ + (R₁ + R₂) * ρ + ρ ^ 2 := by
  unfold steinerParallel2D; ring

/-- The **`3D` parallel-hypersurface integrand** `(R₁ + ρ)(R₂ + ρ)(R₃ + ρ)` (Eq. 8, `n = 4`). -/
noncomputable def steinerParallel3D (R₁ R₂ R₃ ρ : ℝ) : ℝ := (R₁ + ρ) * (R₂ + ρ) * (R₃ + ρ)

/-- **The `3D` Steiner–Weyl expansion (Eq. 9)** — the coefficients are the elementary symmetric functions of the
principal curvatures (the integral invariants `μ₃, μ₂, μ₁, μ₀`). -/
lemma steinerParallel3D_expand (R₁ R₂ R₃ ρ : ℝ) :
    steinerParallel3D R₁ R₂ R₃ ρ
      = R₁ * R₂ * R₃ + (R₁ * R₂ + R₂ * R₃ + R₁ * R₃) * ρ + (R₁ + R₂ + R₃) * ρ ^ 2 + ρ ^ 3 := by
  unfold steinerParallel3D; ring


/-- The **discrete parallel-surface area** `S(M₂^ρ) = S + ρ·A + ρ²·χ` (Eqs. 15–18) — the Steiner–Weyl quadratic in
`ρ` with the discrete invariants: the total triangle area `S`, the edge functional `A`, and the Euler/deficit term
`χ`. -/
noncomputable def discreteSteinerArea (S A χ ρ : ℝ) : ℝ := S + ρ * A + ρ ^ 2 * χ

/-- **The smooth Steiner integrand is the discrete quadratic** — `(R₁ + ρ)(R₂ + ρ)` is the discrete
`discreteSteinerArea` with `S = R₁R₂`, `A = R₁ + R₂`, `χ = 1`: the smooth and piecewise-linear Steiner expansions
have the same `ρ`-polynomial structure. -/
lemma steinerParallel2D_eq_discrete (R₁ R₂ ρ : ℝ) :
    steinerParallel2D R₁ R₂ ρ = discreteSteinerArea (R₁ * R₂) (R₁ + R₂) 1 ρ := by
  unfold steinerParallel2D discreteSteinerArea; ring


variable {ι : Type*}

/-- The **vertex deficit angle** `2π − Σβ` (Eqs. 14, 18, 27) — the angular defect at a vertex; the area of its
spherical-polygon image, the discrete Gaussian curvature. -/
noncomputable def deficitAngle (β : ι → ℝ) (s : Finset ι) : ℝ := 2 * π - ∑ i ∈ s, β i

/-- The **gonihedric curvature** `Σ(π − β)` on the vertex's spherical polygon (Eq. 28). -/
noncomputable def gonihedricCurvature (β : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, (π - β i)

/-- The **gonihedric perimeter** `Σ(π − α)` on the vertex's spherical polygon (Eq. 29). -/
noncomputable def gonihedricPerimeter (α : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, (π - α i)

/-- **The gonihedric curvature and the deficit differ by `(|s| − 2)π`** — `Σ(π − β) − (2π − Σβ) = (n − 2)π` for a
vertex with `n = |s|` incident angles: the two gonihedric measures (Eqs. 27–28) on the spherical polygon differ by
the polygon's angle sum. -/
lemma gonihedric_curvature_sub_deficit (β : ι → ℝ) (s : Finset ι) :
    gonihedricCurvature β s - deficitAngle β s = ((s.card : ℝ) - 2) * π := by
  unfold gonihedricCurvature deficitAngle
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring


/-- The **discrete area functional** `S(M₂) = Σ σ` (Eq. 16) — the total area of the triangles. -/
noncomputable def discreteArea (σ : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, σ i

/-- The **discrete length functional** `A(M₂) = Σ λ·(π − α)` (Eq. 17) — the edge lengths times the exterior
dihedral angles. -/
noncomputable def discreteLength (lam α : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, lam i * (π - α i)

/-- The **discrete Einstein–Hilbert (Regge) action** `Σ σ·ω` (Eq. 4, first term) — the triangle areas times the
deficit angles, `μ₂`, the discrete Hilbert–Einstein action of Regge (the Regge term of `ComplexReggeActionCausality`). -/
noncomputable def reggeEinsteinHilbert (σ ω : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, σ i * ω i

/-- **Gauss–Bonnet: the total curvature is `2π·(#vertices) − (total angle)`** — summing the vertex deficits
`Σ_v (2π − Σβ_v)` gives `2π·|verts| − Σ_v Σβ_v`, the discrete Gauss–Bonnet total (`= 2πχ` for a closed surface). -/
lemma gaussBonnet_totalDeficit {V : Type*} (totalAngle : V → ℝ) (verts : Finset V) :
    ∑ v ∈ verts, (2 * π - totalAngle v) = 2 * π * (verts.card : ℝ) - ∑ v ∈ verts, totalAngle v := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

end Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl
