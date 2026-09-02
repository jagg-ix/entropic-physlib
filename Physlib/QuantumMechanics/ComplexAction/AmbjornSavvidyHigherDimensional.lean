/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl

/-!
# Higher-dimensional invariants, extrinsic curvature, and the ς-index actions (Ambjørn–Savvidy 1996, §4–§6)

Continuing `AmbjornSavvidySteinerWeyl` (Ambjørn–Savvidy hep-th/9606140): the `3D`/`4D` Steiner–Weyl expansions and
discrete invariants (§5–§6), the **total extrinsic curvature** `Θ = Σ(π−α)` with the dynamical-triangulation
relation `A = a·Θ` (Eqs. 31–32), and — the paper's key physics concept — the **generalized `θ(α)`-actions**
`Θ̃ = Σθ(α_ij)` with `θ(α) = (π−α)^ς` (Eqs. 33, 36–37), whose **index `ς`** controls the convergence and critical
properties of the simplicial-gravity partition function.

* **§A — the `4D` Steiner–Weyl expansion (Eq. 65).** `steinerParallel4D`; **`steinerParallel4D_expand`**
  (`Ω + ρV + ρ²S + ρ³A + ρ⁴χ`, coefficients = elementary symmetric functions of the four principal curvatures).
* **§B — higher-dimensional discrete invariants (Eqs. 54–55, 67–68).** `discreteVolume`, `discreteAreaExtrinsic`,
  `discreteDeficitVolume`.
* **§C — extrinsic curvature and dynamical triangulation (Eqs. 31–32).** `extrinsicCurvature`;
  **`dynamicalTriangulation_length_eq_extrinsic`** (`A = a·Θ`).
* **§D — the generalized `θ(α)`-actions and the ς-index (Eqs. 33, 36–37).** `thetaInvariant`, `thetaAbs`,
  `thetaPower`; **`thetaInvariant_thetaPower_one`** (`ς = 1` recovers `Θ`).

**Honest layering.** Exact `ring` / `Finset.sum` / `Real.rpow` identities for the Steiner polynomial, the discrete
invariants, the dynamical-triangulation factorization and the ς-index actions. The solid-angle measures `ω^{(k)}`,
`Ω^{(k)}` on the spherical images, the dual representations and the analytic convergence of the ς-partition
function are the paper's simplicial-geometry analysis, recorded not re-derived.

## References

* J. Ambjørn, G. K. Savvidy, hep-th/9606140, Eqs. 31–33, 36–37, 54–55, 65, 67–68. Continues
  `AmbjornSavvidySteinerWeyl`.


-/

set_option autoImplicit false

open scoped Real BigOperators
open Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyHigherDimensional


/-- The **`4D` parallel-manifold integrand** `∏(R_i + ρ)` (Eq. 65, `n = 5`). -/
noncomputable def steinerParallel4D (R₁ R₂ R₃ R₄ ρ : ℝ) : ℝ :=
  (R₁ + ρ) * (R₂ + ρ) * (R₃ + ρ) * (R₄ + ρ)

/-- **The `4D` Steiner–Weyl expansion (Eq. 65)** `Ω + ρV + ρ²S + ρ³A + ρ⁴χ` — the five coefficients are the
elementary symmetric functions of the four principal curvatures (the integral invariants `μ₄,…,μ₀`: hyper-volume,
volume, area, linear size, Euler character). -/
lemma steinerParallel4D_expand (R₁ R₂ R₃ R₄ ρ : ℝ) :
    steinerParallel4D R₁ R₂ R₃ R₄ ρ
      = R₁ * R₂ * R₃ * R₄
        + (R₁ * R₂ * R₃ + R₁ * R₂ * R₄ + R₁ * R₃ * R₄ + R₂ * R₃ * R₄) * ρ
        + (R₁ * R₂ + R₁ * R₃ + R₁ * R₄ + R₂ * R₃ + R₂ * R₄ + R₃ * R₄) * ρ ^ 2
        + (R₁ + R₂ + R₃ + R₄) * ρ ^ 3 + ρ ^ 4 := by
  unfold steinerParallel4D; ring


variable {ι : Type*}

/-- The **discrete volume** `Σ v` (Eqs. 54, 66) — the total volume of the top-dimensional simplices. -/
noncomputable def discreteVolume (v : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, v i

/-- The **discrete area with the exterior angle** `Σ σ·(π − α)` (Eqs. 55, 67) — the codimension-1 areas times the
exterior dihedral angles. -/
noncomputable def discreteAreaExtrinsic (σ α : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, σ i * (π - α i)

/-- The **discrete deficit-weighted volume** `Σ λ·(2π − Σβ)` (Eqs. 56, the linear invariant `A(M₃)`) — the
codimension-2 sizes times the deficit angles. -/
noncomputable def discreteDeficitVolume (lam deficit : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, lam i * (2 * π - deficit i)


/-- The **total extrinsic curvature** `Θ = Σ(π − α)` (Eq. 31) — the total arc length of the spherical images of
the edges; the discrete extrinsic curvature of the triangulated manifold. -/
noncomputable def extrinsicCurvature (α : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, (π - α i)

/-- **The dynamical-triangulation relation `A = a·Θ` (Eq. 32)** — when every edge has the same length `a` (fixed
link length, as in dynamical triangulation), the linear functional `A(M₂) = Σ λ·(π − α)` is `a` times the total
extrinsic curvature `Θ = Σ(π − α)`. -/
lemma dynamicalTriangulation_length_eq_extrinsic (a : ℝ) (α : ι → ℝ) (s : Finset ι) :
    discreteLength (fun _ => a) α s = a * extrinsicCurvature α s := by
  unfold discreteLength extrinsicCurvature
  rw [Finset.mul_sum]


/-- The **generalized `θ`-action** `Θ̃ = Σ θ(α_ij)` (Eq. 37) — replacing the linear measure `π − α` by a general
function `θ` of the dihedral angle. -/
noncomputable def thetaInvariant (θ : ℝ → ℝ) (α : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, θ (α i)

/-- The **absolute-value action** `θ(α) = |π − α|` (Eq. 33) — the discrete `∫(1/R₁ + 1/R₂)² dS` of Eq. 34. -/
noncomputable def thetaAbs (α : ℝ) : ℝ := |π - α|

/-- The **power-law action** `θ(α) = (π − α)^ς` (Eq. 36) — the **index `ς`** governs the convergence and critical
properties of the simplicial-gravity partition function. -/
noncomputable def thetaPower (ς α : ℝ) : ℝ := (π - α) ^ ς

/-- **The `ς = 1` power-law action is the extrinsic curvature** `θ(α) = (π − α)^1 = π − α` — the linear
(extrinsic-curvature) measure is the `ς = 1` case of the power-law family. -/
lemma thetaPower_one (α : ℝ) : thetaPower 1 α = π - α := Real.rpow_one _

/-- **The `ς = 1` generalized action is `Θ`** — `Θ̃` with `θ = (π − α)^1` is the total extrinsic curvature. -/
lemma thetaInvariant_thetaPower_one (α : ι → ℝ) (s : Finset ι) :
    thetaInvariant (thetaPower 1) α s = extrinsicCurvature α s :=
  Finset.sum_congr rfl (fun i _ => thetaPower_one (α i))

end Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyHigherDimensional
