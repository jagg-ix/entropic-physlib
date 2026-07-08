/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

/-!
# Greaves–Thomas, footnote 4: the Maxwell–Faraday tensor is `F = dA`

The Maxwell example of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) treats the field
strength `F^{αβ}` as a primitive rank-2 tensor (`PTSymmetricQFT.PTTensorDynamics`). Footnote 4 records the
"nicety" they set aside: **the Maxwell–Faraday tensor is most fundamentally `F = dA`** — the exterior
derivative of the gauge-potential one-form `A` — hence a *covariant antisymmetric rank-2 tensor*. This file
formalizes that fundamental origin and its consequences, in the momentum-space conventions of the PT file
(`∂_μ → k_μ`):

  `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`   (`faraday k A μ ν = k μ * A ν − k ν * A μ`).

Everything the footnote alludes to then follows structurally:

* **§A — `F = dA` is antisymmetric** (`faraday_antisymm`, `faraday_diag`). Being `dA`, `F` is automatically a
  covariant *antisymmetric* rank-2 tensor — no antisymmetry need be imposed.
* **§B — the homogeneous Maxwell equation `dF = 0` is automatic** (`faraday_bianchi`). Since `d² = 0`, the
  Bianchi identity `∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0` holds *identically* for `F = dA` — it is not a
  dynamical constraint but an identity (in the §2.2 sense, a formula in the kernel of every realization of an
  `A`-field).
* **§C — gauge invariance** (`faraday_gauge_invariant`). `F[A + dχ] = F[A]`: `d² = 0` again, so the
  potential is defined only up to `A_μ ↦ A_μ + ∂_μ χ`.
* **§D — `F = dA` is `PT`-invariant** (`faraday_pt`, `faraday_pt_matrix`). `F` is rank-2 and `PT`-invariant
  *because* it is built from two rank-1 objects `k, A` that each flip by `(−1)` under total inversion:
  `(−1)² = +1`. This recovers `PTSymmetricQFT.PTTensorDynamics.fieldStrength_pt_invariant` from the more
  fundamental one-form.
* **§E — the inhomogeneous Maxwell equation from the potential** (`maxwellOp_faraday`). Feeding `F = dA` into
  the rank-1 Maxwell operator gives `∂^ν F_{μν} = ∂_μ(∂·A) − □A_μ` in momentum space — the wave operator on
  `A` (the dynamical equation; in Lorenz gauge `∂·A = 0` it is `−□A_μ = J_μ`).

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.1 Example 1 and footnote 4 (`F = dA`).
* Repo dependencies: `PTSymmetricQFT.PTTensorDynamics` (`maxwellOp`, `fieldStrength_pt_invariant`);
  `PTSymmetricQFT.FormalFieldTheory` (§2.2, the formula/identity framework).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

open Matrix
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics

/-! ## §A — the Maxwell–Faraday tensor as the exterior derivative of the potential one-form -/

/-- **The Maxwell–Faraday tensor `F = dA`** in momentum space: `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`
(`= k_μ A_ν − k_ν A_μ`), the exterior derivative of the gauge-potential one-form `A`. -/
noncomputable def faraday (k A : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => k μ * A ν - k ν * A μ

/-- **[Footnote 4] `F = dA` is a covariant *antisymmetric* rank-2 tensor** `F_{μν} = −F_{νμ}` — automatic
from being an exterior derivative. -/
theorem faraday_antisymm (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    faraday k A μ ν = - faraday k A ν μ := by
  simp only [faraday, Matrix.of_apply]; ring

/-- The diagonal vanishes `F_{μμ} = 0` (antisymmetry). -/
theorem faraday_diag (k A : Fin 4 → ℝ) (μ : Fin 4) : faraday k A μ μ = 0 := by
  simp only [faraday, Matrix.of_apply]; ring

/-! ## §B — the homogeneous Maxwell equation `dF = 0` is automatic -/

/-- **[Homogeneous Maxwell / Bianchi] `dF = 0` holds identically for `F = dA`.**
`∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0` — since `d² = 0`, this is an identity, not a dynamical
constraint. -/
theorem faraday_bianchi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 := by
  simp only [faraday, Matrix.of_apply]; ring

/-! ## §C — gauge invariance -/

/-- **Gauge invariance `F[A + dχ] = F[A]`.** The shift `A_μ ↦ A_μ + ∂_μ χ` (`= A_μ + χ k_μ`) leaves `F`
unchanged — `d² = 0`. -/
theorem faraday_gauge_invariant (k A : Fin 4 → ℝ) (χ : ℝ) :
    faraday k (fun ρ => A ρ + χ * k ρ) = faraday k A := by
  ext μ ν; simp only [faraday, Matrix.of_apply]; ring

/-! ## §D — `F = dA` is `PT`-invariant (rank 2 from two rank-1 objects) -/

/-- **[Footnote 4 + §6] `F = dA` is `PT`-invariant** `F[−k, −A] = F[k, A]`. `F` is a rank-2 tensor, invariant
under total inversion *because* it is built from the rank-1 momentum `k` and rank-1 potential `A`, each of
which flips by `(−1)`: the two flips give `(−1)² = +1`. -/
theorem faraday_pt (k A : Fin 4 → ℝ) : faraday (-k) (-A) = faraday k A := by
  ext μ ν; simp only [faraday, Matrix.of_apply, Pi.neg_apply]; ring

/-- The same `PT`-invariance in the matrix-conjugation form `(−I) F (−I) = F` of
`PTSymmetricQFT.PTTensorDynamics.fieldStrength_pt_invariant` — the two index transformations of a rank-2
tensor. -/
theorem faraday_pt_matrix (k A : Fin 4 → ℝ) :
    (-1 : Matrix (Fin 4) (Fin 4) ℝ) * faraday k A * (-1) = faraday k A :=
  fieldStrength_pt_invariant _

/-! ## §E — the inhomogeneous Maxwell equation from the potential (the wave operator) -/

/-- **[Inhomogeneous Maxwell] `∂^ν F_{μν} = ∂_μ(∂·A) − □A_μ`.** Feeding `F = dA` into the rank-1 Maxwell
operator (`PTSymmetricQFT.PTTensorDynamics.maxwellOp`) gives, in momentum space,
`k_α (A·k) − A_α (k·k)` — the wave operator on the potential `A`. (In Lorenz gauge `∂·A = A·k = 0` this is
`−(k·k) A_α = −□A_α`, the sourced wave equation `−□A = J`.) -/
theorem maxwellOp_faraday (k A : Fin 4 → ℝ) :
    maxwellOp (faraday k A) k
      = fun α => k α * (∑ β, A β * k β) - A α * (∑ β, k β * k β) := by
  funext α
  simp only [maxwellOp, faraday, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro β _; ring

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

end
