/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.HubbleEvolution
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

/-!
# The FRW metric as a Levi-Civita comoving-cotetrad congruence

Links the FLRW cosmology layer (`Cosmology.FLRW`, the Friedmann/Hubble dynamics) to the Levi-Civita / Lusanna
tetrad-invariance framework (`LeviCivita.TetradInvariant`: the metric as a congruence `g = EᵀηE =
coordCongruence E η` of the flat Minkowski metric, with the cotetrad `E` the coordinate Jacobian).

The (spatially flat) FRW metric is exactly such a congruence. Its **comoving cotetrad** is the diagonal map
with the local Minkowski frame to comoving coordinates,

  `E_FRW = diag(c, a, a, a)`   (`frwCotetrad`, `a` the scale factor, `c` the light speed),

and the congruence reproduces the FRW line element:

  `tetradMetric E_FRW = EᵀηE = diag(c², −a², −a², −a²)`   (`frwCotetrad_tetradMetric`),
  `xᵀ g_FRW x = c²(x⁰)² − a²|x⃗|²`   (`frw_properSeparationSq`),

so the proper interval is `c²t² − a²|x⃗|²` — Minkowski with the scale factor `a` rescaling the spatial part.
Being a cotetrad congruence, the FRW proper interval is **local-Lorentz-gauge-invariant**
(`frw_properSeparation_lorentz_invariant`): the `SO(1,3)` frame freedom at each comoving point is pure
inertial gauge, exactly as for any metric in the Levi-Civita framework. Evaluated along the Friedmann scale
factor `a(t)` this ties the cosmological dynamics (`HubbleEvolution`) to the tetrad-invariant geometry
(`frw_scaleFactor_tetrad_congruence`).

* **§A — the comoving cotetrad and its metric** (`frwCotetrad`, `frwCotetrad_tetradMetric`,
  `frw_properSeparationSq`).
* **§B — gauge invariance and the Friedmann link** (`frw_properSeparation_lorentz_invariant`,
  `frw_scaleFactor_tetrad_congruence`).

## References

* FLRW cosmology; T. Levi-Civita / L. Lusanna (the cotetrad congruence and local-Lorentz gauge). structures:
  `Cosmology.FLRW.FriedmannEquation`, `LeviCivita.TetradInvariant` (`tetradMetric`, `coordCongruence`,
  `properSeparationSq`, `properSeparationSq_lorentz_gauge`), `Physlib.Relativity` (`minkowskiMatrix`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Cosmology.FLRW.LeviCivitaTetrad

open Matrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

/-! ## §A — the comoving cotetrad and its metric -/

/-- **The FRW comoving cotetrad** `E_FRW = diag(c, a, a, a)` — the coordinate Jacobian taking the local
Minkowski frame to comoving coordinates, with `a` the scale factor and `c` the light speed. -/
noncomputable def frwCotetrad (a c : ℝ) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => c) (fun _ => a))

/-- **[The FRW metric is the comoving cotetrad congruence] `EᵀηE = diag(c², −a², −a², −a²)`.** The flat FRW
metric is the Minkowski metric referred to comoving coordinates, with the scale factor `a` rescaling the
spatial block. -/
theorem frwCotetrad_tetradMetric (a c : ℝ) :
    tetradMetric (frwCotetrad a c)
      = Matrix.diagonal (Sum.elim (fun _ => c ^ 2) (fun _ => -a ^ 2)) := by
  rw [tetradMetric_eq_coordCongruence]
  simp only [coordCongruence, frwCotetrad]
  rw [diagonal_transpose, minkowskiMatrix.as_diagonal, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  cases i <;> simp <;> ring

/-- **[The FRW proper interval] `xᵀ g_FRW x = c²(x⁰)² − a²|x⃗|²`.** The comoving line element: Minkowski with
the scale factor rescaling the spatial part. -/
theorem frw_properSeparationSq (a c : ℝ) (x : (Fin 1 ⊕ Fin 3) → ℝ) :
    properSeparationSq (frwCotetrad a c) x
      = c ^ 2 * (x (Sum.inl 0)) ^ 2 - a ^ 2 * ∑ j : Fin 3, (x (Sum.inr j)) ^ 2 := by
  simp only [properSeparationSq]
  rw [frwCotetrad_tetradMetric, dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_diagonal, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
  have hsum : ∑ j : Fin 3, x (Sum.inr j) * (-a ^ 2 * x (Sum.inr j))
      = -a ^ 2 * ∑ j : Fin 3, (x (Sum.inr j)) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]; ring

/-! ## §B — gauge invariance and the Friedmann link -/

/-- **[The FRW proper interval is local-Lorentz-gauge-invariant] `xᵀ g[ΛE_FRW] x = xᵀ g[E_FRW] x`.** As a
cotetrad congruence, the FRW interval is unchanged by a local Lorentz frame rotation `E ↦ ΛE`, `Λ ∈ SO(1,3)`
— the inertial frame freedom at each comoving point is pure gauge. -/
theorem frw_properSeparation_lorentz_invariant {Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ}
    (hΛ : Λ ∈ LorentzGroup 3) (a c : ℝ) (x : (Fin 1 ⊕ Fin 3) → ℝ) :
    properSeparationSq (Λ * frwCotetrad a c) x = properSeparationSq (frwCotetrad a c) x :=
  properSeparationSq_lorentz_gauge hΛ x

/-- **[The Friedmann scale factor as a comoving cotetrad].** Evaluated along the Friedmann scale factor
`a(t)`, the FRW metric at cosmic time `t` is the comoving congruence `diag(c², −a(t)², −a(t)², −a(t)²)`, whose
proper interval is local-Lorentz-gauge-invariant. This links the cosmological dynamics (`HubbleEvolution`,
the Friedmann equations for `a`) to the Levi-Civita tetrad-invariant geometry: cosmic expansion is the
comoving cotetrad's spatial component `a(t)` evolving in time. -/
theorem frw_scaleFactor_tetrad_congruence (a : Time → ℝ) (c : ℝ) (t : Time)
    {Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} (hΛ : Λ ∈ LorentzGroup 3)
    (x : (Fin 1 ⊕ Fin 3) → ℝ) :
    tetradMetric (frwCotetrad (a t) c)
        = Matrix.diagonal (Sum.elim (fun _ => c ^ 2) (fun _ => -(a t) ^ 2))
      ∧ properSeparationSq (Λ * frwCotetrad (a t) c) x
        = properSeparationSq (frwCotetrad (a t) c) x :=
  ⟨frwCotetrad_tetradMetric (a t) c, frw_properSeparation_lorentz_invariant hΛ (a t) c x⟩

end Cosmology.FLRW.LeviCivitaTetrad

end
