/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

/-!
# Agmon interpolation on the Navier–Stokes Fourier hierarchy

Ports `NavierStokes/NSFourierInequalities.lean` of the reference tree (over `ℚ`; here over `ℝ`)
onto the Sobolev-seminorm hierarchy of `NSFieldFourierSobolevHierarchy`: the Cauchy–Schwarz
**interpolation inequalities** between consecutive squared seminorms, and the two monotone steps
that complete the Poincaré chain.

For a finite Fourier field the seminorms are `∑ |k|^{2m} |â_k|²`; writing the enstrophy summand
as `â_k · (|k|²â_k)` and applying the finite Cauchy–Schwarz inequality
(`Finset.sum_mul_sq_le_sq_mul_sq`) gives, entirely at the squared level — no square roots, no
function spaces:

* `enstrophy_sq_le_kineticEnergy_mul_palinstrophy` — **the discrete Agmon inequality**
  `Ω² ≤ E·P`: the `H¹` seminorm interpolates between `H⁰` and `H²`,
  the finite-mode analogue of `‖ω‖²_{L²} ≤ ‖u‖_{L²}·‖∇ω‖_{L²}` (Agmon 1965).
* `palinstrophy_sq_le_enstrophy_mul_superPalinstrophy` — the same interpolation one rung up,
  `P² ≤ Ω·S` (`H²` between `H¹` and `H³`).
* `enstrophy_le_palinstrophy`, `palinstrophy_le_superPalinstrophy` — under the spectral gap
  `|k| ≥ 1` the hierarchy is monotone, extending the existing `poincare` (`E ≤ Ω`) to the full
  chain `E ≤ Ω ≤ P ≤ S`.

Together with the Bernstein cutoff lemmas already in the hierarchy module
(`palinstrophy_le_sq_enstrophy`, `superPalinstrophy_le_sq_palinstrophy`), a band-limited field
has every seminorm pinched between its neighbours from both sides — the algebraic skeleton of
the Poincaré–Agmon chain used in the enstrophy bootstrap.

## References

* S. Agmon, *Lectures on Elliptic Boundary Value Problems* (1965) — the interpolation
  inequality; C. Foias, O. Manley, R. Rosa, R. Temam, *Navier–Stokes Equations and Turbulence*
  (2001), Ch. II.  Source: `NavierStokes/NSFourierInequalities.lean` (reference tree, own
  authorship), re-authored over `ℝ` on the physlib hierarchy.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

namespace NSFieldFourier

/-- **The discrete Agmon inequality** `Ω² ≤ E·P`: the squared enstrophy is bounded by kinetic
energy times palinstrophy — Cauchy–Schwarz with `f_k = â_k`, `g_k = |k|²â_k`, entirely at the
squared level. -/
theorem enstrophy_sq_le_kineticEnergy_mul_palinstrophy (v : NSFieldFourier) :
    enstrophy v ^ 2 ≤ kineticEnergy v * palinstrophy v := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => v.amp i) (fun i => (v.freq i : ℝ) ^ 2 * v.amp i)
  calc enstrophy v ^ 2
      = (∑ i, v.amp i * ((v.freq i : ℝ) ^ 2 * v.amp i)) ^ 2 := by
        unfold enstrophy
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (∑ i, v.amp i ^ 2) * ∑ i, ((v.freq i : ℝ) ^ 2 * v.amp i) ^ 2 := cs
    _ = kineticEnergy v * palinstrophy v := by
        unfold kineticEnergy palinstrophy
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Agmon interpolation one rung up** `P² ≤ Ω·S`: squared palinstrophy is bounded by
enstrophy times super-palinstrophy — Cauchy–Schwarz with `f_k = |k|â_k`, `g_k = |k|³â_k`. -/
theorem palinstrophy_sq_le_enstrophy_mul_superPalinstrophy (v : NSFieldFourier) :
    palinstrophy v ^ 2 ≤ enstrophy v * superPalinstrophy v := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => (v.freq i : ℝ) * v.amp i) (fun i => (v.freq i : ℝ) ^ 3 * v.amp i)
  calc palinstrophy v ^ 2
      = (∑ i, ((v.freq i : ℝ) * v.amp i) * ((v.freq i : ℝ) ^ 3 * v.amp i)) ^ 2 := by
        unfold palinstrophy
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (∑ i, ((v.freq i : ℝ) * v.amp i) ^ 2)
        * ∑ i, ((v.freq i : ℝ) ^ 3 * v.amp i) ^ 2 := cs
    _ = enstrophy v * superPalinstrophy v := by
        unfold enstrophy superPalinstrophy
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · exact Finset.sum_congr rfl fun i _ => by ring

/-- Under the spectral gap `|k| ≥ 1` the enstrophy is bounded by the palinstrophy — the second
step of the monotone chain `E ≤ Ω ≤ P ≤ S` (the first is `poincare`). -/
theorem enstrophy_le_palinstrophy (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i) :
    enstrophy v ≤ palinstrophy v := by
  unfold enstrophy palinstrophy
  refine Finset.sum_le_sum fun i _ => ?_
  have hk : (1 : ℝ) ≤ (v.freq i : ℝ) := by exact_mod_cast hfreq i
  have hk2 : (1 : ℝ) ≤ (v.freq i : ℝ) ^ 2 := one_le_pow₀ hk
  calc (v.freq i : ℝ) ^ 2 * v.amp i ^ 2
      = 1 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := by ring
    _ ≤ (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) :=
        mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = (v.freq i : ℝ) ^ 4 * v.amp i ^ 2 := by ring

/-- Under the spectral gap `|k| ≥ 1` the palinstrophy is bounded by the super-palinstrophy —
the third step of the monotone chain `E ≤ Ω ≤ P ≤ S`. -/
theorem palinstrophy_le_superPalinstrophy (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i) :
    palinstrophy v ≤ superPalinstrophy v := by
  unfold palinstrophy superPalinstrophy
  refine Finset.sum_le_sum fun i _ => ?_
  have hk : (1 : ℝ) ≤ (v.freq i : ℝ) := by exact_mod_cast hfreq i
  have hk2 : (1 : ℝ) ≤ (v.freq i : ℝ) ^ 2 := one_le_pow₀ hk
  calc (v.freq i : ℝ) ^ 4 * v.amp i ^ 2
      = 1 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) := by ring
    _ ≤ (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) :=
        mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = (v.freq i : ℝ) ^ 6 * v.amp i ^ 2 := by ring

end NSFieldFourier

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

end
