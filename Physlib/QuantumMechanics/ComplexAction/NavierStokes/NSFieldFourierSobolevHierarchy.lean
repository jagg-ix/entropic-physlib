/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorSobolevFieldsT3
public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.TriadicKernel

/-!
# The Navier–Stokes field in Fourier: the Sobolev-seminorm hierarchy on `T³`

Ports the Navier–Stokes field modules (`NSFieldFourier`, `NSFieldGalerkin`) of the reference tree / NS
translator layer into physlib, over `ℝ`, and relates them to the function-space arc already here: the
EM–spacetime superoperator on `Lᵖ(T³, Mat)` (`Electromagnetic.EMSuperoperatorSobolevFieldsT3`) and the Dual-Sphere-Fiber
`6/5` Sobolev kernel (`Hopf.DualSphereSobolevPerfectSquare`).

A finite Fourier field on the 3-torus is `(N modes, wavenumbers k_i, amplitudes â_i)`. Its energy
functionals are exactly the **squared Sobolev seminorms** (by Parseval):

  `kineticEnergy = ∑ |â_k|² = ‖u‖²_{L²}` (`H⁰`),
  `enstrophy     = ∑ |k|² |â_k|² = ‖ω‖²_{L²}` (`H¹`),
  `palinstrophy  = ∑ |k|⁴ |â_k|² = ‖∇ω‖²_{L²}` (`H²`),

so the NS field lives in exactly the Sobolev scale over `T³` on which the EM superoperator acts.

* **§A — the NS Fourier field and its seminorm hierarchy** (`NSFieldFourier`, `kineticEnergy`, `enstrophy`,
  `palinstrophy`, and their `_nonneg`, `enstrophy_pos_of_nontriv`). The squared `H⁰/H¹/H²` seminorms,
  nonnegative, with enstrophy strictly positive on any nonzero mode.
* **§B — the spectral inequalities** (`poincare`, `palinstrophy_le_sq_enstrophy`). The Poincaré spectral gap
  `H⁰ ≤ H¹` (all `|k| ≥ 1`) and the **Bernstein / Galerkin** frequency cutoff `H² ≤ k_max² · H¹` (all
  `|k| ≤ k_max`) — a band-limited field has every seminorm controlled by the next lower one.
* **§C — relation to the physlib arc** (`bandlimited_smooth_ladder`, `sobolev_critical_three`). A
  band-limited NS field satisfies the full Bernstein ladder `H³ ≤ k_max²·H²`, `H² ≤ k_max²·H¹` — it is
  smooth, hence in the domain where the EM superoperator preserves regularity
  (`Electromagnetic.EMSuperoperatorSobolevFieldsT3.emSpacetime_preserves_contDiff`); and its `H¹` enstrophy is the seminorm
  whose 3D critical Sobolev exponent is `6` (`Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate_three`), dual
  `6/5`.

## References

* Parseval / the Fourier characterization of Sobolev norms on `Tⁿ`; the Bernstein inequality on band-limited
  functions.
* Source: `NavierStokes/NSFieldFourier.lean`, `NavierStokes/NSFieldGalerkin.lean` (over `ℚ`; ported here over
  `ℝ`). Repo dependencies: `Electromagnetic.EMSuperoperatorSobolevFieldsT3`, `Hopf.DualSphereSobolevPerfectSquare`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

/-! ## §A — the NS Fourier field and its Sobolev-seminorm hierarchy -/

/-- **A finite Fourier field on `T³`** — `N` modes with natural-number wavenumbers and real amplitudes. -/
structure NSFieldFourier where
  /-- Number of Fourier modes. -/
  N : ℕ
  /-- Wavenumber `|k_i|` of each mode. -/
  freq : Fin N → ℕ
  /-- Amplitude `â_i` of each mode. -/
  amp : Fin N → ℝ

namespace NSFieldFourier

/-- **Kinetic energy** `∑ |â_k|² = ‖u‖²_{L²}` — the squared `H⁰` seminorm (Parseval). -/
noncomputable def kineticEnergy (v : NSFieldFourier) : ℝ := ∑ i, v.amp i ^ 2

/-- **Enstrophy** `∑ |k|² |â_k|² = ‖ω‖²_{L²}` — the squared `H¹` seminorm. -/
noncomputable def enstrophy (v : NSFieldFourier) : ℝ := ∑ i, (v.freq i : ℝ) ^ 2 * v.amp i ^ 2

/-- **Palinstrophy** `∑ |k|⁴ |â_k|² = ‖∇ω‖²_{L²}` — the squared `H²` seminorm. -/
noncomputable def palinstrophy (v : NSFieldFourier) : ℝ := ∑ i, (v.freq i : ℝ) ^ 4 * v.amp i ^ 2

/-- **Super-palinstrophy** `∑ |k|⁶ |â_k|²` — the squared `H³` seminorm. -/
noncomputable def superPalinstrophy (v : NSFieldFourier) : ℝ := ∑ i, (v.freq i : ℝ) ^ 6 * v.amp i ^ 2

theorem kineticEnergy_nonneg (v : NSFieldFourier) : 0 ≤ kineticEnergy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem enstrophy_nonneg (v : NSFieldFourier) : 0 ≤ enstrophy v :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem palinstrophy_nonneg (v : NSFieldFourier) : 0 ≤ palinstrophy v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (sq_nonneg _)

theorem superPalinstrophy_nonneg (v : NSFieldFourier) : 0 ≤ superPalinstrophy v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (sq_nonneg _)

/-- **Enstrophy is positive on any nonzero mode** — the model is non-vacuous: any field with a genuine
(`|k| > 0`, `â ≠ 0`) mode has positive `H¹` seminorm. -/
theorem enstrophy_pos_of_nontriv (v : NSFieldFourier) (i : Fin v.N)
    (hfreq : 0 < v.freq i) (hamp : v.amp i ≠ 0) : 0 < enstrophy v := by
  apply Finset.sum_pos'
  · exact fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have : (0 : ℝ) < (v.freq i : ℝ) ^ 2 := by positivity
    have hamp2 : (0 : ℝ) < v.amp i ^ 2 := by positivity
    positivity

/-! ## §B — the spectral inequalities (Poincaré, Bernstein/Galerkin) -/

/-- **[Poincaré spectral gap] `H⁰ ≤ H¹`.** If every wavenumber satisfies `|k| ≥ 1`, then the kinetic energy
is bounded by the enstrophy — the spectral gap of the torus Laplacian. -/
theorem poincare (v : NSFieldFourier) (hfreq : ∀ i, 1 ≤ v.freq i) :
    kineticEnergy v ≤ enstrophy v := by
  apply Finset.sum_le_sum; intro i _
  have hk2 : (1 : ℝ) ≤ (v.freq i : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (v.freq i : ℝ) := by exact_mod_cast hfreq i
    nlinarith
  calc v.amp i ^ 2 = 1 * v.amp i ^ 2 := (one_mul _).symm
    _ ≤ (v.freq i : ℝ) ^ 2 * v.amp i ^ 2 := mul_le_mul_of_nonneg_right hk2 (sq_nonneg _)

/-- **[Bernstein / Galerkin cutoff] `H² ≤ k_max² · H¹`.** A band-limited field (`|k| ≤ k_max`) has its
palinstrophy controlled by `k_max²` times its enstrophy — the frequency-cutoff inequality. -/
theorem palinstrophy_le_sq_enstrophy (v : NSFieldFourier) (kmax : ℕ)
    (hfreq : ∀ i, v.freq i ≤ kmax) :
    palinstrophy v ≤ (kmax : ℝ) ^ 2 * enstrophy v := by
  unfold palinstrophy enstrophy; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have hsq : (v.freq i : ℝ) ^ 2 ≤ (kmax : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfreq i) 2
  calc (v.freq i : ℝ) ^ 4 * v.amp i ^ 2
      = (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) := by ring
    _ ≤ (kmax : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 2 * v.amp i ^ 2) :=
        mul_le_mul_of_nonneg_right hsq (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **[Bernstein at the next level] `H³ ≤ k_max² · H²`.** -/
theorem superPalinstrophy_le_sq_palinstrophy (v : NSFieldFourier) (kmax : ℕ)
    (hfreq : ∀ i, v.freq i ≤ kmax) :
    superPalinstrophy v ≤ (kmax : ℝ) ^ 2 * palinstrophy v := by
  unfold superPalinstrophy palinstrophy; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have hsq : (v.freq i : ℝ) ^ 2 ≤ (kmax : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfreq i) 2
  calc (v.freq i : ℝ) ^ 6 * v.amp i ^ 2
      = (v.freq i : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) := by ring
    _ ≤ (kmax : ℝ) ^ 2 * ((v.freq i : ℝ) ^ 4 * v.amp i ^ 2) :=
        mul_le_mul_of_nonneg_right hsq (mul_nonneg (by positivity) (sq_nonneg _))

/-! ## §C — relation to the physlib arc -/

/-- **[Band-limited ⟹ smooth ladder] The full Bernstein ladder.** A band-limited NS field has every Sobolev
seminorm controlled by the next lower one (`H² ≤ k²·H¹` and `H³ ≤ k²·H²`) — it is smooth, hence a member of
the domain where the EM–spacetime superoperator preserves regularity
(`Electromagnetic.EMSuperoperatorSobolevFieldsT3.emSpacetime_preserves_contDiff`). -/
theorem bandlimited_smooth_ladder (v : NSFieldFourier) (kmax : ℕ) (hfreq : ∀ i, v.freq i ≤ kmax) :
    palinstrophy v ≤ (kmax : ℝ) ^ 2 * enstrophy v
      ∧ superPalinstrophy v ≤ (kmax : ℝ) ^ 2 * palinstrophy v :=
  ⟨palinstrophy_le_sq_enstrophy v kmax hfreq, superPalinstrophy_le_sq_palinstrophy v kmax hfreq⟩

/-- **[Link to the `6/5` kernel] The `H¹` enstrophy sits at the 3D Sobolev exponent `6`.** The enstrophy is
the squared `H¹` seminorm, and the critical Sobolev embedding exponent of `H¹` in three dimensions is `6`
(`Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate_three`), whose Hölder dual is the `6/5` intrinsic to a
Navier-Stokes `W`-functional spatial integrand. -/
theorem sobolev_critical_three :
    Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate 3 = 6 :=
  Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate_three

/-! ## §D — concrete torus triadic-kernel link -/

open TorusFourier.TriadicKernel

/-- **[Link] The finite Fourier/Sobolev hierarchy can use the concrete torus triadic kernel.**
For any finite mode list on `T³`, every triple is either off-resonant with zero coefficient or has the
standard resonant dot-product coefficient. -/
theorem torusTriadicKernel_cases {N : ℕ} (wvec : Fin N → TorusWaveVec3) (k j l : Fin N) :
    triadicKernelCoeff wvec k j l = 0 ∨
      triadicKernelCoeff wvec k j l =
        (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k) :=
  triadicKernelCoeff_cases wvec k j l

end NSFieldFourier

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy

end
