/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.TriadicKernel
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-!
# Vector-amplitude spectral fields: the join of the wavevector and vorticity structure

`NSFieldFourier` carries wavenumber *magnitudes* and *scalar* amplitudes, so the vortex stretching definable
on it is only the mode-diagonal shell surrogate
(`FieldLevelConfinementBridge.vortexStretchingDiagonal`).  `TorusFourier.TriadicKernel` carries genuine
integer wavevectors on `T³` and the resonance condition `k = j + l`, but no amplitudes.  This module joins
them: a spectral field with **integer wavevectors and real vector amplitudes**, which is the structure a true
vorticity — and hence a true triadic vortex stretching — requires.

The payoff is a grounding theorem for the entire entropic arc.  Throughout, "enstrophy" has been *defined* as
the weighted sum `∑ |k_i|²|â_i|²`.  Here vorticity is built honestly — `ω̂_i = k_i × â_i`, the Fourier
transform of `∇ × u` — and its squared magnitude is computed by the Lagrange identity
(`Hopf.DualSphereFiberDecomposition.crossSphereDefect_lagrange`):

  `|k × â|² = |k|²|â|² − ⟨k, â⟩²`,

so on the **divergence-free** modes `⟨k, â⟩ = 0` that incompressibility demands,

  `|ω̂_i|² = |k_i|² |â_i|²`     (`modeVorticitySq_divFree`).

Summing (`enstrophy_eq_weighted`): the arc's weighted-sum definition of enstrophy **is** the vorticity `L²`
norm, for genuinely divergence-free vector fields.  What was a definitional choice is now a theorem about
`∇ × u`.  The same computation grounds the palinstrophy as `‖∇ω‖²` (`palinstrophy_eq_weighted`).

The resonant triadic stretching `vortexStretchingTriadic` is defined here in the Fourier shape of
`∫(ω·∇)u·ω` — `(ω̂_i · k_j)(â_j · ω̂_l)` summed over triads with `k_i = k_j + k_l` — and its off-resonance
vanishing is recorded (`vortexStretchingTriadic_offResonance_zero`).

## Honest scope

This module builds the *carrier* and grounds the enstrophy/palinstrophy definitions.  It does **not** yet
prove the scaling-critical interpolation `|VS| ≤ C Ω^{3/2}P^{1/2}` for the triadic functional — that is a
genuine Cauchy–Schwarz-over-triads estimate and the next step.  Amplitudes are real rather than complex
(conjugate-symmetric) modes, so the field is a real spectral model, not the full complex Fourier
representation.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.TriadicVectorSpectralField

open Physlib.QuantumMechanics.ComplexAction.TorusFourier.TriadicKernel
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-- **A vector-amplitude spectral field on `T³`**: `N` modes, each carrying an integer wavevector and a real
three-component amplitude — the structure a genuine vorticity requires. -/
structure NSTriadicField where
  /-- Number of modes. -/
  N : ℕ
  /-- Integer wavevector `k_i` of each mode. -/
  wvec : Fin N → TorusWaveVec3
  /-- Real vector amplitude `â_i` of each mode. -/
  amp : Fin N → (Fin 3 → ℝ)

namespace NSTriadicField

variable (v : NSTriadicField)

/-- The mode's wavevector as a real vector. -/
def waveReal (i : Fin v.N) : Fin 3 → ℝ := fun j => ((v.wvec i j : ℤ) : ℝ)

/-- **Incompressibility**: every mode is transverse, `⟨k_i, â_i⟩ = 0` — the Fourier form of `∇·u = 0`. -/
def IsDivFree : Prop := ∀ i : Fin v.N, sphereInner (v.waveReal i) (v.amp i) = 0

/-- **The mode vorticity magnitude** `|ω̂_i|² = |k_i × â_i|²` — the squared Fourier amplitude of `∇ × u`. -/
def modeVorticitySq (i : Fin v.N) : ℝ := crossSphereDefect (v.waveReal i) (v.amp i)

/-- **Transverse modes carry `|ω̂|² = |k|²|â|²`.**  By the Lagrange identity
`|k × â|² = |k|²|â|² − ⟨k,â⟩²`, incompressibility `⟨k,â⟩ = 0` collapses the vorticity magnitude to the
weighted amplitude — the identity the arc's enstrophy definition rests on. -/
theorem modeVorticitySq_divFree (hdf : v.IsDivFree) (i : Fin v.N) :
    v.modeVorticitySq i = sphereNormSq (v.waveReal i) * sphereNormSq (v.amp i) := by
  unfold modeVorticitySq
  rw [crossSphereDefect_lagrange, hdf i]
  ring

/-- **Enstrophy as the vorticity norm** `Ω = ∑ |ω̂_i|²` — defined from the curl, not postulated. -/
noncomputable def enstrophy : ℝ := ∑ i, v.modeVorticitySq i

/-- **Palinstrophy as the vorticity-gradient norm** `P = ∑ |k_i|²|ω̂_i|²`. -/
noncomputable def palinstrophy : ℝ := ∑ i, sphereNormSq (v.waveReal i) * v.modeVorticitySq i

/-- **Grounding theorem: the weighted sum *is* the enstrophy.**  For a divergence-free vector spectral field,
`∑|ω̂_i|² = ∑ |k_i|²|â_i|²` — the definition used throughout the entropic arc is the genuine `L²` norm of the
vorticity `∇ × u`, not a modeling choice. -/
theorem enstrophy_eq_weighted (hdf : v.IsDivFree) :
    v.enstrophy = ∑ i, sphereNormSq (v.waveReal i) * sphereNormSq (v.amp i) := by
  unfold enstrophy
  exact Finset.sum_congr rfl fun i _ => v.modeVorticitySq_divFree hdf i

/-- **Grounding theorem for the palinstrophy**: `P = ∑ |k_i|⁴|â_i|²` on divergence-free fields — the second
rung of the arc's Sobolev ladder is `‖∇ω‖²`. -/
theorem palinstrophy_eq_weighted (hdf : v.IsDivFree) :
    v.palinstrophy
      = ∑ i, sphereNormSq (v.waveReal i) * (sphereNormSq (v.waveReal i) * sphereNormSq (v.amp i)) := by
  unfold palinstrophy
  exact Finset.sum_congr rfl fun i _ => by rw [v.modeVorticitySq_divFree hdf i]

/-- The squared norm on `ℝ³` is non-negative. -/
theorem sphereNormSq_nonneg (ξ : Fin 3 → ℝ) : 0 ≤ sphereNormSq ξ := by
  unfold sphereNormSq sphereInner
  nlinarith [mul_self_nonneg (ξ 0), mul_self_nonneg (ξ 1), mul_self_nonneg (ξ 2)]

/-- Enstrophy is non-negative — a sum of squared cross-product magnitudes. -/
theorem enstrophy_nonneg : 0 ≤ v.enstrophy :=
  Finset.sum_nonneg fun _ _ => crossSphereDefect_nonneg _ _

/-- Palinstrophy is non-negative. -/
theorem palinstrophy_nonneg : 0 ≤ v.palinstrophy :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sphereNormSq_nonneg _) (crossSphereDefect_nonneg _ _)

/-! ### The resonant triadic vortex stretching -/

/-- **Triad resonance** `k_i = k_j + k_l` — the convolution condition of the Fourier nonlinearity. -/
def IsResonant (i j l : Fin v.N) : Prop := v.wvec i = v.wvec j + v.wvec l

/-- **The vorticity vector of a mode**, `ω̂_i = k_i × â_i`. -/
def modeVorticity (i : Fin v.N) : Fin 3 → ℝ := fun m =>
  if m = 0 then v.waveReal i 1 * v.amp i 2 - v.waveReal i 2 * v.amp i 1
  else if m = 1 then v.waveReal i 2 * v.amp i 0 - v.waveReal i 0 * v.amp i 2
  else v.waveReal i 0 * v.amp i 1 - v.waveReal i 1 * v.amp i 0

/-- **The triadic vortex-stretching term** in the Fourier shape of `∫(ω·∇)u·ω`: the stretching contributed by
the triad `(i,j,l)` is `(ω̂_i · k_j)(â_j · ω̂_l)` on resonance and zero off it. -/
noncomputable def stretchingTerm (i j l : Fin v.N) : ℝ :=
  if v.wvec i = v.wvec j + v.wvec l then
    sphereInner (v.modeVorticity i) (v.waveReal j) * sphereInner (v.amp j) (v.modeVorticity l)
  else 0

/-- **The triadic vortex stretching** `VS = ∑_{k_i = k_j + k_l} (ω̂_i · k_j)(â_j · ω̂_l)` — the genuine
convolution functional, summed over all resonant triads. -/
noncomputable def vortexStretchingTriadic : ℝ :=
  ∑ i, ∑ j, ∑ l, v.stretchingTerm i j l

/-- **Off-resonance triads contribute nothing** — the stretching is supported on the resonance surface
`k_i = k_j + k_l`, the defining locality of the Fourier nonlinearity. -/
theorem stretchingTerm_offResonance_zero (i j l : Fin v.N)
    (h : v.wvec i ≠ v.wvec j + v.wvec l) : v.stretchingTerm i j l = 0 := by
  unfold stretchingTerm
  rw [if_neg h]

/-- **A field with no resonant triads has no stretching** — the 3D nonlinearity is switched off exactly when
the mode set supports no convolution, the spectral analogue of the 2D `VS = 0` corner. -/
theorem vortexStretchingTriadic_eq_zero_of_no_resonance
    (h : ∀ i j l : Fin v.N, v.wvec i ≠ v.wvec j + v.wvec l) :
    v.vortexStretchingTriadic = 0 := by
  unfold vortexStretchingTriadic
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun l _ => v.stretchingTerm_offResonance_zero i j l (h i j l)

/-! ### The triad bound: stretching is a three-vortex interaction

Cauchy–Schwarz on `ℝ³` is itself a consequence of the Lagrange identity — non-negativity of `|ξ × η|²` *is*
`⟨ξ,η⟩² ≤ ‖ξ‖²‖η‖²` (`sphereInner_sq_le_normSq_mul`).  Applying it to both factors of a triad term and using
incompressibility at the middle mode (`|k_j|²|â_j|² = |ω̂_j|²`), each triad's stretching is bounded by the
**product of the three mode vorticity magnitudes** (`stretchingTerm_sq_le_vorticity_product`):

  `(ω̂_i · k_j)²(â_j · ω̂_l)² ≤ |ω̂_i|² |ω̂_j|² |ω̂_l|².`

The wavenumber factor `k_j` — the derivative in `∇u` — is absorbed exactly by the transversality of mode `j`:
vortex stretching is a three-vorticity interaction, with no leftover wavenumber weight.  This is the
per-triad content of the estimate; the global scaling-critical bound additionally requires counting the
resonance surface `k_i = k_j + k_l`, which is not done here. -/

/-- **Cauchy–Schwarz on `ℝ³`, from the Lagrange identity.**  `⟨ξ,η⟩² ≤ ‖ξ‖²‖η‖²` — the non-negativity of the
cross-product magnitude `|ξ × η|² = ‖ξ‖²‖η‖² − ⟨ξ,η⟩²` is exactly the Cauchy–Schwarz inequality. -/
theorem sphereInner_sq_le_normSq_mul (ξ η : Fin 3 → ℝ) :
    sphereInner ξ η ^ 2 ≤ sphereNormSq ξ * sphereNormSq η := by
  have h := crossSphereDefect_nonneg ξ η
  rw [crossSphereDefect_lagrange] at h
  linarith

/-- The explicit vorticity vector has the vorticity magnitude: `‖ω̂_i‖² = |k_i × â_i|²` — the coherence of the
vector `modeVorticity` with the scalar `modeVorticitySq`. -/
theorem sphereNormSq_modeVorticity (i : Fin v.N) :
    sphereNormSq (v.modeVorticity i) = v.modeVorticitySq i := by
  unfold sphereNormSq sphereInner modeVorticity modeVorticitySq crossSphereDefect
  norm_num [Fin.ext_iff]
  ring

/-- Each mode's vorticity magnitude is non-negative. -/
theorem modeVorticitySq_nonneg (i : Fin v.N) : 0 ≤ v.modeVorticitySq i :=
  crossSphereDefect_nonneg _ _

/-- **The triad bound: stretching is a three-vortex interaction.**  For a divergence-free field, each triad's
stretching term is bounded by the product of the three mode vorticity magnitudes,
`(term)² ≤ |ω̂_i|²|ω̂_j|²|ω̂_l|²` — the wavenumber factor of the derivative is absorbed exactly by the
transversality of the middle mode. -/
theorem stretchingTerm_sq_le_vorticity_product (hdf : v.IsDivFree) (i j l : Fin v.N) :
    v.stretchingTerm i j l ^ 2
      ≤ v.modeVorticitySq i * v.modeVorticitySq j * v.modeVorticitySq l := by
  unfold stretchingTerm
  by_cases h : v.wvec i = v.wvec j + v.wvec l
  · rw [if_pos h]
    calc (sphereInner (v.modeVorticity i) (v.waveReal j)
            * sphereInner (v.amp j) (v.modeVorticity l)) ^ 2
        = sphereInner (v.modeVorticity i) (v.waveReal j) ^ 2
            * sphereInner (v.amp j) (v.modeVorticity l) ^ 2 := by ring
      _ ≤ (sphereNormSq (v.modeVorticity i) * sphereNormSq (v.waveReal j))
            * (sphereNormSq (v.amp j) * sphereNormSq (v.modeVorticity l)) :=
          mul_le_mul (sphereInner_sq_le_normSq_mul _ _) (sphereInner_sq_le_normSq_mul _ _)
            (sq_nonneg _) (mul_nonneg (sphereNormSq_nonneg _) (sphereNormSq_nonneg _))
      _ = sphereNormSq (v.modeVorticity i)
            * (sphereNormSq (v.waveReal j) * sphereNormSq (v.amp j))
            * sphereNormSq (v.modeVorticity l) := by ring
      _ = v.modeVorticitySq i * v.modeVorticitySq j * v.modeVorticitySq l := by
          rw [v.sphereNormSq_modeVorticity i, v.sphereNormSq_modeVorticity l,
            ← v.modeVorticitySq_divFree hdf j]
  · rw [if_neg h]
    have := mul_nonneg (mul_nonneg (v.modeVorticitySq_nonneg i) (v.modeVorticitySq_nonneg j))
      (v.modeVorticitySq_nonneg l)
    simpa using this

end NSTriadicField

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.TriadicVectorSpectralField

end
