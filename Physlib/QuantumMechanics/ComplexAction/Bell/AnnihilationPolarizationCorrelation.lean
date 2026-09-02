/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Wu–Shaknov: the polarization correlations of annihilation photons

The two photons of `e⁻e⁺ → γγ` (para-positronium, `J^{PC} = 0^{−+}`) are emitted in
the *polarization singlet* — the antisymmetric two-photon state
`|ψ⟩ = (|xy⟩ − |yx⟩)/√2 ∝ ε₁ × ε₂ · k̂`, the pseudoscalar's unique rotationally
invariant, parity-odd combination (Wheeler 1946; Pryce–Ward 1947; Snyder–Pasternack–
Hornbostel 1948).  Wu and Shaknov (1950) measured the predicted excess of Compton
coincidences in *perpendicular* scattering planes, `R = 2.04 ± 0.08` — historically
the first measured entangled photon pair (recognized as EPR-complete by
Bohm–Aharonov 1957, reanalyzed as a Bell-type test by Kasday–Ullman–Wu 1975).

The two-photon amplitude is represented by the matrix `Ψ : Matrix (Fin 2) (Fin 2) ℂ`
(`Ψ i j` = amplitude for photon 1 in linear polarization `i`, photon 2 in `j`), so
`⟨ψ|(A ⊗ B)|ψ⟩ = tr(Ψᴴ·A·Ψ·Bᵀ)` (`pairExpectation`) with no Kronecker bookkeeping.

* **§A — the singlet.** `pairExpectation_singlet` (the closed sandwich formula —
  every observable below is a corollary); `photonSinglet_normalized`;
  `photonSinglet_antisymmetric` (parity-odd: the pseudoscalar face);
  `photonSinglet_rotation_invariant` (`R(α)·Ψ·R(α)ᵀ = Ψ`: the `SO(2)` singlet —
  no preferred transverse axis).
* **§B — Malus for the pair.** `pairAmplitude_singlet`
  (`⟨θ₁,θ₂|ψ⟩ = sin(θ₂−θ₁)/√2`); `parallel_polarizations_forbidden` (the same-angle
  amplitude vanishes identically); `perpendicular_polarizations_maximal`
  (probability `1/2` at right angles) — the perpendicular correlation that the
  Compton polarimeters translate into the coincidence asymmetry.
* **§C — Stokes correlation and the coincidence law.**
  `photonSinglet_unpolarized` (each photon *separately* has no polarization);
  `photonSinglet_stokes_correlation` (`E(φ₁,φ₂) = −cos 2(φ₁−φ₂)`);
  `compton_coincidence_law` (Pryce–Ward): with Compton analyzing powers `κ₁, κ₂`
  (the Klein–Nishina azimuthal modulation, isolated as the polarimeter datum), the
  coincidence rate is `N(φ₁,φ₂) = (1 − κ₁κ₂·cos 2(φ₁−φ₂))/4`.
* **§D — Wu–Shaknov.** `wu_shaknov_perpendicular_excess` (`N_⊥ − N_∥ = κ₁κ₂/2`);
  `wu_shaknov_ratio` (`N_⊥·(1−κ₁κ₂) = N_∥·(1+κ₁κ₂)`, the measured
  `R = (1+κ₁κ₂)/(1−κ₁κ₂)`; `R = 2.04 ± 0.08` observed, i.e. `κ₁κ₂ ≈ 0.34` at the
  Columbia geometry); `annihilation_photons_saturate_tsirelson` — at the standard
  angle quadruple `(0, π/4; π/8, −π/8)` the ideal-analyzer CHSH combination of the
  singlet correlation equals `−2√2`: the annihilation pair *saturates*
  `DeterministicBounds.tsirelsonWitness` (and beats the classical bound `2` of
  `classicalCHSH_bound`) — the 1950 experiment realized a maximally Bell-violating
  state, twenty-two years before Freedman–Clauser.

Honest layering: the Klein–Nishina cross-section (which fixes `κ(θ)` and made
Compton scattering the only polarimeter available at `511 keV`) is *not* derived —
`κ₁, κ₂` enter as the polarimeter data; finite-aperture averaging and the
para-positronium selection rules (why the singlet, not the `0⁺` triplet-face
`(|xx⟩+|yy⟩)/√2`) are quoted from the references.

## References

* C. S. Wu, I. Shaknov, Phys. Rev. 77 (1950) 136.
* M. H. L. Pryce, J. C. Ward, Nature 160 (1947) 435; H. S. Snyder, S. Pasternack,
  J. Hornbostel, Phys. Rev. 73 (1948) 440.
* J. A. Wheeler, Ann. N.Y. Acad. Sci. 48 (1946) 219.
* D. Bohm, Y. Aharonov, Phys. Rev. 108 (1957) 1070; L. R. Kasday, J. D. Ullman,
  C. S. Wu, Nuovo Cimento 25B (1975) 633.
* Repo modules used: `Bell.DeterministicBounds` (`tsirelsonWitness`,
  `classicalCHSH_bound`), `CanonicalTetradGravity.PairAnnihilationGravitationalWave`
  (the vertex producing this pair), `ComptonClock.FrequencyTrinity`
  (`vacuum_bell_compton_decay`, the same CHSH envelope at spacelike separation).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation

open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Matrix


/-- **The two-photon polarization singlet** `Ψ = (|xy⟩ − |yx⟩)/√2` as an amplitude
matrix — the pseudoscalar (`0⁻`) two-photon state of para-positronium,
`∝ ε₁ × ε₂ · k̂`. -/
noncomputable def photonSinglet : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![0, 1; -1, 0]

/-- **Linear polarization at angle `θ`** in the transverse plane. -/
noncomputable def linearPolarization (θ : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos θ : ℂ), (Real.sin θ : ℂ)]

/-- **The pair expectation** `⟨ψ|(A ⊗ B)|ψ⟩ = tr(Ψᴴ·A·Ψ·Bᵀ)` — local observable `A`
on photon 1 and `B` on photon 2, evaluated on the amplitude matrix. -/
noncomputable def pairExpectation (Ψ A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (Ψᴴ * A * Ψ * Bᵀ)

/-- **The joint polarization amplitude** `⟨θ₁, θ₂|ψ⟩` onto product linear
polarizations (real analyzer vectors, so no conjugation is lost). -/
noncomputable def pairAmplitude (Ψ : Matrix (Fin 2) (Fin 2) ℂ) (θ₁ θ₂ : ℝ) : ℂ :=
  linearPolarization θ₁ ⬝ᵥ (Ψ *ᵥ linearPolarization θ₂)

/-- **The linear-polarization Stokes operator** at analyzer angle `φ`:
`σ(φ) = cos 2φ·σ_z + sin 2φ·σ_x`, the `±1`-valued question "polarized along `φ` or
along `φ + π/2`?". -/
noncomputable def stokesOperator (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (2 * φ) : ℂ), (Real.sin (2 * φ) : ℂ);
     (Real.sin (2 * φ) : ℂ), (-Real.cos (2 * φ) : ℂ)]

/-- **The Compton polarimeter response** at azimuth `φ` with analyzing power `κ`:
`(𝟙 + κ·σ(φ))/2` — the Klein–Nishina azimuthal modulation as an (unnormalized)
POVM element; `κ = 1` is the ideal analyzer, `κ ≈ 0.6` per arm at the Wu–Shaknov
scattering angle. -/
noncomputable def comptonResponse (φ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + (κ : ℂ) • stokesOperator φ)

/-! ## §A — the singlet -/

/-- **[The singlet sandwich formula]** `⟨ψ|(A ⊗ B)|ψ⟩ = (A₁₁B₀₀ − A₁₀B₀₁ − A₀₁B₁₀ +
A₀₀B₁₁)/2` — the closed form of every pair observable on the singlet.  (The index
flip `A_{ij} ↦ A_{1−i,1−j}` with alternating signs is the `2×2` adjugate: the
antisymmetric state couples each photon to the *other's* orthogonal complement.) -/
theorem pairExpectation_singlet (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pairExpectation photonSinglet A B
      = 2⁻¹ * (A 1 1 * B 0 0 - A 1 0 * B 0 1 - A 0 1 * B 1 0 + A 0 0 * B 1 1) := by
  have hss : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold pairExpectation photonSinglet
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, Complex.real_smul,
    Complex.ofReal_inv]
  linear_combination (A 1 1 * B 0 0 - A 1 0 * B 0 1 - A 0 1 * B 1 0
    + A 0 0 * B 1 1) * hss

/-- **[Normalization] `⟨ψ|(𝟙 ⊗ 𝟙)|ψ⟩ = 1`.** -/
theorem photonSinglet_normalized : pairExpectation photonSinglet 1 1 = 1 := by
  rw [pairExpectation_singlet]
  simp
  norm_num

/-- **[Parity-odd] `Ψᵀ = −Ψ`** — exchanging the two photons flips the sign: the
singlet is the antisymmetric (pseudoscalar, `ε₁ × ε₂`) combination, as required for
the `0⁻` para-positronium state; the symmetric `0⁺` combination `(|xx⟩+|yy⟩)/√2`
would be parity-even. -/
theorem photonSinglet_antisymmetric : photonSingletᵀ = -photonSinglet := by
  unfold photonSinglet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp

/-- **[Rotational invariance] `R(α)·Ψ·R(α)ᵀ = Ψ`** — rotating *both* transverse
polarization frames by the same angle fixes the singlet (`R J Rᵀ = det R·J = J`):
the annihilation pair has no preferred axis about the flight line, so only the
*relative* analyzer angle can appear in any correlation. -/
theorem photonSinglet_rotation_invariant (α : ℝ) :
    (!![(Real.cos α : ℂ), -(Real.sin α : ℂ);
        (Real.sin α : ℂ), (Real.cos α : ℂ)] * photonSinglet
      * (!![(Real.cos α : ℂ), -(Real.sin α : ℂ);
            (Real.sin α : ℂ), (Real.cos α : ℂ)])ᵀ) = photonSinglet := by
  have hcs : Complex.cos ↑α ^ 2 + Complex.sin ↑α ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq ↑α
  unfold photonSinglet
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Complex.ofReal_inv]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Complex.ofReal_inv]
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hcs
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Complex.ofReal_inv]
    linear_combination -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hcs
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Complex.ofReal_inv]
    ring

/-! ## §B — Malus for the pair -/

/-- **[The pair amplitude is the sine of the relative angle]
`⟨θ₁, θ₂|ψ⟩ = sin(θ₂ − θ₁)/√2`** — the entangled Malus law: only the relative
analyzer angle survives (rotational invariance made concrete). -/
theorem pairAmplitude_singlet (θ₁ θ₂ : ℝ) :
    pairAmplitude photonSinglet θ₁ θ₂
      = (((Real.sqrt 2)⁻¹ * Real.sin (θ₂ - θ₁) : ℝ) : ℂ) := by
  unfold pairAmplitude photonSinglet linearPolarization
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.real_smul,
    Complex.ofReal_inv]
  rw [Complex.sin_sub]
  ring

/-- **[Parallel polarizations are forbidden]** the amplitude for finding *both*
photons polarized along the same axis vanishes identically — the perpendicular
correlation at the heart of the Wu–Shaknov signal. -/
theorem parallel_polarizations_forbidden (θ : ℝ) :
    pairAmplitude photonSinglet θ θ = 0 := by
  rw [pairAmplitude_singlet]
  simp

/-- **[Perpendicular polarizations are maximal]** the joint probability at right
angles is `|⟨θ, θ+π/2|ψ⟩|² = 1/2` — the largest of any product analyzer pair. -/
theorem perpendicular_polarizations_maximal (θ : ℝ) :
    Complex.normSq (pairAmplitude photonSinglet θ (θ + Real.pi / 2)) = 2⁻¹ := by
  rw [pairAmplitude_singlet]
  have h : θ + Real.pi / 2 - θ = Real.pi / 2 := by ring
  rw [h, Real.sin_pi_div_two, mul_one, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-! ## §C — the Stokes correlation and the Compton coincidence law -/

/-- **[Each photon is separately unpolarized]** the singles rate shows no azimuthal
modulation, `⟨σ(φ) ⊗ 𝟙⟩ = ⟨𝟙 ⊗ σ(φ)⟩ = 0` — all the polarization information is in
the *correlation* (the rotational invariance of §A, observable by observable). -/
theorem photonSinglet_unpolarized (φ : ℝ) :
    pairExpectation photonSinglet (stokesOperator φ) 1 = 0
      ∧ pairExpectation photonSinglet 1 (stokesOperator φ) = 0 := by
  constructor <;>
  · rw [pairExpectation_singlet]
    simp [stokesOperator]

/-- **[The singlet Stokes correlation] `E(φ₁, φ₂) = −cos 2(φ₁ − φ₂)`** — the
ideal-analyzer polarization correlation of the annihilation pair: `−1` (perfect
anticorrelation) at parallel analyzers, `+1` at perpendicular, depending only on
the relative angle, with the photon-characteristic *doubled* angle. -/
theorem photonSinglet_stokes_correlation (φ₁ φ₂ : ℝ) :
    pairExpectation photonSinglet (stokesOperator φ₁) (stokesOperator φ₂)
      = ((-Real.cos (2 * φ₁ - 2 * φ₂) : ℝ) : ℂ) := by
  rw [pairExpectation_singlet]
  simp [stokesOperator]
  rw [Complex.cos_sub]
  ring

/-- **[The Pryce–Ward coincidence law]
`N(φ₁, φ₂) = (1 − κ₁κ₂·cos 2(φ₁ − φ₂))/4`** — Compton polarimeters with analyzing
powers `κ₁, κ₂` (the Klein–Nishina azimuthal modulation) applied to the singlet:
the singles are flat (`photonSinglet_unpolarized`), and the coincidence rate
has the Stokes correlation attenuated by `κ₁κ₂` — maximal in perpendicular
scattering planes. -/
theorem compton_coincidence_law (φ₁ φ₂ κ₁ κ₂ : ℝ) :
    pairExpectation photonSinglet (comptonResponse φ₁ κ₁) (comptonResponse φ₂ κ₂)
      = (((1 - κ₁ * κ₂ * Real.cos (2 * φ₁ - 2 * φ₂)) / 4 : ℝ) : ℂ) := by
  rw [pairExpectation_singlet]
  simp [comptonResponse, stokesOperator]
  rw [Complex.cos_sub]
  ring

/-! ## §D — Wu–Shaknov -/

/-- **[The perpendicular excess] `N_⊥ − N_∥ = κ₁κ₂/2`** — the Wu–Shaknov signal:
coincidences with scattering planes at right angles exceed parallel-plane
coincidences by exactly half the product of the analyzing powers; the excess
vanishes iff either polarimeter stops analyzing. -/
theorem wu_shaknov_perpendicular_excess (φ κ₁ κ₂ : ℝ) :
    pairExpectation photonSinglet (comptonResponse φ κ₁)
        (comptonResponse (φ + Real.pi / 2) κ₂)
      - pairExpectation photonSinglet (comptonResponse φ κ₁) (comptonResponse φ κ₂)
      = ((κ₁ * κ₂ / 2 : ℝ) : ℂ) := by
  rw [compton_coincidence_law, compton_coincidence_law]
  have h1 : 2 * φ - 2 * (φ + Real.pi / 2) = -Real.pi := by ring
  have h2 : 2 * φ - 2 * φ = 0 := by ring
  rw [h1, h2, Real.cos_neg, Real.cos_pi, Real.cos_zero]
  push_cast
  ring

/-- **[The Wu–Shaknov ratio] `N_⊥·(1 − κ₁κ₂) = N_∥·(1 + κ₁κ₂)`** — cross-multiplied
form of the measured ratio `R = N_⊥/N_∥ = (1 + κ₁κ₂)/(1 − κ₁κ₂)`.  Wu and Shaknov
found `R = 2.04 ± 0.08`, i.e. `κ₁κ₂ ≈ 0.34` at the Columbia geometry — matching the
Pryce–Ward prediction from the singlet and confirming the pseudoscalar assignment
(the parity-even `0⁺` state would prefer *parallel* planes). -/
theorem wu_shaknov_ratio (φ κ₁ κ₂ : ℝ) :
    pairExpectation photonSinglet (comptonResponse φ κ₁)
        (comptonResponse (φ + Real.pi / 2) κ₂) * ((1 - κ₁ * κ₂ : ℝ) : ℂ)
      = pairExpectation photonSinglet (comptonResponse φ κ₁) (comptonResponse φ κ₂)
        * ((1 + κ₁ * κ₂ : ℝ) : ℂ) := by
  rw [compton_coincidence_law, compton_coincidence_law]
  have h1 : 2 * φ - 2 * (φ + Real.pi / 2) = -Real.pi := by ring
  have h2 : 2 * φ - 2 * φ = 0 := by ring
  rw [h1, h2, Real.cos_neg, Real.cos_pi, Real.cos_zero]
  push_cast
  ring

/-- **[The annihilation pair saturates Tsirelson]** at the standard angle quadruple
`a = 0, a' = π/4, b = π/8, b' = −π/8`, the CHSH combination of the ideal-analyzer
singlet correlations equals `−2√2`: `|S| = tsirelsonWitness`, the quantum maximum —
strictly beyond the classical bound `2` of `classicalCHSH_bound`.  The state Wu and
Shaknov handled in 1950 was maximally Bell-violating (Kasday–Ullman–Wu made the
Bell reading explicit in 1975), twenty-two years before Freedman–Clauser. -/
theorem annihilation_photons_saturate_tsirelson :
    pairExpectation photonSinglet (stokesOperator 0) (stokesOperator (Real.pi / 8))
        + pairExpectation photonSinglet (stokesOperator 0)
          (stokesOperator (-Real.pi / 8))
        + pairExpectation photonSinglet (stokesOperator (Real.pi / 4))
          (stokesOperator (Real.pi / 8))
        - pairExpectation photonSinglet (stokesOperator (Real.pi / 4))
          (stokesOperator (-Real.pi / 8))
      = -(tsirelsonWitness : ℝ) := by
  rw [photonSinglet_stokes_correlation, photonSinglet_stokes_correlation,
    photonSinglet_stokes_correlation, photonSinglet_stokes_correlation]
  simp only [tsirelsonWitness]
  have e1 : 2 * (0 : ℝ) - 2 * (Real.pi / 8) = -(Real.pi / 4) := by ring
  have e2 : 2 * (0 : ℝ) - 2 * (-Real.pi / 8) = Real.pi / 4 := by ring
  have e3 : 2 * (Real.pi / 4) - 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  have e4 : 2 * (Real.pi / 4) - 2 * (-Real.pi / 8) = Real.pi - Real.pi / 4 := by
    ring
  rw [e1, e2, e3, e4, Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four]
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation

end
