/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound
public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Data.Real.Pointwise
meta import Zil

/-!
# The Schrödinger–Newton energy functional

The total energy of a Schrödinger–Newton state `ψ` combines the kinetic (Dirichlet) energy with the
gravitational self-interaction of its density `ρ = ψ²`:

  `E_G[ψ] = ½∫‖∇ψ‖² − ½G·∬ ψ(x)²ψ(y)²/‖x−y‖`   (`schrodingerNewtonEnergy`),

the `n = 3` real Schrödinger–Newton / Choquard functional (the attractive self-gravity lowers the
energy). The kinetic term reuses the repo's Schwartz gradient `gradSchwartz`; the gravitational term
reuses `newtonianSelfEnergy` (`NewtonianConvolutionPotential`). Both the kinetic energy and the
gravitational self-energy of a state are nonnegative. The general-density HLS bridge additionally
proves that every Schwartz state's Born density `ψ²` has finite `L^(6/5)` mass, bounds its Hartree
self-energy by the corresponding `L^(12/5)` wavefunction quantity, and yields a lower bound on the
full attractive energy. The mass-preserving dilation `ψ_r(x) = r√r ψ(rx)` then preserves
normalization and compact support, scales the kinetic and Hartree terms respectively by `r²` and
`r`, and constructs a normalized negative-energy trial at every positive coupling whenever the
seed has positive Hartree interaction. Thus the variational infimum lies below the dispersed
zero-Hartree branch. For any actually attained constrained minimizer, Fermat stationarity along
this exact dilation orbit then derives the virial identity `2K = GH` and the binding identities
`E = -K/2 = -GH/4`; attainment itself remains a separate concentration--compactness problem.
An independent mass-changing scaling `ψ ↦ M² ψ(Mx)` proves the exact cubic
variational law `I_G(M) = M³ I_G(1)` and, from `I_G(1)<0`, strict
subadditivity under every nontrivial mass split. This supplies the genuine
binding inequality excluding the dichotomy branch on the compact Schwartz
core. The reusable continuum Sobolev layer now supplies weak sequential
precompactness for every norm-bounded `H¹(ℝ³)` family. Applying it to this
variational problem still requires a Schwartz-to-`H¹` minimizing-sequence
bound, tightness modulo translations, constraint closure, and lower
semicontinuity before attainment may be claimed.
The final specialization uses the repository's inference-scale coupling `G = ħcσ₀⁴`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory SchwartzMap
open scoped ENNReal Pointwise Space
open Space
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy

/-- The **kinetic (Dirichlet) energy** of a state: `∫ ‖∇ψ(x)‖² dx`, using the repo's Schwartz
gradient `gradSchwartz`. -/
noncomputable def kineticEnergy (ψ : 𝓢(Space 3, ℝ)) : ℝ :=
  ∫ x, ‖gradSchwartz ψ x‖ ^ 2

/-- **[The kinetic energy is nonnegative]** `∫ ‖∇ψ‖² ≥ 0`. -/
@[zil_level physical_theorem]
theorem kineticEnergy_nonneg (ψ : 𝓢(Space 3, ℝ)) : 0 ≤ kineticEnergy ψ :=
  integral_nonneg fun _ => sq_nonneg _

/-- The operator norm of the scalar Fréchet derivative equals the Euclidean
norm of Physlib's Schwartz gradient. This is the pointwise identification
between Mathlib's Sobolev carrier and the kinetic-energy carrier used here. -/
@[zil_level bridge_theorem]
theorem norm_fderiv_eq_gradSchwartz (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    ‖fderiv ℝ (ψ : Space 3 → ℝ) x‖ = ‖gradSchwartz ψ x‖ := by
  rw [gradSchwartz_apply_eq_grad]
  calc
    ‖fderiv ℝ (ψ : Space 3 → ℝ) x‖ =
        ‖gradient (ψ : Space 3 → ℝ) x‖ :=
      ((InnerProductSpace.toDual ℝ (Space 3)).symm.norm_map
        (fderiv ℝ (ψ : Space 3 → ℝ) x)).symm
    _ = ‖∇ (ψ : Space 3 → ℝ) x‖ := by
      rw [gradient_apply_eq_grad]
      exact Space.basis.repr.symm.norm_map _

/-- The integral of the squared Fréchet-derivative norm is exactly the
repository's `kineticEnergy`, not merely an equivalent Sobolev proxy. -/
@[zil_level bridge_theorem]
theorem frechetKineticIntegral_eq (ψ : 𝓢(Space 3, ℝ)) :
    ∫ x, ‖fderiv ℝ (ψ : Space 3 → ℝ) x‖ ^ 2 =
      kineticEnergy ψ := by
  unfold kineticEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ‖fderiv ℝ (ψ : Space 3 → ℝ) x‖ ^ 2 =
      ‖gradSchwartz ψ x‖ ^ 2
    rw [norm_fderiv_eq_gradSchwartz ψ x]

/-- The square of the continuum `L²` Fréchet-gradient norm is precisely the
Dirichlet kinetic energy. This closes the carrier bridge required to complete
the Schrödinger--Newton stability square. -/
@[zil_level physical_theorem]
theorem frechetGradient_eLpNorm_sq_eq_kineticEnergy
    (ψ : 𝓢(Space 3, ℝ)) :
    (eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume).toReal ^ 2 =
      kineticEnergy ψ := by
  have hm : MemLp (fderiv ℝ (ψ : Space 3 → ℝ))
      (2 : ℝ≥0∞) volume := by
    change MemLp
      (SchwartzMap.fderivCLM ℝ (Space 3) ℝ ψ :
        Space 3 → (Space 3 →L[ℝ] ℝ)) (2 : ℝ≥0∞) volume
    exact (SchwartzMap.fderivCLM ℝ (Space 3) ℝ ψ).memLp
      (2 : ℝ≥0∞) volume
  have he := MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
    (f := fderiv ℝ (ψ : Space 3 → ℝ)) (p := (2 : ℝ≥0∞))
    (μ := volume)
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hm
  norm_num at he
  rw [he, ENNReal.toReal_ofReal]
  · rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    · exact frechetKineticIntegral_eq ψ
    · rw [frechetKineticIntegral_eq]
      exact kineticEnergy_nonneg ψ
  · positivity

/-- The real coefficient multiplying the continuum gradient scale after
composing the HLS and dimension-three Sobolev inequalities. -/
noncomputable def schrodingerNewtonStabilityConstant : ℝ :=
  (newtonianHLSConstant *
    (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
      (volume : Measure (Space 3)) 2 : ℝ≥0∞)).toReal

/-- The nested ENNReal coefficient in the Sobolev-HLS theorem is exactly the
real stability constant times the real Fréchet-gradient norm. -/
theorem hlsSobolev_toReal_factor (ψ : 𝓢(Space 3, ℝ)) :
    (newtonianHLSConstant *
      (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (Space 3)) 2 *
        eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume)).toReal =
      schrodingerNewtonStabilityConstant *
        (eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume).toReal := by
  unfold schrodingerNewtonStabilityConstant
  rw [← mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- The **Schrödinger–Newton energy functional** `E_G[ψ] = ½∫‖∇ψ‖² − ½G·∬ ψ²ψ²/‖x−y‖`: the kinetic
energy minus the attractive gravitational self-interaction of the density `ρ = ψ²`. -/
noncomputable def schrodingerNewtonEnergy (G : ℝ) (ψ : 𝓢(Space 3, ℝ)) : ℝ :=
  (1 / 2) * kineticEnergy ψ - (1 / 2) * G * newtonianSelfEnergy (fun x => ψ x ^ 2)

/-- **[The gravitational self-energy of a state is nonnegative]** the self-gravity term of the
Schrödinger–Newton functional, `∬ ψ(x)²ψ(y)²/‖x−y‖ ≥ 0`, since the density `ρ = ψ²` is nonnegative and
the Newton kernel positive. -/
@[zil_level physical_theorem]
theorem schrodingerNewton_selfGravity_nonneg (ψ : 𝓢(Space 3, ℝ)) :
    0 ≤ newtonianSelfEnergy (fun x => ψ x ^ 2) :=
  newtonianSelfEnergy_nonneg _ fun _ => sq_nonneg _

/-- The Born density `ρ = ψ²` of every real Schwartz wavefunction belongs to
`L^(6/5)(ℝ³)`. Equivalently, a Schwartz wavefunction belongs to
`L^(12/5)`, which follows from Mathlib's general `SchwartzMap.memLp`
theorem. -/
@[zil_level physical_theorem]
theorem schwartzBornDensity_lsixFifths (ψ : 𝓢(Space 3, ℝ)) :
    ∫⁻ x, ENNReal.ofReal (ψ x ^ 2) ^ ((6 : ℝ) / 5) ≠ ∞ := by
  have hm := (ψ.memLp (ENNReal.ofReal (12 / 5 : ℝ)) volume).2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : ENNReal.ofReal (12 / 5 : ℝ) ≠ 0)
    ENNReal.ofReal_ne_top] at hm
  norm_num at hm
  have heq :
      (fun x : Space 3 => ENNReal.ofReal (ψ x ^ 2) ^ ((6 : ℝ) / 5)) =
        fun x => ‖ψ x‖ₑ ^ ((12 : ℝ) / 5) := by
    funext x
    rw [show ψ x ^ 2 = |ψ x| ^ 2 by rw [sq_abs],
      ENNReal.ofReal_pow (abs_nonneg (ψ x)) 2,
      ← Real.enorm_eq_ofReal_abs, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  rw [heq]
  exact hm.ne

/-- The exact `L²`--`L⁶` Hölder interpolation needed by the
Schrödinger--Newton functional:

`(∫ u^(12/5))^(5/3) ≤ (∫ u²)^(3/2) (∫ u⁶)^(1/6)`.

This is the continuum, measure-theoretic interpolation step. It is obtained
directly from Hölder with conjugate exponents `10/9` and `10`; no finite-mode
or frequency-lattice substitute is involved. -/
@[zil_level physical_theorem]
theorem lintegral_ltwo_lsix_interpolation
    (u : Space 3 → ℝ≥0∞) (hu : AEMeasurable u volume) :
    (∫⁻ x, u x ^ ((12 : ℝ) / 5)) ^ ((5 : ℝ) / 3) ≤
      (∫⁻ x, u x ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
        (∫⁻ x, u x ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) := by
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume : Measure (Space 3))
    (p := (10 : ℝ) / 9) (q := (10 : ℝ))
    (Real.holderConjugate_iff.mpr (by constructor <;> norm_num))
    (hu.pow_const ((9 : ℝ) / 5)) (hu.pow_const ((3 : ℝ) / 5))
  have hbase :
      (∫⁻ x, u x ^ ((12 : ℝ) / 5)) ≤
        (∫⁻ x, u x ^ (2 : ℝ)) ^ ((9 : ℝ) / 10) *
          (∫⁻ x, u x ^ (6 : ℝ)) ^ ((1 : ℝ) / 10) := by
    have hmul (x : Space 3) :
        u x ^ ((9 : ℝ) / 5) * u x ^ ((3 : ℝ) / 5) =
          u x ^ ((12 : ℝ) / 5) := by
      rw [← ENNReal.rpow_add_of_nonneg ((9 : ℝ) / 5) ((3 : ℝ) / 5)
        (by norm_num) (by norm_num)]
      norm_num
    have hpow_two (x : Space 3) :
        (u x ^ ((9 : ℝ) / 5)) ^ ((10 : ℝ) / 9) = u x ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    have hpow_six (x : Space 3) :
        (u x ^ ((3 : ℝ) / 5)) ^ (10 : ℝ) = u x ^ (6 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    simp_rw [Pi.mul_apply, hmul, hpow_two, hpow_six] at hholder
    norm_num at hholder ⊢
    exact hholder
  calc
    (∫⁻ x, u x ^ ((12 : ℝ) / 5)) ^ ((5 : ℝ) / 3)
        ≤ ((∫⁻ x, u x ^ (2 : ℝ)) ^ ((9 : ℝ) / 10) *
            (∫⁻ x, u x ^ (6 : ℝ)) ^ ((1 : ℝ) / 10)) ^ ((5 : ℝ) / 3) :=
      ENNReal.rpow_le_rpow hbase (by norm_num)
    _ = (∫⁻ x, u x ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
          (∫⁻ x, u x ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      simp only [← ENNReal.rpow_mul]
      norm_num

/-- Applied to `u=|ψ|`, the interpolation theorem says that the precise
`L^(6/5)` Born-density power appearing in HLS is controlled by the `L²`
mass and `L⁶` norm of the wavefunction. -/
@[zil_level physical_theorem]
theorem bornDensity_ltwo_lsix_interpolation (ψ : 𝓢(Space 3, ℝ)) :
    (∫⁻ x, ENNReal.ofReal (ψ x ^ 2) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3) ≤
      (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
        eLpNorm (ψ : Space 3 → ℝ) 6 volume := by
  have h := lintegral_ltwo_lsix_interpolation
    (fun x : Space 3 => ‖ψ x‖ₑ) ψ.continuous.aestronglyMeasurable.enorm
  rw [show (∫⁻ x, ‖ψ x‖ₑ ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) =
      eLpNorm (ψ : Space 3 → ℝ) 6 volume by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num] at h
  convert h using 1
  apply congrArg (fun z : ℝ≥0∞ => z ^ ((5 : ℝ) / 3))
  apply lintegral_congr
  intro x
  rw [show ψ x ^ 2 = |ψ x| ^ 2 by rw [sq_abs],
    ENNReal.ofReal_pow (abs_nonneg (ψ x)) 2,
    ← Real.enorm_eq_ofReal_abs, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- The named HLS functional of a Born density is controlled by the exact
`L²` mass to the third power times the `L⁶` wavefunction norm. This packages
the analytic interpolation without duplicating `newtonianHLSConstant`. -/
@[zil_level physical_theorem]
theorem newtonianHLSBound_bornDensity_le (ψ : 𝓢(Space 3, ℝ)) :
    newtonianHLSBound (fun x => ψ x ^ 2) ≤
      (newtonianHLSConstant *
        (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
          eLpNorm (ψ : Space 3 → ℝ) 6 volume).toReal := by
  have hinterp := bornDensity_ltwo_lsix_interpolation ψ
  unfold newtonianHLSBound
  apply ENNReal.toReal_mono
  · apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · unfold newtonianHLSConstant
        finiteness
      · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        have hm := (ψ.memLp (2 : ℝ≥0∞) volume).2
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (by norm_num) (by norm_num)] at hm
        norm_num at hm
        simpa only [ENNReal.rpow_two] using hm.ne
    · exact (ψ.memLp (6 : ℝ≥0∞) volume).2.ne
  · calc
      newtonianHLSConstant *
          (∫⁻ x, ENNReal.ofReal (ψ x ^ 2) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3)
          ≤ newtonianHLSConstant *
            ((∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
              eLpNorm (ψ : Space 3 → ℝ) 6 volume) := by
        gcongr
      _ = newtonianHLSConstant *
          (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
            eLpNorm (ψ : Space 3 → ℝ) 6 volume := by ring

/-- **[HLS control of Schrödinger–Newton self-gravity]**. The Hartree term of
every real Schwartz wavefunction is bounded by the explicit general-density
HLS functional applied to its Born density `ρ=ψ²`. This is the quantitative
upgrade of `schrodingerNewton_selfGravity_nonneg`. -/
@[zil_level physical_theorem]
theorem schrodingerNewton_selfGravity_le_hls (ψ : 𝓢(Space 3, ℝ)) :
    newtonianSelfEnergy (fun x => ψ x ^ 2) ≤
      newtonianHLSBound (fun x => ψ x ^ 2) := by
  exact newtonianSelfEnergy_le_hls _ (by fun_prop) (fun _ => sq_nonneg _)
    (schwartzBornDensity_lsixFifths ψ)

/-- For an `L²`-normalized Schwartz state, the Newtonian Hartree
self-interaction is bounded by the single `L⁶` norm with the repository's
explicit HLS coefficient. -/
@[zil_level physical_theorem]
theorem normalized_selfGravity_le_lsix (ψ : 𝓢(Space 3, ℝ))
    (hψ : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1) :
    newtonianSelfEnergy (fun x => ψ x ^ 2) ≤
      (newtonianHLSConstant * eLpNorm (ψ : Space 3 → ℝ) 6 volume).toReal := by
  calc
    newtonianSelfEnergy (fun x => ψ x ^ 2)
        ≤ newtonianHLSBound (fun x => ψ x ^ 2) :=
      schrodingerNewton_selfGravity_le_hls ψ
    _ ≤ (newtonianHLSConstant *
          (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) *
            eLpNorm (ψ : Space 3 → ℝ) 6 volume).toReal :=
      newtonianHLSBound_bornDensity_le ψ
    _ = (newtonianHLSConstant *
          eLpNorm (ψ : Space 3 → ℝ) 6 volume).toReal := by
      rw [hψ, ENNReal.one_rpow, mul_one]

/-- The genuine continuum Sobolev endpoint on a compactly supported real
Schwartz state, stated with its actual Fréchet derivative:
`‖ψ‖₆ ≤ C_S ‖Dψ‖₂`. The support premise is exactly the premise of Mathlib's
dimension-three Gagliardo--Nirenberg--Sobolev theorem. -/
@[zil_level physical_theorem]
theorem lsix_le_frechetGradient (ψ : 𝓢(Space 3, ℝ))
    (hψ : HasCompactSupport (ψ : Space 3 → ℝ)) :
    eLpNorm (ψ : Space 3 → ℝ) 6 volume ≤
      MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
          (volume : Measure (Space 3)) 2 *
        eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume := by
  exact MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (F := ℝ) volume (u := (ψ : Space 3 → ℝ))
    (p := 2) (p' := 6) (ψ.smooth 1) hψ
    (by norm_num) (by simp) (by norm_num)

/-- Combining normalized HLS, exact `L²`--`L⁶` interpolation and the
dimension-three Sobolev endpoint bounds the Hartree self-gravity linearly by
the continuum `L²` Fréchet-gradient norm. -/
@[zil_level physical_theorem]
theorem normalized_selfGravity_le_frechetGradient
    (ψ : 𝓢(Space 3, ℝ))
    (hnorm : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1)
    (hcompact : HasCompactSupport (ψ : Space 3 → ℝ)) :
    newtonianSelfEnergy (fun x => ψ x ^ 2) ≤
      (newtonianHLSConstant *
        (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
            (volume : Measure (Space 3)) 2 *
          eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume)).toReal := by
  refine (normalized_selfGravity_le_lsix ψ hnorm).trans ?_
  apply ENNReal.toReal_mono
  · apply ENNReal.mul_ne_top
    · unfold newtonianHLSConstant
      finiteness
    · apply ENNReal.mul_ne_top
      · exact ENNReal.coe_ne_top
      · have hm : MemLp (fderiv ℝ (ψ : Space 3 → ℝ))
            (2 : ℝ≥0∞) volume := by
          change MemLp
            (SchwartzMap.fderivCLM ℝ (Space 3) ℝ ψ :
              Space 3 → (Space 3 →L[ℝ] ℝ)) (2 : ℝ≥0∞) volume
          exact (SchwartzMap.fderivCLM ℝ (Space 3) ℝ ψ).memLp
            (2 : ℝ≥0∞) volume
        exact hm.2.ne
  · gcongr
    exact lsix_le_frechetGradient ψ hcompact

/-- **[Lower bound for the attractive Schrödinger–Newton energy]**. For
`G ≥ 0`, HLS prevents the negative Hartree term from falling below the
explicit `L^(12/5)` control: `½ K[ψ] - ½ G HLS[ψ²] ≤ E_G[ψ]`. -/
@[zil_level physical_theorem]
theorem schrodingerNewtonEnergy_hls_lower_bound (G : ℝ) (hG : 0 ≤ G)
    (ψ : 𝓢(Space 3, ℝ)) :
    (1 / 2) * kineticEnergy ψ - (1 / 2) * G *
        newtonianHLSBound (fun x => ψ x ^ 2)
      ≤ schrodingerNewtonEnergy G ψ := by
  rw [schrodingerNewtonEnergy]
  have h := schrodingerNewton_selfGravity_le_hls ψ
  nlinarith

/-- **[Inference-scale Schrödinger–Newton lower bound]**. Substituting the
repository's continuum Poisson coupling `G = ħcσ₀⁴` into the HLS lower bound
connects the inference-scale gravitational coefficient to the controlled
nonlinear Schrödinger energy. -/
@[zil_level physical_theorem]
theorem inferenceNewtonSchrodingerEnergy_hls_lower_bound
    (ħ c σ₀ : ℝ) (hħ : 0 ≤ ħ) (hc : 0 ≤ c)
    (ψ : 𝓢(Space 3, ℝ)) :
    (1 / 2) * kineticEnergy ψ - (1 / 2) * (ħ * c * σ₀ ^ 4) *
        newtonianHLSBound (fun x => ψ x ^ 2)
      ≤ schrodingerNewtonEnergy (ħ * c * σ₀ ^ 4) ψ := by
  exact schrodingerNewtonEnergy_hls_lower_bound _
    (mul_nonneg (mul_nonneg hħ hc) (by positivity)) ψ

/-- The normalized-state energy lower bound after exact `L²`--`L⁶`
interpolation. It is the immediate pre-coercive form of Schrödinger--Newton
stability; substituting the continuum Sobolev endpoint `L⁶ ≤ C‖∇ψ‖₂` turns
the last term into one linear in the kinetic scale. -/
@[zil_level physical_theorem]
theorem schrodingerNewtonEnergy_normalized_lsix_lower_bound
    (G : ℝ) (hG : 0 ≤ G) (ψ : 𝓢(Space 3, ℝ))
    (hψ : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1) :
    (1 / 2) * kineticEnergy ψ -
        (1 / 2) * G *
          (newtonianHLSConstant * eLpNorm (ψ : Space 3 → ℝ) 6 volume).toReal
      ≤ schrodingerNewtonEnergy G ψ := by
  rw [schrodingerNewtonEnergy]
  have h := normalized_selfGravity_le_lsix ψ hψ
  nlinarith

/-- **[Continuum Sobolev stability bound]**. On the compactly supported
Schwartz core, the normalized attractive Schrödinger--Newton energy is bounded
below by the kinetic energy minus a term linear in the genuine continuum
`L²` Fréchet-gradient norm. This is the analytic form needed for the final
Young/completing-the-square coercivity step. -/
@[zil_level physical_theorem]
theorem schrodingerNewtonEnergy_normalized_frechetGradient_lower_bound
    (G : ℝ) (hG : 0 ≤ G) (ψ : 𝓢(Space 3, ℝ))
    (hnorm : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1)
    (hcompact : HasCompactSupport (ψ : Space 3 → ℝ)) :
    (1 / 2) * kineticEnergy ψ -
        (1 / 2) * G *
          (newtonianHLSConstant *
            (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
                (volume : Measure (Space 3)) 2 *
              eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume)).toReal
      ≤ schrodingerNewtonEnergy G ψ := by
  rw [schrodingerNewtonEnergy]
  have h := normalized_selfGravity_le_frechetGradient ψ hnorm hcompact
  nlinarith

/-- **[Normalized Schrödinger--Newton stability]**. On the compactly
supported normalized Schwartz core, the attractive energy has the
state-independent lower bound

`E_G[ψ] ≥ -(G C_HLS,Sobolev)² / 8`.

The proof uses the exact identity `‖Dψ‖₂² = kineticEnergy ψ` and completes
the square. Thus this is a genuine coercive lower bound, not only finiteness
of the Hartree term. -/
@[zil_level physical_theorem]
theorem schrodingerNewtonEnergy_normalized_stability
    (G : ℝ) (hG : 0 ≤ G) (ψ : 𝓢(Space 3, ℝ))
    (hnorm : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1)
    (hcompact : HasCompactSupport (ψ : Space 3 → ℝ)) :
    -(G * schrodingerNewtonStabilityConstant) ^ 2 / 8 ≤
      schrodingerNewtonEnergy G ψ := by
  have h :=
    schrodingerNewtonEnergy_normalized_frechetGradient_lower_bound
      G hG ψ hnorm hcompact
  rw [hlsSobolev_toReal_factor,
    ← frechetGradient_eLpNorm_sq_eq_kineticEnergy] at h
  have hs := sq_nonneg
    ((eLpNorm (fderiv ℝ (ψ : Space 3 → ℝ)) 2 volume).toReal -
      G * schrodingerNewtonStabilityConstant / 2)
  nlinarith

/-! ## A. Mass-preserving dilation and negative binding -/

/-- Scalar expansion by a nonzero real number on three-dimensional space. -/
noncomputable def spatialDilationCLE (r : ℝ) (hr : r ≠ 0) :
    Space 3 ≃L[ℝ] Space 3 :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)

@[simp]
lemma spatialDilationCLE_apply (r : ℝ) (hr : r ≠ 0) (x : Space 3) :
    spatialDilationCLE r hr x = r • x :=
  rfl

/-- The mass-preserving three-dimensional dilation
`ψ_r(x) = r sqrt(r) ψ(r x)` for `r > 0`. -/
noncomputable def massPreservingDilation
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) : 𝓢(Space 3, ℝ) :=
  (r * Real.sqrt r) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (spatialDilationCLE r hr.ne') ψ

@[simp]
lemma massPreservingDilation_apply
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    massPreservingDilation r hr ψ x =
      (r * Real.sqrt r) * ψ (r • x) :=
  rfl

/-- The square of the three-dimensional mass-preserving amplitude is `r³`. -/
lemma massPreservingDilation_amplitude_sq (r : ℝ) (hr : 0 < r) :
    (r * Real.sqrt r) ^ 2 = r ^ 3 := by
  rw [mul_pow, Real.sq_sqrt hr.le]
  ring

/-- The Born density of the mass-preserving wave dilation is the
mass-preserving density dilation `r³ ρ(rx)`. -/
lemma massPreservingDilation_bornDensity
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    (fun x => massPreservingDilation r hr ψ x ^ 2) =
      (r ^ 3) • dilateDensity r (fun x => ψ x ^ 2) := by
  funext x
  simp only [massPreservingDilation_apply, Pi.smul_apply, smul_eq_mul,
    dilateDensity, mul_pow]
  rw [Real.sq_sqrt hr.le]
  ring

/-- The Newtonian Hartree self-energy scales linearly under the
mass-preserving three-dimensional wave dilation. -/
@[zil_level physical_theorem]
lemma massPreservingDilation_selfEnergy
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    newtonianSelfEnergy (fun x => massPreservingDilation r hr ψ x ^ 2) =
      r * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
  rw [massPreservingDilation_bornDensity r hr ψ,
    newtonianSelfEnergy_smul,
    newtonianSelfEnergy_dilateDensity r hr.ne']
  rw [abs_of_pos hr]
  field_simp

/-- The Fréchet derivative of the mass-preserving dilation has the exact
chain-rule coefficient `r² sqrt(r)`. -/
lemma massPreservingDilation_fderiv
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    fderiv ℝ ((massPreservingDilation r hr ψ : 𝓢(Space 3, ℝ)) :
      Space 3 → ℝ) x =
      ((r * Real.sqrt r) * r) •
        fderiv ℝ (ψ : Space 3 → ℝ) (r • x) := by
  change fderiv ℝ (fun y => (r * Real.sqrt r) * ψ (r • y)) x = _
  rw [show (fun y => (r * Real.sqrt r) * ψ (r • y)) =
      (r * Real.sqrt r) • (fun y => ψ (r • y)) by
    ext y
    simp]
  rw [fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul]
  rw [smul_smul]

/-- The operator norm of a real scalar multiple of a real-valued continuous
linear functional is exactly the scalar times the norm when the scalar is
nonnegative. -/
private lemma norm_real_smul_continuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : 0 ≤ c) (L : E →L[ℝ] ℝ) :
    ‖c • L‖ = c * ‖L‖ := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · apply le_antisymm
    · simpa [Real.norm_eq_abs, abs_of_pos hc] using
        ContinuousLinearMap.opNorm_smul_le c L
    · have hinv := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • L)
      have hcancel : c⁻¹ • (c • L) = L := by
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [hcancel, Real.norm_eq_abs, abs_inv, abs_of_pos hc,
        inv_mul_eq_div] at hinv
      simpa [mul_comm] using (le_div_iff₀ hc).mp hinv

/-- The Dirichlet kinetic energy scales quadratically under the
mass-preserving three-dimensional wave dilation. -/
@[zil_level physical_theorem]
lemma massPreservingDilation_kineticEnergy
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    kineticEnergy (massPreservingDilation r hr ψ) =
      r ^ 2 * kineticEnergy ψ := by
  rw [← frechetKineticIntegral_eq (massPreservingDilation r hr ψ),
    ← frechetKineticIntegral_eq ψ]
  have hcoef : 0 < (r * Real.sqrt r) * r :=
    mul_pos (mul_pos hr (Real.sqrt_pos.mpr hr)) hr
  have hpoint (x : Space 3) :
      ‖fderiv ℝ
          ((massPreservingDilation r hr ψ : 𝓢(Space 3, ℝ)) :
            Space 3 → ℝ) x‖ ^ 2 =
        ((r * Real.sqrt r) * r) ^ 2 *
          ‖fderiv ℝ (ψ : Space 3 → ℝ) (r • x)‖ ^ 2 := by
    rw [massPreservingDilation_fderiv,
      norm_real_smul_continuousLinearMap _ hcoef.le, mul_pow]
  simp_rw [hpoint]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (fun x : Space 3 => ‖fderiv ℝ (ψ : Space 3 → ℝ) x‖ ^ 2)
      r (hR := hr.le), Space.finrank_eq_dim]
  simp only [smul_eq_mul]
  have hamp : ((r * Real.sqrt r) * r) ^ 2 = r ^ 5 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hr.le]
    ring
  rw [hamp]
  field_simp [hr.ne']

/-- The real `L²` mass integral is invariant under the mass-preserving
three-dimensional wave dilation. -/
lemma massPreservingDilation_integral_sq
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    ∫ x, massPreservingDilation r hr ψ x ^ 2 =
      ∫ x, ψ x ^ 2 := by
  simp_rw [massPreservingDilation_apply, mul_pow]
  simp_rw [Real.sq_sqrt hr.le]
  ring_nf
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (fun x : Space 3 => ψ x ^ 2) r (hR := hr.le),
    Space.finrank_eq_dim]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

/-- The squared-enorm lintegral of a real Schwartz state agrees with the
`ENNReal.ofReal` image of its ordinary squared integral. -/
lemma lintegral_enorm_sq_eq_ofReal_integral_sq (ψ : 𝓢(Space 3, ℝ)) :
    ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∫ x, ψ x ^ 2) := by
  have hi : Integrable (fun x : Space 3 => ψ x ^ 2) := by
    have hs :
        (fun x : Space 3 => ψ x ^ 2) =
          (SchwartzMap.smulLeftCLM ℝ (ψ : Space 3 → ℝ) ψ :
            𝓢(Space 3, ℝ)) := by
      funext x
      rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]
      simp [pow_two]
    rw [hs]
    exact SchwartzMap.integrable _
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg (ψ x))]
  apply lintegral_congr
  intro x
  rw [show ψ x ^ 2 = |ψ x| ^ 2 by rw [sq_abs],
    ENNReal.ofReal_pow (abs_nonneg (ψ x)) 2,
    ← Real.enorm_eq_ofReal_abs]
  norm_num

/-- The native squared-enorm `L²` normalization is invariant under the
mass-preserving three-dimensional wave dilation. -/
@[zil_level physical_theorem]
lemma massPreservingDilation_lintegral_enorm_sq
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    ∫⁻ x, ‖massPreservingDilation r hr ψ x‖ₑ ^ (2 : ℝ) =
      ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_enorm_sq_eq_ofReal_integral_sq,
    lintegral_enorm_sq_eq_ofReal_integral_sq,
    massPreservingDilation_integral_sq]

/-- Compact spatial support is invariant under every positive
mass-preserving dilation. -/
lemma massPreservingDilation_hasCompactSupport
    (r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ))
    (hψ : HasCompactSupport (ψ : Space 3 → ℝ)) :
    HasCompactSupport
      (massPreservingDilation r hr ψ : Space 3 → ℝ) := by
  have hcomp : HasCompactSupport
      (fun x : Space 3 => ψ (spatialDilationCLE r hr.ne' x)) := by
    simpa [Function.comp_def] using
      hψ.comp_homeomorph (spatialDilationCLE r hr.ne').toHomeomorph
  have hscaled := hcomp.smul_left
    (f := fun _ : Space 3 => r * Real.sqrt r)
  change HasCompactSupport
    (fun x : Space 3 => (r * Real.sqrt r) * ψ (r • x))
  have heq :
      (fun x : Space 3 => (r * Real.sqrt r) * ψ (r • x)) =
        (fun _ : Space 3 => r * Real.sqrt r) •
          fun x => ψ (spatialDilationCLE r hr.ne' x) := by
    funext x
    rfl
  rw [heq]
  exact hscaled

/-- Exact Schrödinger--Newton energy scaling on the mass-preserving ray:
the kinetic term scales as `r²`, while attraction scales as `r`. -/
@[zil_level physical_theorem]
lemma schrodingerNewtonEnergy_massPreservingDilation
    (G r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) =
      (1 / 2) * r ^ 2 * kineticEnergy ψ -
        (1 / 2) * G * r * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
  rw [schrodingerNewtonEnergy, massPreservingDilation_kineticEnergy,
    massPreservingDilation_selfEnergy]
  ring

/-- Every positive attractive coupling and every seed with positive Hartree
interaction admit a positive mass-preserving scale with strictly negative
Schrödinger--Newton energy. -/
@[zil_level physical_theorem]
lemma exists_massPreservingDilation_negative_energy
    (G : ℝ) (hG : 0 < G) (ψ : 𝓢(Space 3, ℝ))
    (hH : 0 < newtonianSelfEnergy (fun x => ψ x ^ 2)) :
    ∃ (r : ℝ) (hr : 0 < r),
      schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) < 0 := by
  let r := G * newtonianSelfEnergy (fun x => ψ x ^ 2) /
    (2 * (kineticEnergy ψ + 1))
  have hK : 0 ≤ kineticEnergy ψ := kineticEnergy_nonneg ψ
  have hr : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r, hr, ?_⟩
  have hrden :
      r * (2 * (kineticEnergy ψ + 1)) =
        G * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
    dsimp [r]
    field_simp
  have hKlt : kineticEnergy ψ < 2 * (kineticEnergy ψ + 1) := by
    nlinarith
  have hsmall :
      r * kineticEnergy ψ <
        G * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
    calc
      r * kineticEnergy ψ < r * (2 * (kineticEnergy ψ + 1)) :=
        mul_lt_mul_of_pos_left hKlt hr
      _ = G * newtonianSelfEnergy (fun x => ψ x ^ 2) := hrden
  calc
    schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) =
        (1 / 2) * r *
          (r * kineticEnergy ψ -
            G * newtonianSelfEnergy (fun x => ψ x ^ 2)) := by
      rw [schrodingerNewtonEnergy_massPreservingDilation G r hr ψ]
      ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos (by norm_num) hr) (sub_neg.mpr hsmall)

/-- Vanishing of the attractive Hartree interaction, the variational
signature of the dispersed branch in the Schrödinger--Newton problem. -/
def IsHartreeDispersed (ψ : 𝓢(Space 3, ℝ)) : Prop :=
  newtonianSelfEnergy (fun x => ψ x ^ 2) = 0

/-- A negative-energy state cannot lie in the
zero-Hartree dispersed branch. -/
@[zil_level physical_theorem]
lemma negative_energy_not_hartreeDispersed
    (G : ℝ) (ψ : 𝓢(Space 3, ℝ))
    (hE : schrodingerNewtonEnergy G ψ < 0) :
    ¬ IsHartreeDispersed ψ := by
  intro hdispersed
  change newtonianSelfEnergy (fun x => ψ x ^ 2) = 0 at hdispersed
  rw [schrodingerNewtonEnergy, hdispersed, mul_zero, sub_zero] at hE
  nlinarith [kineticEnergy_nonneg ψ]

/-- A normalized compactly supported seed with positive Hartree interaction
generates a normalized compactly supported negative-energy trial. This is the
strict-binding input that excludes the vanishing branch in a subsequent
concentration--compactness argument. -/
@[zil_level physical_theorem]
lemma exists_normalizedCore_negative_energy
    (G : ℝ) (hG : 0 < G) (ψ : 𝓢(Space 3, ℝ))
    (hnorm : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1)
    (hcompact : HasCompactSupport (ψ : Space 3 → ℝ))
    (hH : 0 < newtonianSelfEnergy (fun x => ψ x ^ 2)) :
    ∃ (r : ℝ) (hr : 0 < r),
      (∫⁻ x, ‖massPreservingDilation r hr ψ x‖ₑ ^ (2 : ℝ) = 1) ∧
      HasCompactSupport
        (massPreservingDilation r hr ψ : Space 3 → ℝ) ∧
      schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) < 0 := by
  obtain ⟨r, hr, hE⟩ :=
    exists_massPreservingDilation_negative_energy G hG ψ hH
  exact ⟨r, hr, (massPreservingDilation_lintegral_enorm_sq r hr ψ).trans hnorm,
    massPreservingDilation_hasCompactSupport r hr ψ hcompact, hE⟩

/-! ## B. Variational level, virial identity, and binding of a minimizer -/

/-- The normalized compactly supported Schwartz core on which the continuum
Sobolev coercivity estimate and the exact mass-preserving dilation are both
available. -/
def normalizedCompactCore : Set (𝓢(Space 3, ℝ)) :=
  {ψ | (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1) ∧
    HasCompactSupport (ψ : Space 3 → ℝ)}

/-- The constrained Schrödinger--Newton variational level on the normalized
compactly supported Schwartz core. -/
noncomputable def normalizedCoreGroundEnergy (G : ℝ) : ℝ :=
  sInf (schrodingerNewtonEnergy G '' normalizedCompactCore)

/-- The normalized-core energy range is bounded below at nonnegative
coupling by the already-proved continuum HLS--Sobolev coercivity bound. -/
lemma normalizedCompactCore_energy_bddBelow
    (G : ℝ) (hG : 0 ≤ G) :
    BddBelow (schrodingerNewtonEnergy G '' normalizedCompactCore) := by
  refine ⟨-(G * schrodingerNewtonStabilityConstant) ^ 2 / 8, ?_⟩
  rintro E ⟨ψ, hψ, rfl⟩
  exact schrodingerNewtonEnergy_normalized_stability
    G hG ψ hψ.1 hψ.2

/-- A normalized compactly supported seed with positive Hartree interaction
forces the actual constrained variational level strictly below zero. This is
the quantitative exclusion of the concentration--compactness vanishing
level, not an attainment theorem. -/
@[zil_level physical_theorem]
lemma normalizedCoreGroundEnergy_neg
    (G : ℝ) (hG : 0 < G) (ψ : 𝓢(Space 3, ℝ))
    (hnorm : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) = 1)
    (hcompact : HasCompactSupport (ψ : Space 3 → ℝ))
    (hH : 0 < newtonianSelfEnergy (fun x => ψ x ^ 2)) :
    normalizedCoreGroundEnergy G < 0 := by
  obtain ⟨r, hr, hnormr, hcompactr, hEr⟩ :=
    exists_normalizedCore_negative_energy G hG ψ hnorm hcompact hH
  have hmem :
      schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) ∈
        schrodingerNewtonEnergy G '' normalizedCompactCore :=
    ⟨massPreservingDilation r hr ψ, ⟨hnormr, hcompactr⟩, rfl⟩
  exact (csInf_le
    (normalizedCompactCore_energy_bddBelow G hG.le) hmem).trans_lt hEr

/-- An attained ground state on the normalized compact Schwartz core. The
membership field is explicit because `IsMinOn` itself does not assert that
the distinguished point belongs to the constraint set. -/
def IsNormalizedCoreGroundState
    (G : ℝ) (ψ : 𝓢(Space 3, ℝ)) : Prop :=
  ψ ∈ normalizedCompactCore ∧
    IsMinOn (schrodingerNewtonEnergy G) normalizedCompactCore ψ

/-- The exact quadratic-minus-linear energy profile along the
mass-preserving dilation orbit of a state. -/
noncomputable def dilationEnergyProfile
    (G : ℝ) (ψ : 𝓢(Space 3, ℝ)) (r : ℝ) : ℝ :=
  (1 / 2) * r ^ 2 * kineticEnergy ψ -
    (1 / 2) * G * r * newtonianSelfEnergy (fun x => ψ x ^ 2)

@[simp]
lemma dilationEnergyProfile_one
    (G : ℝ) (ψ : 𝓢(Space 3, ℝ)) :
    dilationEnergyProfile G ψ 1 = schrodingerNewtonEnergy G ψ := by
  simp [dilationEnergyProfile, schrodingerNewtonEnergy]

/-- At every positive scale the algebraic dilation profile is the actual
Schrödinger--Newton energy of the normalized spatially dilated state. -/
lemma dilationEnergyProfile_eq_energy
    (G r : ℝ) (hr : 0 < r) (ψ : 𝓢(Space 3, ℝ)) :
    dilationEnergyProfile G ψ r =
      schrodingerNewtonEnergy G (massPreservingDilation r hr ψ) := by
  exact (schrodingerNewtonEnergy_massPreservingDilation
    G r hr ψ).symm

/-- The derivative of the exact dilation energy profile. -/
lemma hasDerivAt_dilationEnergyProfile
    (G : ℝ) (ψ : 𝓢(Space 3, ℝ)) (r : ℝ) :
    HasDerivAt (dilationEnergyProfile G ψ)
      (r * kineticEnergy ψ -
        (1 / 2) * G * newtonianSelfEnergy (fun x => ψ x ^ 2)) r := by
  unfold dilationEnergyProfile
  convert
    (((hasDerivAt_pow 2 r).const_mul
      ((1 / 2) * kineticEnergy ψ)).sub
      ((hasDerivAt_id r).const_mul
        ((1 / 2) * G *
          newtonianSelfEnergy (fun x => ψ x ^ 2)))) using 1 <;> try rfl
  · funext s
    simp only [Pi.sub_apply, id_eq]
    ring
  · norm_num
    ring

/-- Every attained normalized-core ground state is a local minimum of the
exact mass-preserving dilation profile at unit scale. -/
lemma IsNormalizedCoreGroundState.isLocalMin_dilationEnergyProfile
    {G : ℝ} {ψ : 𝓢(Space 3, ℝ)}
    (hground : IsNormalizedCoreGroundState G ψ) :
    IsLocalMin (dilationEnergyProfile G ψ) 1 := by
  rcases hground with ⟨hψ, hmin⟩
  change ∀ᶠ r in nhds 1, dilationEnergyProfile G ψ 1 ≤
    dilationEnergyProfile G ψ r
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
  rw [dilationEnergyProfile_one,
    dilationEnergyProfile_eq_energy G r hr ψ]
  exact hmin ⟨
    (massPreservingDilation_lintegral_enorm_sq r hr ψ).trans hψ.1,
    massPreservingDilation_hasCompactSupport r hr ψ hψ.2⟩

/-- **Schrödinger--Newton virial identity.** Any actually attained
normalized-core ground state satisfies `2 K = G H`. It follows by applying
Fermat's theorem to the exact mass-preserving dilation orbit, rather than by
postulating a stationary balance equation. -/
@[zil_level physical_theorem]
lemma IsNormalizedCoreGroundState.virial
    {G : ℝ} {ψ : 𝓢(Space 3, ℝ)}
    (hground : IsNormalizedCoreGroundState G ψ) :
    2 * kineticEnergy ψ =
      G * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
  have hzero :=
    hground.isLocalMin_dilationEnergyProfile.deriv_eq_zero
  have hderiv :=
    (hasDerivAt_dilationEnergyProfile G ψ 1).deriv
  rw [hderiv] at hzero
  norm_num at hzero
  linarith

/-- At an attained normalized-core ground state, the total energy is exactly
minus one half of the kinetic energy. -/
@[zil_level physical_theorem]
lemma IsNormalizedCoreGroundState.energy_eq_neg_half_kinetic
    {G : ℝ} {ψ : 𝓢(Space 3, ℝ)}
    (hground : IsNormalizedCoreGroundState G ψ) :
    schrodingerNewtonEnergy G ψ = -(1 / 2) * kineticEnergy ψ := by
  rw [schrodingerNewtonEnergy]
  nlinarith [hground.virial]

/-- At an attained normalized-core ground state, the total energy is exactly
minus one quarter of the gravitational Hartree interaction. -/
@[zil_level physical_theorem]
lemma IsNormalizedCoreGroundState.energy_eq_neg_quarter_selfEnergy
    {G : ℝ} {ψ : 𝓢(Space 3, ℝ)}
    (hground : IsNormalizedCoreGroundState G ψ) :
    schrodingerNewtonEnergy G ψ =
      -(1 / 4) * G * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
  rw [schrodingerNewtonEnergy]
  nlinarith [hground.virial]

/-- If a positive-Hartree seed exists, every attained normalized-core ground
state has strictly negative binding energy. -/
@[zil_level physical_theorem]
lemma IsNormalizedCoreGroundState.energy_neg_of_seed
    {G : ℝ} (hG : 0 < G) {ψ seed : 𝓢(Space 3, ℝ)}
    (hground : IsNormalizedCoreGroundState G ψ)
    (hseedNorm : ∫⁻ x, ‖seed x‖ₑ ^ (2 : ℝ) = 1)
    (hseedCompact : HasCompactSupport (seed : Space 3 → ℝ))
    (hseedHartree :
      0 < newtonianSelfEnergy (fun x => seed x ^ 2)) :
    schrodingerNewtonEnergy G ψ < 0 := by
  obtain ⟨r, hr, hnormr, hcompactr, hEr⟩ :=
    exists_normalizedCore_negative_energy G hG seed
      hseedNorm hseedCompact hseedHartree
  exact (hground.2 ⟨hnormr, hcompactr⟩).trans_lt hEr

/-! ## C. Exact mass scaling and exclusion of dichotomy -/

/-- The finite real `L²` mass of a real Schwartz state. -/
noncomputable def waveMass (ψ : 𝓢(Space 3, ℝ)) : ℝ :=
  ∫ x, ψ x ^ 2

/-- The compactly supported Schwartz constraint set at real mass `M`. -/
def compactCoreAtMass (M : ℝ) : Set (𝓢(Space 3, ℝ)) :=
  {ψ | waveMass ψ = M ∧ HasCompactSupport (ψ : Space 3 → ℝ)}

/-- The constrained energy level at real mass `M`. -/
noncomputable def compactCoreGroundEnergy (G M : ℝ) : ℝ :=
  sInf (schrodingerNewtonEnergy G '' compactCoreAtMass M)

/-- The real mass is nonnegative. -/
lemma waveMass_nonneg (ψ : 𝓢(Space 3, ℝ)) :
    0 ≤ waveMass ψ := by
  exact integral_nonneg fun _ => sq_nonneg _

/-- The native ENNReal-normalized core agrees exactly with the real
unit-mass compact core. -/
lemma compactCoreAtMass_one_eq_normalizedCompactCore :
    compactCoreAtMass 1 = normalizedCompactCore := by
  ext ψ
  constructor
  · rintro ⟨hmass, hcompact⟩
    refine ⟨?_, hcompact⟩
    rw [lintegral_enorm_sq_eq_ofReal_integral_sq, ← waveMass]
    simp [hmass]
  · rintro ⟨hmass, hcompact⟩
    refine ⟨?_, hcompact⟩
    rw [lintegral_enorm_sq_eq_ofReal_integral_sq,
      ENNReal.ofReal_eq_one] at hmass
    exact hmass

/-- Scalar multiplication of a Schwartz state scales the kinetic energy
quadratically. -/
lemma kineticEnergy_smul
    (c : ℝ) (ψ : 𝓢(Space 3, ℝ)) :
    kineticEnergy (c • ψ) = c ^ 2 * kineticEnergy ψ := by
  unfold kineticEnergy
  have hgrad (x : Space 3) :
      gradSchwartz (c • ψ) x = c • gradSchwartz ψ x := by
    change (gradSchwartz (c • ψ)) x = _
    rw [map_smul]
    rfl
  simp_rw [hgrad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]

/-- The mass-changing three-dimensional scaling
`ψ ↦ M² ψ(Mx)`, implemented by multiplying the existing mass-preserving
dilation by `sqrt M`. -/
noncomputable def massScaling
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) : 𝓢(Space 3, ℝ) :=
  Real.sqrt M • massPreservingDilation M hM ψ

@[simp]
lemma massScaling_apply
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    massScaling M hM ψ x = M ^ 2 * ψ (M • x) := by
  rw [massScaling, SchwartzMap.smul_apply,
    massPreservingDilation_apply, smul_eq_mul]
  calc
    Real.sqrt M * (M * Real.sqrt M * ψ (M • x)) =
        M * (Real.sqrt M * Real.sqrt M) * ψ (M • x) := by ring
    _ = M ^ 2 * ψ (M • x) := by
      rw [Real.mul_self_sqrt hM.le]
      ring

/-- The mass-changing scaling multiplies the real `L²` mass by `M`. -/
lemma waveMass_massScaling
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) :
    waveMass (massScaling M hM ψ) = M * waveMass ψ := by
  unfold waveMass massScaling
  have hpoint (x : Space 3) :
      (Real.sqrt M *
        massPreservingDilation M hM ψ x) ^ 2 =
        M * massPreservingDilation M hM ψ x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hM.le]
  simp_rw [SchwartzMap.smul_apply, smul_eq_mul, hpoint]
  rw [integral_const_mul, massPreservingDilation_integral_sq]

/-- The mass-changing scaling multiplies kinetic energy by `M³`. -/
lemma kineticEnergy_massScaling
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) :
    kineticEnergy (massScaling M hM ψ) =
      M ^ 3 * kineticEnergy ψ := by
  rw [massScaling, kineticEnergy_smul, Real.sq_sqrt hM.le,
    massPreservingDilation_kineticEnergy]
  ring

/-- The mass-changing scaling multiplies the Hartree interaction by `M³`. -/
lemma selfEnergy_massScaling
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) :
    newtonianSelfEnergy (fun x => massScaling M hM ψ x ^ 2) =
      M ^ 3 * newtonianSelfEnergy (fun x => ψ x ^ 2) := by
  have hdensity :
      (fun x => massScaling M hM ψ x ^ 2) =
        M • fun x => massPreservingDilation M hM ψ x ^ 2 := by
    funext x
    simp only [massScaling, SchwartzMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, mul_pow, Real.sq_sqrt hM.le]
  rw [hdensity, newtonianSelfEnergy_smul,
    massPreservingDilation_selfEnergy]
  ring

/-- Both terms of the Schrödinger--Newton functional scale by `M³` under
the exact mass-changing map. -/
@[zil_level physical_theorem]
lemma schrodingerNewtonEnergy_massScaling
    (G M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) :
    schrodingerNewtonEnergy G (massScaling M hM ψ) =
      M ^ 3 * schrodingerNewtonEnergy G ψ := by
  rw [schrodingerNewtonEnergy, kineticEnergy_massScaling,
    selfEnergy_massScaling, schrodingerNewtonEnergy]
  ring

/-- Compact support is preserved by the mass-changing scaling. -/
lemma massScaling_hasCompactSupport
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ))
    (hψ : HasCompactSupport (ψ : Space 3 → ℝ)) :
    HasCompactSupport (massScaling M hM ψ : Space 3 → ℝ) := by
  have hscaled :=
    (massPreservingDilation_hasCompactSupport M hM ψ hψ).smul_left
      (f := fun _ : Space 3 => Real.sqrt M)
  rw [show (massScaling M hM ψ : Space 3 → ℝ) =
      (fun _ : Space 3 => Real.sqrt M) *
        (massPreservingDilation M hM ψ : Space 3 → ℝ) by
    funext x
    rfl]
  exact hscaled

/-- Scaling by `M` and then by `M⁻¹` returns the original Schwartz state. -/
lemma massScaling_inv_comp
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ)) :
    massScaling M⁻¹ (inv_pos.mpr hM)
      (massScaling M hM ψ) = ψ := by
  ext x
  rw [massScaling_apply, massScaling_apply]
  simp only [smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
  field_simp [hM.ne']
  simp

/-- Scaling a unit-mass compact-core state by `M` produces a state in the
mass-`M` compact core. -/
lemma massScaling_mem_compactCoreAtMass
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ))
    (hψ : ψ ∈ compactCoreAtMass 1) :
    massScaling M hM ψ ∈ compactCoreAtMass M := by
  exact ⟨by rw [waveMass_massScaling, hψ.1, mul_one],
    massScaling_hasCompactSupport M hM ψ hψ.2⟩

/-- Inverse scaling sends every mass-`M` compact-core state back to the
unit-mass compact core. -/
lemma massScaling_inv_mem_compactCoreAtMass_one
    (M : ℝ) (hM : 0 < M) (ψ : 𝓢(Space 3, ℝ))
    (hψ : ψ ∈ compactCoreAtMass M) :
    massScaling M⁻¹ (inv_pos.mpr hM) ψ ∈ compactCoreAtMass 1 := by
  constructor
  · rw [waveMass_massScaling, hψ.1]
    field_simp [hM.ne']
  · exact massScaling_hasCompactSupport M⁻¹ (inv_pos.mpr hM) ψ hψ.2

/-- The energy range at mass `M` is exactly `M³` times the unit-mass energy
range. This is a set equality induced by the explicit mutually inverse
Schwartz scalings, not an assumed homogeneity of the infimum. -/
lemma energyRangeAtMass_eq_smul
    (G M : ℝ) (hM : 0 < M) :
    schrodingerNewtonEnergy G '' compactCoreAtMass M =
      (M ^ 3) •
        (schrodingerNewtonEnergy G '' compactCoreAtMass 1) := by
  ext E
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    let ψ := massScaling M⁻¹ (inv_pos.mpr hM) φ
    have hψ : ψ ∈ compactCoreAtMass 1 :=
      massScaling_inv_mem_compactCoreAtMass_one M hM φ hφ
    refine Set.mem_smul_set.mpr
      ⟨schrodingerNewtonEnergy G ψ, ⟨ψ, hψ, rfl⟩, ?_⟩
    dsimp [ψ]
    rw [schrodingerNewtonEnergy_massScaling]
    field_simp [hM.ne']
  · rintro ⟨E, ⟨ψ, hψ, rfl⟩, rfl⟩
    refine ⟨massScaling M hM ψ,
      massScaling_mem_compactCoreAtMass M hM ψ hψ, ?_⟩
    rw [schrodingerNewtonEnergy_massScaling]
    rfl

/-- The unit-mass real variational level is the previously defined native
ENNReal-normalized level. -/
lemma compactCoreGroundEnergy_one
    (G : ℝ) :
    compactCoreGroundEnergy G 1 = normalizedCoreGroundEnergy G := by
  rw [compactCoreGroundEnergy, normalizedCoreGroundEnergy,
    compactCoreAtMass_one_eq_normalizedCompactCore]

/-- Exact cubic mass law for the constrained Schrödinger--Newton variational
level: `I_G(M) = M³ I_G(1)` for every positive mass. -/
@[zil_level physical_theorem]
lemma compactCoreGroundEnergy_massScaling
    (G M : ℝ) (hM : 0 < M) :
    compactCoreGroundEnergy G M =
      M ^ 3 * normalizedCoreGroundEnergy G := by
  rw [compactCoreGroundEnergy, energyRangeAtMass_eq_smul G M hM,
    Real.sInf_smul_of_nonneg (by positivity), smul_eq_mul,
    ← compactCoreGroundEnergy, compactCoreGroundEnergy_one]

/-- **Strict binding against dichotomy.** At positive coupling, once a
normalized positive-Hartree seed supplies `I_G(1)<0`, every nontrivial split
`M=a+(M-a)` obeys `I_G(M) < I_G(a)+I_G(M-a)`. This is the standard strict
subadditivity input excluding the dichotomy branch of concentration
compactness. -/
@[zil_level physical_theorem]
lemma compactCoreGroundEnergy_strict_subadditive
    (G M a : ℝ) (hG : 0 < G) (ha : 0 < a) (haM : a < M)
    (seed : 𝓢(Space 3, ℝ))
    (hseedNorm : ∫⁻ x, ‖seed x‖ₑ ^ (2 : ℝ) = 1)
    (hseedCompact : HasCompactSupport (seed : Space 3 → ℝ))
    (hseedHartree :
      0 < newtonianSelfEnergy (fun x => seed x ^ 2)) :
    compactCoreGroundEnergy G M <
      compactCoreGroundEnergy G a +
        compactCoreGroundEnergy G (M - a) := by
  have hM : 0 < M := ha.trans haM
  have hMa : 0 < M - a := sub_pos.mpr haM
  rw [compactCoreGroundEnergy_massScaling G M hM,
    compactCoreGroundEnergy_massScaling G a ha,
    compactCoreGroundEnergy_massScaling G (M - a) hMa]
  have hI :=
    normalizedCoreGroundEnergy_neg G hG seed
      hseedNorm hseedCompact hseedHartree
  have hcube :
      0 < M ^ 3 - (a ^ 3 + (M - a) ^ 3) := by
    have hprod : 0 < 3 * M * a * (M - a) := by positivity
    nlinarith
  have hneg :
      (M ^ 3 - (a ^ 3 + (M - a) ^ 3)) *
        normalizedCoreGroundEnergy G < 0 :=
    mul_neg_of_pos_of_neg hcube hI
  nlinarith

/-- The energetic cost of splitting total mass `M` into the two clusters
`a` and `M-a`. Positive gap means that the unsplit state is energetically
preferred. -/
noncomputable def compactCoreBindingGap (G M a : ℝ) : ℝ :=
  compactCoreGroundEnergy G a +
    compactCoreGroundEnergy G (M - a) -
      compactCoreGroundEnergy G M

/-- Exact quantitative binding-gap formula. The cubic mass law turns the
gap into the positive geometric factor `3 M a (M-a)` times the magnitude of
the unit-mass ground level. -/
@[zil_level physical_theorem]
lemma compactCoreBindingGap_eq
    (G M a : ℝ) (ha : 0 < a) (haM : a < M) :
    compactCoreBindingGap G M a =
      3 * M * a * (M - a) * (-normalizedCoreGroundEnergy G) := by
  have hM : 0 < M := ha.trans haM
  have hMa : 0 < M - a := sub_pos.mpr haM
  rw [compactCoreBindingGap,
    compactCoreGroundEnergy_massScaling G a ha,
    compactCoreGroundEnergy_massScaling G (M - a) hMa,
    compactCoreGroundEnergy_massScaling G M hM]
  ring

/-- Every nontrivial cluster split has a strictly positive binding gap at
positive coupling, given a unit-mass compact seed with positive Hartree
interaction. This is the quantitative form of exclusion of dichotomy. -/
@[zil_level physical_theorem]
lemma compactCoreBindingGap_pos
    (G M a : ℝ) (hG : 0 < G) (ha : 0 < a) (haM : a < M)
    (seed : 𝓢(Space 3, ℝ))
    (hseedNorm : ∫⁻ x, ‖seed x‖ₑ ^ (2 : ℝ) = 1)
    (hseedCompact : HasCompactSupport (seed : Space 3 → ℝ))
    (hseedHartree :
      0 < newtonianSelfEnergy (fun x => seed x ^ 2)) :
    0 < compactCoreBindingGap G M a := by
  rw [compactCoreBindingGap_eq G M a ha haM]
  have hI :=
    normalizedCoreGroundEnergy_neg G hG seed
      hseedNorm hseedCompact hseedHartree
  have hM : 0 < M := ha.trans haM
  have hMa : 0 < M - a := sub_pos.mpr haM
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) hM) ha) hMa)
    (neg_pos.mpr hI)

/-- At the repository's inference-scale coupling
`G = ħ c σ₀⁴`, positive `ħ`, `c`, and nonzero `σ₀` produce the same
strictly positive cluster-binding gap without taking Newton's constant as an
independent theorem input. -/
@[zil_level physical_theorem]
lemma inferenceNewton_compactCoreBindingGap_pos
    (ħ c σ₀ M a : ℝ)
    (hħ : 0 < ħ) (hc : 0 < c) (hσ₀ : σ₀ ≠ 0)
    (ha : 0 < a) (haM : a < M)
    (seed : 𝓢(Space 3, ℝ))
    (hseedNorm : ∫⁻ x, ‖seed x‖ₑ ^ (2 : ℝ) = 1)
    (hseedCompact : HasCompactSupport (seed : Space 3 → ℝ))
    (hseedHartree :
      0 < newtonianSelfEnergy (fun x => seed x ^ 2)) :
    0 < compactCoreBindingGap (ħ * c * σ₀ ^ 4) M a := by
  apply compactCoreBindingGap_pos
    (G := ħ * c * σ₀ ^ 4) (M := M) (a := a)
    (seed := seed) (ha := ha) (haM := haM)
    (hseedNorm := hseedNorm) (hseedCompact := hseedCompact)
    (hseedHartree := hseedHartree)
  have hσ₀2 : 0 < σ₀ ^ 2 := sq_pos_of_ne_zero hσ₀
  have hσ₀4 : 0 < σ₀ ^ 4 := by
    rw [show σ₀ ^ 4 = (σ₀ ^ 2) ^ 2 by ring]
    exact pow_pos hσ₀2 2
  exact mul_pos (mul_pos hħ hc) hσ₀4

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.kineticEnergy_nonneg where
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:the-kinetic-dirichlet-energy-of-a-schrodinger-newton-state-the-integral-of-the-squared-norm-of-the-schwartz-gradient-of-psi-is-nonnegative"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.norm_fderiv_eq_gradSchwartz where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:pointwise-the-operator-norm-of-the-real-scalar-frechet-derivative-equals-the-euclidean-norm-of-the-repositorys-grad-schwartz-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetKineticIntegral_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.norm_fderiv_eq_gradSchwartz",
  formalizes @ "claim:the-integral-of-the-squared-frechet-derivative-norm-is-exactly-the-schrodinger-newton-dirichlet-kinetic-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetGradient_eLpNorm_sq_eq_kineticEnergy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetKineticIntegral_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.kineticEnergy_nonneg",
  formalizes @ "claim:the-square-of-the-continuum-l-two-frechet-gradient-norm-is-exactly-the-repositorys-real-space-dirichlet-kinetic-energy",
  requires @ "claim:the-integral-of-the-squared-frechet-derivative-norm-is-exactly-the-schrodinger-newton-dirichlet-kinetic-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_nonneg where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianSelfEnergy_nonneg",
  formalizes @ "claim:the-gravitational-self-interaction-term-of-the-schrodinger-newton-energy-functional-the-double-integral-of-psi-squared-x-psi-squared-y-over-norm-x-minus-y-is-nonnegative-because-the-density-psi-squared-is-nonnegative-and-the-newton-kernel-positive"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schwartzBornDensity_lsixFifths where
  formalizes @ "claim:the-born-density-psi-squared-of-every-real-schwartz-wavefunction-on-r-three-has-finite-l-six-fifths-mass-equivalently-psi-has-finite-l-twelve-fifths-mass",
  supported_by @ "lean:SchwartzMap.memLp"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lintegral_ltwo_lsix_interpolation where
  formalizes @ "claim:on-r-three-holder-with-conjugate-exponents-ten-ninths-and-ten-proves-the-continuum-interpolation-integral-u-to-the-twelve-fifths-to-the-five-thirds-is-at-most-integral-u-squared-to-the-three-halves-times-integral-u-to-the-sixth-to-the-one-sixth",
  supported_by @ "lean:ENNReal.lintegral_mul_le_Lp_mul_Lq"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.bornDensity_ltwo_lsix_interpolation where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lintegral_ltwo_lsix_interpolation",
  formalizes @ "claim:the-l-six-fifths-hls-power-of-the-born-density-psi-squared-is-controlled-by-the-l-two-mass-to-the-third-power-times-the-l-six-wavefunction-norm",
  requires @ "claim:on-r-three-holder-with-conjugate-exponents-ten-ninths-and-ten-proves-the-continuum-interpolation-integral-u-to-the-twelve-fifths-to-the-five-thirds-is-at-most-integral-u-squared-to-the-three-halves-times-integral-u-to-the-sixth-to-the-one-sixth"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.newtonianHLSBound_bornDensity_le where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.bornDensity_ltwo_lsix_interpolation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_nonneg",
  formalizes @ "claim:the-explicit-hls-functional-of-a-schwartz-born-density-is-at-most-the-named-hls-coefficient-times-the-l-two-mass-to-the-third-power-times-the-l-six-wavefunction-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_le_hls where
  formalizes @ "claim:the-newtonian-hartree-self-gravity-of-every-real-schwartz-wavefunction-is-bounded-by-the-explicit-general-density-hls-functional-of-its-born-density-psi-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_le_hls"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_lsix where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.newtonianHLSBound_bornDensity_le",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_le_hls",
  formalizes @ "claim:for-an-l-two-normalized-real-schwartz-state-the-newtonian-hartree-self-gravity-is-at-most-the-explicit-hls-coefficient-times-the-l-six-wavefunction-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lsix_le_frechetGradient where
  formalizes @ "claim:on-the-compactly-supported-real-schwartz-core-in-r-three-the-continuum-l-six-norm-is-at-most-the-mathlib-sobolev-constant-times-the-l-two-norm-of-the-actual-frechet-derivative",
  supported_by @ "lean:MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_frechetGradient where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lsix_le_frechetGradient",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_lsix",
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:for-a-normalized-compactly-supported-real-schwartz-state-the-newtonian-hartree-self-gravity-is-at-most-the-hls-coefficient-times-the-sobolev-constant-times-the-continuum-l-two-frechet-gradient-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_hls_lower_bound where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_le_hls",
  formalizes @ "claim:for-nonnegative-newton-coupling-g-the-attractive-schrodinger-newton-energy-is-bounded-below-by-one-half-the-kinetic-energy-minus-one-half-g-times-the-explicit-hls-bound-of-the-born-density"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_lsix_lower_bound where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_lsix",
  formalizes @ "claim:for-a-normalized-real-schwartz-state-and-nonnegative-g-the-schrodinger-newton-energy-is-bounded-below-by-one-half-the-dirichlet-energy-minus-one-half-g-times-the-explicit-hls-coefficient-times-the-l-six-norm",
  caveat @ "claim:this-is-the-exact-pre-coercive-continuum-bound-the-final-replacement-of-the-l-six-norm-by-the-real-grad-schwartz-l-two-kinetic-scale-is-a-separate-sobolev-endpoint-bridge"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_frechetGradient_lower_bound where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_frechetGradient",
  formalizes @ "claim:on-the-normalized-compactly-supported-schwartz-core-the-attractive-schrodinger-newton-energy-is-bounded-below-by-one-half-the-dirichlet-energy-minus-a-term-linear-in-the-genuine-continuum-l-two-frechet-gradient-norm",
  caveat @ "claim:compact-support-is-the-explicit-premise-of-the-used-mathlib-sobolev-endpoint-extension-to-the-full-h-one-closure-is-a-separate-density-and-lower-semicontinuity-step"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_stability where
  formalizes @ "claim:on-the-normalized-compactly-supported-real-schwartz-core-the-attractive-schrodinger-newton-energy-has-the-state-independent-lower-bound-minus-the-square-of-g-times-the-composed-hls-sobolev-stability-constant-divided-by-eight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetGradient_eLpNorm_sq_eq_kineticEnergy",
  caveat @ "claim:this-is-a-genuine-completing-the-square-stability-bound-on-the-compactly-supported-schwartz-core-extension-to-all-h-one-states-requires-density-and-lower-semicontinuity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.massPreservingDilation_lintegral_enorm_sq where
  formalizes @ "claim:the-three-dimensional-wave-dilation-psi-r-of-x-equals-r-times-square-root-r-times-psi-of-rx-preserves-the-native-continuum-l-two-mass-exactly",
  supported_by @ "lean:MeasureTheory.Measure.integral_comp_smul_of_nonneg",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_massPreservingDilation where
  formalizes @ "claim:under-the-mass-preserving-three-dimensional-wave-dilation-the-schrodinger-newton-kinetic-energy-scales-as-r-squared-and-the-attractive-hartree-self-energy-scales-as-r",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_dilateDensity",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.exists_massPreservingDilation_negative_energy where
  formalizes @ "claim:at-every-positive-attractive-coupling-every-schwartz-seed-with-positive-hartree-interaction-has-a-positive-mass-preserving-scale-with-strictly-negative-schrodinger-newton-energy",
  supported_by @ "paper:schrodinger-newton-equation-and-its-foundations-arxiv-1407.4370",
  requires @ "claim:the-seed-has-strictly-positive-newtonian-hartree-self-interaction",
  epistemic_status @ "risky",
  caveat @ "claim:this-proves-a-negative-binding-trial-not-attainment-of-the-variational-infimum-a-stationary-ground-state-or-orbital-stability"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.negative_energy_not_hartreeDispersed where
  formalizes @ "claim:a-negative-energy-schrodinger-newton-state-cannot-belong-to-the-zero-hartree-dispersed-branch",
  supported_by @ "paper:schrodinger-newton-equation-and-its-foundations-arxiv-1407.4370",
  epistemic_status @ "risky",
  caveat @ "claim:this-excludes-the-vanishing-hartree-branch-but-does-not-by-itself-exclude-concentration-compactness-dichotomy-or-prove-precompactness-modulo-translations"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.exists_normalizedCore_negative_energy where
  formalizes @ "claim:a-normalized-compactly-supported-schwartz-seed-with-positive-hartree-interaction-generates-a-normalized-compactly-supported-strictly-negative-energy-trial-at-every-positive-coupling",
  supported_by @ "paper:schrodinger-newton-equation-and-its-foundations-arxiv-1407.4370",
  requires @ "claim:the-seed-has-unit-l-two-mass-compact-support-and-strictly-positive-hartree-interaction",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-the-strict-binding-input-that-rules-out-vanishing-it-is-not-the-remaining-concentration-compactness-attainment-or-orbital-stability-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalizedCoreGroundEnergy_neg where
  formalizes @ "claim:at-positive-attractive-coupling-a-normalized-compactly-supported-seed-with-positive-hartree-interaction-forces-the-constrained-schrodinger-newton-variational-infimum-strictly-below-the-zero-energy-dispersed-level",
  supported_by @ "lean:csInf_le",
  epistemic_status @ "risky",
  caveat @ "claim:this-proves-strict-negativity-of-the-infimum-and-excludes-the-vanishing-level-but-does-not-prove-that-the-infimum-is-attained-or-exclude-concentration-compactness-dichotomy"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.virial where
  formalizes @ "claim:any-attained-normalized-core-schrodinger-newton-ground-state-obeys-the-exact-virial-balance-two-times-kinetic-energy-equals-g-times-the-newtonian-hartree-self-energy",
  supported_by @ "lean:IsLocalMin.deriv_eq_zero",
  requires @ "claim:the-state-actually-attains-the-constrained-minimum-on-the-normalized-compact-schwartz-core",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:fermat-stationarity-along-the-exact-mass-preserving-dilation-derives-the-virial-identity-conditionally-on-attainment-it-is-not-an-existence-proof-for-a-minimizer"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_eq_neg_half_kinetic where
  formalizes @ "claim:for-an-attained-normalized-core-ground-state-the-schrodinger-newton-energy-equals-minus-one-half-the-dirichlet-kinetic-energy",
  requires @ "claim:the-attained-ground-state-obeys-the-derived-schrodinger-newton-virial-identity",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_eq_neg_quarter_selfEnergy where
  formalizes @ "claim:for-an-attained-normalized-core-ground-state-the-schrodinger-newton-energy-equals-minus-one-quarter-g-times-the-newtonian-hartree-self-energy",
  requires @ "claim:the-attained-ground-state-obeys-the-derived-schrodinger-newton-virial-identity",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_neg_of_seed where
  formalizes @ "claim:if-a-positive-hartree-normalized-compact-seed-exists-then-every-attained-normalized-core-ground-state-has-strictly-negative-binding-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence",
  requires @ "claim:the-ground-state-attains-the-constrained-minimum-and-the-seed-has-unit-l-two-mass-compact-support-and-positive-hartree-interaction",
  epistemic_status @ "risky",
  caveat @ "claim:the-general-bounded-h-one-weak-subsequence-theorem-is-now-proved-but-applying-it-to-this-minimizing-problem-still-requires-density-a-coercive-h-one-sequence-bound-tightness-mass-constraint-closure-and-hartree-lower-semicontinuity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_massScaling where
  formalizes @ "claim:the-three-dimensional-mass-changing-wave-scaling-psi-m-of-x-equals-m-squared-times-psi-of-mx-multiplies-the-l-two-mass-by-m-and-both-the-kinetic-and-newtonian-hartree-contributions-by-m-cubed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_massPreservingDilation",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreGroundEnergy_massScaling where
  formalizes @ "claim:the-positive-mass-constrained-compact-schwartz-schrodinger-newton-variational-level-obeys-the-exact-cubic-law-i-g-of-m-equals-m-cubed-times-i-g-of-one",
  supported_by @ "lean:Real.sInf_smul_of_nonneg",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-equality-is-for-the-compactly-supported-schwartz-variational-carrier-and-does-not-by-itself-prove-h-one-closure-attainment-or-an-euler-lagrange-ground-state"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreGroundEnergy_strict_subadditive where
  formalizes @ "claim:at-positive-coupling-and-given-a-unit-mass-compact-schwartz-seed-with-positive-hartree-interaction-the-constrained-energy-is-strictly-subadditive-under-every-nontrivial-positive-mass-split",
  requires @ "claim:the-seed-has-unit-l-two-mass-compact-support-and-strictly-positive-hartree-interaction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalizedCoreGroundEnergy_neg",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-the-standard-binding-inequality-excluding-concentration-compactness-dichotomy-on-the-compact-schwartz-variational-level-general-bounded-h-one-weak-precompactness-is-proved-separately-but-the-minimizing-sequence-bound-tightness-lower-semicontinuity-attainment-euler-lagrange-regularity-and-orbital-stability-are-not"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreGroundEnergy_massScaling",
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:the-energy-cost-of-splitting-total-mass-m-into-positive-clusters-a-and-m-minus-a-is-exactly-three-m-a-times-m-minus-a-times-the-negative-unit-mass-variational-level",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_pos where
  formalizes @ "claim:positive-attractive-coupling-and-a-unit-mass-positive-hartree-compact-schwartz-seed-make-the-exact-binding-gap-strictly-positive-for-every-nontrivial-cluster-split",
  requires @ "claim:the-seed-has-unit-l-two-mass-compact-support-and-strictly-positive-hartree-interaction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_eq",
  epistemic_status @ "risky",
  caveat @ "claim:the-positive-gap-is-the-quantitative-compact-core-dichotomy-exclusion-input-the-separate-general-h-one-weak-subsequence-theorem-does-not-by-itself-prove-tightness-mass-preservation-attainment-or-orbital-stability"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.inferenceNewton_compactCoreBindingGap_pos where
  formalizes @ "claim:at-the-model-coupling-g-equals-hbar-c-sigma-zero-to-the-fourth-positive-hbar-c-and-nonzero-sigma-zero-yield-a-strictly-positive-schrodinger-newton-cluster-binding-gap",
  requires @ "claim:the-inference-scale-identification-g-equals-hbar-c-sigma-zero-to-the-fourth-and-a-unit-mass-positive-hartree-compact-schwartz-seed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_pos",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-is-a-model-coupling-specialization-it-does-not-independently-calibrate-sigma-zero-to-the-observed-newton-constant-or-prove-ground-state-attainment"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.inferenceNewtonSchrodingerEnergy_hls_lower_bound where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_hls_lower_bound",
  formalizes @ "claim:at-the-repositorys-inference-scale-coupling-g-equals-hbar-times-c-times-sigma-zero-to-the-fourth-the-schrodinger-newton-energy-obeys-the-explicit-hls-lower-bound",
  caveat @ "claim:this-instantiates-the-model-coupling-g-equals-hbar-c-sigma-zero-four-it-does-not-independently-fit-sigma-zero-to-the-measured-newton-constant"

zil_file_contract physlib.schrodingerNewtonEnergy where
  promises "The Schrodinger-Newton energy functional for a real Schwartz state psi, with kinetic energy and attractive Newtonian Hartree self-gravity. In addition to both terms' sign properties, schwartzBornDensity_lsixFifths proves that psi squared belongs to L^(6/5) by the general Schwartz Lp theorem. The genuine continuum Holder theorem lintegral_ltwo_lsix_interpolation and its Born-density specialization identify the exact mass/L6 control of the HLS power. newtonianHLSBound_bornDensity_le reuses the separately named newtonianHLSConstant; for normalized states, normalized_selfGravity_le_lsix and schrodingerNewtonEnergy_normalized_lsix_lower_bound reduce the Hartree and total-energy estimates to a single L6 norm. On the compactly supported Schwartz core, lsix_le_frechetGradient applies Mathlib's actual dimension-three Sobolev theorem; normalized_selfGravity_le_frechetGradient and schrodingerNewtonEnergy_normalized_frechetGradient_lower_bound consequently control attraction by the genuine continuum L2 Frechet derivative. norm_fderiv_eq_gradSchwartz and frechetGradient_eLpNorm_sq_eq_kineticEnergy identify that analytic carrier exactly with the repository's real-space Dirichlet energy. Completing the square then proves schrodingerNewtonEnergy_normalized_stability, the state-independent lower bound minus (G times the composed HLS-Sobolev constant) squared over eight. The genuine continuum mass-preserving dilation psi-r(x)=r sqrt(r) psi(rx) preserves the native L2 normalization and compact support, scales kinetic energy as r squared and Hartree self-energy as r, and produces a normalized negative-energy trial at every positive coupling from any positive-Hartree seed. The resulting constrained variational level is strictly negative, excluding the zero-energy vanishing branch. The separate mass-changing scaling psi-m(x)=m squared psi(mx) multiplies mass by m and the full energy by m cubed; it identifies the complete energy range at mass m with m cubed times the unit-mass range, proves I-G(m)=m cubed I-G(1), and derives strict subadditivity for every nontrivial mass split, excluding the dichotomy branch on the compact Schwartz variational carrier. The corresponding cluster-binding gap is exactly three m a times m-minus-a times minus I-G(1), is strictly positive under the positive-Hartree seed premise, and remains positive at the model coupling G=hbar c sigma-zero-four. The imported complete continuum H1 carrier proves weak sequential precompactness for every Sobolev-norm-bounded sequence. If the unit level is attained, Fermat stationarity along the exact mass-preserving dilation orbit derives the virial identity two K equals G H and the binding identities E equals minus K over two equals minus G H over four. schrodingerNewton_selfGravity_le_hls and schrodingerNewtonEnergy_hls_lower_bound retain the unrestricted Schwartz bounds, while inferenceNewtonSchrodingerEnergy_hls_lower_bound specializes the result to G=hbar c sigma-zero-four. Honest: applying the general H1 weak-subsequence theorem to the compact Schwartz variational problem still requires a density/coercive-sequence bridge, tightness modulo translations, mass-constraint closure and Hartree lower semicontinuity; strict binding excludes both vanishing and dichotomy at the compact-core variational level but does not by itself prove concentration-compactness attainment, a stationary Euler-Lagrange ground state, regularity, or orbital stability; the virial and binding identities are explicitly conditional on actual attainment; and the inference-scale results are model-coupling specializations rather than an empirical fit of sigma-zero."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Space.gradSchwartz",
    "lean:SchwartzMap.memLp",
    "lean:ENNReal.lintegral_mul_le_Lp_mul_Lq",
    "lean:MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq",
    "lean:Space.gradSchwartz_apply_eq_grad",
    "lean:IsLocalMin.deriv_eq_zero",
    "lean:Real.sInf_smul_of_nonneg",
    "lean:MeasureTheory.Measure.integral_comp_smul_of_nonneg",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianHLSConstant",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_dilateDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonSelfGravity.newtonianSelfEnergy_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianSelfEnergySharpBound.newtonianSelfEnergy_le_hls"]
  forbids_substitutes ["a frequency-space Sobolev norm alone, whereas the kinetic term is the real-space Dirichlet integral of the Schwartz gradient",
    "a signed density, whereas the self-gravity nonnegativity uses the nonnegative density psi^2",
    "mere nonnegativity of the Hartree term, whereas the HLS theorem supplies a finite quantitative upper bound and total-energy lower bound",
    "an abstract Sobolev premise, whereas the compactly supported core theorem applies Mathlib's actual continuum Frechet-derivative inequality",
    "a negative-energy trial mislabeled as attainment of a ground-state minimizer or orbital stability",
    "the conditional virial identity mislabeled as a proof that a constrained minimizer exists",
    "a claim that strict subadditivity alone supplies the minimizing-sequence H1 bound, tightness, mass preservation, lower semicontinuity, attainment, Euler-Lagrange regularity or orbital stability",
    "a claim that the compactly supported-core result already supplies the density and lower-semicontinuity extension to every H1 state"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.kineticEnergy_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.norm_fderiv_eq_gradSchwartz,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetKineticIntegral_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.frechetGradient_eLpNorm_sq_eq_kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schwartzBornDensity_lsixFifths,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lintegral_ltwo_lsix_interpolation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.bornDensity_ltwo_lsix_interpolation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.newtonianHLSBound_bornDensity_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewton_selfGravity_le_hls,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_lsix,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.lsix_le_frechetGradient,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalized_selfGravity_le_frechetGradient,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_hls_lower_bound,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_lsix_lower_bound,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_frechetGradient_lower_bound,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_normalized_stability,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.massPreservingDilation_lintegral_enorm_sq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_massPreservingDilation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.exists_massPreservingDilation_negative_energy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.negative_energy_not_hartreeDispersed,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.exists_normalizedCore_negative_energy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.normalizedCoreGroundEnergy_neg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.virial,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_eq_neg_half_kinetic,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_eq_neg_quarter_selfEnergy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.IsNormalizedCoreGroundState.energy_neg_of_seed,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.schrodingerNewtonEnergy_massScaling,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreGroundEnergy_massScaling,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreGroundEnergy_strict_subadditive,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.compactCoreBindingGap_pos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.inferenceNewton_compactCoreBindingGap_pos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.SchrodingerNewtonEnergy.inferenceNewtonSchrodingerEnergy_hls_lower_bound]

/- ZIL-END -/
