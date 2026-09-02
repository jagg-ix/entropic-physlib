/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
public import Physlib.QuantumMechanics.NonHermitian.Propagator
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.UniformSpace.HeineCantor
meta import Zil

/-!
# The reversible limit as an analytic convergence: `Γ`/`η → ∞`

The frozen-sector reduction `FrozenLimit.frozen_limit_recovers_standard_physics` recovers standard
reversible physics **exactly at the premise** `H_I = 0` (equivalently at the separable point `K = 1`), and
its own docstring flags that it "does not prove convergence as a damping parameter tends to infinity; such
a result would require a separate `Tendsto` theorem." That analytic limit is the gap of thesis pillar III.

This file supplies it, in the concrete reversibility parameter — the rapidity `η`. The Schmidt number
`K = coth η = cosh η / sinh η` is the inverse boost velocity; as `η → ∞` the entanglement is switched off,
`K → 1`, and every entropic correction tends analytically to its reversible value:

* `schmidtNumber_tendsto_one` — `K = coth η → 1` (proved from `exp(−2η) → 0`);
* `entropicAction_tendsto_zero` — the imaginary action `S_I = ℏ·log K → 0`;
* `entropicProperDistance_tendsto_zero` — the entropic proper distance `r = λ_C·log K → 0`;
* `entanglementScreenArea_tendsto_zero` — the existing spherical screen area tends to zero;
* `comptonCellBits_tendsto_zero` — its `G`-free Compton-cell count tends to zero;
* `inferenceEinsteinCoupling_eq_comptonCellBitForm` — at every finite positive rapidity the
  independently supplied Compton-cell count fixes the Einstein coupling directly as
  `κ(σ₀) = 8πℏσ₀⁴/c³`, with no Newton constant among the theorem inputs;
* `gFree_complexEinstein_reversibleFamily` — the same `G`-free coupling gives a family of
  complex Einstein equations whose entropic curvature is `κ log(K(η)) S₀` and tends to zero,
  while the real Einstein sector remains fixed;
* `gFree_complexEinsteinTensor_tendsto_real` and
  `rapidityComplexStressEnergy_tendsto_real` — the full complex geometric and source
  tensors converge entrywise to their real sectors, not merely their imaginary components;
* `gFree_complexEinstein_conservationFamily` — real Bianchi plus a divergence-free reference
  entropic stress gives complex Bianchi and conservation of both sources at every rapidity;
* `inferenceNewtonianConvolutionPotential_eq_convolution` and
  `inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral` — the same inferred coupling
  weights the continuum Newtonian convolution and the Schrödinger–Poisson energy functional;
* `gFree_distributionalWeakFieldEinstein00_of_poisson` — the continuum distributional Poisson
  premise implies the weak-field Einstein `00` equation with `G = ℏcσ₀⁴`, without a `G` input;
* `inferenceNewtonTemperedPotential_weakFieldEinstein00` — on the complex tempered continuum
  carrier, the proved Newton convolution discharges that Poisson premise and yields the weak-field
  `00` equation directly;
* `inferenceNewtonTemperedPotential_source_action` — the same equation evaluated on every Schwartz
  test function has the explicit source integral `4πℏcσ₀⁴ ∫ρη`;
* `inferenceNewtonTemperedPotential_einstein00_and_energy_unique` — the same charted Schwartz
  density has both the `G`-free tempered weak-field Einstein equation and a unique zero-boundary
  continuum `Ḣ¹` energy solution; its `Ḣ⁻¹` source regularity is proved rather than assumed;
* `GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution` — on an arbitrary complete real
  Banach phase space (including continuum Sobolev carriers), a `C¹` Einstein evolution vector field
  has a local trajectory; an explicit Bianchi/constraint-propagation datum keeps the full complex
  tensor Einstein equation true along it with the `G`-free coupling;
* `GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique` — a Lipschitz evolution field makes
  that nonlinear Cauchy trajectory unique on its common local interval;
* `suppression_tendsto_one` — the path-integral weight `exp(−S_I/ℏ) → 1` (no suppression).
* `complexActionPathIntegralWeight_tendsto_phase` and `nnPathWeight_tendsto_phase` — the full scalar
  complex-action weights converge in `ℂ` to their common reversible phase.
* `entropicComplexHamiltonian_tendsto_reversible` — the `log K`-scaled irreversible operator vanishes
  in operator norm, so the complex Hamiltonian converges to its reversible generator;
* `entropicSchrodingerGenerator_tendsto_reversible` — the corresponding Schrödinger generators converge;
* `log_schmidtNumber_le_exp_rate` and the three operator error bounds — beyond
  `η = log 2 / 2`, the imaginary coefficient and operator errors are controlled explicitly by
  `4 exp(-2η)` (with the expected additional `1/|ℏ|` for the Schrödinger generator);
* `entropicPropagator_tendsto_reversible` — at each fixed time, the genuine Banach-algebra propagators
  converge in operator norm, hence strongly on every state.
* `entropicPropagator_tendstoUniformlyOn_boundedInterval` — convergence is uniform in operator norm
  on every bounded closed time interval, and uniformly strong on each fixed state.
* `entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval` and
  `entropicObservableExpectation_tendstoUniformlyOn_boundedInterval` — transition amplitudes and
  bounded-observable expectations inherit that bounded-time uniform recovery.
* `entropicBornWeight_tendstoUniformlyOn_initial` — for self-adjoint `H_R`, the evolved squared norm
  converges uniformly to the initial Born weight (and hence to one for a normalized supplied state).

So the frozen recovery is not only exact at `K = 1` but is the analytic limit of the entropic corrections
vanishing as `η → ∞` — the `Tendsto` upgrade the frozen-sector reduction lacked.

**Honest layering.** The operator result uses the explicit interpolation
`H_I(η) = log(K(η)) • H_I⁰`; it proves the reversible limit of that model, not that every physical
irreversible generator must have this rapidity dependence. Convergence is uniform on every bounded closed
time interval, but no global uniformity over all real times is claimed, nor convergence of path measures
or functional integrals.
The area and Compton-cell count both tend to zero. Their finite-`η` area-per-bit
quotient is not evaluated by substituting those limits (which would be `0/0`), and no limiting `G` is
inferred from this convergence alone.

## References

* Companions: `QuantumMechanics.FrozenLimit` (the exact `H_I = 0` reduction), `MuonAnomaly`.
  `SchmidtRapidityHyperbolicUnification` (`schmidtNumber = coth η`, `entropicAction = ℏ log K`),
  `ComptonClock.EntropicProperDistance` (`r = λ_C log K`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped Convolution Space SchwartzMap Laplacian NNReal
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.NonHermitian.Propagator
open QuantumMechanics.FiniteTarget
open Physlib.Thermodynamics
open Physlib.QFT.PathIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence

/-- The exact exponential form of the Schmidt number,
`coth η = (1 + exp(-2η))/(1 - exp(-2η))`. Keeping this identity public lets the
qualitative limit and the quantitative finite-rapidity estimates share one algebraic reduction. -/
theorem schmidtNumber_eq_exp_ratio (η : ℝ) :
    schmidtNumber η =
      (1 + Real.exp (-(2 * η))) / (1 - Real.exp (-(2 * η))) := by
  have hexpη : Real.exp (-η) ≠ 0 := (Real.exp_pos (-η)).ne'
  rw [schmidtNumber, Real.cosh_eq, Real.sinh_eq, div_div_div_cancel_right₀,
    ← mul_div_mul_right _ _ hexpη]
  congr 1
  · rw [add_mul, ← Real.exp_add, ← Real.exp_add, show η + -η = 0 by ring,
      show -η + -η = -(2 * η) by ring, Real.exp_zero]
  · rw [sub_mul, ← Real.exp_add, ← Real.exp_add, show η + -η = 0 by ring,
      show -η + -η = -(2 * η) by ring, Real.exp_zero]
  · norm_num

/-- **[The Schmidt number tends to `1` in the reversible limit]** `K = coth η = cosh η / sinh η → 1` as
`η → ∞` — the entanglement is switched off, `K → 1`, the separable/reversible point. Proved from
`exp(−2η) → 0` via `K = (1 + e^{−2η})/(1 − e^{−2η})`. -/
theorem schmidtNumber_tendsto_one :
    Tendsto (fun η : ℝ => schmidtNumber η) atTop (𝓝 1) := by
  have hu : Tendsto (fun η : ℝ => Real.exp (-(2 * η))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun η : ℝ => 2 * η) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr h2)
  have key : (fun η : ℝ => schmidtNumber η)
      =ᶠ[atTop] (fun η => (1 + Real.exp (-(2 * η))) / (1 - Real.exp (-(2 * η)))) :=
    Eventually.of_forall schmidtNumber_eq_exp_ratio
  rw [tendsto_congr' key]
  have hlim : Tendsto (fun η : ℝ => (1 + Real.exp (-(2 * η))) / (1 - Real.exp (-(2 * η))))
      atTop (𝓝 ((1 + 0) / (1 - 0))) := by
    apply Tendsto.div (tendsto_const_nhds.add hu) (tendsto_const_nhds.sub hu)
    norm_num
  simpa using hlim

/-- The entanglement entropy `log K → 0` in the reversible limit. -/
theorem log_schmidtNumber_tendsto_zero :
    Tendsto (fun η : ℝ => Real.log (schmidtNumber η)) atTop (𝓝 0) := by
  have hc := (Real.continuousAt_log (one_ne_zero)).tendsto.comp schmidtNumber_tendsto_one
  rwa [Real.log_one] at hc

/-- For positive rapidity, the finite entanglement defect has the exact form
`K(η) - 1 = 2 exp(-2η)/(1-exp(-2η))`. This exposes the exponential scale hidden by the
qualitative `Tendsto` statement. -/
theorem schmidtNumber_sub_one_eq_exp_defect (η : ℝ) (hη : 0 < η) :
    schmidtNumber η - 1 =
      2 * Real.exp (-(2 * η)) / (1 - Real.exp (-(2 * η))) := by
  rw [schmidtNumber_eq_exp_ratio]
  have hq : Real.exp (-(2 * η)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  field_simp [ne_of_gt (sub_pos.mpr hq)]
  ring

/-- **[Explicit reversible-limit rate]** Once `η ≥ log 2 / 2`, the imaginary-action coefficient
obeys `0 ≤ log K(η) ≤ 4 exp(-2η)`. Thus the analytic reversible limit is exponentially fast in
rapidity, with a concrete non-asymptotic constant. -/
@[zil_level physical_theorem]
theorem log_schmidtNumber_le_exp_rate (η : ℝ)
    (hη : Real.log 2 / 2 ≤ η) :
    0 ≤ Real.log (schmidtNumber η) ∧
      Real.log (schmidtNumber η) ≤ 4 * Real.exp (-(2 * η)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hK : 1 < schmidtNumber η := schmidtNumber_gt_one η hηpos
  have hqpos : 0 < Real.exp (-(2 * η)) := Real.exp_pos _
  have hqhalf : Real.exp (-(2 * η)) ≤ (1 / 2 : ℝ) := by
    have hexp : Real.exp (-(2 * η)) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (by linarith)
    simpa [Real.exp_neg, Real.exp_log (show 0 < (2 : ℝ) by norm_num)] using hexp
  constructor
  · exact Real.log_nonneg hK.le
  · calc
      Real.log (schmidtNumber η) ≤ schmidtNumber η - 1 :=
        Real.log_le_sub_one_of_pos (lt_trans (by norm_num) hK)
      _ = 2 * Real.exp (-(2 * η)) / (1 - Real.exp (-(2 * η))) :=
        schmidtNumber_sub_one_eq_exp_defect η hηpos
      _ ≤ 4 * Real.exp (-(2 * η)) := by
        apply (div_le_iff₀ (sub_pos.mpr (lt_of_le_of_lt hqhalf (by norm_num)))).2
        have hp : 0 ≤ Real.exp (-(2 * η)) *
            (1 - 2 * Real.exp (-(2 * η))) :=
          mul_nonneg hqpos.le (by linarith)
        nlinarith

/-- **[The imaginary action vanishes in the reversible limit]** `S_I = ℏ·log K → 0` as `η → ∞`: the
entropic (irreversible) sector of the complex action is switched off analytically, not only exactly at
`K = 1`. -/
theorem entropicAction_tendsto_zero (ħ : ℝ) :
    Tendsto (fun η : ℝ => entropicAction ħ η) atTop (𝓝 0) := by
  have h : Tendsto (fun η : ℝ => ħ * Real.log (schmidtNumber η)) atTop (𝓝 (ħ * 0)) :=
    tendsto_const_nhds.mul log_schmidtNumber_tendsto_zero
  simpa [entropicAction] using h

/-- **[The entropic proper distance vanishes in the reversible limit]** `r = λ_C·log K → 0` as `η → ∞` —
the entropic proper distance collapses to the reversible geometric point. -/
theorem entropicProperDistance_tendsto_zero (m c ħ : ℝ) :
    Tendsto (fun η : ℝ => entropicProperDistance m c ħ η) atTop (𝓝 0) := by
  have h : Tendsto (fun η : ℝ => comptonWavelength m c ħ * Real.log (schmidtNumber η)) atTop
      (𝓝 (comptonWavelength m c ħ * 0)) :=
    tendsto_const_nhds.mul log_schmidtNumber_tendsto_zero
  simpa [entropicProperDistance] using h

/-- **[The entanglement screen collapses in the reversible limit]** The spherical screen built from the
entropic proper distance has area `4πr² → 0`. This reuses the physical screen already present in the
Compton-clock arc rather than introducing a proxy. -/
@[zil_level physical_theorem]
theorem entanglementScreenArea_tendsto_zero (m c ħ : ℝ) :
    Tendsto (fun η : ℝ => sphereArea (entropicProperDistance m c ħ η)) atTop (𝓝 0) := by
  have hr := entropicProperDistance_tendsto_zero m c ħ
  have h : Tendsto
      (fun η : ℝ => (4 * Real.pi) * entropicProperDistance m c ħ η ^ 2) atTop
      (𝓝 ((4 * Real.pi) * 0 ^ 2)) :=
    tendsto_const_nhds.mul (hr.pow 2)
  simpa [sphereArea] using h

/-- **[The `G`-free screen count vanishes with the screen]** The existing Compton-cell count
`A / λ_C² → 0` as reversibility is restored. This does not determine a limiting Newton constant:
both the area and its count vanish, so substituting their limits in an area-per-bit quotient would be
the indeterminate expression `0/0`. -/
@[zil_level physical_theorem]
theorem comptonCellBits_tendsto_zero (m c ħ : ℝ) :
    Tendsto (fun η : ℝ => comptonCellBits m c ħ η) atTop (𝓝 0) := by
  have h := (entanglementScreenArea_tendsto_zero m c ħ).div_const
    (comptonWavelength m c ħ ^ 2)
  simpa [comptonCellBits] using h

/-! ## The `G`-free complex Einstein coupling and its reversible family -/

/-- **The Einstein coupling from the inference scale, without a Newton-constant input.**
Substituting the independently obtained `G = ℏcσ₀⁴` into `κ = 8πG/c⁴` and simplifying gives
`κ(σ₀) = 8πℏσ₀⁴/c³`.  The definition therefore contains only the inference scale and the
quantum/relativistic conversion constants. -/
noncomputable def inferenceEinsteinCoupling (ħ c σ₀ : ℝ) : ℝ :=
  8 * Real.pi * ħ * σ₀ ^ 4 / c ^ 3

/-- The `G`-free coupling is algebraically the conventional Einstein coupling after replacing
`G` by the independently inferred value `ℏcσ₀⁴`.  This lemma is a unit-normalization bridge;
the independent content is the Compton-cell derivation below. -/
theorem inferenceEinsteinCoupling_eq_newtonForm (ħ c σ₀ : ℝ) (hc : c ≠ 0) :
    inferenceEinsteinCoupling ħ c σ₀ =
      8 * Real.pi * (ħ * c * σ₀ ^ 4) / c ^ 4 := by
  unfold inferenceEinsteinCoupling
  field_simp

/-- **[The Einstein coupling from a `G`-free bit count].** At any finite positive rapidity,
the entanglement screen tiled by Compton cells determines

`κ(σ₀) = 8πℏσ₀⁴/c³ = 8π (area / comptonCellBits)/(ℏc)`.

Neither side contains Newton's constant, and the count on the right was defined without it.
This is the finite-rapidity ratio; it deliberately does not substitute the simultaneous
reversible limits `area → 0` and `bits → 0`. -/
@[zil_level physical_theorem]
theorem inferenceEinsteinCoupling_eq_comptonCellBitForm
    (c ħ σ₀ η : ℝ) (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη : 0 < η) :
    inferenceEinsteinCoupling ħ c σ₀ =
      8 * Real.pi *
          (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) /
            comptonCellBits (inferenceMass σ₀) c ħ η) / (ħ * c) := by
  have hm : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]
    exact inv_ne_zero (pow_ne_zero 2 hσ.ne')
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hN : comptonCellBits (inferenceMass σ₀) c ħ η ≠ 0 := by
    rw [comptonCellBits_eq (inferenceMass σ₀) c ħ η hm hc.ne' hħ.ne']
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 2 hlog)
  have hG := newtonG_from_positionVariance σ₀ c ħ η hσ.ne' hc.ne' hħ.ne' hlog
  unfold inferenceEinsteinCoupling
  field_simp [hN, hħ.ne', hc.ne'] at hG ⊢
  nlinarith

/-! ## The inferred coupling on continuum Schrödinger–Poisson matter -/

/-- The Newtonian convolution potential weighted by the independently inferred coupling
`G(σ₀) = ℏcσ₀⁴`. The definition does not accept Newton's constant as an input. It retains the
positive-kernel convention of `newtonianConvolutionPotential`; a physical negative-potential sign,
when desired, belongs to the selected Schrödinger–Poisson equation convention. -/
noncomputable def inferenceNewtonianConvolutionPotential
    (ħ c σ₀ : ℝ) (ρ : Space 3 → ℝ) (x : Space 3) : ℝ :=
  (ħ * c * σ₀ ^ 4) * newtonianConvolutionPotential ρ x

/-- **[The inferred gravitational potential is a genuine continuum convolution]**
The `G`-free coefficient `ℏcσ₀⁴` can equivalently be placed in the source density, after which the
existing Newtonian-potential theorem identifies the result with Mathlib's Bochner convolution. -/
@[zil_level physical_theorem]
theorem inferenceNewtonianConvolutionPotential_eq_convolution
    (ħ c σ₀ : ℝ) (ρ : Space 3 → ℝ) (x : Space 3) :
    inferenceNewtonianConvolutionPotential ħ c σ₀ ρ x =
      (newtonKernel3 ⋆ ((ħ * c * σ₀ ^ 4) • ρ)) x := by
  rw [inferenceNewtonianConvolutionPotential]
  calc
    (ħ * c * σ₀ ^ 4) * newtonianConvolutionPotential ρ x =
        newtonianConvolutionPotential ((ħ * c * σ₀ ^ 4) • ρ) x := by
          symm
          simpa [smul_eq_mul] using
            newtonianConvolutionPotential_smul (ħ * c * σ₀ ^ 4) ρ x
    _ = (newtonKernel3 ⋆ ((ħ * c * σ₀ ^ 4) • ρ)) x :=
      newtonianConvolutionPotential_eq_convolution _ _

/-- The Schrödinger–Poisson gravitational energy with the inferred coupling `ℏcσ₀⁴`.
This is the continuum double-integral matter functional associated with the same parameter that
fixes `inferenceEinsteinCoupling`; it is not a finite-source or point-mass surrogate. -/
noncomputable def inferenceSchrodingerPoissonGravitationalEnergy
    (ħ c σ₀ : ℝ) (ρ : Space 3 → ℝ) : ℝ :=
  (ħ * c * σ₀ ^ 4) * schrodingerPoissonGravitationalEnergy ρ

/-- **[The inferred Schrödinger–Poisson energy is the coupled Newton double integral]**
`E_G[ρ] = (ℏcσ₀⁴/4) ∬ ρ(x)ρ(y)/‖x-y‖`. -/
@[zil_level physical_theorem]
theorem inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral
    (ħ c σ₀ : ℝ) (ρ : Space 3 → ℝ) :
    inferenceSchrodingerPoissonGravitationalEnergy ħ c σ₀ ρ =
      (ħ * c * σ₀ ^ 4 / 4) *
        ∫ x, ∫ y, ρ x * ρ y / ‖x - y‖ := by
  rw [inferenceSchrodingerPoissonGravitationalEnergy,
    schrodingerPoissonGravitationalEnergy_eq_doubleIntegral]
  ring

/-- **[`G`-free continuum Poisson implies the weak-field Einstein `00` equation]**
If the distributional continuum potential satisfies
`ΔΦ = 4π(ℏcσ₀⁴)ρ`, the existing Einstein–Poisson equivalence gives the distributional static
linearized Einstein equation at the inferred coupling. There is no Newton-constant parameter.

The Poisson law remains an explicit premise only on this older real Physlib-distribution carrier.
The complex tempered continuum carrier below now proves and discharges the corresponding premise. -/
@[zil_level physical_theorem]
theorem gFree_distributionalWeakFieldEinstein00_of_poisson
    (ħ c σ₀ : ℝ) (Φ ρ : (Space 3) →d[ℝ] ℝ) (hc : c ≠ 0)
    (hPoisson : Δᵈ Φ = (4 * Real.pi * (ħ * c * σ₀ ^ 4)) • ρ) :
    DistributionalWeakFieldEinstein00Equation3 (ħ * c * σ₀ ^ 4) c Φ ρ :=
  distributionalWeakFieldEinstein00Equation3_of_poisson
    (ħ * c * σ₀ ^ 4) c Φ ρ hc hPoisson

/-! ## The inferred continuum Poisson law closes the tempered weak-field equation -/

/-- The static weak-field Einstein `00` equation on complex tempered distributions. It is the
complex-tempered continuation of `DistributionalWeakFieldEinstein00Equation3`, with
`G₀₀^(1) = (2/c²)ΔΦ` and `T₀₀ = c²ρ`. -/
def TemperedWeakFieldEinstein00Equation3
    (G c : ℝ) (Φ ρ : 𝓢'(Space 3, ℂ)) : Prop :=
  ((2 / c ^ 2 : ℝ) : ℂ) • Δ Φ =
    ((8 * Real.pi * G / c ^ 4 : ℝ) : ℂ) •
      (((c ^ 2 : ℝ) : ℂ) • ρ)

/-- Complex-tempered Poisson implies the static linearized Einstein `00` equation. -/
@[zil_level physical_theorem]
theorem temperedWeakFieldEinstein00Equation3_of_poisson
    (G c : ℝ) (Φ ρ : 𝓢'(Space 3, ℂ)) (hc : c ≠ 0)
    (hPoisson : Δ Φ = ((4 * Real.pi * G : ℝ) : ℂ) • ρ) :
    TemperedWeakFieldEinstein00Equation3 G c Φ ρ := by
  rw [TemperedWeakFieldEinstein00Equation3, hPoisson]
  simp only [smul_smul]
  congr 1
  push_cast
  field_simp [hc]
  ring

/-- **[The inferred continuum potential satisfies weak-field Einstein without a Poisson premise]**
The scalar-extended `1/‖x‖` fundamental solution and genuine tempered convolution prove the
Poisson equation, so the weak-field Einstein `00` equation follows directly with
`G = ℏcσ₀⁴`; Newton's constant is not a theorem input. -/
@[zil_level physical_theorem]
theorem inferenceNewtonTemperedPotential_weakFieldEinstein00
    (ħ c σ₀ : ℝ) (f : 𝓢(Space 3, ℂ)) (hc : c ≠ 0) :
    TemperedWeakFieldEinstein00Equation3
      (ħ * c * σ₀ ^ 4) c
      (inferenceNewtonTemperedPotential ħ c σ₀ f)
      (temperedConvolutionSchwartz (TemperedDistribution.delta 0) f) := by
  apply temperedWeakFieldEinstein00Equation3_of_poisson _ _ _ _ hc
  convert inferenceNewtonTemperedPotential_laplacian ħ c σ₀ f using 1
  · push_cast
    rfl

set_option maxHeartbeats 800000 in
/-- **[Explicit continuum source action]** Evaluating the inferred Poisson equation on any
Schwartz test function gives exactly
`(ΔΦ)(η) = 4πℏcσ₀⁴ ∫ x, f(x)η(x)`. -/
@[zil_level physical_theorem]
theorem inferenceNewtonTemperedPotential_source_action
    (ħ c σ₀ : ℝ) (f η : 𝓢(Space 3, ℂ)) :
    (Δ (inferenceNewtonTemperedPotential ħ c σ₀ f)) η =
      (4 * Real.pi * (ħ * c * σ₀ ^ 4) : ℂ) *
        ∫ x, f x * η x := by
  rw [inferenceNewtonTemperedPotential_laplacian]
  change
    (4 * Real.pi * (ħ * c * σ₀ ^ 4) : ℂ) *
      temperedConvolutionSchwartz (TemperedDistribution.delta 0) f η =
        _
  rw [delta_temperedConvolutionSchwartz_apply]

/-- The `G = ℏcσ₀⁴` Newton source on the continuum homogeneous energy dual.
The coefficient is applied to the already-proved charted Schwartz
`Ḣ⁻¹` source; no primitive Newton constant or additional regularity witness is
introduced. -/
noncomputable def inferenceNewtonSchwartzDotHMinusOneThree
    (ħ c σ₀ : ℝ) (f : 𝓢(Space 3, ℂ)) :
    FourierDotHMinusOneThree :=
  (-(ħ * c * σ₀ ^ 4) : ℂ) • newtonSchwartzDotHMinusOneThree f

/-- **[`G`-free weak-field Einstein plus energy well-posedness.]**
For every Schwartz density, the same inferred coupling gives the complex
tempered weak-field Einstein equation and a unique zero-boundary continuum
`Ḣ¹` weak Newton solution.  This closes the former abstract source-regularity
and boundary-uniqueness premises; full inhomogeneous `H¹` still obeys the
separate infrared `L²` criterion. -/
@[zil_level physical_theorem]
theorem inferenceNewtonTemperedPotential_einstein00_and_energy_unique
    (ħ c σ₀ : ℝ) (f : 𝓢(Space 3, ℂ)) (hc : c ≠ 0) :
    TemperedWeakFieldEinstein00Equation3
        (ħ * c * σ₀ ^ 4) c
        (inferenceNewtonTemperedPotential ħ c σ₀ f)
        (temperedConvolutionSchwartz (TemperedDistribution.delta 0) f) ∧
      ∃! energyDerivative : FourierDotHOneThree,
        IsFourierDotHOneWeakSolution
          (inferenceNewtonSchwartzDotHMinusOneThree ħ c σ₀ f)
          energyDerivative := by
  exact ⟨inferenceNewtonTemperedPotential_weakFieldEinstein00 ħ c σ₀ f hc,
    existsUnique_fourierDotHOneWeakSolution
      (inferenceNewtonSchwartzDotHMinusOneThree ħ c σ₀ f)⟩

/-- The rapidity-dependent entropic source used by the reversible complex-Einstein family:
`S(η) = log(K(η)) S₀`.  It is the tensor analogue of the file's existing
`H_I(η) = log(K(η)) H_I⁰` interpolation. -/
noncomputable def rapidityEntropicStress {ι : Type*}
    (S₀ : Matrix ι ι ℝ) (η : ℝ) : Matrix ι ι ℝ :=
  Real.log (schmidtNumber η) • S₀

/-- The rapidity-scaled entropic stress tends to zero in the product topology on matrices. -/
theorem rapidityEntropicStress_tendsto_zero {ι : Type*} (S₀ : Matrix ι ι ℝ) :
    Tendsto (fun η : ℝ => rapidityEntropicStress S₀ η) atTop (𝓝 0) := by
  simpa [rapidityEntropicStress] using log_schmidtNumber_tendsto_zero.smul_const S₀

/-- Complexifying a fixed real tensor by a real tensor tending to zero converges, in the
matrix product topology, to the purely real complexification.  This reusable continuity
lemma avoids repeating entrywise complex arithmetic for the geometric and source sides. -/
theorem complexCombine_tendsto_right_zero {ι : Type*}
    (A : Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun η => complexCombine A (B η)) atTop (𝓝 (complexCombine A 0)) := by
  refine tendsto_pi_nhds.mpr fun μ => tendsto_pi_nhds.mpr fun ν => ?_
  have hBμν : Tendsto (fun η => B η μ ν) atTop (𝓝 0) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hB μ) ν
  simpa [complexCombine] using
    (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (Tendsto.ofReal hBμν)) :
        Tendsto
          (fun η => (A μ ν : ℂ) + Complex.I * (B η μ ν : ℂ))
          atTop (𝓝 ((A μ ν : ℂ) + Complex.I * (0 : ℂ))))

/-- **[Full geometric reversible limit].** At the inference coupling, the complete
complex Einstein tensor `G + iΛ(η)` converges entrywise to `G + i0`, not only
`Λ(η) → 0`. -/
@[zil_level physical_theorem]
theorem gFree_complexEinsteinTensor_tendsto_real {ι : Type*}
    (G S₀ : Matrix ι ι ℝ) (ħ c σ₀ : ℝ) :
    Tendsto
      (fun η : ℝ => complexEinsteinTensor G
        (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η))
      atTop (𝓝 (complexEinsteinTensor G 0)) := by
  apply complexCombine_tendsto_right_zero
  simpa using (tendsto_const_nhds.smul
    (rapidityEntropicStress_tendsto_zero S₀) : Tendsto
      (fun η : ℝ =>
        inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
      atTop (𝓝 (inferenceEinsteinCoupling ħ c σ₀ • (0 : Matrix ι ι ℝ))))

/-- **[Full source reversible limit].** The complex source
`T + i log(K(η))S₀` converges entrywise to the ordinary real stress-energy `T + i0`. -/
@[zil_level physical_theorem]
theorem rapidityComplexStressEnergy_tendsto_real {ι : Type*}
    (T S₀ : Matrix ι ι ℝ) :
    Tendsto
      (fun η : ℝ => complexStressEnergy T (rapidityEntropicStress S₀ η))
      atTop (𝓝 (complexStressEnergy T 0)) := by
  exact complexCombine_tendsto_right_zero T
    (fun η => rapidityEntropicStress S₀ η)
    (rapidityEntropicStress_tendsto_zero S₀)

/-- **[Complex Einstein equations with no assumed Newton constant].** Fix the real Einstein
sector at the coupling independently determined by the inference variance,
`κ(σ₀) = 8πℏσ₀⁴/c³`.  For every rapidity, set

`S(η) = log(K(η)) S₀`, `Λ(η) = κ(σ₀) S(η)`.

Then the full complex equation
`𝒢 = κ(σ₀) (T + iS(η))` holds at every `η`, and its imaginary curvature tends to
zero as `η → ∞`.  At any finite positive reference rapidity `η₀`, the same coupling
is exactly the independent Compton-cell area-per-bit coupling.

The only dynamical premise is the real Einstein source equation at `κ(σ₀)`; `G` is
neither a parameter nor a hypothesis.  This derives the complex extension and its
reversible reduction, not the measured numerical value of the inference scale `σ₀`. -/
@[zil_level physical_theorem]
theorem gFree_complexEinstein_reversibleFamily {ι : Type*}
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T S₀ : Matrix ι ι ℝ)
    (c ħ σ₀ η₀ : ℝ) (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ) (hη₀ : 0 < η₀)
    (hReal : einsteinFieldEquation Ric scalarR g T
      (inferenceEinsteinCoupling ħ c σ₀)) :
    inferenceEinsteinCoupling ħ c σ₀ =
        8 * Real.pi *
          (sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η₀) /
            comptonCellBits (inferenceMass σ₀) c ħ η₀) / (ħ * c)
      ∧ (∀ η : ℝ,
        complexEinsteinFieldEquation (einsteinTensor Ric scalarR g)
          (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
          T (rapidityEntropicStress S₀ η) (inferenceEinsteinCoupling ħ c σ₀))
      ∧ Tendsto
        (fun η : ℝ =>
          inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
        atTop (𝓝 0) := by
  refine ⟨inferenceEinsteinCoupling_eq_comptonCellBitForm
      c ħ σ₀ η₀ hσ hc hħ hη₀, ?_, ?_⟩
  · intro η
    exact (complexEinsteinFieldEquation_iff_einstein
      Ric scalarR g
      (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
      T (rapidityEntropicStress S₀ η)
      (inferenceEinsteinCoupling ħ c σ₀)).2 ⟨hReal, rfl⟩
  · simpa using (tendsto_const_nhds.smul
      (rapidityEntropicStress_tendsto_zero S₀) : Tendsto
        (fun η : ℝ =>
          inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
        atTop (𝓝 (inferenceEinsteinCoupling ħ c σ₀ • (0 : Matrix ι ι ℝ))))

/-- **[The `G`-free complex Einstein family is Bianchi-consistent].** Suppose the
real Einstein tensor obeys the contracted Bianchi identity and the reference entropic
stress is divergence-free.  Then at every rapidity:

* the complex Einstein equation holds at `κ(σ₀) = 8πℏσ₀⁴/c³`;
* the full complex Einstein tensor obeys the complex Bianchi identity;
* ordinary stress-energy and the rapidity-scaled entropic stress are both conserved.

No Newton constant is an input.  The real Einstein equation, real Bianchi identity,
and conservation of the reference entropic stress remain explicit geometric/dynamical
premises; this theorem does not rename them as thermodynamic derivations. -/
@[zil_level physical_theorem]
theorem gFree_complexEinstein_conservationFamily {ι : Type*}
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T S₀ : Matrix ι ι ℝ)
    (c ħ σ₀ : ℝ) (hσ : 0 < σ₀) (hc : 0 < c) (hħ : 0 < ħ)
    (hReal : einsteinFieldEquation Ric scalarR g T
      (inferenceEinsteinCoupling ħ c σ₀))
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hS₀ : Div S₀ = 0) :
    ∀ η : ℝ,
      complexEinsteinFieldEquation (einsteinTensor Ric scalarR g)
          (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
          T (rapidityEntropicStress S₀ η) (inferenceEinsteinCoupling ħ c σ₀)
      ∧ complexDiv Div
          (complexEinsteinTensor (einsteinTensor Ric scalarR g)
            (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)) = 0
      ∧ Div T = 0
      ∧ Div (rapidityEntropicStress S₀ η) = 0 := by
  have hκpos : 0 < inferenceEinsteinCoupling ħ c σ₀ := by
    unfold inferenceEinsteinCoupling
    positivity
  have hT : Div T = 0 :=
    bianchi_implies_conservation Div Ric scalarR g T
      (inferenceEinsteinCoupling ħ c σ₀) hReal hBianchi hκpos.ne'
  intro η
  have hSη : Div (rapidityEntropicStress S₀ η) = 0 := by
    simp [rapidityEntropicStress, hS₀]
  have hΛη :
      Div (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η) = 0 := by
    simp [hSη]
  have hEFE :=
    (complexEinsteinFieldEquation_iff_einstein Ric scalarR g
      (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)
      T (rapidityEntropicStress S₀ η)
      (inferenceEinsteinCoupling ħ c σ₀)).2 ⟨hReal, rfl⟩
  have hComplexBianchi :=
    (complexBianchi_iff Div (einsteinTensor Ric scalarR g)
      (inferenceEinsteinCoupling ħ c σ₀ • rapidityEntropicStress S₀ η)).2
      ⟨hBianchi, hΛη⟩
  exact ⟨hEFE, hComplexBianchi, hT, hSη⟩

/-- **[The path-integral weight tends to `1` in the reversible limit]** `exp(−S_I/ℏ) → 1` as `η → ∞` —
the entropic suppression of the complex-action weight is removed analytically, recovering the unsuppressed
reversible amplitude. -/
theorem suppression_tendsto_one (ħ : ℝ) :
    Tendsto (fun η : ℝ => Real.exp (-(entropicAction ħ η / ħ))) atTop (𝓝 1) := by
  have hz : Tendsto (fun η : ℝ => -(entropicAction ħ η / ħ)) atTop (𝓝 0) := by
    have h : Tendsto (fun η : ℝ => entropicAction ħ η / ħ) atTop (𝓝 (0 / ħ)) :=
      (entropicAction_tendsto_zero ħ).div_const ħ
    rw [zero_div] at h
    simpa using h.neg
  have hexp := (Real.continuous_exp.tendsto 0).comp hz
  rwa [Real.exp_zero] at hexp

/-- **[The master complex-action weight recovers the reversible phase]** For fixed real action `S_R`,
the scalar master weight converges in `ℂ` to `exp((S_R/ℏ)i)` as the imaginary entropic action
vanishes. This is pointwise scalar convergence, not convergence of a path integral or its measure. -/
@[zil_level physical_theorem]
theorem complexActionPathIntegralWeight_tendsto_phase (S_R ħ : ℝ) :
    Tendsto
      (fun η : ℝ => complexActionPathIntegralWeight S_R (entropicAction ħ η) ħ)
      atTop (𝓝 (Complex.exp ((S_R / ħ : ℂ) * Complex.I))) := by
  have hd : Tendsto
      (fun η : ℝ => ((Real.exp (-(entropicAction ħ η / ħ)) : ℝ) : ℂ))
      atTop (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp (suppression_tendsto_one ħ)
  have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => Complex.exp ((S_R / ħ : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp ((S_R / ħ : ℂ) * Complex.I)))).mul hd
  simpa only [complexActionPathIntegralWeight_eq_lorentzianKernel,
    lorentzianKernel_factorizes, mul_one] using h

/-- **[The Nagao–Nielsen weight has the same reversible limit]** The existing complex-action weight
`exp(i(S_R+iS_I)/ℏ)` converges in `ℂ` to its unit-modulus phase when the entropic action tends to zero.
Together with `complexActionPathIntegralWeight_tendsto_phase`, this gives analytic rather than merely
definitional recovery of their common reversible sector. -/
@[zil_level physical_theorem]
theorem nnPathWeight_tendsto_phase (S_R ħ : ℝ) :
    Tendsto (fun η : ℝ => nnPathWeight S_R (entropicAction ħ η) ħ) atTop
      (𝓝 (Complex.exp (Complex.I * (S_R : ℂ) / (ħ : ℂ)))) := by
  have hd : Tendsto
      (fun η : ℝ => ((Real.exp (-(entropicAction ħ η / ħ)) : ℝ) : ℂ))
      atTop (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp (suppression_tendsto_one ħ)
  have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => Complex.exp (Complex.I * (S_R : ℂ) / (ħ : ℂ))) atTop
      (𝓝 (Complex.exp (Complex.I * (S_R : ℂ) / (ħ : ℂ))))).mul hd
  simpa only [nnPathWeight_eq_phase_mul_damping, mul_one] using h

/-! ## Operator-norm recovery on the continuum Hilbert carrier -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rapidity interpolation of a reference irreversible generator used by the analytic recovery:
`H_I(η) = log(K(η)) • H_I⁰`. The coefficient is dimensionless and tends to zero as `η → ∞`.

This is an explicit model datum, not a claim that every physical irreversible generator must depend on
rapidity in this way. -/
noncomputable def entropicIrreversibleGenerator (H_I : H →L[ℂ] H) (η : ℝ) : H →L[ℂ] H :=
  Real.log (schmidtNumber η) • H_I

omit [CompleteSpace H] in
/-- **[Quantitative irreversible-generator recovery]** Beyond `η = log 2 / 2`, the operator norm
of the rapidity-scaled irreversible generator is bounded by
`4 exp(-2η) ‖H_I⁰‖`. This is a finite-rapidity error certificate, not only a limit theorem. -/
@[zil_level physical_theorem]
theorem entropicIrreversibleGenerator_norm_le_exp_rate
    (H_I : H →L[ℂ] H) (η : ℝ) (hη : Real.log 2 / 2 ≤ η) :
    ‖entropicIrreversibleGenerator H_I η‖ ≤
      4 * Real.exp (-(2 * η)) * ‖H_I‖ := by
  have hlog := log_schmidtNumber_le_exp_rate η hη
  rw [entropicIrreversibleGenerator, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hlog.1]
  exact mul_le_mul_of_nonneg_right hlog.2 (norm_nonneg H_I)

omit [CompleteSpace H] in
/-- **[The irreversible operator vanishes in operator norm]** On any complex Hilbert space,
`log(K(η)) • H_I⁰ → 0` in the norm topology of continuous linear operators. No finite-dimensional
hypothesis is used. -/
@[zil_level physical_theorem]
theorem entropicIrreversibleGenerator_tendsto_zero (H_I : H →L[ℂ] H) :
    Tendsto (fun η : ℝ => entropicIrreversibleGenerator H_I η) atTop (𝓝 0) := by
  simpa [entropicIrreversibleGenerator] using log_schmidtNumber_tendsto_zero.smul_const H_I

omit [CompleteSpace H] in
/-- **[The complex Hamiltonian converges to the reversible Hamiltonian]** For the explicit
`log K` interpolation of the irreversible sector,
`H_C(η) = H_R - i log(K(η)) H_I⁰ → H_R` in operator norm. -/
@[zil_level physical_theorem]
theorem entropicComplexHamiltonian_tendsto_reversible (H_R H_I : H →L[ℂ] H) :
    Tendsto
      (fun η : ℝ => complexHamiltonian H_R (entropicIrreversibleGenerator H_I η))
      atTop (𝓝 H_R) := by
  have hI := entropicIrreversibleGenerator_tendsto_zero H_I
  have hsmul : Tendsto
      (fun η : ℝ => Complex.I • entropicIrreversibleGenerator H_I η) atTop
      (𝓝 (Complex.I • (0 : H →L[ℂ] H))) :=
    (tendsto_const_nhds (x := Complex.I)).smul hI
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => H_R) atTop (𝓝 H_R)).sub hsmul
  simpa [complexHamiltonian] using h

omit [CompleteSpace H] in
/-- **[Quantitative complex-Hamiltonian recovery]** The full non-Hermitian Hamiltonian differs from
its reversible part by at most `4 exp(-2η) ‖H_I⁰‖` in operator norm. Multiplication by `-i` preserves
the irreversible operator norm exactly. -/
@[zil_level physical_theorem]
theorem entropicComplexHamiltonian_error_le_exp_rate
    (H_R H_I : H →L[ℂ] H) (η : ℝ) (hη : Real.log 2 / 2 ≤ η) :
    ‖complexHamiltonian H_R (entropicIrreversibleGenerator H_I η) - H_R‖ ≤
      4 * Real.exp (-(2 * η)) * ‖H_I‖ := by
  calc
    _ = ‖entropicIrreversibleGenerator H_I η‖ := by
      rw [complexHamiltonian]
      simp [norm_smul]
    _ ≤ _ := entropicIrreversibleGenerator_norm_le_exp_rate H_I η hη

omit [CompleteSpace H] in
/-- **[The non-Hermitian Schrödinger generator converges in operator norm]** Multiplication by the fixed
coefficient `-i/ℏ` preserves the operator-norm convergence `H_C(η) → H_R`. -/
@[zil_level physical_theorem]
theorem entropicSchrodingerGenerator_tendsto_reversible
    (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    Tendsto
      (fun η : ℝ => schrodingerGenerator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ)
      atTop (𝓝 (schrodingerGenerator H_R ħ)) := by
  have h : Tendsto
      (fun η : ℝ => (-Complex.I / (ħ : ℂ)) •
        complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) atTop
      (𝓝 ((-Complex.I / (ħ : ℂ)) • H_R)) :=
    (tendsto_const_nhds (x := -Complex.I / (ħ : ℂ))).smul
      (entropicComplexHamiltonian_tendsto_reversible H_R H_I)
  simpa [schrodingerGenerator] using h

omit [CompleteSpace H] in
/-- **[Quantitative Schrödinger-generator recovery]** The generator error is bounded by
`4 exp(-2η) ‖H_I⁰‖ / |ℏ|`. The theorem is algebraically valid for all `ℏ`; its physical reading as
an inverse-Planck scale assumes the usual `ℏ ≠ 0`. -/
@[zil_level physical_theorem]
theorem entropicSchrodingerGenerator_error_le_exp_rate
    (H_R H_I : H →L[ℂ] H) (ħ η : ℝ) (hη : Real.log 2 / 2 ≤ η) :
    ‖schrodingerGenerator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ -
      schrodingerGenerator H_R ħ‖ ≤
      (4 * Real.exp (-(2 * η)) * ‖H_I‖) / |ħ| := by
  calc
    _ = ‖(-Complex.I / (ħ : ℂ))‖ *
        ‖complexHamiltonian H_R (entropicIrreversibleGenerator H_I η) - H_R‖ := by
      rw [schrodingerGenerator, schrodingerGenerator, ← smul_sub, norm_smul]
    _ ≤ ‖(-Complex.I / (ħ : ℂ))‖ *
        (4 * Real.exp (-(2 * η)) * ‖H_I‖) :=
      mul_le_mul_of_nonneg_left
        (entropicComplexHamiltonian_error_le_exp_rate H_R H_I η hη) (norm_nonneg _)
    _ = (4 * Real.exp (-(2 * η)) * ‖H_I‖) / |ħ| := by
      rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      ring

/-- **[The genuine propagator converges in operator norm]** At every fixed time `t`, continuity of the
Banach-algebra exponential upgrades generator convergence to
`exp(tG_η) → exp(tG_R)` in the operator norm. This is the operator-level reversible limit previously
missing from the frozen-sector theorem. Uniform convergence on bounded time intervals is promoted below;
neither result asserts path-measure convergence. -/
@[zil_level physical_theorem]
theorem entropicPropagator_tendsto_reversible
    (H_R H_I : H →L[ℂ] H) (ħ t : ℝ) :
    Tendsto
      (fun η : ℝ => propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t)
      atTop (𝓝 (propagator H_R ħ t)) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hg := entropicSchrodingerGenerator_tendsto_reversible H_R H_I ħ
  have htg := (tendsto_const_nhds : Tendsto (fun _ : ℝ => t) atTop (𝓝 t)).smul hg
  simpa [propagator] using htg.exp

/-- **[Strong state recovery]** Operator-norm convergence of the rapidity-dependent propagators implies
strong convergence on every fixed Hilbert-space state. This remains valid on arbitrary complete complex
Hilbert spaces and is not restricted to a finite matrix carrier. -/
@[zil_level physical_theorem]
theorem entropicPropagator_apply_tendsto_reversible
    (H_R H_I : H →L[ℂ] H) (ħ t : ℝ) (ψ : H) :
    Tendsto
      (fun η : ℝ => propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ)
      atTop (𝓝 (propagator H_R ħ t ψ)) := by
  exact ((continuous_id.clm_apply continuous_const).continuousAt.tendsto).comp
    (entropicPropagator_tendsto_reversible H_R H_I ħ t)

/-- Joint continuity of the propagator in a real irreversible coefficient and a continuous time
carrier. This is the common analytic engine for compact-uniform operator and readout convergence;
factoring it here avoids rebuilding the Banach-algebra exponential argument for each observable. -/
theorem continuous_propagator_coefficient_time
    {τ : Type*} [TopologicalSpace τ]
    (time : τ → ℝ) (htime : Continuous time)
    (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    Continuous (fun p : ℝ × τ => propagator
      (complexHamiltonian H_R (p.1 • H_I)) ħ (time p.2)) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  change Continuous (fun p : ℝ × τ => NormedSpace.exp ((time p.2) •
    ((-Complex.I / (ħ : ℂ)) • (H_R - Complex.I • (p.1 • H_I)))))
  have hI : Continuous (fun p : ℝ × τ => p.1 • H_I) :=
    continuous_fst.smul (continuous_const : Continuous fun _ : ℝ × τ => H_I)
  have hIH : Continuous (fun p : ℝ × τ =>
      H_R - Complex.I • (p.1 • H_I)) :=
    continuous_const.sub
      ((continuous_const : Continuous fun _ : ℝ × τ => Complex.I).smul hI)
  have hG : Continuous (fun p : ℝ × τ =>
      (-Complex.I / (ħ : ℂ)) • (H_R - Complex.I • (p.1 • H_I))) :=
    (continuous_const : Continuous fun _ : ℝ × τ => -Complex.I / (ħ : ℂ)).smul hIH
  have ht : Continuous (fun p : ℝ × τ => time p.2) :=
    htime.comp continuous_snd
  exact NormedSpace.exp_continuous.comp (ht.smul hG)

/-- **[Uniform operator recovery on every compact time carrier]** If a compact parameter space maps
continuously into physical time, then the rapidity-dependent propagator converges uniformly in operator
norm over that entire carrier. The proof applies compact-uniform continuity to the scalar `log K`
interpolation; the operator space itself need not be locally compact or finite-dimensional. -/
@[zil_level physical_theorem]
theorem entropicPropagator_tendstoUniformly_compactTime
    {τ : Type*} [UniformSpace τ] [CompactSpace τ]
    (time : τ → ℝ) (htime : Continuous time)
    (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    TendstoUniformly
      (fun η x => propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ (time x))
      (fun x => propagator H_R ħ (time x)) atTop := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  let F : ℝ → τ → (H →L[ℂ] H) := fun r x =>
    propagator (complexHamiltonian H_R (r • H_I)) ħ (time x)
  have hF : Continuous ↿F :=
    continuous_propagator_coefficient_time time htime H_R H_I ħ
  have hu : TendstoUniformly F (F 0) (𝓝 0) :=
    Continuous.tendstoUniformly F hF 0
  have hzero : complexHamiltonian H_R (0 : H →L[ℂ] H) = H_R := by
    simp [complexHamiltonian]
  intro u hu_mem
  simpa [F, entropicIrreversibleGenerator, hzero] using
    log_schmidtNumber_tendsto_zero (hu u hu_mem)

/-- **[Uniform operator recovery on bounded time intervals]** For every `T`, the non-Hermitian
propagator converges to the reversible propagator uniformly in operator norm for `t ∈ [-T,T]`.
This closes the bounded-time uniformity gap while making no global all-time uniform claim. -/
@[zil_level physical_theorem]
theorem entropicPropagator_tendstoUniformlyOn_boundedInterval
    (T : ℝ) (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    TendstoUniformlyOn
      (fun η t => propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t)
      (fun t => propagator H_R ħ t) atTop (Set.Icc (-T) T) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact entropicPropagator_tendstoUniformly_compactTime
    (fun t : Set.Icc (-T) T => (t : ℝ)) continuous_subtype_val H_R H_I ħ

/-- **[Uniform strong recovery on bounded time intervals]** Applying the uniformly convergent
operator family to a fixed state preserves uniform convergence on `[-T,T]`. This is a continuum
Hilbert-space statement, not a finite-mode surrogate. -/
@[zil_level physical_theorem]
theorem entropicPropagator_apply_tendstoUniformlyOn_boundedInterval
    (T : ℝ) (H_R H_I : H →L[ℂ] H) (ħ : ℝ) (ψ : H) :
    TendstoUniformlyOn
      (fun η t => propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ)
      (fun t => propagator H_R ħ t ψ) atTop (Set.Icc (-T) T) := by
  exact (ContinuousLinearMap.apply ℂ H ψ).uniformContinuous.comp_tendstoUniformlyOn
    (entropicPropagator_tendstoUniformlyOn_boundedInterval T H_R H_I ħ)

/-! ## Uniform recovery of amplitudes, observables, and Born weights -/

/-- **[Every continuous readout recovers uniformly on compact time carriers]** A continuous scalar,
vector, or other uniform-space-valued readout of the propagator inherits compact-time uniform
convergence. This is the reusable measurement-facing consequence of the joint propagator continuity;
no finite-dimensional hypothesis is introduced. -/
theorem entropicPropagator_readout_tendstoUniformly_compactTime
    {τ Y : Type*} [UniformSpace τ] [CompactSpace τ] [UniformSpace Y]
    (time : τ → ℝ) (htime : Continuous time)
    (readout : (H →L[ℂ] H) → Y) (hreadout : Continuous readout)
    (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    TendstoUniformly
      (fun η x => readout (propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ (time x)))
      (fun x => readout (propagator H_R ħ (time x))) atTop := by
  let F : ℝ → τ → Y := fun r x =>
    readout (propagator (complexHamiltonian H_R (r • H_I)) ħ (time x))
  have hF : Continuous ↿F := hreadout.comp
    (continuous_propagator_coefficient_time time htime H_R H_I ħ)
  have hu : TendstoUniformly F (F 0) (𝓝 0) :=
    Continuous.tendstoUniformly F hF 0
  have hzero : complexHamiltonian H_R (0 : H →L[ℂ] H) = H_R := by
    simp [complexHamiltonian]
  intro u hu_mem
  simpa [F, entropicIrreversibleGenerator, hzero] using
    log_schmidtNumber_tendsto_zero (hu u hu_mem)

/-- Continuous readouts converge uniformly over every bounded closed real-time interval. -/
theorem entropicPropagator_readout_tendstoUniformlyOn_boundedInterval
    {Y : Type*} [UniformSpace Y]
    (T : ℝ) (readout : (H →L[ℂ] H) → Y) (hreadout : Continuous readout)
    (H_R H_I : H →L[ℂ] H) (ħ : ℝ) :
    TendstoUniformlyOn
      (fun η t => readout (propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t))
      (fun t => readout (propagator H_R ħ t)) atTop (Set.Icc (-T) T) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact entropicPropagator_readout_tendstoUniformly_compactTime
    (fun t : Set.Icc (-T) T => (t : ℝ)) continuous_subtype_val
    readout hreadout H_R H_I ħ

/-- **[Uniform transition-amplitude recovery]** Every matrix element
`⟪φ, U_η(t)ψ⟫` converges uniformly on bounded time intervals to its reversible value. -/
@[zil_level physical_theorem]
theorem entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval
    (T : ℝ) (H_R H_I : H →L[ℂ] H) (ħ : ℝ) (φ ψ : H) :
    TendstoUniformlyOn
      (fun η t => inner ℂ φ (propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ))
      (fun t => inner ℂ φ (propagator H_R ħ t ψ)) atTop (Set.Icc (-T) T) := by
  exact entropicPropagator_readout_tendstoUniformlyOn_boundedInterval T
    (fun U => inner ℂ φ (U ψ)) (by fun_prop) H_R H_I ħ

/-- **[Uniform bounded-observable recovery]** The quadratic expectation readout
`⟪U_η(t)ψ, A U_η(t)ψ⟫` of every bounded operator converges uniformly on bounded time intervals.
Self-adjointness of `A` is unnecessary for convergence; it is only needed for a real-valued physical
interpretation of the expectation. -/
@[zil_level physical_theorem]
theorem entropicObservableExpectation_tendstoUniformlyOn_boundedInterval
    (T : ℝ) (H_R H_I A : H →L[ℂ] H) (ħ : ℝ) (ψ : H) :
    TendstoUniformlyOn
      (fun η t => inner ℂ
        (propagator (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ)
        (A (propagator
          (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ)))
      (fun t => inner ℂ (propagator H_R ħ t ψ) (A (propagator H_R ħ t ψ)))
      atTop (Set.Icc (-T) T) := by
  exact entropicPropagator_readout_tendstoUniformlyOn_boundedInterval T
    (fun U => inner ℂ (U ψ) (A (U ψ))) (by fun_prop) H_R H_I ħ

/-- **[Uniform Born-weight recovery]** The squared norm of the evolved state—the total Born
weight—converges uniformly on bounded time intervals to the reversible evolved state's squared norm. -/
@[zil_level physical_theorem]
theorem entropicBornWeight_tendstoUniformlyOn_boundedInterval
    (T : ℝ) (H_R H_I : H →L[ℂ] H) (ħ : ℝ) (ψ : H) :
    TendstoUniformlyOn
      (fun η t => ‖propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ‖ ^ 2)
      (fun t => ‖propagator H_R ħ t ψ‖ ^ 2) atTop (Set.Icc (-T) T) := by
  exact entropicPropagator_readout_tendstoUniformlyOn_boundedInterval T
    (fun U => ‖U ψ‖ ^ 2) (by fun_prop) H_R H_I ħ

/-- **[Uniform normalization recovery in the reversible sector]** If `H_R` is self-adjoint and
`ℏ ≠ 0`, its propagator is unitary on the arbitrary complete complex Hilbert carrier. Consequently
the non-Hermitian evolved Born weight converges uniformly on `[-T,T]` to the initial weight `‖ψ‖²`.
For a normalized input this is exactly uniform recovery of total Born probability one. -/
@[zil_level physical_theorem]
theorem entropicBornWeight_tendstoUniformlyOn_initial
    (T : ℝ) (H_R H_I : H →L[ℂ] H) (ħ : ℝ) (ψ : H)
    (hR : IsSelfAdjoint H_R) (hħ : ħ ≠ 0) :
    TendstoUniformlyOn
      (fun η t => ‖propagator
        (complexHamiltonian H_R (entropicIrreversibleGenerator H_I η)) ħ t ψ‖ ^ 2)
      (fun _ : ℝ => ‖ψ‖ ^ 2) atTop (Set.Icc (-T) T) := by
  have hborn := entropicBornWeight_tendstoUniformlyOn_boundedInterval T H_R H_I ħ ψ
  have hu : ∀ t : ℝ, propagator H_R ħ t ∈ unitary (H →L[ℂ] H) := by
    intro t
    have hskew : schrodingerGenerator H_R ħ ∈ skewAdjoint (H →L[ℂ] H) :=
      (schrodingerGenerator_mem_skewAdjoint_iff_isSelfAdjoint H_R ħ hħ).2 hR
    letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
    unfold propagator
    refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr ?_)
    rw [star_smul, star_trivial, skewAdjoint.mem_iff.mp hskew, smul_neg]
  convert hborn using 1
  funext t
  rw [(propagator H_R ħ t).norm_map_of_mem_unitary (hu t) ψ]

/-! ## Nonlinear complex-Einstein Cauchy evolution on continuum Banach carriers -/

variable {X ι : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Analytic data for the gauge-reduced nonlinear complex Einstein Cauchy
problem at the `G`-free coupling `κ = 8πℏσ₀⁴/c³`.

The phase space `X` is an arbitrary complete real normed space, so it may be a
continuum Sobolev space of metric, extrinsic-curvature, and matter fields.
No linearity is imposed on `vectorField`.  The four tensor maps are the
intrinsic geometric/source realizations.  `fieldEquation_propagates` is the
explicit Bianchi plus ADM-constraint propagation obligation; separating it
from the ODE regularity prevents a finite-dimensional Picard theorem from
being misreported as the full Einstein PDE theorem. -/
structure GFreeNonlinearEinsteinCauchyProblem
    [Fintype ι] [DecidableEq ι]
    (ħ c σ₀ : ℝ) (initialState : X) where
  /-- Gauge-fixed nonlinear ADM/Einstein evolution field. -/
  vectorField : X → X
  /-- Intrinsic real Einstein tensor evaluated at a phase-space state. -/
  realEinsteinTensor : X → Matrix ι ι ℝ
  /-- Imaginary/entropic curvature tensor. -/
  entropicCurvature : X → Matrix ι ι ℝ
  /-- Ordinary stress-energy tensor. -/
  stressEnergy : X → Matrix ι ι ℝ
  /-- Entropic stress tensor. -/
  entropicStress : X → Matrix ι ι ℝ
  /-- A Lipschitz constant for Cauchy uniqueness. -/
  lipschitzConstant : ℝ≥0
  /-- Picard--Lindelöf regularity at the supplied initial state. -/
  vectorField_contDiffAt : ContDiffAt ℝ 1 vectorField initialState
  /-- Lipschitz control of the gauge-reduced evolution field. -/
  vectorField_lipschitz : LipschitzWith lipschitzConstant vectorField
  /-- The complete complex tensor equation holds on the initial slice. -/
  initial_fieldEquation :
    complexEinsteinFieldEquation
      (realEinsteinTensor initialState) (entropicCurvature initialState)
      (stressEnergy initialState) (entropicStress initialState)
      (inferenceEinsteinCoupling ħ c σ₀)
  /-- Bianchi identity plus the Hamiltonian/momentum constraints propagate
  the full complex Einstein tensor equation along every local solution. -/
  fieldEquation_propagates :
    ∀ (trajectory : ℝ → X) (ε : ℝ),
      trajectory 0 = initialState →
      (∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt trajectory (vectorField (trajectory t)) t) →
      ∀ t ∈ Set.Ioo (-ε) ε,
        complexEinsteinFieldEquation
          (realEinsteinTensor (trajectory t)) (entropicCurvature (trajectory t))
          (stressEnergy (trajectory t)) (entropicStress (trajectory t))
          (inferenceEinsteinCoupling ħ c σ₀)

namespace GFreeNonlinearEinsteinCauchyProblem

/-- The full complex tensor Einstein equation at one phase-space state. -/
def FieldEquation
    [Fintype ι] [DecidableEq ι]
    {ħ c σ₀ : ℝ} {initialState : X}
    (D : GFreeNonlinearEinsteinCauchyProblem (X := X) (ι := ι)
      ħ c σ₀ initialState) (state : X) : Prop :=
  complexEinsteinFieldEquation
    (D.realEinsteinTensor state) (D.entropicCurvature state)
    (D.stressEnergy state) (D.entropicStress state)
    (inferenceEinsteinCoupling ħ c σ₀)

/-- **Local nonlinear Einstein evolution.** Picard--Lindelöf constructs a
trajectory of the nonlinear gauge-reduced vector field on an open interval.
The supplied Bianchi/constraint propagation theorem upgrades that trajectory
to a solution of the full complex tensor Einstein equation at every time,
with no primitive Newton constant among the equation inputs. -/
@[zil_level physical_theorem]
lemma exists_local_evolution
    [Fintype ι] [DecidableEq ι]
    {ħ c σ₀ : ℝ} {initialState : X}
    (D : GFreeNonlinearEinsteinCauchyProblem (X := X) (ι := ι)
      ħ c σ₀ initialState) :
    ∃ trajectory : ℝ → X, trajectory 0 = initialState ∧
      ∃ ε > 0,
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt trajectory (D.vectorField (trajectory t)) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, D.FieldEquation (trajectory t)) := by
  obtain ⟨trajectory, hzero, ε, hε, hevol⟩ :=
    D.vectorField_contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨trajectory, hzero, ε, hε, ?_, ?_⟩
  · simpa only [zero_sub, zero_add] using hevol
  · intro t ht
    exact D.fieldEquation_propagates trajectory ε hzero
      (by simpa only [zero_sub, zero_add] using hevol) t ht

omit [CompleteSpace X] in
/-- **Boundary/initial-condition uniqueness for nonlinear evolution.** Two
trajectories of the same Lipschitz Einstein vector field with the same Cauchy
datum agree throughout their common open interval. -/
@[zil_level physical_theorem]
lemma local_evolution_unique
    [Fintype ι] [DecidableEq ι]
    {ħ c σ₀ : ℝ} {initialState : X}
    (D : GFreeNonlinearEinsteinCauchyProblem (X := X) (ι := ι)
      ħ c σ₀ initialState)
    {trajectory₁ trajectory₂ : ℝ → X} {ε : ℝ} (hε : 0 < ε)
    (hzero₁ : trajectory₁ 0 = initialState)
    (hzero₂ : trajectory₂ 0 = initialState)
    (hevol₁ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₁ (D.vectorField (trajectory₁ t)) t)
    (hevol₂ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₂ (D.vectorField (trajectory₂ t)) t) :
    Set.EqOn trajectory₁ trajectory₂ (Set.Ioo (-ε) ε) := by
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun _ => D.vectorField) (s := fun _ => Set.univ)
    (K := D.lipschitzConstant) (t₀ := 0)
  · intro _ _
    exact D.vectorField_lipschitz.lipschitzOnWith
  · constructor <;> linarith
  · intro t ht
    exact ⟨hevol₁ t ht, Set.mem_univ _⟩
  · intro t ht
    exact ⟨hevol₂ t ht, Set.mem_univ _⟩
  · rw [hzero₁, hzero₂]

end GFreeNonlinearEinsteinCauchyProblem

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicAction_tendsto_zero where
  formalizes @ "claim:the-imaginary-action-s-i-equals-hbar-log-k-tends-analytically-to-zero-as-the-rapidity-goes-to-infinity-the-schmidt-number-to-one-reversible-limit-a-genuine-tendsto-convergence-not-only-an-exact-value-at-k-equals-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.entropicAction"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate where
  formalizes @ "claim:beyond-eta-equals-log-two-over-two-the-imaginary-action-coefficient-log-k-is-nonnegative-and-at-most-four-exp-minus-two-eta",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.schmidtNumber_sub_one_eq_exp_defect",
  caveat @ "quantitative-bound-for-the-explicit-schmidt-rapidity-parametrization-not-a-universal-relaxation-rate"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicAction_tendsto_zero",
  formalizes @ "claim:the-path-integral-complex-action-weight-exp-minus-s-i-over-hbar-tends-to-one-as-the-rapidity-goes-to-infinity-removing-the-entropic-suppression-analytically-in-the-reversible-limit",
  requires @ "claim:the-imaginary-action-s-i-equals-hbar-log-k-tends-analytically-to-zero-as-the-rapidity-goes-to-infinity-the-schmidt-number-to-one-reversible-limit-a-genuine-tendsto-convergence-not-only-an-exact-value-at-k-equals-one"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entanglementScreenArea_tendsto_zero where
  supported_by @ "lean:HasVarAdjDerivAt.mul",
  formalizes @ "claim:the-existing-entanglement-screen-area-tends-to-zero-in-the-reversible-rapidity-limit",
  caveat @ "the-screen-area-and-its-compton-cell-count-vanish-together-so-this-limit-does-not-evaluate-the-area-per-bit-newton-coupling-or-an-indeterminate-zero-over-zero"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.comptonCellBits_tendsto_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entanglementScreenArea_tendsto_zero",
  formalizes @ "claim:the-g-free-compton-cell-count-of-the-entanglement-screen-tends-to-zero-in-the-reversible-rapidity-limit",
  caveat @ "this-is-a-limit-of-the-independent-count-not-a-limit-derivation-of-newtons-constant"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_newtonForm where
  formalizes @ "claim:the-g-free-inference-einstein-coupling-eight-pi-hbar-sigma0-to-the-fourth-over-c-cubed-equals-the-conventional-eight-pi-g-over-c-fourth-form-after-replacing-g-by-hbar-c-sigma0-to-the-fourth",
  epistemic_status @ "consistency-identity",
  caveat @ "epistemic:this-is-the-algebraic-normalization-bridge-the-independent-content-is-the-compton-cell-derivation-not-this-substitution"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_comptonCellBitForm where
  formalizes @ "claim:at-every-finite-positive-rapidity-the-independent-g-free-compton-cell-count-fixes-the-einstein-coupling-as-eight-pi-hbar-sigma0-to-the-fourth-over-c-cubed-equivalently-eight-pi-area-per-compton-bit-over-hbar-c",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  caveat @ "epistemic:no-newton-constant-occurs-in-the-theorem-inputs-but-the-position-variance-and-compton-cell-tiling-remain-explicit-model-inputs",
  caveat @ "the-finite-rapidity-ratio-is-used-and-not-the-indeterminate-zero-over-zero-of-the-reversible-screen-limit"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonianConvolutionPotential_eq_convolution where
  formalizes @ "claim:the-inferred-coupling-hbar-c-sigma0-to-the-fourth-weights-the-genuine-continuum-newtonian-potential-and-equals-the-bochner-convolution-with-that-weighted-density",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_eq_convolution",
  caveat @ "epistemic:the-convolution-identity-is-exact-but-identifying-hbar-c-sigma0-to-the-fourth-as-the-gravitational-coupling-retains-the-compton-cell-model-input",
  caveat @ "the-positive-newton-kernel-convention-does-not-by-itself-select-the-physical-potential-sign"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral where
  formalizes @ "claim:the-inferred-coupling-gives-the-continuum-schrodinger-poisson-energy-hbar-c-sigma0-to-the-fourth-over-four-times-the-newtonian-density-double-integral",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schrodingerPoissonGravitationalEnergy_eq_doubleIntegral",
  caveat @ "epistemic:an-exact-functional-identity-at-the-model-selected-coupling-not-an-independent-numerical-prediction-of-newtons-constant"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_distributionalWeakFieldEinstein00_of_poisson where
  formalizes @ "claim:the-continuum-distributional-poisson-law-at-hbar-c-sigma0-to-the-fourth-implies-the-static-linearized-einstein-zero-zero-equation-with-no-newton-constant-parameter",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-continuum-potential-satisfies-the-distributional-poisson-law-at-the-inferred-coupling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.distributionalWeakFieldEinstein00Equation3_of_poisson",
  caveat @ "epistemic:this-real-distribution-wrapper-retains-a-poisson-premise-while-the-complex-tempered-carrier-below-now-discharges-its-corresponding-premise",
  caveat @ "static-linearized-zero-zero-equation-not-the-full-nonlinear-einstein-system"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.temperedWeakFieldEinstein00Equation3_of_poisson where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:on-complex-tempered-distributions-the-continuum-poisson-equation-implies-the-static-linearized-einstein-zero-zero-equation",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:the-selected-tempered-potential-satisfies-poisson",
  caveat @ "generic-einstein-poisson-normalization-bridge-the-next-theorem-discharges-the-premise-for-the-constructed-newton-potential"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_weakFieldEinstein00 where
  formalizes @ "claim:the-canonically-complexified-one-over-norm-kernel-convolved-with-any-complex-schwartz-density-satisfies-the-static-linearized-einstein-zero-zero-equation-at-G-equals-hbar-c-sigma-zero-four-without-a-poisson-premise",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-inference-scale-identification-G-equals-hbar-c-sigma-zero-to-the-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.temperedWeakFieldEinstein00Equation3_of_poisson",
  caveat @ "the-continuum-pde-premise-is-discharged-but-the-inference-scale-identification-remains-model-loaded-and-this-is-the-static-linearized-zero-zero-sector"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_source_action where
  formalizes @ "claim:evaluating-the-G-free-continuum-poisson-equation-on-every-complex-schwartz-test-function-gives-four-pi-hbar-c-sigma-zero-four-times-the-integral-of-density-times-test-function",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-inference-scale-identification-G-equals-hbar-c-sigma-zero-to-the-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply",
  caveat @ "an-exact-weak-distributional-source-formula-on-schwartz-data-not-an-H-one-regularity-or-boundary-uniqueness-result"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique where
  formalizes @ "claim:at-the-model-inferred-coupling-G-equals-hbar-c-sigma-zero-four-every-complex-schwartz-density-has-both-the-tempered-static-einstein-zero-zero-equation-and-a-unique-zero-boundary-continuum-homogeneous-H-one-newton-solution",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-inference-scale-identification-G-equals-hbar-c-sigma-zero-to-the-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_weakFieldEinstein00",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique",
  caveat @ "the-source-H-minus-one-regularity-and-zero-boundary-energy-uniqueness-are-proved-for-schwartz-data-but-the-gravitational-coupling-identification-remains-model-loaded-and-the-einstein-result-remains-static-linearized-zero-zero"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution where
  formalizes @ "claim:on-any-complete-real-banach-phase-space-including-continuum-sobolev-field-carriers-a-C-one-gauge-reduced-nonlinear-einstein-vector-field-has-a-local-trajectory-and-explicit-bianchi-constraint-propagation-keeps-the-full-complex-tensor-einstein-equation-true-at-the-G-free-inference-coupling",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-gauge-reduced-einstein-vector-field-is-C-one-at-the-initial-state",
  requires @ "assumption:the-initial-complex-einstein-constraints-hold-and-bianchi-plus-constraint-propagation-preserves-the-full-field-equation",
  supported_by @ "lean:ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling",
  caveat @ "a-genuine-local-banach-space-evolution-theorem-conditional-on-the-gauge-reduced-PDE-regularity-and-constraint-propagation-data-not-an-unconditional-global-maximal-development-or-singularity-avoidance-result"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique where
  formalizes @ "claim:two-nonlinear-einstein-trajectories-of-the-same-lipschitz-gauge-reduced-vector-field-with-identical-cauchy-data-agree-on-their-common-local-time-interval",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-gauge-reduced-einstein-vector-field-is-lipschitz-on-the-phase-space-carrier",
  supported_by @ "lean:ODE_solution_unique_of_mem_Ioo",
  caveat @ "uniqueness-is-for-the-fixed-gauge-reduced-banach-space-evolution-and-does-not-identify-solutions-related-by-an-unspecified-diffeomorphism"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityEntropicStress_tendsto_zero where
  formalizes @ "claim:the-log-schmidt-number-scaled-entropic-stress-tensor-converges-to-zero-in-the-reversible-rapidity-limit",
  requires @ "model:the-entropic-stress-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-tensor",
  caveat @ "model-specific-interpolation-not-a-universal-law-for-every-entropic-stress-tensor"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexCombine_tendsto_right_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  formalizes @ "claim:complexifying-a-fixed-real-tensor-by-a-real-tensor-converging-to-zero-converges-entrywise-to-the-purely-real-complexification",
  epistemic_status @ "consistency-identity",
  caveat @ "structural-product-topology-continuity-lemma-with-no-independent-physical-claim"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinsteinTensor_tendsto_real where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexCombine_tendsto_right_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityEntropicStress_tendsto_zero",
  formalizes @ "claim:the-full-complex-einstein-tensor-at-the-g-free-inference-coupling-converges-entrywise-to-its-purely-real-einstein-tensor-in-the-reversible-rapidity-limit",
  requires @ "claim:the-log-schmidt-number-scaled-entropic-stress-tensor-converges-to-zero-in-the-reversible-rapidity-limit",
  requires @ "model:the-entropic-stress-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-tensor",
  caveat @ "this-is-product-topology-tensor-convergence-on-the-repositorys-matrix-carrier-not-yet-a-global-section-space-or-distributional-curvature-limit"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityComplexStressEnergy_tendsto_real where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexCombine_tendsto_right_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityEntropicStress_tendsto_zero",
  formalizes @ "claim:the-full-complex-stress-energy-tensor-t-plus-i-log-k-s0-converges-entrywise-to-the-ordinary-real-stress-energy-t-plus-i-zero-in-the-reversible-limit",
  requires @ "claim:the-log-schmidt-number-scaled-entropic-stress-tensor-converges-to-zero-in-the-reversible-rapidity-limit",
  caveat @ "model-specific-log-k-source-interpolation-on-the-matrix-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily where
  formalizes @ "claim:the-inference-variance-coupling-with-no-newton-constant-input-extends-any-real-einstein-source-equation-to-a-rapidity-family-of-complex-einstein-equations-whose-imaginary-curvature-vanishes-in-the-reversible-limit",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:at-every-finite-positive-rapidity-the-independent-g-free-compton-cell-count-fixes-the-einstein-coupling-as-eight-pi-hbar-sigma0-to-the-fourth-over-c-cubed-equivalently-eight-pi-area-per-compton-bit-over-hbar-c",
  requires @ "assumption:the-real-einstein-source-equation-holds-at-the-inference-variance-coupling",
  requires @ "model:the-entropic-stress-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein",
  caveat @ "epistemic:this-derives-the-complex-extension-without-a-g-parameter-but-does-not-predict-the-measured-value-of-sigma0-or-newtons-constant-from-no-physical-input",
  caveat @ "the-reversible-limit-removes-the-imaginary-sector-and-does-not-evaluate-the-collapsing-screen-area-over-bit-count"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily where
  formalizes @ "claim:at-the-g-free-inference-coupling-real-bianchi-and-a-divergence-free-reference-entropic-stress-give-at-every-rapidity-the-complex-einstein-equation-complex-bianchi-and-conservation-of-both-real-and-entropic-sources",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-real-einstein-source-equation-holds-at-the-inference-variance-coupling",
  requires @ "assumption:the-real-einstein-tensor-satisfies-the-contracted-bianchi-identity",
  requires @ "assumption:the-reference-entropic-stress-is-divergence-free",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexBianchi_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.bianchi_implies_conservation",
  caveat @ "epistemic:this-is-a-consistency-and-conservation-theorem-not-the-still-missing-raychaudhuri-null-horizon-derivation-of-the-real-einstein-equation-from-clausius-data"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexActionPathIntegralWeight_tendsto_phase where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
  formalizes @ "claim:the-full-master-complex-action-scalar-weight-converges-to-its-pure-reversible-phase-when-entropic-action-vanishes",
  caveat @ "pointwise-complex-scalar-convergence-only-not-operator-semigroup-path-measure-or-functional-integral-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.nnPathWeight_tendsto_phase where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
  formalizes @ "claim:the-nagao-nielsen-complex-action-scalar-weight-converges-to-its-pure-reversible-phase-when-entropic-action-vanishes",
  caveat @ "pointwise-complex-scalar-convergence-only-not-operator-semigroup-path-measure-or-functional-integral-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_tendsto_zero where
  formalizes @ "claim:the-log-schmidt-number-scaled-irreversible-generator-converges-to-zero-in-operator-norm-on-an-arbitrary-complete-complex-hilbert-space",
  requires @ "model:the-irreversible-generator-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-operator",
  caveat @ "model-specific-interpolation-not-a-claim-that-every-physical-irreversible-generator-has-this-rapidity-dependence"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_norm_le_exp_rate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate",
  formalizes @ "claim:the-log-k-scaled-irreversible-operator-has-the-explicit-finite-rapidity-norm-bound-four-exp-minus-two-eta-times-the-reference-operator-norm",
  requires @ "claim:beyond-eta-equals-log-two-over-two-the-imaginary-action-coefficient-log-k-is-nonnegative-and-at-most-four-exp-minus-two-eta",
  caveat @ "model-specific-log-k-interpolation-bound-not-a-universal-physical-decay-law"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_tendsto_reversible where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_tendsto_zero",
  formalizes @ "claim:the-log-k-scaled-non-hermitian-complex-hamiltonian-converges-in-operator-norm-to-its-reversible-hamiltonian",
  requires @ "claim:the-log-schmidt-number-scaled-irreversible-generator-converges-to-zero-in-operator-norm-on-an-arbitrary-complete-complex-hilbert-space"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_error_le_exp_rate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_norm_le_exp_rate",
  formalizes @ "claim:the-non-hermitian-complex-hamiltonian-differs-from-its-reversible-part-by-at-most-four-exp-minus-two-eta-times-the-reference-irreversible-operator-norm",
  requires @ "claim:the-log-k-scaled-irreversible-operator-has-the-explicit-finite-rapidity-norm-bound-four-exp-minus-two-eta-times-the-reference-operator-norm"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_tendsto_reversible where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_tendsto_reversible",
  formalizes @ "claim:the-corresponding-non-hermitian-schrodinger-generator-converges-in-operator-norm-to-the-reversible-generator",
  requires @ "claim:the-log-k-scaled-non-hermitian-complex-hamiltonian-converges-in-operator-norm-to-its-reversible-hamiltonian"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_error_le_exp_rate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_error_le_exp_rate",
  formalizes @ "claim:the-non-hermitian-schrodinger-generator-error-is-at-most-four-exp-minus-two-eta-times-the-reference-irreversible-norm-divided-by-absolute-hbar",
  requires @ "claim:the-non-hermitian-complex-hamiltonian-differs-from-its-reversible-part-by-at-most-four-exp-minus-two-eta-times-the-reference-irreversible-operator-norm",
  caveat @ "the-physical-inverse-hbar-reading-assumes-nonzero-hbar"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendsto_reversible where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_tendsto_reversible",
  formalizes @ "claim:at-every-fixed-time-the-banach-algebra-non-hermitian-propagator-converges-in-operator-norm-to-the-reversible-propagator",
  requires @ "claim:the-corresponding-non-hermitian-schrodinger-generator-converges-in-operator-norm-to-the-reversible-generator",
  caveat @ "this-fixed-time-theorem-is-promoted-to-bounded-interval-uniform-convergence-below-but-does-not-establish-path-measure-or-functional-integral-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendsto_reversible where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendsto_reversible",
  formalizes @ "claim:the-operator-norm-reversible-limit-implies-strong-propagator-convergence-on-every-fixed-hilbert-space-state",
  requires @ "claim:at-every-fixed-time-the-banach-algebra-non-hermitian-propagator-converges-in-operator-norm-to-the-reversible-propagator"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformly_compactTime where
  supported_by @ "lean:MState.Hermitian",
  formalizes @ "claim:the-log-k-scaled-propagator-converges-uniformly-in-operator-norm-over-every-continuously-parameterized-compact-time-carrier",
  requires @ "model:the-irreversible-generator-is-the-dimensionless-log-k-rapidity-scaling-of-a-fixed-reference-operator",
  caveat @ "compact-time-uniformity-not-global-uniformity-over-the-entire-real-time-axis"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformlyOn_boundedInterval where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformly_compactTime",
  formalizes @ "claim:the-non-hermitian-propagator-converges-uniformly-in-operator-norm-to-the-reversible-propagator-on-every-bounded-closed-time-interval",
  requires @ "claim:the-log-k-scaled-propagator-converges-uniformly-in-operator-norm-over-every-continuously-parameterized-compact-time-carrier",
  caveat @ "bounded-interval-uniform-convergence-not-global-all-time-uniformity-or-path-integral-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendstoUniformlyOn_boundedInterval where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformlyOn_boundedInterval",
  formalizes @ "claim:the-propagator-applied-to-every-fixed-continuum-hilbert-state-converges-uniformly-on-every-bounded-closed-time-interval",
  requires @ "claim:the-non-hermitian-propagator-converges-uniformly-in-operator-norm-to-the-reversible-propagator-on-every-bounded-closed-time-interval"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval where
  formalizes @ "claim:every-transition-amplitude-of-the-log-k-scaled-propagator-converges-uniformly-to-its-reversible-value-on-bounded-time-intervals",
  requires @ "claim:the-propagator-applied-to-every-fixed-continuum-hilbert-state-converges-uniformly-on-every-bounded-closed-time-interval"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicObservableExpectation_tendstoUniformlyOn_boundedInterval where
  formalizes @ "claim:every-bounded-operator-quadratic-expectation-of-the-log-k-scaled-propagator-converges-uniformly-to-its-reversible-value-on-bounded-time-intervals",
  requires @ "claim:the-non-hermitian-propagator-converges-uniformly-in-operator-norm-to-the-reversible-propagator-on-every-bounded-closed-time-interval",
  caveat @ "self-adjointness-of-the-observable-is-not-needed-for-complex-convergence-but-is-needed-for-a-real-valued-physical-expectation"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_boundedInterval where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  formalizes @ "claim:the-squared-norm-born-weight-of-the-log-k-scaled-evolved-state-converges-uniformly-to-the-reversible-born-weight-on-bounded-time-intervals",
  requires @ "claim:the-propagator-applied-to-every-fixed-continuum-hilbert-state-converges-uniformly-on-every-bounded-closed-time-interval",
  caveat @ "this-propagates-the-repositorys-supplied-modulus-squared-born-readout-and-does-not-derive-the-born-postulate-from-unitarity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_initial where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_boundedInterval",
  formalizes @ "claim:for-a-self-adjoint-reversible-hamiltonian-the-non-hermitian-evolved-born-weight-converges-uniformly-on-bounded-times-to-the-initial-weight-and-to-one-for-a-normalized-state",
  requires @ "claim:the-squared-norm-born-weight-of-the-log-k-scaled-evolved-state-converges-uniformly-to-the-reversible-born-weight-on-bounded-time-intervals",
  caveat @ "conditional-on-self-adjointness-nonzero-hbar-and-the-supplied-modulus-squared-readout-not-a-derivation-of-the-born-rule"

zil_file_contract physlib.reversibleLimitConvergence where
  promises "The frozen-sector reduction recovers reversible physics exactly at H_I = 0 but did not supply analytic convergence. This file supplies the rapidity limit: K tends to one; imaginary action, entropic proper distance, existing spherical screen area, and the G-free Compton-cell count tend to zero; suppression tends to one; and both master complex-action and Nagao-Nielsen scalar weights converge in C to their pure reversible phases. At every finite positive rapidity, the independently supplied Compton-cell count fixes the Einstein coupling directly as kappa(sigma0) = 8 pi hbar sigma0^4/c^3 = 8 pi area-per-compton-bit/(hbar c), with no Newton constant among the theorem inputs. The same inferred coefficient weights the genuine continuum Newtonian Bochner convolution and the Schrodinger-Poisson density double-integral energy. On the complex tempered carrier, the canonically scalar-extended one-over-norm fundamental solution discharges the continuum Poisson premise and directly yields the static linearized Einstein zero-zero equation plus its explicit Schwartz-test source integral. The older real Physlib-distribution wrapper retains an explicit Poisson premise. Any real Einstein source equation at that coupling extends to a family of complex Einstein equations with entropic stress log K times S0 and imaginary curvature kappa log K times S0; the full complex Einstein tensor and complex stress-energy converge entrywise to their purely real sectors as eta tends to infinity. If the real Einstein tensor and reference entropic stress are divergence-free, every member of this G-free family satisfies complex Bianchi and conserves both real and entropic sources. On an arbitrary complete real Banach phase space, a C-one gauge-reduced nonlinear Einstein vector field has a local trajectory; explicit Bianchi and constraint-propagation data keep the full complex tensor equation true, and Lipschitz control gives Cauchy uniqueness on the common interval. The exact defect K-1 = 2 exp(-2 eta)/(1-exp(-2 eta)) yields the finite-rapidity estimate 0 <= log K <= 4 exp(-2 eta) beyond eta = log 2/2, and therefore explicit exponential norm-error bounds for the irreversible operator, complex Hamiltonian and Schrodinger generator on an arbitrary complete complex Hilbert space. The Banach-algebra propagator converges uniformly in operator norm on every bounded closed time interval and hence uniformly strongly on each fixed state. Continuous readouts inherit compact-time uniform convergence, yielding bounded-time recovery of transition amplitudes, bounded-observable expectations and squared-norm Born weights; for self-adjoint H_R the latter converges to the initial weight and hence to one for a normalized supplied state. This propagates rather than derives the modulus-squared postulate. This model-specific result does not claim a universal relaxation rate, global all-time uniformity, path-measure, functional-integral convergence, unconditional global maximal Einstein development, singularity avoidance, or the Raychaudhuri null-horizon derivation of the real Einstein equation from Clausius data. The finite screen ratio, not the simultaneous zero limits of area and bit count, supplies the coupling; the limit removes the imaginary sector and does not derive a limiting G."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.entropicAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance",
    "lean:Physlib.Thermodynamics.sphereArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexBianchi_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.bianchi_implies_conservation",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_eq_convolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schrodingerPoissonGravitationalEnergy_eq_doubleIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.distributionalWeakFieldEinstein00Equation3_of_poisson",
    "lean:ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀",
    "lean:ODE_solution_unique_of_mem_Ioo",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight",
    "lean:QuantumMechanics.FiniteTarget.complexHamiltonian",
    "lean:Physlib.QuantumMechanics.NonHermitian.Propagator.schrodingerGenerator",
    "lean:Physlib.QuantumMechanics.NonHermitian.Propagator.propagator"]
  forbids_substitutes ["the exact-at-K-equals-1 frozen reduction alone, whereas this is a genuine Tendsto convergence as the rapidity tends to infinity",
    "substituting the joint zero limits of screen area and bit count into their quotient to claim a limiting G",
    "claiming the measured value of Newtons constant from no input whereas the inference scale and Compton-cell tiling remain explicit model data",
    "claiming the reversible limit itself derives the Einstein coupling whereas the coupling is fixed by the finite-rapidity Compton-cell ratio",
    "claiming a Raychaudhuri null-horizon derivation of the real Einstein equation from Clausius data which remains a separate repository gap",
    "claiming H-one regularity boundary-condition uniqueness or nonlinear Einstein evolution from the proved Schwartz-tempered Poisson equation",
    "claiming every physical irreversible generator has the chosen log-K rapidity interpolation",
    "treating the model-specific four-exp-minus-two-eta estimate as a universal physical relaxation rate",
    "global uniform convergence over the entire real-time axis or path-measure or functional-integral convergence"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.schmidtNumber_tendsto_one,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicAction_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicProperDistance_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entanglementScreenArea_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.comptonCellBits_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_newtonForm,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_comptonCellBitForm,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonianConvolutionPotential_eq_convolution,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_distributionalWeakFieldEinstein00_of_poisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.temperedWeakFieldEinstein00Equation3_of_poisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_weakFieldEinstein00,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_source_action,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityEntropicStress_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexCombine_tendsto_right_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinsteinTensor_tendsto_real,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityComplexStressEnergy_tendsto_real,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexActionPathIntegralWeight_tendsto_phase,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.nnPathWeight_tendsto_phase,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_norm_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_error_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_error_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformly_compactTime,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicObservableExpectation_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_initial]

/- ZIL-END -/
