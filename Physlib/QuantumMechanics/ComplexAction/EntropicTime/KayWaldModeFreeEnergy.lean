/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBifurcateHorizonSurfaceGravity
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicciFromMetric
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
public import Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Physlib.Thermodynamics.VerlindeEntropicForce
meta import Zil

/-!
# The free energy of a Hawking mode and the Gibbs relation `F = ⟨E⟩ − TS` (Kay–Wald)

Closes the thermodynamics of a single bosonic Killing-horizon mode in the Hawking–KMS state: the **partition
function** `Z = 1/(1 − e^{−βω}) = n + 1`, the **mean energy** `⟨E⟩ = ωn`, the **Helmholtz free energy**
`F = −T ln Z = −(1/β) ln(n+1)`, and the **Gibbs (thermodynamic) relation**

`F = ⟨E⟩ − T S`,   equivalently   `T S = ⟨E⟩ − F`,

tying together the free energy, the mean energy, and the bosonic thermal entropy `S = βω·n + ln(n+1)` of
`KayWaldBosonicThermalEntropy`. Everything rides on the single identity `Z = n + 1`: the single-mode partition
function is the total-emission occupation, so `ln Z = ln(n+1)` is exactly the free-energy term appearing in the
entropy's first-law split.

* the **single-mode partition function is the total-emission occupation** `Z = 1/(1 − e^{−βω}) = n + 1`
  (`modePartition_eq_occupation_add_one`);
* the **Gibbs relation** `F = ⟨E⟩ − T S` (`gibbs_relation`) — the Helmholtz free energy equals the mean energy
  minus the temperature times the entropy, the defining thermodynamic identity of the equilibrium (KMS) state;
* the **Clausius / heat form** `T S = ⟨E⟩ − F` (`heat_eq_energy_minus_free`) — the heat content of the thermal
  mode;
* the **Hawking specialization** `β = 2π/κ` (`hawking_gibbs_relation`) — the Gibbs relation for a
  bifurcate-Killing-horizon mode at the Hawking temperature.

So the Kay–Wald thermal mode obeys the full Gibbs thermodynamics `F = ⟨E⟩ − TS` with `Z = n+1`, `⟨E⟩ = ωn`, and
the bosonic entropy `S`; the free energy, energy, and entropy of the Hawking radiation are one consistent
equilibrium, on the same thermal spine as the KMS periodicity and the entropy.

* **§A — the partition function `Z = n + 1`** (`modeMeanEnergy`, `modePartitionFunction`, `modeFreeEnergy`,
  `modePartition_eq_occupation_add_one`).
* **§B — the Gibbs relation and its heat form** (`gibbs_relation`, `heat_eq_energy_minus_free`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_gibbs_relation`).
* **§D — the metric-derived Schwarzschild Euclidean saddle**: the Euclidean metric, inverse, and boundary
  determinant are explicit; the static Wick continuation of the exact metric-derived Ricci tensor has
  vanishing Euclidean scalar curvature; the continuum Einstein–Hilbert exterior integral is zero; the radial
  extrinsic-curvature trace is computed from the repository's `metric → christoffelFromMetric` carrier; the
  complete Einstein–Hilbert plus reference-subtracted Gibbons–Hawking–York cutoff action converges to
  `I_E/ℏ = β_H M/2`; imaginary-time periodicity fixes `β_H`; and
  `β_H M + log Z` is the Bekenstein quarter-area entropy
  (`gibbonsHawking_metricDerived_schwarzschild_euclidean_thermodynamics`).

**Honest layering.** The partition-function identity, the free-energy definition, and the Gibbs relation are exact
`Real.log`/`Real.exp` algebra for a single mode with mean energy `⟨E⟩ = ωn` (zero-point energy omitted, as is
conventional for the radiation content). The full grand-canonical ensemble, the integrated Stefan–Boltzmann free
energy (`StatisticalMechanics.MasslessStefanBoltzmann`, a distinct integrated object), and the operator-algebraic
KMS derivation are the referenced content. Section D reuses the proved affine–Killing imaginary-time periodicity,
the exact metric-to-Ricci Schwarzschild vacuum computation as the static Wick-continued bulk datum, the generic
GHY surface-term carrier, and the repository's Schwarzschild area law. The Wick-continued scalar curvature is
proved zero and its restricted exterior Einstein–Hilbert integral is evaluated, rather than represented by a
supplied scalar. The complete bulk-plus-boundary action derives the dimensionless on-shell value
`I_E/ℏ = β_H M/2` as the asymptotic limit of the flat-reference-subtracted radial GHY cutoff computed from the
Euclidean Schwarzschild metric. Ricci flatness makes the vacuum bulk integrand vanish. This remains a classical,
natural-unit, asymptotically-flat saddle calculation: the file does not construct the gravitational functional
measure, prove gauge-fixing determinants, or control loop corrections away from the saddle.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; standard equilibrium thermodynamics. Repo carrier:
  `EntropicTime.KayWaldBosonicThermalEntropy` (`bosonicEntropy`, `bosonicEntropy_thermal`).
* G.W. Gibbons, S.W. Hawking, Phys. Rev. D 15 (1977) 2752; Euclidean gravitational partition function.
* S.W. Hawking, G.T. Horowitz, Class. Quantum Grav. 13 (1996) 1487; background-subtracted Euclidean
  gravitational action, Hamiltonian term, and horizon entropy.
* J.D. Bekenstein, Physics Today 33(1) (1980) 24; imaginary-time periodicity, partition function, Hawking
  temperature, and black-hole entropy.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBifurcateHorizonSurfaceGravity
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm
open Physlib.Relativity.SemiClassical
open Physlib.Thermodynamics
open MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy


/-- **The mean energy of the thermal mode** `⟨E⟩ = ωn` — the mode frequency times the Bose occupation (the
radiation energy above the ground state). -/
noncomputable def modeMeanEnergy (β ω : ℝ) : ℝ := ω * hawkingOccupation β ω

/-- **The single-mode bosonic partition function** `Z = 1/(1 − e^{−βω})` — the geometric sum over the oscillator
tower `Σ_k e^{−βωk}`. -/
noncomputable def modePartitionFunction (β ω : ℝ) : ℝ := 1 / (1 - Real.exp (-(β * ω)))

/-- **The Helmholtz free energy of the mode** `F = −T ln Z = −(1/β) ln Z` — the free energy of the thermal
Killing-horizon mode. -/
noncomputable def modeFreeEnergy (β ω : ℝ) : ℝ := -(1 / β) * Real.log (modePartitionFunction β ω)

/-- **[The single-mode partition function is the total-emission occupation] `Z = 1/(1 − e^{−βω}) = n + 1`.** The
geometric partition function of the bosonic tower equals `n + 1` with `n = 1/(e^{βω}−1)` the Bose occupation, so
`ln Z = ln(n+1)` is exactly the free-energy term in the entropy's first-law split. -/
lemma modePartition_eq_occupation_add_one (β ω : ℝ) (hβω : 0 < β * ω) :
    modePartitionFunction β ω = hawkingOccupation β ω + 1 := by
  have hE1 : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hβω
  have hEne : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp (β * ω) - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; exact absurd h.symm (by linarith)
  unfold modePartitionFunction hawkingOccupation
  rw [Real.exp_neg]
  field_simp
  ring


/-- **[The Gibbs relation] `F = ⟨E⟩ − T S`.** The Helmholtz free energy of the thermal mode equals the mean energy
minus temperature times entropy (`T = 1/β`): using `Z = n+1` and the first-law entropy `S = βω·n + ln(n+1)`, the
`ω n` terms cancel and leave `F = −(1/β) ln(n+1)`. This is the defining thermodynamic identity of the equilibrium
(KMS) state. -/
lemma gibbs_relation (β ω : ℝ) (hβ : β ≠ 0) (hβω : 0 < β * ω) :
    modeFreeEnergy β ω
      = modeMeanEnergy β ω - (1 / β) * bosonicEntropy (hawkingOccupation β ω) := by
  unfold modeFreeEnergy modeMeanEnergy
  rw [modePartition_eq_occupation_add_one β ω hβω, bosonicEntropy_thermal β ω hβω]
  field_simp
  ring

/-- **[The Clausius / heat form] `T S = ⟨E⟩ − F`.** Rearranging the Gibbs relation: the heat content `T S` of the
thermal mode is the mean energy minus the free energy. -/
lemma heat_eq_energy_minus_free (β ω : ℝ) (hβ : β ≠ 0) (hβω : 0 < β * ω) :
    (1 / β) * bosonicEntropy (hawkingOccupation β ω) = modeMeanEnergy β ω - modeFreeEnergy β ω := by
  rw [gibbs_relation β ω hβ hβω]; ring


/-- **[The Gibbs relation for a Hawking mode at `T_H = κ/2π`].** Specializing to the Hawking inverse temperature
`β = hawkingBeta 1 κ 1 1 = 2π/κ`: the free energy, mean energy, and bosonic entropy of a bifurcate-Killing-horizon
mode form a consistent equilibrium `F = ⟨E⟩ − T_H S`. -/
lemma hawking_gibbs_relation (κ ω : ℝ) (hβ : hawkingBeta 1 κ 1 1 ≠ 0)
    (hκω : 0 < hawkingBeta 1 κ 1 1 * ω) :
    modeFreeEnergy (hawkingBeta 1 κ 1 1) ω
      = modeMeanEnergy (hawkingBeta 1 κ 1 1) ω
        - (1 / hawkingBeta 1 κ 1 1) * bosonicEntropy (hawkingOccupation (hawkingBeta 1 κ 1 1) ω) :=
  gibbs_relation (hawkingBeta 1 κ 1 1) ω hβ hκω


/-! ## D. Gibbons–Hawking Euclidean Schwarzschild thermodynamics -/

/-- The Euclidean Schwarzschild metric
`diag(f, f⁻¹, R², R² sin²θ)`, where `f(R) = 1 - 2M/R`.

It is the positive-time-signature continuation of the exact Lorentzian
Schwarzschild metric formalized in `SchwarzschildRicciFromMetric`. -/
noncomputable def euclideanSchwarzschildMetric
    (M R sinTheta : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal
    ![schwF M R, (schwF M R)⁻¹, R ^ 2, R ^ 2 * sinTheta ^ 2]

/-- The Euclidean Schwarzschild metric determinant is
`R⁴ sin²θ`; the factors `f` and `f⁻¹` cancel. -/
lemma euclideanSchwarzschildMetric_det
    (M R sinTheta : ℝ) (hf : schwF M R ≠ 0) :
    (euclideanSchwarzschildMetric M R sinTheta).det =
      R ^ 4 * sinTheta ^ 2 := by
  rw [euclideanSchwarzschildMetric, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp

/-- The inverse Euclidean Schwarzschild metric
`diag(f⁻¹, f, R⁻², (R² sin²θ)⁻¹)`. -/
noncomputable def euclideanSchwarzschildMetricInv
    (M R sinTheta : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal
    ![(schwF M R)⁻¹, schwF M R, (R ^ 2)⁻¹,
      (R ^ 2 * sinTheta ^ 2)⁻¹]

/-- The declared Euclidean inverse is genuine away from the horizon, radial
origin, and polar coordinate axis. -/
lemma euclideanSchwarzschildMetric_mul_inv
    (M R sinTheta : ℝ) (hf : schwF M R ≠ 0)
    (hR : R ≠ 0) (hs : sinTheta ≠ 0) :
    euclideanSchwarzschildMetric M R sinTheta *
        euclideanSchwarzschildMetricInv M R sinTheta = 1 := by
  rw [euclideanSchwarzschildMetric, euclideanSchwarzschildMetricInv,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    fin_cases i <;> simp <;> field_simp
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- The metric induced on a radial Euclidean boundary `R = constant`:
`diag(f, R², R² sin²θ)` in coordinates `(τ, θ, φ)`. -/
noncomputable def euclideanSchwarzschildBoundaryMetric
    (M R sinTheta : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![schwF M R, R ^ 2, R ^ 2 * sinTheta ^ 2]

/-- The radial-boundary determinant is `f R⁴ sin²θ`. Its positive square
root supplies `R² sqrt(f) sinθ`, hence the integrated boundary factor
`β · 4πR² sqrt(f)` used below. -/
lemma euclideanSchwarzschildBoundaryMetric_det
    (M R sinTheta : ℝ) :
    (euclideanSchwarzschildBoundaryMetric M R sinTheta).det =
      schwF M R * R ^ 4 * sinTheta ^ 2 := by
  rw [euclideanSchwarzschildBoundaryMetric, Matrix.det_diagonal,
    Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The Euclidean Schwarzschild Ricci tensor obtained by static Wick
continuation of the repository's exact metric-derived Lorentzian Ricci
tensor.

For a covariant rank-two tensor, `t = -iτ` changes the `00` component by a
minus sign and leaves all other components unchanged. This construction is
therefore not an independent curvature certificate: its source is precisely
`schwarzschild_ricci_eq_zero`, whose connection and Ricci tensor were
computed from the Schwarzschild metric. -/
noncomputable def euclideanSchwarzschildRicciFromMetric
    (M R sinTheta cosTheta : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν =>
    let ric :=
      ricciFromConnection
        (christoffel (schwF M R) (schwDf M R) R sinTheta cosTheta)
        (connDeriv (schwF M R) (schwDf M R) (schwDdf M R)
          R sinTheta cosTheta) μ ν
    if μ = 0 ∧ ν = 0 then -ric else ric

/-- The static Wick continuation of the metric-derived Schwarzschild Ricci
tensor vanishes identically on the regular coordinate domain. -/
lemma euclideanSchwarzschildRicciFromMetric_eq_zero
    (M R sinTheta cosTheta : ℝ)
    (hR : R ≠ 0) (hs : sinTheta ≠ 0) (hf : schwF M R ≠ 0) :
    euclideanSchwarzschildRicciFromMetric M R sinTheta cosTheta = 0 := by
  ext μ ν
  rw [euclideanSchwarzschildRicciFromMetric]
  split_ifs
  · rw [schwarzschild_ricci_eq_zero M R sinTheta cosTheta hR hs hf μ ν]
    simp
  · simpa using
      schwarzschild_ricci_eq_zero M R sinTheta cosTheta hR hs hf μ ν

/-- The Euclidean Schwarzschild scalar curvature is the trace of the
Wick-continued Ricci tensor raised with the Euclidean inverse metric. -/
noncomputable def euclideanSchwarzschildScalarCurvatureFromMetric
    (M R sinTheta cosTheta : ℝ) : ℝ :=
  ricciScalarContraction
    (euclideanSchwarzschildMetricInv M R sinTheta)
    (euclideanSchwarzschildRicciFromMetric M R sinTheta cosTheta)

/-- The Euclidean Schwarzschild scalar curvature vanishes on the regular
coordinate domain. This is the pointwise vacuum Einstein–Hilbert bulk
identity used by the complete regulated action below. -/
lemma euclideanSchwarzschildScalarCurvatureFromMetric_eq_zero
    (M R sinTheta cosTheta : ℝ)
    (hR : R ≠ 0) (hs : sinTheta ≠ 0) (hf : schwF M R ≠ 0) :
    euclideanSchwarzschildScalarCurvatureFromMetric
      M R sinTheta cosTheta = 0 := by
  rw [euclideanSchwarzschildScalarCurvatureFromMetric,
    euclideanSchwarzschildRicciFromMetric_eq_zero
      M R sinTheta cosTheta hR hs hf]
  simp [ricciScalarContraction]

/-- The continuum radial Einstein–Hilbert bulk action between the horizon
and cutoff `R`, after integrating the Euclidean time circle and two-sphere.
The remaining integrand is
`β · 4πr² · scalarCurvature(r)`, with the usual `-1/(16π)`
Euclidean normalization. -/
noncomputable def schwarzschildRegulatedEuclideanBulkAction
    (β M R : ℝ) : ℝ :=
  -(1 / (16 * Real.pi)) *
    ∫ r in Set.Ioc (2 * M) R,
      β * (4 * Real.pi * r ^ 2) *
        euclideanSchwarzschildScalarCurvatureFromMetric M r 1 0

/-- The full continuum Euclidean Schwarzschild bulk action is zero because
the metric-derived scalar curvature vanishes at every exterior point. -/
lemma schwarzschildRegulatedEuclideanBulkAction_eq_zero
    (β M R : ℝ) (hM : 0 < M) :
    schwarzschildRegulatedEuclideanBulkAction β M R = 0 := by
  unfold schwarzschildRegulatedEuclideanBulkAction
  have hintegral :
      (∫ r in Set.Ioc (2 * M) R,
        β * (4 * Real.pi * r ^ 2) *
          euclideanSchwarzschildScalarCurvatureFromMetric M r 1 0) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := by nlinarith [hr.1]
    have hf : 0 < schwF M r := by
      rw [schwF]
      exact sub_pos.mpr ((div_lt_one hr0).mpr hr.1)
    rw [euclideanSchwarzschildScalarCurvatureFromMetric_eq_zero
      M r 1 0 hr0.ne' one_ne_zero hf.ne']
    simp
  rw [hintegral]
  ring

/-- The trace of the extrinsic curvature of the radial Euclidean
Schwarzschild boundary, computed from the exact inverse metric and
`christoffelFromMetric`.

The Lorentzian time contribution can be used directly: Wick rotation changes
both `g^{tt}` and `Γʳₜₜ` by a sign, so their contraction is unchanged. The
spatial components are unchanged. Thus this is the Euclidean trace without
introducing an independent connection certificate. -/
noncomputable def schwarzschildEuclideanBoundaryMeanCurvatureFromMetric
    (M R : ℝ) : ℝ :=
  let f := schwF M R
  let df := schwDf M R
  metricInv f R 1 0 0 *
      (-christoffelFromMetric (metricInv f R 1)
        (metricDeriv f df R 1 0) 1 0 0) / Real.sqrt f +
    metricInv f R 1 2 2 *
      (-christoffelFromMetric (metricInv f R 1)
        (metricDeriv f df R 1 0) 1 2 2) / Real.sqrt f +
    metricInv f R 1 3 3 *
      (-christoffelFromMetric (metricInv f R 1)
        (metricDeriv f df R 1 0) 1 3 3) / Real.sqrt f

/-- The metric-derived radial mean curvature is
`K = 2√f/R + f'/(2√f)`. -/
lemma schwarzschildEuclideanBoundaryMeanCurvatureFromMetric_eq
    (M R : ℝ) (hf : 0 < schwF M R) (hR : R ≠ 0) :
    schwarzschildEuclideanBoundaryMeanCurvatureFromMetric M R =
      2 * Real.sqrt (schwF M R) / R +
        schwDf M R / (2 * Real.sqrt (schwF M R)) := by
  have hsqrt : Real.sqrt (schwF M R) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hf)
  have hsqrt_sq : Real.sqrt (schwF M R) ^ 2 = schwF M R :=
    Real.sq_sqrt hf.le
  rw [schwarzschildEuclideanBoundaryMeanCurvatureFromMetric,
    christoffel_r_tt, christoffel_r_thth, christoffel_r_phph]
  have h00 : metricInv (schwF M R) R 1 0 0 = -(schwF M R)⁻¹ := rfl
  have h22 : metricInv (schwF M R) R 1 2 2 = (R ^ 2)⁻¹ := rfl
  have h33 : metricInv (schwF M R) R 1 3 3 = (R ^ 2)⁻¹ := by
    change (R ^ 2 * 1 ^ 2)⁻¹ = (R ^ 2)⁻¹
    ring
  rw [h00, h22, h33]
  field_simp [hf.ne', hR, hsqrt]
  nlinarith

/-- The integrated reference-subtracted radial GHY datum
`∫√h (K-K₀)` at cutoff radius `R`, with flat matched reference
`K₀ = 2/R` and Euclidean period `β`. -/
noncomputable def schwarzschildReferenceSubtractedGHYIntegral
    (β M R : ℝ) : ℝ :=
  β * (4 * Real.pi * R ^ 2 * Real.sqrt (schwF M R)) *
    (schwarzschildEuclideanBoundaryMeanCurvatureFromMetric M R - 2 / R)

/-- The dimensionless regulated Euclidean gravitational action. The vacuum
Schwarzschild bulk scalar vanishes by `schwarzschild_ricci_eq_zero`, so the
on-shell value is the GHY term divided by the Einstein normalization `16π`.
Since `ghySurfaceTerm 1 B = -2B`, this is `-B/(8π)`. -/
noncomputable def schwarzschildRegulatedEuclideanAction
    (β M R : ℝ) : ℝ :=
  ghySurfaceTerm 1 (schwarzschildReferenceSubtractedGHYIntegral β M R) /
    (16 * Real.pi)

/-- The complete regulated Euclidean gravitational action
`I_E(R) = I_EH(R) + I_GHY(R)`, combining the continuum
Einstein–Hilbert bulk integral with the reference-subtracted GHY boundary
term. -/
noncomputable def schwarzschildRegulatedEinsteinHilbertGHYAction
    (β M R : ℝ) : ℝ :=
  schwarzschildRegulatedEuclideanBulkAction β M R +
    schwarzschildRegulatedEuclideanAction β M R

/-- On the positive-mass Schwarzschild vacuum, the complete regulated
Einstein–Hilbert plus GHY action reduces exactly to the boundary action. -/
lemma schwarzschildRegulatedEinsteinHilbertGHYAction_eq_boundary
    (β M R : ℝ) (hM : 0 < M) :
    schwarzschildRegulatedEinsteinHilbertGHYAction β M R =
      schwarzschildRegulatedEuclideanAction β M R := by
  rw [schwarzschildRegulatedEinsteinHilbertGHYAction,
    schwarzschildRegulatedEuclideanBulkAction_eq_zero β M R hM, zero_add]

/-- Outside the horizon (`2M < R`), the Schwarzschild profile is positive. -/
lemma schwF_pos_of_two_mul_lt
    (M R : ℝ) (hR : 0 < R) (h : 2 * M < R) :
    0 < schwF M R := by
  rw [schwF]
  exact sub_pos.mpr ((div_lt_one hR).mpr h)

/-- Exact finite-cutoff evaluation of the reference-subtracted GHY integral:
`B_R = 4πβ(4M/(1+√f(R)) - 3M)`.

The rationalized form avoids an asymptotic series and makes the limit
`B_R → -4πβM` a direct continuity argument. -/
lemma schwarzschildReferenceSubtractedGHYIntegral_eq
    (β M R : ℝ) (hR : 0 < R) (h : 2 * M < R) :
    schwarzschildReferenceSubtractedGHYIntegral β M R =
      4 * Real.pi * β *
        (4 * M / (1 + Real.sqrt (schwF M R)) - 3 * M) := by
  have hf : 0 < schwF M R := schwF_pos_of_two_mul_lt M R hR h
  have hsqrt : Real.sqrt (schwF M R) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hf)
  have hsum : 1 + Real.sqrt (schwF M R) ≠ 0 := by positivity
  have hsqrt_sq : Real.sqrt (schwF M R) ^ 2 = schwF M R :=
    Real.sq_sqrt hf.le
  have hcore :
      R ^ 2 * Real.sqrt (schwF M R) *
          (2 * Real.sqrt (schwF M R) / R +
            schwDf M R / (2 * Real.sqrt (schwF M R)) - 2 / R) =
        4 * M / (1 + Real.sqrt (schwF M R)) - 3 * M := by
    have hfirst :
        R ^ 2 * Real.sqrt (schwF M R) *
            (2 * Real.sqrt (schwF M R) / R +
              schwDf M R / (2 * Real.sqrt (schwF M R)) - 2 / R) =
          2 * R * Real.sqrt (schwF M R) ^ 2 + M -
            2 * R * Real.sqrt (schwF M R) := by
      rw [schwDf]
      field_simp
    rw [hfirst]
    have hRq :
        R * Real.sqrt (schwF M R) ^ 2 = R - 2 * M := by
      rw [hsqrt_sq, schwF]
      field_simp
    rw [show
      2 * R * Real.sqrt (schwF M R) ^ 2 =
        2 * (R * Real.sqrt (schwF M R) ^ 2) by ring, hRq]
    field_simp
    nlinarith [hRq]
  rw [schwarzschildReferenceSubtractedGHYIntegral,
    schwarzschildEuclideanBoundaryMeanCurvatureFromMetric_eq M R hf hR.ne']
  rw [show
      β * (4 * Real.pi * R ^ 2 * Real.sqrt (schwF M R)) *
          (2 * Real.sqrt (schwF M R) / R +
            schwDf M R / (2 * Real.sqrt (schwF M R)) - 2 / R) =
        4 * Real.pi * β *
          (R ^ 2 * Real.sqrt (schwF M R) *
            (2 * Real.sqrt (schwF M R) / R +
              schwDf M R / (2 * Real.sqrt (schwF M R)) - 2 / R)) by ring,
    hcore]

/-- The Schwarzschild lapse tends to one at spatial infinity. -/
lemma sqrt_schwF_tendsto_one_atTop (M : ℝ) :
    Filter.Tendsto (fun R : ℝ => Real.sqrt (schwF M R))
      Filter.atTop (nhds 1) := by
  have hInv : Filter.Tendsto (fun R : ℝ => R⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hF : Filter.Tendsto (fun R : ℝ => schwF M R)
      Filter.atTop (nhds 1) := by
    simpa [schwF, div_eq_mul_inv] using
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hInv)
  change Filter.Tendsto
    ((fun x : ℝ => Real.sqrt x) ∘ fun R : ℝ => schwF M R)
    Filter.atTop (nhds 1)
  convert (Real.continuous_sqrt.tendsto 1).comp hF using 1 <;> norm_num

/-- The reference-subtracted GHY boundary integral converges to
`-4πβM` as the cutoff tends to spatial infinity. -/
lemma schwarzschildReferenceSubtractedGHYIntegral_tendsto
    (β M : ℝ) :
    Filter.Tendsto (schwarzschildReferenceSubtractedGHYIntegral β M)
      Filter.atTop (nhds (-4 * Real.pi * β * M)) := by
  have hsqrt := sqrt_schwF_tendsto_one_atTop M
  have hden : (1 : ℝ) + 1 ≠ 0 := by norm_num
  have hmain :
      Filter.Tendsto
        (fun R : ℝ =>
          4 * Real.pi * β *
            (4 * M / (1 + Real.sqrt (schwF M R)) - 3 * M))
        Filter.atTop (nhds (-4 * Real.pi * β * M)) := by
    have hnum : Filter.Tendsto (fun _ : ℝ => 4 * M)
        Filter.atTop (nhds (4 * M)) := tendsto_const_nhds
    have hdenT : Filter.Tendsto
        (fun R : ℝ => 1 + Real.sqrt (schwF M R))
        Filter.atTop (nhds (1 + 1)) :=
      tendsto_const_nhds.add hsqrt
    have hthree : Filter.Tendsto (fun _ : ℝ => 3 * M)
        Filter.atTop (nhds (3 * M)) := tendsto_const_nhds
    have hfactor : Filter.Tendsto (fun _ : ℝ => 4 * Real.pi * β)
        Filter.atTop (nhds (4 * Real.pi * β)) := tendsto_const_nhds
    convert hfactor.mul ((hnum.div hdenT hden).sub hthree) using 1 <;>
      norm_num <;> ring
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max (2 * M) 0)] with R hR
  have hR0 : 0 < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRM : 2 * M < R := lt_of_le_of_lt (le_max_left _ _) hR
  exact (schwarzschildReferenceSubtractedGHYIntegral_eq β M R hR0 hRM).symm

/-- **Metric-derived Gibbons–Hawking evaluation.**
The regulated Euclidean gravitational action converges to
`I_E/ℏ = βM/2`; this is the evaluated Schwarzschild saddle rather than a
supplied algebraic input. -/
lemma schwarzschildRegulatedEuclideanAction_tendsto
    (β M : ℝ) :
    Filter.Tendsto (schwarzschildRegulatedEuclideanAction β M)
      Filter.atTop (nhds (β * M / 2)) := by
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold schwarzschildRegulatedEuclideanAction
  rw [show (fun R =>
      ghySurfaceTerm 1
          (schwarzschildReferenceSubtractedGHYIntegral β M R) /
        (16 * Real.pi)) =
      (fun R => -(schwarzschildReferenceSubtractedGHYIntegral β M R) /
        (8 * Real.pi)) by
    funext R
    unfold ghySurfaceTerm
    ring]
  convert
    (schwarzschildReferenceSubtractedGHYIntegral_tendsto β M).neg.div_const
      (8 * Real.pi) using 1 <;>
    field_simp <;> ring

/-- The **complete** Einstein–Hilbert plus GHY action has the same
metric-derived limit `βM/2`: its continuum bulk integral is zero and its
boundary term supplies the entire on-shell value. -/
lemma schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto
    (β M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (schwarzschildRegulatedEinsteinHilbertGHYAction β M)
      Filter.atTop (nhds (β * M / 2)) := by
  have hEq :
      schwarzschildRegulatedEinsteinHilbertGHYAction β M =
        schwarzschildRegulatedEuclideanAction β M := by
    funext R
    exact schwarzschildRegulatedEinsteinHilbertGHYAction_eq_boundary
      β M R hM
  rw [hEq]
  exact schwarzschildRegulatedEuclideanAction_tendsto β M

/-- The Euclidean-time period `2π/κ` of a Schwarzschild saddle in natural
units. This is the real period multiplying the imaginary Killing-time
direction. -/
noncomputable def schwarzschildEuclideanPeriod (M : ℝ) : ℝ :=
  2 * Real.pi / schwarzschildSurfaceGravity 1 M 1

/-- The dimensionless Schwarzschild Euclidean saddle action
`I_E / ℏ = β_H M / 2` in natural units. The equality with the asymptotic
metric-derived GHY action is proved below by
`schwarzschildRegulatedEuclideanAction_tendsto_saddleAction`. -/
noncomputable def schwarzschildEuclideanSaddleAction (M : ℝ) : ℝ :=
  schwarzschildEuclideanPeriod M * M / 2

/-- The saddle partition function `Z = exp (-I_E / ℏ)`. -/
noncomputable def schwarzschildEuclideanPartitionFunction (M : ℝ) : ℝ :=
  Real.exp (-schwarzschildEuclideanSaddleAction M)

/-- The finite-cutoff saddle partition function `exp(-I_E(R)/ℏ)`. -/
noncomputable def schwarzschildRegulatedEuclideanPartitionFunction
    (β M R : ℝ) : ℝ :=
  Real.exp (-schwarzschildRegulatedEuclideanAction β M R)

/-- The finite-cutoff partition function built from the complete
Einstein–Hilbert plus GHY action. -/
noncomputable def schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction
    (β M R : ℝ) : ℝ :=
  Real.exp (-schwarzschildRegulatedEinsteinHilbertGHYAction β M R)

/-- Canonical entropy extracted from the Schwarzschild saddle,
`S = βE + log Z`, in natural units (`E = M`). -/
noncomputable def schwarzschildEuclideanEntropy (M : ℝ) : ℝ :=
  schwarzschildEuclideanPeriod M * M +
    Real.log (schwarzschildEuclideanPartitionFunction M)

/-- The Schwarzschild Euclidean period is exactly the Hawking inverse
temperature. This specializes the affine–Killing geometric period theorem to
the Schwarzschild surface gravity. -/
lemma schwarzschildEuclideanPeriod_eq_hawkingBeta
    (M : ℝ) (hM : 0 < M) :
    schwarzschildEuclideanPeriod M =
      hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 :=
  imaginary_period_is_hawking_beta _
    (ne_of_gt (schwarzschildSurfaceGravity_pos one_pos hM one_pos))

/-- In natural units the Schwarzschild imaginary-time period is
`β_H = 8πM`. -/
lemma schwarzschildEuclideanPeriod_eq_eight_pi_mul_mass
    (M : ℝ) (hM : 0 < M) :
    schwarzschildEuclideanPeriod M = 8 * Real.pi * M := by
  unfold schwarzschildEuclideanPeriod schwarzschildSurfaceGravity
  field_simp
  ring

/-- The inverse Euclidean period is the Hawking temperature. -/
lemma one_div_schwarzschildEuclideanPeriod_eq_hawkingTemperature
    (M : ℝ) (hM : 0 < M) :
    1 / schwarzschildEuclideanPeriod M =
      hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 := by
  rw [schwarzschildEuclideanPeriod_eq_hawkingBeta M hM]
  unfold hawkingBeta
  have hT : hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 ≠ 0 :=
    ne_of_gt (hawkingTemperature_pos 1 _ 1 1 one_pos
      (schwarzschildSurfaceGravity_pos one_pos hM one_pos) one_pos one_pos)
  field_simp

/-- At the geometrically fixed Hawking period, the metric-derived regulated
GHY action converges to the named Schwarzschild saddle action. This theorem
closes the formerly external step `I_E/ℏ = β_H M/2`. -/
lemma schwarzschildRegulatedEuclideanAction_tendsto_saddleAction
    (M : ℝ) :
    Filter.Tendsto
      (schwarzschildRegulatedEuclideanAction
        (schwarzschildEuclideanPeriod M) M)
      Filter.atTop (nhds (schwarzschildEuclideanSaddleAction M)) := by
  simpa [schwarzschildEuclideanSaddleAction] using
    (schwarzschildRegulatedEuclideanAction_tendsto
      (schwarzschildEuclideanPeriod M) M)

/-- The finite-cutoff gravitational partition functions converge to the
Schwarzschild saddle partition function `exp(-β_H M/2)`. -/
lemma schwarzschildRegulatedEuclideanPartitionFunction_tendsto
    (M : ℝ) :
    Filter.Tendsto
      (schwarzschildRegulatedEuclideanPartitionFunction
        (schwarzschildEuclideanPeriod M) M)
      Filter.atTop (nhds (schwarzschildEuclideanPartitionFunction M)) := by
  have hneg :=
    (schwarzschildRegulatedEuclideanAction_tendsto_saddleAction M).neg
  have hexp :=
    (Real.continuous_exp.tendsto
      (-schwarzschildEuclideanSaddleAction M)).comp hneg
  unfold schwarzschildRegulatedEuclideanPartitionFunction
    schwarzschildEuclideanPartitionFunction
  exact hexp.congr' (Filter.Eventually.of_forall (fun _ => rfl))

/-- At the Hawking period, the complete Einstein–Hilbert plus GHY action
converges to the Schwarzschild saddle action. -/
lemma schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto_saddleAction
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto
      (schwarzschildRegulatedEinsteinHilbertGHYAction
        (schwarzschildEuclideanPeriod M) M)
      Filter.atTop (nhds (schwarzschildEuclideanSaddleAction M)) := by
  simpa [schwarzschildEuclideanSaddleAction] using
    (schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto
      (schwarzschildEuclideanPeriod M) M hM)

/-- The complete finite-cutoff gravitational partition function converges
to `exp(-β_H M/2)`. -/
lemma schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction_tendsto
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto
      (schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction
        (schwarzschildEuclideanPeriod M) M)
      Filter.atTop (nhds (schwarzschildEuclideanPartitionFunction M)) := by
  have hneg :=
    (schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto_saddleAction
      M hM).neg
  have hexp :=
    (Real.continuous_exp.tendsto
      (-schwarzschildEuclideanSaddleAction M)).comp hneg
  unfold schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction
    schwarzschildEuclideanPartitionFunction
  exact hexp.congr' (Filter.Eventually.of_forall (fun _ => rfl))

/-- The evaluated Schwarzschild Euclidean saddle action is the Bekenstein
quarter-area entropy in natural units:
`I_E/ℏ = β_H M/2 = A/(4ℓ_P²)`. The proof reuses the existing
Schwarzschild Smarr theorem `T_H S_BH = M/2`. -/
lemma schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt
    (M : ℝ) (hM : 0 < M) :
    schwarzschildEuclideanSaddleAction M =
      bekensteinTauEnt (schwarzschildArea M 1 1) 1 := by
  have hT :
      hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 ≠ 0 :=
    ne_of_gt (hawkingTemperature_pos 1 _ 1 1 one_pos
      (schwarzschildSurfaceGravity_pos one_pos hM one_pos) one_pos one_pos)
  have hSmarr :
      hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 *
          bekensteinTauEnt (schwarzschildArea M 1 1) 1 =
        M / 2 := by
    simpa using
      (hawking_bekensteinTauEnt_smarr
        (M := M) (G := 1) (ℏ := 1) (c := 1) (kB := 1) (ℓP := 1)
        hM.ne' one_ne_zero one_ne_zero one_ne_zero one_ne_zero (by norm_num))
  calc
    schwarzschildEuclideanSaddleAction M =
        hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 * M / 2 := by
      rw [show schwarzschildEuclideanSaddleAction M =
          schwarzschildEuclideanPeriod M * M / 2 by rfl,
        schwarzschildEuclideanPeriod_eq_hawkingBeta M hM]
    _ = hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 *
        (hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 *
          bekensteinTauEnt (schwarzschildArea M 1 1) 1) := by
      rw [hSmarr]
      ring
    _ = (hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1 *
          hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1) *
        bekensteinTauEnt (schwarzschildArea M 1 1) 1 := by ring
    _ = bekensteinTauEnt (schwarzschildArea M 1 1) 1 := by
      rw [hawking_temperature_mul_beta _ _ _ _ hT, one_mul]

/-- The logarithm of the positive Euclidean saddle partition function is
minus the dimensionless on-shell action. -/
lemma log_schwarzschildEuclideanPartitionFunction (M : ℝ) :
    Real.log (schwarzschildEuclideanPartitionFunction M) =
      -schwarzschildEuclideanSaddleAction M := by
  unfold schwarzschildEuclideanPartitionFunction
  exact Real.log_exp _

/-- The entropy extracted from the Euclidean partition function is the
Bekenstein quarter-area entropy:
`β_H M + log Z = A/(4ℓ_P²)`. -/
lemma schwarzschildEuclideanEntropy_eq_bekensteinTauEnt
    (M : ℝ) (hM : 0 < M) :
    schwarzschildEuclideanEntropy M =
      bekensteinTauEnt (schwarzschildArea M 1 1) 1 := by
  calc
    schwarzschildEuclideanEntropy M =
        schwarzschildEuclideanSaddleAction M := by
      rw [show schwarzschildEuclideanEntropy M =
          schwarzschildEuclideanPeriod M * M +
            Real.log (schwarzschildEuclideanPartitionFunction M) by rfl,
        log_schwarzschildEuclideanPartitionFunction]
      unfold schwarzschildEuclideanSaddleAction
      ring
    _ = bekensteinTauEnt (schwarzschildArea M 1 1) 1 :=
      schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt M hM

/-- **[Gibbons–Hawking Euclidean Schwarzschild thermodynamics].**
For positive Schwarzschild mass in natural units:

1. the complex affine parameter is periodic in imaginary Killing time;
2. that period is the Hawking inverse temperature and its inverse is `T_H`;
3. the saddle partition function obeys `log Z = -I_E/ℏ`;
4. the evaluated action and the entropy extracted from `βE + log Z` both
   equal the Bekenstein quarter-area entropy.

The theorem composes the full Bekenstein 1980/Gibbons–Hawking chain while
leaving the on-shell gravitational action evaluation visible in
`schwarzschildEuclideanSaddleAction`. -/
theorem gibbonsHawking_schwarzschild_euclidean_thermodynamics
    (M : ℝ) (hM : 0 < M) :
    (∀ v : ℂ,
      complexAffineParameter (schwarzschildSurfaceGravity 1 M 1)
          (v + 2 * (Real.pi : ℂ) * Complex.I /
            (schwarzschildSurfaceGravity 1 M 1 : ℂ)) =
        complexAffineParameter (schwarzschildSurfaceGravity 1 M 1) v)
      ∧ schwarzschildEuclideanPeriod M =
        hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1
      ∧ 1 / schwarzschildEuclideanPeriod M =
        hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1
      ∧ Real.log (schwarzschildEuclideanPartitionFunction M) =
        -schwarzschildEuclideanSaddleAction M
      ∧ schwarzschildEuclideanSaddleAction M =
        bekensteinTauEnt (schwarzschildArea M 1 1) 1
      ∧ schwarzschildEuclideanEntropy M =
        bekensteinTauEnt (schwarzschildArea M 1 1) 1 :=
  ⟨fun v => affineParameter_imaginary_period _ v (by
      exact_mod_cast
        (ne_of_gt (schwarzschildSurfaceGravity_pos one_pos hM one_pos))),
    schwarzschildEuclideanPeriod_eq_hawkingBeta M hM,
    one_div_schwarzschildEuclideanPeriod_eq_hawkingTemperature M hM,
    log_schwarzschildEuclideanPartitionFunction M,
    schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt M hM,
    schwarzschildEuclideanEntropy_eq_bekensteinTauEnt M hM⟩

/-- **[Metric-derived Gibbons–Hawking Euclidean Schwarzschild chain].**
For positive Schwarzschild mass, this strengthens
`gibbonsHawking_schwarzschild_euclidean_thermodynamics` with the geometric
evaluation that the earlier theorem used as its named saddle:

1. the four-metric and induced radial-boundary determinants are computed;
2. the exact Schwarzschild bulk Ricci tensor vanishes, supplying the static
   Wick-continued vacuum bulk datum;
3. the boundary mean curvature is obtained from the metric's Christoffel
   symbols;
4. the reference-subtracted GHY cutoff action converges to `β_H M/2`;
5. its exponential converges to the saddle partition function;
6. the established period–temperature–area-entropy chain follows.

Thus `I_E/ℏ = β_H M/2` is linked to the repository's exact Schwarzschild
metric and generic GHY infrastructure, rather than remaining an unevaluated
input to the thermodynamic identities. -/
theorem gibbonsHawking_metricDerived_schwarzschild_euclidean_thermodynamics
    (M : ℝ) (hM : 0 < M) :
    (∀ (R sinTheta : ℝ), schwF M R ≠ 0 →
      (euclideanSchwarzschildMetric M R sinTheta).det =
        R ^ 4 * sinTheta ^ 2)
      ∧ (∀ (R sinTheta : ℝ),
        (euclideanSchwarzschildBoundaryMetric M R sinTheta).det =
          schwF M R * R ^ 4 * sinTheta ^ 2)
      ∧ (∀ (R sinTheta cosTheta : ℝ),
        R ≠ 0 → sinTheta ≠ 0 → schwF M R ≠ 0 →
        ∀ μ ν : Fin 4,
          ricciFromConnection
              (christoffel (schwF M R) (schwDf M R)
                R sinTheta cosTheta)
              (connDeriv (schwF M R) (schwDf M R) (schwDdf M R)
                R sinTheta cosTheta) μ ν = 0)
      ∧ (∀ R : ℝ, 0 < R → 2 * M < R →
        schwarzschildEuclideanBoundaryMeanCurvatureFromMetric M R =
          2 * Real.sqrt (schwF M R) / R +
            schwDf M R / (2 * Real.sqrt (schwF M R)))
      ∧ Filter.Tendsto
        (schwarzschildRegulatedEuclideanAction
          (schwarzschildEuclideanPeriod M) M)
        Filter.atTop (nhds (schwarzschildEuclideanSaddleAction M))
      ∧ Filter.Tendsto
        (schwarzschildRegulatedEuclideanPartitionFunction
          (schwarzschildEuclideanPeriod M) M)
        Filter.atTop (nhds (schwarzschildEuclideanPartitionFunction M))
      ∧ ((∀ v : ℂ,
          complexAffineParameter (schwarzschildSurfaceGravity 1 M 1)
              (v + 2 * (Real.pi : ℂ) * Complex.I /
                (schwarzschildSurfaceGravity 1 M 1 : ℂ)) =
            complexAffineParameter (schwarzschildSurfaceGravity 1 M 1) v)
        ∧ schwarzschildEuclideanPeriod M =
          hawkingBeta 1 (schwarzschildSurfaceGravity 1 M 1) 1 1
        ∧ 1 / schwarzschildEuclideanPeriod M =
          hawkingTemperature 1 (schwarzschildSurfaceGravity 1 M 1) 1 1
        ∧ Real.log (schwarzschildEuclideanPartitionFunction M) =
          -schwarzschildEuclideanSaddleAction M
        ∧ schwarzschildEuclideanSaddleAction M =
          bekensteinTauEnt (schwarzschildArea M 1 1) 1
        ∧ schwarzschildEuclideanEntropy M =
          bekensteinTauEnt (schwarzschildArea M 1 1) 1) :=
  ⟨fun R sinTheta hf => euclideanSchwarzschildMetric_det M R sinTheta hf,
    euclideanSchwarzschildBoundaryMetric_det M,
    fun R sinTheta cosTheta hR hsin hf μ ν =>
      schwarzschild_ricci_eq_zero M R sinTheta cosTheta hR hsin hf μ ν,
    fun R hR hMR =>
      schwarzschildEuclideanBoundaryMeanCurvatureFromMetric_eq M R
        (schwF_pos_of_two_mul_lt M R hR hMR) hR.ne',
    schwarzschildRegulatedEuclideanAction_tendsto_saddleAction M,
    schwarzschildRegulatedEuclideanPartitionFunction_tendsto M,
    gibbonsHawking_schwarzschild_euclidean_thermodynamics M hM⟩

/-- **[Complete Einstein–Hilbert plus GHY Schwarzschild saddle].**
This capstone closes the vacuum bulk step left implicit in the boundary-only
evaluation:

* the Euclidean metric has a proved inverse;
* the static Wick continuation of the exact metric-derived Ricci tensor and
  its Euclidean scalar trace vanish;
* the actual continuum radial Einstein–Hilbert bulk integral is zero;
* the complete `I_EH + I_GHY` cutoff action converges to `β_H M/2`;
* its partition function converges to the established Schwarzschild saddle;
* that saddle action and its canonical entropy equal the Bekenstein
  quarter-area entropy.

The theorem is classical and on-shell. It still does not construct the
gauge-fixed gravitational functional measure or loop determinants. -/
theorem gibbonsHawking_completeEinsteinHilbertGHY_schwarzschild_saddle
    (M : ℝ) (hM : 0 < M) :
    (∀ (R sinTheta cosTheta : ℝ),
      R ≠ 0 → sinTheta ≠ 0 → schwF M R ≠ 0 →
      euclideanSchwarzschildMetric M R sinTheta *
          euclideanSchwarzschildMetricInv M R sinTheta = 1
        ∧ euclideanSchwarzschildRicciFromMetric
            M R sinTheta cosTheta = 0
        ∧ euclideanSchwarzschildScalarCurvatureFromMetric
            M R sinTheta cosTheta = 0)
      ∧ (∀ (β R : ℝ),
        schwarzschildRegulatedEuclideanBulkAction β M R = 0)
      ∧ Filter.Tendsto
        (schwarzschildRegulatedEinsteinHilbertGHYAction
          (schwarzschildEuclideanPeriod M) M)
        Filter.atTop (nhds (schwarzschildEuclideanSaddleAction M))
      ∧ Filter.Tendsto
        (schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction
          (schwarzschildEuclideanPeriod M) M)
        Filter.atTop (nhds (schwarzschildEuclideanPartitionFunction M))
      ∧ schwarzschildEuclideanSaddleAction M =
        bekensteinTauEnt (schwarzschildArea M 1 1) 1
      ∧ schwarzschildEuclideanEntropy M =
        bekensteinTauEnt (schwarzschildArea M 1 1) 1 :=
  ⟨fun R sinTheta cosTheta hR hs hf =>
      ⟨euclideanSchwarzschildMetric_mul_inv M R sinTheta hf hR hs,
        euclideanSchwarzschildRicciFromMetric_eq_zero
          M R sinTheta cosTheta hR hs hf,
        euclideanSchwarzschildScalarCurvatureFromMetric_eq_zero
          M R sinTheta cosTheta hR hs hf⟩,
    fun β R => schwarzschildRegulatedEuclideanBulkAction_eq_zero
      β M R hM,
    schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto_saddleAction
      M hM,
    schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction_tendsto
      M hM,
    schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt M hM,
    schwarzschildEuclideanEntropy_eq_bekensteinTauEnt M hM⟩


/-! ## ZIL metadata -/

/-- Link found by `#zil_link`: `comptonTemperature` is `schwarzschildEuclideanPeriod` under `m ↦ M` with conversion `kB^-1 · c^2` and prescription `× 1/16 · π^-2`. -/
theorem comptonTemperature_eq_schwarzschildEuclideanPeriod_scaled (m c kB : ℝ)
    (hm : m ≠ 0) :
    Physlib.Thermodynamics.comptonTemperature m c kB
      = ((1 / 16 : ℝ) * c ^ 2 / (kB * Real.pi ^ 2)) * Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanPeriod m := by
  unfold Physlib.Thermodynamics.comptonTemperature Physlib.Thermodynamics.deBroglieTemperature
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy.schwarzschildEuclideanPeriod
    Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity
  field_simp
  ring

/- ZIL-BEGIN -/

zil attach schwarzschildEuclideanPeriod_eq_hawkingBeta where
  formalizes @ "claim:schwarzschild-euclidean-period-is-hawking-inverse-temperature",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:imaginary-killing-time-period-is-hawking-inverse-temperature",
  epistemic_status @ "conditional-model",
  caveat @ "claim:natural-units-and-positive-schwarzschild-mass"

zil attach schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt where
  formalizes @ "claim:schwarzschild-euclidean-saddle-action-is-bekenstein-quarter-area-entropy",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  requires @ "claim:metric-derived-schwarzschild-ghy-action-converges-to-beta-M-over-two",
  requires @ "claim:smarr-relation-hawking-temperature-times-bekenstein-entropic-time-is-half-mass-energy",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-natural-unit-asymptotically-flat-saddle-with-flat-reference-subtraction"

zil attach euclideanSchwarzschildMetric_det where
  formalizes @ "claim:euclidean-schwarzschild-metric-determinant-is-r-four-sine-squared",
  requires @ "claim:schwarzschild-lapse-is-nonzero-away-from-the-horizon",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:schwarzschild-coordinate-chart-away-from-the-horizon"

zil attach schwarzschild_ricci_eq_zero where
  formalizes @ "claim:schwarzschild-vacuum-bulk-ricci-flat-from-metric",
  supported_by @ "paper:schwarzschild-vacuum-solution",
  requires @ "claim:schwarzschild-metric-to-christoffel-carrier",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:coordinate-chart-away-from-r-zero-polar-axis-and-horizon"

zil attach euclideanSchwarzschildRicciFromMetric_eq_zero where
  formalizes @ "claim:static-wick-continued-metric-derived-schwarzschild-ricci-tensor-vanishes",
  requires @ "claim:schwarzschild-vacuum-bulk-ricci-flat-from-metric",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:explicit-static-schwarzschild-wick-continuation-not-a-general-curved-wick-naturality-theorem"

zil attach euclideanSchwarzschildScalarCurvatureFromMetric_eq_zero where
  formalizes @ "claim:euclidean-schwarzschild-scalar-curvature-from-metric-vanishes",
  requires @ "claim:static-wick-continued-metric-derived-schwarzschild-ricci-tensor-vanishes",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:regular-schwarzschild-coordinate-domain"

zil attach schwarzschildRegulatedEuclideanBulkAction_eq_zero where
  formalizes @ "claim:continuum-euclidean-schwarzschild-einstein-hilbert-bulk-action-vanishes",
  requires @ "claim:euclidean-schwarzschild-scalar-curvature-from-metric-vanishes",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  epistemic_status @ "conditional-model",
  caveat @ "claim:positive-mass-exterior-radial-integral-after-time-circle-and-sphere-integration"

zil attach schwarzschildEuclideanBoundaryMeanCurvatureFromMetric_eq where
  formalizes @ "claim:euclidean-schwarzschild-radial-boundary-mean-curvature-from-metric",
  requires @ "claim:schwarzschild-metric-to-christoffel-carrier",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "mathematical-identity",
  caveat @ "claim:exterior-radial-boundary-with-positive-schwarzschild-lapse"

zil attach schwarzschildRegulatedEuclideanAction_tendsto where
  formalizes @ "claim:metric-derived-schwarzschild-ghy-action-converges-to-beta-M-over-two",
  derives @ "claim:schwarzschild-euclidean-saddle-action-beta-M-over-two",
  requires @ "claim:euclidean-schwarzschild-radial-boundary-mean-curvature-from-metric",
  requires @ "claim:schwarzschild-vacuum-bulk-ricci-flat-from-metric",
  requires @ "claim:flat-reference-subtracted-ghy-boundary-action",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-natural-unit-static-wick-continued-asymptotically-flat-saddle-with-flat-reference-subtraction"

zil attach schwarzschildRegulatedEuclideanPartitionFunction_tendsto where
  formalizes @ "claim:regulated-euclidean-schwarzschild-partition-function-converges-to-saddle",
  requires @ "claim:metric-derived-schwarzschild-ghy-action-converges-to-beta-M-over-two",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "conditional-model",
  caveat @ "claim:saddle-exponential-only-no-functional-measure-or-loop-determinants"

zil attach schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto where
  formalizes @ "claim:complete-einstein-hilbert-plus-ghy-schwarzschild-action-converges-to-beta-M-over-two",
  derives @ "claim:schwarzschild-euclidean-saddle-action-beta-M-over-two",
  requires @ "claim:continuum-euclidean-schwarzschild-einstein-hilbert-bulk-action-vanishes",
  requires @ "claim:metric-derived-schwarzschild-ghy-action-converges-to-beta-M-over-two",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-positive-mass-natural-unit-static-schwarzschild-saddle"

zil attach schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction_tendsto where
  formalizes @ "claim:complete-einstein-hilbert-plus-ghy-partition-function-converges-to-schwarzschild-saddle",
  requires @ "claim:complete-einstein-hilbert-plus-ghy-schwarzschild-action-converges-to-beta-M-over-two",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-saddle-exponential-not-a-gauge-fixed-gravitational-functional-integral"

zil attach schwarzschildEuclideanEntropy_eq_bekensteinTauEnt where
  formalizes @ "claim:euclidean-schwarzschild-partition-function-yields-bekenstein-entropy",
  requires @ "claim:schwarzschild-euclidean-saddle-action-is-bekenstein-quarter-area-entropy",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:saddle-partition-function-only-no-gravitational-functional-measure-or-loop-corrections"

zil attach gibbonsHawking_schwarzschild_euclidean_thermodynamics where
  formalizes @ "claim:gibbons-hawking-period-partition-temperature-entropy-chain-for-schwarzschild",
  requires @ "claim:schwarzschild-euclidean-period-is-hawking-inverse-temperature",
  requires @ "claim:schwarzschild-euclidean-saddle-action-is-bekenstein-quarter-area-entropy",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:exact-natural-unit-saddle-chain-not-a-construction-of-the-gravitational-path-integral"

zil attach gibbonsHawking_metricDerived_schwarzschild_euclidean_thermodynamics where
  formalizes @ "claim:metric-derived-gibbons-hawking-schwarzschild-euclidean-thermodynamics",
  derives @ "claim:gibbons-hawking-period-partition-temperature-entropy-chain-for-schwarzschild",
  requires @ "claim:euclidean-schwarzschild-metric-determinant-is-r-four-sine-squared",
  requires @ "claim:euclidean-schwarzschild-radial-boundary-mean-curvature-from-metric",
  requires @ "claim:metric-derived-schwarzschild-ghy-action-converges-to-beta-M-over-two",
  requires @ "claim:regulated-euclidean-schwarzschild-partition-function-converges-to-saddle",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-natural-unit-asymptotically-flat-saddle-no-functional-measure-gauge-fixing-or-loop-corrections"

zil attach gibbonsHawking_completeEinsteinHilbertGHY_schwarzschild_saddle where
  formalizes @ "claim:complete-einstein-hilbert-plus-ghy-schwarzschild-euclidean-saddle-and-entropy-chain",
  derives @ "claim:metric-derived-gibbons-hawking-schwarzschild-euclidean-thermodynamics",
  requires @ "claim:static-wick-continued-metric-derived-schwarzschild-ricci-tensor-vanishes",
  requires @ "claim:continuum-euclidean-schwarzschild-einstein-hilbert-bulk-action-vanishes",
  requires @ "claim:complete-einstein-hilbert-plus-ghy-schwarzschild-action-converges-to-beta-M-over-two",
  requires @ "claim:complete-einstein-hilbert-plus-ghy-partition-function-converges-to-schwarzschild-saddle",
  supported_by @ "paper:gibbons-hawking-1977-euclidean-gravity",
  supported_by @ "paper:hawking-horowitz-1996-gravitational-action-surface-terms",
  supported_by @ "paper:bekenstein-1980-black-hole-thermodynamics",
  epistemic_status @ "conditional-model",
  caveat @ "claim:classical-on-shell-saddle-with-explicit-static-wick-continuation-no-functional-measure-gauge-fixing-or-loop-determinants"

zil_file_contract physlib.kayWaldModeFreeEnergy where
  promises "Single-mode Hawking Gibbs thermodynamics and the complete metric-derived Euclidean Schwarzschild saddle chain: the Euclidean metric has a proved inverse; the static Wick continuation of the exact metric-derived Ricci tensor and its Euclidean scalar trace vanish; the restricted continuum Einstein-Hilbert bulk integral is zero; the radial mean curvature is computed from the metric connection; the complete Einstein-Hilbert plus reference-subtracted GHY cutoff action converges to beta times mass over two; affine imaginary-time periodicity fixes the Hawking inverse temperature; and beta times mass plus log Z equals the Bekenstein quarter-area entropy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Relativity.SemiClassical.hawkingTemperature",
    "lean:Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity",
    "lean:Physlib.Thermodynamics.bekensteinTauEnt",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.metric",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.schwarzschild_ricci_eq_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad.ricciScalarContraction",
    "lean:Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm.ghySurfaceTerm",
    "lean:MeasureTheory.integral",
    "lean:Real.exp", "lean:Real.log"]
  forbids_substitutes ["constructing the gravitational functional-integral measure",
    "claiming gauge-fixed one-loop determinants from the classical GHY saddle",
    "claiming loop-corrected black-hole entropy from a classical saddle"]
  witnessed_by [gibbs_relation, hawking_gibbs_relation,
    euclideanSchwarzschildMetric_det,
    euclideanSchwarzschildMetric_mul_inv,
    euclideanSchwarzschildBoundaryMetric_det,
    euclideanSchwarzschildRicciFromMetric_eq_zero,
    euclideanSchwarzschildScalarCurvatureFromMetric_eq_zero,
    schwarzschildRegulatedEuclideanBulkAction_eq_zero,
    schwarzschildEuclideanBoundaryMeanCurvatureFromMetric_eq,
    schwarzschildRegulatedEuclideanAction_tendsto,
    schwarzschildRegulatedEinsteinHilbertGHYAction_tendsto,
    schwarzschildRegulatedEuclideanAction_tendsto_saddleAction,
    schwarzschildRegulatedEuclideanPartitionFunction_tendsto,
    schwarzschildRegulatedEinsteinHilbertGHYPartitionFunction_tendsto,
    schwarzschildEuclideanPeriod_eq_hawkingBeta,
    schwarzschildEuclideanSaddleAction_eq_bekensteinTauEnt,
    schwarzschildEuclideanEntropy_eq_bekensteinTauEnt,
    gibbonsHawking_schwarzschild_euclidean_thermodynamics,
    gibbonsHawking_metricDerived_schwarzschild_euclidean_thermodynamics,
    gibbonsHawking_completeEinsteinHilbertGHY_schwarzschild_saddle]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy

end
