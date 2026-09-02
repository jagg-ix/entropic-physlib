/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
meta import Zil

/-!
# Timelike entanglement entropy in CFT2 and AdS3

This module formalizes the universal analytic-continuation core of Doi, Harper,
Mollabashi, Takayanagi, and Taki, *Timelike entanglement entropy*, JHEP 05
(2023) 052 (arXiv:2302.11695), reusing the repository's Ryu--Takayanagi and
Brown--Henneaux carriers.

* The Wick-rotated Poincare-AdS3 hyperbola `t(z) = sqrt(z^2 + T^2)` has the
  exact two-branch Lorentzian line density of the paper's Eqs. (3.3)--(3.4).
* The principal complex logarithm of the negative squared interval produces
  the universal `i pi c / 6` contribution of Eqs. (2.3)--(2.4).
* Eq. (2.3) is proved for a general timelike Minkowski separation, rather than
  only for a purely temporal interval.
* The vacuum line, circle, and finite-temperature formulas reduce in real part
  to the existing CFT2 entropy carriers, while their imaginary part is fixed.
* Brown--Henneaux identifies that imaginary contribution with the area entropy
  of the global-AdS3 timelike geodesic of length `i pi R`.
* In a finite common energy eigenbasis, the two-state thermofield dyad is
  constructed, its partial trace is the normalized non-Hermitian reduced
  transition matrix of Eqs. (1.4) and (2.20)--(2.26), and its diagonal spectral
  pseudo entropy realizes Eq. (1.5).
* The imaginary-temperature weights reduce at zero real-time separation to
  the existing TFD/Gibbs weights and to the repository's Nagao--Nielsen
  complex-action damping carrier.
* Similarity transport extends the spectral pseudo entropy to every supplied
  finite diagonalizable transition matrix, proves its basis independence, and
  identifies its Q-normal structure.
* The higher-dimensional spherical timelike surface coefficient of Eq. (4.17)
  is positive and reduces exactly to the AdS3 imaginary geodesic term.

## Honest scope

These are exact scalar CFT2 and pointwise AdS3 identities on the principal-log
branch. The operator layer proves the paper's finite diagonal sector and its
similarity orbit under a supplied invertible eigenbasis, including nonnormal
diagonalizable transition matrices. Its logarithm is the transported principal
spectral logarithm; defective matrices, an intrinsic arbitrary-matrix logarithm,
infinite/type-III transition operators, and replica twist fields remain outside
scope. The pointwise bulk density is
proved, but global stationarity, homology, saddle selection, and the improper
radial integral remain separate. The entropic-time bridge below is conditional
on identifying `S_I = ℏ Im(S_pseudo)`; it does not claim that the universal
imaginary part alone operationally derives physical time. Indeed, the module
proves that this constant universal term cannot itself be a nontrivial clock
trajectory; an independent imaginary-energy calibration is required. BTZ shocks,
higher-dimensional strips, and the dS/CFT continuation remain outside scope.

## Reference

* K. Doi, J. Harper, A. Mollabashi, T. Takayanagi, Y. Taki,
  JHEP 05 (2023) 052, arXiv:2302.11695.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein

/-!

## A. Pointwise continuum geometry of the timelike AdS3 hyperbola

-/

/-- The Wick-rotated Poincare-AdS3 branch `t(z) = sqrt(z^2 + T^2)`. -/
noncomputable def timelikePoincareTime (T z : ℝ) : ℝ :=
  Real.sqrt (z ^ 2 + T ^ 2)

/-- Its Lorentzian radial speed squared `1 - (dt/dz)^2`. -/
noncomputable def timelikePoincareLorentzSpeedSq (T z : ℝ) : ℝ :=
  1 - (z / timelikePoincareTime T z) ^ 2

/-- The two-branch Poincare line density, including the AdS radius `R`. -/
noncomputable def timelikePoincareLineDensity (R T z : ℝ) : ℝ :=
  2 * R * Real.sqrt (timelikePoincareLorentzSpeedSq T z) / z

/-- The pulled-back Lorentzian speed is `T^2 / (z^2 + T^2)`. -/
@[zil_level bridge_theorem]
lemma timelikePoincareLorentzSpeedSq_eq (T z : ℝ) (hT : 0 < T) :
    timelikePoincareLorentzSpeedSq T z = T ^ 2 / (z ^ 2 + T ^ 2) := by
  have hsum : 0 < z ^ 2 + T ^ 2 := by positivity
  have hsqrt : Real.sqrt (z ^ 2 + T ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsum)
  unfold timelikePoincareLorentzSpeedSq timelikePoincareTime
  rw [div_pow]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hsum.le]
  ring

/-- **Doi et al. Eqs. (3.3)--(3.4), pointwise continuum core.** The
Wick-rotated hyperbola has two-branch line density
`2 R T / (z sqrt(z^2 + T^2))`. -/
@[zil_level physical_theorem]
theorem timelikePoincareLineDensity_eq (R T z : ℝ)
    (hT : 0 < T) (hz : 0 < z) :
    timelikePoincareLineDensity R T z =
      2 * R * T / (z * Real.sqrt (z ^ 2 + T ^ 2)) := by
  have hsum : 0 < z ^ 2 + T ^ 2 := by positivity
  unfold timelikePoincareLineDensity
  rw [timelikePoincareLorentzSpeedSq_eq T z hT,
    Real.sqrt_div (sq_nonneg T), Real.sqrt_sq_eq_abs, abs_of_pos hT]
  field_simp [ne_of_gt hz, ne_of_gt (Real.sqrt_pos.2 hsum)]

/-!

## B. Principal-log analytic continuation

-/

/-- The timelike CFT2 entropy obtained from the principal logarithm of the
negative squared dimensionless interval ratio. -/
noncomputable def timelikeCFTEntropyFromRatio (c q : ℝ) : ℂ :=
  (c / 6 : ℂ) * Complex.log (-((q ^ 2 : ℝ) : ℂ))

/-- On the principal branch, `Log(-q^2) = 2 log q + i pi` for `q > 0`. -/
@[zil_level bridge_theorem]
lemma complexLog_neg_sq (q : ℝ) (hq : 0 < q) :
    Complex.log (-((q ^ 2 : ℝ) : ℂ)) =
      (2 * Real.log q : ℝ) + (Real.pi : ℂ) * Complex.I := by
  calc
    Complex.log (-((q ^ 2 : ℝ) : ℂ)) =
        Complex.log (((q ^ 2 : ℝ) : ℂ) * (-1 : ℂ)) := by ring_nf
    _ = (Real.log (q ^ 2) : ℂ) + Complex.log (-1 : ℂ) :=
      Complex.log_ofReal_mul (sq_pos_of_pos hq) (by norm_num)
    _ = (2 * Real.log q : ℝ) + (Real.pi : ℂ) * Complex.I := by
      rw [Complex.log_neg_one, Real.log_pow]
      norm_num

/-- **Doi et al. Eq. (2.3).** Analytic continuation splits into the ordinary
logarithmic entropy and the universal imaginary term `i pi c / 6`. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyFromRatio_eq (c q : ℝ) (hq : 0 < q) :
    timelikeCFTEntropyFromRatio c q =
      ((c / 3) * Real.log q : ℝ) +
        ((Real.pi * c / 6 : ℝ) : ℂ) * Complex.I := by
  rw [timelikeCFTEntropyFromRatio, complexLog_neg_sq q hq]
  push_cast
  ring

/-- The positive proper-length-to-cutoff ratio for a timelike Minkowski
separation `(dt, dx)`. -/
noncomputable def timelikeMinkowskiIntervalRatio (dt dx eps : ℝ) : ℝ :=
  Real.sqrt (dt ^ 2 - dx ^ 2) / eps

/-- The principal-branch CFT2 entropy of a general timelike Minkowski
separation. -/
noncomputable def timelikeCFTEntropyMinkowski (c dt dx eps : ℝ) : ℂ :=
  timelikeCFTEntropyFromRatio c (timelikeMinkowskiIntervalRatio dt dx eps)

/-- **Doi et al. Eq. (2.3), general interval.** For a genuinely timelike
separation, analytic continuation gives the logarithm of its proper length
and the universal imaginary contribution `i pi c / 6`. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyMinkowski_eq (c dt dx eps : ℝ)
    (hgap : 0 < dt ^ 2 - dx ^ 2) (heps : 0 < eps) :
    timelikeCFTEntropyMinkowski c dt dx eps =
      ((c / 3) * Real.log (Real.sqrt (dt ^ 2 - dx ^ 2) / eps) : ℝ) +
        ((Real.pi * c / 6 : ℝ) : ℂ) * Complex.I := by
  unfold timelikeCFTEntropyMinkowski timelikeMinkowskiIntervalRatio
  exact timelikeCFTEntropyFromRatio_eq c _
    (div_pos (Real.sqrt_pos.2 hgap) heps)

/-!

## C. Vacuum, circle, and finite-temperature CFT2 formulas

-/

/-- The purely timelike vacuum-line interval entropy of Eq. (2.4). -/
noncomputable def timelikeCFTEntropyVacuumLine (c T eps : ℝ) : ℂ :=
  timelikeCFTEntropyFromRatio c (T / eps)

/-- Eq. (2.4): the real part is the existing vacuum-line CFT entropy. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyVacuumLine_eq (c T eps : ℝ)
    (hT : 0 < T) (heps : 0 < eps) :
    timelikeCFTEntropyVacuumLine c T eps =
      (cftEntropyVacuumLine c T eps : ℂ) +
        ((Real.pi * c / 6 : ℝ) : ℂ) * Complex.I := by
  unfold timelikeCFTEntropyVacuumLine
  rw [timelikeCFTEntropyFromRatio_eq c (T / eps) (div_pos hT heps)]
  rfl

/-- The real part of timelike vacuum entropy is ordinary spatial interval entropy. -/
@[zil_level bridge_theorem]
theorem timelikeCFTEntropyVacuumLine_re (c T eps : ℝ)
    (hT : 0 < T) (heps : 0 < eps) :
    (timelikeCFTEntropyVacuumLine c T eps).re =
      cftEntropyVacuumLine c T eps := by
  rw [timelikeCFTEntropyVacuumLine_eq c T eps hT heps]
  simp

/-- The imaginary part is independent of interval size and cutoff. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyVacuumLine_im (c T eps : ℝ)
    (hT : 0 < T) (heps : 0 < eps) :
    (timelikeCFTEntropyVacuumLine c T eps).im = Real.pi * c / 6 := by
  rw [timelikeCFTEntropyVacuumLine_eq c T eps hT heps]
  simp

/-- The purely timelike interval entropy for a CFT2 on a circle. -/
noncomputable def timelikeCFTEntropyCircle (c T R eps : ℝ) : ℂ :=
  timelikeCFTEntropyFromRatio c
    (R / (Real.pi * eps) * Real.sin (Real.pi * T / R))

/-- **Eqs. (2.7)/(3.6).** The global-circle analytic continuation has the
existing Calabrese--Cardy circle entropy as real part and `i pi c / 6` as
imaginary part. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyCircle_eq (c T R eps : ℝ)
    (hT : 0 < T) (hTR : T < R) (hR : 0 < R) (heps : 0 < eps) :
    timelikeCFTEntropyCircle c T R eps =
      (cftEntropy c T R eps : ℂ) +
        ((Real.pi * c / 6 : ℝ) : ℂ) * Complex.I := by
  unfold timelikeCFTEntropyCircle
  rw [timelikeCFTEntropyFromRatio_eq]
  · rfl
  · have hanglepos : 0 < Real.pi * T / R :=
      div_pos (mul_pos Real.pi_pos hT) hR
    have hanglelt : Real.pi * T / R < Real.pi := by
      rw [div_lt_iff₀ hR]
      nlinarith [Real.pi_pos]
    exact mul_pos (div_pos hR (mul_pos Real.pi_pos heps))
      (Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt)

/-- The purely timelike finite-temperature CFT2 entropy of Eq. (2.10). -/
noncomputable def timelikeCFTEntropyFiniteT (c T beta eps : ℝ) : ℂ :=
  timelikeCFTEntropyFromRatio c
    (beta / (Real.pi * eps) * Real.sinh (Real.pi * T / beta))

/-- **Doi et al. Eq. (2.10).** The finite-temperature timelike entropy is the
existing BTZ/CFT2 entropy plus the same universal imaginary contribution. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyFiniteT_eq (c T beta eps : ℝ)
    (hT : 0 < T) (hbeta : 0 < beta) (heps : 0 < eps) :
    timelikeCFTEntropyFiniteT c T beta eps =
      (cftEntropyFiniteT c T beta eps : ℂ) +
        ((Real.pi * c / 6 : ℝ) : ℂ) * Complex.I := by
  unfold timelikeCFTEntropyFiniteT
  rw [timelikeCFTEntropyFromRatio_eq]
  · rfl
  · exact mul_pos (div_pos hbeta (mul_pos Real.pi_pos heps))
      (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos hT) hbeta))

/-!

## D. Brown--Henneaux holographic matching

-/

/-- The area-entropy contribution of the global-AdS3 timelike geodesic with
complex length `i pi R`. -/
noncomputable def timelikeAdS3GeodesicImaginaryEntropy (R G : ℝ) : ℂ :=
  Complex.I * (rtAreaEntropy (Real.pi * R) G : ℂ)

/-- Brown--Henneaux turns the timelike-geodesic area term into `i pi c / 6`. -/
@[zil_level bridge_theorem]
theorem timelikeAdS3GeodesicImaginaryEntropy_eq (R G : ℝ) :
    timelikeAdS3GeodesicImaginaryEntropy R G =
      ((Real.pi * brownHenneaux R G / 6 : ℝ) : ℂ) * Complex.I := by
  unfold timelikeAdS3GeodesicImaginaryEntropy rtAreaEntropy brownHenneaux
  push_cast
  field_simp
  ring

/-- **Doi et al. Eqs. (3.1)--(3.6), bulk/boundary match.** At the
Brown--Henneaux central charge, the real CFT logarithm has the spacelike
Poincare-geodesic coefficient `R/(2G)`, while the universal imaginary part is
the RT area entropy of the timelike global-AdS3 geodesic. -/
@[zil_level physical_theorem]
theorem timelikeCFTEntropyVacuumLine_brownHenneaux (R G T eps : ℝ)
    (hT : 0 < T) (heps : 0 < eps) :
    timelikeCFTEntropyVacuumLine (brownHenneaux R G) T eps =
      ((R / (2 * G) * Real.log (T / eps) : ℝ) : ℂ) +
        timelikeAdS3GeodesicImaginaryEntropy R G := by
  rw [timelikeCFTEntropyVacuumLine_eq _ _ _ hT heps,
    timelikeAdS3GeodesicImaginaryEntropy_eq R G]
  unfold cftEntropyVacuumLine brownHenneaux
  push_cast
  field_simp

/-!

## E. Finite thermofield transition operator and pseudo entropy

This is the finite common-energy-eigenbasis sector of Eqs. (1.4) and
(2.20)--(2.26). The second function supplied to `transitionDyad` is already a
bra coefficient; no hidden complex conjugation is inserted.

-/

variable {ι : Type*}

/-- The rank-one bipartite transition dyad associated to diagonal thermofield
ket coefficients `a` and algebraic bra coefficients `b`. -/
noncomputable def transitionDyad [DecidableEq ι] (a b : ι → ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ := fun p q =>
  (if p.1 = p.2 then a p.1 else 0) *
    (if q.1 = q.2 then b q.1 else 0)

/-- Partial trace of the thermofield transition dyad is diagonal with entries
`a_i b_i`. This is the finite-dimensional core of the paper's reduced
transition matrix `τ_A = Tr_B(|ψ⟩⟨φ|/⟨φ|ψ⟩)`. -/
@[zil_level bridge_theorem]
theorem transitionDyad_traceRight [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) :
    (transitionDyad a b).traceRight = Matrix.diagonal (fun i => a i * b i) := by
  ext i j
  change (∑ k,
      (if i = k then a i else 0) * (if j = k then b j else 0)) =
    if i = j then a i * b i else 0
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Ne.symm hki]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · have hjk : j ≠ k := fun hjk => hij (hik.trans hjk.symm)
      simp [hik, hjk]
    · simp [hik]

/-- The normalized complex Boltzmann weight
`exp(i R E_i - delta E_i) / Z`, written using the repository's
Nagao--Nielsen path-weight carrier. -/
noncomputable def timelikeTransitionWeight
    (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) (i : ι) : ℂ :=
  nnPathWeight (R * E i) (delta * E i) 1 / Z

/-- A half-weight whose algebraic square is `timelikeTransitionWeight` before
normalization. It supplies the two thermofield legs of the transition dyad. -/
noncomputable def timelikeTransitionHalfAmplitude
    (E : ι → ℝ) (R delta : ℝ) (i : ι) : ℂ :=
  nnPathWeight (R * E i) (delta * E i) 2

/-- The two half-weights multiply to the full complex-action weight. -/
@[zil_level bridge_theorem]
theorem timelikeTransitionHalfAmplitude_sq
    (E : ι → ℝ) (R delta : ℝ) (i : ι) :
    timelikeTransitionHalfAmplitude E R delta i ^ 2 =
      nnPathWeight (R * E i) (delta * E i) 1 := by
  unfold timelikeTransitionHalfAmplitude nnPathWeight
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The normalized two-state thermofield transition dyad. -/
noncomputable def timelikeTransitionDyad
    [DecidableEq ι] (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  transitionDyad (timelikeTransitionHalfAmplitude E R delta)
    (fun i => timelikeTransitionHalfAmplitude E R delta i / Z)

/-- The paper's finite diagonal reduced transition matrix. -/
noncomputable def timelikeReducedTransition
    [DecidableEq ι] (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (timelikeTransitionWeight E R delta Z)

/-- **Doi et al. Eqs. (1.4), (2.25)--(2.26).** Tracing out the second
thermofield copy produces the claimed reduced transition matrix. -/
@[zil_level physical_theorem]
theorem timelikeTransitionDyad_traceRight
    [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) :
    (timelikeTransitionDyad E R delta Z).traceRight =
      timelikeReducedTransition E R delta Z := by
  rw [timelikeTransitionDyad, transitionDyad_traceRight]
  unfold timelikeReducedTransition timelikeTransitionWeight
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    rw [← mul_div_assoc, ← pow_two, timelikeTransitionHalfAmplitude_sq]
  · simp [hij]

/-- The complex partition-function identity is exactly the normalization
condition `Tr τ_A = 1` in Eq. (1.4). -/
@[zil_level physical_theorem]
theorem timelikeReducedTransition_trace_one
    [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) (hZ : Z ≠ 0)
    (hpartition : ∑ i, nnPathWeight (R * E i) (delta * E i) 1 = Z) :
    (timelikeReducedTransition E R delta Z).trace = 1 := by
  rw [timelikeReducedTransition, Matrix.trace_diagonal]
  simp only [timelikeTransitionWeight, ← Finset.sum_div, hpartition, div_self hZ]

/-- The spectral pseudo entropy of a diagonal transition matrix. This is the
exact finite diagonal specialization of `-Tr(τ log τ)`, not an arbitrary
nonnormal matrix-log API. -/
noncomputable def diagonalPseudoEntropy [Fintype ι] (w : ι → ℂ) : ℂ :=
  -(∑ i, w i * Complex.log (w i))

/-- **Doi et al. Eq. (1.5), diagonal spectral form.** -/
@[zil_level physical_theorem]
theorem diagonalPseudoEntropy_eq_neg_trace [Fintype ι] [DecidableEq ι]
    (w : ι → ℂ) :
    diagonalPseudoEntropy w =
      -(Matrix.diagonal (fun i => w i * Complex.log (w i))).trace := by
  simp [diagonalPseudoEntropy, Matrix.trace_diagonal]

/-- The pseudo entropy of the normalized timelike reduced transition matrix in
the finite common energy eigenbasis. -/
noncomputable def timelikePseudoEntropy [Fintype ι]
    (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) : ℂ :=
  diagonalPseudoEntropy (timelikeTransitionWeight E R delta Z)

/-- The timelike pseudo entropy is the negative trace of the diagonal spectral
functional `w_i log w_i` of the reduced transition matrix. -/
@[zil_level physical_theorem]
theorem timelikePseudoEntropy_eq_neg_trace [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) :
    timelikePseudoEntropy E R delta Z =
      -(Matrix.diagonal (fun i =>
        timelikeTransitionWeight E R delta Z i *
          Complex.log (timelikeTransitionWeight E R delta Z i))).trace := by
  exact diagonalPseudoEntropy_eq_neg_trace _

/-- A non-real diagonal transition eigenvalue certifies that the reduced
transition matrix is not Hermitian, as required by the pseudo-entropy sector. -/
@[zil_level bridge_theorem]
theorem timelikeReducedTransition_not_hermitian
    [DecidableEq ι] (E : ι → ℝ) (R delta : ℝ) (Z : ℂ) (i : ι)
    (hi : star (timelikeTransitionWeight E R delta Z i) ≠
      timelikeTransitionWeight E R delta Z i) :
    ¬(timelikeReducedTransition E R delta Z).IsHermitian := by
  intro hH
  apply hi
  simpa [timelikeReducedTransition] using hH.apply i i

/-!

## F. TFD/KMS, complex action, and the conditional entropic-time dictionary

-/

/-- At zero Lorentzian separation, the complex transition weight reduces to
the existing TFD/Gibbs reduced weight. Thus the paper's imaginary-temperature
transition sector meets the repository's KMS variational carrier on its static
slice. -/
@[zil_level bridge_theorem]
theorem timelikeTransitionWeight_at_R_zero_eq_tfd
    (E : ι → ℝ) (beta Z : ℝ) (i : ι) :
    timelikeTransitionWeight E 0 beta (Z : ℂ) i =
      (tfdReducedWeight E beta Z i : ℂ) := by
  rw [timelikeTransitionWeight, nnPathWeight_eq_phase_mul_damping,
    tfdReducedWeight_eq_gibbsWeight]
  simp

/-- The explicit dictionary `S_I = ℏ Im(S_pseudo)` for the universal
timelike-CFT2 imaginary entropy. This is an interpretation datum, kept separate
from the theorem that computes the imaginary part. -/
noncomputable def timelikeEntropyImaginaryAction (hbar c : ℝ) : ℝ :=
  hbar * (Real.pi * c / 6)

/-- Under the explicit action/entropy dictionary, the repository's entropic
proper time is the paper's universal imaginary pseudo entropy `pi c / 6`. -/
@[zil_level bridge_theorem]
theorem timelikeEntropy_entropicProperTime (hbar c : ℝ) (hh : hbar ≠ 0) :
    entropicProperTime (timelikeEntropyImaginaryAction hbar c) hbar =
      Real.pi * c / 6 := by
  unfold timelikeEntropyImaginaryAction entropicProperTime
  field_simp

/-- The same dictionary makes the universal timelike imaginary entropy the
modulus exponent of the Nagao--Nielsen complex-action path weight. -/
@[zil_level bridge_theorem]
theorem timelikeEntropy_nnWeight_norm (S_R hbar c : ℝ) (hh : hbar ≠ 0) :
    ‖nnPathWeight S_R (timelikeEntropyImaginaryAction hbar c) hbar‖ =
      Real.exp (-(Real.pi * c / 6)) := by
  rw [norm_nnPathWeight]
  unfold timelikeEntropyImaginaryAction
  congr 2
  field_simp

/-!

## G. Finite diagonalizable and nonnormal transition matrices

The paper's reduced transition matrix need not be Hermitian. The repository's
periodic complex-action carrier already represents any supplied finite
diagonalizable operator as `P D P⁻¹`. Transporting both `D` and its principal
spectral logarithm through the same similarity gives a finite matrix-level
pseudo entropy beyond the diagonal presentation.

-/

/-- A finite diagonalizable transition matrix `P diagonal(w) P⁻¹`. -/
noncomputable def diagonalizableTransition [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (w : ι → ℂ) : Matrix ι ι ℂ :=
  mconj P (Matrix.diagonal w)

/-- The principal spectral logarithm transported through the same eigenbasis.
This is well-defined for the supplied diagonalization; it is not a claim that
every complex matrix has a canonical logarithm. -/
noncomputable def diagonalizableTransitionLog [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (w : ι → ℂ) : Matrix ι ι ℂ :=
  mconj P (Matrix.diagonal (fun i => Complex.log (w i)))

/-- Trace is invariant under similarity by an invertible finite matrix. -/
@[zil_level bridge_theorem]
theorem trace_mconj [Fintype ι] [DecidableEq ι]
    (P X : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    (mconj P X).trace = X.trace := by
  unfold mconj
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.nonsing_inv_mul P hP, Matrix.one_mul]

/-- Spectral functional calculus respects the supplied diagonalizing
similarity: `τ log τ = P diagonal(w log w) P⁻¹`. -/
@[zil_level bridge_theorem]
theorem diagonalizableTransition_mul_log [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (w : ι → ℂ) (hP : IsUnit P.det) :
    diagonalizableTransition P w * diagonalizableTransitionLog P w =
      mconj P (Matrix.diagonal (fun i => w i * Complex.log (w i))) := by
  rw [diagonalizableTransition, diagonalizableTransitionLog, mconj_mul P hP,
    Matrix.diagonal_mul_diagonal]

/-- **Finite diagonalizable pseudo entropy.** The operator expression
`-Tr(τ log τ)` equals the diagonal spectral pseudo entropy even when the
transition matrix is non-Hermitian or nonnormal in the original inner product. -/
@[zil_level physical_theorem]
theorem diagonalizablePseudoEntropy_eq [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (w : ι → ℂ) (hP : IsUnit P.det) :
    -(diagonalizableTransition P w * diagonalizableTransitionLog P w).trace =
      diagonalPseudoEntropy w := by
  rw [diagonalizableTransition_mul_log P w hP, trace_mconj P _ hP]
  simp [diagonalPseudoEntropy, Matrix.trace_diagonal]

/-- **Basis independence/uniqueness.** For fixed spectral data, any two
invertible diagonalizing presentations give the same pseudo entropy. -/
@[zil_level bridge_theorem]
theorem diagonalizablePseudoEntropy_basis_independent
    [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (w : ι → ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    -(diagonalizableTransition P w * diagonalizableTransitionLog P w).trace =
      -(diagonalizableTransition Q w * diagonalizableTransitionLog Q w).trace := by
  rw [diagonalizablePseudoEntropy_eq P w hP,
    diagonalizablePseudoEntropy_eq Q w hQ]

/-- The diagonalizable transition is Q-normal in the metric determined by its
eigenbasis. This is the precise complex-action replacement for ordinary
normality of a generally nonnormal transition matrix. -/
@[zil_level bridge_theorem]
theorem diagonalizableTransition_qNormal [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (w : ι → ℂ) (hP : IsUnit P.det) :
    diagonalizableTransition P w *
        qDagger (qMetric P) (diagonalizableTransition P w) =
      qDagger (qMetric P) (diagonalizableTransition P w) *
        diagonalizableTransition P w := by
  simpa [diagonalizableTransition, hamiltonian] using
    hamiltonian_qNormal P w hP

/-!

## H. Operational duration and the constant-imaginary-part no-go

The universal `pi c / 6` is independent of the interval length. It therefore
cannot by itself be a nontrivial clock trajectory. Once an independent positive
imaginary Einstein energy is supplied, however, it fixes a definite duration;
the repository's operational phase-clock theorem then reads that duration as
physical proper time.

-/

/-- Proper-time duration obtained by dividing the timelike imaginary action by
an independently supplied imaginary rest-energy scale. -/
noncomputable def timelikeEntropyCalibratedDuration
    (mI cLight hbar cCFT : ℝ) : ℝ :=
  timelikeEntropyImaginaryAction hbar cCFT / (mI * cLight ^ 2)

/-- Positive imaginary energy and positive CFT central charge give a positive
calibrated duration. -/
@[zil_level bridge_theorem]
theorem timelikeEntropyCalibratedDuration_pos
    (mI cLight hbar cCFT : ℝ)
    (hE : 0 < mI * cLight ^ 2) (hhbar : 0 < hbar) (hcCFT : 0 < cCFT) :
    0 < timelikeEntropyCalibratedDuration mI cLight hbar cCFT := by
  unfold timelikeEntropyCalibratedDuration timelikeEntropyImaginaryAction
  exact div_pos
    (mul_pos hhbar (div_pos (mul_pos Real.pi_pos hcCFT) (by norm_num))) hE

/-- At the calibrated duration the complex-Einstein imaginary action equals
exactly `ℏ` times the paper's universal imaginary pseudo entropy. -/
@[zil_level bridge_theorem]
theorem timelikeEntropyCalibratedDuration_action
    (mR mI cLight hbar cCFT : ℝ) (hE : mI * cLight ^ 2 ≠ 0) :
    entropicActionEinstein mR mI cLight
        (timelikeEntropyCalibratedDuration mI cLight hbar cCFT) =
      timelikeEntropyImaginaryAction hbar cCFT := by
  rw [entropicActionEinstein_eq]
  unfold timelikeEntropyCalibratedDuration
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ hE

/-- **Operational timelike-entropy duration.** With a positive independent
imaginary-energy calibration, the timelike imaginary action is realized by the
complex-Einstein worldline and the already-proved phase-clock inverse reads its
duration as physical proper time. No premise asserts the final clock equality. -/
@[zil_level physical_theorem]
theorem timelikeEntropyCalibratedDuration_operational
    (mR mI cLight hbar cCFT : ℝ)
    (hE : 0 < mI * cLight ^ 2) (hhbar : 0 < hbar) :
    entropicActionEinstein mR mI cLight
        (timelikeEntropyCalibratedDuration mI cLight hbar cCFT) =
        timelikeEntropyImaginaryAction hbar cCFT ∧
      Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance
          (imaginaryEinsteinPhaseClock mI cLight hbar hE hhbar)
          (imaginaryEinsteinEntropyWorldline mR mI cLight hbar hE hhbar)
          0 (timelikeEntropyCalibratedDuration mI cLight hbar cCFT) =
        timelikeEntropyCalibratedDuration mI cLight hbar cCFT := by
  constructor
  · exact timelikeEntropyCalibratedDuration_action _ _ _ _ _ hE.ne'
  · simpa using imaginaryEinstein_entropicTime_eq_physicalProperTime
      mR mI cLight hbar hE hhbar 0
        (timelikeEntropyCalibratedDuration mI cLight hbar cCFT)

/-- Regard only the paper's universal imaginary contribution as an action along
a putative trajectory. Its value is constant by construction. -/
noncomputable def universalTimelikeEntropyActionAlong
    (hbar cCFT : ℝ) (_sigma : ℝ) : ℝ :=
  timelikeEntropyImaginaryAction hbar cCFT

/-- The universal imaginary contribution has zero increment between every two
trajectory parameters. -/
@[zil_level bridge_theorem]
theorem universalTimelikeEntropyActionAlong_increment
    (hbar cCFT : ℝ) (s t : ℝ) :
    universalTimelikeEntropyActionAlong hbar cCFT t -
      universalTimelikeEntropyActionAlong hbar cCFT s = 0 := by
  simp only [universalTimelikeEntropyActionAlong, sub_self]

/-- **No-go for an uncalibrated universal-imaginary clock.** A constant action
cannot obey a nonzero-frequency clock law across distinct parameters. Thus the
paper's universal `pi c / 6` alone does not operationally derive time. -/
@[zil_level physical_theorem]
theorem universalTimelikeEntropyActionAlong_not_clock
    (hbar cCFT omega s t : ℝ)
    (hhbar : hbar ≠ 0) (homega : omega ≠ 0) (hst : s ≠ t) :
    universalTimelikeEntropyActionAlong hbar cCFT t -
        universalTimelikeEntropyActionAlong hbar cCFT s ≠
      hbar * omega * (t - s) := by
  rw [universalTimelikeEntropyActionAlong_increment]
  exact mul_ne_zero (mul_ne_zero hhbar homega) (sub_ne_zero.mpr hst.symm) |>.symm

/-!

## I. Higher-dimensional spherical timelike surface

-/

/-- The dimension-dependent Gamma-function coefficient in Doi et al.
Eq. (4.17), after separating the AdS-radius, Newton, and hyperbolic-volume
prefactor. -/
noncomputable def higherDimTimelikeSurfaceCoefficient (d : ℝ) : ℝ :=
  Real.sqrt Real.pi * Real.Gamma ((d - 1) / 2) /
    (2 * Real.Gamma (d / 2))

/-- The purely imaginary timelike-surface entropy contribution of Eq. (4.17),
with `areaPrefactor = R_AdS^(d-1) Vol(H^(d-2))/(4 G_N)`. -/
noncomputable def higherDimTimelikeSurfaceEntropy
    (areaPrefactor d : ℝ) : ℂ :=
  Complex.I * (areaPrefactor * higherDimTimelikeSurfaceCoefficient d : ℂ)

/-- The higher-dimensional coefficient is positive throughout the physical
range `d > 1`. -/
@[zil_level bridge_theorem]
theorem higherDimTimelikeSurfaceCoefficient_pos (d : ℝ) (hd : 1 < d) :
    0 < higherDimTimelikeSurfaceCoefficient d := by
  unfold higherDimTimelikeSurfaceCoefficient
  exact div_pos
    (mul_pos (Real.sqrt_pos.2 Real.pi_pos)
      (Real.Gamma_pos_of_pos (by linarith)))
    (mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by linarith)))

/-- At boundary dimension two the Gamma coefficient is exactly `pi/2`. -/
@[zil_level bridge_theorem]
theorem higherDimTimelikeSurfaceCoefficient_two :
    higherDimTimelikeSurfaceCoefficient 2 = Real.pi / 2 := by
  unfold higherDimTimelikeSurfaceCoefficient
  norm_num [Real.Gamma_one_half_eq, Real.Gamma_one]
  exact Real.mul_self_sqrt Real.pi_pos.le

/-- The imaginary part is exactly the real higher-dimensional area
coefficient. -/
@[zil_level physical_theorem]
theorem higherDimTimelikeSurfaceEntropy_im (areaPrefactor d : ℝ) :
    (higherDimTimelikeSurfaceEntropy areaPrefactor d).im =
      areaPrefactor * higherDimTimelikeSurfaceCoefficient d := by
  simp [higherDimTimelikeSurfaceEntropy]

/-- **Doi et al. Eqs. (4.16)--(4.17), AdS3 reduction.** With
`Vol(H⁰) = 2`, the higher-dimensional spherical timelike contribution at
`d = 2` is exactly the existing global-AdS3 geodesic entropy. -/
@[zil_level physical_theorem]
theorem higherDimTimelikeSurfaceEntropy_two (R G : ℝ) :
    higherDimTimelikeSurfaceEntropy (R / (2 * G)) 2 =
      timelikeAdS3GeodesicImaginaryEntropy R G := by
  rw [higherDimTimelikeSurfaceEntropy,
    higherDimTimelikeSurfaceCoefficient_two]
  unfold timelikeAdS3GeodesicImaginaryEntropy rtAreaEntropy
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy

zil attach timelikePoincareLineDensity_eq where
  formalizes @ "claim:timelike-ads3-hyperbola-has-the-paper-two-branch-lorentzian-line-density",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equations-3-3-3-4",
  caveat @ "claim:pointwise-density-not-global-stationarity-or-improper-integral"

zil attach complexLog_neg_sq where
  formalizes @ "claim:principal-log-of-negative-squared-interval-adds-i-pi",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-2-3"

zil attach timelikeCFTEntropyMinkowski_eq where
  formalizes @ "claim:general-timelike-minkowski-interval-has-logarithmic-real-part\
    -and-i-pi-c-over-six",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-2-3",
  caveat @ "claim:requires-positive-timelike-separation-and-positive-cutoff"

zil attach timelikeCFTEntropyVacuumLine_eq where
  formalizes @ "claim:cft2-vacuum-timelike-entropy-is-spacelike-entropy-plus-i-pi-c-over-six",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-2-4"

zil attach timelikeCFTEntropyCircle_eq where
  formalizes @ "claim:cft2-circle-timelike-entropy-is-circle-entropy-plus-i-pi-c-over-six",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equations-2-7-3-6"

zil attach timelikeCFTEntropyFiniteT_eq where
  formalizes @ "claim:cft2-finite-temperature-timelike-entropy-is-btz-entropy-plus-i-pi-c-over-six",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-2-10"

zil attach timelikeCFTEntropyVacuumLine_brownHenneaux where
  formalizes @ "claim:brown-henneaux-matches-cft2-timelike-entropy-to-spacelike\
    -plus-timelike-ads3-geodesics",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equations-3-1-3-6",
  caveat @ "claim:does-not-select-among-multiple-complex-extremal-saddles"

zil attach timelikeTransitionDyad_traceRight where
  formalizes @ "claim:finite-thermofield-transition-dyad-reduces-by-partial-trace\
    -to-timelike-transition-matrix",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052\
    -equations-1-4-2-25-2-26",
  caveat @ "claim:finite-common-energy-eigenbasis-not-an-infinite-type-three-algebra"

zil attach timelikeReducedTransition_trace_one where
  formalizes @ "claim:complex-partition-normalization-makes-reduced-transition-matrix-trace-one",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-1-4"

zil attach timelikePseudoEntropy_eq_neg_trace where
  formalizes @ "claim:finite-diagonal-timelike-pseudo-entropy-is-negative-spectral-trace-log",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-1-5",
  caveat @ "claim:diagonal-spectral-functional-not-an-arbitrary-nonnormal-matrix-logarithm"

zil attach timelikeReducedTransition_not_hermitian where
  formalizes @ "claim:a-nonreal-transition-eigenvalue-certifies-the-timelike-reduced\
    -transition-is-non-hermitian",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-section-2-3"

zil attach timelikeTransitionWeight_at_R_zero_eq_tfd where
  formalizes @ "claim:static-slice-of-imaginary-temperature-transition-weight-is\
    -the-tfd-gibbs-weight",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equations-2-20-2-26",
  caveat @ "claim:weight-level-static-slice-not-a-type-three-kms-state-equivalence"

zil attach timelikeEntropy_entropicProperTime where
  formalizes @ "claim:under-the-explicit-imaginary-action-dictionary-timelike\
    -pseudo-entropy-is-entropic-proper-time",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-conclusion",
  caveat @ "claim:conditional-on-s-i-equals-hbar-times-imaginary-pseudo-entropy\
    -not-an-operational-derivation-of-time"

zil attach timelikeEntropy_nnWeight_norm where
  formalizes @ "claim:timelike-pseudo-entropy-imaginary-action-controls-nagao\
    -nielsen-path-weight-suppression",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052-equation-1-5",
  caveat @ "claim:complex-action-dictionary-not-a-replica-path-integral-construction"

zil attach diagonalizablePseudoEntropy_eq where
  formalizes @ "claim:finite-diagonalizable-non-hermitian-transition-pseudo-entropy\
    -equals-the-basis-spectral-negative-trace-log",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052\
    -equations-1-4-1-5",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian\
    .Basic.mconj",
  caveat @ "claim:supplied-invertible-diagonalization-not-a-logarithm-for-defective\
    -or-infinite-type-three-transition-operators"

zil attach diagonalizablePseudoEntropy_basis_independent where
  formalizes @ "claim:finite-diagonalizable-pseudo-entropy-is-independent-of\
    -the-supplied-invertible-eigenbasis-for-fixed-spectral-data",
  supported_by @ "lean:Matrix.trace_mul_cycle",
  caveat @ "claim:principal-spectral-branch-and-fixed-eigenvalue-labeling"

zil attach diagonalizableTransition_qNormal where
  formalizes @ "claim:the-diagonalizable-timelike-transition-is-normal-in-the\
    -nagao-nielsen-q-metric-even-when-nonnormal-in-the-original-inner-product",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian\
    .Basic.hamiltonian_qNormal"

zil attach timelikeEntropyCalibratedDuration_operational where
  formalizes @ "claim:after-independent-positive-imaginary-energy-calibration\
    -the-universal-timelike-pseudo-entropy-action-fixes-an-operational-physical\
    -proper-time-duration",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein\
    .EntropicComplexEinstein.imaginaryEinstein_entropicTime_eq_physicalProperTime",
  caveat @ "claim:conditional-on-an-independent-imaginary-energy-scale-not-a\
    -derivation-of-that-scale-from-the-universal-imaginary-entropy"

zil attach universalTimelikeEntropyActionAlong_not_clock where
  formalizes @ "claim:the-constant-universal-i-pi-c-over-six-contribution-cannot\
    -by-itself-obey-a-nonzero-frequency-operational-clock-law",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052\
    -equations-2-3-2-4",
  caveat @ "claim:no-go-is-for-the-universal-constant-contribution-not-for-all\
    -interval-dependent-pseudo-entropy-data"

zil attach higherDimTimelikeSurfaceEntropy_two where
  formalizes @ "claim:the-higher-dimensional-spherical-timelike-surface-gamma\
    -coefficient-is-positive-and-reduces-at-d-two-to-the-ads-three-imaginary\
    -geodesic-entropy",
  supported_by @ "paper:doi-harper-mollabashi-takayanagi-taki-jhep05-2023-052\
    -equations-4-16-4-17",
  caveat @ "claim:coefficient-and-reduction-not-a-proof-of-global-saddle-selection\
    -or-the-strip-complex-extremal-surface"

zil_file_contract physlib.timelikeEntanglementEntropy where
  promises "The principal-branch CFT2 and pointwise AdS3 core of timelike\
    entanglement entropy, its finite diagonal transition/pseudo-entropy sector,\
    its finite diagonalizable Q-normal extension, typed TFD and complex-action\
    bridges, an operational-duration calibration with a constant-term no-go,\
    and the higher-dimensional spherical timelike coefficient."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.\
      RyuTakayanagiFormulaAlgebra.cftEntropyVacuumLine",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.\
      RyuTakayanagiFormulaAlgebra.cftEntropyFiniteT",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.\
      RyuTakayanagiFormulaAlgebra.brownHenneaux",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.\
      TFDGibbsVariational.tfdReducedWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.\
      EntropicDampingEquivalence.nnPathWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.\
      ComplexActionDampingCoercivity.entropicProperTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.\
      Basic.mconj",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.\
      EntropicComplexEinstein.imaginaryEinstein_entropicTime_eq_physicalProperTime"
  ]
  forbids_substitutes [
    "claiming a logarithm for defective arbitrary matrices or type-III operators\
      from the supplied finite diagonalizable spectral construction",
    "promoting the conditional imaginary-action dictionary to an operational\
      derivation of physical time",
    "claiming global extremality or saddle selection from a pointwise line density",
    "extending the CFT2 formulas to higher-dimensional strips by relabeling"
  ]
  witnessed_by [
    timelikePoincareLineDensity_eq,
    complexLog_neg_sq,
    timelikeCFTEntropyFromRatio_eq,
    timelikeCFTEntropyMinkowski_eq,
    timelikeCFTEntropyVacuumLine_eq,
    timelikeCFTEntropyVacuumLine_im,
    timelikeCFTEntropyCircle_eq,
    timelikeCFTEntropyFiniteT_eq,
    timelikeAdS3GeodesicImaginaryEntropy_eq,
    timelikeCFTEntropyVacuumLine_brownHenneaux,
    timelikeTransitionDyad_traceRight,
    timelikeReducedTransition_trace_one,
    timelikePseudoEntropy_eq_neg_trace,
    timelikeReducedTransition_not_hermitian,
    timelikeTransitionWeight_at_R_zero_eq_tfd,
    timelikeEntropy_entropicProperTime,
    timelikeEntropy_nnWeight_norm,
    diagonalizablePseudoEntropy_eq,
    diagonalizablePseudoEntropy_basis_independent,
    diagonalizableTransition_qNormal,
    timelikeEntropyCalibratedDuration_operational,
    universalTimelikeEntropyActionAlong_not_clock,
    higherDimTimelikeSurfaceCoefficient_pos,
    higherDimTimelikeSurfaceEntropy_im,
    higherDimTimelikeSurfaceEntropy_two
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.timelikeEntanglementEntropy
