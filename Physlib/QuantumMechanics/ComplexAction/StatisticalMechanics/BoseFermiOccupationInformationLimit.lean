/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.Relativity.Special.UnruhEntropicRate

/-!
# Bose → Fermi statistics: the Pauli occupation bound is the per-mode information limit

In the holographic picture (`AdSCFT.PenroseHolographicMassEntropyBound`) the black hole **saturates** the
information bound while atomic shells are **tiny finite registers** (`Particles.AtomicShellInformationCapacityOctet`).
The distinction is *statistics*: the boson → fermion transition imposes the Pauli occupation bound, and that
bound is exactly the "one bit per mode" that discretizes the continuous holographic capacity into the finite
octet registers.

The two occupations are reciprocal. With `x = β ℏω`:

* **Boson** `n_B = 1/(e^x − 1)` (`boseEinstein`): `1 + 2 n_B = coth(x/2)`, **unbounded** as `x → 0⁺` — the
  bosonic (graviton-condensate) side that *saturates* the gravitational ceiling.
* **Fermion** `n_F = 1/(e^x + 1)` (`fermiDirac`): `1 − 2 n_F = tanh(x/2) ∈ (0,1)`, so `0 < n_F < 1` — the
  **Pauli-bounded** side, each mode at most one fermion = one bit.

This file proves:

* `fermiDirac_pos`, `fermiDirac_lt_one`: `0 < n_F < 1` — the Pauli bound, the per-mode information limit that
  underlies the finite shell capacities `2(2l+1)` and the octet's 8 bits.
* `fermiDirac_lt_half_of_pos`: at positive energy `n_F < 1/2` (below the Fermi level).
* `boseFermi_reciprocity`: `(1 + 2 n_B)(1 − 2 n_F) = 1` — the `coth·tanh = 1` relation joining the unbounded
  bosonic occupation (BH saturation) to the Pauli-bounded fermionic occupation (atomic registers).
* `detectorParityIndex_even_of_even_dimensionKernel` and
  `detectorParityIndex_odd_of_odd_dimensionKernel_and_odd_power`: the parity part of Sriramkumar's
  accelerated-detector formula `α = (D - 1)n`, where even `α` selects the Bose-Einstein factor and odd `α`
  selects the Fermi-Dirac factor.
* `wickReducedDetectorCorrelator`: the Wick reduction `G_M^{(n)} = n! (G_M^+)^n` from Eq. (6).
* `detectorCrossTerm_eq_zero_of_odd_even`: the Eq. (13) cross-term cancellation for an odd power coupled
  with an even power.
* `StationaryDetectorKernel` and `detectorResponseIntegrand`: the stationary proper-time reduction that
  makes the Eq. (5) response-rate integrand depend only on `τ - τ'`.
* `evenDetectorPolynomial` and `oddDetectorPolynomial`: the finite polynomial factors multiplying the
  Bose-Einstein and Fermi-Dirac factors in Eq. (9).
* `unruhInverseTemperatureNatural_mul_lambdaU`: the paper's `2π/g` inverse temperature linked to the
  repository's `UnruhEntropicRate.lambdaU`.
* `imaginaryTimePeriodic_wickReducedDetectorCorrelator`: the KMS-periodicity closure behind the statement
  that the apparent Fermi-Dirac factor does not change the scalar field's bosonic KMS character.
* `detectorDetailedBalance_of_KMSDetailedBalance`: the paper's Eq. (15) recovered from the repository's
  operational `KMSDetailedBalance` carrier.
* `detectorDetailedBalance_superposed`: the superposed odd/even detector response of Eq. (14) preserves the
  detailed-balance condition of Eq. (15).

So the boson→fermion transition is the discretizer: bosons (no bound) let the black hole saturate the
holographic ceiling; fermions (Pauli bound `n_F < 1`) turn each mode into one bit, building the finite atomic
registers nested far below.

## References

* W. Pauli (1925); Bose–Einstein and Fermi–Dirac statistics. `Physlib` (`ComplexOscillator.ComplexFermionicOscillator.fermiDirac`,
  `ThermoFieldDynamics.MatsubaraThermalOscillator.boseEinstein`, `Particles.AtomicShellInformationCapacityOctet`,
  `AdSCFT.PenroseHolographicMassEntropyBound`).
* L. Sriramkumar, "Interpolating between the Bose-Einstein and the Fermi-Dirac Distributions in Odd
  Dimensions", General Relativity and Gravitation 35, 1699-1705 (2003).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.Relativity.Special
open _root_.QuantumMechanics.FiniteTarget
open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

/-- **[Fermion occupation is positive]** `0 < n_F`. -/
lemma fermiDirac_pos (x : ℝ) : 0 < fermiDirac x := by
  unfold fermiDirac; positivity

/-- **[The Pauli bound: `n_F < 1`]** the Fermi–Dirac occupation never reaches `1` — at most one fermion per
mode. This per-mode bound is the "one bit per mode" that makes the atomic shell capacities `2(2l+1)` (and the
octet's 8 bits) finite. -/
lemma fermiDirac_lt_one (x : ℝ) : fermiDirac x < 1 := by
  unfold fermiDirac
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos x]

/-- **[Below the Fermi level]** at positive energy `n_F < 1/2`. -/
lemma fermiDirac_lt_half_of_pos {x : ℝ} (hx : 0 < x) : fermiDirac x < 1 / 2 := by
  unfold fermiDirac
  have he : (1 : ℝ) < Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- **[Bose–Fermi reciprocity `coth·tanh = 1`]** `(1 + 2 n_B)(1 − 2 n_F) = 1` (for `β ℏω ≠ 0`): the unbounded
bosonic occupation `1 + 2 n_B = coth(βℏω/2)` and the Pauli-bounded fermionic occupation
`1 − 2 n_F = tanh(βℏω/2)` are reciprocal. The boson side can saturate (coth → ∞); the fermion side is capped
(tanh < 1) — the statistical origin of "BH saturates, atomic registers stay finite". -/
lemma boseFermi_reciprocity (β ℏω : ℝ) (hx : β * ℏω ≠ 0) :
    (1 + 2 * boseEinstein β ℏω) * (1 - 2 * fermiDirac (β * ℏω)) = 1 := by
  unfold boseEinstein fermiDirac
  have h1 : Real.exp (β * ℏω) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => hx (Real.exp_injective (h.trans Real.exp_zero.symm))
  have h2 : Real.exp (β * ℏω) + 1 ≠ 0 := (by positivity : (0 : ℝ) < Real.exp (β * ℏω) + 1).ne'
  field_simp
  ring

/-- Sriramkumar Eq. (9) uses `α = (D - 1)n`.  For total spacetime dimension
`d = D + 1`, the first factor is `d - 2`; this definition keeps that parity
kernel explicit. -/
def detectorParityIndex (dimensionKernel n : ℕ) : ℕ :=
  dimensionKernel * n

/-- Natural-unit Unruh inverse temperature for a uniformly accelerated detector,
`β_U = 2π/g`. -/
noncomputable def unruhInverseTemperatureNatural (g : ℝ) : ℝ :=
  2 * Real.pi / g

/-- The Unruh variable in Eq. (9), `x = 2πE/g = β_U E`. -/
noncomputable def unruhDetectorVariable (E g : ℝ) : ℝ :=
  2 * Real.pi * E / g

/-- The Bose-Einstein detector factor in Sriramkumar Eq. (9), written as a
function of the Unruh variable `x = 2πE/g`. -/
noncomputable def sriramkumarBoseFactor (x : ℝ) : ℝ :=
  boseEinstein 1 x

/-- The Fermi-Dirac detector factor in Sriramkumar Eq. (9), written as a
function of the Unruh variable `x = 2πE/g`. -/
noncomputable def sriramkumarFermiFactor (x : ℝ) : ℝ :=
  fermiDirac x

/-- Sriramkumar Eq. (14): a detector coupled to an even power and an odd power
has response `R_even(E) + r^2 R_odd(E)`, where `r` is the relative odd-sector
coupling. -/
def superposedDetectorRate (r evenRate oddRate : ℝ) : ℝ :=
  evenRate + r ^ 2 * oddRate

/-- Coupling-normalized odd-sector weight `r^2/(1+r^2)`. -/
noncomputable def oddCouplingWeight (r : ℝ) : ℝ :=
  r ^ 2 / (1 + r ^ 2)

/-- Coupling-normalized even-sector weight `1/(1+r^2)`. -/
noncomputable def evenCouplingWeight (r : ℝ) : ℝ :=
  1 / (1 + r ^ 2)

/-- Coupling-normalized form of Sriramkumar Eq. (14). -/
noncomputable def normalizedSuperposedDetectorRate (r evenRate oddRate : ℝ) : ℝ :=
  superposedDetectorRate r evenRate oddRate / (1 + r ^ 2)

/-- Odd-dimensional Bose/Fermi detector interpolation after normalizing the two
coupling sectors to weights summing to one. -/
noncomputable def oddDimBoseFermiInterpolation (r x : ℝ) : ℝ :=
  normalizedSuperposedDetectorRate r (sriramkumarBoseFactor x) (sriramkumarFermiFactor x)

/-- Sriramkumar Eq. (15): spectrum-level detailed balance at inverse temperature
`β`. -/
def SatisfiesDetectorDetailedBalance (β : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ E : ℝ, R E = Real.exp (-β * E) * R (-E)

/-- Eq. (5) input: a two-time detector correlator whose dependence is only on
the proper-time difference `τ - τ'`. -/
structure StationaryDetectorKernel where
  /-- The two-time correlator before stationarity reduction. -/
  twoTime : ℝ → ℝ → ℂ
  /-- The reduced one-variable kernel after stationarity in detector proper time. -/
  reduced : ℝ → ℂ
  /-- Stationarity: the correlator depends only on `τ - τ'`. -/
  stationary : ∀ τ τ' : ℝ, twoTime τ τ' = reduced (τ - τ')

namespace StationaryDetectorKernel

/-- The diagonal two-time correlator equals the reduced kernel at zero
proper-time separation. -/
lemma diagonal_eq_reduced_zero (K : StationaryDetectorKernel) (τ : ℝ) :
    K.twoTime τ τ = K.reduced 0 := by
  rw [K.stationary τ τ]
  ring_nf

/-- Translating both detector proper times leaves the stationary correlator
unchanged. -/
lemma translate_invariant (K : StationaryDetectorKernel) (shift τ τ' : ℝ) :
    K.twoTime (τ + shift) (τ' + shift) = K.twoTime τ τ' := by
  rw [K.stationary (τ + shift) (τ' + shift), K.stationary τ τ']
  ring_nf

end StationaryDetectorKernel

/-- Eq. (5) integrand for the detector response rate:
`e^{-iE τbar} G^{(n)}(τbar)`.  The integral itself is the analytic input
quoted by the paper; this definition records the exact integrand reused by the
branch formulas. -/
noncomputable def detectorResponseIntegrand (E τbar : ℝ) (kernel : ℝ → ℂ) : ℂ :=
  Complex.exp (-(Complex.I * ((E * τbar : ℝ) : ℂ))) * kernel τbar

/-- Sriramkumar Eq. (6): Wick reduction sends the normal-ordered
`2n`-point detector correlator to `n!` times the `n`-th power of the scalar
Wightman function. -/
noncomputable def wickReducedDetectorCorrelator (n : ℕ) (wightman : ℂ) : ℂ :=
  (Nat.factorial n : ℂ) * wightman ^ n

/-- The mixed odd/even cross term in Eq. (13) is the field moment of total
power `n_o+n_e`. -/
noncomputable def detectorCrossTerm (fieldMoment : ℕ → ℂ) (oddPower evenPower : ℕ) : ℂ :=
  fieldMoment (oddPower + evenPower)

/-- Scalar-field odd moments vanish for the state/correlation class under
consideration. This is the hypothesis used in the paper to eliminate the
Eq. (13) cross terms. -/
def OddFieldMomentsVanish (fieldMoment : ℕ → ℂ) : Prop :=
  ∀ power : ℕ, Odd power → fieldMoment power = 0

/-- Generic imaginary-time periodicity, stated at period `period` in the
complex proper-time plane. -/
def ImaginaryTimePeriodic (period : ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, G (z + period) = G z

/-- The imaginary proper-time KMS period `iβ`. -/
def imaginaryKMSPeriod (β : ℝ) : ℂ :=
  Complex.I * (β : ℂ)

/-- Eq. (9), Bose-Einstein branch: the finite polynomial
`∏_{l=0}^q (l^2+(E/g)^2)` for `α = 2q+2`. -/
noncomputable def evenDetectorPolynomial (q : ℕ) (energyOverAcceleration : ℝ) : ℝ :=
  (Finset.range (q + 1)).prod fun l =>
    ((l : ℝ) ^ 2 + energyOverAcceleration ^ 2)

/-- Eq. (9), Fermi-Dirac branch: the finite polynomial
`∏_{l=0}^q (((2l+1)/2)^2+(E/g)^2)` for `α = 2q+3`. -/
noncomputable def oddDetectorPolynomial (q : ℕ) (energyOverAcceleration : ℝ) : ℝ :=
  (Finset.range (q + 1)).prod fun l =>
    (((2 * (l : ℝ) + 1) / 2) ^ 2 + energyOverAcceleration ^ 2)

/-- Eq. (9), even `α = 2q+2` branch, retaining the paper's normalization
coefficient as an explicit scalar parameter. -/
noncomputable def sriramkumarEvenBranchRate (normalization g E : ℝ) (q : ℕ) : ℝ :=
  normalization * (g ^ (2 * q + 2) / E) *
    sriramkumarBoseFactor (unruhDetectorVariable E g) *
    evenDetectorPolynomial q (E / g)

/-- Eq. (9), odd `α = 2q+3` branch, retaining the paper's normalization
coefficient as an explicit scalar parameter. -/
noncomputable def sriramkumarOddBranchRate (normalization g E : ℝ) (q : ℕ) : ℝ :=
  normalization * g ^ (2 * q + 2) *
    sriramkumarFermiFactor (unruhDetectorVariable E g) *
    oddDetectorPolynomial q (E / g)

/-- The thermal factor selected by Eq. (9): even `α` gives the Bose-Einstein
factor and odd `α` gives the Fermi-Dirac factor. -/
noncomputable def detectorThermalFactorOfIndex (α : ℕ) (x : ℝ) : ℝ :=
  if Even α then sriramkumarBoseFactor x else sriramkumarFermiFactor x

/-- Odd-dimensional Eq. (14) rate using the even and odd Eq. (9) branches. -/
noncomputable def oddDimensionalSriramkumarRate
    (r evenNormalization oddNormalization g E : ℝ) (qEven qOdd : ℕ) : ℝ :=
  superposedDetectorRate r
    (sriramkumarEvenBranchRate evenNormalization g E qEven)
    (sriramkumarOddBranchRate oddNormalization g E qOdd)

/-- Compactified `r = ∞` chart for the normalized Eq. (14) response. With
`u = 1/r`, this is `(u^2 R_even + R_odd)/(1+u^2)`, so `u = 0` is the
Fermi-Dirac end of the interpolation. -/
noncomputable def inverseScaleNormalizedDetectorRate (u evenRate oddRate : ℝ) : ℝ :=
  (u ^ 2 * evenRate + oddRate) / (1 + u ^ 2)

@[simp]
lemma sriramkumarBoseFactor_eq_boseEinstein (x : ℝ) :
    sriramkumarBoseFactor x = boseEinstein 1 x := rfl

@[simp]
lemma sriramkumarFermiFactor_eq_fermiDirac (x : ℝ) :
    sriramkumarFermiFactor x = fermiDirac x := rfl

/-- The detector variable is exactly inverse Unruh temperature times energy. -/
lemma unruhDetectorVariable_eq_inverseTemperature_mul_energy (E g : ℝ) :
    unruhDetectorVariable E g = unruhInverseTemperatureNatural g * E := by
  unfold unruhDetectorVariable unruhInverseTemperatureNatural
  ring

/-- Multiplying the Unruh detector variable by the acceleration recovers
`2πE`. -/
lemma unruhDetectorVariable_mul_acceleration (E g : ℝ) (hg : g ≠ 0) :
    unruhDetectorVariable E g * g = 2 * Real.pi * E := by
  unfold unruhDetectorVariable
  field_simp [hg]

/-- The paper's natural-unit inverse Unruh temperature `2π/g` is the inverse
of the repository's Unruh entropic rate up to the speed-of-light factor:
`β_U · λ_U = 1/c`. -/
lemma unruhInverseTemperatureNatural_mul_lambdaU (M : UnruhEntropicRate)
    (ha : M.a ≠ 0) :
    unruhInverseTemperatureNatural M.a * M.lambdaU = 1 / M.c := by
  unfold unruhInverseTemperatureNatural UnruhEntropicRate.lambdaU
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hc : M.c ≠ 0 := ne_of_gt M.c_pos
  field_simp [ha, hpi, hc]

/-- The detector variable can be written using the repository's Unruh rate:
`2πE/a = E/(c λ_U)`. -/
lemma unruhDetectorVariable_eq_energy_div_c_lambdaU
    (M : UnruhEntropicRate) (E : ℝ) (ha : M.a ≠ 0) :
    unruhDetectorVariable E M.a = E / (M.c * M.lambdaU) := by
  unfold unruhDetectorVariable UnruhEntropicRate.lambdaU
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hc : M.c ≠ 0 := ne_of_gt M.c_pos
  field_simp [ha, hpi, hc]

/-- If the dimension parity kernel `D - 1` is even, the detector index `α` is
even for every coupling power.  This is the parity branch selecting the
Bose-Einstein factor in Eq. (9). -/
lemma detectorParityIndex_even_of_even_dimensionKernel {dimensionKernel n : ℕ}
    (hdim : Even dimensionKernel) : Even (detectorParityIndex dimensionKernel n) := by
  rcases hdim with ⟨k, hk⟩
  refine ⟨k * n, ?_⟩
  rw [detectorParityIndex, hk]
  ring

/-- If the coupling power is even, the detector index `α` is even independently
of the dimension parity kernel. -/
lemma detectorParityIndex_even_of_even_power (dimensionKernel : ℕ) {n : ℕ}
    (hn : Even n) : Even (detectorParityIndex dimensionKernel n) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨dimensionKernel * k, ?_⟩
  rw [detectorParityIndex, hk]
  ring

/-- In odd total spacetime dimensions the dimension parity kernel is odd; an
odd coupling power then gives odd `α`, selecting the Fermi-Dirac factor in
Eq. (9). -/
lemma detectorParityIndex_odd_of_odd_dimensionKernel_and_odd_power {dimensionKernel n : ℕ}
    (hdim : Odd dimensionKernel) (hn : Odd n) : Odd (detectorParityIndex dimensionKernel n) := by
  rcases hdim with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨2 * a * b + a + b, ?_⟩
  rw [detectorParityIndex, ha, hb]
  ring

/-- Eq. (9) branch selection: an even detector index chooses the Bose-Einstein
factor. -/
lemma detectorThermalFactorOfIndex_eq_bose_of_even {α : ℕ} (hα : Even α) (x : ℝ) :
    detectorThermalFactorOfIndex α x = sriramkumarBoseFactor x := by
  simp [detectorThermalFactorOfIndex, hα]

/-- Eq. (9) branch selection: an odd detector index chooses the Fermi-Dirac
factor. -/
lemma detectorThermalFactorOfIndex_eq_fermi_of_odd {α : ℕ} (hα : Odd α) (x : ℝ) :
    detectorThermalFactorOfIndex α x = sriramkumarFermiFactor x := by
  have hnot : ¬ Even α := Nat.not_even_iff_odd.mpr hα
  simp [detectorThermalFactorOfIndex, hnot]

/-- Even dimension kernel means the Eq. (9) detector factor is Bose-Einstein
for every coupling power. -/
lemma detectorThermalFactor_even_dimensionKernel {dimensionKernel n : ℕ}
    (hdim : Even dimensionKernel) (x : ℝ) :
    detectorThermalFactorOfIndex (detectorParityIndex dimensionKernel n) x =
      sriramkumarBoseFactor x :=
  detectorThermalFactorOfIndex_eq_bose_of_even
    (detectorParityIndex_even_of_even_dimensionKernel hdim) x

/-- Even coupling power means the Eq. (9) detector factor is Bose-Einstein
independently of dimension parity. -/
lemma detectorThermalFactor_even_power (dimensionKernel : ℕ) {n : ℕ}
    (hn : Even n) (x : ℝ) :
    detectorThermalFactorOfIndex (detectorParityIndex dimensionKernel n) x =
      sriramkumarBoseFactor x :=
  detectorThermalFactorOfIndex_eq_bose_of_even
    (detectorParityIndex_even_of_even_power dimensionKernel hn) x

/-- Odd dimension kernel and odd coupling power give the Eq. (9)
Fermi-Dirac detector factor. -/
lemma detectorThermalFactor_odd_dimensionKernel_odd_power {dimensionKernel n : ℕ}
    (hdim : Odd dimensionKernel) (hn : Odd n) (x : ℝ) :
    detectorThermalFactorOfIndex (detectorParityIndex dimensionKernel n) x =
      sriramkumarFermiFactor x :=
  detectorThermalFactorOfIndex_eq_fermi_of_odd
    (detectorParityIndex_odd_of_odd_dimensionKernel_and_odd_power hdim hn) x

/-- Eq. (6) at linear coupling: the Wick-reduced correlator is the original
Wightman function. -/
@[simp]
lemma wickReducedDetectorCorrelator_one (wightman : ℂ) :
    wickReducedDetectorCorrelator 1 wightman = wightman := by
  simp [wickReducedDetectorCorrelator]

/-- Eq. (6) recursion: increasing the nonlinear power from `n` to `n+1`
multiplies the Wick-reduced correlator by `(n+1)G^+`. -/
lemma wickReducedDetectorCorrelator_succ (n : ℕ) (wightman : ℂ) :
    wickReducedDetectorCorrelator (n + 1) wightman =
      ((n + 1 : ℕ) : ℂ) * wightman * wickReducedDetectorCorrelator n wightman := by
  unfold wickReducedDetectorCorrelator
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  ring

/-- Odd plus even is odd; this is the parity fact used in Eq. (13). -/
lemma odd_add_even_power {oddPower evenPower : ℕ}
    (hodd : Odd oddPower) (heven : Even evenPower) : Odd (oddPower + evenPower) := by
  rcases hodd with ⟨a, ha⟩
  rcases heven with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb]
  ring

/-- Eq. (13): if odd field moments vanish, then the mixed odd/even cross term
vanishes. -/
lemma detectorCrossTerm_eq_zero_of_odd_even (fieldMoment : ℕ → ℂ)
    {oddPower evenPower : ℕ}
    (hmoment : OddFieldMomentsVanish fieldMoment)
    (hodd : Odd oddPower) (heven : Even evenPower) :
    detectorCrossTerm fieldMoment oddPower evenPower = 0 := by
  unfold detectorCrossTerm
  exact hmoment (oddPower + evenPower) (odd_add_even_power hodd heven)

/-- The first Bose-branch polynomial factor is `(E/g)^2`. -/
@[simp]
lemma evenDetectorPolynomial_zero (energyOverAcceleration : ℝ) :
    evenDetectorPolynomial 0 energyOverAcceleration = energyOverAcceleration ^ 2 := by
  simp [evenDetectorPolynomial]

/-- The first Fermi-branch polynomial factor is `1/4 + (E/g)^2`. -/
@[simp]
lemma oddDetectorPolynomial_zero (energyOverAcceleration : ℝ) :
    oddDetectorPolynomial 0 energyOverAcceleration =
      (1 / 4 : ℝ) + energyOverAcceleration ^ 2 := by
  simp [oddDetectorPolynomial]
  ring_nf

/-- The Bose-branch polynomial in Eq. (9) is nonnegative. -/
lemma evenDetectorPolynomial_nonneg (q : ℕ) (energyOverAcceleration : ℝ) :
    0 ≤ evenDetectorPolynomial q energyOverAcceleration := by
  unfold evenDetectorPolynomial
  exact Finset.prod_nonneg fun l _ =>
    add_nonneg (sq_nonneg (l : ℝ)) (sq_nonneg energyOverAcceleration)

/-- The Fermi-branch polynomial in Eq. (9) is nonnegative. -/
lemma oddDetectorPolynomial_nonneg (q : ℕ) (energyOverAcceleration : ℝ) :
    0 ≤ oddDetectorPolynomial q energyOverAcceleration := by
  unfold oddDetectorPolynomial
  exact Finset.prod_nonneg fun l _ =>
    add_nonneg (sq_nonneg (((2 * (l : ℝ) + 1) / 2)))
      (sq_nonneg energyOverAcceleration)

/-- KMS/imaginary-time periodicity is preserved by powers of a correlator. -/
lemma imaginaryTimePeriodic_pow {period : ℂ} {G : ℂ → ℂ}
    (hG : ImaginaryTimePeriodic period G) (n : ℕ) :
    ImaginaryTimePeriodic period (fun z => G z ^ n) := by
  intro z
  change G (z + period) ^ n = G z ^ n
  rw [hG z]

/-- KMS/imaginary-time periodicity is preserved by linear combinations. -/
lemma imaginaryTimePeriodic_linear_combination {period : ℂ} {G H : ℂ → ℂ}
    (a b : ℂ)
    (hG : ImaginaryTimePeriodic period G)
    (hH : ImaginaryTimePeriodic period H) :
    ImaginaryTimePeriodic period (fun z => a * G z + b * H z) := by
  intro z
  change a * G (z + period) + b * H (z + period) = a * G z + b * H z
  rw [hG z, hH z]

/-- Eq. (6) plus KMS: if the scalar Wightman function is imaginary-time
periodic, then every Wick-reduced nonlinear detector correlator has the same
period. -/
lemma imaginaryTimePeriodic_wickReducedDetectorCorrelator {period : ℂ} {G : ℂ → ℂ}
    (hG : ImaginaryTimePeriodic period G) (n : ℕ) :
    ImaginaryTimePeriodic period
      (fun z => wickReducedDetectorCorrelator n (G z)) := by
  intro z
  unfold wickReducedDetectorCorrelator
  change (Nat.factorial n : ℂ) * G (z + period) ^ n =
    (Nat.factorial n : ℂ) * G z ^ n
  rw [hG z]

/-- Eq. (15) from the repository's `KMSDetailedBalance`: if a detector response
uses `W_minus(E)` and the negative-energy response is the corresponding
`W_plus(E)`, the KMS carrier gives Sriramkumar detailed balance. -/
lemma detectorDetailedBalance_of_KMSDetailedBalance
    (κ : KMSDetailedBalance) (R : ℝ → ℝ)
    (hminus : ∀ E : ℝ, R E = κ.W_minus E)
    (hflip : ∀ E : ℝ, R (-E) = κ.W_plus E) :
    SatisfiesDetectorDetailedBalance κ.beta R := by
  intro E
  rw [hminus E, hflip E, κ.detailed_balance E]
  have hexp :
      Real.exp (-κ.beta * E) * Real.exp (κ.beta * E) = 1 := by
    rw [← Real.exp_add]
    have harg : -κ.beta * E + κ.beta * E = 0 := by ring
    rw [harg, Real.exp_zero]
  rw [← mul_assoc, hexp, one_mul]

/-- The denominator `1+r^2` in the coupling-normalized response is positive. -/
lemma one_add_sq_pos (r : ℝ) : 0 < 1 + r ^ 2 := by
  nlinarith [sq_nonneg r]

/-- The odd-sector interpolation weight is nonnegative. -/
lemma oddCouplingWeight_nonneg (r : ℝ) : 0 ≤ oddCouplingWeight r := by
  unfold oddCouplingWeight
  exact div_nonneg (sq_nonneg r) (le_of_lt (one_add_sq_pos r))

/-- The odd-sector interpolation weight is strictly below one. -/
lemma oddCouplingWeight_lt_one (r : ℝ) : oddCouplingWeight r < 1 := by
  unfold oddCouplingWeight
  rw [div_lt_one (one_add_sq_pos r)]
  nlinarith [sq_nonneg r]

/-- The even-sector interpolation weight is positive. -/
lemma evenCouplingWeight_pos (r : ℝ) : 0 < evenCouplingWeight r := by
  unfold evenCouplingWeight
  exact one_div_pos.mpr (one_add_sq_pos r)

/-- The coupling-normalized even and odd weights sum to one. -/
lemma evenCouplingWeight_add_oddCouplingWeight (r : ℝ) :
    evenCouplingWeight r + oddCouplingWeight r = 1 := by
  unfold evenCouplingWeight oddCouplingWeight
  field_simp [ne_of_gt (one_add_sq_pos r)]

@[simp]
lemma superposedDetectorRate_zero_oddCoupling (evenRate oddRate : ℝ) :
    superposedDetectorRate 0 evenRate oddRate = evenRate := by
  simp [superposedDetectorRate]

/-- The normalized Eq. (14) response is exactly the convex combination with
weights `1/(1+r^2)` and `r^2/(1+r^2)`. -/
lemma normalizedSuperposedDetectorRate_eq_convex (r evenRate oddRate : ℝ) :
    normalizedSuperposedDetectorRate r evenRate oddRate =
      evenCouplingWeight r * evenRate + oddCouplingWeight r * oddRate := by
  unfold normalizedSuperposedDetectorRate superposedDetectorRate evenCouplingWeight oddCouplingWeight
  field_simp [ne_of_gt (one_add_sq_pos r)]

@[simp]
lemma oddDimBoseFermiInterpolation_zero (x : ℝ) :
    oddDimBoseFermiInterpolation 0 x = sriramkumarBoseFactor x := by
  simp [oddDimBoseFermiInterpolation, normalizedSuperposedDetectorRate,
    superposedDetectorRate]

/-- The odd-dimensional interpolation is the normalized Bose/Fermi convex
combination obtained by varying the relative odd coupling `r`. -/
lemma oddDimBoseFermiInterpolation_eq_convex (r x : ℝ) :
    oddDimBoseFermiInterpolation r x =
      evenCouplingWeight r * sriramkumarBoseFactor x +
        oddCouplingWeight r * sriramkumarFermiFactor x := by
  exact normalizedSuperposedDetectorRate_eq_convex r
    (sriramkumarBoseFactor x) (sriramkumarFermiFactor x)

/-- The inverse-scale chart agrees with the normalized Eq. (14) rate for
nonzero `r` after setting `u = 1/r`. -/
lemma normalizedSuperposedDetectorRate_eq_inverseScale
    (r evenRate oddRate : ℝ) (hr : r ≠ 0) :
    normalizedSuperposedDetectorRate r evenRate oddRate =
      inverseScaleNormalizedDetectorRate (1 / r) evenRate oddRate := by
  unfold normalizedSuperposedDetectorRate superposedDetectorRate inverseScaleNormalizedDetectorRate
  field_simp [hr]
  ring

/-- The inverse-scale `u = 0` endpoint is the odd-sector response, i.e. the
Fermi-Dirac branch in odd spacetime dimensions with odd coupling power. -/
@[simp]
lemma inverseScaleNormalizedDetectorRate_zero (evenRate oddRate : ℝ) :
    inverseScaleNormalizedDetectorRate 0 evenRate oddRate = oddRate := by
  simp [inverseScaleNormalizedDetectorRate]

/-- At `r = 0`, the odd-dimensional Sriramkumar response is the even-power
Bose-Einstein branch. -/
@[simp]
lemma oddDimensionalSriramkumarRate_zero
    (evenNormalization oddNormalization g E : ℝ) (qEven qOdd : ℕ) :
    oddDimensionalSriramkumarRate 0 evenNormalization oddNormalization g E qEven qOdd =
      sriramkumarEvenBranchRate evenNormalization g E qEven := by
  simp [oddDimensionalSriramkumarRate]

/-- Sriramkumar Eq. (15) is stable under the Eq. (14) odd/even superposition. -/
lemma detectorDetailedBalance_superposed
    (β r : ℝ) (Re Ro : ℝ → ℝ)
    (he : SatisfiesDetectorDetailedBalance β Re)
    (ho : SatisfiesDetectorDetailedBalance β Ro) :
    SatisfiesDetectorDetailedBalance β
      (fun E => superposedDetectorRate r (Re E) (Ro E)) := by
  intro E
  change superposedDetectorRate r (Re E) (Ro E) =
    Real.exp (-β * E) * superposedDetectorRate r (Re (-E)) (Ro (-E))
  unfold superposedDetectorRate
  rw [he E, ho E]
  ring

/-- Sriramkumar Eq. (15) is also stable after normalizing the Eq. (14) coupling
weights. -/
lemma detectorDetailedBalance_normalizedSuperposed
    (β r : ℝ) (Re Ro : ℝ → ℝ)
    (he : SatisfiesDetectorDetailedBalance β Re)
    (ho : SatisfiesDetectorDetailedBalance β Ro) :
    SatisfiesDetectorDetailedBalance β
      (fun E => normalizedSuperposedDetectorRate r (Re E) (Ro E)) := by
  intro E
  change normalizedSuperposedDetectorRate r (Re E) (Ro E) =
    Real.exp (-β * E) * normalizedSuperposedDetectorRate r (Re (-E)) (Ro (-E))
  unfold normalizedSuperposedDetectorRate superposedDetectorRate
  rw [he E, ho E]
  ring

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoseFermiOccupationInformationLimit

end
