/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Mathlib.Tactic

/-!
# Harper operators, Fermi curves, and Picard-Fuchs equations

Lean-checkable core of Dan Li, *Harper operators, Fermi curves and
Picard-Fuchs equations* (arXiv:1207.5197v2).

The paper has three formal layers:

* the Harper Bloch symbol reduces, after a phase change of variables, to the
  normalized Fermi curve `xi + xi^{-1} + eta + eta^{-1} = lambda`;
* the special fibers at `lambda = 0, ±4` are detected by explicit
  factorizations of the quadratic/discriminant form, and their local
  monodromy is Picard-Lefschetz cycle addition;
* the normalized density of states satisfies a Picard-Fuchs equation.  The
  ordinary, logarithmic, energy, Q-form, Schwarzian, Landen, and truncated
  mirror-map forms are related by algebraic identities.

As in the adjacent `IntegerQuantumHallBulkEdge` file, global analytic
existence of periods/elliptic fibrations is not asserted as a theorem here.
The analytic period input is represented by explicit residual/equation
carriers, while the algebraic reductions and operator identities are proved.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.HarperFermiPicardFuchs

open Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour


/-- The phase-weighted Bloch symbol appearing in Li Eq. (5), with the phase
factors abstracted as nonzero complex numbers `A` and `B`. -/
def harperBlochSymbol (A B xi1 xi2 : ℂ) : ℂ :=
  A * xi1 + A⁻¹ * xi1⁻¹ + B * xi2 + B⁻¹ * xi2⁻¹

/-- The normalized Fermi-curve symbol after the phase change
`xi = A xi1`, `eta = B xi2`: `xi + xi^{-1} + eta + eta^{-1}`. -/
def normalizedFermiSymbol (xi eta : ℂ) : ℂ :=
  xi + xi⁻¹ + eta + eta⁻¹

/-- Li Eq. (11): the phase-weighted Harper component is carried to the
normalized Fermi symbol by `xi = A xi1`, `eta = B xi2`. -/
lemma harperBlochSymbol_eq_normalized
    {A B xi1 xi2 : ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hxi1 : xi1 ≠ 0) (hxi2 : xi2 ≠ 0) :
    harperBlochSymbol A B xi1 xi2 =
      normalizedFermiSymbol (A * xi1) (B * xi2) := by
  unfold harperBlochSymbol normalizedFermiSymbol
  field_simp [hA, hB, hxi1, hxi2]

/-- Polynomial form of the normalized Fermi curve after multiplying by
`xi eta`, matching Li's quadratic in `eta`. -/
def fermiQuadraticPolynomial (xi eta lam : ℂ) : ℂ :=
  xi * eta ^ 2 + (xi ^ 2 - lam * xi + 1) * eta + xi

/-- The normalized affine equation is equivalent to Li's quadratic equation
on `(C*)^2`. -/
lemma normalizedFermiEquation_iff_quadratic
    {xi eta lam : ℂ} (hxi : xi ≠ 0) (heta : eta ≠ 0) :
    normalizedFermiSymbol xi eta = lam ↔
      fermiQuadraticPolynomial xi eta lam = 0 := by
  constructor
  · intro h
    unfold normalizedFermiSymbol at h
    unfold fermiQuadraticPolynomial
    field_simp [hxi, heta] at h ⊢
    ring_nf at h ⊢
    linear_combination h
  · intro h
    unfold normalizedFermiSymbol
    unfold fermiQuadraticPolynomial at h
    field_simp [hxi, heta] at h ⊢
    ring_nf at h ⊢
    linear_combination h


/-- At `lambda = 0`, the Fermi curve splits into the two components
`xi + eta = 0` and `xi eta + 1 = 0`. -/
lemma fermiQuadraticPolynomial_zero_factor (xi eta : ℂ) :
    fermiQuadraticPolynomial xi eta 0 = (xi * eta + 1) * (xi + eta) := by
  unfold fermiQuadraticPolynomial
  ring

/-- The split fiber at `lambda = 0` is exactly the union of Li's two
components. -/
lemma fermiQuadraticPolynomial_zero_iff (xi eta : ℂ) :
    fermiQuadraticPolynomial xi eta 0 = 0 ↔
      xi * eta + 1 = 0 ∨ xi + eta = 0 := by
  rw [fermiQuadraticPolynomial_zero_factor]
  exact mul_eq_zero

/-- Formal partial derivative of Li's quadratic with respect to `xi`. -/
def fermiPartialXi (xi eta lam : ℂ) : ℂ :=
  eta ^ 2 + (2 * xi - lam) * eta + 1

/-- Formal partial derivative of Li's quadratic with respect to `eta`. -/
def fermiPartialEta (xi eta lam : ℂ) : ℂ :=
  2 * xi * eta + (xi ^ 2 - lam * xi + 1)

/-- The `lambda = 4` singular point of the normalized curve is `(1,1)`. -/
lemma fermi_singularPoint_four :
    fermiQuadraticPolynomial 1 1 4 = 0
      ∧ fermiPartialXi 1 1 4 = 0
      ∧ fermiPartialEta 1 1 4 = 0 := by
  norm_num [fermiQuadraticPolynomial, fermiPartialXi, fermiPartialEta]

/-- The `lambda = -4` singular point of the normalized curve is `(-1,-1)`. -/
lemma fermi_singularPoint_neg_four :
    fermiQuadraticPolynomial (-1) (-1) (-4) = 0
      ∧ fermiPartialXi (-1) (-1) (-4) = 0
      ∧ fermiPartialEta (-1) (-1) (-4) = 0 := by
  norm_num [fermiQuadraticPolynomial, fermiPartialXi, fermiPartialEta]

/-- One singular point of the split `lambda = 0` fiber is `(1,-1)`. -/
lemma fermi_singularPoint_zero_pos :
    fermiQuadraticPolynomial 1 (-1) 0 = 0
      ∧ fermiPartialXi 1 (-1) 0 = 0
      ∧ fermiPartialEta 1 (-1) 0 = 0 := by
  norm_num [fermiQuadraticPolynomial, fermiPartialXi, fermiPartialEta]

/-- The other singular point of the split `lambda = 0` fiber is `(-1,1)`. -/
lemma fermi_singularPoint_zero_neg :
    fermiQuadraticPolynomial (-1) 1 0 = 0
      ∧ fermiPartialXi (-1) 1 0 = 0
      ∧ fermiPartialEta (-1) 1 0 = 0 := by
  norm_num [fermiQuadraticPolynomial, fermiPartialXi, fermiPartialEta]

/-- The branch discriminant of Li's quadratic equation in `eta`. -/
def fermiDiscriminant (xi lam : ℂ) : ℂ :=
  (xi ^ 2 - lam * xi + 1) ^ 2 - 4 * xi ^ 2

/-- At `lambda = 4`, the branch discriminant has a double factor at
`xi = 1`, the ordinary double point of the `I_1` fiber. -/
lemma fermiDiscriminant_four_factor (xi : ℂ) :
    fermiDiscriminant xi 4 =
      (xi - 1) ^ 2 * (xi ^ 2 - 6 * xi + 1) := by
  unfold fermiDiscriminant
  ring

/-- At `lambda = -4`, the branch discriminant has a double factor at
`xi = -1`, the other `I_1` fiber. -/
lemma fermiDiscriminant_neg_four_factor (xi : ℂ) :
    fermiDiscriminant xi (-4) =
      (xi + 1) ^ 2 * (xi ^ 2 + 6 * xi + 1) := by
  unfold fermiDiscriminant
  ring

/-- At `lambda = 0`, both `xi = 1` and `xi = -1` are doubled, corresponding
to the split `I_2` fiber. -/
lemma fermiDiscriminant_zero_factor (xi : ℂ) :
    fermiDiscriminant xi 0 = (xi - 1) ^ 2 * (xi + 1) ^ 2 := by
  unfold fermiDiscriminant
  ring

/-- Li's involution quotient energy coordinate `mu = lambda^2 / 16`. -/
def quotientEnergyMu (lam : ℂ) : ℂ :=
  lam ^ 2 / 16

@[simp] lemma quotientEnergyMu_zero : quotientEnergyMu 0 = 0 := by
  norm_num [quotientEnergyMu]

@[simp] lemma quotientEnergyMu_four : quotientEnergyMu 4 = 1 := by
  norm_num [quotientEnergyMu]

@[simp] lemma quotientEnergyMu_neg_four : quotientEnergyMu (-4) = 1 := by
  norm_num [quotientEnergyMu]

/-- Li's real energy/modulus change `eps = (1-k)/(1+k)`.  The same formula
is its own inverse away from `k = -1`. -/
def energyFromModulus (k : ℝ) : ℝ :=
  (1 - k) / (1 + k)

/-- The modulus-energy change is involutive: applying it twice returns `k`. -/
lemma energyFromModulus_involutive {k : ℝ} (hk : 1 + k ≠ 0) :
    energyFromModulus (energyFromModulus k) = k := by
  unfold energyFromModulus
  field_simp [hk]
  ring


/-- Homology-level Picard-Lefschetz transformation
`T_delta(x) = x - (x · delta) delta`, with the signed intersection number
supplied as an integer. -/
def picardLefschetzTransform {Cycle : Type*} [AddCommGroup Cycle]
    (delta : Cycle) (intersection : ℤ) (x : Cycle) : Cycle :=
  x - intersection • delta

/-- Two vanishing cycles applied in the same local degeneration. -/
def twoCyclePicardLefschetzTransform {Cycle : Type*} [AddCommGroup Cycle]
    (delta1 delta2 : Cycle) (n1 n2 : ℤ) (x : Cycle) : Cycle :=
  x - n1 • delta1 - n2 • delta2

/-- Li Lemma 2.1 at `lambda = 4`: `T_4(gamma) = gamma + delta_1`. -/
lemma localMonodromy_four
    {Cycle : Type*} [AddCommGroup Cycle] (gamma delta1 : Cycle) :
    picardLefschetzTransform delta1 (-1) gamma = gamma + delta1 := by
  simp [picardLefschetzTransform]

/-- Li Lemma 2.1 at `lambda = -4`: `T_{-4}(gamma) = gamma - delta_2`. -/
lemma localMonodromy_neg_four
    {Cycle : Type*} [AddCommGroup Cycle] (gamma delta2 : Cycle) :
    picardLefschetzTransform delta2 1 gamma = gamma - delta2 := by
  simp [picardLefschetzTransform]

/-- Li Lemma 2.1 at `lambda = 0`: `T_0(gamma) = gamma - delta_1 + delta_2`. -/
lemma localMonodromy_zero
    {Cycle : Type*} [AddCommGroup Cycle] (gamma delta1 delta2 : Cycle) :
    twoCyclePicardLefschetzTransform delta1 delta2 1 (-1) gamma =
      gamma - delta1 + delta2 := by
  simp [twoCyclePicardLefschetzTransform]

/-- Li Lemma 4.1 at `k = 0`: `S_0(gamma) = gamma + delta_1`. -/
lemma kLocalMonodromy_zero
    {Cycle : Type*} [AddCommGroup Cycle] (gamma delta1 : Cycle) :
    picardLefschetzTransform delta1 (-1) gamma = gamma + delta1 :=
  localMonodromy_four gamma delta1

/-- Li Lemma 4.1 at `k = 1`: `S_1(gamma) = gamma + 2 delta_2 - 2 delta_3`. -/
lemma kLocalMonodromy_one
    {Cycle : Type*} [AddCommGroup Cycle] (gamma delta2 delta3 : Cycle) :
    twoCyclePicardLefschetzTransform delta2 delta3 (-2) 2 gamma =
      gamma + (2 : ℤ) • delta2 - (2 : ℤ) • delta3 := by
  simp [twoCyclePicardLefschetzTransform]

/-- A local monodromy event can be recorded in the repository's Stokes-connection
carrier when the two critical exponents are Stokes-aligned. -/
def localMonodromyStokesConnection (I0 I1 : ℂ) (multiplicity : ℤ)
    (haligned : I0.im = I1.im) : StokesConnection where
  source := stokesCriticalPoint I0
  target := stokesCriticalPoint I1
  multiplicity := multiplicity
  aligned := haligned

/-- The imported Picard-Lefschetz/Stokes layer exposes the conserved imaginary
part for a Li local monodromy connection. -/
lemma localMonodromyStokesConnection_imaginary_eq
    (I0 I1 : ℂ) (multiplicity : ℤ) (haligned : I0.im = I1.im) :
    (localMonodromyStokesConnection I0 I1 multiplicity haligned).source.exponent.im =
      (localMonodromyStokesConnection I0 I1 multiplicity haligned).target.exponent.im :=
  stokesConnection_imaginary_eq
    (localMonodromyStokesConnection I0 I1 multiplicity haligned)

/-- A Li local monodromy Stokes connection has a concrete Stokes flow line in
the imported Picard-Lefschetz contour carrier. -/
lemma localMonodromyStokesConnection_has_flowLine
    (I0 I1 : ℂ) (multiplicity : ℤ) (haligned : I0.im = I1.im) :
    Nonempty (ChernSimonsStokesFlowLine
      (localMonodromyStokesConnection I0 I1 multiplicity haligned)) :=
  chernSimonsStokesFlowLine_exists
    (localMonodromyStokesConnection I0 I1 multiplicity haligned)

/-- The usual downward-flow orientation for Li local monodromy is the ordinary
Picard-Lefschetz height ordering `Re I1 ≤ Re I0`. -/
lemma localMonodromyStokesConnection_heightOrdered_of_re_le
    {I0 I1 : ℂ} {multiplicity : ℤ} {haligned : I0.im = I1.im}
    (hre : I1.re ≤ I0.re) :
    (localMonodromyStokesConnection I0 I1 multiplicity haligned).HeightOrdered :=
  hre

/-- Under the explicit height-ordering hypothesis, Li local monodromy has a
downward gradient-flow line in the same contour layer used by the Chern-Simons
and trefoil analytic-continuation modules. -/
lemma localMonodromyStokesConnection_gradientFlowLine_exists
    (I0 I1 : ℂ) (multiplicity : ℤ) (haligned : I0.im = I1.im)
    (hre : I1.re ≤ I0.re) :
    Nonempty (ChernSimonsGradientFlowLine
      (localMonodromyStokesConnection I0 I1 multiplicity haligned)) :=
  chernSimonsGradientFlowLine_exists_of_heightOrdered
    (localMonodromyStokesConnection I0 I1 multiplicity haligned)
    (localMonodromyStokesConnection_heightOrdered_of_re_le hre)


/-- Li Eq. (15): normalized density of states `D = 2 pi^2 a b DOS`. -/
def normalizedDOS (a b dos : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * a * b * dos

/-- The period form of Li Eq. (12): `DOS = ((1+k)K(k))/(2 pi^2 a b)`. -/
def dosFromQuarterPeriod (a b k K : ℝ) : ℝ :=
  ((1 + k) * K) / (2 * Real.pi ^ 2 * a * b)

/-- Substituting Li Eq. (12) into Eq. (15) gives `D = (1+k)K(k)`. -/
lemma normalizedDOS_dosFromQuarterPeriod
    {a b k K : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedDOS a b (dosFromQuarterPeriod a b k K) = (1 + k) * K := by
  unfold normalizedDOS dosFromQuarterPeriod
  field_simp [ha, hb, Real.pi_ne_zero]

/-- Li Proposition 3.1, Eq. (16), as a residual on a second-order jet
`(D, D', D'')`. -/
def dosPicardFuchsResidual (k D D1 D2 : ℝ) : ℝ :=
  k * (1 - k) * (1 + k) ^ 2 * D2
    + (1 - 2 * k - k ^ 2) * (1 + k) * D1
    + (k - 1) * D

/-- `D` satisfies Li's density-of-states Picard-Fuchs equation at `k`. -/
def SatisfiesDOSPicardFuchs (k D D1 D2 : ℝ) : Prop :=
  dosPicardFuchsResidual k D D1 D2 = 0

/-- Logarithmic first derivative `Theta D = k D'`. -/
def thetaD (k D1 : ℝ) : ℝ :=
  k * D1

/-- Logarithmic second derivative `Theta^2 D = k D' + k^2 D''`. -/
def theta2D (k D1 D2 : ℝ) : ℝ :=
  k * D1 + k ^ 2 * D2

/-- Li Eq. (23), the logarithmic-operator residual. -/
def dosThetaResidual (k D D1 D2 : ℝ) : ℝ :=
  theta2D k D1 D2
    + (2 * k / (k ^ 2 - 1)) * thetaD k D1
    - k / (1 + k) ^ 2 * D

/-- Eq. (16) and the logarithmic-operator form Eq. (23) are the same equation
away from the regular singularities. -/
lemma dosThetaResidual_scaled_eq_picardFuchs
    {k D D1 D2 : ℝ}
    (hk : k ≠ 0) (hm : k ^ 2 - 1 ≠ 0) (hkp : 1 + k ≠ 0) :
    ((1 - k) * (1 + k) ^ 2 / k) * dosThetaResidual k D D1 D2 =
      dosPicardFuchsResidual k D D1 D2 := by
  unfold dosThetaResidual dosPicardFuchsResidual thetaD theta2D
  field_simp [hk, hm, hkp]
  ring_nf

/-- Li Corollary 3.2, Eq. (24), in the energy variable `eps`. -/
def energyPicardFuchsResidual (eps D D1 D2 : ℝ) : ℝ :=
  eps * (1 - eps ^ 2) * D2 + (1 - 3 * eps ^ 2) * D1 - eps * D

/-- Li Eq. (25), `[theta^2 - eps^2 (theta+1)^2]D`, on a second-order jet. -/
def energyThetaResidual (eps D D1 D2 : ℝ) : ℝ :=
  theta2D eps D1 D2
    - eps ^ 2 * (theta2D eps D1 D2 + 2 * thetaD eps D1 + D)

/-- Eq. (25) is Eq. (24) multiplied by `eps`; hence the two residuals have
the same zero set away from `eps = 0`. -/
lemma energyThetaResidual_eq_scaled_picardFuchs
    (eps D D1 D2 : ℝ) :
    energyThetaResidual eps D D1 D2 =
      eps * energyPicardFuchsResidual eps D D1 D2 := by
  unfold energyThetaResidual energyPicardFuchsResidual thetaD theta2D
  ring


/-- Landen transformed modulus using a chosen square root `r^2 = k`. -/
def landenModulusFromRoot (r k : ℝ) : ℝ :=
  2 * r / (1 + k)

/-- Complementary Landen modulus `(1-k)/(1+k)`. -/
def landenComplement (k : ℝ) : ℝ :=
  (1 - k) / (1 + k)

/-- Li Eq. (28): the Landen transformed modulus and its complement square to
one. -/
lemma landen_square_sum
    {r k : ℝ} (hr : r ^ 2 = k) (hk : 1 + k ≠ 0) :
    (landenModulusFromRoot r k) ^ 2 + (landenComplement k) ^ 2 = 1 := by
  unfold landenModulusFromRoot landenComplement
  field_simp [hk]
  nlinarith [hr]

/-- Li Eq. (41), the Q-form potential for `U'' + Q(k) U = 0`. -/
def qFormPotential (k : ℝ) : ℝ :=
  (1 + k ^ 2) ^ 2 / (4 * k ^ 2 * (1 - k ^ 2) ^ 2)

/-- Li Eq. (44), the Schwarzian potential for the period ratio `{t,k}`. -/
def periodRatioSchwarzianPotential (k : ℝ) : ℝ :=
  (1 + k ^ 2) ^ 2 / (2 * k ^ 2 * (1 - k ^ 2) ^ 2)

/-- The Schwarzian potential is twice the Q-form potential, as expected for
the ratio of two independent solutions of `U'' + Q U = 0`, away from the
regular singularities `k = 0, ±1`. -/
lemma periodRatioSchwarzianPotential_eq_two_qFormPotential
    {k : ℝ} (hk : k ≠ 0) (hm : 1 - k ^ 2 ≠ 0) :
    periodRatioSchwarzianPotential k = 2 * qFormPotential k := by
  unfold periodRatioSchwarzianPotential qFormPotential
  field_simp [hk, hm]
  ring

/-- Li Proposition 4.3, Eq. (46), as the energy Schwarzian potential. -/
def energySchwarzianPotential (eps epsPrime : ℝ) : ℝ :=
  -epsPrime ^ 2 * (1 + eps ^ 2) ^ 2 /
    (2 * eps ^ 2 * (1 - eps ^ 2) ^ 2)

/-- The modular `j`-function expression in Li Eq. (33), in the energy
variable `eps`. -/
def modularJFromEnergy (eps : ℝ) : ℝ :=
  256 * (eps ^ 4 - eps ^ 2 + 1) ^ 3 /
    (eps ^ 4 * (eps ^ 2 - 1) ^ 2)

/-- The same `j` expression after the quotient `mu = eps^2`. -/
def modularJFromMu (mu : ℝ) : ℝ :=
  256 * (mu ^ 2 - mu + 1) ^ 3 /
    (mu ^ 2 * (mu - 1) ^ 2)

/-- Li Eq. (33) is literally the same rational function after substituting
`mu = eps^2`. -/
lemma modularJFromEnergy_eq_modularJFromMu (eps : ℝ) :
    modularJFromEnergy eps = modularJFromMu (eps ^ 2) := by
  unfold modularJFromEnergy modularJFromMu
  ring_nf

/-- The bracketed truncation in Li Theorem 4.5:
`epsilon = 1 - 8(Q/4 - 4(Q/4)^2 + 12(Q/4)^3 - ...)`. -/
def mirrorEnergyQ5 (Q : ℝ) : ℝ :=
  1 - 8 *
    (Q / 4
      - 4 * (Q / 4) ^ 2
      + 12 * (Q / 4) ^ 3
      - 32 * (Q / 4) ^ 4
      + 78 * (Q / 4) ^ 5)

/-- The displayed bracketed Q-expansion equals the ordinary polynomial form
through the `Q^5` term. -/
lemma mirrorEnergyQ5_eq_polynomial (Q : ℝ) :
    mirrorEnergyQ5 Q =
      1 - 2 * Q + 2 * Q ^ 2 - (3 / 2) * Q ^ 3
        + Q ^ 4 - (39 / 64) * Q ^ 5 := by
  unfold mirrorEnergyQ5
  ring

/-- Li Eq. (31), written with `s = q^{1/2}` through the displayed `s^5`
term. -/
def energyMuS5 (s : ℝ) : ℝ :=
  1 - 16 * (s - 8 * s ^ 2 + 44 * s ^ 3 - 192 * s ^ 4 + 718 * s ^ 5)

/-- With the paper's identification `Q = 4 q^{1/2}`, the square of the
Theorem 4.5 energy expansion agrees with the Eq. (31) `mu = eps^2`
q-expansion through order `s^5`; the difference starts at `s^6`. -/
lemma mirrorEnergyQ5_square_matches_energyMuS5_through_order_five (s : ℝ) :
    (mirrorEnergyQ5 (4 * s)) ^ 2 - energyMuS5 s =
      s ^ 6 * (35584 - 89088 * s + 185344 * s ^ 2
        - 319488 * s ^ 3 + 389376 * s ^ 4) := by
  unfold mirrorEnergyQ5 energyMuS5
  ring


/-- Real version of Li's branch discriminant.  This is separated from the
complex Fermi-curve expression so it can be compared directly with the real
Hatsugai transfer-matrix surface. -/
def realFermiDiscriminant (x lam : ℝ) : ℝ :=
  (x ^ 2 - lam * x + 1) ^ 2 - 4 * x ^ 2

/-- The Harper trace coordinate whose hyperelliptic discriminant is
`Delta^2 - 4`. -/
def realHarperTraceFromCoordinate (x lam : ℝ) : ℝ :=
  x + x⁻¹ - lam

/-- Li's Fermi-curve branch discriminant is exactly `x^2` times Hatsugai's
hyperelliptic transfer discriminant after the Harper trace substitution. -/
lemma realFermiDiscriminant_eq_x_sq_hatsugaiHyperellipticDiscriminant
    {x lam : ℝ} (hx : x ≠ 0) :
    realFermiDiscriminant x lam =
      x ^ 2 *
        hatsugaiHyperellipticDiscriminant
          (realHarperTraceFromCoordinate x lam) := by
  unfold realFermiDiscriminant hatsugaiHyperellipticDiscriminant
    realHarperTraceFromCoordinate
  field_simp [hx]
  ring

/-- Away from `x = 0`, Li branch points are exactly Hatsugai branch points for
the same Harper trace.  This is the nontrivial branch-surface link between the
Fermi-curve/Picard-Fuchs paper and the IQHE bulk-edge file. -/
lemma realFermiDiscriminant_zero_iff_hatsugaiHyperellipticBranch
    {x lam : ℝ} (hx : x ≠ 0) :
    realFermiDiscriminant x lam = 0 ↔
      hatsugaiHyperellipticDiscriminant
        (realHarperTraceFromCoordinate x lam) = 0 := by
  rw [realFermiDiscriminant_eq_x_sq_hatsugaiHyperellipticDiscriminant hx]
  exact mul_eq_zero.trans
    (by simp [pow_ne_zero 2 hx])


/-- The Li normalized Fermi equation is the same Harper recurrence spectral
object used by the IQHE Hatsugai module: a Fermi point carries a transfer-step
recurrence datum once the one-step angle and dimensionless energy are supplied. -/
structure HarperFermiTransferPoint where
  eps : ℝ
  theta : ℝ
  psiPrev : ℝ
  psi : ℝ
  psiNext : ℝ
  recurrence : HarperRecurrenceAt eps theta psiPrev psi psiNext

namespace HarperFermiTransferPoint

/-- Every Li Fermi-transfer point is advanced by the existing Hatsugai/Harper
transfer matrix. -/
lemma transferMatrix_step (P : HarperFermiTransferPoint) :
    (hatsugaiTransferMatrix P.eps P.theta).mulVec ![P.psi, P.psiPrev] =
      ![P.psiNext, P.psi] :=
  harperRecurrence_transferMatrix_step P.recurrence

end HarperFermiTransferPoint

end Physlib.QuantumMechanics.ComplexAction.HarperFermiPicardFuchs

end
