/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux
public import Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge
public import Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
public import Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential
public meta import Physlib.Meta.Zil

/-!
# Maxwell--Chern--Simons solitons from type-IIB strings

This file formalizes the quantitative core of B.-H. Lee, H.-j. Lee, N. Ohta, and H. S. Yang,
*Maxwell Chern--Simons solitons from type IIB string theory*, Phys. Rev. D **60** (1999), 106003.
It connects the paper to the repository's existing Maxwell--Chern--Simons equation, DJT topological
mass, and continuous Abelian flux carrier rather than introducing parallel gauge infrastructure.

* **# A** proves the type-IIB `(qF,qD)` string-tension formula (Eq. 33), including the pure F-string
  and axion-dressed D-string sectors.
* **# B** identifies the paper's vector-multiplet mass with the repository's DJT mass at integer
  level and proves the paper's compactification realization of the pure-Chern--Simons limit: as
  `L6 -> 0+`, the mass diverges while the Maxwell coefficient vanishes.
* **# C** formalizes the `N = 2` and `N = 3` scalar potentials (Eqs. 45 and 48), classifies the
  complete algebraic zero loci of both, and proves the displayed vacuum branches.
* **# D** records the BPS vortex mass/moduli relation and proves the nontopological
  `Phi = -Q/kappa = 2 pi (n+alpha)` chain through the existing `deserFlux` definition.
* **# E** proves that the coupling map `kappa -> -1/kappa` is involutive and the type-IIB
  `S`-duality charge map `(qF,qD) -> (qD,-qF)` has order four and preserves primitive charge
  sectors.
* **# F** connects the three-dimensional MCS vacuum to the genuine Lovelock tensor layer: the
  metric potential source vanishes exactly on the classified vacuum locus, only Lovelock orders
  `p = 0,1` survive in dimension three, and the existing pure-Lovelock affine first integral then
  yields the source-free order-one Lovelock field equation.

**Honest scope.** The real identities and limits below are proved. The identification of strings with
vortices, the brane-engineered low-energy action, the BPS mass formula, and the integer/string-charge
dictionary are physical inputs from the paper. The module does not construct the underlying type-IIB
supergravity background. In particular, it does not claim the finite-energy BPS domain-wall solution
that the paper explicitly leaves open, and it does not extend the paper's Abelian analysis to a
non-Abelian vortex theory. The Lovelock bridge carries only the metric-proportional scalar-potential
source `U g`; it does not identify that term with the complete Maxwell--Chern--Simons stress tensor or
derive the gravitational coupling from the brane construction.

## References

* B.-H. Lee, H.-j. Lee, N. Ohta, H. S. Yang, Phys. Rev. D **60** (1999), 106003,
  Eqs. (33), (43)--(47), Secs. III.B and IV.
-/

set_option autoImplicit false

open Topology
open Real (pi)
open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux
open Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
open Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination
open Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential

/-! # A. Type-IIB string tension and the axion shift -/

/-- **Lee et al. Eq. (33).** The type-IIB `(qF,qD)` string tension in a constant RR-axion
background `chi`, with string length `stringLength` and coupling `stringCoupling`.

The integer pair is ordered as F-string charge followed by D-string charge. -/
noncomputable def iibStringTension
    (stringLength stringCoupling chi : ℝ) (qF qD : ℤ) : ℝ :=
  Real.sqrt (((qF : ℝ) + (qD : ℝ) * chi) ^ 2 +
      (qD : ℝ) ^ 2 / stringCoupling ^ 2) /
    (2 * pi * stringLength ^ 2)

/-- The type-IIB string tension is nonnegative whenever the string length is nonzero. -/
lemma iibStringTension_nonneg
    (stringLength stringCoupling chi : ℝ) (qF qD : ℤ)
    (hLength : stringLength ≠ 0) :
    0 ≤ iibStringTension stringLength stringCoupling chi qF qD := by
  exact div_nonneg (Real.sqrt_nonneg _)
    (le_of_lt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_ne_zero hLength)))

/-- The pure F-string sector of Eq. (33) is independent of the axion and string coupling. -/
lemma iibFStringTension
    (stringLength stringCoupling chi : ℝ) (qF : ℤ) :
    iibStringTension stringLength stringCoupling chi qF 0 =
      |(qF : ℝ)| / (2 * pi * stringLength ^ 2) := by
  unfold iibStringTension
  norm_num [Real.sqrt_sq_eq_abs]

/-- **The axion-dressed D-string tension.** With the paper's world-volume dictionary
`kappa = -chi`, the `(0,1)` tension contains `sqrt (kappa^2 + g_s^-2)`. -/
@[zil_level physical_theorem]
lemma iibDStringTension_axion_eq_neg_coupling
    (stringLength stringCoupling kappa : ℝ) :
    iibStringTension stringLength stringCoupling (-kappa) 0 1 =
      Real.sqrt (kappa ^ 2 + 1 / stringCoupling ^ 2) /
        (2 * pi * stringLength ^ 2) := by
  unfold iibStringTension
  norm_num

/-- **The axion-dressed D-string is no lighter than the zero-axion D-string.** The
`kappa^2` contribution in Eq. (33) raises the `(0,1)` string tension; this is a derived inequality,
not an additional brane-model premise. -/
@[zil_level physical_theorem]
lemma iibDStringTension_minimal_at_zero
    (stringLength stringCoupling kappa : ℝ) (hLength : stringLength ≠ 0) :
    iibStringTension stringLength stringCoupling 0 0 1 ≤
      iibStringTension stringLength stringCoupling (-kappa) 0 1 := by
  calc
    iibStringTension stringLength stringCoupling 0 0 1 =
        Real.sqrt (0 ^ 2 + 1 / stringCoupling ^ 2) /
          (2 * pi * stringLength ^ 2) := by
      simpa only [neg_zero] using
        iibDStringTension_axion_eq_neg_coupling stringLength stringCoupling 0
    _ ≤ Real.sqrt (kappa ^ 2 + 1 / stringCoupling ^ 2) /
          (2 * pi * stringLength ^ 2) := by
      apply div_le_div_of_nonneg_right _
        (le_of_lt (mul_pos (mul_pos (by norm_num) Real.pi_pos)
          (sq_pos_of_ne_zero hLength)))
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg kappa]
    _ = iibStringTension stringLength stringCoupling (-kappa) 0 1 :=
      (iibDStringTension_axion_eq_neg_coupling
        stringLength stringCoupling kappa).symm

/-- The charge combination under the square root in Eq. (33), isolating the RR-axion analogue of
Witten's electric-charge shift. -/
def iibAxionShiftedFStringCharge (chi : ℝ) (qF qD : ℤ) : ℝ :=
  (qF : ℝ) + (qD : ℝ) * chi

/-- A D-string in the background `chi = -kappa` carries shifted F-string charge `-kappa` in the
paper's sign convention. This is the charge-level content of the Witten-effect interpretation. -/
lemma iibDString_axionShiftedCharge (kappa : ℝ) :
    iibAxionShiftedFStringCharge (-kappa) 0 1 = -kappa := by
  simp [iibAxionShiftedFStringCharge]

/-! # B. Topological mass and the pure-Chern--Simons limit -/

/-- The `N = 2` vector-multiplet mass `|kappa| g^2` following Eq. (43). The second argument is the
squared gauge coupling itself, matching the three-dimensional convention used in the paper. -/
noncomputable def vectorMultipletMass (kappa gaugeCouplingSq : ℝ) : ℝ :=
  |kappa| * gaugeCouplingSq

/-- **The Lee vector mass is the existing DJT topological mass.** At integer level `level` and
`kappa = level/(2 pi)`, the paper's `|kappa| e^2` equals the repository definition
`topologicalMass {e,level}`. -/
@[zil_level bridge_theorem]
lemma vectorMultipletMass_eq_djtTopologicalMass (e : ℝ) (level : ℤ) :
    vectorMultipletMass ((level : ℝ) / (2 * pi)) (e ^ 2) =
      topologicalMass { e := e, level := level } := by
  unfold vectorMultipletMass topologicalMass
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  ring

/-- At fixed nonzero Chern--Simons coupling, the vector-multiplet mass diverges as the squared gauge
coupling tends to infinity. This is the massive half of the paper's pure-CS decoupling limit. -/
@[zil_level physical_theorem]
lemma pureChernSimons_vectorMass_tendsto_atTop (kappa : ℝ) (hkappa : kappa ≠ 0) :
    Filter.Tendsto (fun gaugeCouplingSq : ℝ => vectorMultipletMass kappa gaugeCouplingSq)
      Filter.atTop Filter.atTop := by
  exact Filter.Tendsto.const_mul_atTop (abs_pos.mpr hkappa) Filter.tendsto_id

/-- The Maxwell kinetic coefficient `1/g^2` vanishes in the same strong-coupling limit. -/
@[zil_level physical_theorem]
lemma pureChernSimons_maxwellCoefficient_tendsto_zero :
    Filter.Tendsto (fun gaugeCouplingSq : ℝ => 1 / gaugeCouplingSq)
      Filter.atTop (nhds 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero

/-- **The complete algebraic pure-CS limit.** At fixed nonzero `kappa`, the vector multiplet becomes
infinitely massive while the Maxwell kinetic coefficient vanishes. This states the two limits proved
here; interpreting them as decoupling of the Maxwell multiplet uses the action in Eq. (43). -/
@[zil_level physical_theorem]
theorem pureChernSimons_decoupling_limit (kappa : ℝ) (hkappa : kappa ≠ 0) :
    Filter.Tendsto (fun gaugeCouplingSq : ℝ => vectorMultipletMass kappa gaugeCouplingSq)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun gaugeCouplingSq : ℝ => 1 / gaugeCouplingSq)
        Filter.atTop (nhds 0) :=
  ⟨pureChernSimons_vectorMass_tendsto_atTop kappa hkappa,
    pureChernSimons_maxwellCoefficient_tendsto_zero⟩

/-! ## B.1. Compactification realizes the strong-coupling limit -/

/-- The Maxwell coefficient obtained from the paper's interval/string-coupling dictionary
`1/g^2 = L6/g_s`. -/
noncomputable def maxwellCoefficientFromInterval (L6 stringCoupling : ℝ) : ℝ :=
  L6 / stringCoupling

/-- The squared gauge coupling obtained by inverting `1/g^2 = L6/g_s`. The physical use below
approaches `L6 = 0` through positive lengths and assumes positive string coupling. -/
noncomputable def gaugeCouplingSqFromInterval (L6 stringCoupling : ℝ) : ℝ :=
  stringCoupling / L6

/-- Shrinking the compactification interval makes the paper's Maxwell coefficient vanish. -/
lemma maxwellCoefficientFromInterval_tendsto_zero (stringCoupling : ℝ) :
    Filter.Tendsto (fun L6 : ℝ => maxwellCoefficientFromInterval L6 stringCoupling)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [maxwellCoefficientFromInterval] using
    (Filter.Tendsto.div_const (Filter.tendsto_id (x := nhds (0 : ℝ))) stringCoupling).mono_left
      nhdsWithin_le_nhds

/-- At positive string coupling, shrinking the compactification interval sends the squared gauge
coupling `g_s/L6` to infinity. -/
lemma gaugeCouplingSqFromInterval_tendsto_atTop
    (stringCoupling : ℝ) (hstring : 0 < stringCoupling) :
    Filter.Tendsto (fun L6 : ℝ => gaugeCouplingSqFromInterval L6 stringCoupling)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  simpa [gaugeCouplingSqFromInterval, div_eq_mul_inv] using
    Filter.Tendsto.const_mul_atTop hstring tendsto_inv_nhdsGT_zero

/-- **The paper's compactification route to the pure-CS mass limit.** At fixed nonzero
`kappa` and positive `g_s`, the vector multiplet becomes infinitely massive as `L6 -> 0+`. -/
@[zil_level physical_theorem]
theorem compactification_vectorMass_tendsto_atTop
    (kappa stringCoupling : ℝ) (hkappa : kappa ≠ 0) (hstring : 0 < stringCoupling) :
    Filter.Tendsto
      (fun L6 : ℝ => vectorMultipletMass kappa
        (gaugeCouplingSqFromInterval L6 stringCoupling))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  exact (pureChernSimons_vectorMass_tendsto_atTop kappa hkappa).comp
    (gaugeCouplingSqFromInterval_tendsto_atTop stringCoupling hstring)

/-! # C. Supersymmetric scalar potentials and their vacuum branches

## C.1. The `N = 2` scalar potential
-/

/-- **Lee et al. Eq. (45).** The `N = 2` Maxwell--Chern--Simons scalar potential, written in
terms of the nonnegative squared amplitudes `qSq = |q|^2` and `qTildeSq = |qTilde|^2`. -/
noncomputable def mcsPotential
    (gaugeCouplingSq qSq qTildeSq v kappa X5 : ℝ) : ℝ :=
  gaugeCouplingSq / 2 * (qSq - qTildeSq - v ^ 2 + kappa * X5) ^ 2 +
    X5 ^ 2 * (qSq + qTildeSq)

/-- The Maxwell--Chern--Simons scalar potential is nonnegative on physical squared amplitudes. -/
lemma mcsPotential_nonneg
    (gaugeCouplingSq qSq qTildeSq v kappa X5 : ℝ)
    (hg : 0 ≤ gaugeCouplingSq) (hq : 0 ≤ qSq) (hqt : 0 ≤ qTildeSq) :
    0 ≤ mcsPotential gaugeCouplingSq qSq qTildeSq v kappa X5 := by
  unfold mcsPotential
  exact add_nonneg
    (mul_nonneg (div_nonneg hg (by norm_num)) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (add_nonneg hq hqt))

/-- **Complete zero-potential classification for Eq. (45).** For positive gauge coupling and
physical squared amplitudes, `U = 0` iff either

* `X5 = 0` and `|q|^2 - |qTilde|^2 = v^2` (the Higgs branch), or
* both charged amplitudes vanish and `kappa X5 = v^2` (the symmetric branch).

Thus the two vacua displayed in Eqs. (46)--(47) are not merely checked by substitution: they are the
two branches forced by nonnegativity of the full scalar potential. -/
@[zil_level physical_theorem]
theorem mcsPotential_eq_zero_iff
    (gaugeCouplingSq qSq qTildeSq v kappa X5 : ℝ)
    (hg : 0 < gaugeCouplingSq) (hq : 0 ≤ qSq) (hqt : 0 ≤ qTildeSq) :
    mcsPotential gaugeCouplingSq qSq qTildeSq v kappa X5 = 0 ↔
      (X5 = 0 ∧ qSq - qTildeSq = v ^ 2) ∨
      (qSq = 0 ∧ qTildeSq = 0 ∧ kappa * X5 = v ^ 2) := by
  constructor
  · intro hU
    let balance := qSq - qTildeSq - v ^ 2 + kappa * X5
    have hcoef : 0 < gaugeCouplingSq / 2 := div_pos hg (by norm_num)
    have hfirst : 0 ≤ gaugeCouplingSq / 2 * balance ^ 2 :=
      mul_nonneg hcoef.le (sq_nonneg _)
    have hsecond : 0 ≤ X5 ^ 2 * (qSq + qTildeSq) :=
      mul_nonneg (sq_nonneg _) (add_nonneg hq hqt)
    have hsum : gaugeCouplingSq / 2 * balance ^ 2 +
        X5 ^ 2 * (qSq + qTildeSq) = 0 := by
      simpa [mcsPotential, balance] using hU
    have hfirstZero : gaugeCouplingSq / 2 * balance ^ 2 = 0 := by linarith
    have hbalanceSq : balance ^ 2 = 0 :=
      (mul_eq_zero.mp hfirstZero).resolve_left hcoef.ne'
    have hbalance : balance = 0 := sq_eq_zero_iff.mp hbalanceSq
    have hsecondZero : X5 ^ 2 * (qSq + qTildeSq) = 0 := by linarith
    rcases mul_eq_zero.mp hsecondZero with hX | hcharges
    · left
      have hX0 : X5 = 0 := sq_eq_zero_iff.mp hX
      exact ⟨hX0, by simp [balance, hX0] at hbalance; linarith⟩
    · right
      have hq0 : qSq = 0 := by linarith
      have hqt0 : qTildeSq = 0 := by linarith
      refine ⟨hq0, hqt0, ?_⟩
      simp [balance, hq0, hqt0] at hbalance
      linarith
  · rintro (⟨hX, hbalance⟩ | ⟨hq, hqt, hkX⟩)
    · subst X5
      have hzero : qSq - qTildeSq - v ^ 2 + kappa * 0 = 0 := by linarith
      unfold mcsPotential
      rw [hzero]
      ring
    · subst qSq
      subst qTildeSq
      have hzero : (0 : ℝ) - 0 - v ^ 2 + kappa * X5 = 0 := by linarith
      unfold mcsPotential
      rw [hzero]
      ring

/-- **Eq. (46).** The displayed symmetry-broken vacuum lies on the Higgs branch. -/
lemma mcsPotential_brokenVacuum (gaugeCouplingSq v kappa : ℝ) :
    mcsPotential gaugeCouplingSq (v ^ 2) 0 v kappa 0 = 0 := by
  unfold mcsPotential
  ring

/-- **Eq. (47).** For nonzero Chern--Simons coupling, the displayed symmetry-unbroken vacuum has
`X5 = v^2/kappa` and zero charged amplitudes. -/
lemma mcsPotential_unbrokenVacuum
    (gaugeCouplingSq v kappa : ℝ) (hkappa : kappa ≠ 0) :
    mcsPotential gaugeCouplingSq 0 0 v kappa (v ^ 2 / kappa) = 0 := by
  unfold mcsPotential
  field_simp
  ring

/-! ## C.2. The `N = 3` scalar potential -/

/-- **Lee et al. Eq. (48).** The `N = 3` Maxwell--Chern--Simons scalar potential. Complex norms
represent `|q|^2`, `|qTilde|^2`, `|q qTilde + kappa phi - w^2|^2`, and `|phi|^2` directly rather
than replacing the complex F-term by an unrelated real variable. -/
noncomputable def nThreeMCSPotential
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) : ℝ :=
  gaugeCouplingSq / 2 *
      (Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * X5) ^ 2 +
    gaugeCouplingSq / 2 * Complex.normSq (q * qTilde + (kappa : ℂ) * phi - wSq) +
    (Complex.normSq q + Complex.normSq qTilde) *
      (X3 ^ 2 + Complex.normSq phi)

/-- The complete `N = 3` potential is nonnegative when the squared gauge coupling is nonnegative. -/
lemma nThreeMCSPotential_nonneg
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (hg : 0 ≤ gaugeCouplingSq) :
    0 ≤ nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq := by
  unfold nThreeMCSPotential
  have hcoef : 0 ≤ gaugeCouplingSq / 2 := div_nonneg hg (by norm_num)
  exact add_nonneg
    (add_nonneg (mul_nonneg hcoef (sq_nonneg _))
      (mul_nonneg hcoef (Complex.normSq_nonneg _)))
    (mul_nonneg
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)))

/-- A sum of two complex squared norms vanishes exactly when both complex values vanish. -/
lemma complexNormSq_add_eq_zero_iff (z w : ℂ) :
    Complex.normSq z + Complex.normSq w = 0 ↔ z = 0 ∧ w = 0 := by
  constructor
  · intro h
    have hz : Complex.normSq z = 0 := by
      nlinarith [Complex.normSq_nonneg z, Complex.normSq_nonneg w]
    have hw : Complex.normSq w = 0 := by
      nlinarith [Complex.normSq_nonneg z, Complex.normSq_nonneg w]
    exact ⟨Complex.normSq_eq_zero.mp hz, Complex.normSq_eq_zero.mp hw⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A real square plus a complex squared norm vanishes exactly when both values vanish. -/
lemma sq_add_complexNormSq_eq_zero_iff (x : ℝ) (z : ℂ) :
    x ^ 2 + Complex.normSq z = 0 ↔ x = 0 ∧ z = 0 := by
  constructor
  · intro h
    have hx : x ^ 2 = 0 := by nlinarith [Complex.normSq_nonneg z]
    have hz : Complex.normSq z = 0 := by nlinarith [sq_nonneg x]
    exact ⟨sq_eq_zero_iff.mp hx, Complex.normSq_eq_zero.mp hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- **Complete zero-potential classification for Lee et al. Eq. (48).** At positive gauge
coupling, the `N = 3` potential vanishes iff its D- and F-flat equations hold and either both
charged scalars vanish or both neutral scalar contributions vanish. This proves that the two
displayed vacua are the two algebraic branch types forced by the full nonnegative potential. -/
@[zil_level physical_theorem]
theorem nThreeMCSPotential_eq_zero_iff
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (hg : 0 < gaugeCouplingSq) :
    nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq = 0 ↔
      Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * X5 = 0 ∧
      q * qTilde + (kappa : ℂ) * phi - wSq = 0 ∧
      ((q = 0 ∧ qTilde = 0) ∨ (X3 = 0 ∧ phi = 0)) := by
  let D := Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * X5
  let F := q * qTilde + (kappa : ℂ) * phi - wSq
  let Q := Complex.normSq q + Complex.normSq qTilde
  let S := X3 ^ 2 + Complex.normSq phi
  have hc : 0 < gaugeCouplingSq / 2 := div_pos hg (by norm_num)
  have hDnonneg : 0 ≤ gaugeCouplingSq / 2 * D ^ 2 := mul_nonneg hc.le (sq_nonneg D)
  have hFnonneg : 0 ≤ gaugeCouplingSq / 2 * Complex.normSq F :=
    mul_nonneg hc.le (Complex.normSq_nonneg F)
  have hQnonneg : 0 ≤ Q := add_nonneg (Complex.normSq_nonneg q) (Complex.normSq_nonneg qTilde)
  have hSnonneg : 0 ≤ S := add_nonneg (sq_nonneg X3) (Complex.normSq_nonneg phi)
  have hQSnonneg : 0 ≤ Q * S := mul_nonneg hQnonneg hSnonneg
  constructor
  · intro hU
    have hsum : gaugeCouplingSq / 2 * D ^ 2 +
        gaugeCouplingSq / 2 * Complex.normSq F + Q * S = 0 := by
      simpa [nThreeMCSPotential, D, F, Q, S] using hU
    have hDz : gaugeCouplingSq / 2 * D ^ 2 = 0 := by linarith
    have hFz : gaugeCouplingSq / 2 * Complex.normSq F = 0 := by linarith
    have hQSz : Q * S = 0 := by linarith
    have hD : D = 0 :=
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hDz).resolve_left hc.ne')
    have hF : F = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hFz).resolve_left hc.ne')
    refine ⟨by simpa [D] using hD, by simpa [F] using hF, ?_⟩
    rcases mul_eq_zero.mp hQSz with hQ | hS
    · exact Or.inl (by simpa [Q] using (complexNormSq_add_eq_zero_iff q qTilde).mp hQ)
    · exact Or.inr (by simpa [S] using (sq_add_complexNormSq_eq_zero_iff X3 phi).mp hS)
  · rintro ⟨hD, hF, (⟨hq, hqt⟩ | ⟨hX3, hphi⟩)⟩
    · unfold nThreeMCSPotential
      rw [hD, hF]
      simp [hq, hqt]
    · unfold nThreeMCSPotential
      rw [hD, hF]
      simp [hX3, hphi]

/-- **Eq. (49), the `N = 3` broken vacuum.** The D-flat constraint
`|q|^2-|qTilde|^2=v^2`, F-flat constraint `q qTilde=w^2`, and `phi=X3=X5=0` make every
nonnegative summand in Eq. (48) vanish. -/
@[zil_level physical_theorem]
lemma nThreeMCSPotential_brokenVacuum
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa : ℝ) (wSq : ℂ)
    (hD : Complex.normSq q - Complex.normSq qTilde = v ^ 2)
    (hF : q * qTilde = wSq) :
    nThreeMCSPotential gaugeCouplingSq q qTilde v kappa 0 0 0 wSq = 0 := by
  unfold nThreeMCSPotential
  rw [show Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * 0 = 0 by
    rw [hD]
    ring]
  rw [show q * qTilde + (kappa : ℂ) * 0 - wSq = 0 by
    rw [hF]
    ring]
  simp

/-- The symmetric `N = 3` branch vanishes whenever its two displayed D/F-flat constraints
`kappa X5=v^2` and `kappa phi=w^2` hold. The arbitrary `X3` drops out because both charged
amplitudes vanish. -/
lemma nThreeMCSPotential_unbrokenVacuum_of_constraints
    (gaugeCouplingSq v kappa X5 X3 : ℝ) (phi wSq : ℂ)
    (hD : kappa * X5 = v ^ 2) (hF : (kappa : ℂ) * phi = wSq) :
    nThreeMCSPotential gaugeCouplingSq 0 0 v kappa X5 X3 phi wSq = 0 := by
  unfold nThreeMCSPotential
  rw [show Complex.normSq 0 - Complex.normSq 0 - v ^ 2 + kappa * X5 = 0 by
    simp
    linarith]
  rw [show (0 : ℂ) * 0 + (kappa : ℂ) * phi - wSq = 0 by
    rw [hF]
    ring]
  simp

/-- **Eq. (50), the explicit `N = 3` symmetry-unbroken vacuum.** For nonzero `kappa`, the
configuration `q=qTilde=0`, `X5=v^2/kappa`, and `phi=w^2/kappa` has zero potential. -/
@[zil_level physical_theorem]
lemma nThreeMCSPotential_unbrokenVacuum
    (gaugeCouplingSq v kappa X3 : ℝ) (wSq : ℂ) (hkappa : kappa ≠ 0) :
    nThreeMCSPotential gaugeCouplingSq 0 0 v kappa (v ^ 2 / kappa) X3
      (wSq / (kappa : ℂ)) wSq = 0 := by
  apply nThreeMCSPotential_unbrokenVacuum_of_constraints
  · field_simp
  · rw [← mul_div_assoc,
      mul_div_cancel_left₀ wSq (Complex.ofReal_ne_zero.mpr hkappa)]

/-! # D. Topological and nontopological vortex data -/

/-- The BPS mass `2 pi v^2 n` of `n` topological vortices in the broken phase. -/
noncomputable def topologicalVortexMass (v : ℝ) (n : ℕ) : ℝ :=
  2 * pi * v ^ 2 * n

/-- The `2n` translational zero modes of `n` topological vortices. -/
def topologicalVortexZeroModes (n : ℕ) : ℕ := 2 * n

/-- The topological BPS mass is `pi v^2` times the number of translational zero modes. This combines
the two independent vortex counts reported after Eq. (47). -/
@[zil_level physical_theorem]
lemma topologicalVortexMass_eq_zeroModes (v : ℝ) (n : ℕ) :
    topologicalVortexMass v n = pi * v ^ 2 * topologicalVortexZeroModes n := by
  simp [topologicalVortexMass, topologicalVortexZeroModes]
  ring

/-- The continuous nontopological-vortex flux `2 pi (n + alpha)`, where the paper assumes
`alpha ≥ n + 2`. Unlike `higgsVortexFlux`, `alpha` is real, so this flux is not quantized. -/
noncomputable def nontopologicalVortexFlux (n : ℕ) (alpha : ℝ) : ℝ :=
  2 * pi * ((n : ℝ) + alpha)

/-- Under the integrated Maxwell--Chern--Simons Gauss law `Q = -kappa Phi`, the repository's
continuous topological flux `deserFlux Q kappa` is exactly the paper's nontopological flux. -/
lemma nontopologicalVortexFlux_eq_deserFlux
    (kappa charge alpha : ℝ) (n : ℕ) (hkappa : kappa ≠ 0)
    (hGauss : charge = -kappa * nontopologicalVortexFlux n alpha) :
    deserFlux charge kappa = nontopologicalVortexFlux n alpha := by
  rw [hGauss]
  unfold deserFlux
  field_simp

/-- **Lee's full nontopological flux/charge chain**
`Phi = -Q/kappa = 2 pi (n+alpha)`, proved by reusing `deserFlux` rather than defining a second
Maxwell--Chern--Simons flux convention. -/
@[zil_level bridge_theorem]
theorem nontopologicalVortexFlux_charge_chain
    (kappa charge alpha : ℝ) (n : ℕ) (hkappa : kappa ≠ 0)
    (hGauss : charge = -kappa * nontopologicalVortexFlux n alpha) :
    deserFlux charge kappa = nontopologicalVortexFlux n alpha ∧
      kappa * nontopologicalVortexFlux n alpha = -charge := by
  exact ⟨nontopologicalVortexFlux_eq_deserFlux kappa charge alpha n hkappa hGauss,
    by rw [hGauss]; ring⟩

/-- The paper's asymptotic condition `alpha ≥ n+2` forces positive nontopological flux in the
displayed orientation. -/
lemma nontopologicalVortexFlux_pos
    (alpha : ℝ) (n : ℕ) (halpha : (n : ℝ) + 2 ≤ alpha) :
    0 < nontopologicalVortexFlux n alpha := by
  unfold nontopologicalVortexFlux
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum : 0 < (n : ℝ) + alpha := by linarith
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hsum

/-- The paper's `alphaHat`: the greatest integer strictly below the continuous asymptotic parameter
`alpha`. Writing it as `ceil alpha - 1` handles integer and noninteger values uniformly. -/
noncomputable def leeAlphaHat (alpha : ℝ) : ℤ := ⌈alpha⌉ - 1

/-- `alphaHat` is strictly below `alpha`. -/
lemma leeAlphaHat_lt (alpha : ℝ) : (leeAlphaHat alpha : ℝ) < alpha := by
  unfold leeAlphaHat
  exact_mod_cast Int.le_ceil_iff.mp (le_refl ⌈alpha⌉)

/-- **Maximality of the paper's `alphaHat`.** An integer lies below `alphaHat` exactly when its
real cast is strictly below `alpha`; hence this is the actual greatest-integer-strictly-below
operation, not an externally supplied rounding certificate. -/
@[zil_level bridge_theorem]
lemma le_leeAlphaHat_iff (z : ℤ) (alpha : ℝ) :
    z ≤ leeAlphaHat alpha ↔ (z : ℝ) < alpha := by
  unfold leeAlphaHat
  rw [Int.le_sub_one_iff]
  exact Int.lt_ceil

/-- The paper's nontopological-vortex zero-mode count `2n + 2 alphaHat - 2`. It is integer-valued
because `alphaHat` is the greatest integer strictly below the continuous flux parameter. -/
noncomputable def nontopologicalVortexZeroModes (n : ℕ) (alpha : ℝ) : ℤ :=
  2 * (n : ℤ) + 2 * leeAlphaHat alpha - 2

/-- Under the paper's asymptotic condition `alpha ≥ n+2`, the nontopological solution has at least
`4n` zero modes. This includes the `2n` translational modes and the additional flux/phase moduli. -/
@[zil_level physical_theorem]
lemma nontopologicalVortexZeroModes_ge_four_mul
    (n : ℕ) (alpha : ℝ) (halpha : (n : ℝ) + 2 ≤ alpha) :
    (4 : ℤ) * n ≤ nontopologicalVortexZeroModes n alpha := by
  have hlt : (((n : ℤ) + 1 : ℤ) : ℝ) < alpha := by
    norm_num
    exact lt_of_lt_of_le
      (by linarith : (n : ℝ) + 1 < (n : ℝ) + 2) halpha
  have hhat : (n : ℤ) + 1 ≤ leeAlphaHat alpha :=
    (le_leeAlphaHat_iff _ _).mpr hlt
  unfold nontopologicalVortexZeroModes
  omega

/-! # E. Type-IIB mirror map -/

/-- The Chern--Simons coupling map `kappa' = -1/kappa` induced by the paper's type-IIB mirror
operation. Its physical domain excludes `kappa = 0`; as usual for a Lean field, inversion is
algebraically totalized there. -/
noncomputable def mirrorCoupling (kappa : ℝ) : ℝ := -kappa⁻¹

/-- The totalized algebraic mirror coupling map is an involution. The type-IIB interpretation uses
this identity only at nonzero coupling, where `-1/kappa` is physically defined. -/
@[zil_level physical_theorem]
lemma mirrorCoupling_involutive (kappa : ℝ) :
    mirrorCoupling (mirrorCoupling kappa) = kappa := by
  simp [mirrorCoupling]

/-- Type-IIB `S`-duality on the F1/D1 charge pair: `(qF,qD) -> (qD,-qF)`. -/
def mirrorStringCharge (charge : ℤ × ℤ) : ℤ × ℤ :=
  (charge.2, -charge.1)

/-- A primitive type-IIB string charge is a relatively-prime F1/D1 charge pair. -/
def IsPrimitiveStringCharge (charge : ℤ × ℤ) : Prop :=
  Int.gcd charge.1 charge.2 = 1

/-- **Mirror symmetry preserves primitive BPS charge sectors.** Thus the order-four charge orbit
does not leave the relatively-prime string spectrum used by the paper. -/
@[zil_level physical_theorem]
lemma mirrorStringCharge_primitive_iff (charge : ℤ × ℤ) :
    IsPrimitiveStringCharge (mirrorStringCharge charge) ↔
      IsPrimitiveStringCharge charge := by
  rcases charge with ⟨qF, qD⟩
  simp [IsPrimitiveStringCharge, mirrorStringCharge, Int.gcd, Nat.gcd_comm]

/-- Applying the charge map twice gives simultaneous charge conjugation. -/
lemma mirrorStringCharge_sq (charge : ℤ × ℤ) :
    mirrorStringCharge (mirrorStringCharge charge) = (-charge.1, -charge.2) := by
  simp [mirrorStringCharge]

/-- The type-IIB `S`-duality charge map has order four. -/
@[zil_level physical_theorem]
lemma mirrorStringCharge_four (charge : ℤ × ℤ) :
    mirrorStringCharge (mirrorStringCharge (mirrorStringCharge (mirrorStringCharge charge))) =
      charge := by
  rcases charge with ⟨qF, qD⟩
  simp [mirrorStringCharge]

/-! # F. Three-dimensional MCS vacua and the Lovelock tensor -/

/-- The metric-proportional source contributed by the `N = 3` scalar potential. Only its vanishing
on a vacuum is used below, so this definition is independent of the overall stress-tensor sign
convention and is not presented as the full Maxwell--Chern--Simons stress tensor. -/
noncomputable def nThreeMCSPotentialMetricSource {ι : Type*}
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (g : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq • g

/-- **The MCS metric source has exactly the full `N = 3` vacuum locus.** For a nonzero metric and
positive squared gauge coupling, `U g = 0` iff the D-flat and F-flat equations hold and either the
charged or neutral scalar factor vanishes. -/
@[zil_level bridge_theorem]
lemma nThreeMCSPotentialMetricSource_eq_zero_iff {ι : Type*}
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (g : Matrix ι ι ℝ) (hgauge : 0 < gaugeCouplingSq)
    (hg : g ≠ 0) :
    nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g = 0 ↔
      Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * X5 = 0 ∧
      q * qTilde + (kappa : ℂ) * phi - wSq = 0 ∧
      ((q = 0 ∧ qTilde = 0) ∨ (X3 = 0 ∧ phi = 0)) := by
  rw [nThreeMCSPotentialMetricSource, smul_eq_zero, or_iff_left hg]
  exact nThreeMCSPotential_eq_zero_iff
    gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq hgauge

/-- **The complete Lovelock-tensor classification in the MCS spacetime dimension.** In dimension
three the generalized Einstein/Lovelock tensor term of order `p` survives exactly for `p ≤ 1`;
every genuinely higher-curvature term `p ≥ 2`, beginning with Gauss--Bonnet, vanishes identically. -/
@[zil_level physical_theorem]
theorem leeMCS_dim3_lovelockTensor_classification (p : ℕ) :
    (0 < genKroneckerTrace 3 (2 * p + 1) ↔ p ≤ 1) ∧
      (genKroneckerTrace 3 (2 * p + 1) = 0 ↔ 2 ≤ p) := by
  constructor
  · rw [lovelockTensorTerm_pos_iff]
    omega
  · rw [lovelockTensorTerm_eq_zero_iff]
    omega

/-- **The three-dimensional trace of the MCS potential source is `3U`.** This is the actual matrix
contraction with the inverse metric, using `g⁻¹g = 1`, rather than a component-counting analogy. -/
@[zil_level bridge_theorem]
lemma metricTrace_nThreeMCSPotentialMetricSource
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (gInv g : Matrix (Fin 3) (Fin 3) ℝ)
    (hgInv : gInv * g = 1) :
    metricTrace gInv
      (nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g) =
      3 * nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq := by
  simp [metricTrace, nThreeMCSPotentialMetricSource,
    Matrix.trace_smul, hgInv, Matrix.trace_one]
  ring

/-- **The full potential-sourced order-one Lovelock equation in three dimensions.** This directly
instantiates the repository's pure-Lovelock affine tensor theorem with the MCS potential metric
source; unlike the vacuum corollary below, it retains a nonzero scalar potential. -/
@[zil_level bridge_theorem]
theorem leeMCS_dim3_lovelockFieldEquation
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (RicM gInv g : Matrix (Fin 3) (Fin 3) ℝ)
    (L gravCoupling firstConstant : ℝ)
    (hgInv : gInv * g = 1)
    (htraceRic : metricTrace gInv RicM = L)
    (hfirst : lovelockAffineTensor 1 RicM gInv g
      (nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g)
      gravCoupling = firstConstant • g) :
    RicM - (L / 2) • g + lovelockEddingtonLambda (ι := Fin 3) 1 firstConstant • g =
      gravCoupling •
        nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g := by
  exact lovelockFirstIntegral_derives_fieldEquation
    (ι := Fin 3) 1 one_ne_zero RicM gInv g
    (nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g)
    L gravCoupling firstConstant (by norm_num) hgInv (by simpa using htraceRic) hfirst

/-- The Lovelock cosmological coefficient after absorbing the metric-proportional MCS potential
source into the left-hand side of the field equation. -/
noncomputable def leeMCSLovelockEffectiveLambda
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (gravCoupling firstConstant : ℝ) : ℝ :=
  lovelockEddingtonLambda (ι := Fin 3) 1 firstConstant -
    gravCoupling * nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq

/-- **MCS potential energy is exactly an effective Lovelock cosmological term.** The nonzero
potential source equation is equivalent, by matrix algebra, to a source-free equation with
`Λ_eff = Λ_affine - κ_grav U`. -/
@[zil_level physical_theorem]
theorem leeMCS_dim3_lovelockFieldEquation_effectiveLambda
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (RicM gInv g : Matrix (Fin 3) (Fin 3) ℝ)
    (L gravCoupling firstConstant : ℝ)
    (hgInv : gInv * g = 1)
    (htraceRic : metricTrace gInv RicM = L)
    (hfirst : lovelockAffineTensor 1 RicM gInv g
      (nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g)
      gravCoupling = firstConstant • g) :
    RicM - (L / 2) • g +
      leeMCSLovelockEffectiveLambda gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq
        gravCoupling firstConstant • g = 0 := by
  have hfield := leeMCS_dim3_lovelockFieldEquation
    gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq RicM gInv g
    L gravCoupling firstConstant hgInv htraceRic hfirst
  ext i j
  have hij := congrFun (congrFun hfield i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply] at hij ⊢
  unfold leeMCSLovelockEffectiveLambda
  unfold nThreeMCSPotentialMetricSource at hij
  simp only [Matrix.smul_apply, smul_eq_mul] at hij ⊢
  linear_combination hij

/-- The trace of the surviving order-one Lovelock--Einstein tensor in three dimensions is
`-R/2`, the specialization of Dadhich's general trace formula `R(2m-D)/2`. -/
@[zil_level bridge_theorem]
theorem leeMCS_dim3_lovelockEinsteinTrace (R : ℝ) :
    lovelockEinsteinTrace 3 1 R = -(R / 2) := by
  rw [lovelockEinsteinTrace_eq]
  ring

/-- **The zero-potential MCS vacuum sources the order-one Lovelock equation trivially.** In the
paper's three-dimensional spacetime, instantiate the existing pure-Lovelock affine tensor at its
only dynamical curvature order `m = 1`. If the classified D/F-flat vacuum equations hold, the
potential source vanishes and the affine first integral yields the source-free Lovelock equation.

The affine first integral, inverse-metric identity, and curvature trace are explicit hypotheses;
this theorem does not derive them from the MCS action. -/
@[zil_level bridge_theorem]
theorem leeMCS_dim3_zeroVacuum_lovelockFieldEquation
    (gaugeCouplingSq : ℝ) (q qTilde : ℂ) (v kappa X5 X3 : ℝ)
    (phi wSq : ℂ) (RicM gInv g : Matrix (Fin 3) (Fin 3) ℝ)
    (L gravCoupling firstConstant : ℝ)
    (hgauge : 0 < gaugeCouplingSq)
    (hgInv : gInv * g = 1)
    (htraceRic : metricTrace gInv RicM = L)
    (hD : Complex.normSq q - Complex.normSq qTilde - v ^ 2 + kappa * X5 = 0)
    (hF : q * qTilde + (kappa : ℂ) * phi - wSq = 0)
    (hbranch : (q = 0 ∧ qTilde = 0) ∨ (X3 = 0 ∧ phi = 0))
    (hfirst : lovelockAffineTensor 1 RicM gInv g
      (nThreeMCSPotentialMetricSource gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq g)
      gravCoupling = firstConstant • g) :
    RicM - (L / 2) • g + lovelockEddingtonLambda (ι := Fin 3) 1 firstConstant • g = 0 := by
  have hU : nThreeMCSPotential gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq = 0 :=
    (nThreeMCSPotential_eq_zero_iff
      gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq hgauge).mpr ⟨hD, hF, hbranch⟩
  have hfield := leeMCS_dim3_lovelockFieldEquation
    gaugeCouplingSq q qTilde v kappa X5 X3 phi wSq RicM gInv g
    L gravCoupling firstConstant hgInv htraceRic hfirst
  simpa [nThreeMCSPotentialMetricSource, hU] using hfield

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons

zil attach iibDStringTension_axion_eq_neg_coupling where
  formalizes @ "claim:type-iib-d-string-tension-is-axion-dressed-by-the-mcs-coupling",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equation-33",
  caveat @ "claim:string-brane-identification-is-paper-input-not-a-supergravity-solution"

zil attach iibDStringTension_minimal_at_zero where
  formalizes @ "claim:the-mcs-axion-dressing-cannot-lower-the-type-iib-d-string-tension",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equation-33",
  caveat @ "claim:derived-tension-inequality-not-a-vortex-stability-or-supergravity-backreaction-theorem"

zil attach vectorMultipletMass_eq_djtTopologicalMass where
  formalizes @ "claim:lee-mcs-vector-mass-is-the-existing-djt-level-mass",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equation-43",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT.topologicalMass"

zil attach pureChernSimons_decoupling_limit where
  formalizes @ "claim:fixed-nonzero-cs-coupling-and-infinite-gauge-coupling-decouple-the-maxwell-term",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iv",
  caveat @ "claim:proved-as-coefficient-and-mass-limits-not-operator-effective-action-convergence"

zil attach compactification_vectorMass_tendsto_atTop where
  formalizes @ "claim:shrinking-the-type-iib-compactification-interval-realizes-the-pure-cs-infinite-vector-mass-limit",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iv",
  caveat @ "claim:coefficient-level-compactification-limit-not-a-dimensional-reduction-or-effective-action-convergence-theorem"

zil attach mcsPotential_eq_zero_iff where
  formalizes @ "claim:n-two-mcs-potential-zero-locus-splits-into-higgs-and-symmetric-branches",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equations-45-47",
  caveat @ "claim:algebraic-potential-classification-not-a-global-vortex-pde-existence-theorem"

zil attach nThreeMCSPotential_brokenVacuum where
  formalizes @ "claim:n-three-mcs-potential-has-the-displayed-d-flat-and-f-flat-broken-vacuum",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equations-48-49",
  caveat @ "claim:exact-zero-of-the-supplied-potential-not-a-construction-of-the-bps-vortex-solution"

zil attach nThreeMCSPotential_eq_zero_iff where
  formalizes @ "claim:n-three-mcs-potential-zero-locus-is-exactly-d-flat-f-flat-with-charged-or-neutral-branch-vanishing",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equations-48-50",
  caveat @ "claim:complete-algebraic-zero-locus-not-a-global-vortex-pde-or-moduli-space-classification"

zil attach nThreeMCSPotential_unbrokenVacuum where
  formalizes @ "claim:n-three-mcs-potential-has-the-explicit-symmetric-vacuum-at-v-squared-and-w-squared-over-kappa",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equations-48-50",
  caveat @ "claim:vacuum-algebra-not-a-proof-of-n-three-moduli-space-completeness"

zil attach topologicalVortexMass_eq_zeroModes where
  formalizes @ "claim:topological-mcs-vortex-bps-mass-is-pi-v-squared-times-its-translational-zero-mode-count",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iii-b-1",
  caveat @ "claim:bps-mass-and-zero-mode-formulas-are-paper-inputs-not-derived-from-moduli-space-index-theory"

zil attach nontopologicalVortexFlux_charge_chain where
  formalizes @ "claim:nontopological-mcs-vortex-flux-equals-minus-charge-over-kappa-and-two-pi-n-plus-alpha",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iii-b-2",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux.deserFlux",
  caveat @ "claim:conditional-on-the-integrated-gauss-law-and-supplied-asymptotic-alpha"

zil attach nontopologicalVortexZeroModes_ge_four_mul where
  formalizes @ "claim:lee-alpha-hat-gives-at-least-four-n-nontopological-vortex-zero-modes",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iii-b-2",
  caveat @ "claim:zero-mode-count-formula-is-paper-input-while-lean-proves-the-rounding-and-bound"

zil attach mirrorCoupling_involutive where
  formalizes @ "claim:type-iib-mirror-map-sends-kappa-to-minus-one-over-kappa-involutively",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iv",
  caveat @ "claim:coupling-map-algebra-with-lean-totalized-zero-not-a-construction-of-the-full-quantum-mirror-equivalence"

zil attach mirrorStringCharge_four where
  formalizes @ "claim:type-iib-s-duality-charge-map-qf-qd-to-qd-minus-qf-has-order-four",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iv",
  caveat @ "claim:charge-lattice-action-not-a-proof-of-brane-creation-or-soliton-spectrum-equivalence"

zil attach mirrorStringCharge_primitive_iff where
  formalizes @ "claim:type-iib-mirror-map-preserves-relatively-prime-f1-d1-charge-sectors",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-section-iv",
  caveat @ "claim:arithmetic-charge-sector-invariance-not-a-proof-of-bps-state-existence-or-dual-spectrum-completeness"

zil attach nThreeMCSPotentialMetricSource_eq_zero_iff where
  formalizes @ "claim:the-metric-proportional-n-three-mcs-potential-source-vanishes-exactly-on-the-complete-vacuum-locus",
  supported_by @ "paper:lee-lee-ohta-yang-1999-prd60-106003-equations-48-50",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons.nThreeMCSPotential_eq_zero_iff",
  caveat @ "claim:potential-only-metric-source-not-the-complete-maxwell-chern-simons-stress-tensor"

zil attach leeMCS_dim3_lovelockTensor_classification where
  formalizes @ "claim:three-dimensional-mcs-gravity-retains-only-cosmological-and-einstein-lovelock-tensor-orders",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination.lovelockTensorTerm_pos_iff",
  caveat @ "claim:dimension-and-antisymmetry-classification-not-a-derivation-of-a-brane-induced-gravity-action"

zil attach leeMCS_dim3_zeroVacuum_lovelockFieldEquation where
  formalizes @ "claim:a-classified-zero-potential-mcs-vacuum-reduces-the-three-dimensional-order-one-lovelock-first-integral-to-the-source-free-field-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.lovelockFirstIntegral_derives_fieldEquation",
  requires @ "claim:the-pure-lovelock-affine-first-integral-inverse-metric-identity-and-curvature-trace-are-supplied",
  caveat @ "claim:conditional-affine-tensor-instantiation-not-a-variation-of-the-full-coupled-mcs-gravity-action"

zil attach metricTrace_nThreeMCSPotentialMetricSource where
  formalizes @ "claim:the-three-dimensional-metric-trace-of-the-mcs-potential-source-is-three-times-the-potential",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.metricTrace",
  requires @ "claim:the-supplied-inverse-metric-multiplies-the-metric-to-the-identity",
  caveat @ "claim:trace-of-the-potential-only-source-not-the-trace-of-the-complete-mcs-stress-tensor"

zil attach leeMCS_dim3_lovelockFieldEquation where
  formalizes @ "claim:the-three-dimensional-order-one-lovelock-affine-equation-carries-the-n-three-mcs-potential-as-an-explicit-metric-source",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.lovelockFirstIntegral_derives_fieldEquation",
  requires @ "claim:the-pure-lovelock-affine-first-integral-inverse-metric-identity-and-curvature-trace-are-supplied",
  caveat @ "claim:potential-sector-source-only-not-a-derived-complete-coupled-mcs-gravity-euler-lagrange-system"

zil attach leeMCS_dim3_lovelockFieldEquation_effectiveLambda where
  supported_by @ "lean:leeMCS_dim3_lovelockFieldEquation",
  formalizes @ "claim:the-metric-proportional-mcs-potential-shifts-the-order-one-lovelock-cosmological-coefficient-by-minus-kappa-grav-times-u",
  requires @ "claim:the-potential-sourced-lovelock-affine-field-equation-premises-are-supplied",
  caveat @ "claim:exact-equation-rearrangement-not-a-prediction-or-calibration-of-the-observed-cosmological-constant"

zil attach leeMCS_dim3_lovelockEinsteinTrace where
  formalizes @ "claim:the-surviving-three-dimensional-order-one-lovelock-einstein-tensor-has-trace-minus-r-over-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential.lovelockEinsteinTrace_eq",
  caveat @ "claim:tensor-trace-specialization-not-a-standalone-curvature-solution"

zil_file_contract physlib.maxwellChernSimonsIIBSolitons where
  promises "The equation-level type-IIB/MCS soliton bridge: axion-dressed string tension and its lower bound, DJT vector mass, compactification realization of the pure-CS limit, complete N=2 and N=3 algebraic vacuum structure, topological and nontopological vortex data, primitive-sector-preserving mirror maps, and the honest three-dimensional connection from the potential metric source to the surviving order-one Lovelock tensor, including its trace and exact effective-cosmological-term rewrite."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge.MaxwellChernSimonsFlatPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.TopologicalMassAbelianHiggsFlux.deserFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT.topologicalMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination.lovelockTensorTerm_pos_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockBianchiPotential.lovelockEinsteinTrace",
    "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.lovelockAffineTensor"
  ]
  forbids_substitutes [
    "claiming a constructed type-IIB supergravity brane background from the imported field-theory equations",
    "claiming the finite-energy BPS domain-wall construction that Lee et al. explicitly leave open",
    "extending the paper-specific Abelian vortex results to non-Abelian solitons by relabeling",
    "claiming global vortex PDE existence or moduli-space completeness from the algebraic BPS data",
    "treating the pure-CS coefficient limits as norm-resolvent or effective-action convergence",
    "identifying the scalar-potential metric source with the complete Maxwell-Chern-Simons stress tensor",
    "claiming the conditional Lovelock first-integral instantiation derives a coupled brane-gravity action"
  ]
  witnessed_by [
    iibStringTension_nonneg,
    iibFStringTension,
    iibDStringTension_axion_eq_neg_coupling,
    iibDStringTension_minimal_at_zero,
    vectorMultipletMass_eq_djtTopologicalMass,
    pureChernSimons_decoupling_limit,
    compactification_vectorMass_tendsto_atTop,
    mcsPotential_nonneg,
    mcsPotential_eq_zero_iff,
    mcsPotential_brokenVacuum,
    mcsPotential_unbrokenVacuum,
    nThreeMCSPotential_nonneg,
    nThreeMCSPotential_eq_zero_iff,
    nThreeMCSPotential_brokenVacuum,
    nThreeMCSPotential_unbrokenVacuum,
    topologicalVortexMass_eq_zeroModes,
    nontopologicalVortexFlux_charge_chain,
    nontopologicalVortexFlux_pos,
    leeAlphaHat_lt,
    le_leeAlphaHat_iff,
    nontopologicalVortexZeroModes_ge_four_mul,
    mirrorCoupling_involutive,
    mirrorStringCharge_primitive_iff,
    mirrorStringCharge_four,
    nThreeMCSPotentialMetricSource_eq_zero_iff,
    leeMCS_dim3_lovelockTensor_classification,
    metricTrace_nThreeMCSPotentialMetricSource,
    leeMCS_dim3_lovelockFieldEquation,
    leeMCS_dim3_lovelockFieldEquation_effectiveLambda,
    leeMCS_dim3_lovelockEinsteinTrace,
    leeMCS_dim3_zeroVacuum_lovelockFieldEquation
  ]

/- ZIL-END -/
