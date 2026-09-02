/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.SpaceAndTime.Space.Integrals.Basic
meta import Zil

/-!
# The D3-brane holographic spectrum (GKP hep-th/9802109, completed)

Completes the Gubser–Klebanov–Polyakov analysis (Phys. Lett. B428 (1998) 105,
hep-th/9802109) by adding the pieces that the AdS/CFT + holographic +
dimensional-reduction core makes tractable, on top of
`MassiveStringAnomalousDimensions` (from which the operator dimension and the
`(mR)² = 4n g√(2N)` barrier are leveraged):

* **§A — the `S⁵` Kaluza–Klein reduction (dimensional reduction).**  A massless
  `10`-dimensional scalar on `AdS₅ × S⁵` reduces to a tower of `AdS₅` scalars whose
  effective mass² is the round-`S⁵` scalar-Laplacian eigenvalue `ℓ(ℓ+4)`
  (`sphereS5Eigenvalue`); the `ℓ`-th Kaluza–Klein mode is dual to a boundary
  operator of dimension `4 + ℓ` (`kaluzaKlein_dimension`, via the leveraged
  `partialWave_dimension`).  The `10 = 5 + 5` split (`ads_sphere_dimension_split`)
  is the holographic dimensional reduction that produces the whole partial-wave
  tower (GKP Eqs. PartEOM/GotFlux).  The genuine Haar-induced surface measure on
  the unit `S⁵ ⊂ ℝ⁶` is proved to be `π³` (`unitS5_surfaceVolume`), hence the
  round radius-`R` volume is `π³R⁵` (`roundS5Volume_eq`).

* **§B — the 't Hooft coupling and the `λ^{1/4}` growth.**  With
  `λ = g²_{YM} N` (`tHooftCoupling`) the AdS radius is `R⁴ = 2λ(α')²`
  (`adsRadius_fourth_tHooft`), so the level-`n` barrier is `(mR)² = 4n√(2λ)`
  (`massRadiusSq_lambda`) and the leading anomalous dimension satisfies
  `(mR)⁴ = 32 n² λ` (`massRadius_fourth_lambda`): the dimensions of operators dual
  to massive string states grow as `λ^{1/4}` at strong coupling — the iconic
  strong-coupling scaling of large-`N` gauge theory (GKP Eq. anomform).

* **§B.1–§C — Newton compactification and the central charge.**  The D3 string
  inputs and the proved `S⁵_R` volume give `G₅=πR³/(2N²)`
  (`d3_newton_from_string_compactification`).  Consequently the bulk coefficient
  `πR³/(8G₅)` equals the boundary central charge `N²/4`
  (`d3_bulkCentralCharge_eq_boundary`).  With an explicit dimensional-reduction
  factor `G₅=V G₄`, this is linked—without identifying `G₄` and `G₅`—to the
  recent Compton-cell result `G₄=ℏcσ₀⁴`
  (`comptonCell_d3_compactification_dictionary`).  Independently, the
  stress-tensor two-point function (GKP Eq. TwoTT)
  fixes the conformal anomaly `c = N²/4` (`centralChargeN4`), positive and growing
  as `N²` (`centralChargeN4_pos`) — the `AdS₅` analogue of the Brown–Henneaux
  `c = 3R/2G` of `RyuTakayanagiFormulaAlgebra`, both the boundary-CFT normalization
  read off the bulk on-shell action.

* **§D — Maldacena's rectangular Wilson loop.**  The regularized fundamental-string
  worldsheet gives the strong-coupling quark–antiquark potential
  `E(L) = -4π²√(2λ)/(Γ(1/4)⁴L)` (`maldacenaQuarkPotential`).  Its leading
  rectangular-loop weight is the already-formalized Euclidean/Kuiken exponential
  `e^{-TE}` (`maldacenaRectangularWilsonWeight`), and taking
  `-log(W)/T` recovers the potential exactly
  (`maldacena_rectangularLoop_extracts_potential`).

* **§E — the two characteristic scalings of the Wilson result.**  The coefficient
  scales as `√λ` (`maldacenaWilsonCoefficient_coupling_scale`) while the potential
  scales as `L⁻¹` (`maldacenaQuarkPotential_separation_scale`), the conformal
  covariance emphasized immediately after Eq. (12).  In particular, doubling the
  separation halves the interaction energy, and the result cannot be a
  constant-tension confining potential (`maldacenaQuarkPotential_not_linear`).

* **§F — assembled AdS/CFT Wilson-loop dictionary.**  The worldsheet exponential is
  also the modulus of the repo's master complex-action weight
  (`maldacena_worldsheet_is_master_modulus`), and
  `maldacenaWilsonLoop_dictionary` collects positivity of the coefficient,
  attraction of the potential, energy extraction, conformal scaling, and the
  worldsheet/master-weight identification.

* **§G — Hawking–Page circle-exchange saddles.**  The two Euclidean saddles of
  Maldacena's compactified confining example exchange the thermal circle
  `β` and spatial circle `L=2πr_y`.  Their normalized actions
  `I_conf=C L/β` and `I_deconf=C β/L` cross at `β=L`, have distinct slopes
  there, and reverse dominance on the two sides
  (`hawkingPage_circleExchange_phaseStructure`).  Because the Euclidean
  weight is `e^{-I}`, lower action is proved to mean higher saddle weight.

* **§H — the thermal `3/4` factor.**  The AdS₅ black-brane entropy density
  `s_strong=(π²/2)N²T³` is exactly three quarters of the free `N=4` SYM
  density `s_free=(2π²/3)N²T³`
  (`strongCouplingEntropyDensity_eq_threeFourths_free`), while both carry the
  conformal `N²T³` scaling.

* **§I — large-`N` factorization.**  The factorization defect `c₂/N²` and
  normalized connected three-point ratio `c₃/N` both converge to zero
  (`largeN_correlatorSuppressions_tendsto_zero`), formalizing the asymptotic
  suppression in Maldacena lecture Eqs. 2.12–2.13.

* **§J — KSS shear-viscosity saturation.**  The black-brane shear viscosity
  `η=(π/8)N²T³` and the existing entropy density
  `s=(π²/2)N²T³` give `η/s=1/(4π)`
  (`d3_kssRatio_saturates_twoDerivativeGravity`).  This is the exact
  two-derivative gravity-dual saturation result, not a proof of the conjectured
  universal lower bound in arbitrary quantum systems.  The more primitive
  horizon route keeps the analytic premise `σ_abs(0)=a` explicit and combines
  `η=σ_abs(0)/(16πG)` with `s=a/(4G)`
  (`kssRatio_from_lowFrequencyHorizonAbsorption`).

* **§K — lightlike Wilson loops and jet quenching.**  The strong-coupling
  coefficient
  `q̂=π^(3/2) Γ(3/4)/Γ(5/4) √λ T³`
  (`strongCouplingJetQuenching`) is positive and has the paper's exact
  `√λ` and `T³` homogeneities.  Its adjoint lightlike Wilson-loop exponent
  `exp(-q̂ L⁻L²/(4√2))` is identified with the modulus of the repo's master
  complex-action weight (`jetQuenching_lightlikeWilson_scaling_chain`).
  In the physical positive-parameter regime the coefficient is strictly
  positive and the Wilson factor lies strictly between zero and one
  (`jetQuenching_lightlikeWilson_strictSuppression`).

Honest layering: the `S⁵` scalar harmonic analysis, the Bessel-function flux factor, the
minimal-surface Euler–Lagrange solution, its beta-function integral, and the
subtraction of the infinite probe-quark mass are the papers' analytic content.
The unit-`S⁵` volume is proved from Mathlib's Haar-to-sphere and Euclidean-ball
measure.  The string coupling/radius relations and dimensional-reduction equation
are explicit premises of the D3 compactification theorem.  The eigenvalue,
dimension, coupling, central-charge, Wilson-loop extraction, and
scaling *identities* are formalized here on the existing dictionary and
`ComplexActionPathIntegralWeight`.  In §D–§F the closed form of Maldacena's
regularized result (PRL Eq. (12)) is the input; no claim is made that the
minimal-surface PDE or renormalization has been derived in Lean.  Reusing
`kuikenWeight` is only reuse of the generic real exponential `exp(-S)`: because
the mass-subtracted interaction energy is negative, the regularized leading
Wilson factor is greater than one, not an entropic suppression.

## References

* S. S. Gubser, I. R. Klebanov, A. M. Polyakov, Phys. Lett. B428 (1998) 105,
  hep-th/9802109, §2–§3.
* J. Maldacena, *Wilson Loops in Large N Field Theories*, Phys. Rev. Lett. 80
  (1998) 4859, hep-th/9803002, especially Eqs. (2), (5)–(12).  Local source
  inspected: `Wilson Loops in Large N Field Theoriesmaldacena1998.pdf`.
* J. Maldacena, *TASI 2003 Lectures on AdS/CFT*, hep-th/0309246v5, §6.1:
  the circle-exchange confinement/deconfinement saddle crossing at
  `β_c=2πr_y`.
* Repo modules used: `AdSCFT.MassiveStringAnomalousDimensions`
  (`conformalDimension`, `partialWave_dimension`, `massRadiusSq_tHooft`),
  `AdSCFT.RyuTakayanagiFormulaAlgebra` (`brownHenneaux`), and
  `PathIntegral.ComplexActionPathIntegralWeight` (`kuikenWeight`,
  `master_modulus_is_kuiken`).
* S. Ryu and T. Takayanagi, hep-th/0603001v2, for
  `G₁₀ = π³R⁵G₅`; local source inspected:
  `Ryu–Takayanagi-0603001v2.pdf`.
* P. Kovtun, D. T. Son, and A. O. Starinets, *Viscosity in Strongly
  Interacting Quantum Field Theories from Black Hole Physics*,
  hep-th/0405231, especially Eqs. (5), (10), and (11).
* H. Liu, K. Rajagopal, and U. A. Wiedemann, *Calculating the Jet Quenching
  Parameter from AdS/CFT*, hep-ph/0605178, especially Eqs. (2), (3), and
  (11).  The exact coefficient is the `N=4` SYM result, not a universal QCD
  value.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.Thermodynamics
open MeasureTheory

/-! ## §A — the `S⁵` Kaluza–Klein dimensional reduction -/

/-- **The round-`S⁵` scalar-Laplacian eigenvalue** `ℓ(ℓ+4)` (the `S^m` spectrum
`ℓ(ℓ+m−1)` at `m = 5`) — the effective mass² of the `ℓ`-th Kaluza–Klein mode of a
massless `10`d scalar reduced on `S⁵`. -/
noncomputable def sphereS5Eigenvalue (ℓ : ℝ) : ℝ := ℓ * (ℓ + 4)

/-- **[The `10 = 5 + 5` holographic dimensional reduction]** `AdS₅ × S⁵` splits the
ten dimensions into the `AdS₅` bulk and the internal `S⁵` whose harmonics label the
Kaluza–Klein tower. -/
@[zil_level bridge_theorem]
theorem ads_sphere_dimension_split : (5 : ℕ) + 5 = 10 := rfl

/-- **[The Kaluza–Klein mode dimension] `Δ = 4 + ℓ`.**  The `ℓ`-th `S⁵` harmonic gives
an `AdS₅` scalar of mass² `R²` equal to the `S⁵` eigenvalue `ℓ(ℓ+4)`, dual to a
boundary operator of dimension `4 + ℓ` — the whole partial-wave tower from the one
`10`d field.  (Leverages `partialWave_dimension`.) -/
theorem kaluzaKlein_dimension (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    conformalDimension 4 (sphereS5Eigenvalue ℓ) = 4 + ℓ :=
  partialWave_dimension ℓ hℓ

/-- **[The zero mode is the dimension-`4` operator]** the `ℓ = 0` Kaluza–Klein mode
(the `S⁵` `s`-wave) is dual to the protected dimension-`4` operator `tr F²`. -/
@[zil_level bridge_theorem]
theorem kaluzaKlein_zeroMode : conformalDimension 4 (sphereS5Eigenvalue 0) = 4 := by
  rw [show sphereS5Eigenvalue 0 = 0 from by unfold sphereS5Eigenvalue; ring]
  exact massless_dimension

/-! ### §A.1 — the actual round-`S⁵` compactification volume -/

/-- **The unit five-sphere has surface volume `π³`.**  This is the genuine
Haar-to-sphere measure on the unit sphere in `ℝ⁶`, reduced to the already
formalized six-ball volume.  It is the geometric coefficient in the
`G₁₀ = Vol(S⁵_R) G₅` compactification relation. -/
@[zil_level bridge_theorem]
theorem unitS5_surfaceVolume :
    (volume : Measure (Space 6)).toSphere.real Set.univ = Real.pi ^ 3 := by
  rw [Measure.toSphere_real_apply_univ]
  have hball :
      volume (Metric.ball (0 : Space 6) 1) =
        ENNReal.ofReal (Real.pi ^ 3 / 6) := by
    rw [InnerProductSpace.volume_ball_of_dim_even (k := 3)
      (by norm_num [Space.finrank_eq_dim])]
    norm_num [Space.finrank_eq_dim]
  rw [measureReal_def, hball, ENNReal.toReal_ofReal]
  · norm_num [Space.finrank_eq_dim]
    ring
  · positivity

/-- The surface volume of the round radius-`R` five-sphere, expressed by
scaling the genuine unit-sphere measure by `R⁵`. -/
noncomputable def roundS5Volume (R : ℝ) : ℝ :=
  (volume : Measure (Space 6)).toSphere.real Set.univ * R ^ 5

/-- **The round `S⁵_R` volume is `π³R⁵`.** -/
@[zil_level bridge_theorem]
theorem roundS5Volume_eq (R : ℝ) :
    roundS5Volume R = Real.pi ^ 3 * R ^ 5 := by
  rw [roundS5Volume, unitS5_surfaceVolume]

/-! ## §B — the 't Hooft coupling and the `λ^{1/4}` anomalous dimension -/

/-- **The 't Hooft coupling** `λ = g²_{YM} N`. -/
noncomputable def tHooftCoupling (g N : ℝ) : ℝ := g ^ 2 * N

/-- **[The AdS radius in 't Hooft units] `R⁴ = 2λ(α')²`.**  The paper's
`R⁴ = 2N g²(α')²` written through the 't Hooft coupling. -/
theorem adsRadius_fourth_tHooft (R g N α : ℝ) (hR4 : R ^ 4 = 2 * N * g ^ 2 * α ^ 2) :
    R ^ 4 = 2 * tHooftCoupling g N * α ^ 2 := by
  rw [hR4]; unfold tHooftCoupling; ring

/-- **[The barrier in 't Hooft units] `(mR)² = 4n√(2λ)`.**  From `(mR)² = 4n g√(2N)`
and `g√(2N) = √(2g²N) = √(2λ)` (for `g ≥ 0`). -/
theorem massRadiusSq_lambda (m R n g N : ℝ) (hg : 0 ≤ g)
    (hbarrier : (m * R) ^ 2 = 4 * n * g * Real.sqrt (2 * N)) :
    (m * R) ^ 2 = 4 * n * Real.sqrt (2 * tHooftCoupling g N) := by
  rw [hbarrier]
  unfold tHooftCoupling
  have hsqrt : Real.sqrt (2 * (g ^ 2 * N)) = g * Real.sqrt (2 * N) := by
    rw [show (2 : ℝ) * (g ^ 2 * N) = g ^ 2 * (2 * N) from by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hg]
  rw [hsqrt]; ring

/-- **[The `λ^{1/4}` growth] `(mR)⁴ = 32 n² λ`.**  Squaring the barrier: the leading
anomalous dimension `h_n ≈ mR` of an operator dual to a level-`n` massive string
state grows as `λ^{1/4}` (times `√n`) at large 't Hooft coupling — the strong-coupling
scaling of the `N = 4` gauge-theory spectrum. -/
theorem massRadius_fourth_lambda (m R n g N : ℝ) (hN : 0 ≤ N)
    (hbarrier : (m * R) ^ 2 = 4 * n * g * Real.sqrt (2 * N)) :
    (m * R) ^ 4 = 32 * n ^ 2 * tHooftCoupling g N := by
  have hsN : Real.sqrt (2 * N) ^ 2 = 2 * N :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hN)
  unfold tHooftCoupling
  have h4 : (m * R) ^ 4 = ((m * R) ^ 2) ^ 2 := by ring
  rw [h4, hbarrier, mul_pow, hsN]
  ring

/-! ### §B.1 — ten-to-five dimensional Newton compactification -/

/-- **[D3 compactification determines the five-dimensional Newton constant].**
The D3 radius relation `R⁴ = 4π g_s N (α')²`, the ten-dimensional coupling
`G₁₀ = 8π⁶ g_s² (α')⁴`, and the *geometrically proved* compactification volume
`G₁₀ = Vol(S⁵_R) G₅` imply

`G₅ = π R³ / (2N²)`.

The three displayed relations are explicit string-theory inputs.  The conclusion
is their nontrivial compactification consequence; in particular, the `π³R⁵`
coefficient is supplied by `roundS5Volume_eq`, not postulated a second time. -/
@[zil_level bridge_theorem]
theorem d3_newton_from_string_compactification
    (R g_s N α G10 G5 : ℝ) (hR : R ≠ 0) (hN : N ≠ 0)
    (hR4 : R ^ 4 = 4 * Real.pi * g_s * N * α ^ 2)
    (hG10 : G10 = 8 * Real.pi ^ 6 * g_s ^ 2 * α ^ 4)
    (hreduce : G10 = roundS5Volume R * G5) :
    G5 = Real.pi * R ^ 3 / (2 * N ^ 2) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hR8 :
      R ^ 8 = 16 * Real.pi ^ 2 * g_s ^ 2 * N ^ 2 * α ^ 4 := by
    calc
      R ^ 8 = (R ^ 4) ^ 2 := by ring
      _ = (4 * Real.pi * g_s * N * α ^ 2) ^ 2 := by rw [hR4]
      _ = 16 * Real.pi ^ 2 * g_s ^ 2 * N ^ 2 * α ^ 4 := by ring
  rw [hG10, roundS5Volume_eq] at hreduce
  have hreduce' : 8 * Real.pi ^ 3 * g_s ^ 2 * α ^ 4 = R ^ 5 * G5 := by
    apply (mul_left_cancel₀ (pow_ne_zero 3 hπ))
    calc
      Real.pi ^ 3 * (8 * Real.pi ^ 3 * g_s ^ 2 * α ^ 4) =
          8 * Real.pi ^ 6 * g_s ^ 2 * α ^ 4 := by ring
      _ = Real.pi ^ 3 * R ^ 5 * G5 := hreduce
      _ = Real.pi ^ 3 * (R ^ 5 * G5) := by ring
  have hscaled :
      Real.pi * R ^ 8 = 2 * N ^ 2 * R ^ 5 * G5 := by
    calc
      Real.pi * R ^ 8 =
          Real.pi * (16 * Real.pi ^ 2 * g_s ^ 2 * N ^ 2 * α ^ 4) := by rw [hR8]
      _ = 2 * N ^ 2 * (8 * Real.pi ^ 3 * g_s ^ 2 * α ^ 4) := by ring
      _ = 2 * N ^ 2 * (R ^ 5 * G5) := by rw [hreduce']
      _ = 2 * N ^ 2 * R ^ 5 * G5 := by ring
  have hcore : 2 * N ^ 2 * G5 = Real.pi * R ^ 3 := by
    apply (mul_left_cancel₀ (pow_ne_zero 5 hR))
    calc
      R ^ 5 * (2 * N ^ 2 * G5) = 2 * N ^ 2 * R ^ 5 * G5 := by ring
      _ = Real.pi * R ^ 8 := hscaled.symm
      _ = R ^ 5 * (Real.pi * R ^ 3) := by ring
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hN))).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcore

/-! ## §C — the central charge -/

/-- **The `N = 4` central charge** `c = N²/4` (GKP Eq. TwoTT) — the conformal anomaly
read off the stress-tensor two-point function in the large-`N` limit. -/
noncomputable def centralChargeN4 (N : ℝ) : ℝ := N ^ 2 / 4

/-- The five-dimensional bulk expression for the boundary central charge in
the conventions fixed by the D3 compactification dictionary. -/
noncomputable def bulkCentralCharge5 (R G5 : ℝ) : ℝ :=
  Real.pi * R ^ 3 / (8 * G5)

/-- **[The central charge is positive and grows as `N²`]** `0 < c` for `N ≠ 0`. -/
theorem centralChargeN4_pos (N : ℝ) (hN : N ≠ 0) : 0 < centralChargeN4 N := by
  unfold centralChargeN4; positivity

/-- **[The central charge in the two-point normalization]** the stress-tensor
two-point coefficient `N²/(16π²)` (GKP Eq. TwoPtO prefactor) is `4c/(16π²) = c/(4π²)`
with `c = N²/4`: the anomaly and the two-point normalization have the same `N²` factor. -/
theorem centralChargeN4_twoPointNorm (N : ℝ) :
    N ^ 2 / (16 * Real.pi ^ 2) = centralChargeN4 N / (4 * Real.pi ^ 2) := by
  unfold centralChargeN4; ring

/-- **[Bulk and boundary central charges agree].**  The compactified Newton
relation `G₅ = πR³/(2N²)` turns the bulk coefficient
`πR³/(8G₅)` into the boundary `N²/4`. -/
@[zil_level bridge_theorem]
theorem d3_bulkCentralCharge_eq_boundary (R N G5 : ℝ)
    (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2)) :
    bulkCentralCharge5 R G5 = centralChargeN4 N := by
  unfold bulkCentralCharge5 centralChargeN4
  rw [hG5]
  field_simp [hR, hN, Real.pi_ne_zero]
  ring

/-- **[The Compton-cell/D3 compactification dictionary].**  Let `V` be the
explicit extra-dimensional reduction factor relating the four-dimensional
Newton coupling to the five-dimensional one,
`G₅ = V G₄`.  If `G₄` is the repository's non-circular Compton-cell quotient,
then the D3 compactification theorem yields

`V(ℏcσ₀⁴) = πR³/(2N²)`,

and the same equality closes the bulk/boundary central-charge dictionary.
Keeping `V` explicit is essential: this theorem does **not** identify the
dimensionful couplings `G₄` and `G₅`. -/
@[zil_level bridge_theorem]
theorem comptonCell_d3_compactification_dictionary
    (σ₀ c ħ η V R N G5 : ℝ)
    (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0)
    (hR : R ≠ 0) (hN : N ≠ 0)
    (hG5 : G5 = Real.pi * R ^ 3 / (2 * N ^ 2))
    (hcompact :
      G5 =
        V * (sphereArea
              (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
            / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η))) :
    V * (ħ * c * σ₀ ^ 4) = Real.pi * R ^ 3 / (2 * N ^ 2) ∧
    bulkCentralCharge5 R G5 = centralChargeN4 N ∧
    centralChargeN4 N =
      Real.pi * R ^ 3 / (8 * (V * (ħ * c * σ₀ ^ 4))) := by
  have hscreen :
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
          / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η) =
        ħ * c * σ₀ ^ 4 :=
    newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK
  have hcompact' : G5 = V * (ħ * c * σ₀ ^ 4) := by
    calc
      G5 =
          V * (sphereArea
                  (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
                / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η)) := hcompact
      _ = V * (ħ * c * σ₀ ^ 4) := by rw [hscreen]
  have hcft : bulkCentralCharge5 R G5 = centralChargeN4 N :=
    d3_bulkCentralCharge_eq_boundary R N G5 hR hN hG5
  refine ⟨hcompact'.symm.trans hG5, hcft, ?_⟩
  calc
    centralChargeN4 N = bulkCentralCharge5 R G5 := hcft.symm
    _ = Real.pi * R ^ 3 / (8 * G5) := rfl
    _ = Real.pi * R ^ 3 / (8 * (V * (ħ * c * σ₀ ^ 4))) := by rw [hcompact']

/-! ## §D — Maldacena's rectangular Wilson loop and quark potential -/

/-- **Maldacena's strong-coupling Wilson coefficient**
`c(λ) = 4π²√(2λ)/Γ(1/4)⁴` (PRL 80 (1998), Eq. (12)).

The convention is the one already used by this module,
`λ = g²_{YM}N` and `R⁴ = 2λ(α')²`; hence the paper's numerator contains
`√(2λ)`. -/
noncomputable def maldacenaWilsonCoefficient (lam : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * Real.sqrt (2 * lam) / Real.Gamma (1 / 4) ^ 4

/-- **The regularized large-`N`, strong-coupling quark–antiquark energy**
`E(L) = -c(λ)/L` obtained from the fundamental-string minimal worldsheet
(Maldacena Eq. (12)). -/
noncomputable def maldacenaQuarkPotential (lam L : ℝ) : ℝ :=
  -maldacenaWilsonCoefficient lam / L

/-- **The leading rectangular Wilson-loop weight** `W(T,L) = e^{-T E(L)}` from
Maldacena Eq. (2), after suppressing the `T`-independent prefactor `A(L)`.

This reuses `kuikenWeight 1 S = exp(-S)` with the regularized Euclidean
worldsheet action `S_reg = T E(L)` rather than introducing another exponential
carrier. -/
noncomputable def maldacenaRectangularWilsonWeight (lam L T : ℝ) : ℝ :=
  kuikenWeight 1 (T * maldacenaQuarkPotential lam L)

/-- **The paper's gauge-theory variables are the existing 't Hooft coupling.**
Substituting `λ = g²_{YM}N` into Eq. (12) gives the stated
`-4π²√(2g²_{YM}N)/(Γ(1/4)⁴L)` potential. -/
lemma maldacenaQuarkPotential_tHooft (g N L : ℝ) :
    maldacenaQuarkPotential (tHooftCoupling g N) L =
      -(4 * Real.pi ^ 2 * Real.sqrt (2 * (g ^ 2 * N))
        / (Real.Gamma (1 / 4) ^ 4 * L)) := by
  unfold maldacenaQuarkPotential maldacenaWilsonCoefficient tHooftCoupling
  ring

/-- **The Wilson coefficient is positive at positive 't Hooft coupling.** -/
lemma maldacenaWilsonCoefficient_pos (lam : ℝ) (hlam : 0 < lam) :
    0 < maldacenaWilsonCoefficient lam := by
  have hGamma : 0 < Real.Gamma (1 / 4) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (2 * lam) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hlam)
  unfold maldacenaWilsonCoefficient
  positivity

/-- **The strong-coupling interaction is attractive.**  For positive coupling
and separation, Maldacena's regularized quark–antiquark energy is negative. -/
lemma maldacenaQuarkPotential_neg (lam L : ℝ) (hlam : 0 < lam) (hL : 0 < L) :
    maldacenaQuarkPotential lam L < 0 := by
  unfold maldacenaQuarkPotential
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (maldacenaWilsonCoefficient_pos lam hlam)) hL

/-- **Rectangular-loop energy extraction.**  The leading weight
`W(T,L)=e^{-TE(L)}` obeys `-log(W)/T = E(L)` for nonzero Euclidean time extent,
the exact algebraic content of Maldacena Eq. (2). -/
lemma maldacena_rectangularLoop_extracts_potential (lam L T : ℝ) (hT : T ≠ 0) :
    -(Real.log (maldacenaRectangularWilsonWeight lam L T)) / T =
      maldacenaQuarkPotential lam L := by
  unfold maldacenaRectangularWilsonWeight kuikenWeight
  rw [div_one, Real.log_exp]
  field_simp

/-- **The regularized leading factor exceeds one.**  For positive coupling,
separation, and Euclidean time, `E(L) < 0`, so `e^{-TE(L)} > 1`.  This is a
mass-subtracted Wilson observable, not a probability or confinement
suppression. -/
lemma maldacenaRectangularWilsonWeight_gt_one (lam L T : ℝ)
    (hlam : 0 < lam) (hL : 0 < L) (hT : 0 < T) :
    1 < maldacenaRectangularWilsonWeight lam L T := by
  unfold maldacenaRectangularWilsonWeight kuikenWeight
  rw [div_one, Real.one_lt_exp_iff]
  exact neg_pos.mpr
    (mul_neg_of_pos_of_neg hT (maldacenaQuarkPotential_neg lam L hlam hL))

/-! ## §E — strong-coupling and conformal scaling -/

/-- **The Wilson coefficient scales as `√λ`.**  Rescaling the coupling by
`a²` rescales `c(λ)` by `a` for `a ≥ 0`, making the paper's nonperturbative
square-root coupling dependence explicit. -/
lemma maldacenaWilsonCoefficient_coupling_scale (lam a : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 ≤ a) :
    maldacenaWilsonCoefficient (a ^ 2 * lam) =
      a * maldacenaWilsonCoefficient lam := by
  have h2lam : 0 ≤ 2 * lam := mul_nonneg (by norm_num) hlam
  unfold maldacenaWilsonCoefficient
  rw [show (2 : ℝ) * (a ^ 2 * lam) = (2 * lam) * a ^ 2 by ring,
    Real.sqrt_mul h2lam, Real.sqrt_sq ha]
  ring

/-- **Conformal `1/L` covariance.**  Rescaling the separation by `μ > 0`
rescales the quark–antiquark energy by `μ⁻¹`, as stated after Maldacena Eq. (12). -/
lemma maldacenaQuarkPotential_separation_scale (lam L mu : ℝ)
    (hL : L ≠ 0) (hmu : 0 < mu) :
    maldacenaQuarkPotential lam (mu * L) =
      maldacenaQuarkPotential lam L / mu := by
  unfold maldacenaQuarkPotential
  field_simp

/-- **The scale-invariant product is constant.**  Multiplying the conformal
potential by the separation removes `L`: `L E(L) = -c(λ)`. -/
lemma maldacenaQuarkPotential_scaleInvariant (lam L : ℝ) (hL : L ≠ 0) :
    L * maldacenaQuarkPotential lam L = -maldacenaWilsonCoefficient lam := by
  unfold maldacenaQuarkPotential
  field_simp

/-- **A factor-two dilation halves the interaction energy.** -/
lemma maldacenaQuarkPotential_double (lam L : ℝ) (hL : L ≠ 0) :
    maldacenaQuarkPotential lam (2 * L) =
      maldacenaQuarkPotential lam L / 2 := by
  exact maldacenaQuarkPotential_separation_scale lam L 2 hL (by norm_num)

/-- **The conformal Wilson potential is not a constant-tension linear potential.**
At positive coupling there is no constant `σ` such that `E(L) = σL` at every
positive separation: `E(2L) = E(L)/2`, whereas a linear potential would obey
`E(2L) = 2E(L)`.  This separates Maldacena's conformal result from the repo's
QCD Wilson-loop area-law formalizations. -/
lemma maldacenaQuarkPotential_not_linear (lam : ℝ) (hlam : 0 < lam) :
    ¬ ∃ sigma : ℝ, ∀ L : ℝ, 0 < L →
      maldacenaQuarkPotential lam L = sigma * L := by
  rintro ⟨sigma, hlinear⟩
  have h1 := hlinear 1 (by norm_num)
  have h2 := hlinear 2 (by norm_num)
  have hdouble := maldacenaQuarkPotential_double lam 1 (by norm_num)
  have hneg := maldacenaQuarkPotential_neg lam 1 hlam (by norm_num)
  rw [h1] at hneg
  norm_num at hdouble
  rw [h2, h1] at hdouble
  norm_num at hdouble
  nlinarith

/-! ## §F — the assembled worldsheet/Wilson-loop dictionary -/

/-- **The regularized worldsheet exponential is the master-weight modulus.**
Maldacena's `e^{-S_reg}` with `S_reg = T E(L)` is exactly the modulus of the
repository's complex-action path-integral weight with that real exponential
action in its damping slot. -/
lemma maldacena_worldsheet_is_master_modulus (lam L T S_R : ℝ) :
    maldacenaRectangularWilsonWeight lam L T =
      ‖complexActionPathIntegralWeight S_R
        (T * maldacenaQuarkPotential lam L) 1‖ := by
  unfold maldacenaRectangularWilsonWeight
  rw [master_modulus_is_kuiken]

/-- **Maldacena's rectangular Wilson-loop dictionary, assembled.**  At positive
coupling, separation, and Euclidean time:

* the exact Eq. (12) coefficient is positive;
* the regularized quark–antiquark potential is attractive;
* `-log(W)/T` extracts that potential;
* the mass-subtracted leading Wilson factor is greater than one;
* doubling the separation halves the conformal interaction energy;
* the worldsheet factor `e^{-S_reg}` is the repo's master-weight modulus.

The minimal-surface solution and mass subtraction are the analytical input from
the paper; every implication collected here is checked from the reused Lean
definitions. -/
@[zil_level bridge_theorem]
lemma maldacenaWilsonLoop_dictionary (lam L T S_R : ℝ)
    (hlam : 0 < lam) (hL : 0 < L) (hT : 0 < T) :
    0 < maldacenaWilsonCoefficient lam
      ∧ maldacenaQuarkPotential lam L < 0
      ∧ -(Real.log (maldacenaRectangularWilsonWeight lam L T)) / T =
        maldacenaQuarkPotential lam L
      ∧ 1 < maldacenaRectangularWilsonWeight lam L T
      ∧ maldacenaQuarkPotential lam (2 * L) =
        maldacenaQuarkPotential lam L / 2
      ∧ maldacenaRectangularWilsonWeight lam L T =
        ‖complexActionPathIntegralWeight S_R
          (T * maldacenaQuarkPotential lam L) 1‖ :=
  ⟨maldacenaWilsonCoefficient_pos lam hlam,
    maldacenaQuarkPotential_neg lam L hlam hL,
    maldacena_rectangularLoop_extracts_potential lam L T hT.ne',
    maldacenaRectangularWilsonWeight_gt_one lam L T hlam hL hT,
    maldacenaQuarkPotential_double lam L hL.ne',
    maldacena_worldsheet_is_master_modulus lam L T S_R⟩

/-! ## §G — Hawking–Page circle-exchange saddle selection -/

/-- **The Hawking–Page critical inverse temperature**
`β_c=2πr_y` of the compactified confining example (Maldacena lecture §6.1). -/
noncomputable def hawkingPageCriticalBeta (r_y : ℝ) : ℝ :=
  2 * Real.pi * r_y

/-- The normalized low-temperature (confined) Euclidean saddle action
`I_conf=C L/β`.  Together with `hawkingPageDeconfinedAction` it is the
minimal circle-exchange model: interchanging the two boundary circles
`β ↔ L` interchanges the two actions. -/
noncomputable def hawkingPageConfinedAction (C β L : ℝ) : ℝ :=
  C * L / β

/-- The normalized high-temperature (deconfined/black-brane) Euclidean saddle
action `I_deconf=C β/L`, obtained from the confined saddle by exchanging the
thermal and spatial circles. -/
noncomputable def hawkingPageDeconfinedAction (C β L : ℝ) : ℝ :=
  C * β / L

/-- The Euclidean saddle weight `e^{-I}`, reusing the repository's master real
damping exponential rather than introducing another Boltzmann carrier. -/
noncomputable def hawkingPageSaddleWeight (I : ℝ) : ℝ :=
  kuikenWeight 1 I

/-- Lower Euclidean action gives strictly larger saddle weight. -/
lemma hawkingPageSaddleWeight_order_reversing {I₁ I₂ : ℝ} (h : I₁ < I₂) :
    hawkingPageSaddleWeight I₂ < hawkingPageSaddleWeight I₁ := by
  unfold hawkingPageSaddleWeight kuikenWeight
  rw [div_one, div_one, Real.exp_lt_exp]
  linarith

/-- The two exchanged-circle actions coincide at the crossing `β=L`. -/
lemma hawkingPage_actions_eq_critical (C L : ℝ) (hL : L ≠ 0) :
    hawkingPageConfinedAction C L L = C
      ∧ hawkingPageDeconfinedAction C L L = C := by
  unfold hawkingPageConfinedAction hawkingPageDeconfinedAction
  constructor <;> field_simp

/-- At low temperature (`L<β`) the confined saddle has lower Euclidean
action. -/
lemma hawkingPage_confined_dominates_lowTemperature (C β L : ℝ)
    (hC : 0 < C) (hL : 0 < L) (hβ : L < β) :
    hawkingPageConfinedAction C β L <
      hawkingPageDeconfinedAction C β L := by
  unfold hawkingPageConfinedAction hawkingPageDeconfinedAction
  rw [div_lt_div_iff₀ (lt_trans hL hβ) hL]
  have hsq : L ^ 2 < β ^ 2 := by nlinarith
  convert mul_lt_mul_of_pos_left hsq hC using 1 <;> ring

/-- At high temperature (`β<L`) the deconfined black-brane saddle has lower
Euclidean action. -/
lemma hawkingPage_deconfined_dominates_highTemperature (C β L : ℝ)
    (hC : 0 < C) (hβ : 0 < β) (hβL : β < L) :
    hawkingPageDeconfinedAction C β L <
      hawkingPageConfinedAction C β L := by
  unfold hawkingPageConfinedAction hawkingPageDeconfinedAction
  rw [div_lt_div_iff₀ (lt_trans hβ hβL) hβ]
  have hsq : β ^ 2 < L ^ 2 := by nlinarith
  convert mul_lt_mul_of_pos_left hsq hC using 1 <;> ring

/-- The inverse-temperature derivative of the confined saddle action. -/
lemma hawkingPage_confined_hasDerivAt (C L β : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (fun x => hawkingPageConfinedAction C x L)
      (-(C * L / β ^ 2)) β := by
  unfold hawkingPageConfinedAction
  simpa only [div_eq_mul_inv, mul_neg] using
    (hasDerivAt_inv hβ).const_mul (C * L)

/-- The inverse-temperature derivative of the deconfined saddle action. -/
lemma hawkingPage_deconfined_hasDerivAt (C L β : ℝ) :
    HasDerivAt (fun x => hawkingPageDeconfinedAction C x L) (C / L) β := by
  unfold hawkingPageDeconfinedAction
  simpa [id_eq] using (hasDerivAt_id β).const_mul C |>.div_const L

/-- **The saddle crossing has a nonzero slope jump.**  At `β=L` the two
actions agree, but their inverse-temperature derivatives are `-C/L` and
`C/L`.  This is the first-order Hawking–Page signature in the normalized
circle-exchange action. -/
lemma hawkingPage_slope_jump (C L : ℝ) (hC : 0 < C) (hL : 0 < L) :
    HasDerivAt (fun β => hawkingPageConfinedAction C β L) (-C / L) L
      ∧ HasDerivAt (fun β => hawkingPageDeconfinedAction C β L) (C / L) L
      ∧ -C / L ≠ C / L := by
  refine ⟨?_, hawkingPage_deconfined_hasDerivAt C L L, ?_⟩
  · convert hawkingPage_confined_hasDerivAt C L L hL.ne' using 1
    field_simp
  · have hpos : 0 < C / L := div_pos hC hL
    apply ne_of_lt
    calc
      -C / L < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hC) hL
      _ < C / L := hpos

/-- **[Hawking–Page / confinement-deconfinement phase structure]**
the exchanged-circle saddles:

* meet at `β=L` with unequal slopes;
* select the confined saddle for `L<β` (low temperature);
* select the deconfined black-brane saddle for `β<L` (high temperature);
* and the lower action has the larger master complex-action modulus.

Taking `L=hawkingPageCriticalBeta r_y=2πr_y` gives Maldacena's §6.1
critical temperature.  The theorem proves the normalized circle-exchange
saddle algebra; construction of the two Euclidean gravity solutions and their
renormalized on-shell normalization remain the cited gravitational input. -/
@[zil_level bridge_theorem]
lemma hawkingPage_circleExchange_phaseStructure (C β L : ℝ)
    (hC : 0 < C) (hβ : 0 < β) (hL : 0 < L) :
    (β = L →
      hawkingPageConfinedAction C β L =
          hawkingPageDeconfinedAction C β L
        ∧ HasDerivAt (fun b => hawkingPageConfinedAction C b L) (-C / L) L
        ∧ HasDerivAt (fun b => hawkingPageDeconfinedAction C b L) (C / L) L
        ∧ -C / L ≠ C / L)
      ∧ (L < β →
        hawkingPageConfinedAction C β L <
            hawkingPageDeconfinedAction C β L
          ∧ hawkingPageSaddleWeight
              (hawkingPageDeconfinedAction C β L) <
            hawkingPageSaddleWeight
              (hawkingPageConfinedAction C β L))
      ∧ (β < L →
        hawkingPageDeconfinedAction C β L <
            hawkingPageConfinedAction C β L
          ∧ hawkingPageSaddleWeight
              (hawkingPageConfinedAction C β L) <
            hawkingPageSaddleWeight
              (hawkingPageDeconfinedAction C β L)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    have hs := hawkingPage_slope_jump C β hC hβ
    exact ⟨(hawkingPage_actions_eq_critical C β hβ.ne').1.trans
      (hawkingPage_actions_eq_critical C β hβ.ne').2.symm,
      hs.1, hs.2.1, hs.2.2⟩
  · intro hlow
    have ha :=
      hawkingPage_confined_dominates_lowTemperature C β L hC hL hlow
    exact ⟨ha, hawkingPageSaddleWeight_order_reversing ha⟩
  · intro hhigh
    have ha :=
      hawkingPage_deconfined_dominates_highTemperature C β L hC hβ hhigh
    exact ⟨ha, hawkingPageSaddleWeight_order_reversing ha⟩

/-! ## §H — thermal AdS₅ black-brane entropy and the `3/4` factor -/

/-- **[Maldacena lecture Eq. 5.2]** The strong-coupling entropy density of
thermal `N=4` SYM from the AdS₅ black-brane horizon,
`s_strong=(π²/2)N²T³`. -/
noncomputable def strongCouplingEntropyDensity (N T : ℝ) : ℝ :=
  Real.pi ^ 2 / 2 * N ^ 2 * T ^ 3

/-- **[Maldacena lecture Eq. 5.3]** The free-field entropy density of
`N=4` SYM, `s_free=(2π²/3)N²T³`. -/
noncomputable def freeFieldEntropyDensity (N T : ℝ) : ℝ :=
  2 * Real.pi ^ 2 / 3 * N ^ 2 * T ^ 3

/-- Both thermal entropy densities are nonnegative for nonnegative
temperature. -/
lemma thermalEntropyDensities_nonneg (N T : ℝ) (hT : 0 ≤ T) :
    0 ≤ strongCouplingEntropyDensity N T
      ∧ 0 ≤ freeFieldEntropyDensity N T := by
  unfold strongCouplingEntropyDensity freeFieldEntropyDensity
  constructor <;> positivity

/-- **[The thermal AdS/CFT `3/4` factor]**
`s_strong=(3/4)s_free`.

The theorem checks the exact coefficient comparison after the two entropy
densities are supplied by the black-brane horizon and free-field counts.  It
does not derive either count or the finite-coupling interpolation. -/
@[zil_level bridge_theorem]
lemma strongCouplingEntropyDensity_eq_threeFourths_free (N T : ℝ) :
    strongCouplingEntropyDensity N T =
      (3 / 4 : ℝ) * freeFieldEntropyDensity N T := by
  unfold strongCouplingEntropyDensity freeFieldEntropyDensity
  ring

/-! ## §I — large-`N` correlator factorization -/

/-- The `O(N⁻²)` defect from disconnected two-point factorization
`⟨O₁O₂⟩-⟨O₁⟩⟨O₂⟩` (Maldacena lecture Eq. 2.12), with `c₂` the
`N`-independent coefficient. -/
noncomputable def largeNFactorizationDefect (c₂ : ℝ) (N : ℕ) : ℝ :=
  c₂ / (N : ℝ) ^ 2

/-- The `O(N⁻¹)` normalized connected three-point ratio
`⟨OOO⟩_c/⟨OO⟩_c^{3/2}` (Maldacena lecture Eq. 2.13), with `c₃` the
`N`-independent coefficient. -/
noncomputable def largeNThreePointRatio (c₃ : ℝ) (N : ℕ) : ℝ :=
  c₃ / (N : ℝ)

/-- **[Large-`N` factorization and classical bulk limit]**
the `N⁻²` factorization defect and the `N⁻¹` normalized connected
three-point interaction both vanish as `N→∞`.

The theorem proves the asymptotic consequences of the paper's genus-counting
powers.  It does not derive those powers from matrix-index combinatorics or
construct the boundary correlators. -/
@[zil_level bridge_theorem]
lemma largeN_correlatorSuppressions_tendsto_zero (c₂ c₃ : ℝ) :
    Filter.Tendsto (largeNFactorizationDefect c₂) Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (largeNThreePointRatio c₃) Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun N : ℕ => ((N : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  constructor
  · change Filter.Tendsto (fun N : ℕ => c₂ / (N : ℝ) ^ 2)
      Filter.atTop (nhds 0)
    simpa [div_eq_mul_inv, inv_pow] using
      (hinv.pow 2).const_mul c₂
  · change Filter.Tendsto (fun N : ℕ => c₃ / (N : ℝ))
      Filter.atTop (nhds 0)
    simpa [div_eq_mul_inv] using
      hinv.const_mul c₃

/-! ## §J — KSS shear-viscosity saturation -/

/-- **[KSS Eq. (10)]** The shear-viscosity density of the strongly coupled
thermal D3-brane theory, `η=(π/8)N²T³`.

This closed coefficient incorporates the low-frequency graviton absorption
cross-section calculation `σ_abs(0)=a`; that analytic black-brane calculation
is not rederived by this definition. -/
noncomputable def strongCouplingShearViscosity (N T : ℝ) : ℝ :=
  Real.pi / 8 * N ^ 2 * T ^ 3

/-- **[KSS Eqs. (5) and (10)]** The low-frequency absorption expression
`η=σ_abs(0)/(16πG)` for the shear-viscosity density. -/
noncomputable def lowFrequencyAbsorptionViscosity
    (absorptionCrossSection G : ℝ) : ℝ :=
  absorptionCrossSection / (16 * Real.pi * G)

/-- **[KSS from the horizon absorption theorem].** If the low-frequency
graviton absorption cross-section is the horizon area density,
`σ_abs(0)=a`, then the Kubo/absorption expression
`η=σ_abs(0)/(16πG)` and the Bekenstein–Hawking/RT expression
`s=a/(4G)` give `η/s=1/(4π)`.

Unlike a definition using the final D3 coefficients, this theorem exposes the
load-bearing analytic input `σ_abs(0)=a` as a hypothesis.  It does not prove
that black-hole scattering theorem, nor the conjectured universal inequality. -/
@[zil_level bridge_theorem]
theorem kssRatio_from_lowFrequencyHorizonAbsorption
    (absorptionCrossSection horizonAreaDensity G : ℝ)
    (habs : absorptionCrossSection = horizonAreaDensity)
    (ha : horizonAreaDensity ≠ 0) (hG : G ≠ 0) :
    lowFrequencyAbsorptionViscosity absorptionCrossSection G /
        rtAreaEntropy horizonAreaDensity G =
      1 / (4 * Real.pi) := by
  rw [habs]
  unfold lowFrequencyAbsorptionViscosity rtAreaEntropy
  field_simp [ha, hG, Real.pi_ne_zero]
  all_goals ring

/-- **[KSS saturation in the two-derivative D3 gravity dual]**
`η/s=1/(4π)` for nonzero rank and temperature.

This proves the exact ratio of the black-brane coefficients supplied by the
KSS calculation.  It neither asserts nor proves the conjectured inequality
`η/s ≥ 1/(4π)` for every quantum system, and it makes no claim about
higher-derivative or finite-coupling corrections. -/
@[zil_level bridge_theorem]
theorem d3_kssRatio_saturates_twoDerivativeGravity
    (N T : ℝ) (hN : N ≠ 0) (hT : T ≠ 0) :
    strongCouplingShearViscosity N T /
        strongCouplingEntropyDensity N T =
      1 / (4 * Real.pi) := by
  unfold strongCouplingShearViscosity strongCouplingEntropyDensity
  field_simp [hN, hT, Real.pi_ne_zero]
  all_goals ring

/-! ## §K — lightlike Wilson loops and strong-coupling jet quenching -/

/-- The exact dimensionless Liu–Rajagopal–Wiedemann coefficient
`π^(3/2) Γ(3/4)/Γ(5/4)` in the strong-coupling jet-quenching parameter. -/
noncomputable def jetQuenchingPrefactor : ℝ :=
  Real.pi * Real.sqrt Real.pi *
    Real.Gamma (3 / 4 : ℝ) / Real.Gamma (5 / 4 : ℝ)

/-- **[LRW Eq. (11)]** The `N=4` SYM strong-coupling jet-quenching parameter
`q̂ = π^(3/2) Γ(3/4)/Γ(5/4) √λ T³`. -/
noncomputable def strongCouplingJetQuenching (lam T : ℝ) : ℝ :=
  jetQuenchingPrefactor * Real.sqrt lam * T ^ 3

/-- **[LRW Eq. (2)]** The leading adjoint lightlike Wilson-loop weight
`exp(-q̂ L⁻ L²/(4√2))`. -/
noncomputable def lightlikeAdjointWilsonWeight
    (qhat Lminus L : ℝ) : ℝ :=
  Real.exp (-(qhat * Lminus * L ^ 2) / (4 * Real.sqrt 2))

/-- The LRW gamma-function coefficient is strictly positive. -/
lemma jetQuenchingPrefactor_pos : 0 < jetQuenchingPrefactor := by
  unfold jetQuenchingPrefactor
  have h34 : 0 < Real.Gamma (3 / 4 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have h54 : 0 < Real.Gamma (5 / 4 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  positivity

/-- `q̂` is homogeneous of degree `1/2` in the 't Hooft coupling:
`q̂(a²λ,T)=a q̂(λ,T)` for `a,λ ≥ 0`. -/
lemma strongCouplingJetQuenching_coupling_scale
    (lam T a : ℝ) (hlam : 0 ≤ lam) (ha : 0 ≤ a) :
    strongCouplingJetQuenching (a ^ 2 * lam) T =
      a * strongCouplingJetQuenching lam T := by
  unfold strongCouplingJetQuenching
  rw [show a ^ 2 * lam = lam * a ^ 2 by ring, Real.sqrt_mul hlam,
    Real.sqrt_sq ha]
  ring

/-- `q̂` is homogeneous of degree three in temperature:
`q̂(λ,bT)=b³q̂(λ,T)`. -/
lemma strongCouplingJetQuenching_temperature_scale
    (lam T b : ℝ) :
    strongCouplingJetQuenching lam (b * T) =
      b ^ 3 * strongCouplingJetQuenching lam T := by
  unfold strongCouplingJetQuenching
  ring

/-- The LRW strong-coupling jet-quenching coefficient is strictly positive
for positive 't Hooft coupling and temperature. -/
lemma strongCouplingJetQuenching_pos
    (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) :
    0 < strongCouplingJetQuenching lam T := by
  unfold strongCouplingJetQuenching
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  exact mul_pos (mul_pos jetQuenchingPrefactor_pos hsqrt) (pow_pos hT 3)

/-- The LRW Wilson-loop suppression is exactly the modulus of the repository's
master complex-action weight with imaginary action `q̂L⁻L²` and
`ℏ_eff=4√2`. -/
lemma lightlikeAdjointWilsonWeight_is_master_modulus
    (qhat Lminus L SReal : ℝ) :
    lightlikeAdjointWilsonWeight qhat Lminus L =
      ‖complexActionPathIntegralWeight SReal
        (qhat * Lminus * L ^ 2) (4 * Real.sqrt 2)‖ := by
  rw [master_modulus_is_kuiken]
  unfold lightlikeAdjointWilsonWeight kuikenWeight
  congr 1
  ring

/-- **[The LRW strong-coupling jet-quenching chain]** The exact coefficient is
positive, the result scales as `√λ T³`, and its defining lightlike adjoint
Wilson loop is the master complex-action modulus.

The closed coefficient and the Wilson-loop saddle exponent are the paper's
analytic inputs.  Lean proves their positivity, both homogeneities, and the
complex-action identification; it does not solve the extremal worldsheet,
derive the Wilson-loop prescription, or identify this conformal `N=4` SYM
observable with a universal QCD transport coefficient. -/
@[zil_level bridge_theorem]
theorem jetQuenching_lightlikeWilson_scaling_chain
    (lam T a b Lminus L SReal : ℝ) (hlam : 0 ≤ lam) (ha : 0 ≤ a) :
    0 < jetQuenchingPrefactor
      ∧ strongCouplingJetQuenching (a ^ 2 * lam) T =
          a * strongCouplingJetQuenching lam T
      ∧ strongCouplingJetQuenching lam (b * T) =
          b ^ 3 * strongCouplingJetQuenching lam T
      ∧ lightlikeAdjointWilsonWeight
          (strongCouplingJetQuenching lam T) Lminus L =
        ‖complexActionPathIntegralWeight SReal
          (strongCouplingJetQuenching lam T * Lminus * L ^ 2)
          (4 * Real.sqrt 2)‖ := by
  exact ⟨jetQuenchingPrefactor_pos,
    strongCouplingJetQuenching_coupling_scale lam T a hlam ha,
    strongCouplingJetQuenching_temperature_scale lam T b,
    lightlikeAdjointWilsonWeight_is_master_modulus
      (strongCouplingJetQuenching lam T) Lminus L SReal⟩

/-- **[Physical LRW suppression regime].** At positive coupling, temperature,
and light-cone length, with nonzero transverse separation, the strong-coupling
jet-quenching coefficient is positive and its adjoint lightlike Wilson factor
is a strict damping factor:

`0 < exp(-q̂L⁻L²/(4√2)) < 1`.

This is the sign/order consequence of the LRW saddle result.  It does not turn
the Wilson-loop expectation into a normalized probability. -/
@[zil_level bridge_theorem]
theorem jetQuenching_lightlikeWilson_strictSuppression
    (lam T Lminus L : ℝ)
    (hlam : 0 < lam) (hT : 0 < T)
    (hLm : 0 < Lminus) (hL : L ≠ 0) :
    0 < strongCouplingJetQuenching lam T
      ∧ 0 < lightlikeAdjointWilsonWeight
          (strongCouplingJetQuenching lam T) Lminus L
      ∧ lightlikeAdjointWilsonWeight
          (strongCouplingJetQuenching lam T) Lminus L < 1 := by
  have hq : 0 < strongCouplingJetQuenching lam T :=
    strongCouplingJetQuenching_pos lam T hlam hT
  refine ⟨hq, Real.exp_pos _, ?_⟩
  unfold lightlikeAdjointWilsonWeight
  rw [Real.exp_lt_one_iff]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hL2 : 0 < L ^ 2 := sq_pos_of_ne_zero hL
  have hnum : 0 < strongCouplingJetQuenching lam T * Lminus * L ^ 2 :=
    mul_pos (mul_pos hq hLm) hL2
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum)
    (mul_pos (by norm_num) hs2)

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.ads_sphere_dimension_split where
  formalizes @ "claim:the-d3-brane-kaluza-klein-dimension-splits-the-ads5-mass-into-the-s5-sphere-harmonic-eigenvalue",
  supported_by @ "paper:kim-romans-vannieuwenhuizen-1985-mass-spectrum-ads5-s5"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.kaluzaKlein_zeroMode where
  formalizes @ "claim:the-d3-brane-kaluza-klein-zero-mode-has-conformal-dimension-four-the-marginal-operator",
  requires @ "claim:the-d3-brane-kaluza-klein-dimension-splits-the-ads5-mass-into-the-s5-sphere-harmonic-eigenvalue"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.unitS5_surfaceVolume where
  formalizes @ "claim:the-haar-induced-surface-volume-of-the-unit-five-sphere-in-real-six-space-is-pi-cubed",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:MeasureTheory.Measure.toSphere_real_apply_univ",
  supported_by @ "lean:InnerProductSpace.volume_ball_of_dim_even",
  caveat @ "claim:this-is-a-genuine-measure-theoretic-sphere-volume-theorem-and-does-not-assume-the-d3-string-compactification-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_newton_from_string_compactification where
  formalizes @ "claim:the-d3-radius-ten-dimensional-newton-coupling-and-geometric-five-sphere-reduction-imply-g5-equals-pi-r-cubed-over-two-n-squared",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:ryu-takayanagi-0603001v2-g10-equals-pi-cubed-r-fifth-g5",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.unitS5_surfaceVolume",
  caveat @ "claim:the-five-sphere-volume-is-proved-but-the-d3-radius-relation-g10-normalization-and-kaluza-klein-reduction-equation-are-explicit-string-theory-premises"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_bulkCentralCharge_eq_boundary where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_newton_from_string_compactification",
  formalizes @ "claim:the-d3-five-dimensional-newton-dictionary-makes-the-bulk-central-charge-pi-r-cubed-over-eight-g5-equal-the-boundary-n-squared-over-four",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-d3-radius-ten-dimensional-newton-coupling-and-geometric-five-sphere-reduction-imply-g5-equals-pi-r-cubed-over-two-n-squared",
  caveat @ "claim:an-exact-dictionary-consequence-not-an-independent-numerical-prediction-of-n-or-the-ads-radius"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary where
  formalizes @ "claim:an-explicit-extra-dimensional-reduction-factor-links-the-compton-cell-g4-equals-hbar-c-sigma-fourth-to-the-d3-g5-and-bulk-boundary-central-charge-dictionary",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_bulkCentralCharge_eq_boundary",
  caveat @ "claim:the-reduction-factor-v-is-explicitly-supplied-and-the-theorem-does-not-identify-the-dimensionful-four-and-five-dimensional-newton-couplings",
  caveat @ "claim:the-result-is-a-conditional-cross-sector-dictionary-not-an-observed-value-fit-or-an-independent-ads-cft-prediction"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.maldacenaWilsonLoop_dictionary where
  formalizes @ "claim:maldacenas-regularized-rectangular-worldsheet-gives-an-attractive-conformal-one-over-l-quark-potential-whose-euclidean-weight-is-the-master-complex-action-modulus",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:maldacena-1998-wilson-loops-large-n-equations-2-5-12",
  caveat @ "claim:the-closed-regularized-minimal-worldsheet-result-is-the-paper-input-lean-proves-its-sign-scaling-energy-extraction-and-master-weight-identification-not-the-minimal-surface-pde-or-probe-mass-renormalization",
  caveat @ "claim:conformal-n-equals-four-sym-one-over-l-potential-is-explicitly-not-a-qcd-confining-area-law"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.hawkingPage_circleExchange_phaseStructure where
  formalizes @ "claim:the-two-circle-exchanged-euclidean-ads-saddles-cross-at-beta-equals-l-with-a-nonzero-action-slope-jump-and-reverse-confined-deconfined-dominance",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:maldacena-tasi-ads-cft-0309246v5-section-6-1",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight",
  caveat @ "claim:the-normalized-circle-exchange-actions-capture-the-saddle-ordering-and-first-order-crossing-but-do-not-construct-the-euclidean-gravity-solutions-or-renormalize-their-full-on-shell-actions",
  caveat @ "claim:identifying-l-with-two-pi-r-y-is-the-paper-specific-compactification-input-not-a-universal-qcd-critical-temperature"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.strongCouplingEntropyDensity_eq_threeFourths_free where
  formalizes @ "claim:the-ads5-black-brane-strong-coupling-n-equals-four-sym-entropy-density-is-exactly-three-quarters-of-the-free-field-entropy-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:maldacena-tasi-ads-cft-0309246v5-equations-5-2-5-3",
  caveat @ "claim:exact-comparison-of-two-paper-supplied-coefficients-not-a-gravity-horizon-area-calculation-a-free-field-state-count-or-a-finite-thooft-coupling-interpolation"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.largeN_correlatorSuppressions_tendsto_zero where
  formalizes @ "claim:the-large-n-two-point-factorization-defect-of-order-one-over-n-squared-and-normalized-connected-three-point-ratio-of-order-one-over-n-both-vanish",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:maldacena-tasi-ads-cft-0309246v5-equations-2-12-2-13",
  supported_by @ "lean:tendsto_inv_atTop_zero",
  caveat @ "claim:proves-the-limits-of-the-paper-supplied-genus-counting-powers-not-the-matrix-index-combinatorics-the-correlator-expansion-or-the-bulk-classical-limit"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_kssRatio_saturates_twoDerivativeGravity where
  formalizes @ "claim:the-two-derivative-d3-black-brane-gravity-dual-saturates-the-kss-shear-viscosity-to-entropy-density-ratio-at-one-over-four-pi",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:kovtun-son-starinets-hep-th-0405231-equations-5-10-11",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.strongCouplingEntropyDensity_eq_threeFourths_free",
  caveat @ "claim:the-closed-viscosity-and-entropy-coefficients-are-the-paper-inputs-and-lean-proves-their-exact-ratio-not-the-kubo-absorption-cross-section-calculation",
  caveat @ "claim:this-is-saturation-in-the-two-derivative-d3-gravity-dual-not-a-proof-of-a-universal-lower-bound-or-of-higher-derivative-and-finite-coupling-corrections"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.kssRatio_from_lowFrequencyHorizonAbsorption where
  formalizes @ "claim:an-explicit-low-frequency-absorption-cross-section-equals-horizon-area-premise-combines-the-kubo-viscosity-and-area-entropy-formulas-to-give-the-kss-one-over-four-pi-ratio",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:kovtun-son-starinets-hep-th-0405231-equations-5-10-11",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy",
  caveat @ "claim:the-low-frequency-absorption-cross-section-equals-horizon-area-theorem-is-an-explicit-hypothesis-rather-than-being-hidden-inside-the-final-d3-coefficients",
  caveat @ "claim:lean-proves-the-ratio-from-that-analytic-scattering-input-not-the-black-brane-wave-equation-or-the-conjectured-universal-bound"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.jetQuenching_lightlikeWilson_scaling_chain where
  formalizes @ "claim:the-lrw-strong-coupling-jet-quenching-coefficient-is-positive-scales-as-square-root-lambda-times-temperature-cubed-and-its-lightlike-adjoint-wilson-loop-is-the-master-complex-action-modulus",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:liu-rajagopal-wiedemann-hep-ph-0605178-equations-2-3-11",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  caveat @ "claim:the-extremal-worldsheet-and-closed-gamma-function-coefficient-are-paper-inputs-while-lean-proves-positivity-homogeneity-and-the-master-weight-identification",
  caveat @ "claim:the-result-is-for-conformal-n-equals-four-sym-at-large-n-and-strong-coupling-not-a-universal-qcd-transport-coefficient"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.jetQuenching_lightlikeWilson_strictSuppression where
  formalizes @ "claim:positive-coupling-temperature-and-light-cone-length-with-nonzero-transverse-separation-make-the-lrw-jet-quenching-coefficient-positive-and-the-lightlike-adjoint-wilson-factor-strictly-between-zero-and-one",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-lrw-strong-coupling-jet-quenching-coefficient-is-positive-scales-as-square-root-lambda-times-temperature-cubed-and-its-lightlike-adjoint-wilson-loop-is-the-master-complex-action-modulus",
  supported_by @ "lean:Real.exp_lt_one_iff",
  caveat @ "claim:a-strict-order-theorem-in-the-physical-parameter-regime-not-a-normalization-of-the-wilson-loop-as-a-probability-or-a-universal-qcd-statement"

zil_file_contract physlib.d3BraneHolographicSpectrum where
  promises "The D3-brane holographic spectrum, compactification, and thermal/Wilson observables: the Kaluza-Klein reduction on the five-sphere splits the AdS5 mass into the S5 harmonic eigenvalue and the zero mode has conformal dimension four; the genuine unit-five-sphere measure is pi cubed and the D3 string inputs therefore imply G5 equals pi R cubed over two N squared; this equates the bulk and boundary central charges and, through an explicit reduction volume rather than a dimensionally false equality, links the Compton-cell G4 equals hbar c sigma fourth to the D3 dictionary; Maldacena's closed regularized rectangular-worldsheet result yields an attractive conformal inverse-distance potential with exact master complex-action weight; the two circle-exchanged Hawking-Page saddles cross with a nonzero slope jump, selecting confinement at low temperature and the black-brane/deconfined saddle at high temperature; the AdS5 black-brane entropy density is exactly three quarters of the free-field N equals four SYM entropy density; the paper-supplied one-over-N-squared factorization defect and one-over-N normalized connected three-point ratio vanish at large N; the two-derivative D3 gravity dual saturates the KSS shear-viscosity ratio at one over four pi, with a second theorem exposing the low-frequency absorption-equals-area premise rather than hiding it in final coefficients; and the LRW jet-quenching coefficient is positive, scales as square-root lambda times temperature cubed, supplies a lightlike Wilson-loop master complex-action modulus, and gives a strict zero-to-one damping factor in the physical parameter regime."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.sphereS5Eigenvalue",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.tHooftCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight"]
  forbids_substitutes ["the full supergravity Kaluza-Klein tower with its supermultiplet structure, only the scalar dimension split",
    "a derivation of the N=4 super Yang-Mills spectrum, taken as the holographic dual",
    "solving and renormalizing the Maldacena minimal worldsheet PDE",
    "constructing and holographically renormalizing the full Hawking-Page Euclidean gravity saddles",
    "deriving either thermal entropy coefficient or the finite-coupling interpolation between them",
    "deriving large-N genus-counting powers from matrix-index combinatorics or constructing the boundary correlators",
    "proving the low-frequency black-brane absorption cross-section equals its horizon area",
    "promoting the two-derivative D3 KSS saturation identity into a universal lower-bound theorem",
    "solving the lightlike extremal worldsheet or treating its N=4 SYM jet-quenching coefficient as a universal QCD value",
    "identifying four-dimensional and five-dimensional Newton constants without an explicit compactification factor"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.ads_sphere_dimension_split,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.kaluzaKlein_zeroMode,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.unitS5_surfaceVolume,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_newton_from_string_compactification,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_bulkCentralCharge_eq_boundary,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.comptonCell_d3_compactification_dictionary,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.maldacenaWilsonLoop_dictionary,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.hawkingPage_circleExchange_phaseStructure,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.strongCouplingEntropyDensity_eq_threeFourths_free,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.largeN_correlatorSuppressions_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.d3_kssRatio_saturates_twoDerivativeGravity,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.kssRatio_from_lowFrequencyHorizonAbsorption,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.jetQuenching_lightlikeWilson_scaling_chain,
    Physlib.QuantumMechanics.ComplexAction.AdSCFT.D3BraneHolographicSpectrum.jetQuenching_lightlikeWilson_strictSuppression]

/- ZIL-END -/

#zil_formalization_lint physlib.d3BraneHolographicSpectrum
