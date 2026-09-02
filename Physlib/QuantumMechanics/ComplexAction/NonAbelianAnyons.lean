/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

/-!
# Non-abelian anyons: Fibonacci and Ising fusion and quantum dimensions

Extending the **abelian** exchange spectrum (`ExchangeStatisticsSpectrum`, where every particle has a
`U(1)` exchange phase and quantum dimension `1`) to the **non-abelian** case, where fusion has multiple
channels and the quantum dimension exceeds one. The two universal examples:

  * **Fibonacci** `τ`: `τ × τ = 1 + τ`, quantum dimension `d_τ = φ` (the golden ratio);
  * **Ising** `σ`: `σ × σ = 1 + ψ`, quantum dimension `d_σ = √2`.

The defining consistency of a fusion category — `d_a d_b = Σ_c N_{ab}^c d_c` — fixes these dimensions,
and the criterion `d > 1` distinguishes non-abelian anyons from the abelian ones (`d = 1`).

* **§A — Fibonacci anyons.** `fibonacciDim = φ` with the fusion consistency `d_τ² = 1 + d_τ`
  (`fibonacci_fusion_consistency`, the golden-ratio identity), `d_τ > 1` (`fibonacci_nonabelian`), and
  the total quantum dimension `D² = 1 + d_τ² = 2 + φ` (`fibonacciTotalDim_sq`). The golden self-similarity
  `φ = 1 + 1/φ` (`fibonacci_self_similar`) is the pentagon/`5`-fold (icosahedral) signature.
* **§B — Ising anyons.** `isingSigmaDim = √2` with `d_σ² = 2` (`ising_fusion_consistency`, from
  `σ×σ = 1 + ψ`), `d_σ > 1` (`ising_nonabelian`), and total `D² = 4` (`isingTotalDim_sq`).
* **§C — the abelian/non-abelian criterion.** `IsNonAbelianAnyon d := 1 < d`; Fibonacci and Ising
  satisfy it, while abelian anyons (bosons/fermions/semions of `ExchangeStatisticsSpectrum`) have
  quantum dimension `1` and fail it (`one_not_nonAbelian`).

The module records the scalar identities used by the fusion and zero-mode arguments.  Full
modular/braiding data (`F`- and `R`-matrices, pentagon/hexagon equations, and universality for
topological quantum computation) is outside this file.

## References

* A. Kitaev, "Anyons in an exactly solved model and beyond", Ann. Phys. 321 (2006) 2 (Fibonacci/Ising
  fusion, quantum dimensions); J. Preskill, lecture notes on topological quantum computation. Reuses
  `ExchangeStatisticsSpectrum` and Mathlib `Real.goldenRatio` (`Real.goldenRatio_sq`, `Real.one_lt_goldenRatio`).


-/

set_option autoImplicit false

open scoped goldenRatio

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NonAbelianAnyons

open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
open Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR


/-- **The Fibonacci quantum dimension** `d_τ = φ` (the golden ratio): the single non-trivial anyon `τ`
of the Fibonacci theory has quantum dimension equal to the golden ratio. -/
noncomputable def fibonacciDim : ℝ := Real.goldenRatio

/-- **Fibonacci fusion consistency** `d_τ² = 1 + d_τ` (Kitaev): from the fusion rule `τ × τ = 1 + τ`,
`d_τ · d_τ = d_1 + d_τ = 1 + d_τ`, so `d_τ` is the golden ratio. -/
lemma fibonacci_fusion_consistency : fibonacciDim ^ 2 = 1 + fibonacciDim := by
  rw [fibonacciDim, Real.goldenRatio_sq]; ring

/-- **Fibonacci anyons are non-abelian** `d_τ > 1`: a quantum dimension greater than one means the
fusion `τ × τ` has several outcomes — non-abelian braiding. -/
lemma fibonacci_nonabelian : 1 < fibonacciDim := Real.one_lt_goldenRatio

/-- **The Fibonacci total quantum dimension** `D² = 1 + d_τ² = 2 + φ`: the sum of squared quantum
dimensions over the two objects `{1, τ}`. -/
lemma fibonacciTotalDim_sq : 1 + fibonacciDim ^ 2 = 2 + fibonacciDim := by
  rw [fibonacci_fusion_consistency]; ring

/-- **Golden self-similarity** `φ = 1 + 1/φ`: the Fibonacci quantum dimension satisfies the continued-
fraction/pentagon relation — the `5`-fold (icosahedral) signature, `φ = 2cos(π/5)`. -/
lemma fibonacci_self_similar : fibonacciDim = 1 + 1 / fibonacciDim := by
  have hφ : fibonacciDim ≠ 0 := by rw [fibonacciDim]; exact Real.goldenRatio_ne_zero
  have h := fibonacci_fusion_consistency
  field_simp
  linarith [h]


/-- **The Ising quantum dimension** `d_σ = √2`: this is the same scalar used by
the repository's Moore-Read/FQHE named-anyon model. -/
noncomputable def isingSigmaDim : ℝ := isingSigmaQuantumDimension

/-- **Ising fusion consistency** `d_σ² = 2` (Kitaev): from `σ × σ = 1 + ψ`, `d_σ² = d_1 + d_ψ = 1 + 1 =
2`. -/
lemma ising_fusion_consistency : isingSigmaDim ^ 2 = 2 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num]
  simpa [isingSigmaDim] using isingSigma_fusion_channels

/-- **Ising anyons are non-abelian** `d_σ > 1`. -/
lemma ising_nonabelian : 1 < isingSigmaDim := by
  simpa [isingSigmaDim] using isingSigma_nonabelian

/-- **The Ising total quantum dimension** `D² = 4` (`D = 2`): the sum over `{1, σ, ψ}` of squared
quantum dimensions, `1 + d_σ² + 1 = 1 + 2 + 1`. -/
lemma isingTotalDim_sq : 1 + isingSigmaDim ^ 2 + 1 = 4 := by
  rw [ising_fusion_consistency]; norm_num

/-- **A non-abelian anyon** has quantum dimension `> 1` — its fusion has multiple channels, so braiding
acts by non-commuting matrices on a degenerate space. -/
def IsNonAbelianAnyon (d : ℝ) : Prop := 1 < d

/-- The local `NonAbelianAnyons` Ising scalar is definitionally the FQHE/CSW
Ising `σ` quantum dimension. -/
lemma isingSigmaDim_eq_fqhe_isingSigmaQuantumDimension :
    isingSigmaDim = isingSigmaQuantumDimension := rfl

/-- The named Moore-Read Ising `σ` anyon model uses the same quantum dimension
as this module's Ising scalar. -/
lemma isingSigma_namedAnyon_quantumDimension :
    (namedAnyonModel NamedAnyon.isingSigma).quantumDimension =
      isingSigmaDim := rfl

/-- The named Moore-Read Ising `σ` anyon model is non-abelian in the local
quantum-dimension criterion. -/
lemma isingSigma_namedAnyon_isNonAbelian :
    IsNonAbelianAnyon
      (namedAnyonModel NamedAnyon.isingSigma).quantumDimension := by
  simpa [IsNonAbelianAnyon, isingSigma_namedAnyon_quantumDimension] using ising_nonabelian

/-- The named Ising `ψ` anyon supplies the fermionic endpoint of the
non-abelian Ising sector. -/
lemma isingPsi_namedAnyon_isFermionic :
    IsFermionic (namedAnyonModel NamedAnyon.isingPsi).exchangePhase := by
  simpa [IsFermionic] using isingPsiAnyonModel_fermion_phase

/-- The named Ising vacuum supplies the bosonic endpoint of the non-abelian
Ising sector. -/
lemma isingVacuum_namedAnyon_isBosonic :
    IsBosonic (namedAnyonModel NamedAnyon.isingVacuum).exchangePhase := by
  simpa [IsBosonic] using isingVacuumAnyonModel_boson_phase

/-- The named Ising `σ` model's quantum dimension satisfies the same fusion
equation as the local Ising scalar. -/
lemma isingSigma_namedAnyon_quantumDimension_sq :
    (namedAnyonModel NamedAnyon.isingSigma).quantumDimension ^ 2 = 1 + 1 := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  simpa [isingSigma_namedAnyon_quantumDimension] using ising_fusion_consistency


/-- **Fibonacci is non-abelian** (quantum dimension `φ > 1`). -/
lemma fibonacci_isNonAbelian : IsNonAbelianAnyon fibonacciDim := fibonacci_nonabelian

/-- **Ising is non-abelian** (quantum dimension `√2 > 1`). -/
lemma ising_isNonAbelian : IsNonAbelianAnyon isingSigmaDim := ising_nonabelian

/-- **Abelian anyons are not non-abelian** — the bosons, fermions, and semions of
`ExchangeStatisticsSpectrum` all have quantum dimension `1`, and `1` is not `> 1`: their fusion has a
unique outcome, braiding by a phase (`ExchangeStatisticsSpectrum.IsAnyonic` is `U(1)`, dimension one). -/
lemma one_not_nonAbelian : ¬ IsNonAbelianAnyon 1 := by
  unfold IsNonAbelianAnyon; norm_num

/-! ## D. Majorana zero-mode parity on point solitons -/

/-- The Hilbert-space dimension obtained by quantizing a pair of identical solitons
with `n` Majorana zero modes on each soliton.  The pair has `2n` Majorana generators,
which quantize to a `2^n`-dimensional Clifford module. -/
def pairMajoranaZeroModeHilbertDim (n : ℕ) : ℕ := 2 ^ n

/-- The named Ising `σ` model has the same two-channel fusion count as the
Majorana pair Hilbert space for one zero mode on each soliton. -/
lemma isingSigma_pairMajoranaHilbertDim_eq_namedFusionCount :
    pairMajoranaZeroModeHilbertDim 1 =
      (namedAnyonModel NamedAnyon.isingSigma).fusionChannelCount := rfl

/-- The one-zero-mode Majorana pair has the same two-state size as the concrete
Kálnay Bose-bilinear CAR carrier, and that carrier is a genuine fermion mode
with an idempotent number operator. -/
lemma kalnayBoseBilinear_links_majoranaPairTwoState :
    pairMajoranaZeroModeHilbertDim 1 = 2
      ∧ IsFermionMode boseBilinear
      ∧ fermionNumber boseBilinear * fermionNumber boseBilinear =
          fermionNumber boseBilinear := by
  exact ⟨rfl, boseBilinear_isFermionMode,
    fermionNumber_idempotent boseBilinear boseBilinear_isFermionMode⟩

/-- If a natural number `d` were a local Hilbert-space dimension for one soliton and
`d^2 = 2^n`, then the Majorana zero-mode count `n` would have to be even. -/
lemma square_eq_pairMajoranaHilbertDim_even {d n : ℕ}
    (h : d ^ 2 = pairMajoranaZeroModeHilbertDim n) : Even n := by
  have hfact := congrArg (fun m : ℕ => m.factorization 2) h
  rw [pairMajoranaZeroModeHilbertDim, Nat.factorization_pow,
    Nat.factorization_pow_self Nat.prime_two] at hfact
  use d.factorization 2
  simpa [two_mul] using hfact.symm

/-- An odd number of Majorana zero modes cannot be assigned an integer local
Hilbert-space dimension whose square gives the two-soliton Hilbert space.  This is
the finite arithmetic version of the paper's `sqrt(2)` obstruction. -/
lemma no_localHilbertDim_of_odd_majorana {d n : ℕ} (hn : Odd n) :
    d ^ 2 ≠ pairMajoranaZeroModeHilbertDim n := by
  intro h
  exact (Nat.not_even_iff_odd.mpr hn) (square_eq_pairMajoranaHilbertDim_even h)

/-- A model exchange eigenvalue for a pair of solitons with `n` Majorana zero modes:
up to a sign `eps` with `eps^2 = 1`, exchange contributes `i^n`. -/
noncomputable def majoranaExchangeEigenvalue (eps : ℂ) (n : ℕ) : ℂ :=
  eps * Complex.I ^ n

/-- The square of `i^n` is `(-1)^n`. -/
lemma complex_I_pow_sq_eq_neg_one_pow (n : ℕ) :
    (Complex.I ^ n) ^ 2 = (-1 : ℂ) ^ n := by
  calc
    (Complex.I ^ n) ^ 2 = (Complex.I ^ 2) ^ n := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (-1 : ℂ) ^ n := by
      rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]

/-- The square of the exchange eigenvalue is the fermion-parity sign `(-1)^n`. -/
lemma majoranaExchangeEigenvalue_sq (eps : ℂ) (n : ℕ) (heps : eps ^ 2 = 1) :
    majoranaExchangeEigenvalue eps n ^ 2 = (-1 : ℂ) ^ n := by
  unfold majoranaExchangeEigenvalue
  rw [mul_pow, heps, one_mul, complex_I_pow_sq_eq_neg_one_pow]

/-- Odd Majorana zero-mode count makes the exchange operator projective of square
`-1`, so it cannot be a genuine `Z2` exchange operator in dimensions whose
two-particle configuration space has fundamental group `Z2`. -/
lemma majoranaExchangeEigenvalue_sq_odd (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Odd n) :
    majoranaExchangeEigenvalue eps n ^ 2 = -1 := by
  rw [majoranaExchangeEigenvalue_sq eps n heps, hn.neg_one_pow]

/-- Even Majorana zero-mode count gives a genuine order-two exchange square. -/
lemma majoranaExchangeEigenvalue_sq_even (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Even n) :
    majoranaExchangeEigenvalue eps n ^ 2 = 1 := by
  rw [majoranaExchangeEigenvalue_sq eps n heps, hn.neg_one_pow]

/-- The local Majorana exchange square is the repository's abstract exchange
monodromy applied to the Majorana exchange phase. -/
lemma majoranaExchangeMonodromy_eq_exchangeStatistics (eps : ℂ) (n : ℕ)
    (heps : eps ^ 2 = 1) :
    monodromy (majoranaExchangeEigenvalue eps n) = (-1 : ℂ) ^ n := by
  simpa [monodromy] using majoranaExchangeEigenvalue_sq eps n heps

/-- Odd Majorana zero-mode count gives fermionic monodromy in the repository's
exchange-statistics spectrum. -/
lemma majoranaExchangeMonodromy_odd_isFermionic (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Odd n) :
    IsFermionic (monodromy (majoranaExchangeEigenvalue eps n)) := by
  unfold IsFermionic
  rw [majoranaExchangeMonodromy_eq_exchangeStatistics eps n heps, hn.neg_one_pow]

/-- Even Majorana zero-mode count gives bosonic monodromy in the repository's
exchange-statistics spectrum. -/
lemma majoranaExchangeMonodromy_even_isBosonic (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Even n) :
    IsBosonic (monodromy (majoranaExchangeEigenvalue eps n)) := by
  unfold IsBosonic
  rw [majoranaExchangeMonodromy_eq_exchangeStatistics eps n heps, hn.neg_one_pow]

/-- Odd Majorana zero-mode monodromy agrees with the named Ising `ψ` fermion
sector from the FQHE/CSW anyon taxonomy. -/
lemma majoranaExchangeMonodromy_odd_eq_isingPsiExchange (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Odd n) :
    monodromy (majoranaExchangeEigenvalue eps n) =
      (namedAnyonModel NamedAnyon.isingPsi).exchangePhase := by
  rw [majoranaExchangeMonodromy_eq_exchangeStatistics eps n heps, hn.neg_one_pow]
  exact isingPsiAnyonModel_fermion_phase.symm

/-- Even Majorana zero-mode monodromy agrees with the named Ising vacuum sector
from the FQHE/CSW anyon taxonomy. -/
lemma majoranaExchangeMonodromy_even_eq_isingVacuumExchange (eps : ℂ) {n : ℕ}
    (heps : eps ^ 2 = 1) (hn : Even n) :
    monodromy (majoranaExchangeEigenvalue eps n) =
      (namedAnyonModel NamedAnyon.isingVacuum).exchangePhase := by
  rw [majoranaExchangeMonodromy_eq_exchangeStatistics eps n heps, hn.neg_one_pow]
  exact isingVacuumAnyonModel_boson_phase.symm

/-- Odd Majorana zero-mode monodromy agrees with any Wilson line whose
conformal weight is `1/2`, using the Hopf/Wilson ribbon bridge rather than a
separate fermion-sign calculation. -/
lemma majoranaExchangeMonodromy_odd_eq_hopfWilsonFermionSpin
    (eps : ℂ) {n : ℕ} (heps : eps ^ 2 = 1) (hn : Odd n)
    (k : ℕ) (hk : 0 < k) (a : Fin k) (h : (a.val : ℝ) ^ 2 = k) :
    monodromy (majoranaExchangeEigenvalue eps n) = wilsonTopologicalSpin k a := by
  have hw := hopf_ribbon_wilson_fermion_sign k hk a h
  calc
    monodromy (majoranaExchangeEigenvalue eps n) = -1 := by
      rw [majoranaExchangeMonodromy_eq_exchangeStatistics eps n heps, hn.neg_one_pow]
    _ = Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist.ribbonTwist
        (1 / 2) := hw.1.symm
    _ = wilsonTopologicalSpin k a := hw.2.symm

/-- The parity condition from Sato-Tachikawa-Watari for point-like dynamical
solitons: in spatial dimension at most two, odd Majorana zero modes can occur;
in spatial dimension at least three, the zero-mode count must be even. -/
def PointSolitonMajoranaParityAllowed (spatialDim zeroModes : ℕ) : Prop :=
  spatialDim ≤ 2 ∨ Even zeroModes

/-- In spatial dimension at most two, the parity obstruction does not rule out an
odd Majorana zero mode on a point-like soliton. -/
lemma pointSolitonMajoranaParityAllowed_of_lowDim {spatialDim zeroModes : ℕ}
    (hdim : spatialDim ≤ 2) :
    PointSolitonMajoranaParityAllowed spatialDim zeroModes :=
  Or.inl hdim

/-- In spatial dimension at least three, the parity condition is exactly evenness
of the Majorana zero-mode count. -/
lemma pointSolitonMajoranaParityAllowed_iff_even_of_highDim
    {spatialDim zeroModes : ℕ} (hdim : 3 ≤ spatialDim) :
    PointSolitonMajoranaParityAllowed spatialDim zeroModes ↔ Even zeroModes := by
  constructor
  · intro h
    rcases h with hlow | heven
    · exact False.elim ((not_le_of_gt (lt_of_lt_of_le (by norm_num : 2 < 3) hdim)) hlow)
    · exact heven
  · exact Or.inr

/-- In `3+1` spacetime dimensions and above, an odd Majorana zero-mode count is
excluded for a dynamical point-like soliton by the exchange-order obstruction. -/
lemma odd_majorana_highDim_not_allowed {spatialDim zeroModes : ℕ}
    (hdim : 3 ≤ spatialDim) (hodd : Odd zeroModes) :
    ¬ PointSolitonMajoranaParityAllowed spatialDim zeroModes := by
  intro h
  exact (Nat.not_even_iff_odd.mpr hodd)
    ((pointSolitonMajoranaParityAllowed_iff_even_of_highDim hdim).mp h)

/-- The `2+1`-dimensional Ising/Majorana vortex case with one zero mode is not
excluded by the high-dimensional parity obstruction. -/
lemma twoSpatialDimensions_allow_singleMajoranaZeroMode :
    PointSolitonMajoranaParityAllowed 2 1 :=
  pointSolitonMajoranaParityAllowed_of_lowDim (by norm_num)

/-- The `1+1`-dimensional kink/domain-wall case with one Majorana zero mode is
not excluded by the high-dimensional point-soliton obstruction. -/
lemma oneSpatialDimension_allow_singleMajoranaZeroMode :
    PointSolitonMajoranaParityAllowed 1 1 :=
  pointSolitonMajoranaParityAllowed_of_lowDim (by norm_num)

/-- Point-soliton sectors relevant to the paper's discussion.  The high-dimensional
parity obstruction applies to identical dynamical point solitons without extra
orientational moduli; static backgrounds and orientationally enriched solitons are
separate sectors. -/
inductive MajoranaPointSolitonSector where
  | dynamicalIdenticalPoint
  | staticExternalBackground
  | orientedDynamicalPoint
deriving DecidableEq, Repr

/-- The sector and dimension hypotheses under which the exchange-statistics
parity obstruction applies. -/
def MajoranaPointSolitonSector.statisticsConstraintApplies
    (sector : MajoranaPointSolitonSector) (spatialDim : ℕ) : Prop :=
  sector = MajoranaPointSolitonSector.dynamicalIdenticalPoint ∧ 3 ≤ spatialDim

/-- In a sector where the exchange-statistics obstruction applies, the Majorana
zero-mode count must be even. -/
def MajoranaPointSolitonSector.parityAllowed
    (sector : MajoranaPointSolitonSector) (spatialDim zeroModes : ℕ) : Prop :=
  sector.statisticsConstraintApplies spatialDim → Even zeroModes

/-- For identical dynamical point solitons in spatial dimension at least three,
the sector-level condition is exactly evenness of the zero-mode count. -/
lemma dynamicalIdenticalPoint_parityAllowed_iff_even_of_highDim
    {spatialDim zeroModes : ℕ} (hdim : 3 ≤ spatialDim) :
    MajoranaPointSolitonSector.parityAllowed
      MajoranaPointSolitonSector.dynamicalIdenticalPoint spatialDim zeroModes
        ↔ Even zeroModes := by
  constructor
  · intro h
    exact h ⟨rfl, hdim⟩
  · intro heven _
    exact heven

/-- Static external backgrounds are outside the sector to which the dynamical
identical-particle exchange obstruction applies. -/
lemma staticExternalBackground_not_statisticsConstraintApplies
    (spatialDim : ℕ) :
    ¬ MajoranaPointSolitonSector.statisticsConstraintApplies
      MajoranaPointSolitonSector.staticExternalBackground spatialDim := by
  intro h
  cases h.1

/-- Dynamical solitons with additional orientational moduli are outside the
bare `S^(d-1)/Z2` point-particle sector used by the obstruction. -/
lemma orientedDynamicalPoint_not_statisticsConstraintApplies
    (spatialDim : ℕ) :
    ¬ MajoranaPointSolitonSector.statisticsConstraintApplies
      MajoranaPointSolitonSector.orientedDynamicalPoint spatialDim := by
  intro h
  cases h.1

/-! ## E. Field-theory and M-theory parity checks -/

/-- In the `3+1`-dimensional `SU(2)` doublet monopole example, the number of
Majorana zero modes equals the number of Weyl doublets. -/
def su2MonopoleMajoranaZeroModes (weylDoublets : ℕ) : ℕ := weylDoublets

/-- The `SU(2)` monopole example is allowed in `3+1` dimensions exactly when the
number of Weyl doublets is even, matching Witten's `SU(2)` anomaly parity. -/
lemma su2Monopole_allowed_iff_even_doublets (weylDoublets : ℕ) :
    PointSolitonMajoranaParityAllowed 3 (su2MonopoleMajoranaZeroModes weylDoublets)
      ↔ Even weylDoublets := by
  simpa [su2MonopoleMajoranaZeroModes]
    using pointSolitonMajoranaParityAllowed_iff_even_of_highDim
      (spatialDim := 3) (zeroModes := weylDoublets) (by norm_num)

/-- In the `4+1`-dimensional `SU(2)` instanton-soliton example, the number of
Majorana zero modes equals the number of symplectic-Majorana doublets. -/
def su2InstantonMajoranaZeroModes (doublets : ℕ) : ℕ := doublets

/-- The `4+1`-dimensional instanton-soliton example is allowed exactly when the
number of doublets is even, the parity counterpart of the `π₅(SU(2)) = Z2`
global anomaly condition. -/
lemma su2Instanton_allowed_iff_even_doublets (doublets : ℕ) :
    PointSolitonMajoranaParityAllowed 4 (su2InstantonMajoranaZeroModes doublets)
      ↔ Even doublets := by
  simpa [su2InstantonMajoranaZeroModes]
    using pointSolitonMajoranaParityAllowed_iff_even_of_highDim
      (spatialDim := 4) (zeroModes := doublets) (by norm_num)

/-- Periodic compactification of a string-like soliton with `N` Majorana-Weyl
zero modes produces a point-like soliton with the same zero-mode count. -/
def compactifiedStringMajoranaZeroModes (majoranaWeylModes : ℕ) : ℕ :=
  majoranaWeylModes

/-- The point-soliton parity condition induced by compactifying a string-like
soliton around a periodic circle. -/
def StringLikeMajoranaWeylParityAllowedAfterCompactification
    (spatialDim majoranaWeylModes : ℕ) : Prop :=
  PointSolitonMajoranaParityAllowed spatialDim
    (compactifiedStringMajoranaZeroModes majoranaWeylModes)

/-- After periodic compactification to a point soliton in spatial dimension at
least three, the string-like Majorana-Weyl parity condition is exactly evenness. -/
lemma stringLikeMajoranaWeylParityAllowedAfterCompactification_iff_even_of_highDim
    {spatialDim majoranaWeylModes : ℕ} (hdim : 3 ≤ spatialDim) :
    StringLikeMajoranaWeylParityAllowedAfterCompactification
        spatialDim majoranaWeylModes ↔
      Even majoranaWeylModes := by
  simpa [StringLikeMajoranaWeylParityAllowedAfterCompactification,
    compactifiedStringMajoranaZeroModes]
    using pointSolitonMajoranaParityAllowed_iff_even_of_highDim
      (spatialDim := spatialDim) (zeroModes := majoranaWeylModes) hdim

/-- An odd number of Majorana-Weyl zero modes on a string-like soliton is
excluded after periodic compactification to a high-dimensional point soliton. -/
lemma odd_stringLikeMajoranaWeyl_highDim_not_allowed_afterCompactification
    {spatialDim majoranaWeylModes : ℕ}
    (hdim : 3 ≤ spatialDim) (hodd : Odd majoranaWeylModes) :
    ¬ StringLikeMajoranaWeylParityAllowedAfterCompactification
      spatialDim majoranaWeylModes := by
  intro h
  exact (Nat.not_even_iff_odd.mpr hodd)
    ((stringLikeMajoranaWeylParityAllowedAfterCompactification_iff_even_of_highDim
      hdim).mp h)

/-- In the broken `4+1`-dimensional `SU(2)` example, the monopole string has one
Majorana-Weyl zero mode for each symplectic-Majorana doublet. -/
def su2BrokenMonopoleStringMajoranaWeylModes (doublets : ℕ) : ℕ := doublets

/-- Wrapping the `4+1`-dimensional monopole string on a periodic circle reduces
the parity condition to evenness of the doublet count. -/
lemma su2BrokenMonopoleString_compactified_allowed_iff_even_doublets
    (doublets : ℕ) :
    StringLikeMajoranaWeylParityAllowedAfterCompactification 3
        (su2BrokenMonopoleStringMajoranaWeylModes doublets) ↔
      Even doublets := by
  simpa [su2BrokenMonopoleStringMajoranaWeylModes]
    using
      stringLikeMajoranaWeylParityAllowedAfterCompactification_iff_even_of_highDim
        (spatialDim := 3) (majoranaWeylModes := doublets) (by norm_num)

/-- The M5-brane worldsheet central-charge difference after integrating the anomaly
polynomial over the wrapped four-cycle, expressed using the integer
`∫_P i^*p1(TM)/4` supplied by shifted flux quantization and the M5 Bianchi identity. -/
noncomputable def m5CentralChargeDifference (p1Over4Integral : ℤ) : ℚ :=
  -p1Over4Integral

/-- A rational number is an integer plus one half.  In the paper this is the parity
sector that would correspond to an odd number of Majorana-Weyl fermions on the
string-like soliton. -/
def IsHalfIntegerShift (q : ℚ) : Prop :=
  ∃ k : ℤ, q = (k : ℚ) + 1 / 2

/-- No integer rational number is an integer plus one half. -/
lemma intCast_ne_intCast_add_half (z k : ℤ) :
    (z : ℚ) ≠ (k : ℚ) + 1 / 2 := by
  intro h
  have hrat : ((2 * z : ℤ) : ℚ) = ((2 * k + 1 : ℤ) : ℚ) := by
    norm_num
    linarith
  have hint : (2 * z : ℤ) = 2 * k + 1 := by
    exact_mod_cast hrat
  omega

/-- The contribution of `N` chiral Majorana-Weyl fermions to the worldsheet
central-charge difference, in units where one real chiral fermion contributes
`1/2`. -/
def majoranaWeylCentralChargeShift (N : ℕ) : ℚ :=
  (N : ℚ) / 2

/-- An even number of Majorana-Weyl fermions gives an integer central-charge
difference. -/
lemma majoranaWeylCentralChargeShift_even_isInteger {N : ℕ} (hN : Even N) :
    ∃ k : ℤ, majoranaWeylCentralChargeShift N = k := by
  rcases hN with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [majoranaWeylCentralChargeShift, hk]
  norm_num

/-- An odd number of Majorana-Weyl fermions gives an integer-plus-one-half
central-charge difference. -/
lemma majoranaWeylCentralChargeShift_odd_isHalfIntegerShift {N : ℕ}
    (hN : Odd N) :
    IsHalfIntegerShift (majoranaWeylCentralChargeShift N) := by
  rcases hN with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [majoranaWeylCentralChargeShift, hk]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- Even Majorana-Weyl count is disjoint from the integer-plus-one-half
central-charge sector. -/
lemma majoranaWeylCentralChargeShift_even_not_halfIntegerShift {N : ℕ}
    (hN : Even N) :
    ¬ IsHalfIntegerShift (majoranaWeylCentralChargeShift N) := by
  rcases majoranaWeylCentralChargeShift_even_isInteger hN with ⟨z, hz⟩
  intro h
  rcases h with ⟨k, hk⟩
  exact intCast_ne_intCast_add_half z k (by
    rw [hz] at hk
    exact hk)

/-- Odd Majorana-Weyl count cannot have an integer central-charge difference. -/
lemma majoranaWeylCentralChargeShift_odd_not_integer {N : ℕ} (hN : Odd N) :
    ¬ ∃ k : ℤ, majoranaWeylCentralChargeShift N = k := by
  intro h
  rcases h with ⟨z, hz⟩
  rcases majoranaWeylCentralChargeShift_odd_isHalfIntegerShift hN with ⟨k, hk⟩
  exact intCast_ne_intCast_add_half z k (by
    rw [hz] at hk
    exact hk)

/-- The paper's central-charge parity criterion: the Majorana-Weyl contribution
is integer-valued exactly for an even number of real chiral fermions. -/
lemma majoranaWeylCentralChargeShift_integer_iff_even (N : ℕ) :
    (∃ k : ℤ, majoranaWeylCentralChargeShift N = k) ↔ Even N := by
  constructor
  · intro h
    by_contra hne
    exact majoranaWeylCentralChargeShift_odd_not_integer
      (Nat.not_even_iff_odd.mp hne) h
  · exact majoranaWeylCentralChargeShift_even_isInteger

/-- The M5-brane central-charge difference is an integer once the pulled-back
`p1/4` class is integral. -/
lemma m5CentralChargeDifference_isInteger (p1Over4Integral : ℤ) :
    ∃ k : ℤ, m5CentralChargeDifference p1Over4Integral = k :=
  ⟨-p1Over4Integral, by simp [m5CentralChargeDifference]⟩

/-- Therefore the M5-brane central-charge difference is not in the
integer-plus-one-half sector.  This formalizes the paper's parity conclusion from
Eqs. (8)-(11). -/
lemma m5CentralChargeDifference_not_halfIntegerShift (p1Over4Integral : ℤ) :
    ¬ IsHalfIntegerShift (m5CentralChargeDifference p1Over4Integral) := by
  intro h
  rcases h with ⟨k, hk⟩
  exact intCast_ne_intCast_add_half (-p1Over4Integral) k (by
    simpa [m5CentralChargeDifference] using hk)

/-- If an M5 wrapped-brane worldsheet central-charge difference is identified
with the shift produced by `N` Majorana-Weyl zero modes, shifted flux
quantization forces `N` to be even. -/
lemma m5MajoranaWeylZeroModes_even_of_centralCharge
    {N : ℕ} {p1Over4Integral : ℤ}
    (hcc :
      majoranaWeylCentralChargeShift N =
        m5CentralChargeDifference p1Over4Integral) :
    Even N := by
  by_contra hne
  have hodd : Odd N := Nat.not_even_iff_odd.mp hne
  have hhalf := majoranaWeylCentralChargeShift_odd_isHalfIntegerShift hodd
  rw [hcc] at hhalf
  exact m5CentralChargeDifference_not_halfIntegerShift p1Over4Integral hhalf

/-- Combining periodic compactification with the M5 central-charge formula: if
the Majorana-Weyl contribution matches the integral M5 expression, the resulting
point-like soliton satisfies the high-dimensional parity condition. -/
lemma m5String_compactified_parityAllowed_of_centralCharge
    {spatialDim N : ℕ} {p1Over4Integral : ℤ}
    (hdim : 3 ≤ spatialDim)
    (hcc :
      majoranaWeylCentralChargeShift N =
        m5CentralChargeDifference p1Over4Integral) :
    StringLikeMajoranaWeylParityAllowedAfterCompactification spatialDim N := by
  rw [stringLikeMajoranaWeylParityAllowedAfterCompactification_iff_even_of_highDim hdim]
  exact m5MajoranaWeylZeroModes_even_of_centralCharge hcc

/-! ## F. Seiberg-Witten monodromy integrality check -/

/-- The lower-left entry `4 - n/2` of the Seiberg-Witten monodromy matrix for
`4d N = 2` `SU(2)` gauge theory with `n` half-hypermultiplet doublets. -/
def seibergWittenMonodromyLowerLeft (halfHypermultiplets : ℕ) : ℚ :=
  4 - (halfHypermultiplets : ℚ) / 2

/-- For an even number of half-hypermultiplet doublets, the lower-left
Seiberg-Witten monodromy entry is integer-valued. -/
lemma seibergWittenMonodromyLowerLeft_even_isInteger {n : ℕ} (hn : Even n) :
    ∃ k : ℤ, seibergWittenMonodromyLowerLeft n = k := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(4 : ℤ) - (k : ℤ), ?_⟩
  rw [seibergWittenMonodromyLowerLeft, hk]
  norm_num

/-- For an odd number of half-hypermultiplet doublets, the lower-left
Seiberg-Witten monodromy entry lies in the integer-plus-one-half sector. -/
lemma seibergWittenMonodromyLowerLeft_odd_isHalfIntegerShift {n : ℕ}
    (hn : Odd n) :
    IsHalfIntegerShift (seibergWittenMonodromyLowerLeft n) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(3 : ℤ) - (k : ℤ), ?_⟩
  rw [seibergWittenMonodromyLowerLeft, hk]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- For an odd number of half-hypermultiplet doublets, the Seiberg-Witten
monodromy matrix is not integer-valued. -/
lemma seibergWittenMonodromyLowerLeft_odd_not_integer {n : ℕ} (hn : Odd n) :
    ¬ ∃ k : ℤ, seibergWittenMonodromyLowerLeft n = k := by
  intro h
  rcases h with ⟨z, hz⟩
  rcases seibergWittenMonodromyLowerLeft_odd_isHalfIntegerShift hn with ⟨k, hk⟩
  exact intCast_ne_intCast_add_half z k (by
    rw [hz] at hk
    exact hk)

/-- The Seiberg-Witten monodromy matrix is integer-valued exactly when the
number of half-hypermultiplet doublets is even. -/
lemma seibergWittenMonodromyLowerLeft_integer_iff_even (n : ℕ) :
    (∃ k : ℤ, seibergWittenMonodromyLowerLeft n = k) ↔ Even n := by
  constructor
  · intro h
    by_contra hne
    exact seibergWittenMonodromyLowerLeft_odd_not_integer
      (Nat.not_even_iff_odd.mp hne) h
  · exact seibergWittenMonodromyLowerLeft_even_isInteger

end Physlib.QuantumMechanics.ComplexAction.NonAbelianAnyons
