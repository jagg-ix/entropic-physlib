/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain
public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
public import Mathlib.MeasureTheory.Function.Holder
meta import Zil

/-!
# The conclusive non-relativistic limit: Einstein/Dirac kinetic energy `→ p²/2m`

The chain `ComplexEinstein.DiracSchrodingerChain` reduces the complex Einstein dispersion to the Dirac
eigenvalue problem (exact) and factors it to the kinetic relation `(E − mc²)(E + mc²) = (cp)²`. The
**Schrödinger** end of that chain was only a point-identity there. This file proves the *conclusive*
statement: the relativistic kinetic energy converges, as a genuine limit, to the Schrödinger kinetic
energy.

## The limit

For a physical mass `m > 0` the relativistic kinetic energy is, exactly (`einsteinKinetic_eq`),

  `E(c) − mc² = p² / (√(m² + p²/c²) + m)`   (`E(c) = √((mc²)² + (cp)²)`),

and therefore (`einsteinKinetic_tendsto_schrodinger`)

  `lim_{c→∞} (E(c) − mc²) = p²/(2m)`.

This is the honest non-relativistic limit `|p| ≪ mc`: the rationalized kinetic energy
`p²/(√(m² + p²/c²) + m)` has the denominator `→ 2m`, so the kinetic energy `→ p²/2m` — *exactly* the
free Schrödinger kinetic energy, recovered as a limit (not an algebraic substitution at a point).

## The free Schrödinger equation at the limit energy

With the limit energy `E_S = p²/2m`, the mode `Ψ(t) = e^{−iE_S t/ℏ}` solves the free-particle
Schrödinger equation `iℏ ∂_t Ψ = (p²/2m) Ψ` (`schrodinger_free_mode`, via `greenKernel_satisfies_tdse`).
So the Dirac positive-energy mode, in the non-relativistic limit, *is* the free Schrödinger mode.

## Klein–Gordon–Maxwell to Schrödinger–Poisson

The final sections add the exact Fourier-mode layer used by the
Bechouche–Mauser–Selberg nonrelativistic limit: the minimally coupled
positive/negative-frequency split, its inverse reconstruction, removal of the
two rest-energy phases, invariance of the signed Poisson source, and
continuity of that source when the two dephased sectors and the oscillatory
remainder converge.  The paper-specific Sobolev/Gronwall stability step is
packaged in `EntropicDynamicsEvolutionSchrodingerEhrenfest` so it can reuse the
existing Coulomb modulated-energy infrastructure.

## What this adds over the chain file

The chain file's `dirac_kinetic_nonrel_eq_schrodinger` was the value of the kinetic energy *at*
`E + mc² = 2mc²` — an identity at one point, with the "limit" only asserted in prose. Here the limit
`c → ∞` is proved (`Filter.Tendsto`), and the resulting energy drives the genuine free Schrödinger
TDSE. This is the conclusive form of "Einstein ⟹ Dirac ⟹ Schrödinger".

## References

* The non-relativistic limit `√(m²c⁴ + c²p²) − mc² → p²/2m`. This development:
  `ComplexEinstein.DiracSchrodingerChain`, `ComplexEinstein.FullEinsteinDispersionConsistency`.
* P. Bechouche, N. J. Mauser, S. Selberg, *Nonrelativistic Limit of
  Klein–Gordon–Maxwell to Schrödinger–Poisson* (bibliographic metadata and the
  mathematical correspondence must be independently verified by the human
  contributor, as required by `AI-POLICY.md`).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory
open scoped FourierTransform ENNReal NNReal SchwartzMap
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.Dirac.ConfinedPhotonDiracDispersion
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.DiracSchrodingerChain
open Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit


/-- **The exact relativistic kinetic energy, rationalized.** For `m > 0`, `c > 0`,

  `E(c) − mc² = p² / (√(m² + p²/c²) + m)`,

with `E(c) = √((mc²)² + (cp)²)`. (Rationalizing `√(m²c⁴ + c²p²) − mc²`; the denominator is manifestly
positive and has a finite `c → ∞` limit, unlike the difference of the two diverging terms.) -/
lemma einsteinKinetic_eq (m c p : ℝ) (hm : 0 < m) (hc : 0 < c) :
    einsteinEnergy m c p - m * c ^ 2
      = p ^ 2 / (Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hEnn : 0 ≤ einsteinEnergy m c p := photonDispersion_nonneg _ _ _
  have hEsq : einsteinEnergy m c p ^ 2 = (m * c ^ 2) ^ 2 + (c * p) ^ 2 := einsteinEnergy_sq m c p
  -- `√(m² + p²/c²) = E/c²`
  have hsqrt : Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) = einsteinEnergy m c p / c ^ 2 := by
    have hq : 0 ≤ einsteinEnergy m c p / c ^ 2 := div_nonneg hEnn hc2.le
    have hsq : (einsteinEnergy m c p / c ^ 2) ^ 2 = m ^ 2 + p ^ 2 / c ^ 2 := by
      rw [div_pow, hEsq]; field_simp
    rw [← hsq, Real.sqrt_sq hq]
  have hden : 0 < einsteinEnergy m c p / c ^ 2 + m := add_pos_of_nonneg_of_pos
    (div_nonneg hEnn hc2.le) hm
  rw [hsqrt, eq_div_iff (ne_of_gt hden)]
  have hexp : (einsteinEnergy m c p - m * c ^ 2) * (einsteinEnergy m c p / c ^ 2 + m)
      = (einsteinEnergy m c p ^ 2 - (m * c ^ 2) ^ 2) / c ^ 2 := by
    field_simp; ring
  rw [hexp, hEsq]; field_simp; ring


/-- **The relativistic kinetic energy converges to the Schrödinger kinetic energy.** For `m > 0`,

  `lim_{c→∞} (E(c) − mc²) = p²/(2m)`,

a genuine limit (`Filter.Tendsto`), not an evaluation at a point. The rationalized kinetic energy
`p²/(√(m² + p²/c²) + m)` has denominator `→ 2m`, so the kinetic energy `→ p²/2m`. -/
lemma einsteinKinetic_tendsto_schrodinger (m p : ℝ) (hm : 0 < m) :
    Tendsto (fun c => einsteinEnergy m c p - m * c ^ 2) atTop (𝓝 (p ^ 2 / (2 * m))) := by
  have heq : (fun c => einsteinEnergy m c p - m * c ^ 2)
      =ᶠ[atTop] fun c => p ^ 2 / (Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact einsteinKinetic_eq m c p hm hc
  rw [tendsto_congr' heq]
  have h0 : Tendsto (fun c : ℝ => p ^ 2 / c ^ 2) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num))
  have hin : Tendsto (fun c : ℝ => m ^ 2 + p ^ 2 / c ^ 2) atTop (𝓝 (m ^ 2)) := by
    simpa using tendsto_const_nhds.add h0
  have hsq : Tendsto (fun c : ℝ => Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2)) atTop (𝓝 m) := by
    have hsqrtLimit := hin.sqrt
    simpa [Real.sqrt_sq hm.le] using hsqrtLimit
  have hden : Tendsto (fun c : ℝ => Real.sqrt (m ^ 2 + p ^ 2 / c ^ 2) + m) atTop (𝓝 (2 * m)) := by
    have hdenLimit := hsq.add (tendsto_const_nhds (x := m))
    simpa [show m + m = 2 * m by ring] using hdenLimit
  have h2m : (2 * m) ≠ 0 := ne_of_gt (mul_pos two_pos hm)
  exact tendsto_const_nhds.div hden h2m


/-- **The non-relativistic mode solves the free-particle Schrödinger equation.** With the limit energy
`E_S = p²/2m`, the mode `Ψ(t) = e^{−iE_S t/ℏ}` solves `iℏ ∂_t Ψ = (p²/2m) Ψ` — the genuine free
Schrödinger TDSE (not the relativistic energy). So the Dirac positive-energy mode reduces, in the
non-relativistic limit, to the free Schrödinger mode. -/
lemma schrodinger_free_mode (m p ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (Complex.I * (ℏ : ℂ))
        * deriv (fun s : ℝ => greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ s) t
      = ((p ^ 2 / (2 * m) : ℝ) : ℂ) * greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ t :=
  greenKernel_satisfies_tdse _ ℏ t hℏ


/-- **Complex Einstein ⟹ Dirac ⟹ Schrödinger, conclusively.** For a physical mass `m > 0`, speed
`c > 0`, momentum `p`, and `ℏ ≠ 0`:

* **(Einstein ⟹ Dirac)** the full-Einstein energy `E` is an eigenvalue of the Dirac Hamiltonian,
  `det(E·1 − H) = 0`;
* **(exact kinetic)** `E − mc² = (cp)²/(E + mc²)` — the exact relativistic kinetic energy;
* **(⟹ Schrödinger, as a limit)** `lim_{c→∞} (E(c) − mc²) = p²/2m` — the kinetic energy converges to
  the Schrödinger kinetic energy (a genuine `Tendsto`);
* **(free Schrödinger TDSE)** the mode `e^{−i(p²/2m)t/ℏ}` solves `iℏ ∂_t Ψ = (p²/2m) Ψ`.

The non-relativistic limit is proved, not asserted — the conclusive form of the chain. -/
lemma complexEinstein_dirac_schrodinger_conclusive (m c p : ℝ) (hm : 0 < m) (hc : 0 < c)
    (ℏ t : ℝ) (hℏ : ℏ ≠ 0) :
    (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          - diracHamiltonian (m * c ^ 2) (c * p)).det = 0
      ∧ einsteinEnergy m c p - m * c ^ 2
          = (c * p) ^ 2 / (einsteinEnergy m c p + m * c ^ 2)
      ∧ Tendsto (fun c' => einsteinEnergy m c' p - m * c' ^ 2) atTop (𝓝 (p ^ 2 / (2 * m)))
      ∧ (Complex.I * (ℏ : ℂ))
            * deriv (fun s : ℝ => greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ s) t
          = ((p ^ 2 / (2 * m) : ℝ) : ℂ) * greenKernel ((p ^ 2 / (2 * m) : ℝ) : ℂ) ℏ t := by
  have hEnn : 0 ≤ einsteinEnergy m c p := photonDispersion_nonneg _ _ _
  have hdirac : (einsteinEnergy m c p • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      - diracHamiltonian (m * c ^ 2) (c * p)).det = 0 :=
    fullEinstein_implies_dirac (m * c ^ 2) c p (einsteinEnergy m c p) (einstein_fullDispersion m c p)
  have hEΔ : einsteinEnergy m c p + m * c ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hEnn (mul_pos hm (pow_pos hc 2)))
  exact ⟨hdirac,
    dirac_kinetic_exact (m * c ^ 2) c p (einsteinEnergy m c p) hEΔ hdirac,
    einsteinKinetic_tendsto_schrodinger m p hm,
    schrodinger_free_mode m p ℏ t hℏ⟩

/-! # A. Klein–Gordon–Maxwell frequency splitting -/

/-- The minimally coupled temporal datum `i ∂ₜφ + A₀ φ` appearing in the
Bechouche–Mauser–Selberg positive/negative-frequency decomposition.  This is
the value of the covariant temporal expression at one Fourier mode. -/
def kgmCovariantTemporalDatum (φ dtφ A₀ : ℂ) : ℂ :=
  Complex.I * dtφ + A₀ * φ

/-- The positive-frequency component
`φ₊ = (φ + E⁻¹(i∂ₜφ + A₀φ))/2` at one Fourier mode.  In the continuum
equation, `E⁻¹` is the Fourier multiplier with symbol
`(c⁴ + c²|ξ|²)⁻¹/²`; here `energy` is its nonzero scalar symbol. -/
def kgmPositiveFrequencyMode (energy : ℝ) (φ dtφ A₀ : ℂ) : ℂ :=
  (φ + (energy : ℂ)⁻¹ * kgmCovariantTemporalDatum φ dtφ A₀) / 2

/-- The negative-frequency component
`φ₋ = (φ - E⁻¹(i∂ₜφ + A₀φ))/2` at one Fourier mode. -/
def kgmNegativeFrequencyMode (energy : ℝ) (φ dtφ A₀ : ℂ) : ℂ :=
  (φ - (energy : ℂ)⁻¹ * kgmCovariantTemporalDatum φ dtφ A₀) / 2

/-- **Exact reconstruction from the two KGM frequency sectors.**  The
minimally coupled split loses no scalar-field data: `φ₊ + φ₋ = φ`. -/
lemma kgmFrequencyMode_add (energy : ℝ) (φ dtφ A₀ : ℂ) :
    kgmPositiveFrequencyMode energy φ dtφ A₀ +
        kgmNegativeFrequencyMode energy φ dtφ A₀ = φ := by
  unfold kgmPositiveFrequencyMode kgmNegativeFrequencyMode
  ring

/-- **The frequency-sector difference recovers the covariant temporal
datum.**  Multiplication by the nonzero energy symbol inverts the split:
`E(φ₊ - φ₋) = i∂ₜφ + A₀φ`. -/
lemma energy_mul_kgmFrequencyMode_sub (energy : ℝ) (φ dtφ A₀ : ℂ)
    (henergy : energy ≠ 0) :
    (energy : ℂ) *
        (kgmPositiveFrequencyMode energy φ dtφ A₀ -
          kgmNegativeFrequencyMode energy φ dtφ A₀) =
      kgmCovariantTemporalDatum φ dtφ A₀ := by
  have henergyC : (energy : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr henergy
  unfold kgmPositiveFrequencyMode kgmNegativeFrequencyMode
  field_simp
  ring

/-! # B. Rest-energy dephasing and the Schrödinger–Poisson source -/

/-- Remove the positive-frequency rest-energy oscillation by multiplying by
`exp(i t c²)`, as in `ψ₊ᶜ = exp(i t c²) φ₊ᶜ`. -/
def kgmDephasePositive (c t : ℝ) (φPlus : ℂ) : ℂ :=
  Complex.exp (((c ^ 2 * t : ℝ) : ℂ) * Complex.I) * φPlus

/-- Remove the negative-frequency rest-energy oscillation by multiplying by
`exp(-i t c²)`, as in `ψ₋ᶜ = exp(-i t c²) φ₋ᶜ`. -/
def kgmDephaseNegative (c t : ℝ) (φMinus : ℂ) : ℂ :=
  Complex.exp (((-(c ^ 2 * t) : ℝ) : ℂ) * Complex.I) * φMinus

/-- The signed matter density sourcing the limiting Poisson equation:
`ρ = |ψ₊|² - |ψ₋|²`. -/
def schrodingerPoissonChargeDensity (ψPlus ψMinus : ℂ) : ℝ :=
  Complex.normSq ψPlus - Complex.normSq ψMinus

/-- Rest-energy dephasing preserves the positive-sector density. -/
@[simp] lemma normSq_kgmDephasePositive (c t : ℝ) (φPlus : ℂ) :
    Complex.normSq (kgmDephasePositive c t φPlus) =
      Complex.normSq φPlus := by
  rw [kgmDephasePositive, map_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- Rest-energy dephasing preserves the negative-sector density. -/
@[simp] lemma normSq_kgmDephaseNegative (c t : ℝ) (φMinus : ℂ) :
    Complex.normSq (kgmDephaseNegative c t φMinus) =
      Complex.normSq φMinus := by
  rw [kgmDephaseNegative, map_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- **The Poisson charge source is invariant under removal of the two rest
energies.**  The rapidly oscillating phases disappear from the diagonal
density `|ψ₊|² - |ψ₋|²`; only the paper's explicitly controlled cross-term
remainder can distinguish the finite-`c` KGM source from this main term. -/
@[simp] lemma schrodingerPoissonChargeDensity_dephase (c t : ℝ)
    (φPlus φMinus : ℂ) :
    schrodingerPoissonChargeDensity (kgmDephasePositive c t φPlus)
        (kgmDephaseNegative c t φMinus) =
      schrodingerPoissonChargeDensity φPlus φMinus := by
  simp [schrodingerPoissonChargeDensity]

/-- **Continuity of the signed Schrödinger–Poisson density.**  Convergence of
both complex frequency sectors implies convergence of their signed charge
density.  This is the pointwise nonlinear passage used after the paper's
uniform Sobolev control supplies convergence of the fields. -/
lemma schrodingerPoissonChargeDensity_tendsto
    {ι : Type*} {l : Filter ι} {ψPlus ψMinus : ι → ℂ} {vPlus vMinus : ℂ}
    (hPlus : Tendsto ψPlus l (𝓝 vPlus))
    (hMinus : Tendsto ψMinus l (𝓝 vMinus)) :
    Tendsto (fun i => schrodingerPoissonChargeDensity (ψPlus i) (ψMinus i)) l
      (𝓝 (schrodingerPoissonChargeDensity vPlus vMinus)) := by
  exact ((Complex.continuous_normSq.tendsto vPlus).comp hPlus).sub
    ((Complex.continuous_normSq.tendsto vMinus).comp hMinus)

/-- **Vanishing KGM source remainders give the Schrödinger–Poisson source.**
If the two dephased sectors converge and the oscillatory charge remainder
`R'ᶜ` tends to zero, then the complete finite-`c` source converges to
`|v₊|² - |v₋|²`. -/
lemma kgmChargeSource_tendsto_schrodingerPoisson
    {ι : Type*} {l : Filter ι} {ψPlus ψMinus : ι → ℂ}
    {remainder : ι → ℝ} {vPlus vMinus : ℂ}
    (hPlus : Tendsto ψPlus l (𝓝 vPlus))
    (hMinus : Tendsto ψMinus l (𝓝 vMinus))
    (hRemainder : Tendsto remainder l (𝓝 0)) :
    Tendsto
      (fun i => schrodingerPoissonChargeDensity (ψPlus i) (ψMinus i) +
        remainder i) l
      (𝓝 (schrodingerPoissonChargeDensity vPlus vMinus)) := by
  simpa using
    (schrodingerPoissonChargeDensity_tendsto hPlus hMinus).add hRemainder

/-! # C. Continuum Klein--Gordon pseudodifferential symbols

The following estimates are the pointwise Fourier-symbol content of Lemma 3
in Bechouche--Mauser--Selberg.  Unlike the single-mode frequency splitting
above, the variable `ξ` now ranges over the genuine continuum frequency
space `ℝ³`.  These bounds are the input for the `L²` multiplier theorem and
therefore for the paper's `H¹`/homogeneous-`H¹` estimates.
-/

/-- The continuum Klein--Gordon energy symbol
`E_c(ξ) = sqrt(c⁴ + c²|ξ|²)` on `ℝ³`. -/
def kgmEnergySymbol (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (c ^ 4 + c ^ 2 * ‖ξ‖ ^ 2)

/-- The inverse energy symbol used to diagonalize the KGM scalar field. -/
def kgmInverseEnergySymbol (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (kgmEnergySymbol c ξ)⁻¹

/-- The rest-energy-subtracted symbol generating the dephased sectors. -/
def kgmKineticSymbol (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  kgmEnergySymbol c ξ - c ^ 2

lemma kgmEnergySymbol_sq (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    kgmEnergySymbol c ξ ^ 2 = c ^ 4 + c ^ 2 * ‖ξ‖ ^ 2 := by
  rw [kgmEnergySymbol, Real.sq_sqrt]
  positivity

lemma kgmEnergySymbol_pos (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3))
    (hc : 0 < c) :
    0 < kgmEnergySymbol c ξ := by
  rw [kgmEnergySymbol, Real.sqrt_pos]
  have hc4 : 0 < c ^ 4 := pow_pos hc 4
  positivity

/-- The relativistic energy dominates the rest energy `c²`. -/
lemma c_sq_le_kgmEnergySymbol (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    c ^ 2 ≤ kgmEnergySymbol c ξ := by
  calc
    c ^ 2 = Real.sqrt ((c ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg c)).symm
    _ = Real.sqrt (c ^ 4) := by ring_nf
    _ ≤ Real.sqrt (c ^ 4 + c ^ 2 * ‖ξ‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact le_add_of_nonneg_right
        (mul_nonneg (sq_nonneg c) (sq_nonneg ‖ξ‖))
    _ = kgmEnergySymbol c ξ := rfl

/-- Lemma 3(i), at the exact continuum symbol level:
`|E_c(ξ)⁻¹| ≤ c⁻²`. -/
lemma kgmInverseEnergySymbol_le_inv_c_sq
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 0 < c) :
    kgmInverseEnergySymbol c ξ ≤ (c ^ 2)⁻¹ := by
  unfold kgmInverseEnergySymbol
  exact (inv_le_inv₀ (kgmEnergySymbol_pos c ξ hc) (sq_pos_of_pos hc)).2
    (c_sq_le_kgmEnergySymbol c ξ)

/-- Lemma 3(ii), at the exact continuum symbol level.  For `c ≥ 1`, the
inverse energy gains one inhomogeneous Sobolev derivative with norm at most
`c⁻¹`:
`sqrt(1 + |ξ|²) E_c(ξ)⁻¹ ≤ c⁻¹`. -/
lemma bessel_one_mul_kgmInverseEnergySymbol_le_inv_c
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 1 ≤ c) :
    Real.sqrt (1 + ‖ξ‖ ^ 2) * kgmInverseEnergySymbol c ξ ≤ c⁻¹ := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hweight : 0 ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := Real.sqrt_nonneg _
  have hweight_sq : Real.sqrt (1 + ‖ξ‖ ^ 2) ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hc_sq_le_four : c ^ 2 ≤ c ^ 4 := by
    nlinarith [sq_nonneg c, mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hc]
  have hscaled :
      c * Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ kgmEnergySymbol c ξ := by
    have hleft : 0 ≤ c * Real.sqrt (1 + ‖ξ‖ ^ 2) :=
      mul_nonneg hcpos.le hweight
    have hright : 0 ≤ kgmEnergySymbol c ξ :=
      (kgmEnergySymbol_pos c ξ hcpos).le
    have hsq :
        (c * Real.sqrt (1 + ‖ξ‖ ^ 2)) ^ 2 ≤
          kgmEnergySymbol c ξ ^ 2 := by
      rw [kgmEnergySymbol_sq, mul_pow, hweight_sq]
      nlinarith [sq_nonneg ‖ξ‖]
    nlinarith
  rw [kgmInverseEnergySymbol, ← div_eq_mul_inv]
  apply (div_le_iff₀ (kgmEnergySymbol_pos c ξ hcpos)).2
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hcpos).2 (by simpa [mul_comm] using hscaled)

/-- Exact rationalization of the rest-energy-subtracted symbol. -/
lemma kgmKineticSymbol_eq
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 0 < c) :
    kgmKineticSymbol c ξ =
      c ^ 2 * ‖ξ‖ ^ 2 / (kgmEnergySymbol c ξ + c ^ 2) := by
  have hden : 0 < kgmEnergySymbol c ξ + c ^ 2 :=
    add_pos (kgmEnergySymbol_pos c ξ hc) (sq_pos_of_pos hc)
  apply (eq_div_iff hden.ne').2
  unfold kgmKineticSymbol
  nlinarith [kgmEnergySymbol_sq c ξ]

lemma kgmKineticSymbol_nonneg
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ kgmKineticSymbol c ξ := by
  unfold kgmKineticSymbol
  exact sub_nonneg.mpr (c_sq_le_kgmEnergySymbol c ξ)

/-- Lemma 3(iii), at the exact continuum symbol level:
`0 ≤ E_c(ξ)-c² ≤ c|ξ|`.  This is the uniform wave-scale, one-derivative
bound used at high frequency. -/
lemma kgmKineticSymbol_le_c_mul_norm
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 0 < c) :
    kgmKineticSymbol c ξ ≤ c * ‖ξ‖ := by
  have hkin : 0 ≤ kgmKineticSymbol c ξ := kgmKineticSymbol_nonneg c ξ
  have htarget : 0 ≤ c * ‖ξ‖ := mul_nonneg hc.le (norm_nonneg ξ)
  have hproduct :
      kgmKineticSymbol c ξ * (kgmEnergySymbol c ξ + c ^ 2) =
        c ^ 2 * ‖ξ‖ ^ 2 := by
    unfold kgmKineticSymbol
    nlinarith [kgmEnergySymbol_sq c ξ]
  have hfactor :
      kgmKineticSymbol c ξ ≤ kgmEnergySymbol c ξ + c ^ 2 := by
    unfold kgmKineticSymbol
    nlinarith [sq_nonneg c]
  have hsq : kgmKineticSymbol c ξ ^ 2 ≤ (c * ‖ξ‖) ^ 2 := by
    calc
      kgmKineticSymbol c ξ ^ 2 =
          kgmKineticSymbol c ξ * kgmKineticSymbol c ξ := by ring
      _ ≤ kgmKineticSymbol c ξ * (kgmEnergySymbol c ξ + c ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor hkin
      _ = c ^ 2 * ‖ξ‖ ^ 2 := hproduct
      _ = (c * ‖ξ‖) ^ 2 := by ring
  nlinarith

/-- Lemma 3(iv), at the exact continuum symbol level:
`0 ≤ E_c(ξ)-c² ≤ |ξ|²/2`.  This is the `H² → L²` Schrödinger-scale bound,
uniform in `c`. -/
lemma kgmKineticSymbol_le_norm_sq_div_two
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 0 < c) :
    kgmKineticSymbol c ξ ≤ ‖ξ‖ ^ 2 / 2 := by
  rw [kgmKineticSymbol_eq c ξ hc]
  have hden : 0 < kgmEnergySymbol c ξ + c ^ 2 :=
    add_pos (kgmEnergySymbol_pos c ξ hc) (sq_pos_of_pos hc)
  apply (div_le_iff₀ hden).2
  have hrest := c_sq_le_kgmEnergySymbol c ξ
  nlinarith [sq_nonneg c, sq_nonneg ‖ξ‖]

/-! ## C.1. The paper's spatial null-form symbol -/

/-- The three spatial null forms are packaged as the cross-product symbol
`q(ξ,η) = ξ × η`.  Its coordinates are the paper's
`qᵢⱼ(ξ,η) = ξᵢηⱼ - ξⱼηᵢ`, up to the standard cyclic ordering. -/
def kgmSpatialNullFormSymbol
    (ξ η : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp ξ) (WithLp.ofLp η))

/-- The first inequality in equation (57): the spatial null-form symbol is
bounded by the product of the two frequencies. -/
lemma norm_kgmSpatialNullFormSymbol_le
    (ξ η : EuclideanSpace ℝ (Fin 3)) :
    ‖kgmSpatialNullFormSymbol ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  rw [kgmSpatialNullFormSymbol,
    InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right
    (mul_nonneg (norm_nonneg ξ) (norm_nonneg η)) (Real.sin_le_one _)

lemma kgmSpatialNullFormSymbol_add_left
    (ξ η : EuclideanSpace ℝ (Fin 3)) :
    kgmSpatialNullFormSymbol (ξ + η) η =
      kgmSpatialNullFormSymbol ξ η := by
  apply congrArg (WithLp.toLp 2)
  simp

lemma kgmSpatialNullFormSymbol_add_right
    (ξ η : EuclideanSpace ℝ (Fin 3)) :
    kgmSpatialNullFormSymbol ξ (ξ + η) =
      kgmSpatialNullFormSymbol ξ η := by
  apply congrArg (WithLp.toLp 2)
  simp

/-- The strengthened frequency-angle inequality in equation (57):
`|ξ × η| ≤ |ξ+η| |ξ|¹ᐟ² |η|¹ᐟ²`.  This is the cancellation estimate used
before Plancherel and the `L⁴` spacetime estimate in Proposition 3. -/
lemma norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt
    (ξ η : EuclideanSpace ℝ (Fin 3)) :
    ‖kgmSpatialNullFormSymbol ξ η‖ ≤
      ‖ξ + η‖ * Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖ := by
  have hξη : ‖kgmSpatialNullFormSymbol ξ η‖ ≤ ‖ξ + η‖ * ‖η‖ := by
    rw [← kgmSpatialNullFormSymbol_add_left ξ η]
    exact norm_kgmSpatialNullFormSymbol_le (ξ + η) η
  have hηξ : ‖kgmSpatialNullFormSymbol ξ η‖ ≤ ‖ξ‖ * ‖ξ + η‖ := by
    rw [← kgmSpatialNullFormSymbol_add_right ξ η]
    exact norm_kgmSpatialNullFormSymbol_le ξ (ξ + η)
  have hsξ : (Real.sqrt ‖ξ‖) ^ 2 = ‖ξ‖ := Real.sq_sqrt (norm_nonneg ξ)
  have hsη : (Real.sqrt ‖η‖) ^ 2 = ‖η‖ := Real.sq_sqrt (norm_nonneg η)
  have hsq : ‖kgmSpatialNullFormSymbol ξ η‖ ^ 2 ≤
      (‖ξ + η‖ * Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖) ^ 2 := by
    calc
      ‖kgmSpatialNullFormSymbol ξ η‖ ^ 2 =
          ‖kgmSpatialNullFormSymbol ξ η‖ *
            ‖kgmSpatialNullFormSymbol ξ η‖ := by ring
      _ ≤ (‖ξ + η‖ * ‖η‖) * (‖ξ‖ * ‖ξ + η‖) :=
        mul_le_mul hξη hηξ (norm_nonneg _) (by positivity)
      _ = (‖ξ + η‖ * Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsξ, hsη]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-! ## C.2. Spacetime Fourier convolution for the null form -/

/-- Four-dimensional Fourier frequency `(τ, ξ)`, represented in the native
Euclidean carrier.  Coordinate zero is temporal and the remaining three
coordinates are spatial. -/
abbrev KGMSpacetimeFrequency := EuclideanSpace ℝ (Fin 4)

/-- Spatial projection `(τ, ξ) ↦ ξ` from four-dimensional frequency space. -/
def kgmSpatialFrequency
    (ζ : KGMSpacetimeFrequency) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => WithLp.ofLp ζ i.succ

@[simp] lemma kgmSpatialFrequency_apply
    (ζ : KGMSpacetimeFrequency) (i : Fin 3) :
    kgmSpatialFrequency ζ i = ζ i.succ :=
  rfl

lemma kgmSpatialFrequency_sub
    (ζ ω : KGMSpacetimeFrequency) :
    kgmSpatialFrequency (ζ - ω) =
      kgmSpatialFrequency ζ - kgmSpatialFrequency ω := by
  ext i
  rfl

/-- Spatial coordinate multiplier on spacetime frequency space. -/
def kgmSpatialCoordinateWeight (i : Fin 3) :
    KGMSpacetimeFrequency → ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (i.succ : Fin 4))

lemma kgmSpatialCoordinateWeight_hasTemperateGrowth (i : Fin 3) :
    Function.HasTemperateGrowth (kgmSpatialCoordinateWeight i) := by
  exact (Complex.ofRealCLM.comp
    (EuclideanSpace.proj (i.succ : Fin 4))).hasTemperateGrowth

/-- Multiplication of a spacetime Schwartz amplitude by its `i`-th spatial
frequency coordinate. -/
def kgmSpatialWeightedSchwartz (i : Fin 3)
    (F : 𝓢(KGMSpacetimeFrequency, ℂ)) :
    𝓢(KGMSpacetimeFrequency, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (kgmSpatialCoordinateWeight i) F

@[simp] lemma kgmSpatialWeightedSchwartz_apply
    (i : Fin 3) (F : 𝓢(KGMSpacetimeFrequency, ℂ))
    (ζ : KGMSpacetimeFrequency) :
    kgmSpatialWeightedSchwartz i F ζ =
      (kgmSpatialFrequency ζ i : ℂ) * F ζ := by
  rw [kgmSpatialWeightedSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply
      (kgmSpatialCoordinateWeight_hasTemperateGrowth i)]
  rfl

/-- Equation (56), packaged using the repository's native Schwartz
convolution.  The two terms are precisely
`ηᵢ(ξ-η)ⱼ F̂u(η)F̂v(ξ-η)` and
`ηⱼ(ξ-η)ᵢ F̂u(η)F̂v(ξ-η)` on the full `(λ,η)` spacetime frequency. -/
def kgmSpacetimeNullFormFourierConvolution (i j : Fin 3)
    (Fu Fv : 𝓢(KGMSpacetimeFrequency, ℂ)) :
    𝓢(KGMSpacetimeFrequency, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (kgmSpatialWeightedSchwartz i Fu)
      (kgmSpatialWeightedSchwartz j Fv) -
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (kgmSpatialWeightedSchwartz j Fu)
      (kgmSpatialWeightedSchwartz i Fv)

/-- Exact integral realization of equation (56).  This is an equality of
genuine four-dimensional Bochner convolution integrals, not a finite-mode
sum or a definitional placeholder. -/
lemma kgmSpacetimeNullFormFourierConvolution_apply
    (i j : Fin 3) (Fu Fv : 𝓢(KGMSpacetimeFrequency, ℂ))
    (ζ : KGMSpacetimeFrequency) :
    kgmSpacetimeNullFormFourierConvolution i j Fu Fv ζ =
      (∫ ω,
        ((kgmSpatialFrequency ω i : ℂ) * Fu ω) *
          ((kgmSpatialFrequency (ζ - ω) j : ℂ) * Fv (ζ - ω))) -
      (∫ ω,
        ((kgmSpatialFrequency ω j : ℂ) * Fu ω) *
          ((kgmSpatialFrequency (ζ - ω) i : ℂ) * Fv (ζ - ω))) := by
  rw [kgmSpacetimeNullFormFourierConvolution, sub_apply,
    SchwartzMap.convolution_apply, SchwartzMap.convolution_apply]
  simp only [MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply', kgmSpatialWeightedSchwartz_apply]

/-- Coordinate form of the paper's spatial null symbol. -/
def kgmSpatialNullFormComponent (i j : Fin 3)
    (ξ η : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ξ i * η j - ξ j * η i

/-- The convolution integrand in equation (56) is exactly the paper's
`qᵢⱼ(η,ξ-η)` times the two spacetime Fourier amplitudes. -/
lemma kgmSpacetimeNullForm_integrand_eq
    (i j : Fin 3) (Fu Fv : 𝓢(KGMSpacetimeFrequency, ℂ))
    (ζ ω : KGMSpacetimeFrequency) :
    (((kgmSpatialFrequency ω i : ℂ) * Fu ω) *
          ((kgmSpatialFrequency (ζ - ω) j : ℂ) * Fv (ζ - ω))) -
        (((kgmSpatialFrequency ω j : ℂ) * Fu ω) *
          ((kgmSpatialFrequency (ζ - ω) i : ℂ) * Fv (ζ - ω))) =
      (kgmSpatialNullFormComponent i j
          (kgmSpatialFrequency ω) (kgmSpatialFrequency (ζ - ω)) : ℂ) *
        Fu ω * Fv (ζ - ω) := by
  unfold kgmSpatialNullFormComponent
  push_cast
  ring

/-- Equation (57) for every scalar component `qᵢⱼ`, obtained from the
already proved vector cross-product estimate. -/
lemma abs_kgmSpatialNullFormComponent_le_add_mul_sqrt
    (i j : Fin 3) (ξ η : EuclideanSpace ℝ (Fin 3)) :
    |kgmSpatialNullFormComponent i j ξ η| ≤
      ‖ξ + η‖ * Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖ := by
  have hcomponent : |kgmSpatialNullFormComponent i j ξ η| ≤
      ‖kgmSpatialNullFormSymbol ξ η‖ := by
    have hcoord (k : Fin 3) :
        |kgmSpatialNullFormSymbol ξ η k| ≤
          ‖kgmSpatialNullFormSymbol ξ η‖ := by
      simpa only [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (kgmSpatialNullFormSymbol ξ η) k)
    have h0 := hcoord (0 : Fin 3)
    have h1 := hcoord (1 : Fin 3)
    have h2 := hcoord (2 : Fin 3)
    have h12 : |ξ 1 * η 2 - ξ 2 * η 1| ≤
        ‖kgmSpatialNullFormSymbol ξ η‖ := by
      change |ξ 1 * η 2 - ξ 2 * η 1| ≤ _ at h0
      exact h0
    have h20 : |ξ 2 * η 0 - ξ 0 * η 2| ≤
        ‖kgmSpatialNullFormSymbol ξ η‖ := by
      change |ξ 2 * η 0 - ξ 0 * η 2| ≤ _ at h1
      exact h1
    have h01 : |ξ 0 * η 1 - ξ 1 * η 0| ≤
        ‖kgmSpatialNullFormSymbol ξ η‖ := by
      change |ξ 0 * η 1 - ξ 1 * η 0| ≤ _ at h2
      exact h2
    -- Every antisymmetric component is one coordinate of the cross product,
    -- possibly with sign; the three-dimensional cases are finite.
    fin_cases i <;> fin_cases j
    case «0».«0» => simp [kgmSpatialNullFormComponent]
    case «0».«1» => exact h01
    case «0».«2» =>
      unfold kgmSpatialNullFormComponent
      rw [abs_sub_comm]
      exact h20
    case «1».«0» =>
      unfold kgmSpatialNullFormComponent
      rw [abs_sub_comm]
      exact h01
    case «1».«1» => simp [kgmSpatialNullFormComponent]
    case «1».«2» => exact h12
    case «2».«0» => exact h20
    case «2».«1» =>
      unfold kgmSpatialNullFormComponent
      rw [abs_sub_comm]
      exact h12
    case «2».«2» => simp [kgmSpatialNullFormComponent]
  exact hcomponent.trans
    (norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt ξ η)

/-! ## C.3. The inverse-gradient cancellation behind equation (58) -/

/-- The spatial inverse-gradient multiplier applied to one scalar null-form
symbol.  The denominator is the output frequency `|ξ+η|`; at zero output
frequency Lean's field inverse gives the canonical value zero. -/
def kgmInverseSpatialNormNullComponent (i j : Fin 3)
    (ξ η : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖ξ + η‖⁻¹ * kgmSpatialNullFormComponent i j ξ η

/-- The pointwise multiplier reduction in equation (58): after applying
`|∇|⁻¹`, the total-frequency factor in equation (57) cancels and only
one half derivative remains on each input frequency. -/
lemma abs_kgmInverseSpatialNormNullComponent_le (i j : Fin 3)
    (ξ η : EuclideanSpace ℝ (Fin 3)) :
    |kgmInverseSpatialNormNullComponent i j ξ η| ≤
      Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖ := by
  by_cases hsum : ‖ξ + η‖ = 0
  · simp [kgmInverseSpatialNormNullComponent, hsum]
    positivity
  · have hsymbol :=
      abs_kgmSpatialNullFormComponent_le_add_mul_sqrt i j ξ η
    rw [kgmInverseSpatialNormNullComponent, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (ξ + η)))]
    calc
      ‖ξ + η‖⁻¹ * |kgmSpatialNullFormComponent i j ξ η| ≤
          ‖ξ + η‖⁻¹ *
            (‖ξ + η‖ * Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖) :=
        mul_le_mul_of_nonneg_left hsymbol (inv_nonneg.mpr (norm_nonneg _))
      _ = Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖ := by
        field_simp

/-- Complex-amplitude form of the equation-(58) reduction.  This is the
Fourier-integrand estimate subsequently combined in the paper with
Plancherel, Hölder, and the spacetime `L⁴` estimate. -/
lemma norm_kgmInverseSpatialNormNullComponent_mul_le
    (i j : Fin 3) (ξ η : EuclideanSpace ℝ (Fin 3)) (a b : ℂ) :
    ‖((kgmInverseSpatialNormNullComponent i j ξ η : ℝ) : ℂ) * a * b‖ ≤
      (Real.sqrt ‖ξ‖ * ‖a‖) * (Real.sqrt ‖η‖ * ‖b‖) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |kgmInverseSpatialNormNullComponent i j ξ η| * ‖a‖ * ‖b‖ ≤
        (Real.sqrt ‖ξ‖ * Real.sqrt ‖η‖) * ‖a‖ * ‖b‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (abs_kgmInverseSpatialNormNullComponent_le i j ξ η)
          (norm_nonneg a))
        (norm_nonneg b)
    _ = (Real.sqrt ‖ξ‖ * ‖a‖) * (Real.sqrt ‖η‖ * ‖b‖) := by ring

/-! ## C.4. Fourier majorization and spacetime Hölder -/

/-- Equation (56) in its single-integral null-symbol form.  The cancellation
between the two coordinate convolutions is performed inside the Bochner
integral, where equation (57) applies directly. -/
lemma kgmSpacetimeNullFormFourierConvolution_eq_integral
    (i j : Fin 3) (Fu Fv : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) :
    kgmSpacetimeNullFormFourierConvolution i j Fu Fv ζ =
      ∫ ω,
        (kgmSpatialNullFormComponent i j
          (kgmSpatialFrequency ω) (kgmSpatialFrequency (ζ - ω)) : ℂ) *
          Fu ω * Fv (ζ - ω) := by
  have hIntegrable (a b : Fin 3) : Integrable (fun ω =>
      ((kgmSpatialFrequency ω a : ℂ) * Fu ω) *
        ((kgmSpatialFrequency (ζ - ω) b : ℂ) * Fv (ζ - ω))) := by
    have hweighted : Integrable (fun ω =>
        kgmSpatialWeightedSchwartz a Fu ω *
          kgmSpatialWeightedSchwartz b Fv (ζ - ω)) := by
      apply (kgmSpatialWeightedSchwartz a Fu).integrable.mul_bdd
      · exact ((kgmSpatialWeightedSchwartz b Fv).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun ω =>
          SchwartzMap.norm_le_seminorm ℝ
            (kgmSpatialWeightedSchwartz b Fv) (ζ - ω)
    simpa only [kgmSpatialWeightedSchwartz_apply] using hweighted
  rw [kgmSpacetimeNullFormFourierConvolution_apply,
    ← integral_sub (hIntegrable i j) (hIntegrable j i)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    kgmSpacetimeNullForm_integrand_eq i j Fu Fv ζ ω

/-- Fourier-side realization of `|∇|⁻¹ Qᵢⱼ(u,v)`.  Unlike a symbolic
multiplier placeholder, this is the actual four-dimensional Bochner integral
with the inverse output spatial frequency built into its null symbol. -/
def kgmInverseSpatialNullFourierIntegral (i j : Fin 3)
    (Fu Fv : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) : ℂ :=
  ∫ ω,
    ((kgmInverseSpatialNormNullComponent i j
      (kgmSpatialFrequency ω) (kgmSpatialFrequency (ζ - ω)) : ℝ) : ℂ) *
      Fu ω * Fv (ζ - ω)

/-- The integral realization is exactly the inverse spatial-frequency
multiplier applied to the equation-(56) null-form convolution. -/
lemma kgmInverseSpatialNullFourierIntegral_eq_multiplier_mul
    (i j : Fin 3) (Fu Fv : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) :
    kgmInverseSpatialNullFourierIntegral i j Fu Fv ζ =
      ((‖kgmSpatialFrequency ζ‖⁻¹ : ℝ) : ℂ) *
        kgmSpacetimeNullFormFourierConvolution i j Fu Fv ζ := by
  rw [kgmInverseSpatialNullFourierIntegral,
    kgmSpacetimeNullFormFourierConvolution_eq_integral,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    unfold kgmInverseSpatialNormNullComponent
    rw [kgmSpatialFrequency_sub]
    have hsum : kgmSpatialFrequency ω +
        (kgmSpatialFrequency ζ - kgmSpatialFrequency ω) =
        kgmSpatialFrequency ζ := by abel
    rw [hsum]
    push_cast
    ring

/-- Magnitude of one half spatial derivative of a spacetime Fourier
amplitude. -/
def kgmHalfSpatialFourierMagnitude
    (F : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) : ℝ :=
  Real.sqrt ‖kgmSpatialFrequency ζ‖ * ‖F ζ‖

lemma kgmHalfSpatialFourierMagnitude_nonneg
    (F : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) :
    0 ≤ kgmHalfSpatialFourierMagnitude F ζ := by
  exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The unconditional convolution-majorization step of equation (58).
No positivity assumption is needed here because the right side uses Fourier
magnitudes. -/
lemma enorm_kgmInverseSpatialNullFourierIntegral_le
    (i j : Fin 3) (Fu Fv : SchwartzMap KGMSpacetimeFrequency ℂ)
    (ζ : KGMSpacetimeFrequency) :
    ‖kgmInverseSpatialNullFourierIntegral i j Fu Fv ζ‖ₑ ≤
      ∫⁻ ω,
        ENNReal.ofReal
          (kgmHalfSpatialFourierMagnitude Fu ω *
            kgmHalfSpatialFourierMagnitude Fv (ζ - ω)) := by
  rw [kgmInverseSpatialNullFourierIntegral]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply lintegral_mono
  intro ω
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [kgmHalfSpatialFourierMagnitude] using
    norm_kgmInverseSpatialNormNullComponent_mul_le i j
      (kgmSpatialFrequency ω) (kgmSpatialFrequency (ζ - ω))
      (Fu ω) (Fv (ζ - ω))

/-- Complex `Lᵖ` functions on spacetime. -/
abbrev KGMSpacetimeLp (p : ℝ≥0∞) :=
  Lp (α := KGMSpacetimeFrequency) ℂ p

section SpacetimeHolder

local instance kgmHolderTripleFourFourTwo : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    change ((↑(4 : NNReal) : ENNReal)⁻¹ + (↑(4 : NNReal) : ENNReal)⁻¹) =
      (↑(2 : NNReal) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0)]
    exact congrArg ENNReal.ofNNReal
      (show (4 : NNReal)⁻¹ + 4⁻¹ = 2⁻¹ by norm_num)

/-- The physical-space product `L⁴ × L⁴ → L²`, bundled through
Mathlib's native Hölder map. -/
def kgmSpacetimeL4Product
    (u v : KGMSpacetimeLp 4) : KGMSpacetimeLp 2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holder 2 u v

lemma kgmSpacetimeL4Product_coeFn
    (u v : KGMSpacetimeLp 4) :
    kgmSpacetimeL4Product u v =ᵐ[volume] fun z => u z * v z := by
  exact ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ) u v

/-- The exact spacetime Hölder step used after equation (58). -/
lemma norm_kgmSpacetimeL4Product_le
    (u v : KGMSpacetimeLp 4) :
    ‖kgmSpacetimeL4Product u v‖ ≤ ‖u‖ * ‖v‖ := by
  simpa [kgmSpacetimeL4Product] using
    (ContinuousLinearMap.norm_holder_apply_apply_le
      (B := ContinuousLinearMap.mul ℂ ℂ) (r := 2) u v)

/-- Plancherel transports an almost-everywhere Fourier-magnitude
majorization back to a physical-spacetime `L²` norm inequality.  This is the
native continuum replacement for treating Plancherel as an informal proof
step. -/
lemma norm_kgmSpacetimeLpTwo_le_of_fourier_norm_ae_le
    (f g : KGMSpacetimeLp 2)
    (hFourier : ∀ᵐ z ∂volume, ‖(𝓕 f) z‖ ≤ ‖(𝓕 g) z‖) :
    ‖f‖ ≤ ‖g‖ := by
  calc
    ‖f‖ = ‖𝓕 f‖ := (MeasureTheory.Lp.norm_fourier_eq f).symm
    _ ≤ ‖𝓕 g‖ := Lp.norm_le_norm_of_ae_le hFourier
    _ = ‖g‖ := MeasureTheory.Lp.norm_fourier_eq g

/-- The integrated Plancherel–Hölder closure of equation (58).  Once the
inverse-gradient null output is Fourier-majorized by the product of the two
half-spatial-derivative carriers, its spacetime `L²` norm is bounded by the
product of their `L⁴` norms.

The Fourier-majorization hypothesis is intentionally explicit: the theorem
does not assert the separate wave-propagator `L⁴` Strichartz estimate used in
Proposition 3 of Bechouche–Mauser–Selberg. -/
lemma norm_kgmEquation58Output_le_l4_mul_l4
    (nullOutput : KGMSpacetimeLp 2)
    (halfU halfV : KGMSpacetimeLp 4)
    (hFourier : ∀ᵐ z ∂volume,
      ‖(𝓕 nullOutput) z‖ ≤
        ‖(𝓕 (kgmSpacetimeL4Product halfU halfV)) z‖) :
    ‖nullOutput‖ ≤ ‖halfU‖ * ‖halfV‖ :=
  (norm_kgmSpacetimeLpTwo_le_of_fourier_norm_ae_le
      nullOutput (kgmSpacetimeL4Product halfU halfV) hFourier).trans
    (norm_kgmSpacetimeL4Product_le halfU halfV)

/-! ## C.5. Duhamel `L⁴` control and the Proposition 3 closure -/

local instance kgmFactOneLeFour : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

/-- The two analytic pieces in the paper's Duhamel formula (47), together
with the sharp-wave `L⁴` estimates needed for its Corollary (48).  The
carrier records the homogeneous propagator part and the forcing integral as
actual spacetime `L⁴` functions; the two bounds remain explicit analytic
data rather than being hidden behind the algebraic conclusion. -/
structure KGMDuhamelL4Control where
  /-- Half-spatial derivative of the homogeneous propagator term. -/
  homogeneousPart : KGMSpacetimeLp 4
  /-- Half-spatial derivative of the Duhamel forcing term. -/
  forcingPart : KGMSpacetimeLp 4
  /-- The initial-data `H¹` norm appearing in Corollary (48). -/
  initialH1Norm : ℝ
  /-- The forcing `L¹_t H¹_x` norm appearing in Corollary (48). -/
  forcingL1H1Norm : ℝ
  initialH1Norm_nonneg : 0 ≤ initialH1Norm
  forcingL1H1Norm_nonneg : 0 ≤ forcingL1H1Norm
  /-- The `q = r = 4` homogeneous sharp-wave estimate. -/
  homogeneous_bound : ‖homogeneousPart‖ ≤ initialH1Norm
  /-- The corresponding Minkowski/Duhamel forcing estimate. -/
  forcing_bound : ‖forcingPart‖ ≤ forcingL1H1Norm

namespace KGMDuhamelL4Control

/-- Half-spatial derivative of the complete solution in formula (47). -/
def halfDerivative (U : KGMDuhamelL4Control) : KGMSpacetimeLp 4 :=
  U.homogeneousPart + U.forcingPart

/-- Total data-and-forcing control on the right side of Corollary (48). -/
def totalControl (U : KGMDuhamelL4Control) : ℝ :=
  U.initialH1Norm + U.forcingL1H1Norm

lemma totalControl_nonneg (U : KGMDuhamelL4Control) :
    0 ≤ U.totalControl :=
  add_nonneg U.initialH1Norm_nonneg U.forcingL1H1Norm_nonneg

/-- Formula (47) plus the two component estimates gives the inhomogeneous
`L⁴` estimate (48) by the Banach-space triangle inequality. -/
lemma norm_halfDerivative_le_totalControl (U : KGMDuhamelL4Control) :
    ‖U.halfDerivative‖ ≤ U.totalControl := by
  exact (norm_add_le U.homogeneousPart U.forcingPart).trans
    (add_le_add U.homogeneous_bound U.forcing_bound)

end KGMDuhamelL4Control

/-- Proposition 3 in its exact norm form once the two load-bearing analytic
inputs are exposed: equation (58)'s Fourier majorization and Corollary (48)'s
`q = r = 4` controls for the two independently signed solutions. -/
lemma norm_kgmProposition3Output_le_data_forcing
    (nullOutput : KGMSpacetimeLp 2)
    (u v : KGMDuhamelL4Control)
    (hFourier : ∀ᵐ z ∂volume,
      ‖(𝓕 nullOutput) z‖ ≤
        ‖(𝓕 (kgmSpacetimeL4Product
          u.halfDerivative v.halfDerivative)) z‖) :
    ‖nullOutput‖ ≤ u.totalControl * v.totalControl := by
  exact (norm_kgmEquation58Output_le_l4_mul_l4
      nullOutput u.halfDerivative v.halfDerivative hFourier).trans
    (mul_le_mul
      u.norm_halfDerivative_le_totalControl
      v.norm_halfDerivative_le_totalControl
      (norm_nonneg v.halfDerivative)
      u.totalControl_nonneg)

/-- Finite-component form of the projected null-form corollary (54): a
finite sum of outputs satisfying Proposition 3 is controlled by the sum of
their data-and-forcing products.  This is the reusable normed-space step for
the three spatial antisymmetric components; identifying a concrete Leray or
Riesz representation remains a separate geometric identity. -/
lemma norm_sum_kgmProposition3Outputs_le
    {ι : Type*} [Fintype ι]
    (nullOutput : ι → KGMSpacetimeLp 2)
    (u v : ι → KGMDuhamelL4Control)
    (hFourier : ∀ k, ∀ᵐ z ∂volume,
      ‖(𝓕 (nullOutput k)) z‖ ≤
        ‖(𝓕 (kgmSpacetimeL4Product
          (u k).halfDerivative (v k).halfDerivative)) z‖) :
    ‖∑ k, nullOutput k‖ ≤
      ∑ k, (u k).totalControl * (v k).totalControl := by
  exact (norm_sum_le Finset.univ nullOutput).trans
    (Finset.sum_le_sum fun k _ =>
      norm_kgmProposition3Output_le_data_forcing
        (nullOutput k) (u k) (v k) (hFourier k))

end SpacetimeHolder

/-! ## C.6. The actual continuum inverse-energy multiplier -/

lemma continuous_kgmInverseEnergySymbol (c : ℝ) (hc : 0 < c) :
    Continuous (kgmInverseEnergySymbol c) := by
  unfold kgmInverseEnergySymbol kgmEnergySymbol
  apply Continuous.inv₀
  · fun_prop
  · intro ξ
    exact (kgmEnergySymbol_pos c ξ hc).ne'

lemma kgmInverseEnergySymbol_pos
    (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (hc : 0 < c) :
    0 < kgmInverseEnergySymbol c ξ :=
  inv_pos.mpr (kgmEnergySymbol_pos c ξ hc)

lemma memLp_kgmInverseEnergySymbol_mul
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) :
    MemLp
      (fun ξ => ((kgmInverseEnergySymbol c ξ : ℝ) : ℂ) * f ξ) 2 := by
  refine (Lp.memLp f).of_le_mul (c := (c ^ 2)⁻¹) ?_ ?_
  · exact
      ((Complex.continuous_ofReal.comp
        (continuous_kgmInverseEnergySymbol c hc)).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable f)
  · filter_upwards [] with ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (kgmInverseEnergySymbol_pos c ξ hc)]
    exact mul_le_mul_of_nonneg_right
      (kgmInverseEnergySymbol_le_inv_c_sq c ξ hc) (norm_nonneg (f ξ))

/-- The inverse KGM energy acting on continuum frequency-space `L²(ℝ³)`. -/
def kgmInverseEnergyFrequencyMultiplier
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) : EuclideanL2 3 :=
  (memLp_kgmInverseEnergySymbol_mul c hc f).toLp
    (fun ξ => ((kgmInverseEnergySymbol c ξ : ℝ) : ℂ) * f ξ)

lemma kgmInverseEnergyFrequencyMultiplier_coeFn
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) :
    kgmInverseEnergyFrequencyMultiplier c hc f =ᵐ[volume]
      fun ξ => ((kgmInverseEnergySymbol c ξ : ℝ) : ℂ) * f ξ :=
  MemLp.coeFn_toLp _

/-- Lemma 3(i) as a genuine continuum `L²` operator estimate. -/
lemma norm_kgmInverseEnergyFrequencyMultiplier_le
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) :
    ‖kgmInverseEnergyFrequencyMultiplier c hc f‖ ≤ (c ^ 2)⁻¹ * ‖f‖ := by
  rw [kgmInverseEnergyFrequencyMultiplier, Lp.norm_toLp, Lp.norm_def]
  have hC : 0 ≤ (c ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg c)
  rw [← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · finiteness
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [] with ξ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (kgmInverseEnergySymbol_pos c ξ hc)]
  exact mul_le_mul_of_nonneg_right
    (kgmInverseEnergySymbol_le_inv_c_sq c ξ hc) (norm_nonneg (f ξ))

/-- The inverse KGM pseudodifferential operator on physical-space
`L²(ℝ³)`, defined by Plancherel conjugation `𝓕⁻ E_c(D)⁻¹ 𝓕`. -/
def kgmInverseEnergyOperator
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) : EuclideanL2 3 :=
  𝓕⁻ (kgmInverseEnergyFrequencyMultiplier c hc (𝓕 f))

/-- The physical-space inverse-energy operator has norm at most `c⁻²`. -/
lemma norm_kgmInverseEnergyOperator_le
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) :
    ‖kgmInverseEnergyOperator c hc f‖ ≤ (c ^ 2)⁻¹ * ‖f‖ := by
  have hinv :
      ‖𝓕⁻ (kgmInverseEnergyFrequencyMultiplier c hc (𝓕 f))‖ =
        ‖kgmInverseEnergyFrequencyMultiplier c hc (𝓕 f)‖ := by
    simpa using
      (MeasureTheory.Lp.norm_fourier_eq
        (𝓕⁻ (kgmInverseEnergyFrequencyMultiplier c hc (𝓕 f)))).symm
  rw [kgmInverseEnergyOperator, hinv]
  exact (norm_kgmInverseEnergyFrequencyMultiplier_le c hc (𝓕 f)).trans_eq
    (by rw [MeasureTheory.Lp.norm_fourier_eq])

lemma besselPotentialWeight_one_eq_sqrt
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    besselPotentialWeight 1 ξ = Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  rw [besselPotentialWeight, Real.sqrt_eq_rpow]

private lemma weightedFourier_kgmInverseEnergyOperator_ae
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3) :
    weightedFourier 1 (kgmInverseEnergyOperator c hc f) =ᵐ[volume]
      fun ξ =>
        (besselPotentialWeight 1 ξ : ℂ) *
          (((kgmInverseEnergySymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ) := by
  have hFourier :
      𝓕 (kgmInverseEnergyOperator c hc f) =
        kgmInverseEnergyFrequencyMultiplier c hc (𝓕 f) := by
    simp [kgmInverseEnergyOperator]
  filter_upwards [
    kgmInverseEnergyFrequencyMultiplier_coeFn c hc (𝓕 f)
  ] with ξ hξ
  unfold weightedFourier
  rw [hFourier, hξ]

/-- Lemma 3(ii) on the native continuum Sobolev carrier: for `c ≥ 1`,
`E_c(D)⁻¹ : L²(ℝ³) → H¹(ℝ³)` and its `H¹` norm is at most `c⁻¹`
times the input `L²` norm. -/
lemma kgmInverseEnergyOperator_hasSobolevRegularity_one
    (c : ℝ) (hc : 1 ≤ c) (f : EuclideanL2 3) :
    HasSobolevRegularity 1
      (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f) := by
  let hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have htarget :
      MemLp
        (fun ξ =>
          (besselPotentialWeight 1 ξ : ℂ) *
            (((kgmInverseEnergySymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ)) 2 := by
    refine (Lp.memLp (𝓕 f)).of_le_mul (c := c⁻¹) ?_ ?_
    · exact
        (((Complex.continuous_ofReal.comp
          (continuous_besselPotentialWeight 1)).aestronglyMeasurable).mul
          ((Complex.continuous_ofReal.comp
            (continuous_kgmInverseEnergySymbol c hcpos)).aestronglyMeasurable.mul
            (Lp.aestronglyMeasurable (𝓕 f))))
    · filter_upwards [] with ξ
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (besselPotentialWeight_pos 1 ξ),
        abs_of_pos (kgmInverseEnergySymbol_pos c ξ hcpos),
        besselPotentialWeight_one_eq_sqrt]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (bessel_one_mul_kgmInverseEnergySymbol_le_inv_c c ξ hc)
        (norm_nonneg ((𝓕 f) ξ))
  unfold HasSobolevRegularity
  exact htarget.ae_eq
    (weightedFourier_kgmInverseEnergyOperator_ae c hcpos f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The quantitative continuum `L² → H¹` pseudodifferential estimate. -/
lemma sobolevNorm_kgmInverseEnergyOperator_le
    (c : ℝ) (hc : 1 ≤ c) (f : EuclideanL2 3) :
    sobolevNorm 1
        (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f)
        (kgmInverseEnergyOperator_hasSobolevRegularity_one c hc f) ≤
      c⁻¹ * ‖f‖ := by
  let hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [← MeasureTheory.Lp.norm_fourier_eq f]
  unfold sobolevNorm sobolevDerivativeFrequency
  rw [Lp.norm_toLp, Lp.norm_def]
  have hC : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
  rw [← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · finiteness
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [
    weightedFourier_kgmInverseEnergyOperator_ae c hcpos f
  ] with ξ hξ
  rw [hξ, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos 1 ξ),
    abs_of_pos (kgmInverseEnergySymbol_pos c ξ hcpos),
    besselPotentialWeight_one_eq_sqrt]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right
    (bessel_one_mul_kgmInverseEnergySymbol_le_inv_c c ξ hc)
    (norm_nonneg ((𝓕 f) ξ))

/-- The inverse KGM energy has genuine homogeneous first-order Sobolev
regularity.  This is the `Ḣ¹` form of the continuum multiplier result, not a
finite-mode analogue. -/
lemma kgmInverseEnergyOperator_hasHomogeneousOne
    (c : ℝ) (hc : 1 ≤ c) (f : EuclideanL2 3) :
    HasHomogeneousSobolevRegularityOne
      (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f) :=
  (kgmInverseEnergyOperator_hasSobolevRegularity_one c hc f).hasHomogeneousOne

/-- The paper-specific homogeneous estimate
`‖|D| E_c(D)⁻¹ f‖₂ ≤ c⁻¹ ‖f‖₂`.  It follows by composing the exact
continuum `L² → H¹` multiplier bound with the proved norm-one embedding
`H¹ → Ḣ¹`. -/
lemma homogeneousSobolevOneNorm_kgmInverseEnergyOperator_le
    (c : ℝ) (hc : 1 ≤ c) (f : EuclideanL2 3) :
    homogeneousSobolevOneNorm
        (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f)
        (kgmInverseEnergyOperator_hasHomogeneousOne c hc f) ≤
      c⁻¹ * ‖f‖ := by
  calc
    homogeneousSobolevOneNorm
        (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f)
        (kgmInverseEnergyOperator_hasHomogeneousOne c hc f) ≤
      sobolevNorm 1
        (kgmInverseEnergyOperator c (lt_of_lt_of_le zero_lt_one hc) f)
        (kgmInverseEnergyOperator_hasSobolevRegularity_one c hc f) :=
      homogeneousSobolevOneNorm_le_sobolevNorm_one _
    _ ≤ c⁻¹ * ‖f‖ := sobolevNorm_kgmInverseEnergyOperator_le c hc f

/-! ## C.7. The rest-energy-subtracted continuum multiplier -/

lemma continuous_kgmKineticSymbol (c : ℝ) :
    Continuous (kgmKineticSymbol c) := by
  unfold kgmKineticSymbol kgmEnergySymbol
  fun_prop

/-! ### C.7.1. The actual rest-energy-subtracted KGM propagator -/

/-- Fourier phase of the two dephased KGM sectors,
`exp(i σ t (E_c(ξ) - c²))`.  The paper's independently signed propagators
are obtained with `σ = ±1`. -/
def kgmRestSubtractedPhase
    (σ c t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (Complex.I *
    Complex.ofReal (σ * t * kgmKineticSymbol c ξ))

@[simp] lemma kgmRestSubtractedPhase_zero
    (σ c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    kgmRestSubtractedPhase σ c 0 ξ = 1 := by
  simp [kgmRestSubtractedPhase]

lemma kgmRestSubtractedPhase_add
    (σ c s t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    kgmRestSubtractedPhase σ c (s + t) ξ =
      kgmRestSubtractedPhase σ c s ξ *
        kgmRestSubtractedPhase σ c t ξ := by
  unfold kgmRestSubtractedPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma norm_kgmRestSubtractedPhase
    (σ c t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖kgmRestSubtractedPhase σ c t ξ‖ = 1 := by
  rw [kgmRestSubtractedPhase, Complex.norm_exp]
  simp

lemma continuous_kgmRestSubtractedPhase (σ c : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      kgmRestSubtractedPhase σ c p.1 p.2) := by
  unfold kgmRestSubtractedPhase
  have hreal : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      σ * p.1 * kgmKineticSymbol c p.2) :=
    (continuous_const.mul continuous_fst).mul
      ((continuous_kgmKineticSymbol c).comp continuous_snd)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hreal))

/-- The exact frequencywise derivative of the dephased KGM phase.  This is
the symbol-level infinitesimal-generator identity. -/
lemma hasDerivAt_kgmRestSubtractedPhase
    (σ c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => kgmRestSubtractedPhase σ c τ ξ)
      (kgmRestSubtractedPhase σ c t ξ *
        (Complex.I * Complex.ofReal (σ * kgmKineticSymbol c ξ))) t := by
  unfold kgmRestSubtractedPhase
  let a : ℂ := Complex.I * Complex.ofReal (σ * kgmKineticSymbol c ξ)
  have harg : HasDerivAt (fun τ : ℝ => a * (τ : ℂ)) a t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a
  have he := harg.cexp
  convert he using 1
  · funext τ
    congr 1
    push_cast
    simp [a]
    ring
  · congr 1
    push_cast
    simp [a]
    ring_nf

/-- Punctured difference quotient of the KGM phase at time zero. -/
def kgmRestSubtractedPhaseSlope
    (σ c t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  t⁻¹ • (kgmRestSubtractedPhase σ c t ξ - 1)

lemma kgmRestSubtractedPhaseSlope_tendsto
    (σ c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun t : ℝ => kgmRestSubtractedPhaseSlope σ c t ξ)
      (𝓝[≠] 0)
      (𝓝 (Complex.I * Complex.ofReal (σ * kgmKineticSymbol c ξ))) := by
  simpa only [kgmRestSubtractedPhaseSlope, zero_add,
    kgmRestSubtractedPhase_zero, one_mul] using
    (hasDerivAt_kgmRestSubtractedPhase σ c ξ 0).tendsto_slope_zero

/-- Uniform difference-quotient domination by the generator symbol. -/
lemma norm_kgmRestSubtractedPhaseSlope_le
    (σ c t : ℝ) (ht : t ≠ 0) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖kgmRestSubtractedPhaseSlope σ c t ξ‖ ≤
      |σ * kgmKineticSymbol c ξ| := by
  have hphase :
      ‖kgmRestSubtractedPhase σ c t ξ - 1‖ ≤
        ‖σ * t * kgmKineticSymbol c ξ‖ := by
    rw [kgmRestSubtractedPhase, Complex.norm_exp_I_mul_ofReal_sub_one]
    calc
      ‖2 * Real.sin ((σ * t * kgmKineticSymbol c ξ) / 2)‖ =
          2 * |Real.sin ((σ * t * kgmKineticSymbol c ξ) / 2)| := by simp
      _ ≤ 2 * |(σ * t * kgmKineticSymbol c ξ) / 2| :=
        (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
      _ = ‖σ * t * kgmKineticSymbol c ξ‖ := by
        rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]
        ring
  rw [kgmRestSubtractedPhaseSlope, norm_smul, Real.norm_eq_abs,
    abs_inv]
  calc
    |t|⁻¹ * ‖kgmRestSubtractedPhase σ c t ξ - 1‖
        ≤ |t|⁻¹ * |σ * t * kgmKineticSymbol c ξ| :=
      mul_le_mul_of_nonneg_left hphase (inv_nonneg.mpr (abs_nonneg t))
    _ = |σ * kgmKineticSymbol c ξ| := by
      rw [abs_mul, abs_mul, abs_mul]
      field_simp [abs_ne_zero.mpr ht]

lemma memLp_kgmRestSubtractedPhase_mul
    (σ c t : ℝ) (f : EuclideanL2 3) :
    MemLp (fun ξ => kgmRestSubtractedPhase σ c t ξ * f ξ) 2 := by
  exact (Lp.memLp f).congr_norm
    (((continuous_kgmRestSubtractedPhase σ c).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun ξ => by
      rw [norm_mul, norm_kgmRestSubtractedPhase, one_mul])

/-- Frequency-space `L²` multiplier for the rest-energy-subtracted KGM
propagator. -/
def kgmRestSubtractedMultiplier
    (σ c t : ℝ) (f : EuclideanL2 3) : EuclideanL2 3 :=
  (memLp_kgmRestSubtractedPhase_mul σ c t f).toLp
    (fun ξ => kgmRestSubtractedPhase σ c t ξ * f ξ)

lemma kgmRestSubtractedMultiplier_coeFn
    (σ c t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplier σ c t f =ᵐ[volume]
      fun ξ => kgmRestSubtractedPhase σ c t ξ * f ξ :=
  MemLp.coeFn_toLp _

/-- The frequency-space difference quotient of the dephased KGM flow. -/
def kgmRestSubtractedMultiplierSlope
    (σ c t : ℝ) (f : EuclideanL2 3) : EuclideanL2 3 :=
  t⁻¹ • (kgmRestSubtractedMultiplier σ c t f - f)

private lemma kgmRestSubtractedMultiplierSlope_coeFn
    (σ c t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplierSlope σ c t f =ᵐ[volume]
      fun ξ => kgmRestSubtractedPhaseSlope σ c t ξ * f ξ := by
  filter_upwards [
    Lp.coeFn_smul t⁻¹ (kgmRestSubtractedMultiplier σ c t f - f),
    Lp.coeFn_sub (kgmRestSubtractedMultiplier σ c t f) f,
    kgmRestSubtractedMultiplier_coeFn σ c t f
  ] with ξ hsmul hsub hmul
  rw [kgmRestSubtractedMultiplierSlope, hsmul, Pi.smul_apply,
    Complex.real_smul]
  rw [hsub]
  change ((t⁻¹ : ℝ) : ℂ) *
      (kgmRestSubtractedMultiplier σ c t f ξ - f ξ) =
    kgmRestSubtractedPhaseSlope σ c t ξ * f ξ
  rw [hmul]
  rw [kgmRestSubtractedPhaseSlope]
  change ((t⁻¹ : ℝ) : ℂ) *
      (kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ) =
    (((t⁻¹ : ℝ) : ℂ) *
      (kgmRestSubtractedPhase σ c t ξ - 1)) * f ξ
  ring

@[simp] lemma kgmRestSubtractedMultiplier_zero
    (σ c : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplier σ c 0 f = f := by
  apply Lp.ext (μ := volume)
  filter_upwards [kgmRestSubtractedMultiplier_coeFn σ c 0 f] with ξ hξ
  simpa using hξ

lemma kgmRestSubtractedMultiplier_add
    (σ c s t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplier σ c (s + t) f =
      kgmRestSubtractedMultiplier σ c s
        (kgmRestSubtractedMultiplier σ c t f) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    kgmRestSubtractedMultiplier_coeFn σ c (s + t) f,
    kgmRestSubtractedMultiplier_coeFn σ c t f,
    kgmRestSubtractedMultiplier_coeFn σ c s
      (kgmRestSubtractedMultiplier σ c t f)
  ] with ξ hst ht hs
  rw [hst, hs, ht, kgmRestSubtractedPhase_add]
  ring

@[simp] lemma norm_kgmRestSubtractedMultiplier
    (σ c t : ℝ) (f : EuclideanL2 3) :
    ‖kgmRestSubtractedMultiplier σ c t f‖ = ‖f‖ := by
  rw [kgmRestSubtractedMultiplier, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul, norm_kgmRestSubtractedPhase, one_mul]

lemma kgmRestSubtractedMultiplier_map_add
    (σ c t : ℝ) (f g : EuclideanL2 3) :
    kgmRestSubtractedMultiplier σ c t (f + g) =
      kgmRestSubtractedMultiplier σ c t f +
        kgmRestSubtractedMultiplier σ c t g := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    kgmRestSubtractedMultiplier_coeFn σ c t (f + g),
    kgmRestSubtractedMultiplier_coeFn σ c t f,
    kgmRestSubtractedMultiplier_coeFn σ c t g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (kgmRestSubtractedMultiplier σ c t f)
      (kgmRestSubtractedMultiplier σ c t g)
  ] with ξ hsum hf hg hfg hout
  rw [hsum, hfg, hout]
  change kgmRestSubtractedPhase σ c t ξ * (f ξ + g ξ) =
    kgmRestSubtractedMultiplier σ c t f ξ +
      kgmRestSubtractedMultiplier σ c t g ξ
  rw [hf, hg]
  ring

lemma kgmRestSubtractedMultiplier_map_smul
    (σ c t : ℝ) (a : ℂ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplier σ c t (a • f) =
      a • kgmRestSubtractedMultiplier σ c t f := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    kgmRestSubtractedMultiplier_coeFn σ c t (a • f),
    kgmRestSubtractedMultiplier_coeFn σ c t f,
    Lp.coeFn_smul a f,
    Lp.coeFn_smul a (kgmRestSubtractedMultiplier σ c t f)
  ] with ξ hmul hf haf hout
  rw [hmul, haf, hout]
  change kgmRestSubtractedPhase σ c t ξ * (a * f ξ) =
    a * kgmRestSubtractedMultiplier σ c t f ξ
  rw [hf]
  ring

/-- The KGM phase multiplier as a complex-linear isometric automorphism of
frequency-space `L²`; its inverse is the multiplier at time `-t`. -/
def kgmRestSubtractedMultiplierₗᵢ
    (σ c t : ℝ) : EuclideanL2 3 ≃ₗᵢ[ℂ] EuclideanL2 3 where
  toFun := kgmRestSubtractedMultiplier σ c t
  invFun := kgmRestSubtractedMultiplier σ c (-t)
  left_inv f := by
    calc
      kgmRestSubtractedMultiplier σ c (-t)
          (kgmRestSubtractedMultiplier σ c t f) =
          kgmRestSubtractedMultiplier σ c (-t + t) f :=
        (kgmRestSubtractedMultiplier_add σ c (-t) t f).symm
      _ = f := by simp
  right_inv f := by
    calc
      kgmRestSubtractedMultiplier σ c t
          (kgmRestSubtractedMultiplier σ c (-t) f) =
          kgmRestSubtractedMultiplier σ c (t + -t) f :=
        (kgmRestSubtractedMultiplier_add σ c t (-t) f).symm
      _ = f := by simp
  map_add' := kgmRestSubtractedMultiplier_map_add σ c t
  map_smul' := kgmRestSubtractedMultiplier_map_smul σ c t
  norm_map' := norm_kgmRestSubtractedMultiplier σ c t

@[simp] lemma kgmRestSubtractedMultiplierₗᵢ_apply
    (σ c t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedMultiplierₗᵢ σ c t f =
      kgmRestSubtractedMultiplier σ c t f :=
  rfl

/-- Physical-space KGM propagator `U_c^σ(t)`, obtained by Plancherel
conjugation of the rest-energy-subtracted phase multiplier. -/
def kgmRestSubtractedEvolution
    (σ c t : ℝ) (f : EuclideanL2 3) : EuclideanL2 3 :=
  𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f))

/-- The physical-space KGM evolution as a complex-linear isometric
automorphism, obtained by Fourier conjugation. -/
def kgmRestSubtractedEvolutionₗᵢ
    (σ c t : ℝ) : EuclideanL2 3 ≃ₗᵢ[ℂ] EuclideanL2 3 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
      (EuclideanSpace ℝ (Fin 3)) ℂ).trans
    ((kgmRestSubtractedMultiplierₗᵢ σ c t).trans
      (MeasureTheory.Lp.fourierTransformₗᵢ
        (EuclideanSpace ℝ (Fin 3)) ℂ).symm)

@[simp] lemma kgmRestSubtractedEvolutionₗᵢ_apply
    (σ c t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedEvolutionₗᵢ σ c t f =
      kgmRestSubtractedEvolution σ c t f :=
  rfl

@[simp] lemma kgmRestSubtractedEvolution_zero
    (σ c : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedEvolution σ c 0 f = f := by
  simp [kgmRestSubtractedEvolution]

lemma kgmRestSubtractedEvolution_add
    (σ c s t : ℝ) (f : EuclideanL2 3) :
    kgmRestSubtractedEvolution σ c (s + t) f =
      kgmRestSubtractedEvolution σ c s
        (kgmRestSubtractedEvolution σ c t f) := by
  simp [kgmRestSubtractedEvolution, kgmRestSubtractedMultiplier_add]

@[simp] lemma norm_kgmRestSubtractedEvolution
    (σ c t : ℝ) (f : EuclideanL2 3) :
    ‖kgmRestSubtractedEvolution σ c t f‖ = ‖f‖ := by
  have hinv :
      ‖𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f))‖ =
        ‖kgmRestSubtractedMultiplier σ c t (𝓕 f)‖ := by
    simpa using
      (MeasureTheory.Lp.norm_fourier_eq
        (𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f)))).symm
  rw [kgmRestSubtractedEvolution, hinv,
    norm_kgmRestSubtractedMultiplier, MeasureTheory.Lp.norm_fourier_eq]

private lemma weightedFourier_kgmRestSubtractedEvolution_ae
    (s σ c t : ℝ) (f : EuclideanL2 3) :
    weightedFourier s (kgmRestSubtractedEvolution σ c t f) =ᵐ[volume]
      fun ξ => kgmRestSubtractedPhase σ c t ξ * weightedFourier s f ξ := by
  have hFourier :
      𝓕 (kgmRestSubtractedEvolution σ c t f) =
        kgmRestSubtractedMultiplier σ c t (𝓕 f) := by
    simp [kgmRestSubtractedEvolution]
  change (fun ξ => (besselPotentialWeight s ξ : ℂ) *
    (𝓕 (kgmRestSubtractedEvolution σ c t f)) ξ) =ᵐ[volume] _
  rw [hFourier]
  filter_upwards [kgmRestSubtractedMultiplier_coeFn σ c t (𝓕 f)] with ξ hξ
  dsimp [weightedFourier]
  rw [hξ]
  ring

/-- The concrete KGM propagator preserves every available Bessel-potential
Sobolev domain. -/
lemma kgmRestSubtractedEvolution_hasSobolevRegularity
    (s σ c t : ℝ) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity s f) :
    HasSobolevRegularity s (kgmRestSubtractedEvolution σ c t f) := by
  have hphase : MemLp
      (fun ξ => kgmRestSubtractedPhase σ c t ξ * weightedFourier s f ξ) 2 := by
    exact hf.congr_norm
      ((((continuous_kgmRestSubtractedPhase σ c).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
          hf.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul, norm_kgmRestSubtractedPhase, one_mul])
  exact hphase.ae_eq
    (weightedFourier_kgmRestSubtractedEvolution_ae s σ c t f).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exact conservation of the native continuum `H^s` norm by the KGM
rest-energy-subtracted propagator. -/
lemma sobolevNorm_kgmRestSubtractedEvolution
    (s σ c t : ℝ) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity s f) :
    sobolevNorm s (kgmRestSubtractedEvolution σ c t f)
        (kgmRestSubtractedEvolution_hasSobolevRegularity s σ c t f hf) =
      sobolevNorm s f hf := by
  unfold sobolevNorm sobolevDerivativeFrequency
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [
    weightedFourier_kgmRestSubtractedEvolution_ae s σ c t f
  ] with ξ hξ
  rw [hξ, norm_mul, norm_kgmRestSubtractedPhase, one_mul]

private lemma kgmMultiplier_error_sq_integral_tendsto_zero
    (σ c : ℝ) (f : EuclideanL2 3) :
    Tendsto
      (fun t : ℝ => ∫ ξ,
        ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
  let F : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun t ξ => ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖ ^ 2
  have hF_meas :
      ∀ᶠ t : ℝ in 𝓝 0, AEStronglyMeasurable (F t) := by
    filter_upwards [] with t
    exact (((((continuous_kgmRestSubtractedPhase σ c).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f)).sub
          (Lp.aestronglyMeasurable f)).norm.pow 2)
  have hbound :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ ξ ∂volume,
        ‖F t ξ‖ ≤ 4 * ‖f ξ‖ ^ 2 := by
    filter_upwards [] with t
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _)]
      have hnorm :
          ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖ ≤
            2 * ‖f ξ‖ := by
        calc
          ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖
              ≤ ‖kgmRestSubtractedPhase σ c t ξ * f ξ‖ + ‖f ξ‖ :=
            norm_sub_le _ _
          _ = 2 * ‖f ξ‖ := by
            rw [norm_mul, norm_kgmRestSubtractedPhase]
            ring
      calc
        ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖ ^ 2
            ≤ (2 * ‖f ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = 4 * ‖f ξ‖ ^ 2 := by ring
  have hbound_integrable : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin 3) => 4 * ‖f ξ‖ ^ 2) :=
    ((Lp.memLp f).integrable_norm_pow two_ne_zero).const_mul 4
  have hlim : ∀ᵐ ξ ∂volume,
      Tendsto (fun t : ℝ => F t ξ) (𝓝 0) (𝓝 0) := by
    filter_upwards [] with ξ
    have hphase : Tendsto
        (fun t : ℝ => kgmRestSubtractedPhase σ c t ξ)
        (𝓝 0) (𝓝 1) := by
      have hcontinuous : Continuous
          (fun t : ℝ => kgmRestSubtractedPhase σ c t ξ) :=
        (continuous_kgmRestSubtractedPhase σ c).comp
          (continuous_id.prodMk continuous_const)
      rw [← kgmRestSubtractedPhase_zero σ c ξ]
      exact hcontinuous.continuousAt
    dsimp [F]
    convert (((hphase.mul_const (f ξ)).sub tendsto_const_nhds).norm.pow 2) using 1
    simp
  simpa [F] using tendsto_integral_filter_of_dominated_convergence
    (fun ξ : EuclideanSpace ℝ (Fin 3) => 4 * ‖f ξ‖ ^ 2)
    hF_meas hbound hbound_integrable hlim

private lemma norm_sq_kgmMultiplier_sub_eq_integral
    (σ c t : ℝ) (f : EuclideanL2 3) :
    ‖kgmRestSubtractedMultiplier σ c t f - f‖ ^ 2 =
      ∫ ξ, ‖kgmRestSubtractedPhase σ c t ξ * f ξ - f ξ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner
      (kgmRestSubtractedMultiplier σ c t f - f)
      (kgmRestSubtractedMultiplier σ c t f - f))]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub (kgmRestSubtractedMultiplier σ c t f) f,
    kgmRestSubtractedMultiplier_coeFn σ c t f
  ] with ξ hsub hmul
  rw [hsub]
  change RCLike.re (inner ℂ
      (kgmRestSubtractedMultiplier σ c t f ξ - f ξ)
      (kgmRestSubtractedMultiplier σ c t f ξ - f ξ)) = _
  rw [hmul, inner_self_eq_norm_sq]

/-- Strong frequency-space `L²` recovery at time zero. -/
lemma kgmRestSubtractedMultiplier_tendsto_zero
    (σ c : ℝ) (f : EuclideanL2 3) :
    Tendsto (fun t : ℝ => kgmRestSubtractedMultiplier σ c t f)
      (𝓝 0) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsq : Tendsto
      (fun t : ℝ => ‖kgmRestSubtractedMultiplier σ c t f - f‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa only [norm_sq_kgmMultiplier_sub_eq_integral] using
      kgmMultiplier_error_sq_integral_tendsto_zero σ c f
  have heventually := hsq.eventually (Iio_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [heventually] with t ht
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (kgmRestSubtractedMultiplier σ c t f - f)]

/-- The concrete rest-energy-subtracted KGM evolution is strongly continuous
at time zero on all of `L²(ℝ³)`. -/
lemma kgmRestSubtractedEvolution_tendsto_zero
    (σ c : ℝ) (f : EuclideanL2 3) :
    Tendsto (fun t : ℝ => kgmRestSubtractedEvolution σ c t f)
      (𝓝 0) (𝓝 f) := by
  have hinv : Tendsto (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)
      (𝓝 (𝓕 f)) (𝓝 f) := by
    have h : Tendsto (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)
        (𝓝 (𝓕 f)) (𝓝 (𝓕⁻ (𝓕 f))) :=
      (ContinuousFourierInv.continuous_fourierInv :
        Continuous (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)).continuousAt
    simpa only [FourierTransform.fourierInv_fourier_eq] using h
  exact hinv.comp (kgmRestSubtractedMultiplier_tendsto_zero σ c (𝓕 f))

/-- The resulting unitary group is strongly continuous at every time. -/
lemma kgmRestSubtractedEvolution_tendsto
    (σ c t₀ : ℝ) (f : EuclideanL2 3) :
    Tendsto (fun t : ℝ => kgmRestSubtractedEvolution σ c t f)
      (𝓝 t₀) (𝓝 (kgmRestSubtractedEvolution σ c t₀ f)) := by
  have hzero := kgmRestSubtractedEvolution_tendsto_zero σ c f
  have hshift : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => t - t₀) :=
      continuous_id.sub continuous_const
    have ht : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      hcont.continuousAt
    simpa using ht
  have hcomp := hzero.comp hshift
  have houter : Continuous
      (kgmRestSubtractedEvolutionₗᵢ σ c t₀ :
        EuclideanL2 3 → EuclideanL2 3) :=
    (kgmRestSubtractedEvolutionₗᵢ σ c t₀).continuous
  have hout : Tendsto
      (fun t : ℝ => kgmRestSubtractedEvolutionₗᵢ σ c t₀
        (kgmRestSubtractedEvolution σ c (t - t₀) f))
      (𝓝 t₀)
      (𝓝 (kgmRestSubtractedEvolutionₗᵢ σ c t₀ f)) :=
    Filter.Tendsto.comp houter.continuousAt hcomp
  have hfun :
      (fun t : ℝ => kgmRestSubtractedEvolution σ c t f) =
        (fun t : ℝ => kgmRestSubtractedEvolutionₗᵢ σ c t₀
          (kgmRestSubtractedEvolution σ c (t - t₀) f)) := by
    funext t
    rw [kgmRestSubtractedEvolutionₗᵢ_apply,
      ← kgmRestSubtractedEvolution_add]
    congr 2
    ring
  rw [hfun]
  simpa using hout

/-- Pointwise unitary `C₀`-group laws for the concrete rest-energy-subtracted
KGM flow. -/
def KGMRestSubtractedUnitaryC0Group
    (σ c : ℝ) (f : EuclideanL2 3) : Prop :=
    (∀ t : ℝ, kgmRestSubtractedEvolutionₗᵢ σ c t f =
      kgmRestSubtractedEvolution σ c t f) ∧
    kgmRestSubtractedEvolution σ c 0 f = f ∧
    (∀ s t : ℝ, kgmRestSubtractedEvolution σ c (s + t) f =
      kgmRestSubtractedEvolution σ c s
        (kgmRestSubtractedEvolution σ c t f)) ∧
    (∀ t : ℝ, ‖kgmRestSubtractedEvolution σ c t f‖ = ‖f‖) ∧
    (∀ t₀ : ℝ, Tendsto
      (fun t : ℝ => kgmRestSubtractedEvolution σ c t f)
      (𝓝 t₀) (𝓝 (kgmRestSubtractedEvolution σ c t₀ f)))

/-- Capstone certificate: the concrete rest-energy-subtracted KGM flow is a
complex-linear unitary `C₀` group on `L²(ℝ³)`.  The strong generator is
identified below first on the native `H¹` domain and then on its exact maximal
Fourier-multiplier domain. -/
lemma kgmRestSubtracted_unitaryC0Group
    (σ c : ℝ) (f : EuclideanL2 3) :
    KGMRestSubtractedUnitaryC0Group σ c f := by
  exact ⟨fun t => kgmRestSubtractedEvolutionₗᵢ_apply σ c t f,
    kgmRestSubtractedEvolution_zero σ c f,
    fun s t => kgmRestSubtractedEvolution_add σ c s t f,
    fun t => norm_kgmRestSubtractedEvolution σ c t f,
    fun t₀ => kgmRestSubtractedEvolution_tendsto σ c t₀ f⟩

lemma besselPotentialWeight_two_eq
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    besselPotentialWeight 2 ξ = 1 + ‖ξ‖ ^ 2 := by
  simp [besselPotentialWeight]

lemma memLp_kgmKineticSymbol_mul_of_H1
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    MemLp (fun ξ => ((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ) 2 := by
  refine hf.of_le_mul (c := c) ?_ ?_
  · exact
      ((Complex.continuous_ofReal.comp
        (continuous_kgmKineticSymbol c)).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable (𝓕 f))
  · filter_upwards [] with ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (kgmKineticSymbol_nonneg c ξ),
      weightedFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (besselPotentialWeight_pos 1 ξ),
      besselPotentialWeight_one_eq_sqrt]
    have hsymbol := kgmKineticSymbol_le_c_mul_norm c ξ hc
    have hnorm_le : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg ξ) (by positivity)]
      linarith
    calc
      kgmKineticSymbol c ξ * ‖(𝓕 f) ξ‖
          ≤ (c * ‖ξ‖) * ‖(𝓕 f) ξ‖ :=
        mul_le_mul_of_nonneg_right hsymbol (norm_nonneg ((𝓕 f) ξ))
      _ ≤ c * (Real.sqrt (1 + ‖ξ‖ ^ 2) * ‖(𝓕 f) ξ‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnorm_le (norm_nonneg ((𝓕 f) ξ))) hc.le

/-- The physical-space generator `E_c(D)-c²`, constructed on the native
continuum `H¹(ℝ³)` domain. -/
def kgmKineticOperator
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) : EuclideanL2 3 :=
  𝓕⁻ ((memLp_kgmKineticSymbol_mul_of_H1 c hc f hf).toLp
    (fun ξ => ((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ))

private lemma fourier_kgmKineticOperator_ae
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    (fun ξ => (𝓕 (kgmKineticOperator c hc f hf) : EuclideanL2 3) ξ) =ᵐ[volume]
      fun ξ => ((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ := by
  simpa [kgmKineticOperator] using
    (MemLp.coeFn_toLp (memLp_kgmKineticSymbol_mul_of_H1 c hc f hf))

/-- Fourier representative of the infinitesimal generator of the dephased
KGM group.  The factor `σ` is retained, so the degenerate flow `σ = 0` has
the correct all-of-`L²` generator domain. -/
def kgmRestSubtractedGeneratorField
    (σ c : ℝ) (f : EuclideanL2 3) :
    EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ =>
  (Complex.I * Complex.ofReal σ) *
    (((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ)

/-- Exact maximal Fourier-multiplier domain of the dephased KGM generator. -/
def KGMRestSubtractedGeneratorDomain
    (σ c : ℝ) (f : EuclideanL2 3) : Prop :=
  MemLp (kgmRestSubtractedGeneratorField σ c f) 2

/-- Frequency-space generator on its maximal multiplier domain. -/
def kgmRestSubtractedFrequencyGenerator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) : EuclideanL2 3 :=
  hf.toLp (kgmRestSubtractedGeneratorField σ c f)

/-- Physical-space generator obtained by Plancherel conjugation of the
maximal Fourier multiplier. -/
def kgmRestSubtractedPhysicalGenerator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) : EuclideanL2 3 :=
  𝓕⁻ (kgmRestSubtractedFrequencyGenerator σ c f hf)

/-- Pointwise frequency action of the rest-subtracted KGM generator.  Unlike
`kgmRestSubtractedGeneratorField`, this accepts a frequency-space vector
directly and is therefore the graph function used by the bundled partial
operator below. -/
def kgmRestSubtractedFrequencyGeneratorField
    (σ c : ℝ) (u : EuclideanL2 3) :
    EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ =>
  (Complex.I * Complex.ofReal σ) *
    (((kgmKineticSymbol c ξ : ℝ) : ℂ) * u ξ)

/-- The maximal frequency-multiplier domain as a complex submodule of
Euclidean `L²`. -/
def kgmRestSubtractedFrequencyGeneratorDomainSubmodule
    (σ c : ℝ) : Submodule ℂ (EuclideanL2 3) where
    carrier := {u | MemLp (kgmRestSubtractedFrequencyGeneratorField σ c u) 2 volume}
    zero_mem' := by
      apply MemLp.zero'.ae_eq
      filter_upwards [Lp.coeFn_zero ℂ 2
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))] with ξ hξ
      simp [kgmRestSubtractedFrequencyGeneratorField, hξ]
    add_mem' := by
      intro u v hu hv
      apply (hu.add hv).ae_eq
      filter_upwards [Lp.coeFn_add u v] with ξ hξ
      rw [kgmRestSubtractedFrequencyGeneratorField, hξ]
      simp [kgmRestSubtractedFrequencyGeneratorField, mul_add]
    smul_mem' := by
      intro z u hu
      apply (hu.const_smul z).ae_eq
      filter_upwards [Lp.coeFn_smul z u] with ξ hξ
      rw [kgmRestSubtractedFrequencyGeneratorField, hξ]
      simp [kgmRestSubtractedFrequencyGeneratorField, mul_left_comm]

lemma mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
    (σ c : ℝ) (u : EuclideanL2 3) :
    u ∈ kgmRestSubtractedFrequencyGeneratorDomainSubmodule σ c ↔
      MemLp (kgmRestSubtractedFrequencyGeneratorField σ c u) 2 volume :=
  Iff.rfl

/-- The dephased KGM infinitesimal generator as a genuine partial complex
linear map on frequency `L²`.  Its domain is the maximal multiplier domain;
in particular, when `σ = 0` the domain is all of `L²`. -/
def kgmRestSubtractedFrequencyGeneratorOperator
    (σ c : ℝ) : EuclideanL2 3 →ₗ.[ℂ] EuclideanL2 3 where
  domain := kgmRestSubtractedFrequencyGeneratorDomainSubmodule σ c

  toFun := {
    toFun := fun u =>
      ((mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff σ c u.1).mp u.2).toLp
        (kgmRestSubtractedFrequencyGeneratorField σ c u.1)
    map_add' := by
      intro u v
      let huvMem := (mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
        σ c (u + v).1).mp (u + v).2
      let huMem := (mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
        σ c u.1).mp u.2
      let hvMem := (mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
        σ c v.1).mp v.2
      apply Lp.ext (μ := volume)
      filter_upwards [
        MemLp.coeFn_toLp huvMem,
        MemLp.coeFn_toLp huMem,
        MemLp.coeFn_toLp hvMem,
        Lp.coeFn_add u.1 v.1,
        Lp.coeFn_add
          (huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1))
          (hvMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c v.1))
      ] with ξ huv hu hv hinput houtput
      rw [huv]
      change kgmRestSubtractedFrequencyGeneratorField σ c (u + v).1 ξ =
        (huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1) +
          hvMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c v.1)) ξ
      rw [houtput]
      change kgmRestSubtractedFrequencyGeneratorField σ c (u + v).1 ξ =
        (huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1)) ξ +
          (hvMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c v.1)) ξ
      rw [hu, hv]
      have hval : (u + v).1 = u.1 + v.1 := rfl
      rw [kgmRestSubtractedFrequencyGeneratorField, hval, hinput]
      simp [kgmRestSubtractedFrequencyGeneratorField, mul_add]
    map_smul' := by
      intro z u
      let hzuMem := (mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
        σ c (z • u).1).mp (z • u).2
      let huMem := (mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff
        σ c u.1).mp u.2
      apply Lp.ext (μ := volume)
      filter_upwards [
        MemLp.coeFn_toLp hzuMem,
        MemLp.coeFn_toLp huMem,
        Lp.coeFn_smul z u.1,
        Lp.coeFn_smul z
          (huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1))
      ] with ξ hzu hu hinput houtput
      rw [hzu]
      change kgmRestSubtractedFrequencyGeneratorField σ c (z • u).1 ξ =
        (z • huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1)) ξ
      rw [houtput]
      change kgmRestSubtractedFrequencyGeneratorField σ c (z • u).1 ξ =
        z * (huMem.toLp (kgmRestSubtractedFrequencyGeneratorField σ c u.1)) ξ
      rw [hu]
      have hval : (z • u).1 = z • u.1 := rfl
      rw [kgmRestSubtractedFrequencyGeneratorField, hval, hinput]
      simp [kgmRestSubtractedFrequencyGeneratorField, mul_left_comm]
  }

lemma kgmRestSubtractedFrequencyGeneratorOperator_apply_ae
    (σ c : ℝ)
    (u : (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain) :
    (kgmRestSubtractedFrequencyGeneratorOperator σ c u :
        EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
      kgmRestSubtractedFrequencyGeneratorField σ c u.1 := by
  exact MemLp.coeFn_toLp
    ((mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff σ c u.1).mp u.2)

/-- The old predicate and the domain of the bundled partial operator are
definitionally the same maximal graph condition after Fourier transform. -/
lemma kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator
    (σ c : ℝ) (f : EuclideanL2 3) :
    KGMRestSubtractedGeneratorDomain σ c f ↔
      𝓕 f ∈ (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain := by
  rfl

/-- Applying the bundled frequency operator reproduces exactly the previously
proved maximal-domain generator vector. -/
lemma kgmRestSubtractedFrequencyGeneratorOperator_apply
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    kgmRestSubtractedFrequencyGeneratorOperator σ c
        ⟨𝓕 f,
          (kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator σ c f).mp hf⟩ =
      kgmRestSubtractedFrequencyGenerator σ c f hf := by
  apply Lp.ext (μ := volume)
  filter_upwards [MemLp.coeFn_toLp hf,
    kgmRestSubtractedFrequencyGeneratorOperator_apply_ae σ c
      ⟨𝓕 f,
        (kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator σ c f).mp hf⟩] with ξ h₁ h₂
  exact h₂.trans h₁.symm

/-- The physical maximal-generator domain as the Fourier pullback of the
frequency multiplier domain. -/
def kgmRestSubtractedPhysicalGeneratorDomainSubmodule
    (σ c : ℝ) : Submodule ℂ (EuclideanL2 3) :=
    (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain.comap
      (MeasureTheory.Lp.fourierTransformₗᵢ
        (EuclideanSpace ℝ (Fin 3)) ℂ).toLinearEquiv.toLinearMap

/-- Fourier transform restricted to the physical maximal-generator domain. -/
def kgmRestSubtractedPhysicalDomainFourier
    (σ c : ℝ) :
    kgmRestSubtractedPhysicalGeneratorDomainSubmodule σ c →ₗ[ℂ]
      (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain where
  toFun := fun f => ⟨𝓕 f.1, f.2⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact FourierTransform.fourier_add f.1 g.1
  map_smul' := by
    intro z f
    apply Subtype.ext
    exact FourierTransform.fourier_smul z f.1

/-- The maximal rest-subtracted KGM generator in physical space, obtained by
Plancherel conjugation of the bundled frequency multiplier.  Its domain is
the Fourier pullback of the exact maximal frequency domain. -/
def kgmRestSubtractedPhysicalGeneratorOperator
    (σ c : ℝ) : EuclideanL2 3 →ₗ.[ℂ] EuclideanL2 3 where
  domain := kgmRestSubtractedPhysicalGeneratorDomainSubmodule σ c
  toFun :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      (EuclideanSpace ℝ (Fin 3)) ℂ).symm.toLinearEquiv.toLinearMap.comp
      ((kgmRestSubtractedFrequencyGeneratorOperator σ c).toFun.comp
        (kgmRestSubtractedPhysicalDomainFourier σ c))

lemma mem_kgmRestSubtractedPhysicalGeneratorOperator_domain_iff
    (σ c : ℝ) (f : EuclideanL2 3) :
    f ∈ (kgmRestSubtractedPhysicalGeneratorOperator σ c).domain ↔
      𝓕 f ∈ (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain :=
  Iff.rfl

/-- The bundled physical operator agrees with the previously proved
Plancherel-conjugated generator vector on the maximal domain. -/
lemma kgmRestSubtractedPhysicalGeneratorOperator_apply
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    kgmRestSubtractedPhysicalGeneratorOperator σ c
        ⟨f, (mem_kgmRestSubtractedPhysicalGeneratorOperator_domain_iff
          σ c f).mpr
            ((kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator
              σ c f).mp hf)⟩ =
      kgmRestSubtractedPhysicalGenerator σ c f hf := by
  simp only [kgmRestSubtractedPhysicalGeneratorOperator]
  change 𝓕⁻ (kgmRestSubtractedFrequencyGeneratorOperator σ c
      ⟨𝓕 f, _⟩) =
    𝓕⁻ (kgmRestSubtractedFrequencyGenerator σ c f hf)
  congr 1

/-- The maximal KGM generator is formally skew-adjoint: multiplication by
`i σ (E_c(ξ)-c²)` transfers across the `L²` pairing with a minus sign.
This is the operator-theoretic infinitesimal form of the proved unitary flow;
it does not silently assert surjectivity of the resolvent. -/
lemma kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg
    (σ c : ℝ) :
    (kgmRestSubtractedFrequencyGeneratorOperator σ c).IsFormalAdjoint
      (-(kgmRestSubtractedFrequencyGeneratorOperator σ c)) := by
  intro u v
  have hvDomain : v.1 ∈
      (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain := by
    simpa using v.2
  change inner ℂ ((kgmRestSubtractedFrequencyGeneratorOperator σ c) u) v.1 =
    inner ℂ u.1 (-((kgmRestSubtractedFrequencyGeneratorOperator σ c)
      ⟨v.1, hvDomain⟩))
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [
    kgmRestSubtractedFrequencyGeneratorOperator_apply_ae σ c u,
    kgmRestSubtractedFrequencyGeneratorOperator_apply_ae σ c ⟨v.1, hvDomain⟩,
    Lp.coeFn_neg
      ((kgmRestSubtractedFrequencyGeneratorOperator σ c)
        ⟨v.1, hvDomain⟩)
  ] with ξ hu hv hneg
  rw [hu, hneg]
  change inner ℂ (kgmRestSubtractedFrequencyGeneratorField σ c u.1 ξ) (v.1 ξ) =
    inner ℂ (u.1 ξ)
      (-((kgmRestSubtractedFrequencyGeneratorOperator σ c) ⟨v.1, hvDomain⟩ ξ))
  rw [hv]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul, kgmRestSubtractedFrequencyGeneratorField]
  ring

private lemma euclideanL2_tendsto_zero_iff_lintegral_enorm_sq
    {ι : Type*} {l : Filter ι} {u : ι → EuclideanL2 3} :
    Tendsto u l (𝓝 0) ↔
      Tendsto (fun i => ∫⁻ ξ, ‖u i ξ‖ₑ ^ 2) l (𝓝 0) := by
  trans Tendsto
    (fun i => (∫⁻ ξ, ‖u i ξ‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) l (𝓝 0)
  · simp [tendsto_iff_edist_tendsto_0, edist_zero_right,
      Lp.enorm_def, eLpNorm, eLpNorm']
  constructor <;> intro h
  · apply Tendsto.ennrpow_const 2 at h
    simpa [← ENNReal.rpow_mul_natCast] using h
  · apply Tendsto.ennrpow_const 2⁻¹ at h
    simpa using h

/-- The maximal frequency domain is dense in continuum `L²`.  The proof uses
bounded-symbol truncations of an arbitrary `L²` vector; no Sobolev regularity
is imposed on the vector being approximated. -/
lemma kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain
    (σ c : ℝ) :
    (kgmRestSubtractedFrequencyGeneratorOperator σ c).HasDenseDomain := by
  let a : EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ =>
    (Complex.I * Complex.ofReal σ) *
      ((kgmKineticSymbol c ξ : ℝ) : ℂ)
  have haStrong : AEStronglyMeasurable a :=
    ((Complex.continuous_ofReal.comp
      (continuous_kgmKineticSymbol c)).aestronglyMeasurable.const_smul
        (Complex.I * Complex.ofReal σ)).congr (by
          filter_upwards [] with ξ
          rfl)
  obtain ⟨a', haMeas, haa'⟩ := AEStronglyMeasurable.aemeasurable haStrong
  intro u
  apply mem_closure_iff_seq_limit.mpr
  let s : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun n =>
    a' ⁻¹' Metric.closedBall 0 n
  have hs : ∀ n, MeasurableSet (s n) := fun _ => by measurability
  let uCut : ℕ → EuclideanL2 3 := fun n =>
    ((Lp.memLp u).indicator (hs n)).toLp
      ((s n).indicator (u : EuclideanSpace ℝ (Fin 3) → ℂ))
  have huCut : ∀ n,
      (uCut n : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
        (s n).indicator u := fun n => MemLp.coeFn_toLp _
  refine ⟨uCut, ?_, ?_⟩
  · intro n
    change uCut n ∈
      kgmRestSubtractedFrequencyGeneratorDomainSubmodule σ c
    rw [mem_kgmRestSubtractedFrequencyGeneratorDomainSubmodule_iff]
    apply (Lp.memLp ((n : ℂ) • uCut n)).mono
    · refine (haStrong.mul (Lp.aestronglyMeasurable (uCut n))).congr ?_
      filter_upwards [] with ξ
      simp [a, kgmRestSubtractedFrequencyGeneratorField, mul_assoc]
    · filter_upwards [haa', Lp.coeFn_smul (n : ℂ) (uCut n), huCut n] with ξ ha hsmul hcut
      have haCoeff :
          (Complex.I * Complex.ofReal σ) *
              ((kgmKineticSymbol c ξ : ℝ) : ℂ) = a' ξ := by
        exact ha
      rw [kgmRestSubtractedFrequencyGeneratorField, ← mul_assoc,
        haCoeff, hsmul]
      by_cases hξ : ξ ∈ s n
      · rw [norm_mul]
        calc
          ‖a' ξ‖ * ‖uCut n ξ‖ ≤ (n : ℝ) * ‖uCut n ξ‖ :=
            mul_le_mul_of_nonneg_right (by simpa [s] using hξ) (norm_nonneg _)
          _ = ‖((n : ℂ) •
              (uCut n : EuclideanSpace ℝ (Fin 3) → ℂ)) ξ‖ := by simp
      · simp [hcut, hξ]
  · apply tendsto_sub_nhds_zero_iff.mp
    apply euclideanL2_tendsto_zero_iff_lintegral_enorm_sq.mpr
    have hdiff : ∀ n,
        ∫⁻ ξ, ‖(uCut n - u) ξ‖ₑ ^ 2 =
          ∫⁻ ξ, ‖(s n)ᶜ.indicator u ξ‖ₑ ^ 2 := by
      intro n
      refine lintegral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (uCut n) u, huCut n] with ξ hsub hcut
      rw [hsub]
      change ‖uCut n ξ - u ξ‖ₑ ^ 2 =
        ‖(s n)ᶜ.indicator u ξ‖ₑ ^ 2
      rw [hcut]
      change ‖(s n).indicator u ξ - u ξ‖ₑ ^ 2 =
        ‖(s n)ᶜ.indicator u ξ‖ₑ ^ 2
      by_cases hξ : ξ ∈ s n <;> simp [hξ]
    simp_rw [hdiff]
    rw [← MeasureTheory.lintegral_zero
      (α := EuclideanSpace ℝ (Fin 3)) (μ := volume)]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun ξ => ‖u ξ‖ₑ ^ 2) ?_ ?_ ?_ ?_
    · measurability
    · intro n
      filter_upwards with ξ
      by_cases hξ : ξ ∈ s n <;> simp [hξ]
    · have huFiniteRaw :=
        (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.ofNat_ne_top).mp
            (Lp.memLp u).2
      norm_num at huFiniteRaw
      exact huFiniteRaw.ne
    · filter_upwards [haa'] with ξ ha
      rw [← zero_pow two_ne_zero, ← enorm_zero (E := ℂ)]
      refine ENNReal.Tendsto.pow (Tendsto.enorm ?_)
      refine tendsto_nhds_of_eventually_eq ?_
      apply eventually_atTop.mpr
      use ⌈‖a' ξ‖⌉.toNat
      intro n hn
      have hle : ‖a' ξ‖ ≤ n := calc
        ‖a' ξ‖ ≤ (⌈‖a' ξ‖⌉ : ℝ) := Int.le_ceil _
        _ ≤ ⌈‖a' ξ‖⌉.toNat := by
          exact_mod_cast Int.self_le_toNat ⌈‖a' ξ‖⌉
        _ ≤ n := Nat.cast_le.mpr hn
      simp [s, hle]

/-- The densely defined maximal multiplier is closable.  Its proved formal
adjoint `-A` supplies the dense formal-adjoint witness required by the
repository's unbounded-operator infrastructure. -/
lemma kgmRestSubtractedFrequencyGeneratorOperator_isClosable
    (σ c : ℝ) :
    (kgmRestSubtractedFrequencyGeneratorOperator σ c).IsClosable := by
  apply LinearPMap.isClosable_of_exists_dense_formalAdjoint
    (kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain σ c)
  refine ⟨-(kgmRestSubtractedFrequencyGeneratorOperator σ c), ?_, ?_⟩
  · change Dense
      (((-(kgmRestSubtractedFrequencyGeneratorOperator σ c)).domain :
        Set (EuclideanL2 3)))
    rw [LinearPMap.neg_domain]
    exact kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain σ c
  · exact
      (kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg σ c).symm

/-- The maximal KGM frequency generator is a genuine unbounded operator in
the repository sense: it is densely defined and closable. -/
lemma kgmRestSubtractedFrequencyGeneratorOperator_isUnbounded
    (σ c : ℝ) :
    (kgmRestSubtractedFrequencyGeneratorOperator σ c).IsUnbounded :=
  ⟨kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain σ c,
    kgmRestSubtractedFrequencyGeneratorOperator_isClosable σ c⟩

lemma hasKGMRestSubtractedGeneratorDomain_of_H1
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    KGMRestSubtractedGeneratorDomain σ c f := by
  exact (memLp_kgmKineticSymbol_mul_of_H1 c hc f hf).const_smul
    (Complex.I * Complex.ofReal σ)

private lemma kgmGenerator_error_sq_integral_tendsto_zero
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    Tendsto
      (fun t : ℝ => ∫ ξ,
        ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ -
          (Complex.I * Complex.ofReal σ) *
            (((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ)‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  let G : EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ =>
    (Complex.I * Complex.ofReal σ) *
      (((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ)
  let F : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ := fun t ξ =>
    ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ - G ξ‖ ^ 2
  have hG_mem : MemLp G 2 := by
    change MemLp (kgmRestSubtractedGeneratorField σ c f) 2
    exact hf
  have hF_meas :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, AEStronglyMeasurable (F t) := by
    filter_upwards [] with t
    have hslope : Continuous
        (fun ξ : EuclideanSpace ℝ (Fin 3) =>
          kgmRestSubtractedPhaseSlope σ c t ξ) := by
      unfold kgmRestSubtractedPhaseSlope
      have hphase : Continuous
          (fun ξ : EuclideanSpace ℝ (Fin 3) =>
            kgmRestSubtractedPhase σ c t ξ) :=
        (continuous_kgmRestSubtractedPhase σ c).comp
          (continuous_const.prodMk continuous_id)
      have ht : Continuous (fun _ : EuclideanSpace ℝ (Fin 3) => (t⁻¹ : ℝ)) :=
        continuous_const
      exact ht.smul (hphase.sub continuous_const)
    exact (((hslope.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (𝓕 f))).sub hG_mem.1).norm.pow 2)
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ ξ ∂volume,
        ‖F t ξ‖ ≤ 4 * ‖G ξ‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _)]
      have hGnorm :
          ‖G ξ‖ = |σ * kgmKineticSymbol c ξ| * ‖(𝓕 f) ξ‖ := by
        dsimp [G]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        rw [abs_of_nonneg (kgmKineticSymbol_nonneg c ξ), abs_mul]
        rw [abs_of_nonneg (kgmKineticSymbol_nonneg c ξ)]
        ring
      have hslopeNorm :
          ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ‖ ≤
            ‖G ξ‖ := by
        rw [norm_mul, hGnorm]
        exact mul_le_mul_of_nonneg_right
          (norm_kgmRestSubtractedPhaseSlope_le σ c t ht0 ξ)
          (norm_nonneg ((𝓕 f) ξ))
      have herr :
          ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ - G ξ‖ ≤
            2 * ‖G ξ‖ := by
        calc
          ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ - G ξ‖
              ≤ ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ‖ +
                  ‖G ξ‖ := norm_sub_le _ _
          _ ≤ ‖G ξ‖ + ‖G ξ‖ :=
            add_le_add hslopeNorm le_rfl
          _ = 2 * ‖G ξ‖ := by ring
      calc
        ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ - G ξ‖ ^ 2
            ≤ (2 * ‖G ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) herr 2
        _ = 4 * ‖G ξ‖ ^ 2 := by ring
  have hbound_integrable : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin 3) => 4 * ‖G ξ‖ ^ 2) :=
    (hG_mem.integrable_norm_pow two_ne_zero).const_mul 4
  have hlim : ∀ᵐ ξ ∂volume,
      Tendsto (fun t : ℝ => F t ξ) (𝓝[≠] 0) (𝓝 0) := by
    filter_upwards [] with ξ
    have hslope := kgmRestSubtractedPhaseSlope_tendsto σ c ξ
    have hproduct := hslope.mul_const ((𝓕 f) ξ)
    have hproduct' : Tendsto
        (fun t : ℝ =>
          kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ)
        (𝓝[≠] 0) (𝓝 (G ξ)) := by
      convert hproduct using 1
      dsimp [G]
      push_cast
      ring_nf
    have hconst : Tendsto (fun _ : ℝ => G ξ)
        (𝓝[≠] 0) (𝓝 (G ξ)) := tendsto_const_nhds
    simpa [F] using ((hproduct'.sub hconst).norm.pow 2)
  simpa [F, G] using tendsto_integral_filter_of_dominated_convergence
    (fun ξ : EuclideanSpace ℝ (Fin 3) => 4 * ‖G ξ‖ ^ 2)
    hF_meas hbound hbound_integrable hlim

private lemma norm_sq_kgmMultiplierSlope_sub_generator_eq_integral
    (σ c t : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) -
        kgmRestSubtractedFrequencyGenerator σ c f hf‖ ^ 2 =
      ∫ ξ,
        ‖kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ -
          (Complex.I * Complex.ofReal σ) *
            (((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ)‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner
      (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) -
        kgmRestSubtractedFrequencyGenerator σ c f hf)
      (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) -
        kgmRestSubtractedFrequencyGenerator σ c f hf))]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (kgmRestSubtractedFrequencyGenerator σ c f hf),
    kgmRestSubtractedMultiplierSlope_coeFn σ c t (𝓕 f),
    MemLp.coeFn_toLp hf
  ] with ξ hsub hslope hgenerator
  rw [hsub]
  change RCLike.re (inner ℂ
      (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) ξ -
        kgmRestSubtractedFrequencyGenerator σ c f hf ξ)
      (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) ξ -
        kgmRestSubtractedFrequencyGenerator σ c f hf ξ)) = _
  rw [hslope]
  change RCLike.re (inner ℂ
      (kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ -
        kgmRestSubtractedFrequencyGenerator σ c f hf ξ)
      (kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ -
        kgmRestSubtractedFrequencyGenerator σ c f hf ξ)) = _
  have hgenerator' :
      kgmRestSubtractedFrequencyGenerator σ c f hf ξ =
        kgmRestSubtractedGeneratorField σ c f ξ := by
    simpa only [kgmRestSubtractedFrequencyGenerator] using hgenerator
  rw [hgenerator', inner_self_eq_norm_sq]
  rfl

/-- Strong frequency-space differentiability holds on the exact maximal
Fourier-multiplier domain. -/
lemma kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    Tendsto
      (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (𝓝[≠] 0)
      (𝓝 (kgmRestSubtractedFrequencyGenerator σ c f hf)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsq : Tendsto
      (fun t : ℝ =>
        ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) -
          kgmRestSubtractedFrequencyGenerator σ c f hf‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [norm_sq_kgmMultiplierSlope_sub_generator_eq_integral]
      using kgmGenerator_error_sq_integral_tendsto_zero σ c f hf
  have heventually := hsq.eventually (Iio_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [heventually] with t ht
  rw [dist_eq_norm]
  nlinarith [norm_nonneg
    (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) -
      kgmRestSubtractedFrequencyGenerator σ c f hf)]

private lemma aestronglyMeasurable_kgmRestSubtractedGeneratorField
    (σ c : ℝ) (f : EuclideanL2 3) :
    AEStronglyMeasurable (kgmRestSubtractedGeneratorField σ c f) := by
  have hkinetic : AEStronglyMeasurable
      (fun ξ : EuclideanSpace ℝ (Fin 3) =>
        ((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ) :=
    (Complex.continuous_ofReal.comp
      (continuous_kgmKineticSymbol c)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (𝓕 f))
  refine (hkinetic.const_smul (Complex.I * Complex.ofReal σ)).congr ?_
  filter_upwards [] with ξ
  change (Complex.I * Complex.ofReal σ) *
      (((kgmKineticSymbol c ξ : ℝ) : ℂ) * (𝓕 f) ξ) =
    kgmRestSubtractedGeneratorField σ c f ξ
  rfl

private lemma aestronglyMeasurable_kgmRestSubtractedRawSlope
    (σ c t : ℝ) (f : EuclideanL2 3) :
    AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ) := by
  have hslope : Continuous
      (fun ξ : EuclideanSpace ℝ (Fin 3) =>
        kgmRestSubtractedPhaseSlope σ c t ξ) := by
    unfold kgmRestSubtractedPhaseSlope
    have hphase : Continuous
        (fun ξ : EuclideanSpace ℝ (Fin 3) =>
          kgmRestSubtractedPhase σ c t ξ) :=
      (continuous_kgmRestSubtractedPhase σ c).comp
        (continuous_const.prodMk continuous_id)
    have ht : Continuous (fun _ : EuclideanSpace ℝ (Fin 3) => (t⁻¹ : ℝ)) :=
      continuous_const
    exact ht.smul (hphase.sub continuous_const)
  exact hslope.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (𝓕 f))

/-- Necessity of the multiplier-domain condition: if the Fourier-space
difference quotient has any strong `L²` limit, then the exact symbol times the
datum belongs to `L²`.  This is the reverse implication missing from an
`H¹`-only sufficient-domain theorem. -/
lemma KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto
    (σ c : ℝ) (f g : EuclideanL2 3)
    (hlim : Tendsto
      (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (𝓝[≠] 0) (𝓝 g)) :
    KGMRestSubtractedGeneratorDomain σ c f := by
  let Q : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ := fun t ξ =>
    kgmRestSubtractedPhaseSlope σ c t ξ * (𝓕 f) ξ
  let G : EuclideanSpace ℝ (Fin 3) → ℂ :=
    kgmRestSubtractedGeneratorField σ c f
  have hnorm : Tendsto
      (fun t : ℝ => ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f)‖)
      (𝓝[≠] 0) (𝓝 ‖g‖) := hlim.norm
  have hnormBound : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f)‖ < ‖g‖ + 1 :=
    hnorm.eventually (Iio_mem_nhds (lt_add_one ‖g‖))
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      eLpNorm (Q t) 2 volume ≤ ENNReal.ofReal (‖g‖ + 1) := by
    filter_upwards [hnormBound] with t ht
    calc
      eLpNorm (Q t) 2 volume =
          eLpNorm (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) :
            EuclideanSpace ℝ (Fin 3) → ℂ) 2 volume :=
        eLpNorm_congr_ae
          (kgmRestSubtractedMultiplierSlope_coeFn σ c t (𝓕 f)).symm
      _ = ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f)‖ₑ :=
        (Lp.enorm_def _).symm
      _ = ENNReal.ofReal
          ‖kgmRestSubtractedMultiplierSlope σ c t (𝓕 f)‖ :=
        (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖g‖ + 1) :=
        ENNReal.ofReal_le_ofReal ht.le
  have hpoint : ∀ᵐ ξ ∂volume,
      Tendsto (fun t : ℝ => Q t ξ) (𝓝[≠] 0) (𝓝 (G ξ)) := by
    filter_upwards [] with ξ
    have hproduct :=
      (kgmRestSubtractedPhaseSlope_tendsto σ c ξ).mul_const ((𝓕 f) ξ)
    convert hproduct using 1
    dsimp [Q, G, kgmRestSubtractedGeneratorField]
    push_cast
    ring_nf
  have hfinite : eLpNorm G 2 volume ≤ ENNReal.ofReal (‖g‖ + 1) :=
    Lp.eLpNorm_le_of_ae_tendsto hbound
      (fun t => by
        simpa only [Q] using
          aestronglyMeasurable_kgmRestSubtractedRawSlope σ c t f)
      hpoint
  refine ⟨?_, hfinite.trans_lt ENNReal.ofReal_lt_top⟩
  simpa only [G] using
    aestronglyMeasurable_kgmRestSubtractedGeneratorField σ c f

/-- Exact maximal-domain characterization in frequency space: a strong
difference-quotient limit exists iff the datum belongs to the multiplier
domain. -/
lemma kgmRestSubtractedMultiplierSlope_exists_tendsto_iff
    (σ c : ℝ) (f : EuclideanL2 3) :
    (∃ g : EuclideanL2 3,
      Tendsto
        (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
        (𝓝[≠] 0) (𝓝 g)) ↔
      KGMRestSubtractedGeneratorDomain σ c f := by
  constructor
  · rintro ⟨g, hg⟩
    exact KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto σ c f g hg
  · intro hf
    exact ⟨kgmRestSubtractedFrequencyGenerator σ c f hf,
      kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator σ c f hf⟩

/-- Any strong Fourier-space derivative is necessarily the maximal
multiplier generator; the value is not an additional choice. -/
lemma kgmRestSubtractedMultiplierSlope_limit_eq_maximalGenerator
    (σ c : ℝ) (f g : EuclideanL2 3)
    (hlim : Tendsto
      (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (𝓝[≠] 0) (𝓝 g)) :
    g = kgmRestSubtractedFrequencyGenerator σ c f
      (KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto σ c f g hlim) := by
  exact tendsto_nhds_unique hlim
    (kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator σ c f
      (KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto σ c f g hlim))

lemma kgmRestSubtractedFrequencyGenerator_of_H1
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    kgmRestSubtractedFrequencyGenerator σ c f
        (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf) =
      (Complex.I * Complex.ofReal σ) •
        𝓕 (kgmKineticOperator c hc f hf) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    MemLp.coeFn_toLp
      (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf),
    Lp.coeFn_smul (Complex.I * Complex.ofReal σ)
      (𝓕 (kgmKineticOperator c hc f hf)),
    fourier_kgmKineticOperator_ae c hc f hf
  ] with ξ hgenerator hsmul hkinetic
  have hgenerator' :
      kgmRestSubtractedFrequencyGenerator σ c f
          (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf) ξ =
        kgmRestSubtractedGeneratorField σ c f ξ := by
    simpa only [kgmRestSubtractedFrequencyGenerator] using hgenerator
  rw [hgenerator', hsmul]
  change kgmRestSubtractedGeneratorField σ c f ξ =
    (Complex.I * Complex.ofReal σ) *
      (𝓕 (kgmKineticOperator c hc f hf)) ξ
  rw [hkinetic]
  rfl

/-- On the native continuum `H¹` domain, the strong frequency-space
difference quotient of the dephased KGM group converges to
`i σ (E_c-c²)`. -/
lemma kgmRestSubtractedMultiplierSlope_tendsto_generator
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    Tendsto
      (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (𝓝[≠] 0)
      (𝓝 ((Complex.I * Complex.ofReal σ) •
        𝓕 (kgmKineticOperator c hc f hf))) := by
  rw [← kgmRestSubtractedFrequencyGenerator_of_H1 σ c hc f hf]
  exact kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator σ c f
    (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf)

/-- Operator-level Stone generator statement: on precisely the domain of the
bundled partial multiplier, the frequency-space `C₀`-group difference
quotient converges to that operator's value. -/
lemma kgmRestSubtractedMultiplierSlope_tendsto_frequencyOperator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : 𝓕 f ∈
      (kgmRestSubtractedFrequencyGeneratorOperator σ c).domain) :
    Tendsto
      (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
      (𝓝[≠] 0)
      (𝓝 (kgmRestSubtractedFrequencyGeneratorOperator σ c
        ⟨𝓕 f, hf⟩)) := by
  let hdomain : KGMRestSubtractedGeneratorDomain σ c f :=
    (kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator σ c f).mpr hf
  rw [kgmRestSubtractedFrequencyGeneratorOperator_apply σ c f hdomain]
  exact kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator σ c f hdomain

lemma kgmRestSubtractedEvolutionSlope_eq_fourierInv
    (σ c t : ℝ) (f : EuclideanL2 3) :
    t⁻¹ • (kgmRestSubtractedEvolution σ c t f - f) =
      𝓕⁻ (kgmRestSubtractedMultiplierSlope σ c t (𝓕 f)) := by
  rw [kgmRestSubtractedMultiplierSlope, kgmRestSubtractedEvolution]
  have hfInv : (𝓕⁻ (𝓕 f) : EuclideanL2 3) = f :=
    FourierTransform.fourierInv_fourier_eq f
  have hsub :
      (𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f) - 𝓕 f) :
          EuclideanL2 3) =
        𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f)) - 𝓕⁻ (𝓕 f) :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      (EuclideanSpace ℝ (Fin 3)) ℂ).symm.map_sub _ _
  calc
    t⁻¹ • (𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f)) - f) =
        t⁻¹ • (𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f)) -
          𝓕⁻ (𝓕 f)) := by rw [hfInv]
    _ = ((t⁻¹ : ℝ) : ℂ) •
          (𝓕⁻ (kgmRestSubtractedMultiplier σ c t (𝓕 f)) - 𝓕⁻ (𝓕 f)) :=
      (IsScalarTower.algebraMap_smul ℂ (t⁻¹ : ℝ) _).symm
    _ = 𝓕⁻ (((t⁻¹ : ℝ) : ℂ) •
        (kgmRestSubtractedMultiplier σ c t (𝓕 f) - 𝓕 f)) := by
      rw [FourierTransform.fourierInv_smul, hsub]
    _ = 𝓕⁻ (t⁻¹ •
        (kgmRestSubtractedMultiplier σ c t (𝓕 f) - 𝓕 f)) := by
      congr 1

/-- On the exact maximal multiplier domain, the physical-space difference
quotient converges strongly to the Plancherel-conjugated generator. -/
lemma kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : KGMRestSubtractedGeneratorDomain σ c f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        (kgmRestSubtractedEvolution σ c t f - f))
      (𝓝[≠] 0)
      (𝓝 (kgmRestSubtractedPhysicalGenerator σ c f hf)) := by
  have hinv : Tendsto (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)
      (𝓝 (kgmRestSubtractedFrequencyGenerator σ c f hf))
      (𝓝 (kgmRestSubtractedPhysicalGenerator σ c f hf)) := by
    have h : Tendsto (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)
        (𝓝 (kgmRestSubtractedFrequencyGenerator σ c f hf))
        (𝓝 (𝓕⁻ (kgmRestSubtractedFrequencyGenerator σ c f hf))) :=
      (ContinuousFourierInv.continuous_fourierInv :
        Continuous (𝓕⁻ : EuclideanL2 3 → EuclideanL2 3)).continuousAt
    simpa only [kgmRestSubtractedPhysicalGenerator] using h
  have hcomp := hinv.comp
    (kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator σ c f hf)
  convert hcomp using 1
  funext t
  exact kgmRestSubtractedEvolutionSlope_eq_fourierInv σ c t f

/-- Operator-level physical-space generator statement: on precisely the
Fourier pullback of the maximal multiplier domain, the dephased KGM `C₀`
group difference quotient converges to the bundled physical operator. -/
lemma kgmRestSubtractedEvolutionSlope_tendsto_physicalGeneratorOperator
    (σ c : ℝ) (f : EuclideanL2 3)
    (hf : f ∈
      (kgmRestSubtractedPhysicalGeneratorOperator σ c).domain) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        (kgmRestSubtractedEvolution σ c t f - f))
      (𝓝[≠] 0)
      (𝓝 (kgmRestSubtractedPhysicalGeneratorOperator σ c ⟨f, hf⟩)) := by
  let hdomain : KGMRestSubtractedGeneratorDomain σ c f :=
    (kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator σ c f).mpr
      ((mem_kgmRestSubtractedPhysicalGeneratorOperator_domain_iff σ c f).mp hf)
  rw [kgmRestSubtractedPhysicalGeneratorOperator_apply σ c f hdomain]
  exact kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator σ c f hdomain

lemma kgmRestSubtractedPhysicalGenerator_of_H1
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    kgmRestSubtractedPhysicalGenerator σ c f
        (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf) =
      (Complex.I * Complex.ofReal σ) •
        kgmKineticOperator c hc f hf := by
  rw [kgmRestSubtractedPhysicalGenerator,
    kgmRestSubtractedFrequencyGenerator_of_H1,
    FourierTransform.fourierInv_smul,
    FourierTransform.fourierInv_fourier_eq]

/-- Exact maximal-domain characterization in physical space.  By the Fourier
isometry, a strong physical difference quotient exists precisely on the same
multiplier domain as its frequency-space representative. -/
lemma kgmRestSubtractedEvolutionSlope_exists_tendsto_iff
    (σ c : ℝ) (f : EuclideanL2 3) :
    (∃ g : EuclideanL2 3,
      Tendsto
        (fun t : ℝ => t⁻¹ •
          (kgmRestSubtractedEvolution σ c t f - f))
        (𝓝[≠] 0) (𝓝 g)) ↔
      KGMRestSubtractedGeneratorDomain σ c f := by
  constructor
  · rintro ⟨g, hg⟩
    have hfourier : Tendsto (𝓕 : EuclideanL2 3 → EuclideanL2 3)
        (𝓝 g) (𝓝 (𝓕 g)) :=
      (ContinuousFourier.continuous_fourier :
        Continuous (𝓕 : EuclideanL2 3 → EuclideanL2 3)).continuousAt
    have hcomp := hfourier.comp hg
    have hfreq : Tendsto
        (fun t : ℝ => kgmRestSubtractedMultiplierSlope σ c t (𝓕 f))
        (𝓝[≠] 0) (𝓝 (𝓕 g)) := by
      convert hcomp using 1
      funext t
      change kgmRestSubtractedMultiplierSlope σ c t (𝓕 f) =
        𝓕 (t⁻¹ • (kgmRestSubtractedEvolution σ c t f - f))
      rw [kgmRestSubtractedEvolutionSlope_eq_fourierInv,
        FourierTransform.fourier_fourierInv_eq]
    exact KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto
      σ c f (𝓕 g) hfreq
  · intro hf
    exact ⟨kgmRestSubtractedPhysicalGenerator σ c f hf,
      kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator σ c f hf⟩

/-- The physical dephased KGM `C₀` group has the strong infinitesimal
generator `i σ (E_c(D)-c²)` on the native continuum `H¹(ℝ³)` domain. -/
lemma kgmRestSubtractedEvolutionSlope_tendsto_generator
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        (kgmRestSubtractedEvolution σ c t f - f))
      (𝓝[≠] 0)
      (𝓝 ((Complex.I * Complex.ofReal σ) •
        kgmKineticOperator c hc f hf)) := by
  rw [← kgmRestSubtractedPhysicalGenerator_of_H1 σ c hc f hf]
  exact kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator σ c f
    (hasKGMRestSubtractedGeneratorDomain_of_H1 σ c hc f hf)

/-- Combined continuum certificate: the dephased KGM evolution is a unitary
`C₀` group on `L²`, and on every native `H¹` datum its strong generator is
exactly `i σ (E_c(D)-c²)`. -/
lemma kgmRestSubtracted_unitaryC0Group_with_H1Generator
    (σ c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    KGMRestSubtractedUnitaryC0Group σ c f ∧
      Tendsto
        (fun t : ℝ => t⁻¹ •
          (kgmRestSubtractedEvolution σ c t f - f))
        (𝓝[≠] 0)
        (𝓝 ((Complex.I * Complex.ofReal σ) •
          kgmKineticOperator c hc f hf)) := by
  exact ⟨kgmRestSubtracted_unitaryC0Group σ c f,
    kgmRestSubtractedEvolutionSlope_tendsto_generator σ c hc f hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 3(iii) as a genuine continuum operator estimate:
`E_c(D)-c² : H¹(ℝ³) → L²(ℝ³)` has norm at most `c`. -/
lemma norm_kgmKineticOperator_le_c_mul_sobolevNorm_one
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 1 f) :
    ‖kgmKineticOperator c hc f hf‖ ≤ c * sobolevNorm 1 f hf := by
  have hPlancherel : ‖kgmKineticOperator c hc f hf‖ =
      ‖𝓕 (kgmKineticOperator c hc f hf)‖ :=
    (MeasureTheory.Lp.norm_fourier_eq _).symm
  rw [hPlancherel, Lp.norm_def, sobolevNorm, sobolevDerivativeFrequency,
    Lp.norm_toLp]
  rw [show c * (eLpNorm (weightedFourier 1 f) 2 volume).toReal =
      (ENNReal.ofReal c * eLpNorm (weightedFourier 1 f) 2 volume).toReal by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]]
  apply ENNReal.toReal_mono
  · finiteness
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [fourier_kgmKineticOperator_ae c hc f hf] with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (kgmKineticSymbol_nonneg c ξ),
    weightedFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos 1 ξ),
    besselPotentialWeight_one_eq_sqrt]
  have hsymbol := kgmKineticSymbol_le_c_mul_norm c ξ hc
  have hnorm_le : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg ξ) (by positivity)]
    linarith
  calc
    kgmKineticSymbol c ξ * ‖(𝓕 f) ξ‖
        ≤ (c * ‖ξ‖) * ‖(𝓕 f) ξ‖ :=
      mul_le_mul_of_nonneg_right hsymbol (norm_nonneg ((𝓕 f) ξ))
    _ ≤ c * (Real.sqrt (1 + ‖ξ‖ ^ 2) * ‖(𝓕 f) ξ‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnorm_le (norm_nonneg ((𝓕 f) ξ))) hc.le

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 3(iv) as a genuine continuum operator estimate.  On the `H²`
domain, the same generator has the uniform Schrödinger-scale bound
`‖(E_c(D)-c²)f‖₂ ≤ (1/2)‖f‖_{H²}`. -/
lemma norm_kgmKineticOperator_le_half_sobolevNorm_two
    (c : ℝ) (hc : 0 < c) (f : EuclideanL2 3)
    (hf : HasSobolevRegularity 2 f) :
    ‖kgmKineticOperator c hc f (hf.mono (by norm_num))‖ ≤
      (1 / 2 : ℝ) * sobolevNorm 2 f hf := by
  have hPlancherel :
      ‖kgmKineticOperator c hc f (hf.mono (by norm_num))‖ =
        ‖𝓕 (kgmKineticOperator c hc f (hf.mono (by norm_num)))‖ :=
    (MeasureTheory.Lp.norm_fourier_eq _).symm
  rw [hPlancherel, Lp.norm_def, sobolevNorm, sobolevDerivativeFrequency,
    Lp.norm_toLp]
  rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · finiteness
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [
    fourier_kgmKineticOperator_ae c hc f (hf.mono (by norm_num))
  ] with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (kgmKineticSymbol_nonneg c ξ),
    weightedFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos 2 ξ), besselPotentialWeight_two_eq]
  have hsymbol := kgmKineticSymbol_le_norm_sq_div_two c ξ hc
  calc
    kgmKineticSymbol c ξ * ‖(𝓕 f) ξ‖
        ≤ (‖ξ‖ ^ 2 / 2) * ‖(𝓕 f) ξ‖ :=
      mul_le_mul_of_nonneg_right hsymbol (norm_nonneg ((𝓕 f) ξ))
    _ ≤ (1 / 2 : ℝ) * ((1 + ‖ξ‖ ^ 2) * ‖(𝓕 f) ξ‖) := by
      nlinarith [norm_nonneg ((𝓕 f) ξ), sq_nonneg ‖ξ‖]

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit

end

end

/- ZIL-BEGIN -/

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency.einsteinEnergy]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger where
  formalizes @ "claim:the-rationalized-relativistic-kinetic-fourier-symbol-converges-to-the-schrodinger-symbol-as-c-tends-to-infinity",
  epistemic_status @ "risky",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-dispersion-limit",
  caveat @ "claim:genuine-pointwise-fourier-symbol-limit-not-the-paper's-uniform-H1-pseudodifferential-multiplier-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.energy_mul_kgmFrequencyMode_sub where
  at_level algebraic
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmPositiveFrequencyMode,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmNegativeFrequencyMode,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmCovariantTemporalDatum]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.energy_mul_kgmFrequencyMode_sub where
  formalizes @ "claim:the-positive-negative-frequency-split-is-invertible-at-every-nonzero-fourier-energy-symbol",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-frequency-decomposition",
  caveat @ "claim:exact-single-fourier-mode-algebra-not-the-continuum-pseudodifferential-multiplier-bound"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity_dephase where
  at_level algebraic
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmDephasePositive,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmDephaseNegative]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity_dephase where
  formalizes @ "claim:removing-the-positive-and-negative-rest-energy-phases-preserves-the-diagonal-signed-poisson-charge-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Complex.norm_exp_ofReal_mul_I",
  caveat @ "claim:exact-phase-cancellation-for-the-diagonal-density-not-vanishing-of-the-paper's-oscillatory-cross-term-remainder"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmChargeSource_tendsto_schrodingerPoisson where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmChargeSource_tendsto_schrodingerPoisson where
  formalizes @ "claim:convergence-of-both-dephased-frequency-sectors-and-vanishing-of-the-oscillatory-charge-remainder-give-the-schrodinger-poisson-source",
  epistemic_status @ "risky",
  supported_by @ "lean:Complex.continuous_normSq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-charge-density-decomposition",
  caveat @ "claim:nonlinear-continuity-consequence-after-explicit-convergence-premises-not-a-proof-of-the-paper's-sobolev-compactness-or-remainder-estimates"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmInverseEnergyOperator_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseEnergyOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmInverseEnergyOperator_le where
  formalizes @ "claim:lemma-3-i-ii-the-continuum-plancherel-pseudodifferential-operator-Ec-inverse-maps-L2-R3-to-H1-R3-with-norm-at-most-c-inverse",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-lemma-3",
  caveat @ "claim:genuine-continuum-L2-to-H1-Fourier-multiplier-bound-not-yet-the-bilinear-null-form-Strichartz-estimate-or-the-global-KGM-existence-theorem"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.homogeneousSobolevOneNorm_kgmInverseEnergyOperator_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseEnergyOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.homogeneousSobolevOneNorm_kgmInverseEnergyOperator_le where
  formalizes @ "claim:the-continuum-inverse-energy-operator-obeys-the-homogeneous-H1-bound-norm-D-Ec-inverse-f-L2-at-most-c-inverse-times-norm-f-L2",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.homogeneousSobolevOneNorm_le_sobolevNorm_one",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-lemma-3",
  caveat @ "claim:genuine-continuum-homogeneous-Sobolev-multiplier-estimate-not-the-paper's-bilinear-spacetime-null-form-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpatialNullFormSymbol]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt where
  formalizes @ "claim:equation-57-spatial-null-form-symbol-cancellation-bound-norm-xi-cross-eta-at-most-norm-xi-plus-eta-times-square-root-frequency-factors",
  epistemic_status @ "risky",
  supported_by @ "lean:InnerProductGeometry.norm_ofLp_crossProduct",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equation-57",
  caveat @ "claim:exact-continuum-frequency-symbol-bound-that-precedes-Plancherel-not-yet-equation-58-or-Proposition-3-which-also-require-convolution-and-L4-spacetime-Strichartz-estimates"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution_apply where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution_apply where
  formalizes @ "claim:equation-56-the-spacetime-fourier-transform-of-the-spatial-null-form-is-the-four-dimensional-convolution-of-coordinate-weighted-schwartz-amplitudes",
  epistemic_status @ "risky",
  supported_by @ "lean:SchwartzMap.convolution_apply",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equation-56",
  caveat @ "claim:exact-four-dimensional-Bochner-convolution-identity-on-Schwartz-amplitudes-not-by-itself-the-L2-null-form-bound-or-an-L4-Strichartz-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmInverseSpatialNormNullComponent_mul_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNormNullComponent]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmInverseSpatialNormNullComponent_mul_le where
  formalizes @ "claim:equation-58-pointwise-fourier-reduction-the-inverse-output-gradient-cancels-the-null-symbol-and-leaves-one-half-spatial-derivative-on-each-amplitude",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.abs_kgmSpatialNullFormComponent_le_add_mul_sqrt",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equations-57-58",
  caveat @ "claim:exact-pointwise-multiplier-and-complex-amplitude-majorant-including-zero-output-frequency-not-the-integrated-spacetime-L2-conclusion-which-still-requires-Plancherel-Holder-and-L4-Strichartz"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral_eq_multiplier_mul where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral_eq_multiplier_mul where
  formalizes @ "claim:equations-56-58-the-actual-four-dimensional-Bochner-null-integral-with-inverse-output-gradient-equals-the-inverse-spatial-frequency-multiplier-times-the-null-convolution",
  epistemic_status @ "risky",
  supported_by @ "lean:SchwartzMap.convolution_apply",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equations-56-58",
  caveat @ "claim:exact-Schwartz-integral-and-multiplier-identity-not-yet-an-L2-bound-or-a-wave-propagator-Strichartz-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.enorm_kgmInverseSpatialNullFourierIntegral_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmHalfSpatialFourierMagnitude]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.enorm_kgmInverseSpatialNullFourierIntegral_le where
  formalizes @ "claim:equation-58-the-inverse-gradient-null-integral-is-unconditionally-majorized-by-the-convolution-of-the-two-half-spatial-derivative-Fourier-magnitudes",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.enorm_integral_le_lintegral_enorm",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equation-58",
  caveat @ "claim:unconditional-pointwise-frequency-majorization-on-Schwartz-amplitudes-not-by-itself-the-integrated-L2-bound-or-Proposition-3"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmEquation58Output_le_l4_mul_l4 where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeL4Product]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmEquation58Output_le_l4_mul_l4 where
  formalizes @ "claim:equation-58-Plancherel-and-Holder-close-a-Fourier-majorized-inverse-gradient-null-output-from-L4-times-L4-into-spacetime-L2",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "lean:ContinuousLinearMap.norm_holder_apply_apply_le",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equation-58",
  caveat @ "claim:exact-integrated-conclusion-under-the-explicit-Fourier-majorization-premise-not-a-proof-of-the-separate-wave-propagator-L4-Strichartz-bound-needed-for-Proposition-3"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.norm_halfDerivative_le_totalControl where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.halfDerivative,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.totalControl]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.norm_halfDerivative_le_totalControl where
  formalizes @ "claim:formula-47-and-corollary-48-the-homogeneous-and-Duhamel-L4-parts-combine-into-the-initial-H1-plus-forcing-L1H1-control",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:norm_add_le",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-47-48",
  caveat @ "claim:exact-Banach-space-Duhamel-closure-after-the-two-L4-component-estimates-recorded-in-the-carrier-not-a-proof-of-Proposition-1's-oscillatory-integral-Strichartz-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmProposition3Output_le_data_forcing where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmProposition3Output_le_data_forcing where
  formalizes @ "claim:Proposition-3-the-inverse-gradient-null-form-L2-norm-is-bounded-by-the-product-of-initial-H1-plus-forcing-L1H1-controls",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmEquation58Output_le_l4_mul_l4",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-Proposition-3",
  caveat @ "claim:exact-Proposition-3-conclusion-from-explicit-Fourier-majorization-and-sharp-wave-L4-control-data-not-an-unconditional-construction-of-those-analytic-inputs"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_sum_kgmProposition3Outputs_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_sum_kgmProposition3Outputs_le where
  formalizes @ "claim:equation-54-corollary-finite-spatial-null-components-obey-the-sum-of-Proposition-3-data-and-forcing-products",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:norm_sum_le",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-equation-54-and-Proposition-3-corollary",
  caveat @ "claim:finite-norm-sum-closure-under-componentwise-Proposition-3-premises-not-the-concrete-Leray-projection-or-Riesz-transform-identity"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_add where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_add where
  formalizes @ "claim:the-rest-energy-subtracted-positive-or-negative-frequency-Fourier-propagator-obeys-the-exact-time-composition-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Complex.exp_add",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-40-42",
  caveat @ "claim:exact-group-law-for-the-constructed-time-slice-L2-propagator-not-strong-continuity-generator-identification-or-a-spacetime-Strichartz-estimate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedEvolution where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedEvolution where
  formalizes @ "claim:the-rest-energy-subtracted-KGM-Fourier-propagator-is-an-exact-L2-isometry",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-40-42",
  caveat @ "claim:exact-Plancherel-L2-norm-conservation-for-a-unit-modulus-multiplier-not-a-proof-of-the-paper's-sharp-wave-L4-bound"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmRestSubtractedEvolution where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmRestSubtractedEvolution where
  formalizes @ "claim:the-concrete-rest-energy-subtracted-KGM-propagator-preserves-every-native-Bessel-potential-Hs-norm",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-40-42",
  caveat @ "claim:exact-time-slice-Hs-conservation-for-the-linear-Fourier-flow-not-dispersive-decay-bilinear-null-form-control-or-nonlinear-well-posedness"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto_zero where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto_zero where
  formalizes @ "claim:the-concrete-rest-energy-subtracted-KGM-propagator-recovers-every-L2-initial-datum-strongly-at-time-zero",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.tendsto_integral_filter_of_dominated_convergence",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-40-42",
  caveat @ "claim:genuine-strong-L2-continuity-derived-by-dominated-convergence-not-pointwise-Carleson-recovery-generator-domain-identification-or-an-L4-Strichartz-bound"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto where
  formalizes @ "claim:the-unitary-KGM-propagator-is-strongly-continuous-at-every-real-time",
  epistemic_status @ "risky",
  supported_by @ "lean:ContinuousLinearEquiv.continuous",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-formulas-40-42",
  caveat @ "claim:all-times-strong-continuity-from-the-group-law-and-time-zero-dominated-convergence-not-by-itself-the-maximal-generator-domain-characterization-proved-separately-below"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedUnitaryC0Group]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group where
  formalizes @ "claim:the-rest-energy-subtracted-Fourier-flow-is-a-complex-linear-unitary-C0-group-on-L2-R3",
  epistemic_status @ "risky",
  supported_by @ "lean:LinearIsometryEquiv",
  supported_by @ "lean:MeasureTheory.tendsto_integral_filter_of_dominated_convergence",
  caveat @ "claim:bundled-unitary-C0-group-certificate-with-the-exact-maximal-multiplier-domain-and-generator-characterization-proved-separately-below"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.hasDerivAt_kgmRestSubtractedPhase where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhase,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticSymbol]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.hasDerivAt_kgmRestSubtractedPhase where
  formalizes @ "claim:the-rest-energy-subtracted-Fourier-phase-has-exact-time-derivative-i-sigma-Kc-times-the-phase",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:HasDerivAt.cexp",
  caveat @ "claim:exact-frequencywise-complex-exponential-derivative-not-by-itself-the-strong-L2-maximal-domain-result-proved-separately-below"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope_tendsto where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticSymbol]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope_tendsto where
  formalizes @ "claim:the-punctured-time-difference-quotient-of-the-dephased-phase-converges-frequencywise-to-i-sigma-Kc",
  epistemic_status @ "risky",
  supported_by @ "lean:HasDerivAt.tendsto_slope_zero",
  caveat @ "claim:genuine-punctured-filter-limit-at-each-frequency-not-an-interchange-of-limit-and-L2-integration"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedPhaseSlope_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticSymbol]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedPhaseSlope_le where
  formalizes @ "claim:every-nonzero-time-phase-difference-quotient-is-uniformly-dominated-by-absolute-sigma-Kc",
  epistemic_status @ "risky",
  supported_by @ "lean:Complex.norm_exp_I_mul_ofReal_sub_one",
  supported_by @ "lean:Real.abs_sin_le_abs",
  caveat @ "claim:sharp-frequencywise-dominator-needed-for-the-L2-generator-proof-not-by-itself-integrability-or-maximal-domain-identification"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGenerator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator where
  formalizes @ "claim:every-datum-in-the-exact-rest-subtracted-energy-multiplier-domain-has-the-strong-frequency-space-generator-limit",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto",
  supported_by @ "lean:MeasureTheory.tendsto_integral_filter_of_dominated_convergence",
  caveat @ "claim:sufficiency-on-the-exact-symbol-weighted-L2-domain-with-necessity-and-limit-uniqueness-proved-by-the-following-maximal-domain-characterization"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator where
  formalizes @ "claim:the-exact-maximal-strong-generator-domain-is-the-domain-of-a-genuine-unbounded-partial-linear-frequency-operator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:LinearPMap",
  caveat @ "claim:exact-packaging-of-the-proved-maximal-multiplier-domain-with-density-and-closability-established-separately-but-not-resolvent-surjectivity"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg where
  formalizes @ "claim:the-maximal-frequency-generator-multiplier-i-sigma-times-Ec-minus-c-squared-is-formally-skew-adjoint-in-the-continuum-L2-pairing",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.L2.inner_def",
  caveat @ "claim:genuine-formal-adjoint-pairing-on-the-maximal-domain-not-yet-equality-with-the-Hilbert-space-adjoint-which-also-requires-the-maximal-adjoint-domain-proof"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain where
  formalizes @ "claim:bounded-symbol-truncations-prove-the-maximal-frequency-generator-domain-is-dense-in-continuum-L2",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.tendsto_lintegral_of_dominated_convergence'",
  caveat @ "claim:genuine-density-of-the-exact-maximal-domain-without-assuming-H1-regularity-not-yet-an-adjoint-domain-equality"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isUnbounded where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isUnbounded where
  formalizes @ "claim:the-maximal-frequency-generator-is-a-densely-defined-closable-partial-linear-operator",
  epistemic_status @ "risky",
  supported_by @ "lean:LinearPMap.isClosable_of_exists_dense_formalAdjoint",
  caveat @ "claim:unbounded-operator-in-the-repository-sense-dense-domain-and-closability-not-the-separate-claim-that-no-global-operator-norm-bound-exists"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_frequencyOperator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_frequencyOperator where
  formalizes @ "claim:the-concrete-unitary-C0-frequency-flow-has-the-bundled-maximal-partial-operator-as-its-strong-infinitesimal-generator",
  epistemic_status @ "risky",
  supported_by @ "lean:Filter.Tendsto",
  caveat @ "claim:operator-level-strong-generator-identification-on-the-exact-domain-not-an-application-of-Stone's-theorem-or-a-nonlinear-KGM-existence-result"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_physicalGeneratorOperator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhysicalGeneratorOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_physicalGeneratorOperator where
  formalizes @ "claim:Plancherel-conjugation-bundles-the-physical-space-maximal-generator-and-identifies-it-as-the-strong-generator-of-the-dephased-C0-group",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.fourierTransformₗᵢ",
  caveat @ "claim:genuine-physical-space-partial-operator-and-strong-generator-on-its-exact-domain-not-a-nonlinear-KGM-well-posedness-or-scattering-result"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_exists_tendsto_iff where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_exists_tendsto_iff where
  formalizes @ "claim:a-strong-frequency-space-difference-quotient-limit-exists-if-and-only-if-the-datum-lies-in-the-exact-maximal-multiplier-domain",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto",
  supported_by @ "lean:tendsto_nhds_unique",
  caveat @ "claim:exact-maximal-domain-characterization-for-the-concrete-dephased-linear-KGM-group-not-self-adjointness-of-a-bundled-unbounded-partial-operator-or-nonlinear-KGM-well-posedness"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_exists_tendsto_iff where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_exists_tendsto_iff where
  formalizes @ "claim:the-physical-space-strong-generator-domain-is-exactly-the-Plancherel-conjugate-maximal-Fourier-multiplier-domain",
  epistemic_status @ "risky",
  supported_by @ "lean:ContinuousFourier.continuous_fourier",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  caveat @ "claim:coordinate-free-L2-Plancherel-equivalence-of-strong-generator-existence-not-a-self-adjointness-essential-spectrum-or-nonlinear-evolution-theorem"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_generator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_generator where
  formalizes @ "claim:the-frequency-space-L2-difference-quotient-converges-strongly-on-H1-to-i-sigma-times-the-rest-subtracted-energy-multiplier",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.tendsto_integral_filter_of_dominated_convergence",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  caveat @ "claim:genuine-strong-L2-generator-limit-on-the-native-H1-subdomain-specializing-the-separately-proved-exact-maximal-domain-characterization"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_generator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_generator where
  formalizes @ "claim:the-physical-space-dephased-KGM-C0-group-has-strong-H1-generator-i-sigma-times-Ec-of-D-minus-c-squared",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.fourierTransformₗᵢ",
  supported_by @ "lean:IsScalarTower.algebraMap_smul",
  caveat @ "claim:physical-space-H1-specialization-of-the-separately-proved-maximal-domain-equivalence-not-a-self-adjointness-or-nonlinear-KGM-evolution-claim"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group_with_H1Generator where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedUnitaryC0Group,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group_with_H1Generator where
  formalizes @ "claim:combined-unitary-C0-group-and-strong-H1-infinitesimal-generator-certificate-for-the-dephased-continuum-flow",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_generator",
  caveat @ "claim:combined-C0-group-and-H1-generator-corollary-with-the-exact-maximal-domain-equivalence-recorded-separately-not-a-nonlinear-evolution-certificate"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_c_mul_sobolevNorm_one where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_c_mul_sobolevNorm_one where
  formalizes @ "claim:lemma-3-iii-the-continuum-rest-energy-subtracted-operator-maps-H1-R3-to-L2-R3-with-bound-c",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-lemma-3",
  caveat @ "claim:genuine-linear-continuum-H1-to-L2-pseudodifferential-bound-not-a-nonlinear-KGM-well-posedness-result"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_half_sobolevNorm_two where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator]

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_half_sobolevNorm_two where
  formalizes @ "claim:lemma-3-iv-the-continuum-rest-energy-subtracted-operator-maps-H2-R3-to-L2-R3-uniformly-with-bound-one-half",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.Lp.norm_fourier_eq",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-lemma-3",
  caveat @ "claim:genuine-linear-continuum-H2-to-L2-uniform-pseudodifferential-bound-not-the-paper's-bilinear-null-form-or-global-existence-theorem"

zil_file_contract physlib.kgmSchrodingerPoissonFourierMode where
  promises "The Fourier and continuum pseudodifferential layers of the Klein-Gordon-Maxwell nonrelativistic limit: the minimally coupled positive/negative-frequency split reconstructs the scalar and covariant temporal data; the exact continuum Ec and Ec-c-squared symbols satisfy all four bounds of Lemma 3; Plancherel conjugation constructs the genuine Ec-inverse L2-to-H1 and L2-to-homogeneous-H1 operator and the rest-energy-subtracted H1-to-L2 and H2-to-L2 operators with their quantitative bounds; the concrete rest-energy-subtracted Fourier propagator is a complex-linear unitary C0 group with exact time composition, L2 and native Hs conservation, and strong continuity at every time; its exact maximal symbol-weighted L2 generator domain is dense by bounded-symbol truncation, its frequency operator is closable and hence an unbounded operator in the repository sense, and Plancherel conjugation supplies the genuine physical partial operator; the strong difference quotients converge to these bundled operators in frequency and physical space, with the native H1 theorem as a quantitative corollary; the spatial null-form cross-product symbol satisfies equation 57; equation 56 is realized by genuine four-dimensional Schwartz convolution; the actual inverse-gradient null integral equals the multiplier-applied convolution and has the unconditional half-derivative lintegral majorant; Plancherel and Holder close the integrated equation-58 L2 estimate under its explicit Fourier-majorization premise; the Duhamel homogeneous and forcing pieces combine into Corollary 48, which closes Proposition 3 and its finite-component equation-54 corollary under explicit sharp-wave and Fourier-majorization data; rest-energy dephasing preserves the signed diagonal charge density; and a vanishing oscillatory source remainder yields the Schrodinger-Poisson source."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmCovariantTemporalDatum",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseEnergyOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhysicalGeneratorOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity"]
  forbids_substitutes ["claiming the explicit Fourier-majorization or sharp-wave L4 fields of the Duhamel carrier follow from the constructed unitary C0 propagator merely because its group law, norm conservation and strong continuity are proved",
    "upgrading the bundled operator's proved formal skew-adjoint pairing to equality with its Hilbert-space adjoint without a maximal adjoint-domain proof",
    "claiming the oscillatory charge remainder vanishes without the explicit convergence premise",
    "claiming global-in-time KGM convergence from a finite-time-slab limit"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmFrequencyMode_add,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.energy_mul_kgmFrequencyMode_sub,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseEnergySymbol_le_inv_c_sq,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.bessel_one_mul_kgmInverseEnergySymbol_le_inv_c,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticSymbol_le_c_mul_norm,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticSymbol_le_norm_sq_div_two,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution_apply,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmInverseSpatialNormNullComponent_mul_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral_eq_multiplier_mul,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.enorm_kgmInverseSpatialNullFourierIntegral_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmEquation58Output_le_l4_mul_l4,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.norm_halfDerivative_le_totalControl,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmProposition3Output_le_data_forcing,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_sum_kgmProposition3Outputs_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_add,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.hasDerivAt_kgmRestSubtractedPhase,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedPhaseSlope_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isUnbounded,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_frequencyOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_exists_tendsto_iff,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_physicalGeneratorOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_exists_tendsto_iff,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group_with_H1Generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmInverseEnergyOperator_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.homogeneousSobolevOneNorm_kgmInverseEnergyOperator_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_c_mul_sobolevNorm_one,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_half_sobolevNorm_two,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity_dephase,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmChargeSource_tendsto_schrodingerPoisson]

/- ZIL-END -/
