/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Module
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-!
# The inverted oscillator: non-Hermitian ladder algebra and minimum uncertainty

Formalizes the *exact* algebraic core of R. Zerimeche, R. Moufok, N. Amaouche, M. Maamache, *Inverted
oscillator: pseudo-hermiticity and coherent states* (arXiv:2204.10804). The inverted (repulsive) oscillator
`Hʳ = p²/2m − ½mω²x²` is the harmonic oscillator under `ω → iω`; its **non-Hermitian ladder operators**
`(A, Ā)` are built from the Hermitian ones `(a, a†)` (with `[a, a†] = 1`) by

  `A = a + i·a†`,   `Ā = ½(a† + i·a)`   (`loweringA`, `raisingA`).

**§A — the inverted ladder algebra.** Despite `A` not being the adjoint of `Ā`, they satisfy the *same*
canonical commutation relation as the harmonic pair:

  `[A, Ā] = A Ā − Ā A = 1`   (`invertedLadder_comm`),

and their symmetric product reconstructs the inverted Hamiltonian:

  `Ā A + A Ā = i·(a†² + a²)`   (`invertedLadder_anticomm`),
  `i·(Ā A + A Ā) = −(a†² + a²)`   (`invertedLadder_hamiltonian`),

so `Hʳ = (iℏω/2)(Ā A + A Ā) = −(ℏω/2)(a†² + a²)` (Eqs 12, 29) — the `ω → iω` image of `Hᵒˢ = (ℏω/2)(a†a +
a a†)`. (Over a `ℂ`-algebra, `i = Complex.I` enters by scalar multiplication.)

**§B — minimum uncertainty.** The inverted coherent states saturate the Heisenberg bound (Eqs 62–63): with
`ΔX = √(ℏ/2mω)` and `ΔP = √(mωℏ/2)`,

  `ΔX · ΔP = ℏ/2`   (`inverted_coherent_minimum_uncertainty`),

so they are minimum-uncertainty wave packets — the "quasi-classical" states whose averages follow the
classical (hyperbolically unstable) trajectory, even though the inverted oscillator is unbound.

This is the pseudo-Hermitian / `ω → iω` companion to `OperatorAlgebra.ZetaInvertedOscillator` (whose monodromy
`e^{±ωt}` is the same hyperbolic instability) and the repo's complex-action / Bogoliubov layer.

## References

* Zerimeche–Moufok–Amaouche–Maamache (2022), Eqs 12, 28–31, 62–63; Mostafazadeh (pseudo-Hermiticity).
  Carriers: `Mathlib` (`Complex.I`, `Real.sqrt`); cf. `OperatorAlgebra.ZetaInvertedOscillator`,
  `CollisionOperatorSl2.LinearBoltzmannOperator` (the `[∇, v] = 1` ladder pattern).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorPseudoHermitian

open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics


variable {R : Type*} [Ring R] [Algebra ℂ R] (a ad : R)

/-- **The inverted-oscillator lowering operator** `A = a + i·a†` (Eq 30, non-Hermitian). -/
noncomputable def loweringA : R := a + Complex.I • ad

/-- **The inverted-oscillator raising operator** `Ā = ½(a† + i·a)` (Eq 31). -/
noncomputable def raisingA : R := (1 / 2 : ℂ) • (ad + Complex.I • a)

/-- **[The inverted ladder satisfies the CCR] `[A, Ā] = 1`.** Although `A` is not the adjoint of `Ā`, the
commutator `A Ā − Ā A` equals `1`, exactly as for the Hermitian pair — the `i²`-terms cancel and `[a, a†] = 1`
remains. -/
lemma invertedLadder_comm (hcomm : a * ad - ad * a = 1) :
    loweringA a ad * raisingA a ad - raisingA a ad * loweringA a ad = 1 := by
  have hsub : a * ad = ad * a + 1 := by rw [← hcomm]; abel
  simp only [loweringA, raisingA, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_smul, hsub]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

/-- **[The symmetric product reconstructs `Hʳ`] `Ā A + A Ā = i·(a†² + a²)`.** -/
lemma invertedLadder_anticomm (hcomm : a * ad - ad * a = 1) :
    raisingA a ad * loweringA a ad + loweringA a ad * raisingA a ad
      = Complex.I • (ad * ad + a * a) := by
  have hsub : a * ad = ad * a + 1 := by rw [← hcomm]; abel
  simp only [loweringA, raisingA, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_smul, hsub]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

/-- **[The inverted Hamiltonian] `i·(Ā A + A Ā) = −(a†² + a²)`.** Hence `Hʳ = (iℏω/2)(Ā A + A Ā) =
−(ℏω/2)(a†² + a²)` — the `ω → iω` image of the harmonic oscillator. -/
lemma invertedLadder_hamiltonian (hcomm : a * ad - ad * a = 1) :
    Complex.I • (raisingA a ad * loweringA a ad + loweringA a ad * raisingA a ad)
      = -(ad * ad + a * a) := by
  rw [invertedLadder_anticomm a ad hcomm, smul_smul, Complex.I_mul_I, neg_one_smul]


/-- **[Inverted coherent states are minimum-uncertainty] `ΔX · ΔP = ℏ/2`.** With `ΔX = √(ℏ/2mω)` and
`ΔP = √(mωℏ/2)` (Eqs 62–63), the product saturates the Heisenberg bound: the inverted coherent states are
quasi-classical minimum-uncertainty wave packets, even though the inverted oscillator is unbound. -/
lemma inverted_coherent_minimum_uncertainty {ℏ m ω : ℝ} (hℏ : 0 ≤ ℏ) (hm : 0 < m) (hω : 0 < ω) :
    Real.sqrt (ℏ / (2 * m * ω)) * Real.sqrt (m * ω * ℏ / 2) = ℏ / 2 := by
  rw [← Real.sqrt_mul (by positivity)]
  rw [show ℏ / (2 * m * ω) * (m * ω * ℏ / 2) = (ℏ / 2) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-!

Beyond the static ladder algebra, the *time-dependent* signature of the inverted oscillator is exponential
energy/variance growth `E(t) = E₀·cosh(2κt) ~ (E₀/2)e^{2κt}` — the unstable runaway with rate `2κ`. This is the
classical/quantum image of the entropic instability: the growth rate `2κ` is the Lyapunov exponent
`Λ ∝ ⟨H_I⟩`, the imaginary-energy / entropy-production rate of the complex-action sector. -/

/-- **The inverted-oscillator energy growth** `E(t) = E₀·cosh(2κt)` — the energy/variance under inverted
(unstable) evolution, growing hyperbolically with instability rate `2κ`. -/
noncomputable def invertedEnergyGrowth (E₀ κ t : ℝ) : ℝ := E₀ * Real.cosh (2 * κ * t)

/-- **[Energy never drops below its initial value]** `E₀ ≤ E(t)` (for `E₀ ≥ 0`), since `cosh ≥ 1`. -/
lemma invertedEnergyGrowth_ge_init (E₀ κ t : ℝ) (hE : 0 ≤ E₀) :
    E₀ ≤ invertedEnergyGrowth E₀ κ t := by
  unfold invertedEnergyGrowth
  have hpos : 0 < Real.exp (2 * κ * t) := Real.exp_pos _
  have hprod : Real.exp (2 * κ * t) * Real.exp (-(2 * κ * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : (1 : ℝ) ≤ Real.cosh (2 * κ * t) := by
    rw [Real.cosh_eq]
    nlinarith [hpos, hprod, sq_nonneg (Real.exp (2 * κ * t) - 1)]
  nlinarith [h1, hE]

/-- **[Exponential instability] `(E₀/2)·e^{2κt} ≤ E(t)`** — the energy grows at least exponentially with rate
`2κ`, the inverted-oscillator runaway. The rate `2κ = Λ` is the Lyapunov / imaginary-energy rate `∝ ⟨H_I⟩`. -/
lemma invertedEnergyGrowth_exp_lower (E₀ κ t : ℝ) (hE : 0 ≤ E₀) :
    E₀ / 2 * Real.exp (2 * κ * t) ≤ invertedEnergyGrowth E₀ κ t := by
  unfold invertedEnergyGrowth
  rw [Real.cosh_eq]
  nlinarith [mul_nonneg hE (Real.exp_pos (-(2 * κ * t))).le]

/-! ## C. Spectral output of inverted-oscillator growth -/

/-- Spectral power obtained by evaluating a white-noise output rule on the
existing IQHO hyperbolic energy growth. -/
noncomputable def iqhoGrowthOutputSpectrum (sigma2 E0 kappa t : ℝ) : ℝ :=
  outputSpectrum sigma2
    ((invertedEnergyGrowth E0 kappa t : ℝ) : ℂ)

/-- IQHO growth spectral power is nonnegative for nonnegative input variance. -/
lemma iqhoGrowthOutputSpectrum_nonneg
    {sigma2 : ℝ} (hsigma : 0 ≤ sigma2) (E0 kappa t : ℝ) :
    0 ≤ iqhoGrowthOutputSpectrum sigma2 E0 kappa t := by
  exact outputSpectrum_nonneg hsigma
    ((invertedEnergyGrowth E0 kappa t : ℝ) : ℂ)

/-- IQHO growth spectral power is the input power times the squared hyperbolic
growth factor. -/
lemma iqhoGrowthOutputSpectrum_eq
    (sigma2 E0 kappa t : ℝ) :
    iqhoGrowthOutputSpectrum sigma2 E0 kappa t =
      sigma2 * (invertedEnergyGrowth E0 kappa t) ^ 2 := by
  unfold iqhoGrowthOutputSpectrum outputSpectrum
  rw [Complex.normSq_ofReal]
  ring

/-- For nonnegative input power and nonnegative initial energy, IQHO hyperbolic
growth increases the spectral output relative to the initial line. -/
lemma iqhoGrowthOutputSpectrum_ge_initial
    {sigma2 E0 : ℝ} (hsigma : 0 ≤ sigma2) (hE0 : 0 ≤ E0)
    (kappa t : ℝ) :
    iqhoGrowthOutputSpectrum sigma2 E0 0 0
      ≤ iqhoGrowthOutputSpectrum sigma2 E0 kappa t := by
  rw [iqhoGrowthOutputSpectrum_eq, iqhoGrowthOutputSpectrum_eq]
  simp [invertedEnergyGrowth]
  have hgrowth : E0 ≤ E0 * Real.cosh (2 * kappa * t) :=
    invertedEnergyGrowth_ge_init E0 kappa t hE0
  have hgrowth_nonneg : 0 ≤ E0 * Real.cosh (2 * kappa * t) :=
    le_trans hE0 hgrowth
  have hdiff : 0 ≤ E0 * Real.cosh (2 * kappa * t) - E0 :=
    sub_nonneg.mpr hgrowth
  have hsum : 0 ≤ E0 * Real.cosh (2 * kappa * t) + E0 :=
    add_nonneg hgrowth_nonneg hE0
  have hprod : 0 ≤
      (E0 * Real.cosh (2 * kappa * t) - E0) *
        (E0 * Real.cosh (2 * kappa * t) + E0) :=
    mul_nonneg hdiff hsum
  have hsq : E0 ^ 2 ≤ (E0 * Real.cosh (2 * kappa * t)) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq hsigma

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.InvertedOscillatorPseudoHermitian

end
