/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

/-!
# Equipartition — `⟨E⟩ = ½·kB·T` for a quadratic degree of freedom

Phase-5 follow-up (B7), leveraging:

* **physlib's `CanonicalEnsemble`**
  (`Physlib.StatisticalMechanics.CanonicalEnsemble.Basic`)
  for the structure, Boltzmann measure `μBolt`, normalised distribution
  `μProd`, and `meanEnergy = ∫ energy ∂μProd`.
* **Mathlib's Gaussian integral**
  (`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral.integral_gaussian`)
  for the partition-function value `Z(T) = √(2π·kB·T/k)`.
* **Mathlib's `gaussianReal`**
  (`Mathlib.Probability.Distributions.Gaussian.Real`)
  for the centered Gaussian measure with explicit variance `v`.
* **Mathlib's `variance_id_gaussianReal` + `integral_id_gaussianReal`**
  (`Mathlib.Probability.Variance` + Gaussian/Real)
  for the **second moment** `⟨q²⟩ = v` of a centered Gaussian.

## Structure of the equipartition derivation

For `H(q) = ½·k·q²` and Boltzmann measure `μBolt T = volume.withDensity
(q ↦ ofReal (exp(−β·k·q²/2)))`, with `β = 1/(kB·T)`:

1. **Partition function.**  `∫ exp(−β·k·q²/2) dq = √(2π·kB·T/k)`,
   the load-bearing Gaussian-integral identity
   (`gaussian_partition_function_value`), proven directly via
   `Mathlib.integral_gaussian`.

2. **Measure equivalence (deferred).**  After normalising by `Z`,
   `μProd T` equals `gaussianReal 0 v` with `v = kB·T/k`.  This step
   is the measure-theoretic plumbing (`Measure.withDensity_smul`,
   `gaussianPDF_def`, `gaussianReal_of_var_ne_zero`) — a follow-up
   commit will establish it.

3. **Second moment.**  Under `gaussianReal 0 v`,
   `⟨q²⟩ = Var(id) + (∫ id)² = v + 0 = v` by
   `Mathlib.variance_id_gaussianReal`,
   `Mathlib.integral_id_gaussianReal`, and `variance_eq_sub`.

4. **Equipartition.**  `⟨H⟩ = (k/2)·⟨q²⟩ = (k/2)·v = (k/2)·(kB·T/k)
   = ½·kB·T`.

## Status of this commit

Contents:

* `QuadraticDOFEnsemble` — the structure (full, real proof).
* `gaussian_partition_function_value` — step (1), fully proven.
* `gaussian_partition_function_pos` — positivity, fully proven.

The full equipartition theorem (`meanEnergy T = ½·kB·T`) needs the
measure-equivalence step (2); once that is provided, the chain
(1)–(4) closes in a handful of `rw`s using the Mathlib variance
lemmas referenced above.  Per the project's no-placeholder-proof convention,
the equipartition theorem **statement is not asserted here** —
only the scaffold.  The follow-up commit can land both the
measure-equivalence step and the equipartition theorem together.

No new axioms beyond Mathlib's std-3 closure.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.StatisticalMechanics.Equipartition

open MeasureTheory Real Constants

/-! ## §1 — Quadratic-DOF canonical ensemble -/

/-- **Quadratic-DOF canonical ensemble.**  A particle on `ℝ` whose
energy is `H(q) = ½·k·q²` for some spring constant `k > 0`.  The
underlying microstate measure is Lebesgue (volume); the energy is
continuous (hence measurable).

This is the canonical model for a single classical harmonic-oscillator
position degree of freedom (or, by symmetry, a single momentum
component `p²/(2m)` with `1/(2m)` playing the role of `k/2`). -/
noncomputable def QuadraticDOFEnsemble (k : ℝ) (_hk : 0 < k) :
    CanonicalEnsemble ℝ where
  energy q := (1 / 2) * k * q ^ 2
  dof := 1
  phaseSpaceunit := 1
  hPos := one_pos
  energy_measurable := by fun_prop

@[simp] theorem QuadraticDOFEnsemble_energy (k : ℝ) (hk : 0 < k) (q : ℝ) :
    (QuadraticDOFEnsemble k hk).energy q = (1 / 2) * k * q ^ 2 := rfl

@[simp] theorem QuadraticDOFEnsemble_dof (k : ℝ) (hk : 0 < k) :
    (QuadraticDOFEnsemble k hk).dof = 1 := rfl

/-! ## §2 — Partition function via `Mathlib.integral_gaussian`

For `k > 0` and `β > 0`,

  `Z = ∫ exp(−(β·k/2) · q²) dq  =  √(2π / (β·k))`,

a direct rewrite of `Mathlib.integral_gaussian` with `b = β·k/2`.
This is the load-bearing physics input for the equipartition
derivation `⟨H⟩ = −∂(log Z)/∂β = 1/(2β) = ½·kB·T`. -/

/-- **Partition-function value for the quadratic-DOF ensemble.**  The
Boltzmann integral `∫ exp(−(βk/2)·q²) dq` equals the Gaussian
normalisation `√(2π/(β·k))`.

This is the `Z(T)` of the canonical ensemble at inverse temperature
`β = 1/(kB·T)`, prior to dimensional normalisation by
`phaseSpaceunit`. -/
theorem gaussian_partition_function_value
    (k β : ℝ) (_hk : 0 < k) (_hβ : 0 < β) :
    ∫ q : ℝ, Real.exp (- (β * k / 2) * q ^ 2) = √(2 * π / (β * k)) := by
  rw [integral_gaussian (β * k / 2)]
  congr 1
  field_simp

/-- **Strict positivity of the partition function.**  When `β·k > 0`
(positive temperature and positive spring constant), the Boltzmann
integral is strictly positive. -/
theorem gaussian_partition_function_pos
    (k β : ℝ) (hk : 0 < k) (hβ : 0 < β) :
    0 < ∫ q : ℝ, Real.exp (- (β * k / 2) * q ^ 2) := by
  rw [gaussian_partition_function_value k β hk hβ]
  apply Real.sqrt_pos.mpr
  have : 0 < β * k := mul_pos hβ hk
  positivity

/-! ## §3 — Second-moment identity from `Mathlib.gaussianReal`

The conditional equipartition theorem below routes through:

* `Mathlib.Probability.Variance.variance_eq_sub`
  — `Var(X) = ⟨X²⟩ − ⟨X⟩²` for `MemLp X 2 μ` under a probability
  measure.
* `Mathlib.Probability.Distributions.Gaussian.Real.variance_id_gaussianReal`
  — `Var[id; gaussianReal μ v] = v`.
* `Mathlib.Probability.Distributions.Gaussian.Real.integral_id_gaussianReal`
  — `∫ x ∂gaussianReal μ v = μ`.

Composing these three yields `⟨q²⟩ = v` under `gaussianReal 0 v`. -/

/-- **Second-moment identity under a centered Gaussian** (extracted as
its own lemma for clarity).  Under the centered Gaussian measure
`gaussianReal 0 v`, the second moment of the identity equals `v`. -/
theorem integral_sq_gaussianReal_zero (v : NNReal) (_hv : v ≠ 0)
    (hL2 : MemLp (fun x : ℝ => x) 2 (ProbabilityTheory.gaussianReal 0 v)) :
    ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 v) = (v : ℝ) := by
  -- variance_eq_sub: Var(X) = ⟨X²⟩ − ⟨X⟩²
  have hvar := ProbabilityTheory.variance_eq_sub
                  (μ := ProbabilityTheory.gaussianReal 0 v)
                  (X := fun x : ℝ => x) hL2
  -- Normalise (fun x => x)^2 to fun x => x^2 pointwise inside the integrand.
  simp only [Pi.pow_apply] at hvar
  -- Substitute variance_id_gaussianReal (Var = v) and integral_id_gaussianReal (⟨id⟩ = 0).
  rw [ProbabilityTheory.variance_fun_id_gaussianReal,
      ProbabilityTheory.integral_id_gaussianReal] at hvar
  -- hvar now reads: (v : ℝ) = ∫ x², ... − 0², so the conclusion follows.
  linarith

/-! ## §4 — Measure-equivalence step

The normalised canonical-ensemble distribution `μProd T` of the
quadratic-DOF ensemble coincides with `gaussianReal 0 v` (the centered
real Gaussian measure with variance `v`), where `v = 1/(T.β · k)`.

Proof strategy via `Measure.ext`:
* Evaluate both sides on an arbitrary measurable set `s`.
* `μProd T s = (μBolt T univ)⁻¹ · ∫⁻_s ofReal(exp(−βkq²/2)) ∂volume`.
* `gaussianReal 0 v s = ∫⁻_s ofReal(gaussianPDFReal 0 v q) ∂volume`.
* `gaussianPDFReal 0 v q = Z⁻¹ · exp(−q²/(2v)) = Z⁻¹ · exp(−βkq²/2)`
  with `Z = √(2π·v) = √(2π/(β·k))`.
* `μBolt T univ = ofReal Z` (from `integral_gaussian`).
* `(ofReal Z)⁻¹ · ∫⁻_s ofReal(exp(...)) = ∫⁻_s ofReal(Z⁻¹ · exp(...))`
  (constant pull-out via `lintegral_const_mul` + `ENNReal.ofReal_mul`).
* RHS = LHS.

This step closes the equipartition chain: composed with
`integral_sq_gaussianReal_zero` it yields `⟨H⟩ = (k/2)·v = ½·kB·T`.
-/

/-! ### Pointwise density-equivalence (algebraic content of the measure equivalence)

The Boltzmann density of `QuadraticDOFEnsemble k hk` at inverse
temperature `β = T.β` is `exp(−β·k·q²/2)`.  The `gaussianPDFReal 0 v`
density at variance `v = 1/(β·k)` is

  `(√(2π·v))⁻¹ · exp(−q²/(2v))  =  Z⁻¹ · exp(−β·k·q²/2)`,

with `Z = √(2π/(β·k))` (the partition function).

We isolate the *algebraic* density identity (no measure machinery) as
its own lemma; the measure-level identity then composes this with
`withDensity_congr_ae` + the partition-function value to give the full
`μProd = gaussianReal` equality.
-/

/-- **Density algebraic identity.**  At `v = 1/(β·k)` (β, k > 0), the
Mathlib `gaussianPDFReal 0 v` density rearranges into the inverse
partition function times the bare Boltzmann factor. -/
theorem gaussianPDFReal_eq_inv_Z_mul_boltzmann
    (k β : ℝ) (hk : 0 < k) (hβ : 0 < β) (q : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 ⟨1 / (β * k), by positivity⟩ q
      = (√(2 * π / (β * k)))⁻¹ * Real.exp (- (β * k / 2) * q ^ 2) := by
  unfold ProbabilityTheory.gaussianPDFReal
  have hβk : 0 < β * k := mul_pos hβ hk
  have hv : (0 : ℝ) < 1 / (β * k) := by positivity
  have hβk_ne : (β * k) ≠ 0 := ne_of_gt hβk
  congr 1
  · congr 1; congr 1
    show 2 * π * (1 / (β * k)) = 2 * π / (β * k)
    field_simp
  · congr 1
    show -(q - 0) ^ 2 / (2 * (1 / (β * k))) = -(β * k / 2) * q ^ 2
    field_simp
    ring

/-- **ENNReal density identity** (lift of the algebraic identity to
`ENNReal.ofReal`).  Allows the algebraic identity to be used inside
`withDensity` integrands. -/
theorem ofReal_gaussianPDFReal_eq_inv_Z_mul_boltzmann
    (k β : ℝ) (hk : 0 < k) (hβ : 0 < β) (q : ℝ) :
    ENNReal.ofReal
        (ProbabilityTheory.gaussianPDFReal 0 ⟨1 / (β * k), by positivity⟩ q)
      = ENNReal.ofReal ((√(2 * π / (β * k)))⁻¹)
          * ENNReal.ofReal (Real.exp (- (β * k / 2) * q ^ 2)) := by
  rw [gaussianPDFReal_eq_inv_Z_mul_boltzmann k β hk hβ q,
      ENNReal.ofReal_mul (by positivity)]

/-- **Measure-equivalence step (full).**  The centered Gaussian measure
`gaussianReal 0 v` with `v = 1/(β·k)` equals the inverse-partition-
function multiple of the unnormalised Boltzmann measure
`volume.withDensity (q ↦ exp(−β·k·q²/2))`.

Composes:

* `gaussianReal_of_var_ne_zero` — unfolds `gaussianReal` as `withDensity`.
* `gaussianPDF_def` — unfolds `gaussianPDF` as `ENNReal.ofReal ∘ gaussianPDFReal`.
* `ofReal_gaussianPDFReal_eq_inv_Z_mul_boltzmann` (this file) — the
  density-level algebraic identity.
* `withDensity_smul` — pulls the `ofReal Z⁻¹` factor out as a scalar
  on the measure.

This is the load-bearing connection between Mathlib's `gaussianReal`
and physlib's Boltzmann-measure construction. -/
theorem gaussianReal_eq_inv_Z_smul_boltzmannMeasure
    (k β : ℝ) (hk : 0 < k) (hβ : 0 < β) :
    ProbabilityTheory.gaussianReal 0 ⟨1 / (β * k), by positivity⟩
      = ENNReal.ofReal ((√(2 * π / (β * k)))⁻¹)
          • (MeasureTheory.volume.withDensity
              (fun q => ENNReal.ofReal (Real.exp (- (β * k / 2) * q ^ 2)))) := by
  have hβk : 0 < β * k := mul_pos hβ hk
  have hv_pos : (0 : ℝ) < 1 / (β * k) := by positivity
  have hv_ne : (⟨1 / (β * k), le_of_lt hv_pos⟩ : NNReal) ≠ 0 := by
    intro h
    have hval : (⟨1 / (β * k), le_of_lt hv_pos⟩ : NNReal).val =
                  (0 : NNReal).val := by rw [h]; rfl
    exact ne_of_gt hv_pos hval
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv_ne]
  -- Identify the density: `gaussianPDF 0 v = c • boltzmann_density` pointwise.
  have heq :
      ProbabilityTheory.gaussianPDF 0 ⟨1 / (β * k), le_of_lt hv_pos⟩
        = (ENNReal.ofReal ((√(2 * π / (β * k)))⁻¹)) •
            (fun q => ENNReal.ofReal (Real.exp (- (β * k / 2) * q ^ 2))) := by
    funext q
    show ENNReal.ofReal
            (ProbabilityTheory.gaussianPDFReal 0
              ⟨1 / (β * k), le_of_lt hv_pos⟩ q)
        = _
    exact ofReal_gaussianPDFReal_eq_inv_Z_mul_boltzmann k β hk hβ q
  rw [heq]
  -- Pull the constant factor out of `withDensity`.
  have hmeas :
      Measurable (fun q : ℝ => ENNReal.ofReal (Real.exp (- (β * k / 2) * q ^ 2))) := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    fun_prop
  rw [MeasureTheory.withDensity_smul _ hmeas]

/-! ## §5 — The QuadraticDOF Boltzmann measure matches the canonical-form Gaussian density -/

/-- The Boltzmann measure of `QuadraticDOFEnsemble k hk` at temperature `T`
equals the canonical-form `volume.withDensity (q ↦ ofReal (exp(−(β·k/2)·q²)))`
used in `gaussianReal_eq_inv_Z_smul_boltzmannMeasure`.

The two forms differ only by `ring` rearrangement inside `Real.exp`:
`−T.β · ((1/2)·k·q²) = −(T.β·k/2)·q²`. -/
theorem μBolt_QuadraticDOF_eq_canonical
    (k : ℝ) (hk : 0 < k) (T : Temperature) :
    (QuadraticDOFEnsemble k hk).μBolt T
      = MeasureTheory.volume.withDensity
          (fun q : ℝ =>
            ENNReal.ofReal (Real.exp (- ((T.β : ℝ) * k / 2) * q ^ 2))) := by
  unfold CanonicalEnsemble.μBolt
  congr 1
  funext q
  congr 1
  congr 1
  show -((T.β : ℝ)) * (QuadraticDOFEnsemble k hk).energy q
      = -((T.β : ℝ) * k / 2) * q ^ 2
  simp only [QuadraticDOFEnsemble_energy]
  ring

/-! ## §6 — Full measure equivalence: μProd = gaussianReal -/

/-- **Full measure-equivalence theorem.**  The normalised canonical-ensemble
distribution `μProd T` of `QuadraticDOFEnsemble k hk` at temperature `T` is
exactly the centered Gaussian measure with variance `v = 1/(T.β·k) = kB·T/k`.

This is the load-bearing structural identification connecting physlib's
canonical-ensemble construction to Mathlib's `gaussianReal`. -/
theorem μProd_QuadraticDOFEnsemble_eq_gaussianReal
    (k : ℝ) (hk : 0 < k) (T : Temperature) (hT_pos : 0 < (T.val : ℝ)) :
    (QuadraticDOFEnsemble k hk).μProd T
      = ProbabilityTheory.gaussianReal 0
          ⟨1 / ((T.β : ℝ) * k), by have := Temperature.beta_pos T hT_pos; positivity⟩ := by
  have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT_pos
  have hβk : 0 < (T.β : ℝ) * k := mul_pos hβ hk
  -- The Boltzmann measure in canonical form.
  have hbolt := μBolt_QuadraticDOF_eq_canonical k hk T
  -- The measure-equivalence theorem.
  have hmeq := gaussianReal_eq_inv_Z_smul_boltzmannMeasure k (T.β : ℝ) hk hβ
  -- Combine: gaussianReal 0 v = ofReal Z⁻¹ • μBolt T  (after rewriting via hbolt).
  rw [← hbolt] at hmeq
  -- μProd T = (μBolt T univ)⁻¹ • μBolt T.
  unfold CanonicalEnsemble.μProd
  -- From hmeq, taking Set.univ on both sides:
  --   gaussianReal 0 v univ = (ofReal Z⁻¹) • μBolt T univ.
  -- Since gaussianReal is a probability measure, LHS = 1.
  -- So μBolt T univ = (ofReal Z⁻¹)⁻¹ = ofReal Z.
  -- Hence (μBolt T univ)⁻¹ = (ofReal Z)⁻¹ = ofReal Z⁻¹.
  -- Then μProd T = ofReal Z⁻¹ • μBolt T = gaussianReal 0 v.
  have hZ_pos : 0 < (√(2 * π / ((T.β : ℝ) * k)) : ℝ) := by
    apply Real.sqrt_pos.mpr; positivity
  have hZ_inv_pos : 0 < (√(2 * π / ((T.β : ℝ) * k)))⁻¹ := inv_pos.mpr hZ_pos
  -- Compute μBolt T univ from hmeq: gaussianReal is a probability measure, so applying
  -- to Set.univ yields 1 = ofReal Z⁻¹ * μBolt T univ, hence μBolt T univ = ofReal Z.
  have hZ_ofReal_ne_zero : ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ_pos).ne'
  have hZ_ofReal_ne_top : ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have huniv : (QuadraticDOFEnsemble k hk).μBolt T Set.univ
      = ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k))) := by
    have h1 : ProbabilityTheory.gaussianReal 0
        ⟨1 / ((T.β : ℝ) * k), by positivity⟩ Set.univ = 1 :=
      (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _).measure_univ
    rw [hmeq, Measure.smul_apply, smul_eq_mul,
        ENNReal.ofReal_inv_of_pos hZ_pos] at h1
    -- h1: (ofReal Z)⁻¹ * μBolt T univ = 1.
    -- Multiply both sides by ofReal Z.
    have h2 : ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k)))
        * ((ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k))))⁻¹
            * (QuadraticDOFEnsemble k hk).μBolt T Set.univ)
      = ENNReal.ofReal (√(2 * π / ((T.β : ℝ) * k))) * 1 := by rw [h1]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hZ_ofReal_ne_zero hZ_ofReal_ne_top,
        one_mul, mul_one] at h2
    exact h2
  -- Now μProd T = (ofReal Z)⁻¹ • μBolt T = ofReal Z⁻¹ • μBolt T = gaussianReal 0 v.
  rw [huniv]
  rw [← ENNReal.ofReal_inv_of_pos hZ_pos]
  exact hmeq.symm

/-! ## §7 — The equipartition theorem `⟨H⟩ = ½·kB·T` -/

/-- **The equipartition theorem for a single quadratic degree of freedom.**

For `H(q) = ½·k·q²` (`k > 0`) at temperature `T > 0`, the mean energy in
the canonical ensemble is exactly `½·kB·T`.

Composes the full chain shipped in this module:

* `μProd_QuadraticDOFEnsemble_eq_gaussianReal` — measure-equivalence step
  (this file).
* `MeasureTheory.integral_const_mul` — pulls the constant `(1/2)·k` out
  of the integral.
* `integral_sq_gaussianReal_zero` — `⟨q²⟩ = v` under the centered Gaussian
  (this file).
* `Physlib.Thermodynamics.Temperature.β` definition — `β = 1/(kB·T)`
  gives the substitution `v = kB·T/k`.

The final algebraic step `(k/2) · (kB·T/k) = ½·kB·T` follows by
`field_simp` + `ring`. -/
theorem equipartition_quadraticDOF
    (k : ℝ) (hk : 0 < k) (T : Temperature) (hT_pos : 0 < T.val) :
    (QuadraticDOFEnsemble k hk).meanEnergy T = (1 / 2) * kB * T.val := by
  have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT_pos
  have hβk_pos : 0 < (T.β : ℝ) * k := mul_pos hβ hk
  -- Step 1: meanEnergy = ∫ energy ∂μProd, then μProd = gaussianReal 0 v.
  rw [CanonicalEnsemble.meanEnergy,
      μProd_QuadraticDOFEnsemble_eq_gaussianReal k hk T hT_pos]
  -- Step 2: Unfold energy as (1/2)·k·q²; rewrite as ((1/2)·k)·q² and pull out the constant.
  simp only [QuadraticDOFEnsemble_energy]
  have h_assoc : (fun q : ℝ => (1 / 2) * k * q ^ 2)
      = fun q : ℝ => ((1 / 2) * k) * q ^ 2 := by
    funext q; ring
  rw [h_assoc, MeasureTheory.integral_const_mul]
  -- Goal: ((1/2) * k) * ∫ q, q² ∂(gaussianReal 0 ⟨1/(T.β·k), _⟩) = (1/2) * kB * T.val
  -- Step 3: ⟨q²⟩ = v = 1/(T.β·k) by integral_sq_gaussianReal_zero.
  have hv_ne : (⟨1 / ((T.β : ℝ) * k), by positivity⟩ : NNReal) ≠ 0 := by
    intro h
    have hval : (⟨1 / ((T.β : ℝ) * k), by positivity⟩ : NNReal).val =
                  (0 : NNReal).val := by rw [h]; rfl
    exact ne_of_gt (by positivity : (0 : ℝ) < 1 / ((T.β : ℝ) * k)) hval
  rw [integral_sq_gaussianReal_zero _ hv_ne
        (ProbabilityTheory.memLp_id_gaussianReal 2)]
  -- Goal: ((1/2) * k) * ↑⟨1/(T.β·k), _⟩ = (1/2) * kB * T.val
  -- Step 4: unfold the Subtype coercion, then use T.β = 1/(kB·T.val).
  show (1 / 2 * k) * (1 / ((T.β : ℝ) * k)) = 1 / 2 * kB * T.val
  have hβ_def : (T.β : ℝ) = 1 / (kB * T.val) := by
    show (T.β : NNReal).val = 1 / (kB * T.val)
    unfold Temperature.β
    rfl
  rw [hβ_def]
  have hkB_T : 0 < kB * T.val := mul_pos kB_pos hT_pos
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hkB_T_ne : kB * T.val ≠ 0 := ne_of_gt hkB_T
  field_simp

end Physlib.StatisticalMechanics.Equipartition

end
