/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
public import Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.MeasureTheory.Integral.Prod
meta import Zil

/-!
# The Cameron–Martin–Maruyama–Girsanov formula for a Bilaplacian (Léandre 2012)

Formalizes the algebraic core of *R. Léandre, "A Path-Integral Approach to the
Cameron–Martin–Maruyama–Girsanov Formula Associated to a Bilaplacian," J. Funct. Spaces Appl. 2012*: the
Itô tables for the Laplacian and the Bilaplacian, the exponential-martingale Wiener product, and the
Cameron–Martin–Maruyama–Girsanov change of measure, and the polynomial form of Léandre's perturbed
bilaplacian generator.

* **§A — the Itô table for the Bilaplacian** (Eqs. 1.11–1.12, 2.11). The differentials `dw^i` realized in
  the truncated algebra `ℝ[X]/(X⁵)` (the Bilaplacian `L = −∂⁴` is 4th order): `dw^i · dw^j = dw^{i+j}`
  (`dw_mul`), `dw^i = 0` for `i ≥ 5` (`dw_truncate`), the iterated Itô rule (associativity, `dw_iterated`),
  and `dw⁴ = 24 ds` (`dw4_eq_24_ds`, the leading correction).
* **§B — the Itô table for the Laplacian** (Eq. 1.9). The Brownian case in `ℝ[X]/(X³)`:
  `dB · dB = ½ ds` (`dB_sq`).
* **§C — the exponential martingale and Wiener product** (Eqs. 1.7–1.8). `Ψ(σ) = exp(∫h dB − ‖h‖²/2)`
  (`expMartingale`), with the Wiener product realized as an algebra homomorphism `Ψ(σ₁·σ₂) = Ψ(σ₁)Ψ(σ₂)`
  (`expMartingale_hom`).
* **§D — the Cameron–Martin–Maruyama–Girsanov density** (p. 3). The Radon–Nikodym derivative
  `exp(−∫h dB − ‖h‖²/2)` (`cameronMartinGirsanov`), strictly positive, whose drift-free value is exactly
  the entropic damping / Cameron–Martin weight `e^{−S_I/ℏ}` of the arc
  (`cameronMartinGirsanov_eq_entropyDamping`).
* **§E — an actual finite-time change of measure.** `endpointCameronMartinDensity` is proved to be the
  exact ratio between shifted and unshifted positive-time Wiener kernels
  (`wienerDensity_shift_eq_density_mul`). The translated Gaussian measure is then proved equal to the
  unshifted measure reweighted by this density (`gaussianReal_map_shift_eq_withDensity`), its
  Radon–Nikodym derivative is identified almost everywhere (`rnDeriv_gaussianReal_shift`), its density
  integrates to one, and the generic Cameron–Martin expectation identity follows.
* **§F — Léandre's perturbed bilaplacian generator** (Eqs. 3.3–3.4 and 3.8).
  `leandrePolynomialGenerator α hₜ = −∂⁴ + αhₜ∂³` acts on every monomial with the exact descending
  factorial coefficients from the paper (`eval_leandrePolynomialGenerator_X_pow`).
* **§G — van Kampen's Itô--Stratonovich equivalence** (van Kampen Eq. 21). The two conventions
  describe the same Markov process after the drift correction `f_I = f_S + ½gg'`; the two drift
  conversions are proved inverse, their conservative Fokker--Planck right-hand sides agree after
  correction, and constant additive noise makes the correction vanish.
* **§H — nonlinear coordinates** (van Kampen Eq. 12). The Itô transformed drift contains the
  second-derivative correction `½g²φ''`, while the ordinary/Stratonovich drift is `fφ'`; affine
  changes make them coincide.
* **§I — internal noise and the master equation** (van Kampen Eq. 26). The gain--loss equation is
  realized using the repository's existing finite collapse/jump kernel, with off-diagonal
  nonnegativity and total-mass conservation. Its continuum integral form is also defined, and
  Fubini proves that its integrated right-hand side vanishes under the natural product
  integrability hypothesis.

The measure theorem in §E is the genuine one-time Gaussian Cameron–Martin theorem. It does not claim
that the repository now contains Léandre's full bosonic Connes space, formal Wiener chaos, or a
countably additive path measure for the bilaplacian—the paper itself treats the latter as a
Hida-type distribution because `−∂⁴` does not generate a positivity-preserving Markov semigroup.
Likewise, §§G--I prove the coefficient/operator identities and master-equation conservation stated
by van Kampen; they do not replace the Wong--Zakai colored-noise limit or derive the system-size
expansion from a microscopic particle model.

## References

* R. Léandre, *A Path-Integral Approach to the Cameron–Martin–Maruyama–Girsanov Formula Associated to a
  Bilaplacian*, J. Funct. Spaces Appl. 2012, Article ID 458738 — the formalized paper (the Itô tables and
  the bilaplacian CMMG formula).
* R. H. Cameron, W. T. Martin, *Transformations of Wiener integrals under translations*, Ann. Math. 45
  (1944) 386 — the Cameron–Martin theorem.
* G. Maruyama, *Continuous Markov processes and stochastic equations*, Rend. Circ. Mat. Palermo 4 (1955)
  48 — the Maruyama density.
* I. V. Girsanov, *On transforming a certain class of stochastic processes by absolutely continuous
  substitution of measures*, Theory Probab. Appl. 5 (1960) 285 — the Girsanov change of measure.
* N. G. van Kampen, *Itô versus Stratonovich*, J. Stat. Phys. 24 (1981) 175--187 — equivalent
  drift conventions, external colored-noise limits, and the internal-noise master equation.
* T. Hida, H.-H. Kuo, J. Potthoff, L. Streit, *White Noise: An Infinite Dimensional Calculus*, Kluwer
  (1993) — the Hida–Streit distribution approach to path integrals used by Léandre.
* Repo link: `NonHermitian.WickRotation.entropyDamping` (the arc's Cameron–Martin weight, §D).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian

open Polynomial
open scoped NNReal ENNReal
open BigOperators MeasureTheory ProbabilityTheory
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
open Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse


/-- The Bilaplacian truncation ideal `(X⁵)`: the Bilaplacian is 4th order, so differentials `dw^i` with
`i ≥ 5` vanish. -/
noncomputable def ItoI : Ideal ℝ[X] := Ideal.span {(X : ℝ[X]) ^ 5}

/-- **The Itô differential** `dw^i = X^i mod X⁵` in the Bilaplacian Itô algebra `ℝ[X]/(X⁵)`. -/
noncomputable def dw (i : ℕ) : ℝ[X] ⧸ ItoI := Ideal.Quotient.mk ItoI (X ^ i)

/-- **[Léandre Eq. 1.12] The Itô product adds indices** `dw^i · dw^j = dw^{i+j}` — the Itô table for the
Bilaplacian. -/
lemma dw_mul (i j : ℕ) : dw i * dw j = dw (i + j) := by
  unfold dw; rw [← map_mul, ← pow_add]

set_option backward.isDefEq.respectTransparency false in
/-- **The Bilaplacian truncation** `dw^i = 0` for `i ≥ 5` — fifth- and higher-order differentials vanish
(the Bilaplacian is 4th order). -/
lemma dw_truncate (i : ℕ) (hi : 5 ≤ i) : dw i = 0 := by
  unfold dw ItoI
  rw [show (X : ℝ[X]) ^ i = X ^ 5 * X ^ (i - 5) by rw [← pow_add]; congr 1; omega, map_mul]
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _)), zero_mul]

/-- **[Léandre Eq. 2.11] The iterated Itô rule** `(dw^i · dw^j) · dw^k = dw^{i+j+k}` — associativity of the
Itô product, the basis of the associativity of the Wiener product. -/
lemma dw_iterated (i j k : ℕ) : dw i * dw j * dw k = dw (i + j + k) := by
  rw [dw_mul, dw_mul]

/-- The Lebesgue (time) differential `ds := dw⁴/24` of the Bilaplacian. -/
noncomputable def dsB : ℝ[X] ⧸ ItoI := (1 / 24 : ℝ) • dw 4

/-- **[Léandre Eq. 1.11] `dw⁴ = 24 ds`** — the leading (4th-order) Itô correction of the Bilaplacian. -/
lemma dw4_eq_24_ds : dw 4 = (24 : ℝ) • dsB := by
  unfold dsB; rw [smul_smul]; norm_num


/-- The Laplacian truncation ideal `(X³)`: the Laplacian is 2nd order, `dB^i = 0` for `i ≥ 3`. -/
noncomputable def LapI : Ideal ℝ[X] := Ideal.span {(X : ℝ[X]) ^ 3}

/-- The Brownian differential `dB = X mod X³`. -/
noncomputable def dB : ℝ[X] ⧸ LapI := Ideal.Quotient.mk LapI X

/-- The Brownian Lebesgue differential `ds := 2·dB²`. -/
noncomputable def dsLap : ℝ[X] ⧸ LapI := (2 : ℝ) • Ideal.Quotient.mk LapI (X ^ 2)

/-- **[Léandre Eq. 1.9] The Itô table for the Laplacian** `dB · dB = ½ ds` — the classical Brownian Itô
rule, the 2nd-order analogue of the Bilaplacian table. -/
lemma dB_sq : dB * dB = (1 / 2 : ℝ) • dsLap := by
  unfold dB dsLap; rw [← map_mul, ← pow_two, smul_smul]; norm_num


/-- **[Léandre Eq. 1.7] The exponential martingale** `Ψ(σ) = exp(∫₀¹ h_s dB_s − ‖h‖²/2)` — the functional
of a coherent vector (`I` is the stochastic integral `∫h dB`, `q = ‖h‖²`). -/
noncomputable def expMartingale (I q : ℝ) : ℝ := Real.exp (I - q / 2)

/-- **[Léandre Eq. 1.8] The Wiener product is a homomorphism** `Ψ(σ₁ · σ₂) = Ψ(σ₁) Ψ(σ₂)` — the map `Ψ`
turns the Wiener product (additive on `(I, q)`) into the ordinary product of functionals. -/
lemma expMartingale_hom (I1 q1 I2 q2 : ℝ) :
    expMartingale (I1 + I2) (q1 + q2) = expMartingale I1 q1 * expMartingale I2 q2 := by
  unfold expMartingale; rw [← Real.exp_add]; congr 1; ring

/-- The exponential martingale is strictly positive. -/
lemma expMartingale_pos (I q : ℝ) : 0 < expMartingale I q := Real.exp_pos _


/-- **[Léandre, p. 3] The scalar Cameron–Martin–Maruyama–Girsanov expression**
`exp(−∫₀¹ h_s dB_s − ‖h‖²/2)`. The actual finite-time Radon–Nikodym statement is established below by
`rnDeriv_gaussianReal_shift`; this definition alone does not assert a relation between measures. -/
noncomputable def cameronMartinGirsanov (I q : ℝ) : ℝ := Real.exp (-I - q / 2)

/-- The scalar CMMG expression is strictly positive. -/
lemma cameronMartinGirsanov_pos (I q : ℝ) : 0 < cameronMartinGirsanov I q := Real.exp_pos _

/-- **[Bridge] The drift-free CMMG density is the arc's Cameron–Martin weight.** With no stochastic-integral
drift (`I = 0`), the Cameron–Martin–Maruyama–Girsanov density `exp(−‖h‖²/2)` is exactly the entropic
damping `e^{−S_I/ℏ}` (`WickRotation.entropyDamping`) of the path-integral arc (with `S_I = (‖h‖²/2)·ℏ`):
the rigorous probabilistic Cameron–Martin density and the path-integral Cameron–Martin weight coincide. -/
lemma cameronMartinGirsanov_eq_entropyDamping (q ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    cameronMartinGirsanov 0 q = entropyDamping ((q / 2) * ℏ) ℏ := by
  unfold cameronMartinGirsanov entropyDamping; congr 1; field_simp; ring

/-! ## E. Finite-time Cameron--Martin quasi-invariance of the Wiener kernel -/

/-- The finite-time Cameron--Martin density associated with translating the
Gaussian/Wiener endpoint from mean `y` to mean `y+a`:
`exp(a(x-y)/τ - a²/(2τ))`. -/
noncomputable def endpointCameronMartinDensity
    (τ a x y : ℝ) : ℝ :=
  Real.exp (a * (x - y) / τ - a ^ 2 / (2 * τ))

/-- The endpoint Cameron--Martin density is strictly positive. -/
lemma endpointCameronMartinDensity_pos
    (τ a x y : ℝ) :
    0 < endpointCameronMartinDensity τ a x y :=
  Real.exp_pos _

/-- The endpoint Cameron--Martin density is measurable in the translated
endpoint. -/
lemma endpointCameronMartinDensity_measurable
    (τ a y : ℝ) :
    Measurable (fun x => endpointCameronMartinDensity τ a x y) := by
  unfold endpointCameronMartinDensity
  fun_prop

/-- The finite-time density is exactly the scalar Girsanov expression with
`I = -a(x-y)/τ` and quadratic energy `q = a²/τ`. -/
lemma endpointCameronMartinDensity_eq_girsanov
    (τ a x y : ℝ) :
    endpointCameronMartinDensity τ a x y =
      cameronMartinGirsanov (-a * (x - y) / τ) (a ^ 2 / τ) := by
  unfold endpointCameronMartinDensity cameronMartinGirsanov
  congr 1
  ring

/-- **Finite-time Cameron--Martin kernel identity.** Translating the starting
point by `a` multiplies the explicit Wiener kernel by the endpoint
Cameron--Martin density. -/
lemma wienerDensity_shift_eq_density_mul
    (τ a x y : ℝ) (hτ : τ ≠ 0) :
    wienerDensity τ x (y + a) =
      endpointCameronMartinDensity τ a x y * wienerDensity τ x y := by
  unfold wienerDensity endpointCameronMartinDensity
  have hexponent :
      (-(x - (y + a)) ^ 2 / (2 * τ)) =
        (a * (x - y) / τ - a ^ 2 / (2 * τ)) +
          (-(x - y) ^ 2 / (2 * τ)) := by
    field_simp
    ring
  rw [hexponent, Real.exp_add]
  ring

/-- The same shift identity in Mathlib's normalized real Gaussian-density
representation. -/
lemma gaussianPDFReal_shift_eq_density_mul
    (τ a x y : ℝ) (hτ : 0 < τ) :
    gaussianPDFReal (y + a) τ.toNNReal x =
      endpointCameronMartinDensity τ a x y *
        gaussianPDFReal y τ.toNNReal x := by
  rw [← wienerDensity_eq_gaussianPDFReal τ x (y + a) hτ,
    ← wienerDensity_eq_gaussianPDFReal τ x y hτ]
  exact wienerDensity_shift_eq_density_mul τ a x y hτ.ne'

/-- The `ℝ≥0∞`-valued density used by `Measure.withDensity`. -/
noncomputable def endpointCameronMartinRN
    (τ a y : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (endpointCameronMartinDensity τ a x y)

/-- The finite-time Radon--Nikodym density is measurable. -/
lemma endpointCameronMartinRN_measurable
    (τ a y : ℝ) :
    Measurable (endpointCameronMartinRN τ a y) := by
  unfold endpointCameronMartinRN
  exact (endpointCameronMartinDensity_measurable τ a y).ennreal_ofReal

/-- **Genuine finite-time Cameron--Martin measure theorem.** The Gaussian law
with translated mean `y+a` equals the Gaussian law with mean `y`, reweighted
by the explicit endpoint density. -/
theorem gaussianReal_shift_eq_withDensity
    (τ a y : ℝ) (hτ : 0 < τ) :
    gaussianReal (y + a) τ.toNNReal =
      (gaussianReal y τ.toNNReal).withDensity
        (endpointCameronMartinRN τ a y) := by
  have hv : τ.toNNReal ≠ 0 := by
    intro h
    have hcoe := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
    simp [max_eq_left hτ.le] at hcoe
    exact hτ.ne' hcoe
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF y τ.toNNReal)
      (endpointCameronMartinRN_measurable τ a y)]
  apply withDensity_congr_ae
  filter_upwards [] with x
  change gaussianPDF (y + a) τ.toNNReal x =
    gaussianPDF y τ.toNNReal x *
      endpointCameronMartinRN τ a y x
  unfold gaussianPDF endpointCameronMartinRN
  rw [gaussianPDFReal_shift_eq_density_mul τ a x y hτ,
    ENNReal.ofReal_mul (endpointCameronMartinDensity_pos τ a x y).le]
  ring

/-- Translating the Gaussian endpoint map is the same measure as reweighting
the original Gaussian law by the Cameron--Martin density. -/
theorem gaussianReal_map_shift_eq_withDensity
    (τ a y : ℝ) (hτ : 0 < τ) :
    (gaussianReal y τ.toNNReal).map (· + a) =
      (gaussianReal y τ.toNNReal).withDensity
        (endpointCameronMartinRN τ a y) := by
  rw [gaussianReal_map_add_const]
  exact gaussianReal_shift_eq_withDensity τ a y hτ

/-- **Actual Radon--Nikodym identification.** The derivative of the translated
finite-time Gaussian law with respect to the original law is almost
everywhere the explicit Cameron--Martin density. -/
theorem rnDeriv_gaussianReal_shift
    (τ a y : ℝ) (hτ : 0 < τ) :
    (gaussianReal (y + a) τ.toNNReal).rnDeriv
        (gaussianReal y τ.toNNReal) =ᵐ[gaussianReal y τ.toNNReal]
      endpointCameronMartinRN τ a y := by
  rw [gaussianReal_shift_eq_withDensity τ a y hτ]
  exact Measure.rnDeriv_withDensity _
    (endpointCameronMartinRN_measurable τ a y)

/-- The Cameron--Martin density has expectation one under the original
Gaussian law, so the reweighting preserves probability mass. -/
theorem lintegral_endpointCameronMartinRN_eq_one
    (τ a y : ℝ) (hτ : 0 < τ) :
    ∫⁻ x, endpointCameronMartinRN τ a y x
        ∂(gaussianReal y τ.toNNReal) = 1 := by
  have hmeasure := gaussianReal_shift_eq_withDensity τ a y hτ
  have huniv := congrArg (fun μ : Measure ℝ => μ Set.univ) hmeasure
  simpa [withDensity_apply _ MeasurableSet.univ] using huniv.symm

/-- **Finite-time Cameron--Martin expectation formula.** Expectations under
the translated Gaussian law equal density-weighted expectations under the
original law. The statement is valid for arbitrary real normed-space-valued
Bochner integrands. -/
theorem integral_gaussianReal_shift_eq_density_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ a y : ℝ) (hτ : 0 < τ) (F : ℝ → E) :
    ∫ x, F x ∂(gaussianReal (y + a) τ.toNNReal) =
      ∫ x, endpointCameronMartinDensity τ a x y • F x
        ∂(gaussianReal y τ.toNNReal) := by
  rw [gaussianReal_shift_eq_withDensity τ a y hτ]
  rw [integral_withDensity_eq_integral_toReal_smul
    (endpointCameronMartinRN_measurable τ a y)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [endpointCameronMartinRN,
    (endpointCameronMartinDensity_pos τ a x y).le]

/-! ## F. Léandre's bilaplacian plus cubic-drift generator -/

/-- **[Léandre Eqs. 3.3--3.4]** The polynomial realization of the perturbed
bilaplacian generator `Lₕ,ₜ = -∂⁴ + α hₜ ∂³`. -/
noncomputable def leandrePolynomialGenerator
    (α ht : ℝ) (f : ℝ[X]) : ℝ[X] :=
  -(derivative^[4] f) + C (α * ht) * derivative^[3] f

/-- The perturbed bilaplacian generator acts on `Xⁿ` by fourth- and
third-descending-factorial terms. -/
lemma leandrePolynomialGenerator_X_pow
    (α ht : ℝ) (n : ℕ) :
    leandrePolynomialGenerator α ht (X ^ n) =
      -(C (n.descFactorial 4 : ℝ) * X ^ (n - 4)) +
        C (α * ht) * (C (n.descFactorial 3 : ℝ) * X ^ (n - 3)) := by
  unfold leandrePolynomialGenerator
  rw [iterate_derivative_X_pow_eq_C_mul,
    iterate_derivative_X_pow_eq_C_mul]

/-- **[Léandre Eq. 3.8]** Pointwise monomial form of the generator:
`-n(n-1)(n-2)(n-3)xⁿ⁻⁴ + αhₜ n(n-1)(n-2)xⁿ⁻³`, encoded by descending
factorials so the formula also handles degrees below four without side
conditions. -/
theorem eval_leandrePolynomialGenerator_X_pow
    (α ht x : ℝ) (n : ℕ) :
    (leandrePolynomialGenerator α ht (X ^ n)).eval x =
      -(n.descFactorial 4 : ℝ) * x ^ (n - 4) +
        α * ht * (n.descFactorial 3 : ℝ) * x ^ (n - 3) := by
  rw [leandrePolynomialGenerator_X_pow]
  simp
  ring

/-- With zero Cameron--Martin drift, Léandre's generator reduces exactly to
the unperturbed negative bilaplacian. -/
lemma leandrePolynomialGenerator_zero_drift
    (α : ℝ) (f : ℝ[X]) :
    leandrePolynomialGenerator α 0 f = -(derivative^[4] f) := by
  simp [leandrePolynomialGenerator]

/-! ## G. van Kampen's Itô--Stratonovich drift equivalence -/

noncomputable section

/-- Half of the multiplicative-noise logarithmic-Jacobian term `gg'/2`.
This is the noise-induced drift separating the Itô and Stratonovich
coefficient conventions in van Kampen Eq. 21. -/
def noiseInducedDrift (g g' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 / 2 : ℝ) * g x * g' x

/-- The Itô drift equivalent to a supplied Stratonovich drift:
`f_I = f_S + gg'/2` (van Kampen Eq. 21). -/
def itoEquivalentDrift (f g g' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f x + noiseInducedDrift g g' x

/-- The Stratonovich drift equivalent to a supplied Itô drift:
`f_S = f_I - gg'/2` (van Kampen Eq. 21). -/
def stratonovichEquivalentDrift (f g g' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f x - noiseInducedDrift g g' x

/-- Converting an Itô drift to Stratonovich and back returns the original
drift. -/
lemma itoEquivalentDrift_stratonovichEquivalentDrift
    (f g g' : ℝ → ℝ) :
    itoEquivalentDrift (stratonovichEquivalentDrift f g g') g g' = f := by
  funext x
  simp [itoEquivalentDrift, stratonovichEquivalentDrift, noiseInducedDrift]

/-- Converting a Stratonovich drift to Itô and back returns the original
drift. -/
lemma stratonovichEquivalentDrift_itoEquivalentDrift
    (f g g' : ℝ → ℝ) :
    stratonovichEquivalentDrift (itoEquivalentDrift f g g') g g' = f := by
  funext x
  simp [itoEquivalentDrift, stratonovichEquivalentDrift, noiseInducedDrift]

/-- **[van Kampen Eq. 5]** The conservative one-dimensional Itô
Fokker--Planck right-hand side
`-∂(fP) + ½∂²(g²P)`. -/
def itoFokkerPlanckRHS (f g P : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    -deriv (fun y => f y * P y) x +
      (1 / 2 : ℝ) * deriv (deriv (fun y => g y ^ 2 * P y)) x

/-! ### The convention equivalence, proved rather than defined -/

/-- **[van Kampen Eq. 7b]** The Stratonovich diffusion flux `½ g ∂(g P)`.  The nested derivative is
what characterizes the Stratonovich convention; nothing here mentions an Itô drift. -/
def stratonovichDiffusionFlux (g P : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 / 2 : ℝ) * (g x * deriv (fun z => g z * P z) x)

/-- **[van Kampen Eq. 5]** The Itô diffusion flux `½ ∂(g² P)`. -/
def itoDiffusionFlux (g P : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 / 2 : ℝ) * deriv (fun z => g z ^ 2 * P z) x

/-- **The flux identity behind the convention change.**  `g ∂(gP) + g g' P = ∂(g²P)`: the
Stratonovich diffusion flux differs from the Itô one by exactly the noise-induced drift flux
`½ g g' P`.  This is the analytic content of the Itô/Stratonovich correspondence, and it needs the
product rule — it is not true by unfolding a definition. -/
lemma stratonovich_ito_flux_identity (g P : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hP : Differentiable ℝ P) :
    (fun y => g y * deriv (fun z => g z * P z) y + g y * deriv g y * P y)
      = fun y => deriv (fun z => g z ^ 2 * P z) y := by
  funext x
  have hgP : deriv (fun z => g z * P z) x = deriv g x * P x + g x * deriv P x :=
    deriv_mul (hg x) (hP x)
  have hpow : deriv (fun z => g z ^ 2) x = 2 * g x * deriv g x := by
    rw [deriv_fun_pow (hg x) 2]; ring
  have hsq : deriv (fun z => g z ^ 2 * P z) x
      = deriv (fun z => g z ^ 2) x * P x + g x ^ 2 * deriv P x :=
    deriv_mul ((hg x).pow 2) (hP x)
  rw [hgP, hsq, hpow]
  ring

/-- The conservative Stratonovich right-hand side in its **own** form, `-∂(f P - ½ g ∂(g P))`,
built from `stratonovichDiffusionFlux` and making no reference to any Itô drift. -/
def stratonovichConservativeRHS (f g P : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -deriv (fun y => f y * P y - stratonovichDiffusionFlux g P y) x

/-- The conservative Itô right-hand side in the same single-flux form, `-∂(f P - ½ ∂(g² P))`. -/
def itoConservativeRHS (f g P : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -deriv (fun y => f y * P y - itoDiffusionFlux g P y) x

/-- **[van Kampen Eq. 21, proved]** The Stratonovich operator written in its own nested-derivative
form equals the Itô operator once the drift is corrected by `½gg'`.

An earlier definition in this file built the Stratonovich operator *out of* its equivalent Itô
drift, so the equivalence held by unfolding and was never established; it has been removed.  Here the two sides are
built independently — nested `g ∂(gP)` on one
side, `∂(g²P)` on the other — and the identification rests on the product rule via
`stratonovich_ito_flux_identity`, which is why differentiability of `g` and `P` is required. -/
theorem stratonovichConservativeRHS_eq_ito_corrected (f g P : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hP : Differentiable ℝ P) :
    stratonovichConservativeRHS f g P
      = itoConservativeRHS (itoEquivalentDrift f g (deriv g)) g P := by
  unfold stratonovichConservativeRHS itoConservativeRHS
  have hflux := congrFun (stratonovich_ito_flux_identity g P hg hP)
  have hint :
      (fun y => f y * P y - stratonovichDiffusionFlux g P y)
        = fun y => itoEquivalentDrift f g (deriv g) y * P y - itoDiffusionFlux g P y := by
    funext y
    have hy := hflux y
    unfold stratonovichDiffusionFlux itoDiffusionFlux itoEquivalentDrift noiseInducedDrift
    linarith [hy]
  rw [hint]

/-- With additive noise the two conservative forms agree with **no** drift correction: the flux
identity degenerates because `g' = 0`. -/
theorem stratonovichConservativeRHS_const_noise (f P : ℝ → ℝ) (c : ℝ)
    (hP : Differentiable ℝ P) :
    stratonovichConservativeRHS f (fun _ => c) P
      = itoConservativeRHS f (fun _ => c) P := by
  have hg : Differentiable ℝ (fun _ : ℝ => c) := differentiable_const c
  have hmain := stratonovichConservativeRHS_eq_ito_corrected f (fun _ => c) P hg hP
  have hdrift : itoEquivalentDrift f (fun _ : ℝ => c) (deriv fun _ : ℝ => c) = f := by
    funext x
    simp [itoEquivalentDrift, noiseInducedDrift]
  rw [hmain, hdrift]

/-! ## H. Nonlinear coordinate changes -/

/-- **[van Kampen Eq. 12a]** The Itô drift after a nonlinear coordinate
change, including the quadratic-variation correction `½g²φ''`. -/
def itoCoordinateDrift (f g φ' φ'' : ℝ) : ℝ :=
  f * φ' + (1 / 2 : ℝ) * g ^ 2 * φ''

/-- The ordinary/Stratonovich drift after a coordinate change: `fφ'`. -/
def stratonovichCoordinateDrift (f φ' : ℝ) : ℝ := f * φ'

/-- The discrepancy between the Itô and ordinary/Stratonovich coordinate
drifts is exactly the quadratic-variation term `½g²φ''`. -/
lemma itoCoordinateDrift_eq_stratonovich_add
    (f g φ' φ'' : ℝ) :
    itoCoordinateDrift f g φ' φ'' =
      stratonovichCoordinateDrift f φ' +
        (1 / 2 : ℝ) * g ^ 2 * φ'' :=
  rfl

/-- For affine coordinate changes (`φ''=0`), the Itô and Stratonovich
coordinate-transformation laws coincide. -/
lemma itoCoordinateDrift_affine
    (f g φ' : ℝ) :
    itoCoordinateDrift f g φ' 0 =
      stratonovichCoordinateDrift f φ' := by
  simp [itoCoordinateDrift, stratonovichCoordinateDrift]

/-! ## I. Internal noise: finite and continuum gain--loss master equations -/

section FiniteMasterEquation

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The finite gain--loss generator associated with transition rates
`W(arrival|source)`. It is a concrete instance of the repository's existing
finite collapse/jump kernel. -/
def vanKampenGainLossKernel
    (W : Ω → Ω → ℝ) : CollapseKernel Ω :=
  fun arrival source =>
    W arrival source -
      if arrival = source then ∑ z : Ω, W z source else 0

/-- **[van Kampen Eq. 26, finite form]** Applying the gain--loss kernel to a
density gives `Σ_source [W(arrival|source)P(source) -
W(source|arrival)P(arrival)]`. -/
lemma vanKampenGainLossKernel_action
    (W : Ω → Ω → ℝ) (P : ProbabilityDensity Ω) (x : Ω) :
    kernelAction (vanKampenGainLossKernel W) P x =
      ∑ x' : Ω, (W x x' * P x' - W x' x * P x) := by
  simp only [kernelAction, vanKampenGainLossKernel, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  have hdiag :
      ∑ source : Ω,
          (if x = source then ∑ z : Ω, W z source else 0) * P source =
        (∑ z : Ω, W z x) * P x := by
    classical
    rw [Finset.sum_eq_single x]
    · simp
    · intro source _ hsource
      simp [hsource.symm]
    · simp
  rw [hdiag, Finset.sum_mul]

/-- Every gain--loss kernel is column conservative: its total arrival rate
and total departure rate cancel for each source state. -/
lemma vanKampenGainLossKernel_columnConservative
    (W : Ω → Ω → ℝ) :
    columnConservative (vanKampenGainLossKernel W) := by
  intro source
  simp [vanKampenGainLossKernel, Finset.sum_sub_distrib]

/-- Nonnegative transition rates give nonnegative off-diagonal entries of
the gain--loss generator. -/
lemma vanKampenGainLossKernel_offDiagonal_nonneg
    (W : Ω → Ω → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    {arrival source : Ω} (hne : arrival ≠ source) :
    0 ≤ vanKampenGainLossKernel W arrival source := by
  simp [vanKampenGainLossKernel, hne, hW]

/-- The finite internal-noise master equation conserves total probability
at the infinitesimal level. This reuses the repository's generic
column-conservative-kernel theorem. -/
theorem vanKampenGainLoss_totalMass_eq_zero
    (W : Ω → Ω → ℝ) (P : ProbabilityDensity Ω) :
    totalMass (kernelAction (vanKampenGainLossKernel W) P) = 0 :=
  totalMass_kernelAction_eq_zero_of_columnConservative _ _
    (vanKampenGainLossKernel_columnConservative W)

end FiniteMasterEquation

section ContinuumMasterEquation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **[van Kampen Eq. 26]** The continuum gain--loss master-equation
right-hand side
`∫ [W(x|x')P(x') - W(x'|x)P(x)] dμ(x')`. -/
def continuumGainLossRHS
    (μ : Measure Ω) (W : Ω → Ω → ℝ) (P : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ x', (W x x' * P x' - W x' x * P x) ∂μ

/-- **Continuum probability conservation.** If the gain integrand is
integrable on the product space, then Fubini exchanges arrival and source,
so the total gain and total loss cancel exactly. -/
theorem integral_continuumGainLossRHS_eq_zero
    (μ : Measure Ω) [SFinite μ]
    (W : Ω → Ω → ℝ) (P : Ω → ℝ)
    (h : Integrable (Function.uncurry (fun x x' => W x x' * P x'))
      (μ.prod μ)) :
    ∫ x, continuumGainLossRHS μ W P x ∂μ = 0 := by
  let F : Ω → Ω → ℝ := fun x x' => W x x' * P x'
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := h
  have hFs : Integrable (Function.uncurry (fun x x' => F x' x))
      (μ.prod μ) := by
    change Integrable ((Function.uncurry F) ∘ Prod.swap) (μ.prod μ)
    exact hF.swap
  have hFi : Integrable (fun x => ∫ x', F x x' ∂μ) μ :=
    hF.integral_prod_left
  have hFsi : Integrable (fun x => ∫ x', F x' x ∂μ) μ :=
    hFs.integral_prod_left
  unfold continuumGainLossRHS
  have hinter :
      (fun x => ∫ x', (F x x' - F x' x) ∂μ) =ᵐ[μ]
        (fun x => (∫ x', F x x' ∂μ) - ∫ x', F x' x ∂μ) := by
    filter_upwards [hF.prod_right_ae, hFs.prod_right_ae] with x hx hxs
    exact integral_sub hx hxs
  rw [integral_congr_ae hinter, integral_sub hFi hFsi,
    integral_integral_swap hF]
  simp

end ContinuumMasterEquation

end

end Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.cameronMartinGirsanov_eq_entropyDamping where
  formalizes @ "claim:the-drift-free-cameron-martin-girsanov-density-equals-the-entropic-damping-weight-exp-minus-imaginary-action-over-hbar",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:leandre-bilaplacian-stochastic-cameron-martin-girsanov",
  caveat @ "claim:this-scalar-exponential-identity-alone-is-not-a-radon-nikodym-theorem-the-measure-level-identification-is-rnDeriv-gaussianReal-shift"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.expMartingale_hom where
  formalizes @ "claim:the-wiener-exponential-martingale-is-an-algebra-homomorphism-of-the-wiener-product"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.dw_mul where
  formalizes @ "claim:the-bilaplacian-ito-differential-product-adds-indices-in-the-truncated-ito-algebra"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.dB_sq where
  formalizes @ "claim:the-classical-brownian-ito-rule-dB-squared-equals-one-half-the-lebesgue-differential"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.gaussianReal_map_shift_eq_withDensity where
  formalizes @ "claim:translation-of-the-positive-time-gaussian-wiener-endpoint-law-equals-reweighting-by-the-explicit-cameron-martin-density",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-wiener-time-variance-is-strictly-positive",
  supported_by @ "paper:leandre-bilaplacian-stochastic-cameron-martin-girsanov",
  supported_by @ "lean:ProbabilityTheory.gaussianReal_map_add_const",
  caveat @ "claim:this-is-a-genuine-finite-time-one-endpoint-measure-theorem-not-the-full-infinite-dimensional-path-space-or-bilaplacian-hida-distribution-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.rnDeriv_gaussianReal_shift where
  formalizes @ "claim:the-radon-nikodym-derivative-of-the-shifted-positive-time-gaussian-law-is-almost-everywhere-the-explicit-cameron-martin-density",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:translation-of-the-positive-time-gaussian-wiener-endpoint-law-equals-reweighting-by-the-explicit-cameron-martin-density",
  supported_by @ "lean:MeasureTheory.Measure.rnDeriv_withDensity",
  caveat @ "claim:the-almost-everywhere-derivative-is-with-respect-to-the-finite-time-gaussian-endpoint-law"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.integral_gaussianReal_shift_eq_density_smul where
  formalizes @ "claim:every-bochner-expectation-under-the-shifted-positive-time-gaussian-law-equals-the-cameron-martin-density-weighted-expectation-under-the-original-law",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:translation-of-the-positive-time-gaussian-wiener-endpoint-law-equals-reweighting-by-the-explicit-cameron-martin-density",
  supported_by @ "lean:integral_withDensity_eq_integral_toReal_smul",
  caveat @ "claim:the-bochner-integral-convention-returns-zero-outside-integrability-the-theorem-does-not-supply-integrability-of-an-arbitrary-observable"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.eval_leandrePolynomialGenerator_X_pow where
  formalizes @ "claim:leandres-perturbed-bilaplacian-generator-minus-fourth-derivative-plus-alpha-h-t-times-third-derivative-has-the-paper-descending-factorial-action-on-every-polynomial-monomial",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:leandre-bilaplacian-stochastic-cameron-martin-girsanov-equations-3-3-3-4-and-3-8",
  caveat @ "claim:this-proves-the-generator-on-the-polynomial-core-it-does-not-construct-the-bosonic-connes-completion-or-a-countably-additive-bilaplacian-path-measure"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovich_ito_flux_identity where
  formalizes @ "claim:the-stratonovich-diffusion-flux-g-times-the-derivative-of-g-p-plus-the-noise-induced-drift-flux-equals-the-ito-diffusion-flux-derivative-of-g-squared-p",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equations-5-7-and-21",
  caveat @ "requires-differentiability-of-the-noise-amplitude-and-the-density-the-identity-is-the-product-rule-not-a-definitional-unfolding"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovichConservativeRHS_eq_ito_corrected where
  formalizes @ "claim:the-stratonovich-fokker-planck-operator-is-the-ito-fokker-planck-operator-after-adding-the-noise-induced-drift-one-half-g-times-g-prime",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:the-stratonovich-diffusion-flux-g-times-the-derivative-of-g-p-plus-the-noise-induced-drift-flux-equals-the-ito-diffusion-flux-derivative-of-g-squared-p",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equations-5-7-and-21",
  caveat @ "claim:this-is-the-exact-coefficient-and-forward-operator-equivalence-under-differentiability-of-g-and-p-it-does-not-prove-the-wong-zakai-colored-noise-limit"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovichConservativeRHS_const_noise where
  formalizes @ "claim:for-additive-state-independent-noise-the-ito-and-stratonovich-fokker-planck-operators-coincide-without-a-drift-correction",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:the-stratonovich-fokker-planck-operator-is-the-ito-fokker-planck-operator-after-adding-the-noise-induced-drift-one-half-g-times-g-prime",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equations-2-3"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.itoCoordinateDrift_eq_stratonovich_add where
  formalizes @ "claim:under-a-nonlinear-coordinate-change-the-ito-drift-is-the-ordinary-stratonovich-drift-plus-one-half-g-squared-times-the-coordinate-second-derivative",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equation-12",
  caveat @ "claim:this-formalizes-the-local-coefficient-transformation-not-a-general-stochastic-integral-change-of-variables-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.vanKampenGainLossKernel_action where
  formalizes @ "claim:the-repository-finite-jump-kernel-instantiates-van-kampens-internal-noise-gain-loss-master-equation",
  epistemic_status @ "analytic-theorem",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equation-26",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.kernelAction"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.vanKampenGainLoss_totalMass_eq_zero where
  formalizes @ "claim:the-finite-internal-noise-gain-loss-master-equation-conserves-total-probability",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:the-repository-finite-jump-kernel-instantiates-van-kampens-internal-noise-gain-loss-master-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse.totalMass_kernelAction_eq_zero_of_columnConservative"

zil attach Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.integral_continuumGainLossRHS_eq_zero where
  formalizes @ "claim:the-continuum-internal-noise-gain-loss-master-equation-conserves-total-probability-by-fubini-exchange-of-arrival-and-source",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-continuum-gain-integrand-is-bochner-integrable-on-the-product-space",
  supported_by @ "paper:van-kampen-1981-ito-versus-stratonovich-equation-26",
  supported_by @ "lean:MeasureTheory.integral_integral_swap",
  caveat @ "claim:this-proves-conservation-for-the-supplied-integrable-rate-kernel-it-does-not-derive-the-rate-kernel-or-the-system-size-expansion-from-microscopic-dynamics"

zil_file_contract physlib.leandreCameronMartinBilaplacian where
  promises "The Leandre Bilaplacian stochastic calculus and van Kampen convention/master-equation bridge: the truncated Ito algebras carry the fourth-order Bilaplacian and second-order Laplacian Ito tables; the Wiener exponential martingale is a homomorphism; the positive-time endpoint law has an explicit normalized Radon-Nikodym derivative and Bochner expectation formula; the scalar drift-free exponential equals entropic damping; the polynomial-core generator is minus the fourth derivative plus alpha h_t times the third derivative; Ito and Stratonovich forward operators are equivalent after the one-half-g-g-prime drift correction and coincide for additive noise; nonlinear coordinates carry the Ito quadratic-variation correction; and finite plus continuum internal-noise gain-loss master equations conserve total probability."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.expMartingale",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.cameronMartinGirsanov",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.endpointCameronMartinRN",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.leandrePolynomialGenerator"]
  forbids_substitutes ["the full infinite-jet Ito algebra, this uses the polynomial truncation ideals fixing the operator order",
    "calling the scalar exponential by itself a proved Radon-Nikodym derivative",
    "calling the finite-time Gaussian endpoint theorem a full path-space Cameron-Martin theorem",
    "claiming a countably additive probability path measure for the non-Markovian negative bilaplacian",
    "claiming the algebraic Ito-Stratonovich drift equivalence proves the Wong-Zakai colored-noise limit",
    "claiming the conservative master equation derives a microscopic transition-rate kernel or the van Kampen system-size expansion"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.cameronMartinGirsanov_eq_entropyDamping,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.expMartingale_hom,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.dw_mul,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.dw_iterated,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.dB_sq,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.gaussianReal_map_shift_eq_withDensity,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.rnDeriv_gaussianReal_shift,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.lintegral_endpointCameronMartinRN_eq_one,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.integral_gaussianReal_shift_eq_density_smul,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.eval_leandrePolynomialGenerator_X_pow,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovich_ito_flux_identity,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovichConservativeRHS_eq_ito_corrected,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.stratonovichConservativeRHS_const_noise,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.itoCoordinateDrift_eq_stratonovich_add,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.vanKampenGainLossKernel_action,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.vanKampenGainLoss_totalMass_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.LeandreCameronMartinBilaplacian.integral_continuumGainLossRHS_eq_zero]

/- ZIL-END -/
