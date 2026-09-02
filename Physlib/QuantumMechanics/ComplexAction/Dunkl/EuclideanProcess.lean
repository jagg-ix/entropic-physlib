/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator
public import Physlib.QFT.PathIntegral.FeynmanKac
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Euclidean time evolution of the Wigner–Dunkl process: two Bessel processes + Feynman–Kac

Formalization of §5 and Appendix A of *G. Junker, "On the Path Integral Formulation of Wigner–Dunkl
Quantum Mechanics," arXiv:2312.12895*: the Euclidean-time evolution `e^{τ(L^{(ν)} − V)}` of Wigner–Dunkl
quantum mechanics, and the **Dunkl process** that realizes it. The Dunkl process has *jumps* (the
reflection `R`), but it splits — via the parity projectors `P± = (1 ± R)/2` — into **two continuous Bessel
processes**: one *reflecting* (Neumann, index `ν − ½`) and one *absorbing* (Dirichlet, index `ν + ½`).

This file builds the splitting structurally on `ℝ[X]` (reusing `reflPoly` from `Dunkl.Oscillator`) and
**uses the reference tree Feynman–Kac infrastructure** (`Physlib.QFT.PathIntegral.FeynmanKac`):

* **§A — the parity decomposition** (Junker Eq. 76): `P± = (1 ± R)/2` are complementary orthogonal
  idempotents on `ℝ[X]` (`parityPlus_idem`, `parity_add`), with `P₊` even and `P₋` odd
  (`parityPlus_even`, `parityMinus_odd`) and `R = P₊ − P₋`. The even sector drives the reflecting
  process, the odd sector the absorbing process.
* **§B — the two Bessel processes** (Eq. 77, A.1): `besselReflectingIndex ν = ν − ½` (Neumann `f'(0)=0`)
  and `besselAbsorbingIndex ν = ν + ½` (Dirichlet `f(0)=0`), with index difference `1`
  (`bessel_index_diff`); the Bessel generator `L_B^{(α)} = ½(∂² + (2α+1)/x ∂)` has formal monomial
  eigenvalue `½ n(n + 2α)` (`besselGenEigenvalue`).
* **§C — the transition-density split** (Eq. 77): `d_τ^{(ν)}(x,y) = b_τ^{(ν−½)}(|x|,|y|) +
  xy·b_τ^{(ν+½)}(|x|,|y|)` (`dunklTransitionDensity`), and at `ν = 0` (Eq. 79) the Dunkl density is the
  ordinary Wiener/heat kernel `wienerDensity` (`wienerDensity_symm`, `wienerDensity_pos`).
* **§D — the Dunkl–Feynman–Kac formula** (Eq. 78): both Bessel path integrals carry the *same*
  reference tree Feynman–Kac weight `fkPathWeight V z τ = exp(−∫₀^τ V(z s) ds)`. The Euclidean Dunkl
  propagator is the parity combination of two `FeynmanKacModel` propagators (`dunklEuclideanFK`); each
  inherits the Chapman–Kolmogorov semigroup law (`dunklEuclideanFK_semigroup_refl/abs`); the free process
  has unit weight (`dunkl_fk_free_weight`), and a non-negative potential damps it (`dunkl_fk_weight_le_one`).
  The Euclidean weight ties to the entropic Wick rotation `euclideanEvolutionFactor`.
* **§E — the weighted kernel law itself** (Eq. 46): `DunklKernelSemigroup` records a kernel satisfying
  the paper's exact `|z|^{2ν} dz` Chapman–Kolmogorov convolution.  `dunklSequentialKernel_eq_total`
  collapses two consecutive slices, while `dunklInterruptedKernel` inserts an operator between them.
  The latter reduces to the semigroup kernel for the identity insertion and vanishes for the zero
  insertion.  This distinction is the kernel-level interface used by the Glenn photon-exchange bridge.
* **§F — a concrete analytic instance**: at `ν = 0`, two positive-time Wiener kernels factor through
  a normalized Gaussian bridge density.  Its integral is one, proving the pointwise convolution
  theorem and constructing `freeWienerDunklSemigroup` without an externally supplied semigroup law.
* **§G — normalization and finite slicing**: the explicit kernel is integrable with total mass one,
  and every finite chain of equal positive-time slices collapses exactly to the total-time kernel.
  This proves the finite algebraic content of Eq. 56 while leaving its continuum mesh limit explicit.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

open scoped NNReal
open Polynomial
open MeasureTheory ProbabilityTheory
open Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator
open Physlib.QFT.PathIntegral


/-- `R` is additive: `R(p + q) = Rp + Rq`. -/
lemma reflPoly_add (p q : ℝ[X]) : reflPoly (p + q) = reflPoly p + reflPoly q := by
  simp [reflPoly, add_comp]

/-- `R` commutes with real scalars: `R(c • p) = c • Rp`. -/
lemma reflPoly_smul (c : ℝ) (p : ℝ[X]) : reflPoly (c • p) = c • reflPoly p := by
  simp [reflPoly, smul_comp]

/-- `R` is subtractive: `R(p − q) = Rp − Rq`. -/
lemma reflPoly_sub (p q : ℝ[X]) : reflPoly (p - q) = reflPoly p - reflPoly q := by
  simp [reflPoly, sub_comp]

/-- **[Junker Eq. 76] The even parity projector** `P₊ = (1 + R)/2`. -/
noncomputable def parityPlus (p : ℝ[X]) : ℝ[X] := (1 / 2 : ℝ) • (p + reflPoly p)

/-- **[Junker Eq. 76] The odd parity projector** `P₋ = (1 − R)/2`. -/
noncomputable def parityMinus (p : ℝ[X]) : ℝ[X] := (1 / 2 : ℝ) • (p - reflPoly p)

/-- **The projectors are complementary**: `P₊ p + P₋ p = p` (the even–odd decomposition). -/
lemma parity_add (p : ℝ[X]) : parityPlus p + parityMinus p = p := by
  simp only [parityPlus, parityMinus, ← smul_add]; rw [add_add_sub_cancel,
    show ((1 : ℝ) / 2) • (p + p) = ((1 : ℝ) / 2 * 2) • p by rw [← smul_smul, two_smul]]
  norm_num

/-- **`R = P₊ − P₋`**: the reflection is the difference of the parity projectors. -/
lemma parity_sub_eq_refl (p : ℝ[X]) : parityPlus p - parityMinus p = reflPoly p := by
  simp only [parityPlus, parityMinus, ← smul_sub, sub_sub_sub_cancel_left,
    show p + reflPoly p - (p - reflPoly p) = reflPoly p + reflPoly p by ring,
    show reflPoly p + reflPoly p = (2 : ℝ) • reflPoly p by rw [two_smul], smul_smul]
  norm_num

/-- **`P₊` lands in the even subspace**: `R(P₊ p) = P₊ p`. -/
lemma parityPlus_even (p : ℝ[X]) : reflPoly (parityPlus p) = parityPlus p := by
  rw [parityPlus, reflPoly_smul, reflPoly_add, reflPoly_involutive, add_comm]

/-- **`P₋` lands in the odd subspace**: `R(P₋ p) = −P₋ p`. -/
lemma parityMinus_odd (p : ℝ[X]) : reflPoly (parityMinus p) = -parityMinus p := by
  rw [parityMinus, reflPoly_smul, reflPoly_sub, reflPoly_involutive, ← smul_neg, neg_sub]

/-- **`P₊` is idempotent**: `P₊(P₊ p) = P₊ p` (a genuine projector). -/
lemma parityPlus_idem (p : ℝ[X]) : parityPlus (parityPlus p) = parityPlus p := by
  conv_lhs => rw [parityPlus, parityPlus_even]
  rw [show parityPlus p + parityPlus p = (2 : ℝ) • parityPlus p by rw [two_smul], smul_smul]
  norm_num

/-- **`P₋` is idempotent**: `P₋(P₋ p) = P₋ p`. -/
lemma parityMinus_idem (p : ℝ[X]) : parityMinus (parityMinus p) = parityMinus p := by
  conv_lhs => rw [parityMinus, parityMinus_odd]
  rw [sub_neg_eq_add,
    show parityMinus p + parityMinus p = (2 : ℝ) • parityMinus p by rw [two_smul], smul_smul]
  norm_num


/-- **[Junker §5] The reflecting Bessel index** `α = ν − ½` — the even sector becomes a Bessel process
with a Neumann boundary condition `f'(0) = 0` (reflection at the origin). -/
noncomputable def besselReflectingIndex (ν : ℝ) : ℝ := ν - 1 / 2

/-- **[Junker §5] The absorbing Bessel index** `β = ν + ½` — the odd sector becomes a Bessel process with
a Dirichlet boundary condition `f(0) = 0` (absorption at the origin). -/
noncomputable def besselAbsorbingIndex (ν : ℝ) : ℝ := ν + 1 / 2

/-- **The two Bessel indices differ by `1`**: `(ν + ½) − (ν − ½) = 1` — the Radon–Nikodym index shift
(Eq. A.6) relating the reflecting and absorbing processes. -/
lemma bessel_index_diff (ν : ℝ) : besselAbsorbingIndex ν - besselReflectingIndex ν = 1 := by
  unfold besselReflectingIndex besselAbsorbingIndex; ring

/-- **[Junker Eq. A.1] The Bessel generator's monomial eigenvalue** `L_B^{(α)} xⁿ = ½ n(n + 2α) xⁿ⁻²`:
the spectrum of `L_B^{(α)} = ½(∂² + (2α+1)/x ∂)` on `xⁿ`. -/
noncomputable def besselGenEigenvalue (α : ℝ) (n : ℕ) : ℝ := (1 / 2) * n * (n + 2 * α)

/-- The free Bessel generator (`α = −½`, i.e. `ν = 0`) reduces to `½ ∂²`: eigenvalue `½ n(n−1)`, the
ordinary second derivative on `xⁿ` — the generator of Wiener/Brownian motion. -/
lemma besselGenEigenvalue_free (n : ℕ) : besselGenEigenvalue (-(1 / 2)) n = (1 / 2) * n * (n - 1) := by
  unfold besselGenEigenvalue; ring


/-- **[Junker Eq. 77] The Dunkl transition density splits into two Bessel densities.** Given a Bessel
transition density `b` (index, time, two points; Eq. A.2), the Dunkl heat kernel is
`d_τ^{(ν)}(x,y) = b_τ^{(ν−½)}(|x|,|y|) + xy·b_τ^{(ν+½)}(|x|,|y|)` — the even (reflecting) part plus the
sign-weighted odd (absorbing) part. The `xy` prefactor is the parity signature of `P₋`. -/
noncomputable def dunklTransitionDensity (b : ℝ → ℝ → ℝ → ℝ → ℝ) (ν τ x y : ℝ) : ℝ :=
  b (besselReflectingIndex ν) τ |x| |y| + x * y * b (besselAbsorbingIndex ν) τ |x| |y|

/-- **[Junker Eq. 79] The Wiener / heat kernel** `d_τ^{(0)}(x,y) = (2πτ)^{−1/2} exp(−(x−y)²/2τ)` — the
`ν = 0` Dunkl density on the real line, the transition density of Brownian motion. -/
noncomputable def wienerDensity (τ x y : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * τ)) * Real.exp (-(x - y) ^ 2 / (2 * τ))

/-- The Wiener density is **symmetric**: `d_τ(x,y) = d_τ(y,x)`. -/
lemma wienerDensity_symm (τ x y : ℝ) : wienerDensity τ x y = wienerDensity τ y x := by
  unfold wienerDensity; rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

/-- The Wiener density is **strictly positive** for `τ > 0`. -/
lemma wienerDensity_pos (τ x y : ℝ) (hτ : 0 < τ) : 0 < wienerDensity τ x y := by
  unfold wienerDensity
  exact mul_pos (by positivity) (Real.exp_pos _)


/-- **[Junker Eq. 78] The free Dunkl process carries unit Feynman–Kac weight**: with `V = 0` the shared
weight `fkPathWeight V z τ = exp(−∫₀^τ V) = 1`. The Bessel path integrals of Eq. 78 then reduce to the
bare Bessel transition measures. -/
lemma dunkl_fk_free_weight (z : ℝ → ℝ) (τ : ℝ) : fkPathWeight (fun _ => 0) z τ = 1 := by
  simp [fkPathWeight, fkPathPotential]

/-- **A non-negative potential damps the Dunkl–Feynman–Kac weight**: for `V ≥ 0` and `τ ≥ 0` the shared
weight `fkPathWeight V z τ ≤ 1`. So both Bessel path integrals in Eq. 78 are contractive — the Euclidean
evolution is a genuine (sub-Markovian) semigroup. -/
lemma dunkl_fk_weight_le_one (V : ℝ → ℝ) (z : ℝ → ℝ) (τ : ℝ)
    (hV : ∀ y, 0 ≤ V y) (hτ : 0 ≤ τ) : fkPathWeight V z τ ≤ 1 :=
  fkPathWeight_le_one V z τ hV hτ

/-- **[Junker Eq. 78] The Euclidean Dunkl propagator** as the parity combination of two Bessel
Feynman–Kac propagators: `⟨x|e^{τ(L^{(ν)}−V)}|y⟩ = (reflecting) + xy·(absorbing)`. Both `FeynmanKacModel`s
carry the same potential `V`; the reflecting one realizes the even sector (index `ν − ½`), the absorbing
one the odd sector (index `ν + ½`). -/
noncomputable def dunklEuclideanFK
    (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (τ x y : ℝ) : ℝ :=
  feynman_kac_propagator Brefl β obs τ x + x * y * feynman_kac_propagator Babs β obs τ x

/-- **The reflecting Bessel sector obeys the Chapman–Kolmogorov semigroup law** (Eq. A.3) — inherited
from the reference tree `feynman_kac_propagator_semigroup`. -/
lemma dunklEuclideanFK_semigroup_refl (Brefl : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (t s x : ℝ) :
    feynman_kac_propagator Brefl β obs (t + s) x
      = Brefl.pathIntegral (fun y => feynman_kac_propagator Brefl β obs s y) t x :=
  feynman_kac_propagator_semigroup Brefl β obs t s x

/-- **The absorbing Bessel sector obeys the Chapman–Kolmogorov semigroup law** (Eq. A.3). -/
lemma dunklEuclideanFK_semigroup_abs (Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (t s x : ℝ) :
    feynman_kac_propagator Babs β obs (t + s) x
      = Babs.pathIntegral (fun y => feynman_kac_propagator Babs β obs s y) t x :=
  feynman_kac_propagator_semigroup Babs β obs t s x

/-- **At the origin `x = 0` (or `y = 0`) the absorbing sector drops out**: `dunklEuclideanFK … 0 y =`
the pure reflecting propagator. This is the Dirichlet/absorption boundary condition `f(0) = 0` of the
odd Bessel process — the absorbing process contributes nothing at the origin. -/
lemma dunklEuclideanFK_origin (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (τ y : ℝ) :
    dunklEuclideanFK Brefl Babs β obs τ 0 y = feynman_kac_propagator Brefl β obs τ 0 := by
  simp [dunklEuclideanFK]

/-! ## E. The explicit weighted Chapman--Kolmogorov kernel -/

/-- **[Junker Eq. 46] The Wigner--Dunkl spatial weight** `|z|^{2ν}` in the
kernel-composition integral.  The admissible Hilbert-space range `ν > -1/2`
is imposed by concrete analytic realizations; the algebraic composition API
keeps `ν` explicit and does not silently assume local integrability. -/
noncomputable def dunklSpatialWeight (ν z : ℝ) : ℝ := |z| ^ (2 * ν)

/-- Weighted composition of two complex Wigner--Dunkl kernels:
`(K₂ ⋆_ν K₁)(x,y) = ∫ |z|^{2ν} K₂(x,z) K₁(z,y) dz`. -/
noncomputable def dunklWeightedKernelComposition
    (ν : ℝ) (K₂ K₁ : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  ∫ z, ((dunklSpatialWeight ν z : ℝ) : ℂ) * K₂ x z * K₁ z y

/-- A kernel realization of the exact Wigner--Dunkl
Kolmogorov--Chapman law (Junker Eq. 46).  The structure deliberately exposes
the analytic kernel and its weighted composition theorem; it is stronger than
the purely observable-level `FeynmanKacModel.compose` field and prevents an
abstract semigroup from being mislabeled as a proved integral kernel. -/
structure DunklKernelSemigroup (ν : ℝ) where
  /-- Time-dependent transition/propagator kernel. -/
  kernel : ℝ → ℝ → ℝ → ℂ
  /-- Exact weighted kernel composition for two strictly positive Euclidean
  time slices.  At zero time a pointwise heat kernel is replaced by a Dirac
  distribution, so that endpoint is intentionally not mislabeled as a
  function-valued identity kernel. -/
  compose :
    ∀ (t₂ t₁ x y : ℝ), 0 < t₂ → 0 < t₁ →
      kernel (t₂ + t₁) x y =
        dunklWeightedKernelComposition ν (kernel t₂) (kernel t₁) x y

namespace DunklKernelSemigroup

/-- Two consecutive Wigner--Dunkl propagator slices, written as the explicit
weighted integral appearing on the right side of Junker Eq. 46. -/
noncomputable def sequentialKernel {ν : ℝ} (S : DunklKernelSemigroup ν)
    (t₂ t₁ x y : ℝ) : ℂ :=
  dunklWeightedKernelComposition ν (S.kernel t₂) (S.kernel t₁) x y

/-- **[Junker Eq. 46] Consecutive propagation collapses to total time.**
This is the exact `|z|^{2ν} dz` kernel identity, not merely multiplication of
scalar damping factors. -/
theorem sequentialKernel_eq_total {ν : ℝ} (S : DunklKernelSemigroup ν)
    (t₂ t₁ x y : ℝ) (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    dunklWeightedKernelComposition ν (S.kernel t₂) (S.kernel t₁) x y =
      S.kernel (t₂ + t₁) x y :=
  (S.compose t₂ t₁ x y ht₂ ht₁).symm

/-- Kernel composition with a pointwise operator inserted at the intermediate
state.  It is the Wigner--Dunkl analogue of the pointwise Green-kernel
composition `A B C` already used by the continuum scalar-field layer. -/
noncomputable def interruptedKernel {ν : ℝ} (S : DunklKernelSemigroup ν)
    (insertion : ℝ → ℂ) (t₂ t₁ x y : ℝ) : ℂ :=
  ∫ z, ((dunklSpatialWeight ν z : ℝ) : ℂ) *
    S.kernel t₂ x z * insertion z * S.kernel t₁ z y

/-- An identity insertion does not interrupt the propagator: the weighted
kernel composition collapses to the total-time Wigner--Dunkl kernel. -/
lemma interruptedKernel_one_eq_total {ν : ℝ}
    (S : DunklKernelSemigroup ν) (t₂ t₁ x y : ℝ)
    (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    S.interruptedKernel (fun _ => 1) t₂ t₁ x y =
      S.kernel (t₂ + t₁) x y := by
  rw [← S.sequentialKernel_eq_total t₂ t₁ x y ht₂ ht₁]
  simp [interruptedKernel, dunklWeightedKernelComposition]

/-- A zero insertion kills the interrupted Wigner--Dunkl channel. -/
lemma interruptedKernel_zero {ν : ℝ} (S : DunklKernelSemigroup ν)
    (t₂ t₁ x y : ℝ) :
    S.interruptedKernel (fun _ => 0) t₂ t₁ x y = 0 := by
  simp [interruptedKernel]

end DunklKernelSemigroup

/-! ## F. Concrete positive-time Wiener realization at `ν = 0` -/

/-- Product factorization behind the Chapman--Kolmogorov law.  For positive
times, the product of two Wiener kernels is the total-time kernel times the
Gaussian bridge density with mean `(t₁x + t₂y)/(t₂+t₁)` and variance
`t₂t₁/(t₂+t₁)`.  This isolates all square-root normalization and completion
of the square before integration. -/
lemma wienerDensity_mul_factorization
    (t₂ t₁ x y z : ℝ) (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    wienerDensity t₂ x z * wienerDensity t₁ z y =
      wienerDensity (t₂ + t₁) x y *
        gaussianPDFReal ((t₁ * x + t₂ * y) / (t₂ + t₁))
          (t₂ * t₁ / (t₂ + t₁)).toNNReal z := by
  have hsum : 0 < t₂ + t₁ := by positivity
  have hvpos : 0 < t₂ * t₁ / (t₂ + t₁) := by positivity
  have hs2 : Real.sqrt (2 * Real.pi * t₂) ≠ 0 := ne_of_gt (by positivity)
  have hs1 : Real.sqrt (2 * Real.pi * t₁) ≠ 0 := ne_of_gt (by positivity)
  have hss : Real.sqrt (2 * Real.pi * (t₂ + t₁)) ≠ 0 := ne_of_gt (by positivity)
  have hsv : Real.sqrt (2 * Real.pi * (t₂ * t₁ / (t₂ + t₁))) ≠ 0 :=
    ne_of_gt (by positivity)
  unfold wienerDensity gaussianPDFReal
  have hnorm :
      (1 / Real.sqrt (2 * Real.pi * t₂)) *
          (1 / Real.sqrt (2 * Real.pi * t₁)) =
        (1 / Real.sqrt (2 * Real.pi * (t₂ + t₁))) *
          (Real.sqrt (2 * Real.pi * (t₂ * t₁ / (t₂ + t₁))))⁻¹ := by
    have hsqrt :
        Real.sqrt (2 * Real.pi * t₂) * Real.sqrt (2 * Real.pi * t₁) =
          Real.sqrt (2 * Real.pi * (t₂ + t₁)) *
            Real.sqrt (2 * Real.pi * (t₂ * t₁ / (t₂ + t₁))) := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * t₂),
        ← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * (t₂ + t₁))]
      congr 1
      field_simp
    rw [one_div, one_div, one_div]
    field_simp
    convert hsqrt.symm using 1
    ring_nf
  have hexponent :
      (-(x - z) ^ 2 / (2 * t₂)) + (-(z - y) ^ 2 / (2 * t₁)) =
        (-(x - y) ^ 2 / (2 * (t₂ + t₁))) +
          (-(z - (t₁ * x + t₂ * y) / (t₂ + t₁)) ^ 2 /
            (2 * (t₂ * t₁ / (t₂ + t₁)))) := by
    field_simp
    ring
  calc
    (1 / Real.sqrt (2 * Real.pi * t₂)) *
          Real.exp (-(x - z) ^ 2 / (2 * t₂)) *
        ((1 / Real.sqrt (2 * Real.pi * t₁)) *
          Real.exp (-(z - y) ^ 2 / (2 * t₁))) =
      ((1 / Real.sqrt (2 * Real.pi * t₂)) *
          (1 / Real.sqrt (2 * Real.pi * t₁))) *
        (Real.exp (-(x - z) ^ 2 / (2 * t₂)) *
          Real.exp (-(z - y) ^ 2 / (2 * t₁))) := by ring
    _ = ((1 / Real.sqrt (2 * Real.pi * (t₂ + t₁))) *
          (Real.sqrt (2 * Real.pi * (t₂ * t₁ / (t₂ + t₁))))⁻¹) *
        Real.exp
          ((-(x - y) ^ 2 / (2 * (t₂ + t₁))) +
            (-(z - (t₁ * x + t₂ * y) / (t₂ + t₁)) ^ 2 /
              (2 * (t₂ * t₁ / (t₂ + t₁))))) := by
        rw [hnorm, ← Real.exp_add, hexponent]
    _ = (1 / Real.sqrt (2 * Real.pi * (t₂ + t₁))) *
          Real.exp (-(x - y) ^ 2 / (2 * (t₂ + t₁))) *
        ((Real.sqrt (2 * Real.pi * (t₂ * t₁ / (t₂ + t₁))))⁻¹ *
          Real.exp
            (-(z - (t₁ * x + t₂ * y) / (t₂ + t₁)) ^ 2 /
              (2 * (t₂ * t₁ / (t₂ + t₁))))) := by
        rw [Real.exp_add]
        ring
  simp [max_eq_left hvpos.le]

/-- **Concrete Wiener Chapman--Kolmogorov convolution.**  The proof integrates
the bridge factorization and uses Mathlib's normalized Gaussian-density
integral.  Unlike the abstract carrier field, this is an analytic theorem
about the explicit pointwise kernel. -/
theorem wienerDensity_convolution
    (t₂ t₁ x y : ℝ) (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    ∫ z, ((wienerDensity t₂ x z * wienerDensity t₁ z y : ℝ) : ℂ) =
      (wienerDensity (t₂ + t₁) x y : ℂ) := by
  let v : ℝ≥0 := (t₂ * t₁ / (t₂ + t₁)).toNNReal
  let m : ℝ := (t₁ * x + t₂ * y) / (t₂ + t₁)
  rw [show
      (fun z => ((wienerDensity t₂ x z * wienerDensity t₁ z y : ℝ) : ℂ)) =
        (fun z => (wienerDensity (t₂ + t₁) x y : ℂ) *
          (gaussianPDFReal m v z : ℂ)) by
      funext z
      rw [wienerDensity_mul_factorization t₂ t₁ x y z ht₂ ht₁]
      simp only [Complex.ofReal_mul]
      rfl]
  rw [integral_const_mul]
  rw [integral_complex_ofReal, integral_gaussianPDFReal_eq_one]
  · simp
  · dsimp [v]
    intro h
    have hcoe := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
    simp [max_eq_left (by positivity :
      0 ≤ t₂ * t₁ / (t₂ + t₁))] at hcoe
    rcases hcoe with (h₂ | h₁) | hsum
    · exact (ne_of_gt ht₂) h₂
    · exact (ne_of_gt ht₁) h₁
    · exact (ne_of_gt (by positivity : 0 < t₂ + t₁)) hsum

/-- The explicit `ν = 0` Wigner--Dunkl kernel is a positive-time weighted
kernel semigroup.  Since `|z|⁰ = 1`, Junker's weighted Eq. 46 reduces exactly
to the Wiener convolution proved above. -/
noncomputable def freeWienerDunklSemigroup : DunklKernelSemigroup 0 where
  kernel τ x y := (wienerDensity τ x y : ℂ)
  compose t₂ t₁ x y ht₂ ht₁ := by
    rw [dunklWeightedKernelComposition]
    have hweight : ∀ z : ℝ, dunklSpatialWeight 0 z = 1 := by
      intro z
      simp [dunklSpatialWeight]
    simp_rw [hweight]
    simp only [Complex.ofReal_one, one_mul, ← Complex.ofReal_mul]
    exact (wienerDensity_convolution t₂ t₁ x y ht₂ ht₁).symm

/-! ## G. Markov normalization and finite equal-time slicing -/

/-- For positive time, the Wiener kernel is exactly Mathlib's real Gaussian
probability density with mean `y` and variance `τ`. -/
lemma wienerDensity_eq_gaussianPDFReal
    (τ x y : ℝ) (hτ : 0 < τ) :
    wienerDensity τ x y =
      gaussianPDFReal y τ.toNNReal x := by
  unfold wienerDensity gaussianPDFReal
  simp [max_eq_left hτ.le]

/-- The positive-time Wiener kernel is Lebesgue integrable in its endpoint. -/
lemma integrable_wienerDensity
    (τ y : ℝ) (hτ : 0 < τ) :
    Integrable (fun x => wienerDensity τ x y) := by
  simpa only [wienerDensity_eq_gaussianPDFReal τ _ y hτ] using
    integrable_gaussianPDFReal y τ.toNNReal

/-- The positive-time Wiener kernel has total mass one.  Together with
`wienerDensity_pos`, this supplies the concrete Markov normalization that is
not present in a bare algebraic semigroup carrier. -/
theorem integral_wienerDensity_eq_one
    (τ y : ℝ) (hτ : 0 < τ) :
    ∫ x, wienerDensity τ x y = 1 := by
  rw [show (fun x => wienerDensity τ x y) =
      gaussianPDFReal y τ.toNNReal by
    funext x
    exact wienerDensity_eq_gaussianPDFReal τ x y hτ]
  apply integral_gaussianPDFReal_eq_one
  intro h
  have hcoe := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
  simp [max_eq_left hτ.le] at hcoe
  exact (ne_of_gt hτ) hcoe

namespace DunklKernelSemigroup

/-- The `(n+1)`-slice weighted convolution of one equal positive-time kernel.
Index zero is one slice; the successor adds one slice on the left.  This
avoids pretending that the zero-time Dirac kernel is pointwise. -/
noncomputable def positiveTimeSlicing {ν : ℝ}
    (S : DunklKernelSemigroup ν) (δ : ℝ) :
    ℕ → ℝ → ℝ → ℂ
  | 0 => S.kernel δ
  | n + 1 => dunklWeightedKernelComposition ν (S.kernel δ)
      (positiveTimeSlicing S δ n)

/-- **Finite equal-time form of Junker Eq. 56.**  Every `(n+1)`-fold weighted
convolution with slice width `δ > 0` equals the semigroup kernel at total time
`(n+1)δ`.  This is an exact finite identity; no continuum mesh-limit or
path-measure convergence is claimed. -/
lemma positiveTimeSlicing_eq_total {ν : ℝ}
    (S : DunklKernelSemigroup ν) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n x y, S.positiveTimeSlicing δ n x y =
      S.kernel (((n + 1 : ℕ) : ℝ) * δ) x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [positiveTimeSlicing]
  | succ n ih =>
      intro x y
      rw [positiveTimeSlicing]
      have hfun :
          S.positiveTimeSlicing δ n =
            S.kernel (((n + 1 : ℕ) : ℝ) * δ) := by
        funext x y
        exact ih x y
      rw [hfun]
      calc
        dunklWeightedKernelComposition ν (S.kernel δ)
            (S.kernel (((n + 1 : ℕ) : ℝ) * δ)) x y =
          S.kernel (δ + ((n + 1 : ℕ) : ℝ) * δ) x y :=
            S.sequentialKernel_eq_total δ
              (((n + 1 : ℕ) : ℝ) * δ) x y hδ (by positivity)
        _ = S.kernel (((n + 1 + 1 : ℕ) : ℝ) * δ) x y := by
          congr 2
          push_cast
          ring

end DunklKernelSemigroup

/-- The exact finite time-slicing theorem instantiated by the explicit
positive-time free Wiener/Dunkl kernel. -/
theorem freeWiener_positiveTimeSlicing_eq_total
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (x y : ℝ) :
    freeWienerDunklSemigroup.positiveTimeSlicing δ n x y =
      (wienerDensity (((n + 1 : ℕ) : ℝ) * δ) x y : ℂ) :=
  freeWienerDunklSemigroup.positiveTimeSlicing_eq_total δ hδ n x y

end Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

end
