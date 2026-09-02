/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
public import Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
public import Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm
public import Physlib.Mathematics.LovelockRund.PoincareStokes
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.VolumeMeasure
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
meta import Zil

/-!
# The diffeomorphism variation of the metric and the Lorentz–Levi-Civita thesis

Loinger, *Proof of a Lorentz and Levi-Civita thesis* (arXiv:1109.5268), argues that the left-hand side of the
Einstein equations, `G^{jk} = R^{jk} − ½g^{jk}R`, is the genuine energy–momentum–stress tensor of the
gravitational field — because it is a *symmetric* tensor that is *covariantly conserved* as a Noether identity
of coordinate (diffeomorphism) invariance, independently of the field equations.

The rigorously algebraic kernel is §2's transformation law (Eq. 7): under the infinitesimal coordinate change
`x'^j = x^j + ε^j`, the metric varies by (minus) its **Lie derivative**,
  `δ*g_{mn} = −(L_ε g)_{mn} = −(ε^s ∂_s g_{mn} + g_{sn} ∂_m ε^s + g_{ms} ∂_n ε^s)`.
This module formalizes that law, its symmetry (which forces the conjugate variational derivative to be
symmetric), and the Killing characterization `δ*g = 0`. The variational/integral steps (Eqs. 8–13, boundary
terms) are not carried out; the paper's conclusion — that `G^{jk}` is symmetric and conserved — is assembled
from the existing `einsteinTensor_symm` and `bianchi_implies_conservation`.

* `metricLieDerivative` — Eq. 7, `(L_ε g)_{mn}` from the metric `g`, its derivatives `dg` and `∂ε` (`dε`).
* `metricLieDerivative_symm`, `metricDiffeoVariation`, `metricDiffeoVariation_symm` — the diffeomorphism
  variation `δ*g = −L_ε g` and its symmetry.
* `IsKillingVector`, `metricDiffeoVariation_zero_iff_isKilling` — `δ*g = 0` iff `ε` is Killing.
* `einsteinTensor_is_thesis_tensor` — Loinger's thesis: `G^{jk}` is symmetric *and* covariantly conserved.
* `noether_conservation` — Eq. 9: `(∀ ε, ∑ᵢ (Div P)ᵢ εⁱ = 0) ⇒ Div P = 0`, the Noether identity for the
  variational derivative of *any* scalar density (arbitrariness of `ε`).
* `einsteinTensor_noether_conserved` — Eq. 13: `G^{jk}_{;k} = 0` derived from diffeomorphism invariance.
* `loinger_thesis_from_invariance` — the full thesis from invariance alone: `G` symmetric, conserved, and `T`
  conserved, with the contracted Bianchi identity *derived* rather than assumed.
* `noether_invariance_iff_secondBianchi` — the two routes to Eq. 13 agree: Noether diffeomorphism invariance
  `∀ ε, ∑ᵢ (∇G)ᵢ εⁱ = 0` **iff** the contracted second (differential) Bianchi identity `∇^μR_{μν} = ½∇_νR`
  (`LeviCivita.BianchiValidation`), both being exactly `∇G = 0` — Loinger's remark that Eq. 13 holds by
  invariance *and* "by virtue of the Bianchi relations."
* `hasDerivAt_det_affine_metric` — Jacobi's determinant variation along an arbitrary metric direction.
* `hasDerivAt_lorentzianVolumeDensity_affine` — the genuine Lorentzian density variation
  `δ√(-det g) = ½√(-det g) tr(g⁻¹δg)`.
* `hasDerivAt_einsteinHilbertDensity_affine` — the exact bulk-density product rule for
  `√(-det g) R`, retaining the curvature variation that must later be reduced by Palatini identity and
  boundary conditions.

**Honest layering.** The Lie-derivative law, its symmetry, and the Noether arbitrariness step (`noether_conservation`)
are exact. The remaining physical input is `hinv` — the diffeomorphism invariance of the action, already in the
post-`IBP` form `∑ᵢ (Div P)ᵢ εⁱ` of Eq. 8; producing that form from `⟨P, δ*g⟩` is the paper's variational
computation (`∫ … d⁴x`, Stokes), which is not carried out.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
open Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm
open Physlib.Mathematics.LovelockRund
open MeasureTheory Set

variable {ι : Type*} [Fintype ι]

/-- **The Lie derivative of the metric** (Loinger Eq. 7) `(L_ε g)_{mn} = ε^s ∂_s g_{mn} + g_{sn} ∂_m ε^s +
g_{ms} ∂_n ε^s`, from the metric `g`, its partial derivatives `dg` (`dg s = ∂_s g`) and the gradient of the
vector field, `dε m s = ∂_m ε^s`. -/
noncomputable def metricLieDerivative (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun m n =>
    (∑ s, ε s * dg s m n) + (∑ s, g m s * dε n s) + (∑ s, g n s * dε m s)

/-- **[The Lie derivative of a symmetric metric is symmetric] `(L_ε g)_{mn} = (L_ε g)_{nm}`** — from the
symmetry of the metric derivatives `∂_s g_{mn} = ∂_s g_{nm}`. This is why the conjugate variational derivative
`P^{jk}` (contracted against `δ*g`) is a *symmetric* tensor. -/
lemma metricLieDerivative_symm (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) (hdg : ∀ s, (dg s)ᵀ = dg s) :
    (metricLieDerivative g dg ε dε)ᵀ = metricLieDerivative g dg ε dε := by
  ext m n
  simp only [Matrix.transpose_apply, metricLieDerivative, Matrix.of_apply]
  rw [show (∑ s, ε s * dg s n m) = ∑ s, ε s * dg s m n from
    Finset.sum_congr rfl fun s _ => by
      rw [show dg s n m = dg s m n from by
        simpa [Matrix.transpose_apply] using (congrFun (congrFun (hdg s) m) n)]]
  ring

/-- **The diffeomorphism variation of the metric** (Loinger Eq. 7) `δ*g = −L_ε g` — the change of the metric
under the infinitesimal coordinate transformation `x'^j = x^j + ε^j`. -/
noncomputable def metricDiffeoVariation (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  - metricLieDerivative g dg ε dε

/-- **[The diffeomorphism variation is symmetric] `δ*g_{mn} = δ*g_{nm}`.** -/
lemma metricDiffeoVariation_symm (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) (hdg : ∀ s, (dg s)ᵀ = dg s) :
    (metricDiffeoVariation g dg ε dε)ᵀ = metricDiffeoVariation g dg ε dε := by
  rw [metricDiffeoVariation, transpose_neg, metricLieDerivative_symm g dg ε dε hdg]

/-- **A Killing vector** `L_ε g = 0` — the metric is unchanged under the flow of `ε`. -/
def IsKillingVector (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ) (dε : Matrix ι ι ℝ) : Prop :=
  metricLieDerivative g dg ε dε = 0

/-- **[The metric is diffeomorphism-invariant iff `ε` is Killing] `δ*g = 0 ↔ IsKillingVector`.** -/
lemma metricDiffeoVariation_zero_iff_isKilling (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ε : ι → ℝ)
    (dε : Matrix ι ι ℝ) :
    metricDiffeoVariation g dg ε dε = 0 ↔ IsKillingVector g dg ε dε := by
  rw [metricDiffeoVariation, neg_eq_zero, IsKillingVector]

omit [Fintype ι] in
/-- **[The Lorentz–Levi-Civita thesis] `G^{jk}` is symmetric and covariantly conserved.** Loinger's
conclusion: the Einstein tensor `G^{jk} = R^{jk} − ½g^{jk}R` — the variational derivative `P^{jk}` of the
Einstein–Hilbert action, conjugate to the symmetric metric variation `δ*g` above — is a symmetric tensor
(`einsteinTensor_symm`) that is covariantly conserved (`bianchi_implies_conservation`), the two defining
properties of a true energy–momentum–stress tensor. Assembled from existing infrastructure; the Noether
derivation of the divergence-free identity `hBianchi` is the paper's §2–3 variational argument. -/
lemma einsteinTensor_is_thesis_tensor
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (Ric g T : Matrix ι ι ℝ) (scalarR κ : ℝ)
    (hRic : Ricᵀ = Ric) (hg : gᵀ = g)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) (hκ : κ ≠ 0) :
    (einsteinTensor Ric scalarR g)ᵀ = einsteinTensor Ric scalarR g ∧ Div T = 0 :=
  ⟨einsteinTensor_symm Ric scalarR g hRic hg,
    bianchi_implies_conservation Div Ric scalarR g T κ hEFE hBianchi hκ⟩


/-- **[Noether: arbitrary variation ⇒ conservation] `(∀ ε, ∑ᵢ (Div P)ᵢ εⁱ = 0) ⇒ Div P = 0`** (Loinger Eq. 9).
The diffeomorphism invariance `δ*_g 𝒥 = 0` of a scalar-density action, after the integration by parts of Eq. 8,
is the linear functional `ε ↦ ∑ⱼ (P^m_{j;m}) εʲ`; its vanishing for *every* vector field `ε` forces the
covariant divergence `Div P = P^m_{;m}` to vanish. This is the Noether identity for the variational derivative
`P` of *any* scalar density, independent of the field equations. -/
lemma noether_conservation [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (P : Matrix ι ι ℝ)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div P i * ε i = 0) : Div P = 0 := by
  funext j
  have h := hinv (Pi.single j 1)
  simpa [Pi.single_apply, Finset.sum_ite_eq'] using h

/-- **[Loinger Eq. 13] the Einstein tensor is covariantly conserved** `G^{jk}_{;k} = 0` as a Noether identity.
For `S = R` the variational derivative of the Einstein–Hilbert action `∫ R √(-g)` is `P^{jk} = G^{jk} =
R^{jk} − ½g^{jk}R` (Hilbert, Eq. 11); the diffeomorphism invariance of the action (`hinv`) therefore forces
`Div G = 0` by `noether_conservation` — the contracted Bianchi identity *derived from coordinate invariance*,
not assumed. -/
lemma einsteinTensor_noether_conserved [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric g : Matrix ι ι ℝ) (scalarR : ℝ)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div (einsteinTensor Ric scalarR g) i * ε i = 0) :
    Div (einsteinTensor Ric scalarR g) = 0 :=
  noether_conservation Div (einsteinTensor Ric scalarR g) hinv

/-- **[The Lorentz–Levi-Civita thesis, from invariance alone]** given only the diffeomorphism invariance of the
Einstein–Hilbert action (`hinv`) and the field equation `G = κT`, the Einstein tensor is symmetric, covariantly
conserved (`G^{jk}_{;k} = 0`, Eq. 13, *derived* via `noether_conservation`), and the matter stress-energy is
conserved. This is Loinger's full conclusion: `G^{jk}` has both defining properties of the true
energy–momentum–stress tensor of the gravitational field, obtained without invoking the field equations to get
the Bianchi identity. -/
lemma loinger_thesis_from_invariance [DecidableEq ι] (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric g T : Matrix ι ι ℝ) (scalarR κ : ℝ) (hRic : Ricᵀ = Ric) (hg : gᵀ = g)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) (hκ : κ ≠ 0)
    (hinv : ∀ ε : ι → ℝ, ∑ i, Div (einsteinTensor Ric scalarR g) i * ε i = 0) :
    (einsteinTensor Ric scalarR g)ᵀ = einsteinTensor Ric scalarR g
      ∧ Div (einsteinTensor Ric scalarR g) = 0 ∧ Div T = 0 := by
  have hcons := einsteinTensor_noether_conserved Div Ric g scalarR hinv
  exact ⟨einsteinTensor_symm Ric scalarR g hRic hg, hcons,
    bianchi_implies_conservation Div Ric scalarR g T κ hEFE hcons hκ⟩


open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

/-- **[Arbitrary test field ⇒ vanishing] `(∀ ε, ∑ᵢ vᵢ εⁱ = 0) ↔ v = 0`** — the linear-algebra core of the
Noether step (`noether_conservation` is its `v = Div P` instance), stated for a divergence covector `v`. -/
lemma forall_inner_eq_zero_iff [DecidableEq ι] (v : ι → ℝ) :
    (∀ ε : ι → ℝ, ∑ i, v i * ε i = 0) ↔ v = 0 := by
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using hj
  · rintro rfl ε
    simp

/-- **[Loinger Eq. 13, both routes agree] Noether invariance ⟺ contracted second Bianchi.** The diffeomorphism
invariance of the Einstein–Hilbert action — `∀ ε, ∑ᵢ (∇G)ᵢ εⁱ = 0`, the Noether/§B route — holds *iff* the
contracted second (differential) Bianchi identity `∇^μ R_{μν} = ½∇_ν R` holds (`contractedSecondBianchi`,
`LeviCivita.BianchiValidation`, the differential-geometry route). Both are exactly `∇G = 0`
(`einsteinDivergence = 0`). This is Loinger's remark that Eq. 13 follows from coordinate invariance *and* is
"identically satisfied by virtue of the Bianchi relations." -/
lemma noether_invariance_iff_secondBianchi [DecidableEq ι] (divRicci gradScalar : ι → ℝ) :
    (∀ ε : ι → ℝ, ∑ i, einsteinDivergence divRicci gradScalar i * ε i = 0)
      ↔ contractedSecondBianchi divRicci gradScalar := by
  rw [forall_inner_eq_zero_iff, einsteinDivergence_eq_zero_iff]

/-- **[Loinger Eq. 13 via the second Bianchi] `∇G = 0`** from the contracted second Bianchi identity — the
differential-geometry route to the conservation of the Einstein tensor (the Bianchi companion of the
Noether-route `einsteinTensor_noether_conserved`). -/
lemma einsteinDivergence_zero_of_secondBianchi (divRicci gradScalar : ι → ℝ)
    (hB : contractedSecondBianchi divRicci gradScalar) :
    einsteinDivergence divRicci gradScalar = 0 :=
  (einsteinDivergence_eq_zero_iff divRicci gradScalar).mpr hB

/-! ### Exact nonlinear metric-density variations -/

/-- The determinant polynomial for the affine perturbation of the identity.
Its linear Taylor coefficient is the matrix trace. -/
noncomputable def determinantVariationPolynomial
    [DecidableEq ι] (M : Matrix ι ι ℝ) : Polynomial ℝ :=
  Matrix.det
    (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)

/-- Evaluating the determinant-variation polynomial gives the determinant
of the affine matrix perturbation. -/
lemma determinantVariationPolynomial_eval [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) :
    (determinantVariationPolynomial M).eval t =
      Matrix.det (1 + t • M) := by
  simp [determinantVariationPolynomial, eval_det,
    ← Matrix.smul_eq_mul_diagonal]

/-- Its derivative at the identity is exactly `tr M`. -/
lemma determinantVariationPolynomial_derivative_zero [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    (determinantVariationPolynomial M).derivative.eval 0 =
      Matrix.trace M := by
  exact Matrix.derivative_det_one_add_X_smul M

/-- Jacobi's formula at the identity, as an actual analytic derivative:
`d/dt det(I + tM)|₀ = tr M`. -/
@[zil_level bridge_theorem]
lemma hasDerivAt_det_one_add_smul [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.det (1 + t • M))
      (Matrix.trace M) 0 := by
  have hp := (determinantVariationPolynomial M).hasDerivAt (0 : ℝ)
  rw [determinantVariationPolynomial_derivative_zero] at hp
  simpa only [determinantVariationPolynomial_eval] using hp

/-- Factoring an affine metric perturbation through a supplied right
inverse. -/
lemma affine_metric_eq_mul_one_add [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ) (hInv : g * gInv = 1) (t : ℝ) :
    g + t • h = g * (1 + t • (gInv * h)) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    ← Matrix.mul_assoc, hInv, Matrix.one_mul]

/-- **Jacobi's determinant formula for an affine metric path.**
For `g(t) = g + t h` and a certified inverse `g⁻¹`,
`d(det g(t))/dt|₀ = det(g) tr(g⁻¹h)`. -/
@[zil_level bridge_theorem]
lemma hasDerivAt_det_affine_metric [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ) (hInv : g * gInv = 1) :
    HasDerivAt (fun t : ℝ => Matrix.det (g + t • h))
      (Matrix.det g * Matrix.trace (gInv * h)) 0 := by
  have hp :=
    (hasDerivAt_det_one_add_smul (gInv * h)).const_mul
      (Matrix.det g)
  have heq :
      (fun t : ℝ => Matrix.det (g + t • h)) =
        fun t : ℝ =>
          Matrix.det g * Matrix.det (1 + t • (gInv * h)) := by
    funext t
    rw [affine_metric_eq_mul_one_add g gInv h hInv t,
      Matrix.det_mul]
  rw [heq]
  exact hp

/-- The real Lorentzian coordinate volume density `√(-det g)`. The
hypothesis `det g < 0` below states the even-dimensional Lorentz-signature
branch relevant to the four-dimensional metric carrier. -/
noncomputable def lorentzianVolumeDensity [DecidableEq ι]
    (g : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (-Matrix.det g)

/-- The coordinate density used by the nonlinear variation is the
Lorentzian branch of the canonical absolute-determinant metric density. -/
@[zil_level bridge_theorem]
lemma lorentzianVolumeDensity_eq_absoluteDeterminantDensity [DecidableEq ι]
    (g : Matrix ι ι ℝ) (hLorentz : Matrix.det g < 0) :
    lorentzianVolumeDensity g =
      PseudoRiemannianMetric.absoluteDeterminantDensity g :=
  (PseudoRiemannianMetric.absoluteDeterminantDensity_eq_sqrt_neg_det
    g hLorentz).symm

/-- **The nonlinear Lorentzian volume-density variation.**
For a nondegenerate Lorentzian metric path,
`δ√(-det g) = ½√(-det g) tr(g⁻¹δg)`. -/
@[zil_level bridge_theorem]
lemma hasDerivAt_lorentzianVolumeDensity_affine [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ) (hInv : g * gInv = 1)
    (hLorentz : Matrix.det g < 0) :
    HasDerivAt
      (fun t : ℝ => lorentzianVolumeDensity (g + t • h))
      (lorentzianVolumeDensity g / 2 *
        Matrix.trace (gInv * h)) 0 := by
  have hdet := (hasDerivAt_det_affine_metric g gInv h hInv).neg
  have hpos : 0 < -Matrix.det g := neg_pos.mpr hLorentz
  have hne : -Matrix.det g ≠ 0 := ne_of_gt hpos
  have hsqrt := hdet.sqrt (by simpa using hne)
  have hsqrt_ne : Real.sqrt (-Matrix.det g) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsq : (Real.sqrt (-Matrix.det g)) ^ 2 = -Matrix.det g :=
    Real.sq_sqrt (le_of_lt hpos)
  have hcoef :
      -(Matrix.det g * Matrix.trace (gInv * h)) /
          (2 * Real.sqrt (-Matrix.det g)) =
        Real.sqrt (-Matrix.det g) / 2 *
          Matrix.trace (gInv * h) := by
    let s := Real.sqrt (-Matrix.det g)
    have hs : s ≠ 0 := by simpa [s] using hsqrt_ne
    have hdet_s : Matrix.det g = -(s ^ 2) := by
      dsimp [s]
      nlinarith [hsq]
    change -(Matrix.det g * Matrix.trace (gInv * h)) / (2 * s) =
      s / 2 * Matrix.trace (gInv * h)
    rw [hdet_s]
    field_simp
  convert hsqrt using 1
  · rfl
  · dsimp [lorentzianVolumeDensity]
    simpa using hcoef.symm

/-- The pointwise Einstein--Hilbert bulk density `√(-det g) R`. -/
noncomputable def einsteinHilbertDensity [DecidableEq ι]
    (g : Matrix ι ι ℝ) (scalarR : ℝ) : ℝ :=
  lorentzianVolumeDensity g * scalarR

/-- **Exact nonlinear Einstein--Hilbert density variation.**
If `R(t)` has directional derivative `δR`, then
`δ(√(-g)R) = √(-g)δR + ½√(-g)tr(g⁻¹δg)R`.

This is the honest pre-integration-by-parts identity. The first summand is
not deleted: turning its curvature variation into the Einstein tensor plus
a boundary divergence still requires the Palatini/boundary theorem. -/
@[zil_level bridge_theorem]
lemma hasDerivAt_einsteinHilbertDensity_affine [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ) (hInv : g * gInv = 1)
    (hLorentz : Matrix.det g < 0)
    (scalarR : ℝ → ℝ) (δscalarR : ℝ)
    (hscalarR : HasDerivAt scalarR δscalarR 0) :
    HasDerivAt
      (fun t : ℝ =>
        einsteinHilbertDensity (g + t • h) (scalarR t))
      (lorentzianVolumeDensity g * δscalarR +
        lorentzianVolumeDensity g / 2 *
          Matrix.trace (gInv * h) * scalarR 0) 0 := by
  have hvol :=
    hasDerivAt_lorentzianVolumeDensity_affine
      g gInv h hInv hLorentz
  have hraw := hvol.mul hscalarR
  have hfun :
      (fun t : ℝ =>
        einsteinHilbertDensity (g + t • h) (scalarR t)) =ᶠ[nhds 0]
        ((fun t : ℝ =>
          lorentzianVolumeDensity (g + t • h)) * scalarR) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hconverted := hraw.congr_of_eventuallyEq hfun
  refine hconverted.congr_deriv ?_
  rw [show g + (0 : ℝ) • h = g by simp]
  ring

/-! ### Existing Einstein--Palatini connection and curvature variation -/

/-- The repository's Einstein--Palatini projective connection really reduces
to the supplied Levi--Civita base after imposing the torsion-free gauge. This
is a composition of the existing projective-mode classification, not a second
implementation of the Palatini connection equation. -/
@[zil_level bridge_theorem]
lemma palatiniProjective_torsionFree_eq_base [DecidableEq ι]
    (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (hd : 2 ≤ Fintype.card ι)
    (hFull :
      IsTorsionFree
        (entropicConnection Γ (projectiveConnection U))) :
    entropicConnection Γ (projectiveConnection U) = Γ := by
  have hU :=
    (entropicConnection_projective_isTorsionFree_iff
      Γ U hΓ hd).mp hFull
  funext l
  ext μ ν
  simp [entropicConnection, projectiveConnection_apply, hU]

/-- The covariant derivative of a connection variation
`C^ρ_{νσ} = δΓ^ρ_{νσ}` with respect to the background connection:
`∇_μ C^ρ_{νσ}`. The derivative jet `dC μ ρ ν σ` is
`∂_μ C^ρ_{νσ}`. -/
noncomputable def connectionVariationCovariantDerivative
    (Γ C : ι → Matrix ι ι ℝ)
    (dC : ι → ι → Matrix ι ι ℝ)
    (μ ρ ν σ : ι) : ℝ :=
  (dC μ ρ) ν σ
    + ∑ l, (Γ ρ) μ l * (C l) ν σ
    - ∑ l, (Γ l) μ ν * (C ρ) l σ
    - ∑ l, (Γ l) μ σ * (C ρ) ν l

/-- The Palatini curvature variation
`δR^ρ_{σμν} = ∇_μ δΓ^ρ_{νσ} - ∇_ν δΓ^ρ_{μσ}`. -/
noncomputable def palatiniRiemannVariation
    (Γ C : ι → Matrix ι ι ℝ)
    (dC : ι → ι → Matrix ι ι ℝ)
    (ρ σ μ ν : ι) : ℝ :=
  connectionVariationCovariantDerivative Γ C dC μ ρ ν σ -
    connectionVariationCovariantDerivative Γ C dC ν ρ μ σ

/-- For a torsion-free background, the covariant Palatini formula is the
linear coefficient obtained by differentiating the existing
`∂Γ - ∂Γ + ΓΓ - ΓΓ` curvature carrier. -/
lemma palatiniRiemannVariation_eq_linearCoefficient
    (Γ C : ι → Matrix ι ι ℝ)
    (dC : ι → ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ) (ρ σ μ ν : ι) :
    palatiniRiemannVariation Γ C dC ρ σ μ ν =
      (dC μ ρ) ν σ - (dC ν ρ) μ σ
      + (∑ l, ((C ρ) μ l * (Γ l) ν σ +
          (Γ ρ) μ l * (C l) ν σ))
      - (∑ l, ((C ρ) ν l * (Γ l) μ σ +
          (Γ ρ) ν l * (C l) μ σ)) := by
  unfold palatiniRiemannVariation
    connectionVariationCovariantDerivative
  have hsym : ∀ l, (Γ l) μ ν = (Γ l) ν μ := by
    intro l
    simpa [Matrix.transpose_apply] using
      congrFun (congrFun (hΓ l) ν) μ
  simp_rw [hsym]
  repeat rw [Finset.sum_add_distrib]
  have hpos :
      (∑ x, (Γ x) ν σ * (C ρ) μ x) =
        ∑ x, (C ρ) μ x * (Γ x) ν σ :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hneg :
      (∑ x, (Γ x) μ σ * (C ρ) ν x) =
        ∑ x, (C ρ) ν x * (Γ x) μ σ :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hpos, hneg]
  ring

/-- **The analytic Palatini identity for the existing curvature.**
The directional derivative at `t=0` of
`R(Γ+tC, ∂Γ+t∂C)` is exactly
`∇_μC^ρ_{νσ}-∇_νC^ρ_{μσ}`. -/
@[zil_level bridge_theorem]
lemma riemannFromConnection_hasDerivAt_connectionVariation
    (Γ C : ι → Matrix ι ι ℝ)
    (dΓ dC : ι → ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ) (ρ σ μ ν : ι) :
    HasDerivAt
      (fun t : ℝ =>
        riemannFromConnection
          (fun a => Γ a + t • C a)
          (fun a b => dΓ a b + t • dC a b)
          ρ σ μ ν)
      (palatiniRiemannVariation Γ C dC ρ σ μ ν) 0 := by
  have haffine (a b : ℝ) :
      HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const b).const_add a
  have hmul {f g : ℝ → ℝ} {f' g' : ℝ}
      (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
      HasDerivAt (fun t => f t * g t)
        (f' * g 0 + f 0 * g') 0 :=
    (hf.mul hg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hadd {f g : ℝ → ℝ} {f' g' : ℝ}
      (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
      HasDerivAt (fun t => f t + g t) (f' + g') 0 :=
    (hf.add hg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsub {f g : ℝ → ℝ} {f' g' : ℝ}
      (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
      HasDerivAt (fun t => f t - g t) (f' - g') 0 :=
    (hf.sub hg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hproduct (a b c d : ℝ) :
      HasDerivAt
        (fun t : ℝ => (a + t * b) * (c + t * d))
        (b * c + a * d) 0 := by
    simpa using hmul (haffine a b) (haffine c d)
  have hsum₁ :
      HasDerivAt
        (fun t : ℝ =>
          ∑ l, ((Γ ρ) μ l + t * (C ρ) μ l) *
            ((Γ l) ν σ + t * (C l) ν σ))
        (∑ l, ((C ρ) μ l * (Γ l) ν σ +
          (Γ ρ) μ l * (C l) ν σ)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      hproduct ((Γ ρ) μ l) ((C ρ) μ l)
        ((Γ l) ν σ) ((C l) ν σ)
  have hsum₂ :
      HasDerivAt
        (fun t : ℝ =>
          ∑ l, ((Γ ρ) ν l + t * (C ρ) ν l) *
            ((Γ l) μ σ + t * (C l) μ σ))
        (∑ l, ((C ρ) ν l * (Γ l) μ σ +
          (Γ ρ) ν l * (C l) μ σ)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      hproduct ((Γ ρ) ν l) ((C ρ) ν l)
        ((Γ l) μ σ) ((C l) μ σ)
  have h :=
    hsub
      (hadd
        (hsub
          (haffine ((dΓ μ ρ) ν σ) ((dC μ ρ) ν σ))
          (haffine ((dΓ ν ρ) μ σ) ((dC ν ρ) μ σ)))
        hsum₁)
      hsum₂
  rw [palatiniRiemannVariation_eq_linearCoefficient
    Γ C dC hΓ]
  simpa only [riemannFromConnection, Pi.add_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h

/-- Ricci contraction of the Palatini Riemann variation. -/
noncomputable def palatiniRicciVariation
    (Γ C : ι → Matrix ι ι ℝ)
    (dC : ι → ι → Matrix ι ι ℝ)
    (σ ν : ι) : ℝ :=
  ∑ μ, palatiniRiemannVariation Γ C dC μ σ μ ν

/-- Differentiation commutes with the existing finite Ricci contraction. -/
@[zil_level bridge_theorem]
lemma ricciFromConnection_hasDerivAt_connectionVariation
    (Γ C : ι → Matrix ι ι ℝ)
    (dΓ dC : ι → ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ) (σ ν : ι) :
    HasDerivAt
      (fun t : ℝ =>
        ricciFromConnection
          (fun a => Γ a + t • C a)
          (fun a b => dΓ a b + t • dC a b)
          σ ν)
      (palatiniRicciVariation Γ C dC σ ν) 0 := by
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ μ, riemannFromConnection
            (fun a => Γ a + t • C a)
            (fun a b => dΓ a b + t • dC a b)
            μ σ μ ν)
        (∑ μ,
          palatiniRiemannVariation Γ C dC μ σ μ ν) 0 :=
    HasDerivAt.fun_sum fun μ _ =>
      riemannFromConnection_hasDerivAt_connectionVariation
        Γ C dΓ dC hΓ μ σ μ ν
  simpa only [ricciFromConnection,
    palatiniRicciVariation] using hsum

/-- Scalar curvature constructed from the existing connection-built Ricci
tensor and an inverse metric. -/
noncomputable def scalarCurvatureFromConnection
    (gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ) : ℝ :=
  ∑ σ, ∑ ν, gInv σ ν * ricciFromConnection Γ dΓ σ ν

/-- Full scalar-curvature variation: variation of the inverse metric
contracted with Ricci plus the inverse metric contracted with the Palatini
Ricci variation. -/
noncomputable def palatiniScalarCurvatureVariation
    (gInv δgInv : Matrix ι ι ℝ)
    (Γ C : ι → Matrix ι ι ℝ)
    (dΓ dC : ι → ι → Matrix ι ι ℝ) : ℝ :=
  (∑ σ, ∑ ν,
      δgInv σ ν * ricciFromConnection Γ dΓ σ ν) +
    ∑ σ, ∑ ν,
      gInv σ ν * palatiniRicciVariation Γ C dC σ ν

/-- **The contracted scalar Palatini identity.**
The inverse-metric and connection variations are differentiated together;
the derivative is the sum of the Ricci metric contraction and the contracted
Palatini Ricci variation. -/
@[zil_level bridge_theorem]
lemma scalarCurvatureFromConnection_hasDerivAt_palatini
    (gInv δgInv : Matrix ι ι ℝ)
    (Γ C : ι → Matrix ι ι ℝ)
    (dΓ dC : ι → ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ) :
    HasDerivAt
      (fun t : ℝ =>
        scalarCurvatureFromConnection
          (gInv + t • δgInv)
          (fun a => Γ a + t • C a)
          (fun a b => dΓ a b + t • dC a b))
      (palatiniScalarCurvatureVariation
        gInv δgInv Γ C dΓ dC) 0 := by
  have haffine (a b : ℝ) :
      HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const b).const_add a
  have hmul {f g : ℝ → ℝ} {f' g' : ℝ}
      (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
      HasDerivAt (fun t => f t * g t)
        (f' * g 0 + f 0 * g') 0 :=
    (hf.mul hg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hterms (σ ν : ι) :
      HasDerivAt
        (fun t : ℝ =>
          (gInv σ ν + t * δgInv σ ν) *
            ricciFromConnection
              (fun a => Γ a + t • C a)
              (fun a b => dΓ a b + t • dC a b)
              σ ν)
        (δgInv σ ν * ricciFromConnection Γ dΓ σ ν +
          gInv σ ν *
            palatiniRicciVariation Γ C dC σ ν) 0 := by
    have hRic :=
      ricciFromConnection_hasDerivAt_connectionVariation
        Γ C dΓ dC hΓ σ ν
    simpa using
      hmul (haffine (gInv σ ν) (δgInv σ ν)) hRic
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ σ, ∑ ν,
            (gInv σ ν + t * δgInv σ ν) *
              ricciFromConnection
                (fun a => Γ a + t • C a)
                (fun a b => dΓ a b + t • dC a b)
                σ ν)
        (∑ σ, ∑ ν,
          (δgInv σ ν * ricciFromConnection Γ dΓ σ ν +
            gInv σ ν *
              palatiniRicciVariation Γ C dC σ ν)) 0 :=
    HasDerivAt.fun_sum fun σ _ =>
      HasDerivAt.fun_sum fun ν _ => hterms σ ν
  have hcoeff :
      (∑ σ, ∑ ν,
          (δgInv σ ν * ricciFromConnection Γ dΓ σ ν +
            gInv σ ν *
              palatiniRicciVariation Γ C dC σ ν)) =
        palatiniScalarCurvatureVariation
          gInv δgInv Γ C dΓ dC := by
    unfold palatiniScalarCurvatureVariation
    rw [Finset.sum_congr rfl fun _ _ =>
      Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
  rw [← hcoeff]
  simpa only [scalarCurvatureFromConnection,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hsum

/-- The derivative of the inverse metric along a covariant metric variation:
`δg⁻¹ = -g⁻¹(δg)g⁻¹`. -/
noncomputable def inverseMetricVariation [DecidableEq ι]
    (gInv h : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  -(gInv * h * gInv)

/-- The inverse-metric variation is symmetric when the inverse metric and
covariant metric variation are symmetric. -/
lemma inverseMetricVariation_symm [DecidableEq ι]
    (gInv h : Matrix ι ι ℝ)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hh : ∀ i j, h i j = h j i) :
    ∀ i j, inverseMetricVariation gInv h i j =
      inverseMetricVariation gInv h j i := by
  intro i j
  simp only [inverseMetricVariation, Matrix.neg_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hgInv j b, hh b a, hgInv a i]
  ring

/-- The inverse-metric variation solves the differentiated right-inverse
constraint `δg g⁻¹ + g δg⁻¹ = 0`. -/
@[zil_level bridge_theorem]
lemma inverseMetricVariation_linearized_rightInverse [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ) (hInv : g * gInv = 1) :
    h * gInv + g * inverseMetricVariation gInv h = 0 := by
  unfold inverseMetricVariation
  rw [Matrix.mul_neg, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hInv, Matrix.one_mul]
  simp

/-- **Einstein--Hilbert density derivative through the Palatini chain.**
This composes the nonlinear determinant/volume derivative with the existing
connection-built Riemann and Ricci tensors, their Palatini derivative, scalar
contraction, and the actual inverse-metric variation. -/
@[zil_level physical_theorem]
lemma einsteinHilbertDensity_hasDerivAt_palatini [DecidableEq ι]
    (g gInv h : Matrix ι ι ℝ)
    (Γ C : ι → Matrix ι ι ℝ)
    (dΓ dC : ι → ι → Matrix ι ι ℝ)
    (hInv : g * gInv = 1) (hLorentz : Matrix.det g < 0)
    (hΓ : IsTorsionFree Γ) :
    HasDerivAt
      (fun t : ℝ =>
        einsteinHilbertDensity
          (g + t • h)
          (scalarCurvatureFromConnection
            (gInv + t • inverseMetricVariation gInv h)
            (fun a => Γ a + t • C a)
            (fun a b => dΓ a b + t • dC a b)))
      (lorentzianVolumeDensity g *
          palatiniScalarCurvatureVariation
            gInv (inverseMetricVariation gInv h)
              Γ C dΓ dC +
        lorentzianVolumeDensity g / 2 *
          Matrix.trace (gInv * h) *
            scalarCurvatureFromConnection gInv Γ dΓ) 0 := by
  refine (hasDerivAt_einsteinHilbertDensity_affine
      g gInv h hInv hLorentz
      (fun t =>
        scalarCurvatureFromConnection
          (gInv + t • inverseMetricVariation gInv h)
          (fun a => Γ a + t • C a)
          (fun a b => dΓ a b + t • dC a b))
      (palatiniScalarCurvatureVariation
        gInv (inverseMetricVariation gInv h) Γ C dΓ dC)
      (scalarCurvatureFromConnection_hasDerivAt_palatini
        gInv (inverseMetricVariation gInv h)
          Γ C dΓ dC hΓ)).congr_deriv ?_
  simp

/-! ### Existing GHY and Stokes boundary reduction -/

/-- Under fixed induced metric and vanishing tangential-divergence
contribution, the existing GHY boundary identity makes the Einstein--Hilbert
connection-variation boundary integrand cancel the `2 δK` surface variation.
This is exactly the scalar boundary data already formalized in
`GHYSurfaceTerm.boundaryIntegrand_eq`. -/
@[zil_level bridge_theorem]
lemma ghy_cancels_fixedMetric_palatiniBoundary
    (δvn δK dK_h dmuK dGamma_hh dGamma_nh εDdA : ℝ)
    (h20 : δK = dK_h + dmuK - dGamma_hh)
    (h26 : δK = -εDdA - dmuK + dGamma_nh)
    (h28 : δvn = dGamma_hh - dGamma_nh)
    (hfixed : dK_h = 0) (htangent : εDdA = 0) :
    δvn + 2 * δK = 0 := by
  rw [boundaryIntegrand_eq δvn δK dK_h dmuK
    dGamma_hh dGamma_nh εDdA h20 h26 h28,
    hfixed, htangent]
  ring

/-- The integrated Palatini first-variation carrier on a genuine continuum
coordinate box: bulk Euler--Lagrange density plus the Fréchet-defined
divergence of the boundary current. -/
noncomputable def integratedEinsteinHilbertPalatiniVariation
    {n : ℕ} (a b : BoxPoint n)
    (bulk : BoxPoint n → ℝ)
    (boundaryDerivative :
      BoxPoint n → BoxPoint n →L[ℝ] BoxVector n ℝ) : ℝ :=
  ∫ x in Icc a b,
    bulk x + boxDivergence boundaryDerivative x

/-- **Genuine Stokes reduction of the integrated Palatini variation.**
On a rectangular continuum chart, if the oriented boundary flux vanishes,
the existing Bochner divergence theorem removes the Palatini divergence and
leaves exactly the integrated bulk Euler--Lagrange density. -/
@[zil_level physical_theorem]
lemma integratedEinsteinHilbertPalatiniVariation_eq_bulk_of_boundary
    {n : ℕ}
    (a b : BoxPoint n) (hle : a ≤ b)
    (bulk : BoxPoint n → ℝ)
    (boundaryCurrent : BoxPoint n → BoxVector n ℝ)
    (boundaryDerivative :
      BoxPoint n → BoxPoint n →L[ℝ] BoxVector n ℝ)
    (singular : Set (BoxPoint n))
    (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn boundaryCurrent (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ singular,
        HasFDerivAt boundaryCurrent (boundaryDerivative x) x)
    (hbulk : IntegrableOn bulk (Icc a b))
    (hdiv :
      IntegrableOn (boxDivergence boundaryDerivative) (Icc a b))
    (hboundary :
      (∑ i : Fin (n + 1),
        ((∫ x in Icc
            (a ∘ i.succAbove) (b ∘ i.succAbove),
            boundaryCurrent (i.insertNth (b i) x) i) -
          ∫ x in Icc
            (a ∘ i.succAbove) (b ∘ i.succAbove),
            boundaryCurrent (i.insertNth (a i) x) i)) = 0) :
    integratedEinsteinHilbertPalatiniVariation
        a b bulk boundaryDerivative =
      ∫ x in Icc a b, bulk x := by
  rw [integratedEinsteinHilbertPalatiniVariation,
    MeasureTheory.integral_add hbulk hdiv,
    integral_boxDivergence_eq_zero_of_boundary
      a b hle boundaryCurrent boundaryDerivative singular
      hsingular hcontinuous hderiv hdiv hboundary,
    add_zero]

/- ZIL-BEGIN -/

zil attach hasDerivAt_det_affine_metric where
  formalizes @ "claim:jacobi-determinant-variation-for-an-affine-finite-metric-path-is-an-actual-analytic-derivative-det-prime-equals-det-times-trace-of-inverse-times-variation",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:Matrix.derivative_det_one_add_X_smul",
  caveat @ "scope:finite-coordinate-matrix-path-with-a-certified-right-inverse"

zil attach hasDerivAt_lorentzianVolumeDensity_affine where
  formalizes @ "claim:the-lorentzian-coordinate-volume-density-has-variation-delta-sqrt-minus-det-g-equals-one-half-sqrt-minus-det-g-times-trace-g-inverse-delta-g",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.hasDerivAt_det_affine_metric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.lorentzianVolumeDensity_eq_absoluteDeterminantDensity",
  caveat @ "premise:the-selected-coordinate-metric-has-negative-determinant-and-a-certified-inverse",
  caveat @ "scope:this-theorem-is-pointwise-the-metric-built-global-measure-and-action-are-supplied-downstream-by-GlobalEinsteinHilbertAction"

zil attach hasDerivAt_einsteinHilbertDensity_affine where
  formalizes @ "claim:the-exact-pointwise-einstein-hilbert-density-variation-splits-into-the-scalar-curvature-variation-and-the-lorentzian-volume-density-trace-variation",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.hasDerivAt_lorentzianVolumeDensity_affine",
  caveat @ "scope:pre-integration-by-parts-bulk-density-identity-the-curvature-variation-is-retained",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.einsteinHilbertDensity_hasDerivAt_palatini"

zil_file_contract physlib.einsteinHilbertNonlinearDensityVariation where
  promises "The nonlinear metric determinant, Lorentzian volume density and pointwise Einstein-Hilbert bulk density have genuine analytic directional derivatives. The scalar-curvature variation is now discharged by the existing connection-built Riemann carrier through an analytic Palatini derivative and its Ricci/scalar contractions; the GHY identity and genuine coordinate-box divergence theorem remove the resulting boundary contribution under explicit fixed-boundary and regularity hypotheses."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "mathlib:Matrix.derivative_det_one_add_X_smul",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.lorentzianVolumeDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.einsteinHilbertDensity"
  ]
  forbids_substitutes [
    "calling the pointwise density derivative a completed global Einstein-Hilbert action variation",
    "dropping the scalar-curvature variation without a Palatini and boundary theorem",
    "treating a negative determinant as a complete proof of Lorentzian signature"
  ]
  witnessed_by [
    hasDerivAt_det_affine_metric,
    hasDerivAt_lorentzianVolumeDensity_affine,
    hasDerivAt_einsteinHilbertDensity_affine
  ]

zil attach palatiniProjective_torsionFree_eq_base where
  formalizes @ "claim:the-existing-einstein-palatini-projective-connection-reduces-exactly-to-the-levi-civita-base-after-the-torsion-free-gauge-condition",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.entropicConnection_projective_isTorsionFree_iff",
  caveat @ "scope:finite-coordinate-index-projective-mode-classification"

zil attach riemannFromConnection_hasDerivAt_connectionVariation where
  formalizes @ "claim:the-analytic-directional-derivative-of-the-existing-connection-built-riemann-curvature-is-the-palatini-covariant-curl-of-the-connection-variation",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.entropicConnection_projective_isTorsionFree_iff",
  caveat @ "premise:the-background-connection-is-torsion-free"

zil attach scalarCurvatureFromConnection_hasDerivAt_palatini where
  formalizes @ "claim:the-palatini-riemann-variation-commutes-with-ricci-and-inverse-metric-scalar-contraction",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.riemannFromConnection_hasDerivAt_connectionVariation"

zil attach einsteinHilbertDensity_hasDerivAt_palatini where
  formalizes @ "claim:the-nonlinear-einstein-hilbert-coordinate-density-has-an-actual-directional-derivative-built-from-the-inverse-metric-variation-and-the-contracted-palatini-connection-variation",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.hasDerivAt_einsteinHilbertDensity_affine",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.scalarCurvatureFromConnection_hasDerivAt_palatini",
  caveat @ "scope:pointwise-coordinate-density-derivative-before-continuum-integral-interchange"

zil attach ghy_cancels_fixedMetric_palatiniBoundary where
  formalizes @ "claim:the-existing-ghy-boundary-identity-cancels-the-palatini-connection-variation-boundary-integrand-under-fixed-induced-metric-and-zero-tangential-divergence",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm.boundaryIntegrand_eq",
  caveat @ "scope:exact-scalar-boundary-data-identity-using-the-repositorys-existing-ghy-carrier"

zil attach integratedEinsteinHilbertPalatiniVariation_eq_bulk_of_boundary where
  formalizes @ "claim:on-a-genuine-continuum-coordinate-box-the-bochner-divergence-theorem-removes-the-palatini-boundary-divergence-when-the-oriented-boundary-flux-vanishes",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.integral_boxDivergence_eq_zero_of_boundary",
  caveat @ "premise:continuity-frechet-differentiability-integrability-and-zero-oriented-boundary-flux-are-explicit",
  caveat @ "scope:coordinate-box-stokes-reduction-not-yet-an-atlas-independent-global-manifold-action-integral"

zil_file_contract physlib.einsteinHilbertPalatiniBoundaryReduction where
  promises "The existing Einstein-Palatini projective connection, connection-built Riemann/Ricci curvature, GHY boundary identity and genuine Bochner box-divergence theorem are composed into one nonlinear Einstein-Hilbert variation layer: torsion-free gauge fixing returns the Levi-Civita base; the analytic curvature derivative is the Palatini covariant curl; contraction gives the scalar-curvature derivative; the actual inverse-metric derivative feeds the nonlinear density derivative; and explicit fixed-boundary or zero-flux hypotheses remove the boundary term."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.entropicConnection_projective_isTorsionFree_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.GHYSurfaceTerm.boundaryIntegrand_eq",
    "lean:Physlib.Mathematics.LovelockRund.integral_boxDivergence_eq_zero_of_boundary"
  ]
  forbids_substitutes [
    "introducing-a-second-independent-riemann-or-palatini-connection-carrier",
    "dropping-the-curvature-variation-before-proving-its-analytic-derivative",
    "discarding-the-boundary-divergence-without-explicit-ghy-or-zero-flux-hypotheses",
    "calling-a-coordinate-box-integral-an-atlas-independent-global-action"
  ]
  witnessed_by [
    palatiniProjective_torsionFree_eq_base,
    riemannFromConnection_hasDerivAt_connectionVariation,
    ricciFromConnection_hasDerivAt_connectionVariation,
    scalarCurvatureFromConnection_hasDerivAt_palatini,
    einsteinHilbertDensity_hasDerivAt_palatini,
    ghy_cancels_fixedMetric_palatiniBoundary,
    integratedEinsteinHilbertPalatiniVariation_eq_bulk_of_boundary
  ]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

end
