/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The regularization layer: APS `η`-function, the local limit `K → δ`, and the gauge measure

The three analytic-layer items the Aastrup–Grimstrup arc
(arXiv:2501.00005 / arXiv:2410.07290) kept as recorded scope, at their exact cores.

## §A — the Atiyah–Patodi–Singer `η`-function (the regularization behind Eq. 8)

`η(s) = Σ_λ sign(λ)·|λ|^{−s}` — for the finite spectra of the matrix carriers the
series is a finite sum, so the APS analytic continuation is *trivial* and the
regularized invariant is computable:

* `etaFunction` — the finite `η`-function of a spectrum `λ : Fin n → ℝ`.
* `etaFunction_continuous` — for a spectrum avoiding `0` the `η`-function is
  continuous in `s` (the finite-dimensional face of "`η(s)` extends
  meromorphically and is regular at `s = 0`").
* `etaFunction_zero` / `etaFunction_zero_eq_count` — the regularized value at
  `s = 0` is the naive asymmetry count: `η(0) = Σ sign λ = #{λ > 0} − #{λ < 0}` —
  the spectral asymmetry the paper's `Tr_ξ(i∇^A)` measures.
* `etaFunction_symmetric_zero` — for a spectrum symmetric under an involutive
  pairing `λ ↦ −λ`, the **whole** `η`-function vanishes (not just its value at
  `0`): the eigenvalue-level face of
  `ConfigurationSpaceSpectralAsymmetry.spectralAsymmetry_vanishes_of_symmetric`.

## §B — the local limit `K → δ` (paper page 12)

The kernel `K(m₁,m₂) = Σᵢξᵢ(m₁)ξᵢ(m₂)` *"gives us a Dirac delta function"* in the
local limit. The exact mechanism: the kernel operator `K f = Σᵢ⟪ξᵢ, f⟫·ξᵢ` of an
orthonormal family

* reproduces the family (`kernelOperator_reproduces`) and is idempotent
  (`kernelOperator_projection`) — a projection, the finite-rank truncation of `δ`;
* acts as the **identity on the span** (`kernelOperator_reproduces_span`);
* hence for a **complete** family — the local limit, where the `ξᵢ` exhaust the
  one-forms — it *is* the delta: `K f = f` for every state
  (`localLimit_kernel_delta`). This is the limit in which
  `(∫Tr(ξᵢ∧F))² → ∫Tr(F²)` and the smeared CAR/CCR kernels
  (`smearedField_CAR_kernel`, `smeared_CCR_kernel`) become the local canonical
  relations.

## §C — the `L²(ℱ)`/BRST gauge measure (papers §2.1)

The gauge fixing `𝒜 ≃ ℱ × 𝒢` (`ConfigurationSpaceGaugeGeometry.gaugeSliceEquiv`)
lifts to the measure level: if the measure on the configuration space factorizes
through the slice equivalence into a product measure, then

* `gauge_integral_factorizes` — for a **gauge-invariant** observable (constant
  along the `𝒢`-factor), the configuration-space integral splits as

  `∫_𝒜 f dμ = vol(𝒢) · ∫_ℱ f dμ_ℱ` —

  the gauge-group volume factors out and the observable descends to the slice:
  `L²(𝒜) = L²(ℱ × 𝒢)` with gauge-invariant states living in
  `L²(ℱ) ⊗ (constants)` — the measure-theoretic content of *"work with `ℱ`
  instead of `𝒜`"* and of the Faddeev–Popov/BRST division by the gauge volume.
  (Applied to `|f|²` this is the `L²`-norm factorization.)

## Honest scope

§A is the finite-spectrum `η` (the infinite-dimensional meromorphic continuation
and the APS index theorem are the analytic frontier); §B states completeness as a
span hypothesis (the Sobolev-norm control of *which* families are complete is the
papers' [3]); §C takes the product-factorization of the measure as the hypothesis
(constructing it from a `𝒢`-invariant measure is the Weil-measure step, and the
FP determinant is absorbed into `μ_ℱ`; ghosts are not constructed).

## References

* M. F. Atiyah, V. K. Patodi, I. M. Singer, *Spectral asymmetry and Riemannian
  geometry I–III*, Math. Proc. Camb. Philos. Soc. 77/78/79 (1975–76).
* J. Aastrup, J. M. Grimstrup, arXiv:2410.07290 (Eq. 8, p. 12), arXiv:2309.06374
  (the `L²(ℱ)` construction), arXiv:2501.00005 §2.
* Carriers: `ConfigurationSpaceSpectralAsymmetry` (`spectralInvariant`),
  `ConfigurationSpaceGaugeGeometry` (`gaugeSliceEquiv`),
  `ConfigurationSpaceDiracFluctuation` (the smeared kernels).
-/

set_option autoImplicit false

open MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization

/-! ## §A — the APS `η`-function -/

variable {n : ℕ}

/-- **The finite Atiyah–Patodi–Singer `η`-function** of a spectrum:
`η(s) = Σᵢ sign(λᵢ)·|λᵢ|^{−s}`. -/
noncomputable def etaFunction (lam : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i, Real.sign (lam i) * |lam i| ^ (-s)

/-- **The finite `η`-function is continuous** (for a spectrum avoiding `0`) — the
finite-dimensional face of the APS meromorphic continuation being regular at
`s = 0`. -/
theorem etaFunction_continuous (lam : Fin n → ℝ) (hlam : ∀ i, lam i ≠ 0) :
    Continuous (etaFunction lam) := by
  unfold etaFunction
  refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
  have hpos : 0 < |lam i| := abs_pos.mpr (hlam i)
  have hrw : (fun s : ℝ => |lam i| ^ (-s))
      = fun s => Real.exp (Real.log |lam i| * (-s)) := by
    funext s
    rw [Real.rpow_def_of_pos hpos]
  rw [hrw]
  exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)

/-- **The regularized value at `s = 0`**: `η(0) = Σᵢ sign λᵢ`. -/
theorem etaFunction_zero (lam : Fin n → ℝ) :
    etaFunction lam 0 = ∑ i, Real.sign (lam i) := by
  unfold etaFunction
  simp [Real.rpow_zero]

/-- **`η(0)` is the spectral asymmetry count**: `η(0) = #{λ > 0} − #{λ < 0}` — the
asymmetry of the spectrum, the quantity the paper's `Tr_ξ(i∇^A)` measures. -/
theorem etaFunction_zero_eq_count (lam : Fin n → ℝ) :
    etaFunction lam 0
      = ((Finset.univ.filter fun i => 0 < lam i).card : ℝ)
        - ((Finset.univ.filter fun i => lam i < 0).card : ℝ) := by
  rw [etaFunction_zero]
  have hsign : ∀ x : ℝ,
      Real.sign x = (if 0 < x then (1 : ℝ) else 0) - (if x < 0 then (1 : ℝ) else 0) := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, if_neg (asymm h), if_pos h]
      norm_num
    · rw [h, Real.sign_zero]
      norm_num
    · rw [Real.sign_of_pos h, if_pos h, if_neg (asymm h)]
      norm_num
  rw [Finset.sum_congr rfl fun i _ => hsign (lam i), Finset.sum_sub_distrib,
    Finset.sum_boole, Finset.sum_boole]

/-- **A symmetric spectrum has identically vanishing `η`** — for an involutive
pairing `σ` with `λ(σ i) = −λ(i)`, the terms cancel pairwise for *every* `s`, not
only at `s = 0`: the eigenvalue-level face of
`spectralAsymmetry_vanishes_of_symmetric`. -/
theorem etaFunction_symmetric_zero (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hinv : ∀ i, σ (σ i) = i) (hσ : ∀ i, lam (σ i) = -lam i) (s : ℝ) :
    etaFunction lam s = 0 := by
  unfold etaFunction
  refine Finset.sum_involution (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i _
    rw [hσ i, Real.sign_neg, abs_neg]
    ring
  · intro i _ hne hfix
    have hzero : lam i = 0 := by
      have := hσ i
      rw [hfix] at this
      linarith
    exact hne (by rw [hzero, Real.sign_zero, zero_mul])
  · intro i _
    exact Finset.mem_univ _
  · intro i _
    exact hinv i

/-! ## §B — the local limit `K → δ` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The kernel operator** `K f = Σᵢ ⟪ξᵢ, f⟫·ξᵢ` — the action of the paper's
kernel `K(m₁,m₂) = Σᵢξᵢ(m₁)ξᵢ(m₂)` on states. -/
noncomputable def kernelOperator (ξ : Fin n → E) (f : E) : E :=
  ∑ i, (inner ℂ (ξ i) f) • ξ i

/-- The kernel reproduces the family: `K ξⱼ = ξⱼ`. -/
theorem kernelOperator_reproduces {ξ : Fin n → E} (hON : Orthonormal ℂ ξ)
    (j : Fin n) : kernelOperator ξ (ξ j) = ξ j := by
  unfold kernelOperator
  simp [orthonormal_iff_ite.mp hON, ite_smul]

/-- The kernel operator is idempotent — a projection, the finite-rank truncation of
the delta. -/
theorem kernelOperator_projection {ξ : Fin n → E} (hON : Orthonormal ℂ ξ) (f : E) :
    kernelOperator ξ (kernelOperator ξ f) = kernelOperator ξ f := by
  unfold kernelOperator
  simp [orthonormal_iff_ite.mp hON, mul_ite]

/-- **The kernel is the identity on the span**: for any state generated by the
family, `K f = f` — the reproducing/delta property on the accessible sector. -/
theorem kernelOperator_reproduces_span {ξ : Fin n → E} (hON : Orthonormal ℂ ξ)
    {f : E} (hf : f ∈ Submodule.span ℂ (Set.range ξ)) :
    kernelOperator ξ f = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact kernelOperator_reproduces hON j
  | zero => simp [kernelOperator]
  | add x y hx hy ihx ihy =>
      have hsplit : kernelOperator ξ (x + y) = kernelOperator ξ x + kernelOperator ξ y := by
        simp [kernelOperator, add_smul, Finset.sum_add_distrib]
      rw [hsplit, ihx, ihy]
  | smul c x hx ih =>
      have hsmul : kernelOperator ξ (c • x) = c • kernelOperator ξ x := by
        simp [kernelOperator, Finset.smul_sum, smul_smul]
      rw [hsmul, ih]

/-- **The local limit `K → δ`** (paper page 12): when the family is **complete** —
the local limit, in which the `ξᵢ` exhaust the one-forms — the kernel acts as the
identity on every state: `K = δ`, the limit in which
`(∫Tr(ξᵢ∧F))² → ∫Tr(F²)` and the smeared CAR/CCR kernels become the local
canonical relations. -/
theorem localLimit_kernel_delta {ξ : Fin n → E} (hON : Orthonormal ℂ ξ)
    (hcomplete : ∀ f : E, f ∈ Submodule.span ℂ (Set.range ξ)) (f : E) :
    kernelOperator ξ f = f :=
  kernelOperator_reproduces_span hON (hcomplete f)

/-! ## §B.1 — The covariant Sobolev kernel of Aastrup-Grimstrup 2008 -/

/-- **Weighted finite spectral kernel.** If `ξᵢ` are eigenmodes of the covariant
Laplacian/Dirac square and `wᵢ = f(λᵢ)^2`, this is the finite-mode version of the
paper's kernel `K_{f,A}(m₁,m₂) = Σᵢ ξᵢ(m₁)ξᵢ(m₂)` acting as `f(Δ_A)^2`. -/
noncomputable def weightedKernelOperator (ξ : Fin n → E) (w : Fin n → ℂ) (f : E) : E :=
  ∑ i, (w i * inner ℂ (ξ i) f) • ξ i

/-- On an orthonormal eigenbasis, the weighted kernel multiplies the `j`-th mode by
its spectral weight. This is the checked finite form of
`f(Δ_A)^2 ξⱼ = f(λⱼ)^2 ξⱼ`. -/
lemma weightedKernelOperator_apply_basis {ξ : Fin n → E} (hON : Orthonormal ℂ ξ)
    (w : Fin n → ℂ) (j : Fin n) :
    weightedKernelOperator ξ w (ξ j) = w j • ξ j := by
  unfold weightedKernelOperator
  simp [orthonormal_iff_ite.mp hON, mul_ite, ite_smul]

/-- With unit weights, the weighted kernel is the unweighted reproducing kernel
`kernelOperator`. This reuses the existing local-limit kernel instead of introducing
a second copy of the delta approximation. -/
lemma weightedKernelOperator_one_eq_kernelOperator (ξ : Fin n → E) :
    weightedKernelOperator ξ (fun _ => 1) = kernelOperator ξ := by
  funext f
  simp [weightedKernelOperator, kernelOperator]

/-- The weighted kernel composed with itself squares the spectral weights on each
basis mode, the finite spectral-calculus identity behind using `K_{f,A}` as the
integral kernel of `f(Δ_A)^2`. -/
lemma weightedKernelOperator_apply_basis_twice {ξ : Fin n → E} (hON : Orthonormal ℂ ξ)
    (w : Fin n → ℂ) (j : Fin n) :
    weightedKernelOperator ξ w (weightedKernelOperator ξ w (ξ j)) = (w j * w j) • ξ j := by
  rw [weightedKernelOperator_apply_basis hON]
  unfold weightedKernelOperator
  simp [orthonormal_iff_ite.mp hON, mul_ite, ite_smul]

/-! ## §B.2 — Static versus dynamical regularization -/

/-- A regulator is static for a Hamiltonian when its Heisenberg commutator with the
Hamiltonian vanishes. In the paper this is the non-covariant Sobolev case; the
gauge-covariant metric is dynamical because its covariant Laplacian depends on `A`. -/
def RegulatorStatic {R : Type*} [Ring R] (H K : R) : Prop :=
  H * K - K * H = 0

/-- A nonzero Hamiltonian commutator is precisely a failure of static
regularization. This isolates the paper's Section 6 criterion without introducing
a new evolution operator. -/
lemma not_regulatorStatic_of_commutator_ne_zero {R : Type*} [Ring R] {H K : R}
    (h : H * K - K * H ≠ 0) : ¬ RegulatorStatic H K := by
  intro hstat
  exact h hstat

/-- If the regulator commutes with the Hamiltonian, it is static in the
Heisenberg-generator sense. -/
lemma regulatorStatic_of_commute {R : Type*} [Ring R] {H K : R} (h : H * K = K * H) :
    RegulatorStatic H K := by
  unfold RegulatorStatic
  rw [h, sub_self]

/-! ## §C — the `L²(ℱ)`/BRST gauge measure -/

/-- **The gauge-invariant integral factorizes through the slice** (papers §2.1, the
`L²(ℱ)` construction): if the configuration-space measure factorizes through the
gauge-slice equivalence `e : 𝒜 ≃ ℱ × 𝒢` into a product measure, then for any
integrable observable constant along the gauge orbits,

`∫_𝒜 f dμ = vol(𝒢) · ∫_ℱ f dμ_ℱ` —

the gauge volume factors out and the observable descends to the slice: the
measure-theoretic content of `L²(𝒜) = L²(ℱ × 𝒢)` and of the Faddeev–Popov/BRST
division by the gauge group. -/
theorem gauge_integral_factorizes
    {X F G : Type*} [MeasurableSpace X] [MeasurableSpace F] [MeasurableSpace G]
    {μ : Measure X} {μF : Measure F} {μG : Measure G}
    [SigmaFinite μF] [SigmaFinite μG]
    (e : X ≃ᵐ F × G) (hμ : MeasurePreserving e μ (μF.prod μG))
    (f : X → ℝ) (hint : Integrable f μ) (g₀ : G)
    (hconst : ∀ p g, f (e.symm (p, g)) = f (e.symm (p, g₀))) :
    ∫ x, f x ∂μ = (μG Set.univ).toReal • ∫ p, f (e.symm (p, g₀)) ∂μF := by
  have hge : (fun q => f (e.symm q)) ∘ ⇑e = f := by
    funext x
    rw [Function.comp_apply, e.symm_apply_apply]
  have hcomp : ∫ x, f x ∂μ = ∫ q, f (e.symm q) ∂(μF.prod μG) := by
    rw [← hμ.integral_comp e.measurableEmbedding (fun q => f (e.symm q))]
    congr 1
    exact hge.symm
  have hint2 : Integrable (fun q => f (e.symm q)) (μF.prod μG) :=
    (hμ.integrable_comp_emb e.measurableEmbedding).mp (by rwa [hge])
  rw [hcomp, MeasureTheory.integral_prod _ hint2]
  have hinner : ∀ p : F, (∫ g, f (e.symm (p, g)) ∂μG)
      = (μG Set.univ).toReal • f (e.symm (p, g₀)) := by
    intro p
    rw [show (fun g => f (e.symm (p, g))) = fun _ => f (e.symm (p, g₀)) from
      funext fun g => hconst p g]
    exact integral_const _
  simp_rw [hinner]
  exact integral_smul _ _

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRegularization

end
