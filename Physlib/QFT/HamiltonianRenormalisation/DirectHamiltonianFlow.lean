/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.FreeScalarCovarianceFlow
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The direct Hamiltonian flow and the comparison of the flows
(Hamiltonian renormalisation II, §3.2–3.3)

Sections 3.2 and 3.3 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation II*
(arXiv:1711.06727v2).  The direct flow works with the single sharp-time field species: the flow
of Hilbert-space measures (Eqs. 3.108–3.109) is the pullback of the Gaussian generating
functionals along the coarse-graining injections, and the flow of the frequency covariances is
`(ω^{(n+1)}_M)⁻¹ = I† (ω^{(n)}_{2M})⁻¹ I` — the same block-spin recursion as §3.1, restricted to
smearing functions with sharp time dependence.  Proved here:

* `gaussianWeyl`, `gaussianWeyl_flow` — **Eqs. 3.106/3.109/3.114**: the Gaussian generating
  functional `f ↦ e^{−¼⟨f, C f⟩}` pulls back along an embedding `I` to the Gaussian generating
  functional with covariance `I† C I`: the flow of measures stays within the Gaussian family and
  is entirely a flow of covariances.
* `covariance_fixedPoint_automatic` — the remark under **Eqs. 3.22/3.31**: the cylindrical
  projections `C_M := I_M† C I_M` of a single continuum covariance are *automatically* a fixed
  point of the flow, because the injections compose, `I_{2M} ∘ I_{M→2M} = I_M`.
* `couplingFunction_tendsto_one`, `couplingFunction_tendsto_zero` — **Eq. 3.75 and §3.3**: at the
  fixed point of the path-integral flow the coupling functions are
  `ĝ_N(t) = 2(1−cos t)/(t+2πN)²`; in the continuum limit `t = 2πl/M → 0` the principal mode
  survives, `ĝ₀ → 1`, while every image mode dies, `ĝ_N → 0` for `N ≠ 0` — the quantitative form
  of §3.3's comparison: the field species that the path-integral flow inflates all freeze in the
  continuum limit, where the single-species description of the direct flow is recovered.

**Comparison of the flows (§3.3).**  The two flows differ at every finite resolution: the
path-integral flow doubles the field species at each step (`poleDoubling_first_step`,
Eq. 3.71) because the OS construction forces equivariance of the contraction semigroups with the
embeddings, while the direct flow stays with one species and drives the same hyperbolic
fixed-point recursion (`fixedPoint_a/b/c`, Eq. 3.58).  At the fixed point the direct-flow
Hamiltonian is the continuum Hamiltonian sandwiched between the embeddings (Eq. 3.118), and the
cylindrical projections of the continuum measure agree with the finite-resolution path-integral
measures (`continuum_projection_match`, Eq. 3.69).

**Honest layering.**  Exact inner-product/adjoint algebra and real limits.  The Fock-space
matrix-element induction (Eqs. 3.112–3.117), the fixed-point Hamiltonian sandwich (Eqs.
3.118–3.120) and the operator square roots of Eqs. 3.98–3.100 need a bosonic second-quantisation
layer (annihilators on a Fock measure space) that the repository does not yet provide — the
two-dimensional symplectic `WeylCCRSpacetime` and the fermionic CAR modules do not fit — and are
recorded, not re-derived.  The `k₀`-integral identity `1/(2ω) = ∫ dk₀/2π (k₀²+ω²)⁻¹` of Eq. 3.110
is likewise recorded as the sharp-time restriction that ties §3.2 to §3.1.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II: renormalisation flow of
  1+1 dimensional free scalar fields*, arXiv:1711.06727v2, §§3.2–3.3 (Eqs. 3.108–3.121).
-/

set_option autoImplicit false

open Real Filter ContinuousLinearMap
open scoped RealInnerProductSpace Topology

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-! ## §A — the Gaussian measure flow (Eqs. 3.106, 3.108–3.109, 3.114) -/

section GaussianFlow

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- **The Gaussian generating functional** (Eqs. 3.106/3.114): the expectation of the Weyl
element `e^{iφ[f]}` in the Gaussian measure with covariance operator `C` is `e^{−¼⟨f, C f⟩}`. -/
noncomputable def gaussianWeyl (C : E →L[ℝ] E) (f : E) : ℝ :=
  Real.exp (-(1/4) * ⟪f, C f⟫)

/-- **The measure flow stays Gaussian** (Eqs. 3.108–3.109): pulling the Gaussian generating
functional back along an embedding `I` — the direct-flow definition
`ν^{(n+1)}(e^{iφ[f]}) := ν^{(n)}(e^{iφ[I·f]})` — gives the Gaussian generating functional with
the flowed covariance `I† C I`.  The flow of measures is entirely a flow of covariances. -/
theorem gaussianWeyl_flow (C : E →L[ℝ] E) (I : F →L[ℝ] E) (f : F) :
    gaussianWeyl C (I f) = gaussianWeyl (adjoint I ∘L (C ∘L I)) f := by
  unfold gaussianWeyl
  rw [comp_apply, comp_apply, adjoint_inner_right]

/-- **Cylindrical projections are automatically a fixed point** (the remark under
Eqs. 3.22/3.31): if the injections compose, `I_{2M} ∘ I_{M→2M} = I_M`, then the family of
cylindrical projections `C_M := I_M† C I_M` of a single continuum covariance `C` satisfies the
flow equation `C_M = I_{M→2M}† C_{2M} I_{M→2M}` identically. -/
theorem covariance_fixedPoint_automatic (C : E →L[ℝ] E)
    (I₂ : F →L[ℝ] E) (I₁₂ : G →L[ℝ] F) (I₁ : G →L[ℝ] E)
    (hco : I₂ ∘L I₁₂ = I₁) :
    adjoint I₁ ∘L (C ∘L I₁)
      = adjoint I₁₂ ∘L ((adjoint I₂ ∘L (C ∘L I₂)) ∘L I₁₂) := by
    rw [← hco, adjoint_comp]
    ext g
    simp only [comp_apply]

end GaussianFlow

/-! ## §B — the continuum limit freezes the field species (Eq. 3.75, §3.3) -/

/-- `sin t / t → 1` as `t → 0`, from the derivative of `sin` at `0`. -/
private lemma tendsto_sin_div :
    Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
  have h := Real.hasDerivAt_sin 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cos_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [slope_def_field, Real.sin_zero]

/-- **The principal coupling function survives** (Eq. 3.75 at `N = 0`, §3.3): in the continuum
limit `t = k_M l → 0` the fixed-point coupling `ĝ₀(t) = 2(1−cos t)/t²` tends to `1` — the single
sharp-time field species of the continuum description. -/
theorem couplingFunction_tendsto_one :
    Tendsto (fun t : ℝ => 2*(1 - Real.cos t)/t^2) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
  have hhalf : Tendsto (fun t : ℝ => t/2) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun t : ℝ => t/2) (𝓝 (0:ℝ)) (𝓝 (0/2)) :=
        (continuous_id.div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero ht two_ne_zero
  have hsq : Tendsto (fun t : ℝ => (Real.sin (t/2) / (t/2))^2) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have := (tendsto_sin_div.comp hhalf).pow 2
    simpa using this
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t:ℝ) ≠ 0 := ht
  have h2t : Real.cos t = 1 - 2*Real.sin (t/2)^2 := by
    have hc := Real.cos_two_mul (t/2)
    have hs := Real.sin_sq_add_cos_sq (t/2)
    rw [show 2*(t/2) = t by ring] at hc
    linarith
  rw [h2t, div_pow, show ((t:ℝ)/2)^2 = t^2/4 by ring]
  field_simp
  ring

/-- **Every image coupling function freezes** (Eq. 3.75 at `N ≠ 0`, §3.3): in the continuum
limit the fixed-point couplings of the image modes vanish, `ĝ_N(t) = 2(1−cos t)/(t+2πN)² → 0`
for `N ≠ 0` — the field species inflated by the path-integral flow all decouple, and the theory
is again described by a single dispersion relation. -/
theorem couplingFunction_tendsto_zero (N : ℤ) (hN : N ≠ 0) :
    Tendsto (fun t : ℝ => 2*(1 - Real.cos t)/(t + 2*Real.pi*N)^2) (𝓝 (0:ℝ)) (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ => 2*(1 - Real.cos t)) (𝓝 (0:ℝ)) (𝓝 0) := by
    have : Continuous fun t : ℝ => 2*(1 - Real.cos t) := by continuity
    simpa using this.tendsto 0
  have hden : Tendsto (fun t : ℝ => (t + 2*Real.pi*N)^2) (𝓝 (0:ℝ)) (𝓝 ((2*Real.pi*N)^2)) := by
    have : Continuous fun t : ℝ => (t + 2*Real.pi*N)^2 := by continuity
    simpa using this.tendsto 0
  have hden_ne : ((2*Real.pi*N)^2 : ℝ) ≠ 0 := by
    apply pow_ne_zero
    have hπ : (2*Real.pi : ℝ) ≠ 0 := by positivity
    exact mul_ne_zero hπ (Int.cast_ne_zero.mpr hN)
  have hdiv := hnum.div hden hden_ne
  rw [zero_div] at hdiv
  exact Filter.Tendsto.congr (fun _ => rfl) hdiv

end Physlib.QFT.HamiltonianRenormalisation

end
