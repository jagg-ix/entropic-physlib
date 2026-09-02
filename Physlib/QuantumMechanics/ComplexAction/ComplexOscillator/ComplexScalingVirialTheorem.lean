/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The complex virial theorem: resonances are stationary in the scaling angle

In the complex-scaling method (Aguilar–Balslev–Combes–Simon; Cerioni et al. 2013) a resonance is exposed by
the similarity transformation `H_θ = S_θ H S_θ⁻¹` with `S_θ = e^{θ W}` (`r ↦ r e^{iθ}`, `W` the dilation
generator). The defining property of the method — the **complex virial theorem** — is that a true resonance
eigenvalue is **stationary in the unphysical scaling angle**: `dE_n/dθ = 0`. This file formalizes its two
exact algebraic cores.

* **§A — eigenvalues are similarity invariants.** `eigenvalue_scaled_invariant`: if `H v = E v`, then the
  scaled operator `S H S⁻¹` has eigenvector `S v` with the **same** eigenvalue `E` (`S` any invertible
  endomorphism). `scaledHamiltonian_eigenvalue_indep`: hence for *every* angle `θ` the scaled Hamiltonian
  `H_θ` carries the same eigenvalue `E` — the eigenvalue is θ-independent. This is the global form of
  `dE_n/dθ = 0`.

* **§B — the complex virial theorem (Hellmann–Feynman form).** With the bilinear `c`-product `B` (a
  *symmetric bilinear* form, not a Hermitian inner product — under which the complex-scaled Hamiltonian is
  `B`-symmetric, `B (H x) y = B x (H y)`), the eigenvalue derivative `dE/dθ ∝ B v (⁅W,H⁆ v)` and
  `complexVirial` proves the commutator expectation vanishes in an eigenstate: `B v ((W H − H W) v) = 0`.
  Since `dH_θ/dθ = ⁅W, H_θ⁆`, this is `dE/dθ = 0` (`scalingEigenvalueDerivative_eq_zero`).

* **§C — the scaling angle cannot enter physical data.** `not_eigenvalue_of_scalingAngle_dependent`: any
  quantity `P(θ)` that genuinely varies with `θ` (`P θ₁ ≠ P θ₂`) is **not** a complex-scaling eigenvalue
  (which is θ-independent). This makes precise why identifying the complex-scaling angle with a *physical*
  parameter (e.g. a spacetime noncommutativity `θ^{μν}`, as in the "noncommutative Regge" extension) is
  illegitimate: the spectrum is, by construction, stationary in `θ`.

## References

* J. Aguilar, J. M. Combes, *Comm. Math. Phys.* **22** (1971); E. Balslev, J. M. Combes (1971); B. Simon.
  A. Cerioni et al., *Accurate complex scaling of three-dimensional numerical potentials* (2013). The
  complex virial theorem `dE/dθ = 0` for resonance eigenvalues.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexScalingVirialTheorem

variable {M : Type*} [AddCommGroup M] [Module ℂ M]


/-- **[Eigenvalues survive complex scaling]** if `H v = E v` then the scaled operator `S H S⁻¹` has
eigenvector `S v` with the *same* eigenvalue `E` (`S` any invertible endomorphism). Complex scaling is a
similarity transformation, so it cannot move a resonance eigenvalue. -/
lemma eigenvalue_scaled_invariant (S : (Module.End ℂ M)ˣ) (H : Module.End ℂ M) {v : M} {E : ℂ}
    (hEig : H v = E • v) :
    ((S : Module.End ℂ M) * H * (↑S⁻¹ : Module.End ℂ M)) ((S : Module.End ℂ M) v)
      = E • ((S : Module.End ℂ M) v) := by
  have hSinv : (↑S⁻¹ : Module.End ℂ M) ((S : Module.End ℂ M) v) = v := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply, hSinv, hEig, map_smul]

/-- **[The scaled eigenvalue is independent of the angle `θ`]** for any family of scaling units `S_θ`, every
scaled Hamiltonian `H_θ = S_θ H S_θ⁻¹` carries the same eigenvalue `E` (with eigenvector `S_θ v`). This is
the global statement `dE_n/dθ = 0` — the complex-scaling spectrum does not depend on the unphysical angle. -/
lemma scaledHamiltonian_eigenvalue_indep (Sθ : ℝ → (Module.End ℂ M)ˣ) (H : Module.End ℂ M)
    {v : M} {E : ℂ} (hEig : H v = E • v) (θ : ℝ) :
    ((Sθ θ : Module.End ℂ M) * H * (↑(Sθ θ)⁻¹ : Module.End ℂ M)) ((Sθ θ : Module.End ℂ M) v)
      = E • ((Sθ θ : Module.End ℂ M) v) :=
  eigenvalue_scaled_invariant (Sθ θ) H hEig


/-- **[The complex virial theorem]** for the bilinear `c`-product `B` under which `H` is symmetric
(`B (H x) y = B x (H y)` — the complex-scaled Hamiltonian is complex-symmetric, not Hermitian), the
commutator expectation vanishes in an eigenstate: `B v (⁅W, H⁆ v) = 0`. Since `dH_θ/dθ = ⁅W, H_θ⁆`, the
Hellmann–Feynman eigenvalue derivative `dE/dθ ∝ B v (⁅W,H⁆ v)` is zero — the resonance is stationary in the
scaling angle. -/
lemma complexVirial (B : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (H W : Module.End ℂ M) {v : M} {E : ℂ}
    (hSym : ∀ x y, B (H x) y = B x (H y)) (hEig : H v = E • v) :
    B v ((W * H - H * W) v) = 0 := by
  have e1 : B v (W (H v)) = E • B v (W v) := by
    rw [hEig, map_smul, map_smul]
  have e2 : B v (H (W v)) = E • B v (W v) := by
    rw [← hSym v (W v), hEig, LinearMap.map_smul₂]
  have hcomm : (W * H - H * W) v = W (H v) - H (W v) := by
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [hcomm, map_sub, e1, e2, sub_self]

/-- **The Hellmann–Feynman eigenvalue derivative** `dE/dθ = B v (⁅W,H⁆ v) / B v v` of a resonance under the
scaling generated by `W`. -/
noncomputable def scalingEigenvalueDerivative (B : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (H W : Module.End ℂ M) (v : M) : ℂ :=
  B v ((W * H - H * W) v) / B v v

/-- **[`dE/dθ = 0`]** the complex virial theorem: the resonance eigenvalue derivative in the scaling angle
vanishes. -/
lemma scalingEigenvalueDerivative_eq_zero (B : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (H W : Module.End ℂ M)
    {v : M} {E : ℂ} (hSym : ∀ x y, B (H x) y = B x (H y)) (hEig : H v = E • v) :
    scalingEigenvalueDerivative B H W v = 0 := by
  rw [scalingEigenvalueDerivative, complexVirial B H W hSym hEig, zero_div]


/-- A quantity equal to a fixed (θ-independent) complex-scaling eigenvalue is constant in `θ`. -/
lemma const_of_eq_eigenvalue {P : ℝ → ℂ} {E : ℂ} (h : ∀ θ, P θ = E) (θ₁ θ₂ : ℝ) :
    P θ₁ = P θ₂ := by rw [h θ₁, h θ₂]

/-- **[A scaling-angle-dependent quantity is not an eigenvalue]** if `P` genuinely varies with the scaling
angle (`P θ₁ ≠ P θ₂`) then it is not a complex-scaling eigenvalue — there is no `E` with `P θ = E` for all
`θ`. Identifying the (unphysical, spectrum-stationary) scaling angle with a physical parameter on which
observables depend therefore contradicts the complex virial theorem. -/
lemma not_eigenvalue_of_scalingAngle_dependent {P : ℝ → ℂ} {θ₁ θ₂ : ℝ} (hdep : P θ₁ ≠ P θ₂) :
    ¬ ∃ E : ℂ, ∀ θ, P θ = E := by
  rintro ⟨E, h⟩
  exact hdep (const_of_eq_eigenvalue h θ₁ θ₂)


/-! ### The Feynman–Hellmann theorem, analytically

The `scalingEigenvalueDerivative` above is the Hellmann–Feynman *form* — the c-product formula for
`dE/dθ` taken as a definition. Here is the *theorem* itself, on a real inner-product space: for a
differentiable family of self-adjoint operators with a differentiable normalized eigenbranch, the
eigenvalue derivative is the expectation of the operator derivative, `ω′ = ⟪ψ, H′ψ⟫` — the
eigenvector derivative drops out. This is the engine behind lattice magnetizations
(Hamer–Kogut Eq. 3.12, `M = (1/N)·∂ω₀/∂h`: differentiate the ground energy in the source, no
wave-function response needed) and of the §B virial identity. -/

/-- **The Feynman–Hellmann theorem** `dω/dt = ⟪ψ, (dH/dt)ψ⟫`: along a differentiable normalized
eigenbranch `H(t)ψ(t) = ω(t)ψ(t)` of a family of self-adjoint operators, the eigenvalue derivative
is the expectation value of the operator derivative — the `⟪ψ′, …⟫` response terms cancel against
each other through the eigenvalue equation and symmetry, with no need for `⟪ψ, ψ′⟫ = 0`. -/
theorem feynman_hellmann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℝ → E →L[ℝ] E) (H' : E →L[ℝ] E) (ψ : ℝ → E) (ψ' : E) (ω : ℝ → ℝ) (ω' : ℝ)
    (t : ℝ)
    (hH : HasDerivAt H H' t) (hψ : HasDerivAt ψ ψ' t) (hω : HasDerivAt ω ω' t)
    (heig : ∀ s, H s (ψ s) = ω s • ψ s)
    (hnorm : inner ℝ (ψ t) (ψ t) = (1 : ℝ))
    (hsym : ∀ x y, inner ℝ (H t x) y = inner ℝ x (H t y)) :
    ω' = inner ℝ (ψ t) (H' (ψ t)) := by
  have h1 : HasDerivAt (fun s => H s (ψ s)) (H' (ψ t) + H t ψ') t := hH.clm_apply hψ
  have h2 : HasDerivAt (fun s => H s (ψ s)) (ω t • ψ' + ω' • ψ t) t := by
    have hs := hω.smul hψ
    have hfun : (fun s => H s (ψ s)) = fun s => ω s • ψ s := funext heig
    rw [hfun]
    exact hs
  have huniq : H' (ψ t) + H t ψ' = ω t • ψ' + ω' • ψ t := h1.unique h2
  have hin := congrArg (fun z => inner ℝ (ψ t) z) huniq
  simp only [inner_add_right, real_inner_smul_right] at hin
  have hsymterm : inner ℝ (ψ t) ((H t) ψ') = ω t * inner ℝ (ψ t) ψ' := by
    rw [← hsym (ψ t) ψ', heig t, real_inner_smul_left]
  rw [hnorm, hsymterm] at hin
  linarith


/-! ### The non-Hermitian Hellmann–Feynman theorem (Hajong–Modak–Mandal, arXiv:2308.13914)

For `Ĥ† ≠ Ĥ` the theorem survives with the *biorthogonal* pairing: right eigenvectors
`Ĥ|R⟩ = E|R⟩`, left eigenvectors `⟨L|Ĥ = E⟨L|`, normalization `⟨L|R⟩ = 1`, and then
`∂E/∂λ = ⟨L|∂Ĥ/∂λ|R⟩` (their Eqs. 8/11–12) — the derivation needs **no** Hermiticity, no PT
symmetry, and no G-operator: the `⟨L′|…⟩` and `⟨…|R′⟩` response terms combine into
`E·∂⟨L|R⟩ = 0`. Below on the concrete matrix carrier (the paper's own §III setting): the
theorem, the PT two-level model `H = [[iλ,−1],[−1,−iλ]]` with its spectrum `E² = 1−λ²`, the PT
transition at `λ_c = 1`, and the divergence of `∂E/∂λ` at the exceptional point — the paper's
central observation that the HFT blows up exactly where eigenvalues turn complex. -/

/-- **The non-Hermitian Hellmann–Feynman theorem** `∂E/∂λ = ⟨L|∂Ĥ/∂λ|R⟩`: for a differentiable
family of (arbitrary, not necessarily Hermitian or PT-symmetric) matrices with differentiable
biorthogonally-normalized left/right eigenbranches, the eigenvalue derivative is the left–right
expectation of the matrix derivative — the response terms cancel through
`E·∂⟨L|R⟩ = 0` (Eqs. 8/11–12 of Hajong–Modak–Mandal). -/
theorem nonHermitian_feynman_hellmann {n : ℕ}
    (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n) (Fin n) ℂ)
    (L R : ℝ → Fin n → ℂ) (L' R' : Fin n → ℂ) (E : ℝ → ℂ) (E' : ℂ) (t : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t)
    (hL : ∀ i, HasDerivAt (fun s => L s i) (L' i) t)
    (hR : ∀ i, HasDerivAt (fun s => R s i) (R' i) t)
    (hE : HasDerivAt E E' t)
    (heig : ∀ s, (H s).mulVec (R s) = E s • R s)
    (hleft : ∀ s, Matrix.vecMul (L s) (H s) = E s • L s)
    (hnorm : ∀ s, dotProduct (L s) (R s) = 1) :
    E' = dotProduct (L t) (H'.mulVec (R t)) := by
  have hNder : HasDerivAt (fun s => dotProduct (L s) (R s))
      (dotProduct L' (R t) + dotProduct (L t) R') t := by
    have h1 := HasDerivAt.sum (u := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => (hL i).mul (hR i))
    have hfun : (∑ i, ((fun s => L s i) * fun s => R s i) : ℝ → ℂ)
        = fun s => ∑ i, L s i * R s i := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at h1
    simpa [dotProduct, Finset.sum_add_distrib] using h1
  have hNconst : HasDerivAt (fun s => dotProduct (L s) (R s)) 0 t := by
    have hfun : (fun s => dotProduct (L s) (R s)) = fun _ => 1 := funext hnorm
    rw [hfun]
    exact hasDerivAt_const t 1
  have hzero : dotProduct L' (R t) + dotProduct (L t) R' = 0 := hNder.unique hNconst
  have hg : ∀ i, HasDerivAt (fun s => (H s).mulVec (R s) i)
      (H'.mulVec (R t) i + (H t).mulVec R' i) t := by
    intro i
    have h1 := HasDerivAt.sum (u := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => (hH i j).mul (hR j))
    have hfun : (∑ j, ((fun s => H s i j) * fun s => R s j) : ℝ → ℂ)
        = fun s => ∑ j, H s i j * R s j := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at h1
    simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using h1
  have hFder : HasDerivAt (fun s => dotProduct (L s) ((H s).mulVec (R s)))
      (dotProduct L' ((H t).mulVec (R t)) + (dotProduct (L t) (H'.mulVec (R t))
        + dotProduct (L t) ((H t).mulVec R'))) t := by
    have h2 := HasDerivAt.sum (u := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => (hL i).mul (hg i))
    have hfun : (∑ i, ((fun s => L s i) * fun s => (H s).mulVec (R s) i) : ℝ → ℂ)
        = fun s => ∑ i, L s i * (H s).mulVec (R s) i := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun] at h2
    simpa [dotProduct, mul_add, Finset.sum_add_distrib] using h2
  have hFE : (fun s => dotProduct (L s) ((H s).mulVec (R s))) = E := by
    funext s
    rw [heig s, dotProduct_smul, hnorm s, smul_eq_mul, mul_one]
  have huniq : dotProduct L' ((H t).mulVec (R t)) + (dotProduct (L t) (H'.mulVec (R t))
      + dotProduct (L t) ((H t).mulVec R')) = E' := by
    have hF := hFder
    rw [hFE] at hF
    exact hF.unique hE
  have e1 : dotProduct L' ((H t).mulVec (R t)) = E t * dotProduct L' (R t) := by
    rw [heig t, dotProduct_smul, smul_eq_mul]
  have e2 : dotProduct (L t) ((H t).mulVec R') = E t * dotProduct (L t) R' := by
    rw [Matrix.dotProduct_mulVec, hleft t, smul_dotProduct, smul_eq_mul]
  rw [e1, e2] at huniq
  linear_combination (-1 : ℂ) * huniq + E t * hzero

/-- **The PT-symmetric two-level model** `H = [[iλ, −1], [−1, −iλ]]` of the paper's §III. -/
noncomputable def ptTwoLevel (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * lam, -1; -1, -Complex.I * lam]

/-- **[Traceless]** the two levels are symmetric about zero. -/
theorem ptTwoLevel_trace (lam : ℝ) : Matrix.trace (ptTwoLevel lam) = 0 := by
  simp [ptTwoLevel, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **[The determinant]** `det H = λ² − 1`, so the spectrum is `E² = 1 − λ²`: real for `λ ≤ 1`
(PT unbroken), imaginary for `λ > 1` (broken) — the exceptional point sits at `λ_c = 1`. -/
theorem ptTwoLevel_det (lam : ℝ) : Matrix.det (ptTwoLevel lam) = (lam : ℂ) ^ 2 - 1 := by
  rw [Matrix.det_fin_two]
  simp [ptTwoLevel]
  linear_combination (-(lam : ℂ) ^ 2) * Complex.I_sq

/-- **[The PT transition]** the eigenvalue equation `E² = 1 − λ²` has a real solution exactly for
`λ² ≤ 1` — the unbroken phase is the closed unit interval of the Hermiticity-breaking
parameter, with the exceptional point at its boundary. -/
theorem pt_transition_iff (lam : ℝ) :
    (∃ E : ℝ, E ^ 2 = 1 - lam ^ 2) ↔ lam ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨E, hE⟩
    nlinarith [sq_nonneg E]
  · intro h
    exact ⟨Real.sqrt (1 - lam ^ 2), Real.sq_sqrt (by linarith)⟩

/-- **[The Hellmann–Feynman derivative diverges at the exceptional point]** the paper's Eq. 14
value `|∂E₊/∂λ| = λ/√(1−λ²)` tends to `+∞` as `λ → 1⁻`: both sides of the modified HFT blow up
exactly where the eigenvalues turn from real to complex — the divergence diagnoses the EP. -/
theorem ep_divergence :
    Filter.Tendsto (fun lam : ℝ => lam / Real.sqrt (1 - lam ^ 2))
      (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
  have hsq : Filter.Tendsto (fun lam : ℝ => Real.sqrt (1 - lam ^ 2))
      (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Filter.Tendsto (fun lam : ℝ => Real.sqrt (1 - lam ^ 2)) (nhds 1) (nhds 0) := by
        have h0 : Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 := by norm_num
        have := (Real.continuous_sqrt.comp (by fun_prop :
          Continuous fun lam : ℝ => 1 - lam ^ 2)).tendsto 1
        simpa [Function.comp_def, h0] using this
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)),
        eventually_mem_nhdsWithin] with lam h1 h2
      have hlt : lam < 1 := h2
      have hpos : 0 < 1 - lam ^ 2 := by nlinarith
      exact Real.sqrt_pos.mpr hpos
  have hinv : Filter.Tendsto (fun lam : ℝ => (Real.sqrt (1 - lam ^ 2))⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
    simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hsq
  have hnum : Filter.Tendsto (fun lam : ℝ => lam) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    (continuous_id.tendsto 1).mono_left nhdsWithin_le_nhds
  have hmul := hnum.pos_mul_atTop one_pos hinv
  simpa [div_eq_mul_inv] using hmul


/-! ### The continuum model (§IV, Eqs. 19–22)

The 2d oscillator with non-Hermitian coupling `iλxy` is solved by the *complex rotation* of
Eq. 21, `X = √((k+1)/2)·x − i√((k−1)/2)·y`, `Y = i√((k−1)/2)·x + √((k+1)/2)·y` — a rotation by
an imaginary angle, i.e. a Wick-rotated boost (`(k±1)/2 = cosh²/sinh²` of the half-rapidity; the
repo's `LeviCivita.BoostRotationWickContour` is the same contour mechanism). Its exact structure:
the quadratic form is *preserved*, `X² + Y² = x² + y²` (`complex_rotation_preserves_form` — the
rotation is complex-orthogonal, which is why the kinetic term survives untouched), while the
difference picks up exactly the cross term, `X² − Y² = k(x² − y²) − 2i√(k²−1)·xy`
(`complex_rotation_cross_term`) — the `iλxy` coupling is *generated* by the boost, and choosing
`k` with `1/k = √(1 − λ²/λ_c²)` diagonalizes it. The 2d exceptional point is the same transition
as the two-level model, rescaled: real `1/k` exists iff `λ² ≤ λ_c²`
(`continuum_pt_transition`, *reusing* `pt_transition_iff`). And the paper's observation that the
`n₁ = n₂` levels stay real through the broken phase is the conjugate-pair mechanism
`C₂ = C̄₁ ⟹ (n+½)(C₁+C₂) ∈ ℝ` (`equal_quanta_real`). -/

/-- **[The Eq. 21 rotation is complex-orthogonal]** `X² + Y² = x² + y²`: the imaginary-angle
rotation preserves the Euclidean quadratic form exactly — the kinetic and radial terms of the
2d oscillator pass through the transformation unchanged. -/
theorem complex_rotation_preserves_form (k x y : ℝ) (hk : 1 ≤ k) :
    ((Real.sqrt ((k + 1) / 2) : ℂ) * x - Complex.I * Real.sqrt ((k - 1) / 2) * y) ^ 2
      + (Complex.I * Real.sqrt ((k - 1) / 2) * x + (Real.sqrt ((k + 1) / 2) : ℂ) * y) ^ 2
      = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
  have ha : ((Real.sqrt ((k + 1) / 2) : ℝ) : ℂ) ^ 2 = ((k : ℂ) + 1) / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by linarith)]
  have hb : ((Real.sqrt ((k - 1) / 2) : ℝ) : ℂ) ^ 2 = ((k : ℂ) - 1) / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by linarith)]
  linear_combination ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * ha
    + Complex.I ^ 2 * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * hb
    + ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * (((k : ℂ) - 1) / 2) * Complex.I_sq

/-- **[The rotation generates the `iλxy` coupling]**
`X² − Y² = k(x² − y²) − 2i√(k²−1)·xy`: the anisotropy is boosted by `k` and an *imaginary* cross
term appears — precisely the non-Hermitian `iλxy` interaction of Eq. 19, which the choice
`1/k = √(1−λ²/λ_c²)` then absorbs. -/
theorem complex_rotation_cross_term (k x y : ℝ) (hk : 1 ≤ k) :
    ((Real.sqrt ((k + 1) / 2) : ℂ) * x - Complex.I * Real.sqrt ((k - 1) / 2) * y) ^ 2
      - (Complex.I * Real.sqrt ((k - 1) / 2) * x + (Real.sqrt ((k + 1) / 2) : ℂ) * y) ^ 2
      = (k : ℂ) * ((x : ℂ) ^ 2 - (y : ℂ) ^ 2)
        - 2 * Complex.I * Real.sqrt (k ^ 2 - 1) * x * y := by
  have ha : ((Real.sqrt ((k + 1) / 2) : ℝ) : ℂ) ^ 2 = ((k : ℂ) + 1) / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by linarith)]
  have hb : ((Real.sqrt ((k - 1) / 2) : ℝ) : ℂ) ^ 2 = ((k : ℂ) - 1) / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by linarith)]
  have hab : ((Real.sqrt ((k + 1) / 2) : ℝ) : ℂ) * ((Real.sqrt ((k - 1) / 2) : ℝ) : ℂ)
      = (Real.sqrt (k ^ 2 - 1) : ℂ) / 2 := by
    norm_cast
    rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ (k + 1) / 2),
      show (k + 1) / 2 * ((k - 1) / 2) = (k ^ 2 - 1) / 4 by ring,
      show (k ^ 2 - 1 : ℝ) / 4 = (k ^ 2 - 1) * (1 / 4) by ring,
      Real.sqrt_mul (by nlinarith : (0 : ℝ) ≤ k ^ 2 - 1),
      show Real.sqrt (1 / 4) = 1 / 2 by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  linear_combination ((x : ℂ) ^ 2 - (y : ℂ) ^ 2) * ha
    - Complex.I ^ 2 * ((x : ℂ) ^ 2 - (y : ℂ) ^ 2) * hb
    - (4 : ℂ) * Complex.I * x * y * hab
    - ((x : ℂ) ^ 2 - (y : ℂ) ^ 2) * (((k : ℂ) - 1) / 2) * Complex.I_sq

/-- **[The continuum exceptional point]** a real `1/k = √(1−λ²/λ_c²)` exists iff `λ² ≤ λ_c²` —
the 2d model's PT transition at `λ_c = mω₋²/2` is the two-level transition rescaled
(*reusing* `pt_transition_iff` at `λ/λ_c`). -/
theorem continuum_pt_transition (lam lamc : ℝ) (h : lamc ≠ 0) :
    (∃ r : ℝ, r ^ 2 = 1 - lam ^ 2 / lamc ^ 2) ↔ lam ^ 2 ≤ lamc ^ 2 := by
  have h1 := pt_transition_iff (lam / lamc)
  rw [div_pow] at h1
  have hpos : (0 : ℝ) < lamc ^ 2 := by positivity
  constructor
  · intro hr
    have h2 := h1.mp hr
    rw [div_le_one hpos] at h2
    exact h2
  · intro hle
    exact h1.mpr (by rw [div_le_one hpos]; exact hle)

/-- **[Equal quanta stay real]** if the two mode frequencies are complex conjugates
(`C₂ = C̄₁`, the broken phase), the `n₁ = n₂ = n` levels
`E = (n+½)C₁ + (n+½)C₂ = (2n+1)·Re C₁` are real for *all* couplings — the paper's §IV
observation that eigenstates with equal quanta show no real-to-complex transition (and hence no
HFT divergence). -/
theorem equal_quanta_real (n : ℕ) (C : ℂ) :
    ((n : ℂ) + 1 / 2) * C + ((n : ℂ) + 1 / 2) * (starRingEnd ℂ) C
      = (((2 * n + 1 : ℝ) * C.re : ℝ) : ℂ) := by
  rw [← mul_add, Complex.add_conj]
  push_cast
  ring


/-! ### The generalized virial theorem (§V, Eqs. 23–25)

Eq. 25's mechanism: apply the (non-Hermitian) HFT to a *scaling family*. When the family is a
similarity orbit — `H(s) = S(s)·H·S(s)⁻¹`, the situation of `eigenvalue_scaled_invariant` and
`scaledHamiltonian_eigenvalue_indep` above — the eigenvalue is constant in `s`, so the HFT
forces the virial identity `⟨L|∂H/∂s|R⟩ = 0`: the analytic realization of the §B algebraic
`complexVirial`/`scalingEigenvalueDerivative_eq_zero`. For a trapped system the spectrum is
*not* scale-invariant and the residual is the `−½Σ l_q·∂E/∂l_q` of Eq. 25 — for the harmonic
trap that residual is exactly the half-energy relation `oscillator_virial_half_energy` on the
`BargmannFockCCR` ladder. -/

/-- **[The virial identity from scale invariance]** if the eigenvalue of a differentiable
biorthogonal eigenbranch is *constant* along the family (a similarity/scaling orbit), then
`⟨L|∂Ĥ/∂s|R⟩ = 0` — Eq. 25 with vanishing trap terms, derived by *reusing*
`nonHermitian_feynman_hellmann` at `E′ = 0`. -/
theorem virial_vanishing_from_scaling {n : ℕ}
    (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n) (Fin n) ℂ)
    (L R : ℝ → Fin n → ℂ) (L' R' : Fin n → ℂ) (E0 : ℂ) (t : ℝ)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t)
    (hL : ∀ i, HasDerivAt (fun s => L s i) (L' i) t)
    (hR : ∀ i, HasDerivAt (fun s => R s i) (R' i) t)
    (heig : ∀ s, (H s).mulVec (R s) = E0 • R s)
    (hleft : ∀ s, Matrix.vecMul (L s) (H s) = E0 • L s)
    (hnorm : ∀ s, dotProduct (L s) (R s) = 1) :
    dotProduct (L t) (H'.mulVec (R t)) = 0 := by
  have h := nonHermitian_feynman_hellmann H H' L R L' R' (fun _ => E0) 0 t hH hL hR
    (hasDerivAt_const t E0) heig hleft hnorm
  exact h.symm

/-- **[The harmonic trapping combination]** for `U = ½Ω²x²` the Eq. 27 combination
`U + ½x·U′` collapses to `Ω²x²` — so the trapping energy is `Ẽ_tr = ½⟨Ω²x²⟩_G` (Eq. 29), whose
ladder evaluation is `oscillator_virial_ladder` and whose value is
`oscillator_virial_half_energy`: `E = 2Ẽ_tr` for any complex frequency. -/
theorem harmonic_trapping_combination (Om x : ℝ) :
    HasDerivAt (fun t => 1 / 2 * Om ^ 2 * t ^ 2) (Om ^ 2 * x) x
      ∧ 1 / 2 * Om ^ 2 * x ^ 2 + 1 / 2 * x * (Om ^ 2 * x) = Om ^ 2 * x ^ 2 := by
  constructor
  · have hp := (hasDerivAt_pow 2 x).const_mul (1 / 2 * Om ^ 2)
    have hval : 1 / 2 * Om ^ 2 * (2 * x ^ (2 - 1)) = Om ^ 2 * x := by
      norm_num
      ring
    rw [← hval]
    simpa using hp
  · ring


open Matrix

/-! ### The metric operator `G` (Eqs. 2–5, 13)

The biorthogonal structure is organized by the Hermitian *metric operator* `G = Σᵢ|Lᵢ⟩⟨Lᵢ|`
(Eq. 3): it carries right eigenvectors to left ones, `G|Rⱼ⟩ = |Lⱼ⟩` (Eq. 2's `⟨Lᵢ| = ⟨Rᵢ|G`),
turns G-expectations into the biorthogonal pairing `⟨R|GO|R⟩ = ⟨L|O|R⟩` (Eq. 4) — the pairing
`nonHermitian_feynman_hellmann` runs on — and in the unbroken phase, where the Hamiltonian is a
*good observable* `Ĥ†G = GĤ` (Eq. 5), it forces the spectrum real. All four at exact matrix
level, plus the paper's concrete two-level metric `G^u ∝ [[1, iλ], [−iλ, 1]]` (Eq. 13). -/

/-- **The metric operator** `G = Σᵢ|Lᵢ⟩⟨Lᵢ|` built from the left eigenvectors (Eq. 3). -/
noncomputable def metricOperator {n : ℕ} (L : Fin n → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, Matrix.vecMulVec (L i) (star (L i))

/-- **[`G` is Hermitian]** `Gᴴ = G`. -/
theorem metricOperator_hermitian {n : ℕ} (L : Fin n → Fin n → ℂ) :
    (metricOperator L)ᴴ = metricOperator L := by
  unfold metricOperator
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

/-- **[`G` carries right eigenvectors to left ones]** `G|Rⱼ⟩ = |Lⱼ⟩` (Eq. 2 in ket form), from
biorthonormality alone. -/
theorem metricOperator_mulVec_right {n : ℕ} (L R : Fin n → Fin n → ℂ) (j : Fin n)
    (hbi : ∀ i k, dotProduct (star (L i)) (R k) = if i = k then 1 else 0) :
    (metricOperator L).mulVec (R j) = L j := by
  unfold metricOperator
  rw [Matrix.sum_mulVec]
  funext a
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Pi.star_apply]
  have hterm : ∀ i, (∑ b, L i a * star (L i b) * R j b)
      = L i a * (if i = j then 1 else 0) := by
    intro i
    rw [← hbi i j]
    simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  calc (∑ i, ∑ b, L i a * star (L i b) * R j b)
      = ∑ i, L i a * (if i = j then 1 else 0) := Finset.sum_congr rfl fun i _ => hterm i
    _ = L j a := by simp

/-- **[The star-pairing moves a matrix onto its adjoint]** `⟨u|Mw⟩ = ⟨Mᴴu|w⟩`. -/
theorem star_dot_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    dotProduct (star u) (M.mulVec w) = dotProduct (star (Mᴴ.mulVec u)) w := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **[The G-inner product is the biorthogonal pairing]** `⟨Rⱼ|GO|Rⱼ⟩ = ⟨Lⱼ|O|Rⱼ⟩` (Eq. 4):
G-expectations reduce to left–right matrix elements — the pairing on which
`nonHermitian_feynman_hellmann` runs. -/
theorem metric_inner_eq_biorthogonal {n : ℕ} (L R : Fin n → Fin n → ℂ)
    (O : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (hbi : ∀ i k, dotProduct (star (L i)) (R k) = if i = k then 1 else 0) :
    dotProduct (star (R j)) ((metricOperator L * O).mulVec (R j))
      = dotProduct (star (L j)) (O.mulVec (R j)) := by
  rw [← Matrix.mulVec_mulVec, star_dot_mulVec, metricOperator_hermitian,
    metricOperator_mulVec_right L R j hbi]

/-- **[Good observables have real eigenvalues]** `Ĥ†G = GĤ` (Eq. 5, the unbroken phase) with `G`
Hermitian carrying `|R⟩` to `|L⟩` and `⟨L|R⟩ = 1` forces `Ē = E` — the reality mechanism of the
PT-unbroken spectrum. -/
theorem good_observable_real_eigenvalue {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℂ) (R L : Fin n → ℂ) (E : ℂ)
    (hgood : Hᴴ * G = G * H)
    (hGR : G.mulVec R = L)
    (hnorm : dotProduct (star L) R = 1)
    (heig : H.mulVec R = E • R) :
    (starRingEnd ℂ) E = E := by
  have hconj : ∀ u w : Fin n → ℂ,
      (starRingEnd ℂ) (dotProduct (star u) w) = dotProduct (star w) u := by
    intro u w
    simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hE : dotProduct (star L) (H.mulVec R) = E := by
    rw [heig, dotProduct_smul, smul_eq_mul, hnorm, mul_one]
  have h1 : (starRingEnd ℂ) E = dotProduct (star (H.mulVec R)) L := by
    rw [← hE, hconj]
  have h2 : Hᴴ.mulVec L = E • L := by
    rw [← hGR, Matrix.mulVec_mulVec, hgood, ← Matrix.mulVec_mulVec, heig,
      Matrix.mulVec_smul, hGR]
  have h3 : dotProduct (star (H.mulVec R)) L = E * dotProduct (star R) L := by
    have hsd := star_dot_mulVec Hᴴ R L
    rw [Matrix.conjTranspose_conjTranspose] at hsd
    rw [← hsd, h2, dotProduct_smul, smul_eq_mul]
  have h4 : dotProduct (star R) L = 1 := by
    have hc := hconj L R
    rw [hnorm, map_one] at hc
    exact hc.symm
  rw [h1, h3, h4, mul_one]

/-- **The two-level metric** `G^u ∝ [[1, iλ], [−iλ, 1]]` of Eq. 13 (unnormalized — the
`1/√(1−λ²)` prefactor drops out of the intertwining relation). -/
noncomputable def ptMetric (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.I * lam; -(Complex.I * lam), 1]

/-- **[The two-level metric is Hermitian]**. -/
theorem ptMetric_hermitian (lam : ℝ) : (ptMetric lam)ᴴ = ptMetric lam := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptMetric, Matrix.conjTranspose_apply]

/-- **[The two-level Hamiltonian is a good observable]** `Ĥ†G^u = G^uĤ` (Eq. 5 verified on
Eq. 13): with `good_observable_real_eigenvalue` this is exactly why the unbroken-phase
spectrum `E² = 1−λ²` of `ptTwoLevel` is real for `λ² ≤ 1`. -/
theorem ptTwoLevel_good_observable (lam : ℝ) :
    (ptTwoLevel lam)ᴴ * ptMetric lam = ptMetric lam * ptTwoLevel lam := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptTwoLevel, ptMetric, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two] <;>
    ring


/-! ### The real-to-complex-transition conjecture

The paper conjectures that the divergence of the modified HFT tracks the *real-to-complex
transition* of the eigenvalue — not the exceptional point per se (their Eq.-18 lattice model
separates the two). The exactly solvable instance is formalized: on the two-level model the
eigenbranch is `E(λ) = √(1−λ²)` with exact derivative `−λ/√(1−λ²)`
(`two_level_eigenvalue_deriv` — the LHS of the HFT, matching Eq. 14's RHS), the largest coupling
with a real eigenvalue is exactly `λ = 1` (`real_to_complex_transition_point`, reusing
`pt_transition_iff`), and the derivative diverges precisely approaching that point
(`divergence_at_real_complex_transition`, reusing `ep_divergence`) — transition point and
divergence point coincide. The general claim, resting on lattice numerics, remains a
conjecture and is recorded here at docstring level only. -/

/-- **[The exact eigenbranch derivative]** `∂/∂λ √(1−λ²) = −λ/√(1−λ²)` on the unbroken phase —
the left side of the modified HFT for the two-level model, equal to Eq. 14's matrix element. -/
theorem two_level_eigenvalue_deriv (lam : ℝ) (h : lam ^ 2 < 1) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-lam / Real.sqrt (1 - lam ^ 2)) lam := by
  have hpos : (0 : ℝ) < 1 - lam ^ 2 := by linarith
  have hne : 1 - lam ^ 2 ≠ 0 := hpos.ne'
  have hsne : Real.sqrt (1 - lam ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hinner : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * lam)) lam := by
    simpa using (hasDerivAt_pow 2 lam).const_sub 1
  have hs := (Real.hasDerivAt_sqrt hne).comp lam hinner
  have hval : -lam / Real.sqrt (1 - lam ^ 2)
      = 1 / (2 * Real.sqrt (1 - lam ^ 2)) * -(2 * lam) := by
    field_simp
  rw [hval]
  simpa [Function.comp_def] using hs

/-- **[The transition point is `λ = 1`]** the largest coupling admitting a real eigenvalue is
exactly the boundary of the unbroken phase (reusing `pt_transition_iff`). -/
theorem real_to_complex_transition_point :
    IsGreatest {lam : ℝ | ∃ E : ℝ, E ^ 2 = 1 - lam ^ 2} 1 := by
  constructor
  · exact ⟨0, by norm_num⟩
  · intro lam hlam
    have h := (pt_transition_iff lam).mp hlam
    nlinarith

/-- **[The conjecture's solvable instance]** on the two-level model the real-to-complex
transition point and the HFT-divergence point coincide at `λ = 1`: the largest real-spectrum
coupling is `1` and `∂E/∂λ` diverges approaching it — assembled entirely from
`real_to_complex_transition_point` and `ep_divergence`. -/
theorem divergence_at_real_complex_transition :
    IsGreatest {lam : ℝ | ∃ E : ℝ, E ^ 2 = 1 - lam ^ 2} 1
      ∧ Filter.Tendsto (fun lam : ℝ => lam / Real.sqrt (1 - lam ^ 2))
          (nhdsWithin 1 (Set.Iio 1)) Filter.atTop :=
  ⟨real_to_complex_transition_point, ep_divergence⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexScalingVirialTheorem

end
