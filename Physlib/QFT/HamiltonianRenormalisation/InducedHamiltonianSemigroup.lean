/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.FreeScalarCovarianceFlow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The path integral induced Hamiltonians (Hamiltonian renormalisation II, §3.1.2)

Section 3.1.2 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation II* (arXiv:1711.06727v2):
the OS reconstruction of the flowed measures `μ^{(n)}_{RM}`.  The covariance acquires `2ⁿ`
distinct simple poles in `q²` (Eqs. 3.70–3.74), the class representatives live on `2ⁿ` sharp
times (Eq. 3.82), and the time-translation contraction semigroup acts on those representatives
through a matrix built from interpolating coefficients at the pole frequencies
(Eqs. 3.85–3.91), whose semigroup law rests on a van der Monde/Lagrange-interpolation identity
(Eqs. 3.92–3.94).  Proved here:

* `poleDoubling_first_step` — **Eq. 3.71**: the first flow step of the naive covariance already
  displays two distinct simple poles in `q²`, one for each Brillouin branch — the pole-doubling
  mechanism that inflates the field species.
* `timeEvolutionMatrix`, `timeEvolutionMatrix_semigroup` — **Eqs. 3.90–3.94**: the matrix
  `A^{r,r'}(β) = Σ_N h^r_N e^{−ω_N(β+τr')}` built from coefficients `h^r_N` that interpolate the
  frequencies, `Σ_r e^{−ω_N τ r}·h^r_{N'} = δ_{N,N'}` (Eq. 3.80 at the pole values), satisfies
  the contraction-semigroup law `A(β₁)·A(β₂) = A(β₁+β₂)` — the paper's van der Monde argument,
  here as an exact finite-sum computation.

**Honest layering.**  Exact field algebra and `Finset` manipulation.  The residue extraction of
the sharp-time representatives (Eqs. 3.79–3.82), the null-vector identification (Eqs. 3.83–3.84),
the Lagrange-basis construction of the interpolating functions `h_N` (Eq. 3.81), and the
second-quantised realisation with `2ⁿ` mutually commuting field species (Eqs. 3.95–3.107, which
needs a bosonic Fock/Weyl layer that the repository's `WeylCCRSpacetime` two-dimensional
symplectic module does not provide) are recorded, not re-derived.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II: renormalisation flow of
  1+1 dimensional free scalar fields*, arXiv:1711.06727v2, §3.1.2 (Eqs. 3.70–3.107).
-/

set_option autoImplicit false

open Real Finset

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-! ## §A — pole doubling (Eqs. 3.70–3.71) -/

/-- **Eq. 3.71**: one flow step applied to the naive covariance `ε²_{2M}/(2[1−cos(t/2)] + (q/2)²)`
produces a sum of two simple-pole terms, one per Brillouin branch — at each renormalisation step
the number of `q²`-poles doubles. -/
theorem poleDoubling_first_step (ε q t : ℝ)
    (h₁ : 2*(1 - Real.cos (t/2)) + q^2/4 ≠ 0)
    (h₂ : 2*(1 + Real.cos (t/2)) + q^2/4 ≠ 0) :
    (1/2) * ( (ε/2)^2/(2*(1 - Real.cos (t/2)) + (q/2)^2) * (1 + Real.cos (t/2))
      + (ε/2)^2/(2*(1 + Real.cos (t/2)) + (q/2)^2) * (1 - Real.cos (t/2)) )
      = ε^2/8 * ( (1 + Real.cos (t/2))/(2*(1 - Real.cos (t/2)) + q^2/4)
        + (1 - Real.cos (t/2))/(2*(1 + Real.cos (t/2)) + q^2/4) ) := by
  have h₁' : 2*(1 - Real.cos (t/2)) + (q/2)^2 ≠ 0 := by
    intro h
    exact h₁ (by linarith [h, sq_nonneg q])
  have h₂' : 2*(1 + Real.cos (t/2)) + (q/2)^2 ≠ 0 := by
    intro h
    exact h₂ (by linarith [h, sq_nonneg q])
  have e₁ : 2*(1 - Real.cos (t/2)) + (q/2)^2 = 2*(1 - Real.cos (t/2)) + q^2/4 := by ring
  have e₂ : 2*(1 + Real.cos (t/2)) + (q/2)^2 = 2*(1 + Real.cos (t/2)) + q^2/4 := by ring
  rw [e₁, e₂]
  rw [e₁] at h₁'
  rw [e₂] at h₂'
  field_simp
  ring

/-! ## §B — the semigroup of the sharp-time representatives (Eqs. 3.90–3.94) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- **Eq. 3.90**: the time-evolution matrix on the `2ⁿ` sharp-time representatives,
`A^{r,r'}(β) = Σ_N h^r_N e^{−ω_N(β + τr')}`, built from the frequencies `ω_N` and the
interpolating coefficients `h^r_N` of Eq. 3.88. -/
noncomputable def timeEvolutionMatrix (h : Fin d → ι → ℝ) (ω : ι → ℝ) (τ : ℝ)
    (β : ℝ) (r r' : Fin d) : ℝ :=
  ∑ N : ι, h r N * Real.exp (-(ω N * (β + τ*r')))

/-- **Eqs. 3.92–3.94, the van der Monde semigroup law**: if the coefficients interpolate the
frequencies, `Σ_r e^{−ω_N τr}·h^r_{N'} = δ_{N,N'}` (Eq. 3.80 evaluated at the pole values
`k₀ = −iω_N`), then the time-evolution matrices compose as a one-parameter semigroup,
`A(β₁)·A(β₂) = A(β₁+β₂)`. -/
theorem timeEvolutionMatrix_semigroup (h : Fin d → ι → ℝ) (ω : ι → ℝ) (τ : ℝ)
    (hinterp : ∀ N N' : ι,
      (∑ r : Fin d, Real.exp (-(ω N * (τ*r))) * h r N') = if N = N' then 1 else 0)
    (β₁ β₂ : ℝ) (r r'' : Fin d) :
    ∑ r' : Fin d, timeEvolutionMatrix h ω τ β₁ r r' * timeEvolutionMatrix h ω τ β₂ r' r''
      = timeEvolutionMatrix h ω τ (β₁ + β₂) r r'' := by
  have key : ∀ N : ι,
      (∑ r' : Fin d, Real.exp (-(ω N * (τ*r'))) * timeEvolutionMatrix h ω τ β₂ r' r'')
        = Real.exp (-(ω N * (β₂ + τ*r''))) := by
    intro N
    unfold timeEvolutionMatrix
    calc ∑ r' : Fin d, Real.exp (-(ω N * (τ*r')))
          * ∑ N' : ι, h r' N' * Real.exp (-(ω N' * (β₂ + τ*r'')))
        = ∑ N' : ι, (∑ r' : Fin d, Real.exp (-(ω N * (τ*r'))) * h r' N')
            * Real.exp (-(ω N' * (β₂ + τ*r''))) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun N' _ =>
            Finset.sum_congr rfl fun r' _ => by ring
      _ = Real.exp (-(ω N * (β₂ + τ*r''))) := by
          simp_rw [hinterp, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq]
          simp
  have expand : ∀ g : Fin d → ℝ,
      ∑ r' : Fin d, (∑ N : ι, h r N * Real.exp (-(ω N * (β₁ + τ*r')))) * g r'
        = ∑ N : ι, h r N * Real.exp (-(ω N * β₁))
            * ∑ r' : Fin d, Real.exp (-(ω N * (τ*r'))) * g r' := by
    intro g
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [show -(ω N * (β₁ + τ*r')) = -(ω N * β₁) + -(ω N * (τ*r')) from by ring,
      Real.exp_add]
    ring
  calc ∑ r' : Fin d, timeEvolutionMatrix h ω τ β₁ r r' * timeEvolutionMatrix h ω τ β₂ r' r''
      = ∑ N : ι, h r N * Real.exp (-(ω N * β₁))
          * ∑ r' : Fin d, Real.exp (-(ω N * (τ*r')))
            * timeEvolutionMatrix h ω τ β₂ r' r'' :=
        expand fun r' => timeEvolutionMatrix h ω τ β₂ r' r''
    _ = ∑ N : ι, h r N * Real.exp (-(ω N * β₁)) * Real.exp (-(ω N * (β₂ + τ*r''))) := by
        refine Finset.sum_congr rfl fun N _ => ?_
        rw [key N]
    _ = timeEvolutionMatrix h ω τ (β₁ + β₂) r r'' := by
        unfold timeEvolutionMatrix
        refine Finset.sum_congr rfl fun N _ => ?_
        rw [show -(ω N * (β₁ + β₂ + τ*r'')) = -(ω N * β₁) + -(ω N * (β₂ + τ*r'')) from by ring,
          Real.exp_add, mul_assoc]

/-! ## §C — the fixed-point pole parametrisation (Eqs. 3.72–3.75) -/

/-- **Eqs. 3.62 + 3.74–3.75, the fixed-point poles and coefficients**: the `N`-th spatial
image term of the fixed-point covariance — momentum `(l+NM)·k_R` in the extended Brillouin
zone, weight `2(1−cos([l+NM]k_M))/([l+NM]k_M)²` — is exactly the simple-pole term with pole
`λ*_N(t) = t + 2πN` and coefficient `ĝ*_N(t) = 2(1−cos t)/(t+2πN)²` in the universal
parametrisation of Eq. 3.74: at the fixed point every image mode is switched on with its
Mittag-Leffler coefficient. -/
theorem imagePole_coefficient (kR kM ε k₀ p t q : ℝ) (l M' NN : ℝ)
    (hkM : kM = kR * ε) (ht : t = kM * l) (h2π : kM * M' = 2 * Real.pi)
    (hq : q^2 = (k₀^2 + p^2) * ε^2) (hε : ε ≠ 0)
    (hpole : t + 2*Real.pi*NN ≠ 0) :
    (1 / (((l + NN*M') * kR)^2 + k₀^2 + p^2))
        * (2*(1 - Real.cos t) / (((l + NN*M') * kM)^2))
      = ε^2 * (2*(1 - Real.cos t) / ((t + 2*Real.pi*NN)^2))
          / (q^2 + (t + 2*Real.pi*NN)^2) := by
  have hlam : (l + NN*M') * kM = t + 2*Real.pi*NN := by
    rw [ht, ← h2π]
    ring
  have hkR2 : ((l + NN*M') * kR)^2 * ε^2 = (t + 2*Real.pi*NN)^2 := by
    rw [← hlam, hkM]
    ring
  have hq0 : 0 ≤ q^2 := by
    rw [hq]
    positivity
  have hdenq : q^2 + (t + 2*Real.pi*NN)^2 ≠ 0 := by
    intro h0
    have hx2 : (t + 2*Real.pi*NN)^2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (t + 2*Real.pi*NN)]) (sq_nonneg _)
    exact (pow_ne_zero 2 hpole) hx2
  have hden1 : ((l + NN*M')*kR)^2 + k₀^2 + p^2 = (q^2 + (t + 2*Real.pi*NN)^2)/ε^2 := by
    rw [eq_div_iff (pow_ne_zero 2 hε)]
    linear_combination hkR2 - hq
  rw [hden1, hlam]
  field_simp

end Physlib.QFT.HamiltonianRenormalisation

end
