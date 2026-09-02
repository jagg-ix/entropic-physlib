/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# The covariance flow of the 1+1 free scalar field (Hamiltonian renormalisation II, §3.1.1)

Section 3.1.1 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation II: renormalisation flow of
1+1 dimensional free scalar fields* (arXiv:1711.06727v2): the block-spin flow of the history-field
Gaussian measures, in the Fourier variables `t = k_M l` and `q = √(k₀² + p²)·ε_{RM}`.  The flow of
covariances (Eq. 3.40) is

  `ĉ^{(n+1)}_M(l) = ½{ĉ^{(n)}_{2M}(l)[1+cos(t/2)] + ĉ^{(n)}_{2M}(l+M)[1−cos(t/2)]}`,

the second slot being the shifted Brillouin branch `cos(k_{2M}(l+M)) = −cos(t/2)`
(`Real.cos_add_pi`).  The paper parametrises the covariances by three functions (Eq. 3.45),

  `ĉ^{(n)}(l) = (ε²_{RM}/q³) · (b_n(q) + c_n(q)·cos t)/(a_n(q) − cos t)`,

and its §3.1.1 rests on four exact computations, all proved here:

* `initial_covariance_ansatz` — **Eqs. 3.42–3.44**: the naive lattice-Laplacian covariance
  `ε²/(2[1−cos t] + q²)` is the ansatz with `a₀ = 1 + q²/2`, `b₀ = q³/2`, `c₀ = 0`.
* `covariance_flow_step` — **Eqs. 3.46–3.47**: the ansatz is invariant under the flow, with the
  recursion `a_{n+1}(q) = 2a_n(q/2)² − 1`, `b_{n+1} = 2[2ab + b + c + ac](q/2)`,
  `c_{n+1} = 2[b + c + ac](q/2)` read off the common-denominator computation of Eq. 3.46.
* `fixedPoint_a`, `fixedPoint_b`, `fixedPoint_c` — **Eqs. 3.48/3.58**: the hyperbolic triple
  `a_*(q) = cosh q`, `b_*(q) = q·cosh q − sinh q`, `c_*(q) = sinh q − q` solves the fixed point
  equations exactly — `a_*` by the cosine-duplication functional equation of `cosh`, `b_*`/`c_*`
  by the double-argument identities.  `fixedPoint_d` is the decoupled combination
  `d_* = b_* + c_* = q(cosh q − 1)` of **Eq. 3.49**.
* `fixedPoint_covariance_flow` — the packaged statement: one flow step applied to the fixed-point
  covariance returns the fixed-point covariance at the coarser resolution.
* `continuum_projection_match`, `image_ladder_resummed`, `tsum_exp_geometric` — **Eqs. 3.65/3.69**:
  the geometric ladder of temporal images resums to `sinh q/(cosh q − cos t)`
  (`(1−r²)/(1−2r·cos t+r²)` at `r = e^{−q}`, each one-sided ladder being the geometric series
  `∑ e^{N(−q±it)} = (1−e^{−q±it})⁻¹`), and the resummed continuum cylindrical projection displays
  exactly the fixed-point triple `(a_*, b_*, c_*)` — the paper's *perfect match*: the fixed point
  of the path-integral flow is the cylindrical projection of the continuum covariance.

**Honest layering.**  Exact field/hyperbolic algebra and the complex geometric series.  The
Gaussian measures themselves, the Poisson resummation step (Eq. 3.63) and the two residue
integrals (Eqs. 3.66–3.68) that produce the ladder coefficients are the paper's analytic input,
recorded not re-derived; the uniqueness argument for the fixed point (the polynomial-degree
count Eqs. 3.50–3.52 and the `q → 0` normalisations Eqs. 3.56–3.57) is likewise recorded.  The
`2πN`-spaced pole ladder of Eq. 3.75 has the same shape as the boson Matsubara frequencies of
`Physlib.QFT.Matsubara.PathIntegral`, but its index counts spatial momentum images, not thermal
modes — noted, not identified.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II: renormalisation flow of
  1+1 dimensional free scalar fields*, arXiv:1711.06727v2, §3.1.1 (Eqs. 3.40–3.69).
-/

set_option autoImplicit false

open Real

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-! ## §A — the ansatz and the initial covariance (Eqs. 3.42–3.45) -/

/-- **Eqs. 3.42–3.44**: the naive lattice-Laplacian covariance `ε²/(2[1−cos t] + q²)` is the
three-function ansatz of Eq. 3.45 with `a₀(q) = 1 + q²/2`, `b₀(q) = q³/2`, `c₀(q) = 0`. -/
theorem initial_covariance_ansatz (ε q t : ℝ) (hq : q ≠ 0)
    (hden : 2*(1 - Real.cos t) + q^2 ≠ 0) :
    ε^2 / (2*(1 - Real.cos t) + q^2)
      = ε^2/q^3 * ((q^3/2 + 0*Real.cos t) / ((1 + q^2/2) - Real.cos t)) := by
  have hden' : (1 + q^2/2) - Real.cos t ≠ 0 := fun h => hden (by linarith)
  rw [div_mul_div_comm, div_eq_div_iff hden (mul_ne_zero (pow_ne_zero 3 hq) hden')]
  ring

/-! ## §B — the flow preserves the ansatz (Eqs. 3.40, 3.46–3.47) -/

/-- **Eqs. 3.46–3.47**: one block-spin flow step (Eq. 3.40) applied to the ansatz at resolution
`2M` — values `A = a_n(q/2)`, `B = b_n(q/2)`, `C = c_n(q/2)`, lattice constant `ε/2`, momentum
variable `t/2`, with the shifted Brillouin branch as the second slot — returns the ansatz at
resolution `M` with the recursion values `a_{n+1} = 2A² − 1`, `b_{n+1} = 2[2AB + B + C + AC]`,
`c_{n+1} = 2[B + C + AC]` of Eq. 3.47. -/
theorem covariance_flow_step (ε q t A B C : ℝ) (hq : q ≠ 0)
    (h₁ : A - Real.cos (t/2) ≠ 0) (h₂ : A + Real.cos (t/2) ≠ 0) :
    (1/2) * ( (ε/2)^2/(q/2)^3 * ((B + C*Real.cos (t/2)) / (A - Real.cos (t/2)))
        * (1 + Real.cos (t/2))
      + (ε/2)^2/(q/2)^3 * ((B - C*Real.cos (t/2)) / (A + Real.cos (t/2)))
        * (1 - Real.cos (t/2)) )
      = ε^2/q^3 * ((2*(2*A*B + B + C + A*C) + 2*(B + C + A*C)*Real.cos t)
          / ((2*A^2 - 1) - Real.cos t)) := by
  have h2t : 2*(t/2) = t := by ring
  have hct : Real.cos t = 2*Real.cos (t/2)^2 - 1 := by
    have := Real.cos_two_mul (t/2)
    rw [h2t] at this
    linarith
  rw [hct]
  have hden : (2*A^2 - 1) - (2*Real.cos (t/2)^2 - 1) ≠ 0 := by
    have hfac : (2*A^2 - 1) - (2*Real.cos (t/2)^2 - 1)
        = 2*(A - Real.cos (t/2))*(A + Real.cos (t/2)) := by ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero two_ne_zero h₁) h₂
  field_simp
  ring

/-! ## §C — the hyperbolic fixed point (Eqs. 3.48–3.49, 3.58) -/

/-- **Eq. 3.48**: `a_*(q) = cosh q` solves `a_*(q) = 2a_*(q/2)² − 1` — the duplication functional
equation of the hyperbolic cosine, stated at `x = q/2`. -/
theorem fixedPoint_a (x : ℝ) : Real.cosh (2*x) = 2*Real.cosh x^2 - 1 := by
  rw [Real.cosh_two_mul]
  linear_combination - Real.cosh_sq_sub_sinh_sq x

/-- **Eq. 3.58, `b` component**: `b_*(q) = q·cosh q − sinh q` solves the recursion
`b_*(q) = 2[2a_*b_* + b_* + c_* + a_*c_*](q/2)`, stated at `x = q/2`. -/
theorem fixedPoint_b (x : ℝ) :
    (2*x)*Real.cosh (2*x) - Real.sinh (2*x)
      = 2*(2*Real.cosh x*(x*Real.cosh x - Real.sinh x) + (x*Real.cosh x - Real.sinh x)
          + (Real.sinh x - x) + Real.cosh x*(Real.sinh x - x)) := by
  rw [Real.cosh_two_mul, Real.sinh_two_mul]
  linear_combination (-2*x) * Real.cosh_sq_sub_sinh_sq x

/-- **Eq. 3.58, `c` component**: `c_*(q) = sinh q − q` solves the recursion
`c_*(q) = 2[b_* + c_* + a_*c_*](q/2)`, stated at `x = q/2`. -/
theorem fixedPoint_c (x : ℝ) :
    Real.sinh (2*x) - 2*x
      = 2*((x*Real.cosh x - Real.sinh x) + (Real.sinh x - x)
          + Real.cosh x*(Real.sinh x - x)) := by
  rw [Real.sinh_two_mul]
  ring

/-- **Eq. 3.49**: the decoupled combination `d_* = b_* + c_* = q(cosh q − 1)` solves its own
homogeneous equation `d_*(q) = 4[1 + a_*(q/2)]·d_*(q/2)`, stated at `x = q/2`. -/
theorem fixedPoint_d (x : ℝ) :
    (2*x)*(Real.cosh (2*x) - 1) = 4*(1 + Real.cosh x)*(x*(Real.cosh x - 1)) := by
  rw [Real.cosh_two_mul]
  linear_combination (-2*x) * Real.cosh_sq_sub_sinh_sq x

/-- **The hyperbolic triple is a fixed point of the flow** (Eqs. 3.40 + 3.58 packaged): one
block-spin step applied to the fixed-point covariance at resolution `2M` returns the fixed-point
covariance at resolution `M`. -/
theorem fixedPoint_covariance_flow (ε q t : ℝ) (hq : q ≠ 0)
    (h₁ : Real.cosh (q/2) - Real.cos (t/2) ≠ 0)
    (h₂ : Real.cosh (q/2) + Real.cos (t/2) ≠ 0) :
    (1/2) * ( (ε/2)^2/(q/2)^3
        * (((q/2)*Real.cosh (q/2) - Real.sinh (q/2)
            + (Real.sinh (q/2) - q/2)*Real.cos (t/2)) / (Real.cosh (q/2) - Real.cos (t/2)))
        * (1 + Real.cos (t/2))
      + (ε/2)^2/(q/2)^3
        * (((q/2)*Real.cosh (q/2) - Real.sinh (q/2)
            - (Real.sinh (q/2) - q/2)*Real.cos (t/2)) / (Real.cosh (q/2) + Real.cos (t/2)))
        * (1 - Real.cos (t/2)) )
      = ε^2/q^3 * ((q*Real.cosh q - Real.sinh q + (Real.sinh q - q)*Real.cos t)
          / (Real.cosh q - Real.cos t)) := by
  have h2q : 2*(q/2) = q := by ring
  have ha := fixedPoint_a (q/2)
  have hb := fixedPoint_b (q/2)
  have hc := fixedPoint_c (q/2)
  rw [h2q] at ha hb hc
  have hstep := covariance_flow_step ε q t (Real.cosh (q/2))
    ((q/2)*Real.cosh (q/2) - Real.sinh (q/2)) (Real.sinh (q/2) - q/2) hq h₁ h₂
  rw [← ha, ← hb, ← hc] at hstep
  exact hstep

/-! ## §D — the continuum cylindrical projection matches the fixed point (Eqs. 3.65, 3.69) -/

/-- The one-sided ladder of temporal images is a geometric series (the summation entering
Eq. 3.65): `∑_{N≥0} e^{N(−q+iσt)} = (1 − e^{−q+iσt})⁻¹` for `q > 0` and either sign `σ` of the
phase. -/
theorem tsum_exp_geometric (q t : ℝ) (hq : 0 < q) :
    ∑' N : ℕ, Complex.exp ((N : ℂ) * (-(q:ℂ) + t*Complex.I))
      = (1 - Complex.exp (-(q:ℂ) + t*Complex.I))⁻¹ := by
  have hnorm : ‖Complex.exp (-(q:ℂ) + t*Complex.I)‖ < 1 := by
    rw [Complex.norm_exp]
    have hre : (-(q:ℂ) + t*Complex.I).re = -q := by simp
    rw [hre]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  simp_rw [Complex.exp_nat_mul]
  exact tsum_geometric_of_norm_lt_one (K := ℂ) hnorm

/-- **The resummed image ladder** (the closing step of Eq. 3.69): the two-sided geometric ladder
at ratio `r = e^{−q}` has the closed form `(1−r²)/(1−2r·cos t+r²) = sinh q/(cosh q − cos t)`. -/
theorem image_ladder_resummed (q t : ℝ) (hq : 0 < q) :
    (1 - Real.exp (-q)^2) / (1 - 2*Real.exp (-q)*Real.cos t + Real.exp (-q)^2)
      = Real.sinh q / (Real.cosh q - Real.cos t) := by
  have hE : Real.exp (-q) * Real.exp q = 1 := by
    rw [← Real.exp_add]
    simp
  have hcosh : (1:ℝ) < Real.cosh q := by
    have h1 : Real.cosh q = 1 + 2*Real.sinh (q/2)^2 := by
      have h2 := Real.cosh_two_mul (q/2)
      rw [show 2*(q/2) = q by ring] at h2
      linear_combination h2 + Real.cosh_sq_sub_sinh_sq (q/2)
    have hs : 0 < Real.sinh (q/2) := by
      rw [Real.sinh_eq]
      have hlt : Real.exp (-(q/2)) < Real.exp (q/2) := Real.exp_lt_exp.mpr (by linarith)
      linarith
    have h3 : 0 < Real.sinh (q/2)^2 := pow_pos hs 2
    linarith
  have hden₂ : 0 < Real.cosh q - Real.cos t :=
    sub_pos.mpr (lt_of_le_of_lt (Real.cos_le_one t) hcosh)
  have hkey : 1 - 2*Real.exp (-q)*Real.cos t + Real.exp (-q)^2
      = 2*Real.exp (-q)*(Real.cosh q - Real.cos t) := by
    rw [Real.cosh_eq]
    linear_combination -hE
  have hden₁ : 1 - 2*Real.exp (-q)*Real.cos t + Real.exp (-q)^2 ≠ 0 := by
    rw [hkey]
    exact ne_of_gt (mul_pos (by positivity) hden₂)
  rw [div_eq_div_iff hden₁ hden₂.ne']
  rw [Real.sinh_eq, Real.cosh_eq]
  linear_combination (Real.cos t - Real.exp (-q)) * hE

/-- **Eq. 3.69, perfect match**: the Poisson-resummed continuum cylindrical projection —
`(q − sinh q)/q³` from the `N = 0` principal-value residue plus the `(cosh q − 1)/q³` coefficient
of the resummed ladder — is exactly the fixed-point ansatz with the hyperbolic triple
`(a_*, b_*, c_*) = (cosh q, q·cosh q − sinh q, sinh q − q)` of Eq. 3.58: the fixed point of the
path-integral flow is the cylindrical projection of the continuum covariance. -/
theorem continuum_projection_match (q t : ℝ) (hq : q ≠ 0)
    (hden : Real.cosh q - Real.cos t ≠ 0) :
    (q - Real.sinh q)/q^3
      + (Real.cosh q - 1)/q^3 * (Real.sinh q / (Real.cosh q - Real.cos t))
      = 1/q^3 * ((q*Real.cosh q - Real.sinh q + (Real.sinh q - q)*Real.cos t)
          / (Real.cosh q - Real.cos t)) := by
  field_simp
  ring

end Physlib.QFT.HamiltonianRenormalisation

end
