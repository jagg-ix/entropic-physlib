/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

/-!
# The α-order metric of the Gaussian manifold: Levi-Civita connection and non-constant curvature

The companion to `FisherRaoGaussianLeviCivita`. The same Gaussian family `(μ, σ)`, metrized instead
by the **α-order entropy metric** (`α = 2`) `g^{(α)} = diag(1/(4√π), 3/(8√π))/σ³` (Gassner-Cafaro
2019, Eq. 21), has a *different* connection and curvature — and this is the paper's critical point:
the α-metric manifold is **not** maximally symmetric.

* **§A** the α-order metric `g^{(α)}` and its inverse, with `g^{(α)} · (g^{(α)})⁻¹ = 1`.
* **§B** the Levi-Civita connection derived from the metric: `Γ^μ_{μσ} = −3/(2σ)`, `Γ^σ_{μμ} = 1/σ`,
  `Γ^σ_{σσ} = −3/(2σ)` (Gassner-Cafaro Eq. 22). The `√π` of the metric cancels between the inverse
  metric and its derivative, leaving purely rational coefficients.
* **§C** the curvature *derived from the connection*. The single independent Riemann component
  `R^μ_{σμσ} = −3/(2σ²)` (Eq. 23) is computed from the Christoffel symbols through
  `R^l_{ijk} = ∂_j Γ^l_{ki} − ∂_k Γ^l_{ji} + Γ^l_{jm}Γ^m_{ki} − Γ^l_{km}Γ^m_{ji}` (Eq. 13). Lowering
  and dividing by `det g` gives the **Gauss (sectional) curvature** `K^{(α)} = R^μ_{σμσ}/g_{σσ} =
  −4√π σ` (Eq. 26) and the **scalar curvature** `R^{(α)} = 2K = −8√π σ` (Eq. 25).
* **§D** the critical contrast: `K^{(α)} = −4√π σ` **varies with `σ`**, so — unlike the Fisher-Rao
  manifold, whose curvature is the constant `−1/2` (`FisherRaoGaussianLeviCivita.frMaximallySymmetric`)
  — the α-order manifold is isotropic but *not homogeneous*, hence not maximally symmetric.

This is the geometric root of the paper's dynamical comparison: the position-dependent curvature of
the α-metric produces the slow (logarithmic) growth of the information geometric entropy of entropic
motion, against the fast (linear) growth on the constantly-curved Fisher-Rao manifold.

## References

* S. Gassner, C. Cafaro, arXiv:1903.11190 — Eqs. 21-26 (the α-order metric): the metric, Christoffel
  connection, Riemann component, scalar and sectional curvatures, and the failure of maximal symmetry.
* J. Burbea, C. R. Rao, *Entropy differential metric, distance and divergence measures in probability
  spaces*, J. Multivariate Anal. 12 (1982) 575 — the `φ_α`-entropy metric family the α-metric belongs to.
-/

set_option autoImplicit false

open Real

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.AlphaOrderGaussianCurvature

@[expose] public section

/-! ## A. The α-order metric of the Gaussian statistical manifold -/

/-- **The α-order metric component** `g_μμ = 1/(4√π σ³)` (Gassner-Cafaro Eq. 21). -/
noncomputable def gAlMuMu (σ : ℝ) : ℝ := (4 * Real.sqrt Real.pi)⁻¹ * (σ ^ 3)⁻¹

/-- **The α-order metric component** `g_σσ = 3/(8√π σ³)`. -/
noncomputable def gAlSiSi (σ : ℝ) : ℝ := 3 * (8 * Real.sqrt Real.pi)⁻¹ * (σ ^ 3)⁻¹

/-- **The inverse α-order metric component** `g^{μμ} = 4√π σ³`. -/
noncomputable def gInvAlMuMu (σ : ℝ) : ℝ := 4 * Real.sqrt Real.pi * σ ^ 3

/-- **The inverse α-order metric component** `g^{σσ} = 8√π σ³/3`. -/
noncomputable def gInvAlSiSi (σ : ℝ) : ℝ := 8 * Real.sqrt Real.pi * σ ^ 3 / 3

/-- `√π ≠ 0`. -/
lemma sqrtPi_ne_zero : Real.sqrt Real.pi ≠ 0 := by positivity

/-- **[`g^{μμ} g_μμ = 1`] the inverse relation for the location entry** (Gassner-Cafaro Eq. 21). -/
lemma gInvAlMuMu_mul (σ : ℝ) (hσ : σ ≠ 0) : gInvAlMuMu σ * gAlMuMu σ = 1 := by
  have hπ := sqrtPi_ne_zero
  rw [gInvAlMuMu, gAlMuMu]; field_simp

/-- **[`g^{σσ} g_σσ = 1`] the inverse relation for the scale entry.** -/
lemma gInvAlSiSi_mul (σ : ℝ) (hσ : σ ≠ 0) : gInvAlSiSi σ * gAlSiSi σ = 1 := by
  have hπ := sqrtPi_ne_zero
  rw [gInvAlSiSi, gAlSiSi]; field_simp

/-! ## B. The Levi-Civita connection (Christoffel symbols, Eq. 22) -/

/-- **[Derivative of `g_μμ`] `∂_σ g_μμ = −3/(4√π σ⁴)`.** -/
lemma gAlMuMu_deriv (σ : ℝ) (hσ : σ ≠ 0) :
    deriv gAlMuMu σ = (4 * Real.sqrt Real.pi)⁻¹ * (-3 / σ ^ 4) := by
  have hπ := sqrtPi_ne_zero
  have h : HasDerivAt gAlMuMu
      ((4 * Real.sqrt Real.pi)⁻¹ * (-((3 : ℝ) * σ ^ (3 - 1)) / (σ ^ 3) ^ 2)) σ :=
    ((hasDerivAt_pow 3 σ).inv (pow_ne_zero 3 hσ)).const_mul _
  rw [h.deriv]; field_simp

/-- **[Derivative of `g_σσ`] `∂_σ g_σσ = −9/(8√π σ⁴)`.** -/
lemma gAlSiSi_deriv (σ : ℝ) (hσ : σ ≠ 0) :
    deriv gAlSiSi σ = 3 * (8 * Real.sqrt Real.pi)⁻¹ * (-3 / σ ^ 4) := by
  have hπ := sqrtPi_ne_zero
  have h : HasDerivAt gAlSiSi
      (3 * (8 * Real.sqrt Real.pi)⁻¹ * (-((3 : ℝ) * σ ^ (3 - 1)) / (σ ^ 3) ^ 2)) σ :=
    ((hasDerivAt_pow 3 σ).inv (pow_ne_zero 3 hσ)).const_mul _
  rw [h.deriv]; field_simp

/-- **The Levi-Civita coefficient `Γ^μ_{μσ}`** `= ½ g^{μμ} ∂_σ g_{μμ}`. -/
noncomputable def christoffel_Mu_MuSi (σ : ℝ) : ℝ := (1 / 2) * gInvAlMuMu σ * deriv gAlMuMu σ

/-- **The Levi-Civita coefficient `Γ^σ_{μμ}`** `= −½ g^{σσ} ∂_σ g_{μμ}`. -/
noncomputable def christoffel_Si_MuMu (σ : ℝ) : ℝ := -(1 / 2) * gInvAlSiSi σ * deriv gAlMuMu σ

/-- **The Levi-Civita coefficient `Γ^σ_{σσ}`** `= ½ g^{σσ} ∂_σ g_{σσ}`. -/
noncomputable def christoffel_Si_SiSi (σ : ℝ) : ℝ := (1 / 2) * gInvAlSiSi σ * deriv gAlSiSi σ

/-- **[The connection field, Gassner-Cafaro Eq. 22] `Γ^μ_{μσ} = −3/(2σ)`.** The `√π` cancels between
`g^{μμ}` and `∂_σ g_{μμ}`. -/
lemma christoffel_Mu_MuSi_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Mu_MuSi σ = -3 / (2 * σ) := by
  have hπ := sqrtPi_ne_zero
  rw [christoffel_Mu_MuSi, gInvAlMuMu, gAlMuMu_deriv σ hσ]; field_simp

/-- **[The connection field, Gassner-Cafaro Eq. 22] `Γ^σ_{μμ} = 1/σ`.** -/
lemma christoffel_Si_MuMu_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Si_MuMu σ = 1 / σ := by
  have hπ := sqrtPi_ne_zero
  rw [christoffel_Si_MuMu, gInvAlSiSi, gAlMuMu_deriv σ hσ]; field_simp; ring

/-- **[The connection field, Gassner-Cafaro Eq. 22] `Γ^σ_{σσ} = −3/(2σ)`.** -/
lemma christoffel_Si_SiSi_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Si_SiSi σ = -3 / (2 * σ) := by
  have hπ := sqrtPi_ne_zero
  rw [christoffel_Si_SiSi, gInvAlSiSi, gAlSiSi_deriv σ hσ]; field_simp

/-! ## C. Curvature derived from the connection -/

/-- **The closed-form connection coefficient `Γ^μ_{μσ} = Γ^σ_{σσ} = −3/(2σ)`** as a function of `σ`,
used to compute the Riemann tensor. -/
noncomputable def gammaMuSi (σ : ℝ) : ℝ := -3 / (2 * σ)

/-- **[Derivative of the connection coefficient] `∂_σ Γ^μ_{μσ} = 3/(2σ²)`.** -/
lemma gammaMuSi_deriv (σ : ℝ) (hσ : σ ≠ 0) : deriv gammaMuSi σ = 3 / (2 * σ ^ 2) := by
  have h2 : (2 : ℝ) * σ ≠ 0 := mul_ne_zero (by norm_num) hσ
  have hu : HasDerivAt (fun s : ℝ => 2 * s) 2 σ := by
    simpa using (hasDerivAt_id σ).const_mul (2 : ℝ)
  have h : HasDerivAt gammaMuSi ((-3 : ℝ) * (-2 / (2 * σ) ^ 2)) σ := (hu.inv h2).const_mul (-3)
  rw [h.deriv]; field_simp

/-- **The independent Riemann curvature component `R^μ_{σμσ}`** computed from the Christoffel symbols
through Gassner-Cafaro Eq. 13,
`R^μ_{σμσ} = −∂_σ Γ^μ_{μσ} + Γ^μ_{μσ}Γ^σ_{σσ} − Γ^μ_{σσ}Γ^μ_{μσ}`, the surviving terms for this
`μ`-independent metric with `Γ^μ_{σσ} = 0`. -/
noncomputable def riemann_Mu_SiMuSi (σ : ℝ) : ℝ :=
  -deriv gammaMuSi σ + gammaMuSi σ * gammaMuSi σ - gammaMuSi σ * gammaMuSi σ

/-- **[The Riemann component, Gassner-Cafaro Eq. 23] `R^μ_{σμσ} = −3/(2σ²)`** — derived from the
Levi-Civita connection. -/
lemma riemann_Mu_SiMuSi_eq (σ : ℝ) (hσ : σ ≠ 0) : riemann_Mu_SiMuSi σ = -3 / (2 * σ ^ 2) := by
  rw [riemann_Mu_SiMuSi, gammaMuSi_deriv σ hσ]; ring

/-- **The Gauss (sectional) curvature** `K^{(α)} = R_{σμσμ}/det g = R^μ_{σμσ}/g_{σσ}`. -/
noncomputable def alphaSectionalCurvature (σ : ℝ) : ℝ := riemann_Mu_SiMuSi σ / gAlSiSi σ

/-- **[The sectional curvature, Gassner-Cafaro Eq. 26] `K^{(α)} = −4√π σ`.** Lowering `R^μ_{σμσ}` and
dividing by `det g` gives a curvature that depends on `σ`. -/
theorem alphaSectionalCurvature_eq (σ : ℝ) (hσ : σ ≠ 0) :
    alphaSectionalCurvature σ = -4 * Real.sqrt Real.pi * σ := by
  have hπ := sqrtPi_ne_zero
  rw [alphaSectionalCurvature, riemann_Mu_SiMuSi_eq σ hσ, gAlSiSi]; field_simp; ring

/-- **The scalar curvature** `R^{(α)} = 2 K^{(α)}` (the two-dimensional relation between the scalar
and Gauss curvatures). -/
noncomputable def alphaScalarCurvature (σ : ℝ) : ℝ := 2 * alphaSectionalCurvature σ

/-- **[The scalar curvature, Gassner-Cafaro Eq. 25] `R^{(α)} = −8√π σ`.** -/
theorem alphaScalarCurvature_eq (σ : ℝ) (hσ : σ ≠ 0) :
    alphaScalarCurvature σ = -8 * Real.sqrt Real.pi * σ := by
  rw [alphaScalarCurvature, alphaSectionalCurvature_eq σ hσ]; ring

/-! ## D. The critical contrast: the α-order manifold is not maximally symmetric -/

/-- **[The α-order curvature is not constant]** `K^{(α)} = −4√π σ` takes different values at different
scales `σ`, so the α-order Gaussian manifold is isotropic but not homogeneous — hence, unlike the
Fisher-Rao manifold of constant curvature `−1/2`, it is **not maximally symmetric** (Gassner-Cafaro,
Eq. 26 versus Eq. 20). -/
theorem alpha_curvature_not_constant (σ₁ σ₂ : ℝ) (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0) (hne : σ₁ ≠ σ₂) :
    alphaSectionalCurvature σ₁ ≠ alphaSectionalCurvature σ₂ := by
  rw [alphaSectionalCurvature_eq σ₁ h₁, alphaSectionalCurvature_eq σ₂ h₂]
  intro h
  exact hne (mul_left_cancel₀ (mul_ne_zero (by norm_num) sqrtPi_ne_zero) h)

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.AlphaOrderGaussianCurvature
