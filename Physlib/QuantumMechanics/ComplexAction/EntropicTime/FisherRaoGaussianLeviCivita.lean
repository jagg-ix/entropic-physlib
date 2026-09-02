/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
meta import Zil

/-!
# The Levi-Civita connection of the Fisher-Rao Gaussian statistical manifold, and its constant
negative curvature

The Gaussian family `p(x|μ,σ) = (2πσ²)^{-1/2} exp(-(x-μ)²/2σ²)` with the Fisher-Rao information metric
is a two-dimensional statistical manifold `(μ, σ)` whose metric is `g = diag(1, 2)/σ²` (Gassner-Cafaro
2019, Eq. 9). This is the arena of Caticha's *entropic dynamics*: the expected trajectory between two
distributions is the geodesic of this information metric, so the affine connection derived here is the
connection that governs entropic motion.

From the metric alone we derive its **Levi-Civita connection** (the Christoffel symbols, the affine
"connection field" of the manifold) and its curvature:

* **§A** the Fisher-Rao metric `g` and its inverse, with `g · g⁻¹ = 1` and `g_σσ = 2 g_μμ`.
* **§B** the Levi-Civita connection `Γ^k_{ij} = ½ g^{km}(∂_i g_{mj} + ∂_j g_{im} − ∂_m g_{ij})`. Because
  the metric depends only on `σ`, the surviving coefficients reduce to metric-derivative expressions:
  `Γ^μ_{μσ} = ½ g^{μμ} ∂_σ g_{μμ} = −1/σ`, `Γ^σ_{μμ} = −½ g^{σσ} ∂_σ g_{μμ} = 1/(2σ)`,
  `Γ^σ_{σσ} = ½ g^{σσ} ∂_σ g_{σσ} = −1/σ` (Gassner-Cafaro Eq. 12), the remaining ones vanishing.
* **§C** the curvature. The manifold has constant sectional curvature `K = −1/2` (Eq. 20), so its
  Riemann tensor is the constant-curvature form `R_{abcd} = K(g_{ac}g_{bd} − g_{ad}g_{bc})`
  (`Curvature.constantCurvature`). Contracting through the repository's general-relativity curvature
  API gives the **Ricci tensor** `R_{bd} = −½ g_{bd}` — an Einstein manifold — (Eq. 16) and the
  **scalar curvature** `R = −1` (Eq. 18).
* **§D** maximal symmetry: being of constant curvature, the manifold is maximally symmetric
  (isotropic and homogeneous); its scalar curvature is the two-dimensional value `R = 2K`.

The constant *negative* curvature is what makes the Gaussian statistical manifold hyperbolic — the
geometric source of the exponential geodesic spread (positive Jacobi/Lyapunov behaviour) that Gassner
and Cafaro read as the linear temporal growth of the information geometric entropy of entropic motion.

## References

* S. Gassner, C. Cafaro, *Information Geometric Complexity of Entropic Motion on Curved Statistical
  Manifolds under Different Metrizations of Probability Spaces*, arXiv:1903.11190 — Eqs. 4, 9-20 (the
  Fisher-Rao case): the metric, Christoffel connection, Riemann/Ricci tensors and scalar curvature.
* A. Caticha, *Entropic Dynamics*, Entropy 17 (2015) 6110 — the expected trajectory of entropic
  motion is the geodesic of the information metric, governed by this Levi-Civita connection
  (`EntropicTime.EntropicDynamicsCanonicalRepresentation`,
  `EntropicTime.ProbabilityMetricInformationGeometry` — the Fisher-Rao information metric).
* N. N. Cencov, *Statistical Decision Rules and Optimal Inference* — uniqueness of the Fisher-Rao
  metric under Markov morphisms.
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126 (2011) 1021,
  arXiv:1104.3381 — the entropic-time complex contour whose real (reversible) leaf carries this
  metric (`ActionAngleNagaoNielsenComplexAction`, `Bell.LeviCivitaNagaoContour`).
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

/-! ## A. The Fisher-Rao metric of the Gaussian statistical manifold -/

/-- **The Fisher-Rao metric component** `g_μμ = 1/σ²` (the `μ`-`μ` entry). -/
noncomputable def gMuMu (σ : ℝ) : ℝ := (σ ^ 2)⁻¹

/-- **The Fisher-Rao metric component** `g_σσ = 2/σ²` (the `σ`-`σ` entry): the Gaussian Fisher
information of the scale is twice that of the location. -/
noncomputable def gSiSi (σ : ℝ) : ℝ := 2 * (σ ^ 2)⁻¹

/-- **The inverse metric component** `g^{μμ} = σ²`. -/
noncomputable def gInvMuMu (σ : ℝ) : ℝ := σ ^ 2

/-- **The inverse metric component** `g^{σσ} = σ²/2`. -/
noncomputable def gInvSiSi (σ : ℝ) : ℝ := σ ^ 2 / 2

/-- **The Fisher-Rao information metric** `g = diag(1, 2)/σ²` of the Gaussian manifold with coordinates
`(θ¹, θ²) = (μ, σ)` (Gassner-Cafaro Eq. 9). -/
noncomputable def frMetric (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gMuMu σ, 0; 0, gSiSi σ]

/-- **The inverse Fisher-Rao metric** `g⁻¹ = diag(1, 1/2)·σ²` (Gassner-Cafaro Eq. 11). -/
noncomputable def frMetricInv (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gInvMuMu σ, 0; 0, gInvSiSi σ]

/-- **[The metric is symmetric] `g_{ij} = g_{ji}`.** -/
lemma frMetric_symm (σ : ℝ) : ∀ i j, frMetric σ i j = frMetric σ j i := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [frMetric]

/-- **[The scale carries twice the location's Fisher information] `g_σσ = 2 g_μμ`.** -/
lemma gSiSi_eq_two_gMuMu (σ : ℝ) : gSiSi σ = 2 * gMuMu σ := rfl

/-- **[`g⁻¹` is the metric inverse] `g⁻¹ · g = 1`** — the defining relation `g^{ij} g_{jk} = δ^i_k`
(Gassner-Cafaro Eq. 11). -/
lemma frMetricInv_mul_metric (σ : ℝ) (hσ : σ ≠ 0) :
    frMetricInv σ * frMetric σ = 1 := by
  have h2 : (σ ^ 2) ≠ 0 := pow_ne_zero 2 hσ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frMetric, frMetricInv, gMuMu, gSiSi, gInvMuMu, gInvSiSi, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp

/-! ## B. The Levi-Civita connection (Christoffel symbols) -/

/-- **[Derivative of `g_μμ`] `∂_σ g_μμ = −2/σ³`.** -/
lemma gMuMu_deriv (σ : ℝ) (hσ : σ ≠ 0) : deriv gMuMu σ = -2 / σ ^ 3 := by
  have h : HasDerivAt gMuMu (-((2 : ℝ) * σ ^ (2 - 1)) / (σ ^ 2) ^ 2) σ :=
    (hasDerivAt_pow 2 σ).inv (pow_ne_zero 2 hσ)
  rw [h.deriv]; field_simp; ring

/-- **[Derivative of `g_σσ`] `∂_σ g_σσ = −4/σ³`.** -/
lemma gSiSi_deriv (σ : ℝ) (hσ : σ ≠ 0) : deriv gSiSi σ = -4 / σ ^ 3 := by
  have h : HasDerivAt gSiSi (2 * (-((2 : ℝ) * σ ^ (2 - 1)) / (σ ^ 2) ^ 2)) σ :=
    ((hasDerivAt_pow 2 σ).inv (pow_ne_zero 2 hσ)).const_mul 2
  rw [h.deriv]; field_simp; ring

/-- **The Levi-Civita coefficient `Γ^μ_{μσ}`** `= ½ g^{μμ} ∂_σ g_{μμ}`: the surviving `μ`-`μ`-`σ`
Christoffel symbol of the Fisher-Rao connection (the other terms in `½ g^{μμ}(∂_μ g_{μσ} + ∂_σ g_{μμ}
− ∂_μ g_{μσ})` vanish because the metric is `μ`-independent). -/
noncomputable def christoffel_Mu_MuSi (σ : ℝ) : ℝ := (1 / 2) * gInvMuMu σ * deriv gMuMu σ

/-- **The Levi-Civita coefficient `Γ^σ_{μμ}`** `= −½ g^{σσ} ∂_σ g_{μμ}`. -/
noncomputable def christoffel_Si_MuMu (σ : ℝ) : ℝ := -(1 / 2) * gInvSiSi σ * deriv gMuMu σ

/-- **The Levi-Civita coefficient `Γ^σ_{σσ}`** `= ½ g^{σσ} ∂_σ g_{σσ}`. -/
noncomputable def christoffel_Si_SiSi (σ : ℝ) : ℝ := (1 / 2) * gInvSiSi σ * deriv gSiSi σ

/-- **[The connection field, Gassner-Cafaro Eq. 12] `Γ^μ_{μσ} = −1/σ`** — derived from the metric
inverse and the metric derivative. -/
lemma christoffel_Mu_MuSi_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Mu_MuSi σ = -1 / σ := by
  rw [christoffel_Mu_MuSi, gInvMuMu, gMuMu_deriv σ hσ]; field_simp

/-- **[The connection field, Gassner-Cafaro Eq. 12] `Γ^σ_{μμ} = 1/(2σ)`.** -/
lemma christoffel_Si_MuMu_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Si_MuMu σ = 1 / (2 * σ) := by
  rw [christoffel_Si_MuMu, gInvSiSi, gMuMu_deriv σ hσ]; field_simp

/-- **[The connection field, Gassner-Cafaro Eq. 12] `Γ^σ_{σσ} = −1/σ`.** -/
lemma christoffel_Si_SiSi_eq (σ : ℝ) (hσ : σ ≠ 0) : christoffel_Si_SiSi σ = -1 / σ := by
  rw [christoffel_Si_SiSi, gInvSiSi, gSiSi_deriv σ hσ]; field_simp; ring

/-! ## C. Curvature of the connection (curved statistical spacetime) -/

/-- **The Riemann curvature tensor of the Fisher-Rao Gaussian manifold** is the constant-curvature
form with sectional curvature `K = −1/2` (Gassner-Cafaro Eq. 20): `R_{abcd} = K(g_{ac}g_{bd} −
g_{ad}g_{bc})`. -/
noncomputable def frRiemann (σ : ℝ) : RiemannTensor (Fin 2) :=
  constantCurvature (-1 / 2) (frMetric σ)

/-- **[The Fisher-Rao Riemann tensor obeys the Levi-Civita curvature symmetries].** -/
lemma frRiemann_isRiemann (σ : ℝ) : IsRiemannCurvature (frRiemann σ) :=
  isRiemannCurvature_constantCurvature (-1 / 2) (frMetric σ) (frMetric_symm σ)

/-- **[The Fisher-Rao manifold is an Einstein manifold] `R_{bd} = −½ g_{bd}`** (Gassner-Cafaro Eq. 16):
the Ricci tensor of the constant-curvature manifold is proportional to the metric, with the diagonal
`R_μμ = −1/(2σ²)`, `R_σσ = −1/σ²`. -/
lemma frRicci_eq (σ : ℝ) (hσ : σ ≠ 0) :
    ricci (frMetricInv σ) (frRiemann σ) = (-1 / 2 : ℝ) • frMetric σ := by
  ext b d
  fin_cases b <;> fin_cases d <;>
    simp [ricci, frRiemann, constantCurvature, frMetric, frMetricInv, gMuMu, gSiSi, gInvMuMu,
      gInvSiSi, Fin.sum_univ_two, Matrix.smul_apply] <;> field_simp

/-- **[The scalar curvature, Gassner-Cafaro Eq. 18] `R = −1`** — the metric trace of the Ricci tensor,
`R = g^{bd} R_{bd} = 2K`, the constant negative scalar curvature of the Gaussian statistical
manifold. -/
theorem frScalarCurvature (σ : ℝ) (hσ : σ ≠ 0) :
    scalarCurvature (frMetricInv σ) (frRiemann σ) = -1 := by
  rw [scalarCurvature, ricciScalarContraction, frRicci_eq σ hσ, mul_smul_comm,
    frMetricInv_mul_metric σ hσ, Matrix.trace_smul, Matrix.trace_one]
  norm_num

/-! ## D. Maximal symmetry (the entropic-motion manifold is hyperbolic) -/

/-- **[The Gaussian statistical manifold is maximally symmetric].** Its Riemann tensor is the
constant-curvature form of sectional curvature `K = −1/2` (isotropic and homogeneous), and its scalar
curvature is the two-dimensional value `R = 2K = −1`. Constant *negative* curvature makes the manifold
hyperbolic — the geometry underlying the exponential geodesic spread of Caticha's entropic motion. -/
theorem frMaximallySymmetric (σ : ℝ) (hσ : σ ≠ 0) :
    frRiemann σ = constantCurvature (-1 / 2) (frMetric σ)
    ∧ ricci (frMetricInv σ) (frRiemann σ) = (-1 / 2 : ℝ) • frMetric σ
    ∧ scalarCurvature (frMetricInv σ) (frRiemann σ) = 2 * (-1 / 2) := by
  refine ⟨rfl, frRicci_eq σ hσ, ?_⟩
  rw [frScalarCurvature σ hσ]; norm_num

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frRicci_eq where
  formalizes @ "claim:the-fisher-rao-gaussian-ricci-tensor-is-computed-from-the-levi-civita-connection-of-the-fisher-metric",
  supported_by @ "paper:amari-nagaoka-methods-of-information-geometry"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frScalarCurvature where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frRicci_eq",
  formalizes @ "claim:the-fisher-rao-gaussian-statistical-manifold-has-constant-negative-scalar-curvature-it-is-hyperbolic",
  requires @ "claim:the-fisher-rao-gaussian-ricci-tensor-is-computed-from-the-levi-civita-connection-of-the-fisher-metric",
  caveat @ "claim:the-mean-variance-gaussian-family-only-a-two-dimensional-hyperbolic-slice-of-information-geometry"

zil_file_contract physlib.fisherRaoGaussianLeviCivita where
  promises "The Fisher-Rao geometry of the Gaussian family: the Levi-Civita connection of the Fisher information metric gives a Ricci tensor and a constant negative scalar curvature, so the mean-variance statistical manifold is hyperbolic."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.christoffel_Mu_MuSi"]
  forbids_substitutes ["the full information-geometry of an arbitrary exponential family, only the two-dimensional Gaussian slice",
    "the alpha-connection dually-flat structure, only the metric Levi-Civita curvature"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frRicci_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.frScalarCurvature]

/- ZIL-END -/
