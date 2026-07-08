/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
# The entropic connection and the covariant Hessian: a concrete imaginary curvature

Supplies the **Christoffel-dependent** gravity structures of complex-action/entropic-time (Paper 2+4 §"Relation to Classical
Spacetime"), turning the imaginary curvature `Λ_μν` of `ComplexEinstein.FieldEquations` from a free
parameter into the **concrete covariant Hessian** `Λ_μν = ∇_μ∇_νφ`.

Working in a coordinate chart, the Christoffel symbols are represented as `Γ : ι → Matrix ι ι ℝ` with
`(Γ l) μ ν = Γ^l_{μν}` (upper index `l`, lower pair `μν`); the Levi-Civita / torsion-free condition is
`(Γ l)ᵀ = Γ l` (`IsTorsionFree`).

* **the covariant Hessian** `∇_μ∇_νφ = ∂_μ∂_νφ − Γ^λ_{μν} ∂_λφ` (`covariantHessian`), the concrete
  imaginary curvature, **symmetric** when the partial Hessian is symmetric and `Γ` is torsion-free
  (`covariantHessian_symm`); instantiating it as the `Λ` of the complex Einstein equation gives the
  imaginary field equation `∇_μ∇_νφ = κ S_μν` (`covariantHessian_complexEinstein`);
* **the entropic connection** `Γ̃^λ_{μν} = Γ^λ_{μν} + C^λ_{μν}[φ]` (`entropicConnection`, eq G3), staying
  torsion-free when the correction is symmetric (`entropicConnection_torsionFree`);
* **entropic non-metricity** `∇_λ g_μν = −2∇_λφ g_μν` (`IsEntropicNonMetricity`, eq G4), whose
  equilibrium limit `∇φ = 0` is exactly metric compatibility `∇_λ g = 0`
  (`entropicNonMetricity_equilibrium`);
* **the complex covariant derivative** `∇̃_μΨ = ∇_μΨ + i ∂_μφ Ψ` (`complexCovariantDeriv`, eq G5),
  reducing to the ordinary derivative at equilibrium (`complexCovariantDeriv_equilibrium`); the
  imaginary connection `A_μ = ∂_μφ` is an **exact** one-form, so its field strength
  `∂_μ A_ν − ∂_ν A_μ` vanishes — the imaginary connection is flat and the geometric phase is integrable
  (`imaginaryConnection_flat`).

* **§A — the covariant Hessian as the imaginary curvature** (`IsTorsionFree`, `covariantHessian`,
  `covariantHessian_symm`, `covariantHessian_complexEinstein`).
* **§B — the entropic connection** (`entropicConnection`, `entropicConnection_torsionFree`).
* **§C — entropic non-metricity** (`metricCovariantDeriv`, `IsMetricCompatible`,
  `IsEntropicNonMetricity`, `entropicNonMetricity_equilibrium`).
* **§D — the complex covariant derivative and the flat imaginary connection**
  (`complexCovariantDeriv`, `complexCovariantDeriv_equilibrium`, `imaginaryConnectionCurvature`,
  `imaginaryConnection_flat`, `imaginaryConnectionCurvature_eq_zero_iff`).

## References

* complex-action/entropic-time complex action / entropic geometry (Paper 2+4); standard Levi-Civita connection and the
  covariant Hessian of a scalar. Repo dependencies: `ComplexEinstein.FieldEquations`
  (`complexEinsteinFieldEquation`, `einsteinTensor`, `einsteinFieldEquation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

variable {ι : Type*}

/-! ## §A — the covariant Hessian as the concrete imaginary curvature -/

/-- **The torsion-free (Levi-Civita) condition** `Γ^λ_{μν} = Γ^λ_{νμ}` — each upper-index Christoffel
matrix is symmetric in its lower pair. -/
def IsTorsionFree (Γ : ι → Matrix ι ι ℝ) : Prop := ∀ l, (Γ l)ᵀ = Γ l

/-- **The covariant Hessian of a scalar** `∇_μ∇_νφ = ∂_μ∂_νφ − Γ^λ_{μν} ∂_λφ` — the concrete imaginary
curvature `Λ_μν`, built from the partial Hessian `H_μν = ∂_μ∂_νφ`, the Christoffel symbols `Γ`, and the
gradient covector `∂_λφ = dφ λ`. -/
def covariantHessian [Fintype ι] (Γ : ι → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (dφ : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun μ ν => H μ ν - ∑ l, (Γ l) μ ν * dφ l

/-- **[The covariant Hessian is symmetric] `∇_μ∇_νφ = ∇_ν∇_μφ`.** When the partial Hessian is symmetric
(`∂_μ∂_νφ = ∂_ν∂_μφ`, Schwarz) and the connection is torsion-free, the covariant Hessian — hence the
imaginary curvature `Λ_μν` — is symmetric. -/
theorem covariantHessian_symm [Fintype ι] (Γ : ι → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (dφ : ι → ℝ)
    (hH : Hᵀ = H) (hΓ : IsTorsionFree Γ) :
    (covariantHessian Γ H dφ)ᵀ = covariantHessian Γ H dφ := by
  ext μ ν
  simp only [Matrix.transpose_apply, covariantHessian]
  rw [show H ν μ = H μ ν from congrFun (congrFun hH μ) ν]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by
    rw [show (Γ l) ν μ = (Γ l) μ ν from congrFun (congrFun (hΓ l) μ) ν]

/-- **[The concrete imaginary Einstein equation] `∇_μ∇_νφ = κ S_μν`.** With the imaginary curvature `Λ`
instantiated as the covariant Hessian `∇_μ∇_νφ` (`covariantHessian`), it is symmetric, and the complex
Einstein field equation splits into the standard Einstein equation `G = κT` and the **concrete** imaginary
equation `∇_μ∇_νφ = κ S_μν` — the entropic stress sources the second covariant derivative of the entropic
potential. -/
theorem covariantHessian_complexEinstein [Fintype ι] (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g : Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (dφ : ι → ℝ) (T S : Matrix ι ι ℝ)
    (κ : ℝ)
    (hH : Hᵀ = H) (hΓ : IsTorsionFree Γ) :
    (covariantHessian Γ H dφ)ᵀ = covariantHessian Γ H dφ
      ∧ (complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) (covariantHessian Γ H dφ) T S κ
          ↔ einsteinFieldEquation Ric scalarR g T κ ∧ covariantHessian Γ H dφ = κ • S) :=
  ⟨covariantHessian_symm Γ H dφ hH hΓ,
    complexEinsteinFieldEquation_iff_einstein Ric scalarR g (covariantHessian Γ H dφ) T S κ⟩

/-! ## §B — the entropic connection `Γ̃ = Γ + C` (eq G3) -/

/-- **The entropic connection** `Γ̃^λ_{μν} = Γ^λ_{μν} + C^λ_{μν}[φ]` — the Levi-Civita connection modified
by the entropic correction `C` (the information-flow contribution to parallel transport). -/
def entropicConnection (Γ C : ι → Matrix ι ι ℝ) : ι → Matrix ι ι ℝ := fun l => Γ l + C l

/-- **[The entropic connection stays torsion-free]** when the correction `C` is symmetric in its lower
pair: `Γ̃^λ_{μν} = Γ̃^λ_{νμ}`. -/
theorem entropicConnection_torsionFree (Γ C : ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ) (hC : IsTorsionFree C) : IsTorsionFree (entropicConnection Γ C) := by
  intro l
  simp only [entropicConnection, Matrix.transpose_add, hΓ l, hC l]

/-! ## §C — entropic non-metricity `∇_λ g_μν = −2∇_λφ g_μν` (eq G4) -/

/-- **The metric covariant derivative** `∇_λ g_μν = ∂_λ g_μν − Γ^σ_{λμ} g_σν − Γ^σ_{λν} g_μσ` (with
`∂_λ g = dg λ`). -/
def metricCovariantDeriv [Fintype ι] (Γ dg : ι → Matrix ι ι ℝ) (g : Matrix ι ι ℝ) :
    ι → Matrix ι ι ℝ :=
  fun l => fun μ ν => dg l μ ν - (∑ σ, (Γ σ) l μ * g σ ν) - (∑ σ, (Γ σ) l ν * g μ σ)

/-- **Metric compatibility** `∇_λ g_μν = 0` — the standard Levi-Civita condition (lengths preserved under
parallel transport). -/
def IsMetricCompatible [Fintype ι] (Γ dg : ι → Matrix ι ι ℝ) (g : Matrix ι ι ℝ) : Prop :=
  ∀ l, metricCovariantDeriv Γ dg g l = 0

/-- **Entropic non-metricity** `∇_λ g_μν = −2∇_λφ g_μν` (eq G4) — information flow rescales vector lengths
during parallel transport, proportional to the entropic gradient `∇_λφ = dφ λ`. -/
def IsEntropicNonMetricity [Fintype ι] (Γ dg : ι → Matrix ι ι ℝ) (g : Matrix ι ι ℝ) (dφ : ι → ℝ) :
    Prop :=
  ∀ l, metricCovariantDeriv Γ dg g l = (-2 * dφ l) • g

/-- **[Equilibrium is metric compatibility] `∇φ = 0 ⟹ ∇_λ g = 0`.** Entropic non-metricity with
vanishing entropic gradient is exactly the standard Levi-Civita metric compatibility — at equilibrium the
entropic geometry is metric. -/
theorem entropicNonMetricity_equilibrium [Fintype ι] (Γ dg : ι → Matrix ι ι ℝ) (g : Matrix ι ι ℝ) :
    IsEntropicNonMetricity Γ dg g 0 ↔ IsMetricCompatible Γ dg g := by
  unfold IsEntropicNonMetricity IsMetricCompatible
  constructor
  · intro h l; have hl := h l; simpa using hl
  · intro h l; have hl := h l; simpa using hl

/-! ## §D — the complex covariant derivative and the flat imaginary connection (eq G5) -/

/-- **The complex covariant derivative** `∇̃_μΨ = ∇_μΨ + i ∂_μφ Ψ` (eq G5) — the covariant derivative on
quantum fields acquires an imaginary entropic term (directional information leak as geometric phase). Here
`DΨ μ = ∇_μΨ` is the ordinary covariant derivative covector and `Ψ` the field value. -/
def complexCovariantDeriv (DΨ : ι → ℂ) (dφ : ι → ℝ) (Ψ : ℂ) : ι → ℂ :=
  fun μ => DΨ μ + Complex.I * (dφ μ : ℂ) * Ψ

/-- **[Equilibrium] `∇̃_μΨ = ∇_μΨ` at `∇φ = 0`.** With vanishing entropic gradient the complex covariant
derivative reduces to the ordinary one — no geometric phase. -/
theorem complexCovariantDeriv_equilibrium (DΨ : ι → ℂ) (Ψ : ℂ) :
    complexCovariantDeriv DΨ 0 Ψ = DΨ := by
  funext μ
  simp [complexCovariantDeriv]

/-- **The imaginary connection field strength** `F_μν = ∂_μ A_ν − ∂_ν A_μ` of the imaginary connection
`A_μ = ∂_μφ`, with `H_μν = ∂_μ A_ν = ∂_μ∂_νφ` the partial Hessian: `F = H − Hᵀ`. -/
def imaginaryConnectionCurvature (H : Matrix ι ι ℝ) : Matrix ι ι ℝ := H - Hᵀ

/-- **[The imaginary connection is flat] `F = 0`.** Because the imaginary connection `A_μ = ∂_μφ` is an
**exact** one-form (a gradient), its field strength `∂_μ∂_νφ − ∂_ν∂_μφ` vanishes (Schwarz: the partial
Hessian is symmetric) — the entropic geometric phase is integrable, with no genuine imaginary curvature. -/
theorem imaginaryConnection_flat (H : Matrix ι ι ℝ) (hH : Hᵀ = H) :
    imaginaryConnectionCurvature H = 0 := by
  rw [imaginaryConnectionCurvature, hH, sub_self]

/-- **[Flat ⟺ symmetric Hessian]** `F = 0 ⟺ ∂_μ∂_νφ = ∂_ν∂_μφ`. -/
theorem imaginaryConnectionCurvature_eq_zero_iff (H : Matrix ι ι ℝ) :
    imaginaryConnectionCurvature H = 0 ↔ Hᵀ = H := by
  rw [imaginaryConnectionCurvature, sub_eq_zero]
  exact eq_comm

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

end
