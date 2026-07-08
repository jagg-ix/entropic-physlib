/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-!
# The complex Einstein field equations and the entropic stress tensor

Builds the **complex (complex-action/entropic-time) Einstein field equations** on top of the real Einstein field equation of
`ComplexEinstein.EinsteinFieldEquationsPhysLean`. The real sector is standard GR; the imaginary sector includes the
entropy-production geometry.

* the **entropic stress tensor** `S_μν = −∇_μφ ∇_νφ + ½ g_μν (∇φ)²` (`entropicStressTensor`), the
  variation of the imaginary action `S_I` with respect to the metric — symmetric
  (`entropicStressTensor_symm`), vanishing at equilibrium `∇φ = 0` (`entropicStressTensor_equilibrium`);
* the **complex Einstein tensor** `𝒢_μν = G_μν + i Λ_μν` (`complexEinsteinTensor`), with `Λ_μν` the
  imaginary curvature from `∇_μ∇_νφ`; its real/imaginary parts recover `G` and `Λ`
  (`complexEinsteinTensor_map_re`, `complexEinsteinTensor_map_im`);
* the **complex Einstein field equation** `𝒢_μν = κ(T_μν + i S_μν)` (`complexEinsteinFieldEquation`,
  `κ = 8πG/c⁴`), which holds **iff** both the real Einstein equation `G = κT` *and* the imaginary
  equation `Λ = κS` hold (`complexEinsteinFieldEquation_iff`); the real conjunct is *exactly* the
  `einsteinFieldEquation` of the existing bridge (`complexEinsteinFieldEquation_iff_einstein`);
* the **complex Bianchi identity** `∇^μ𝒢_μν = 0` splits into the standard Bianchi `∇^μG_μν = 0` and the
  entropic Bianchi `∇^μΛ_μν = 0` (`complexBianchi_iff`), forcing both real stress-energy conservation
  `∇^μT_μν = 0` *and* entropic stress conservation `∇^μS_μν = 0` (`complexEinstein_conservation`, the
  real sector via the existing `bianchi_implies_conservation`);
* the **equilibrium correspondence / Jacobson limit**: when the entropic sector vanishes (`Λ = 0`,
  `S = 0` at `∇φ = 0`), the complex equations reduce *exactly* to standard GR `G = κT`
  (`complexEinstein_equilibrium_reduces`) — complex-action/entropic-time is a true extension of GR, not a replacement.

* **§A — the entropic stress tensor** (`entropicStressTensor`, `entropicStressTensor_symm`,
  `entropicStressTensor_equilibrium`).
* **§B — the complex Einstein tensor and field equation** (`complexCombine`, `complexEinsteinTensor`,
  `complexStressEnergy`, `complexEinsteinFieldEquation`, `complexEinsteinFieldEquation_iff`,
  `complexEinsteinFieldEquation_iff_einstein`).
* **§C — the complex Bianchi split and conservation** (`complexDiv`, `complexBianchi_iff`,
  `complexEinstein_conservation`).
* **§D — equilibrium correspondence and the assembly** (`complexEinstein_equilibrium_reduces`,
  `complexEinsteinFieldEquations`).

## References

* complex-action/entropic-time complex action and complex Einstein equations (Paper 2+4); C. W. Misner, K. S. Thorne,
  J. A. Wheeler, *Gravitation*; T. Jacobson (equilibrium thermodynamic derivation). Repo dependencies:
  `ComplexEinstein.EinsteinFieldEquationsPhysLean` (`einsteinTensor`, `einsteinFieldEquation`,
  `bianchi_implies_conservation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

variable {ι : Type*}

/-! ## §A — the entropic stress tensor `S_μν = −∇_μφ∇_νφ + ½g_μν(∇φ)²` -/

/-- **The gradient outer product** `(∇φ ⊗ ∇φ)_μν = ∇_μφ ∇_νφ` — the rank-one tensor from the entropic
gradient covector `∇φ`. -/
def gradOuter (dφ : ι → ℝ) : Matrix ι ι ℝ := fun μ ν => dφ μ * dφ ν

/-- **The gradient outer product is symmetric** `(∇φ⊗∇φ)ᵀ = ∇φ⊗∇φ`. -/
theorem gradOuter_symm (dφ : ι → ℝ) : (gradOuter dφ)ᵀ = gradOuter dφ := by
  ext μ ν; simp [gradOuter, Matrix.transpose_apply, mul_comm]

/-- **The entropic stress tensor** `S_μν = −∇_μφ ∇_νφ + ½ g_μν (∇φ)²` — the variation of the imaginary
action `S_I` with respect to the metric (`gradSq = (∇φ)²` the squared gradient norm). It has the same
structure as a massless scalar field, with purely imaginary coupling. -/
noncomputable def entropicStressTensor (dφ : ι → ℝ) (gradSq : ℝ) (g : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  -gradOuter dφ + (gradSq / 2) • g

/-- **The entropic stress tensor is symmetric** `S_μν = S_νμ` (when `g` is). -/
theorem entropicStressTensor_symm (dφ : ι → ℝ) (gradSq : ℝ) (g : Matrix ι ι ℝ) (hg : gᵀ = g) :
    (entropicStressTensor dφ gradSq g)ᵀ = entropicStressTensor dφ gradSq g := by
  rw [entropicStressTensor, transpose_add, transpose_neg, gradOuter_symm, transpose_smul, hg]

/-- **[Equilibrium] `S_μν = 0` at `∇φ = 0`.** With vanishing entropic gradient (`∇φ = 0`, hence
`(∇φ)² = 0`) the entropic stress tensor vanishes — the spatially-uniform entropy-production limit. -/
theorem entropicStressTensor_equilibrium (g : Matrix ι ι ℝ) :
    entropicStressTensor 0 0 g = 0 := by
  ext μ ν; simp [entropicStressTensor, gradOuter]

/-! ## §B — the complex Einstein tensor and field equation -/

/-- **The complexification** `A + i B` of a pair of real tensors, entrywise. -/
def complexCombine (A B : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun μ ν => (A μ ν : ℂ) + Complex.I * (B μ ν : ℂ)

theorem complexCombine_apply (A B : Matrix ι ι ℝ) (μ ν : ι) :
    complexCombine A B μ ν = (A μ ν : ℂ) + Complex.I * (B μ ν : ℂ) := rfl

theorem complexCombine_map_re (A B : Matrix ι ι ℝ) : (complexCombine A B).map Complex.re = A := by
  ext μ ν
  simp [complexCombine, Matrix.map_apply]

theorem complexCombine_map_im (A B : Matrix ι ι ℝ) : (complexCombine A B).map Complex.im = B := by
  ext μ ν
  simp [complexCombine, Matrix.map_apply]

/-- **[The complexification splits] `A + iB = C + iD ⟺ A = C ∧ B = D`.** Equality of complex tensors is
equality of real and imaginary sectors. -/
theorem complexCombine_eq_iff (A B C D : Matrix ι ι ℝ) :
    complexCombine A B = complexCombine C D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext μ ν
      have hμν := congrFun (congrFun h μ) ν
      rw [complexCombine_apply, complexCombine_apply] at hμν
      simpa using congrArg Complex.re hμν
    · ext μ ν
      have hμν := congrFun (congrFun h μ) ν
      rw [complexCombine_apply, complexCombine_apply] at hμν
      simpa using congrArg Complex.im hμν
  · rintro ⟨rfl, rfl⟩; rfl

theorem smul_complexCombine (κ : ℝ) (A B : Matrix ι ι ℝ) :
    κ • complexCombine A B = complexCombine (κ • A) (κ • B) := by
  ext μ ν
  simp only [Matrix.smul_apply, complexCombine_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul]
  ring

/-- **The complex Einstein tensor** `𝒢_μν = G_μν + i Λ_μν` — the standard Einstein tensor `G` plus the
imaginary curvature `Λ` (from `∇_μ∇_νφ`). -/
def complexEinsteinTensor (G Λ : Matrix ι ι ℝ) : Matrix ι ι ℂ := complexCombine G Λ

/-- **The complex stress-energy** `T_μν + i S_μν` — ordinary matter stress-energy `T` plus the entropic
stress tensor `S`. -/
def complexStressEnergy (T S : Matrix ι ι ℝ) : Matrix ι ι ℂ := complexCombine T S

/-- **[Real part] `Re 𝒢 = G`.** -/
theorem complexEinsteinTensor_map_re (G Λ : Matrix ι ι ℝ) :
    (complexEinsteinTensor G Λ).map Complex.re = G := complexCombine_map_re G Λ

/-- **[Imaginary part] `Im 𝒢 = Λ`.** -/
theorem complexEinsteinTensor_map_im (G Λ : Matrix ι ι ℝ) :
    (complexEinsteinTensor G Λ).map Complex.im = Λ := complexCombine_map_im G Λ

/-- **The complex Einstein field equation** `𝒢_μν = κ(T_μν + i S_μν)` — `G + iΛ = κ(T + iS)`,
`κ = 8πG/c⁴`. The real sector is standard GR; the imaginary sector couples the imaginary curvature to the
entropic stress. -/
def complexEinsteinFieldEquation (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) : Prop :=
  complexEinsteinTensor G Λ = κ • complexStressEnergy T S

/-- **[The complex Einstein equation splits] `𝒢 = κ(T+iS) ⟺ (G = κT) ∧ (Λ = κS)`.** The complex field
equation is *exactly* the pair of the real Einstein equation `G = κT` and the imaginary equation
`Λ = κS` (entropic curvature sourced by entropic stress). -/
theorem complexEinsteinFieldEquation_iff (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) :
    complexEinsteinFieldEquation G Λ T S κ ↔ G = κ • T ∧ Λ = κ • S := by
  unfold complexEinsteinFieldEquation complexEinsteinTensor complexStressEnergy
  rw [smul_complexCombine, complexCombine_eq_iff]

/-- **[The real sector is the standard Einstein field equation].** With `G = einsteinTensor`, the complex
Einstein equation holds iff the *existing* `einsteinFieldEquation` (the bridge's `G = κT`) holds together
with the imaginary equation `Λ = κS`. The real part of the complex-action/entropic-time field equation is exactly GR. -/
theorem complexEinsteinFieldEquation_iff_einstein (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ : ℝ) :
    complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ
      ↔ einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S := by
  rw [complexEinsteinFieldEquation_iff, einsteinFieldEquation]

/-! ## §C — the complex Bianchi split and conservation -/

/-- **The complex divergence** `∇^μ M_μν = (∇^μ Re M) + i(∇^μ Im M)` — a real divergence operator `Div`
lifted to complex tensors entrywise on the real and imaginary parts. -/
noncomputable def complexDiv (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (M : Matrix ι ι ℂ) : ι → ℂ :=
  fun ν => (Div (M.map Complex.re) ν : ℂ) + Complex.I * (Div (M.map Complex.im) ν : ℂ)

theorem complexDiv_complexEinsteinTensor (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (G Λ : Matrix ι ι ℝ) :
    complexDiv Div (complexEinsteinTensor G Λ)
      = fun ν => (Div G ν : ℂ) + Complex.I * (Div Λ ν : ℂ) := by
  unfold complexDiv
  rw [complexEinsteinTensor_map_re, complexEinsteinTensor_map_im]

/-- **[The complex Bianchi identity splits] `∇^μ𝒢_μν = 0 ⟺ ∇^μG_μν = 0 ∧ ∇^μΛ_μν = 0`.** The
divergence-free complex Einstein tensor is exactly the standard Bianchi identity `∇^μG = 0` together with
the entropic Bianchi identity `∇^μΛ = 0`. -/
theorem complexBianchi_iff (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ)) (G Λ : Matrix ι ι ℝ) :
    complexDiv Div (complexEinsteinTensor G Λ) = 0 ↔ Div G = 0 ∧ Div Λ = 0 := by
  rw [complexDiv_complexEinsteinTensor]
  constructor
  · intro h
    refine ⟨funext fun ν => ?_, funext fun ν => ?_⟩
    · have hν := congrFun h ν
      simpa using congrArg Complex.re hν
    · have hν := congrFun h ν
      simpa using congrArg Complex.im hν
  · rintro ⟨hG, hΛ⟩
    funext ν
    have hGν : Div G ν = 0 := congrFun hG ν
    have hΛν : Div Λ ν = 0 := congrFun hΛ ν
    simp [hGν, hΛν]

/-- **[Complex Bianchi ⟹ real and entropic conservation] `∇^μT_μν = 0 ∧ ∇^μS_μν = 0`.** Given the complex
Einstein field equation and the complex Bianchi identity `∇^μ𝒢_μν = 0` (with `κ ≠ 0`), both the ordinary
stress-energy and the entropic stress tensor are conserved. The real conservation reuses the bridge's
`bianchi_implies_conservation`; the entropic conservation follows from `Λ = κS` and `∇^μΛ = 0`. -/
theorem complexEinstein_conservation (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T S Λ : Matrix ι ι ℝ) (κ : ℝ)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ)
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0)
    (hκ : κ ≠ 0) :
    Div T = 0 ∧ Div S = 0 := by
  obtain ⟨hReal, hImag⟩ := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp hEFE
  obtain ⟨hBG, hBΛ⟩ := (complexBianchi_iff Div (einsteinTensor Ric scalarR g) Λ).mp hBianchi
  refine ⟨bianchi_implies_conservation Div Ric scalarR g T κ hReal hBG hκ, ?_⟩
  rw [hImag, map_smul] at hBΛ
  exact (smul_eq_zero.mp hBΛ).resolve_left hκ

/-! ## §D — equilibrium correspondence and the assembly -/

/-- **[Equilibrium correspondence / Jacobson limit] complex Einstein ⟶ standard GR.** When the entropic
sector vanishes (`Λ = 0` and `S = entropicStressTensor 0 0 g = 0` at `∇φ = 0`), the complex Einstein
field equation reduces *exactly* to the standard Einstein field equation `G = κT`
(`einsteinFieldEquation`). complex-action/entropic-time is a true extension of GR: at equilibrium it *is* GR. -/
theorem complexEinstein_equilibrium_reduces (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) :
    complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) 0 T (entropicStressTensor 0 0 g) κ
      ↔ einsteinFieldEquation Ric scalarR g T κ := by
  rw [entropicStressTensor_equilibrium, complexEinsteinFieldEquation_iff_einstein,
    smul_zero, and_iff_left rfl]

/-- **[The complex Einstein field equations, assembled].** With the entropic stress tensor `S` sourcing
the imaginary curvature `Λ`: the complex equation `𝒢 = κ(T+iS)` splits into the standard Einstein
equation `G = κT` and the imaginary equation `Λ = κS`; the complex Bianchi identity splits into the
standard and entropic Bianchi identities and forces both `∇^μT = 0` and `∇^μS = 0`; and at equilibrium
(`Λ = 0`, `S = 0`) the system reduces to standard GR. The real sector is GR; the imaginary sector is the
entropy-production geometry. -/
theorem complexEinsteinFieldEquations (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T S Λ : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ)
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0) :
    (einsteinFieldEquation Ric scalarR g T κ ∧ Λ = κ • S)
      ∧ (Div (einsteinTensor Ric scalarR g) = 0 ∧ Div Λ = 0)
      ∧ (Div T = 0 ∧ Div S = 0)
      ∧ (complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) 0 T (entropicStressTensor 0 0 g) κ
          ↔ einsteinFieldEquation Ric scalarR g T κ) :=
  ⟨(complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp hEFE,
    (complexBianchi_iff Div (einsteinTensor Ric scalarR g) Λ).mp hBianchi,
    complexEinstein_conservation Div Ric scalarR g T S Λ κ hEFE hBianchi hκ,
    complexEinstein_equilibrium_reduces Ric scalarR g T κ⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

end
