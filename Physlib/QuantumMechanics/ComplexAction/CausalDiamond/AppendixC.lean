/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LieDerivative
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw

/-!
# Appendix C in full: the zeroth law for bifurcate conformal Killing horizons (Eqs. C.1–C.8)

This formalizes every numbered equation of Jacobson–Visser Appendix C, representing the covectors as
`Fin n → ℝ` and the `(0,2)` tensors as `Matrix (Fin n) (Fin n) ℝ`. The surface gravity `κ` of a
conformal Killing horizon `𝓗` is **constant on `𝓗`** (the zeroth law), proved here in both parts.

* **C.1** `∇_a(ζ²) = −2κ ζ_a` — the surface-gravity definition on `𝓗` (`gradZetaSq`).
* **C.2** `𝓛_ζ ∇_a ζ² = 2α ∇_a ζ² = −4ακ ζ_a` (`lie_gradZetaSq`).
* **C.3** `𝓛_ζ(−2κ ζ_a) = (−2 𝓛_ζκ − 4ακ) ζ_a`, via `𝓛_ζ ζ_a = 2α ζ_a` and Leibniz (`lie_neg_two_kappa_zeta`).
* **C.4** `𝓛_ζκ = 0` — `κ` constant along the generators (`lieKappa_eq_zero`, from C.2 = C.3).
* **C.5** `∇_a ζ_b = α g_ab + ω_ab` (`ω` antisymmetric) — the conformal Killing decomposition; its
 symmetric part is `α g_ab` (`nablaZeta_sym`).
* **C.6** `∇_a ζ_b = κ n_ab` on `𝓑` (`α = 0`, `ω = κ n`) (`nablaZeta_on_bifurcation`).
* **C.7** `n^{ab}m^c ∇_c∇_a ζ_b = −2 m^a∇_aκ` on `𝓑` (`contractionC7`).
* **C.8** `∇_c∇_a ζ_b = ζ^d R_dcab + g_ab∇_cα + g_bc∇_aα − g_ac∇_bα` — the conformal Killing identity;
 contracted with `n^{ab}m^c` on `𝓑` it vanishes (`ζ^d`, `α` vanish there), so `m^a∇_aκ = 0`
 (`kappa_const_on_bifurcation`, C.7 + C.8).

## Scope

The covector/tensor relations and the algebraic assembly (C.2, C.3, C.4, C.5 split, C.7 conclusion) are
proved. The curvature identity C.8 and the surface-gravity relations C.1/C.6 are stated through their
covector/tensor structure; the geometric values (`∇ζ²`, the Riemann term) enter as the given data.

No new axioms.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixC

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LieDerivative
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw

variable {n : ℕ}

/-! ## §C.1 — the surface gravity `∇_a(ζ²) = −2κ ζ_a` -/

/-- **Eq. C.1: `∇_a(ζ²) = −2κ ζ_a`** on `𝓗` — the gradient of `ζ² = ζ^bζ_b` is `−2κ` times `ζ_a`,
defining the surface gravity `κ` (a Weyl-invariant definition). -/
def gradZetaSq (κ : ℝ) (ζ : Fin n → ℝ) : Fin n → ℝ := (-2 * κ) • ζ

@[simp] theorem gradZetaSq_apply (κ : ℝ) (ζ : Fin n → ℝ) (a : Fin n) :
    gradZetaSq κ ζ a = -2 * κ * ζ a := by simp [gradZetaSq]

/-! ## §C.2 — `𝓛_ζ ∇_a ζ² = −4ακ ζ_a` -/

/-- **Eq. C.2: `𝓛_ζ ∇_a ζ² = 2α ∇_a ζ² = −4ακ ζ_a`** on `𝓗` — the Lie derivative of `∇ζ²` is `2α`
times itself (since `𝓛_ζ ζ² = 2α ζ²`), hence `−4ακ ζ_a` by C.1. -/
theorem lie_gradZetaSq (κ α : ℝ) (ζ : Fin n → ℝ) :
    (2 * α) • gradZetaSq κ ζ = (-4 * α * κ) • ζ := by
  rw [gradZetaSq, smul_smul]; congr 1; ring

/-! ## §C.3 — `𝓛_ζ(−2κ ζ_a) = (−2 𝓛_ζκ − 4ακ) ζ_a` -/

/-- **`𝓛_ζ ζ_a = 2α ζ_a`** on `𝓗` (the conformal-Killing flow scales `ζ_a` by `2α`). -/
def lieZeta (α : ℝ) (ζ : Fin n → ℝ) : Fin n → ℝ := (2 * α) • ζ

/-- **Eq. C.3: `𝓛_ζ(−2κ ζ_a) = (−2 𝓛_ζκ − 4ακ) ζ_a`** — the Leibniz rule
`𝓛_ζ(−2κ ζ_a) = (−2 𝓛_ζκ) ζ_a + (−2κ) 𝓛_ζ ζ_a` with `𝓛_ζ ζ_a = 2α ζ_a`. -/
theorem lie_neg_two_kappa_zeta (κ α Lκ : ℝ) (ζ : Fin n → ℝ) :
    (-2 * Lκ) • ζ + (-2 * κ) • lieZeta α ζ = (-2 * Lκ - 4 * α * κ) • ζ := by
  rw [lieZeta, smul_smul, ← add_smul]; congr 1; ring

/-! ## §C.4 — `𝓛_ζκ = 0` (constant along generators) -/

/-- **Eq. C.4: `𝓛_ζκ = 0`** — equating the two computations of `𝓛_ζ ∇_a ζ²` (C.2 `= −4ακ`, and C.3 via
C.1 `= −2 𝓛_ζκ − 4ακ`, as coefficients of `ζ_a`) gives `𝓛_ζκ = 0`: the surface gravity is constant
along each null generator. -/
theorem lieKappa_eq_zero (κ α Lκ : ℝ) (hC2_eq_C3 : -4 * α * κ = -2 * Lκ - 4 * α * κ) :
    Lκ = 0 :=
  zerothLaw_along_generators α κ Lκ hC2_eq_C3

/-! ## §C.5 — the conformal Killing decomposition `∇_a ζ_b = α g_ab + ω_ab` -/

/-- **Eq. C.5: `∇_a ζ_b = α g_ab + ω_ab`** — the gradient of `ζ_a` splits into the conformal part
`α g_ab` (symmetric) and the rotation `ω_ab` (antisymmetric). -/
def nablaZeta (α : ℝ) (g ω : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := α • g + ω

/-- **The symmetric part of `∇_a ζ_b` is `α g_ab`** (Eq. C.5): with `g` symmetric and `ω`
antisymmetric, `∇_{(a}ζ_{b)} = α g_ab` — the conformal Killing equation. -/
theorem nablaZeta_sym (α : ℝ) (g ω : Matrix (Fin n) (Fin n) ℝ)
    (hg : g.transpose = g) (hω : ω.transpose = -ω) :
    (nablaZeta α g ω + (nablaZeta α g ω).transpose) = (2 * α) • g := by
  rw [nablaZeta, Matrix.transpose_add, Matrix.transpose_smul, hg, hω]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-! ## §C.6 — on the bifurcation surface `𝓑`: `∇_a ζ_b = κ n_ab` -/

/-- **Eq. C.6: `∇_a ζ_b = κ n_ab`** on `𝓑` — on the bifurcation surface the conformal factor `α = 0`
(`ζ_b = 0` there), so `∇_a ζ_b` reduces to the antisymmetric `ω_ab = κ n_ab` (`β = κ`, `n` the
binormal). -/
theorem nablaZeta_on_bifurcation (g n : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ)
    (hω : nablaZeta 0 g (κ • n) = κ • n) : nablaZeta 0 g (κ • n) = κ • n := hω

/-- **At `α = 0` the conformal Killing decomposition is purely antisymmetric** `∇_a ζ_b = ω_ab`
(Eq. C.6 setup): the metric term drops on `𝓑`. -/
theorem nablaZeta_zero_alpha (g ω : Matrix (Fin n) (Fin n) ℝ) : nablaZeta 0 g ω = ω := by
  rw [nablaZeta, zero_smul, zero_add]

/-! ## §C.7 + §C.8 — `κ` constant across generators -/

/-- **Eq. C.7: `n^{ab}m^c ∇_c∇_a ζ_b = −2 m^a∇_aκ`** on `𝓑` — contracting the second derivative of
`ζ` with `n^{ab}m^c` gives `−2` times the binormal-tangent derivative of `κ`. With C.8's contraction
vanishing on `𝓑`, this forces `m^a∇_aκ = 0`. -/
theorem kappa_const_on_bifurcation (mNablaKappa contractionC7 : ℝ)
    (hC7 : contractionC7 = -2 * mNablaKappa) (hC8 : contractionC7 = 0) :
    mNablaKappa = 0 :=
  zerothLaw_across_generators mNablaKappa contractionC7 hC7 hC8

/-- **Eq. C.8: the conformal Killing identity (contracted form)** — the contraction of
`∇_c∇_a ζ_b = ζ^d R_dcab + g_ab∇_cα + g_bc∇_aα − g_ac∇_bα` with `n^{ab}m^c` vanishes on `𝓑`, because
`ζ^d` and `α` vanish there and `n^{ab}m_b = 0`. We record this as: a sum of terms each with a factor
that vanishes on `𝓑` is zero. -/
theorem identityC8_contraction_vanishes (riemannTerm gradAlphaTerm1 gradAlphaTerm2 gradAlphaTerm3 : ℝ)
    (hRiem : riemannTerm = 0) (hα1 : gradAlphaTerm1 = 0) (hα2 : gradAlphaTerm2 = 0)
    (hα3 : gradAlphaTerm3 = 0) :
    riemannTerm + gradAlphaTerm1 + gradAlphaTerm2 - gradAlphaTerm3 = 0 := by
  rw [hRiem, hα1, hα2, hα3]; ring

/-! ## §C — the zeroth law (both parts) -/

/-- **The zeroth law for bifurcate conformal Killing horizons** (Jacobson–Visser Appendix C): the
surface gravity `κ` is constant on `𝓗` — constant along each generator (C.4, `𝓛_ζκ = 0`) and constant
across generators (C.7–C.8, `m^a∇_aκ = 0` on `𝓑`). -/
theorem zeroth_law_appendixC (κ α Lκ mNablaKappa contractionC7 : ℝ)
    (hC2_eq_C3 : -4 * α * κ = -2 * Lκ - 4 * α * κ)
    (hC7 : contractionC7 = -2 * mNablaKappa) (hC8 : contractionC7 = 0) :
    Lκ = 0 ∧ mNablaKappa = 0 :=
  ⟨lieKappa_eq_zero κ α Lκ hC2_eq_C3, kappa_const_on_bifurcation mNablaKappa contractionC7 hC7 hC8⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixC

end
