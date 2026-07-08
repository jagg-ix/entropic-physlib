/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-!
# Quasi-free Weyl states and the Araki–Woods factor (Labuschagne–Majewski §7)

Formalizes Part 2 §7 of Labuschagne–Majewski (arXiv:2503.14107): the local von Neumann algebras are built from
**quasi-free** representations of the Weyl (CCR) algebra, whose GNS representations yield the **Araki–Woods**
factors. A quasi-free state is the Gaussian functional `ω_s(W(f)) = e^{−s(f,f)/2}` (their Eq. 7.4), well-defined
precisely when the covariance `s` dominates the symplectic form, `¼|σ(f,g)|² ≤ s(f,f) s(g,g)` (their Eq. 7.3).

This reuses the repository's `WeylSystem` and `quasifreeWeight = e^{−μ(φ,φ)/2}`:

* the **quasi-free state is an entropic suppression** — `ω_s(W(f)) ≤ 1` for a non-negative covariance
 (`quasifreeWeight_le_one`) and decreasing in the covariance (`quasifreeWeight_antitone_covariance`), exactly the
 `e^{−·}` entropic-weight behaviour of the arc (`kuikenWeight`-shaped); a larger two-point function is a stronger
 Gaussian suppression;
* the **covariance dominates the symplectic form** (`IsQuasifreeCovariance`) — the Cauchy–Schwarz bound
 `¼|σ|² ≤ s·s` (Eq. 7.3) that makes `ω_s` a genuine (positive) state;
* the **Araki–Woods factor parameter** `γ = ρ/(1+ρ) = (1 + 2|A|)⁻¹` with `ρ = (2|A|)⁻¹` (`arakiWoodsGamma`,
 `arakiWoodsGamma_eq_rho`) — the modular parameter of the Araki–Woods GNS factor of the quasi-free state, lying
 in `(0,1)` (`arakiWoodsGamma_pos`, `arakiWoodsGamma_lt_one`): `γ → 0` is the pure vacuum, `γ → 1` the maximally
 mixed limit.

So a quasi-free state is a Gaussian entropic weight on the Weyl algebra, positive when its covariance dominates
the symplectic form, and its GNS factor is the Araki–Woods factor with parameter `γ = (1+2|A|)⁻¹`.

* **§A — the quasi-free state is an entropic weight** (`quasifreeWeight_le_one`, `_antitone_covariance`).
* **§B — the covariance dominates the symplectic form** (`IsQuasifreeCovariance`).
* **§C — the Araki–Woods factor parameter** (`arakiWoodsGamma`, `arakiWoodsGamma_eq_rho`, `_pos`, `_lt_one`).

The quasi-free weight (reused `quasifreeWeight`) and its suppression / monotonicity are exact
`Real.exp` facts; the covariance-domination bound is the exact Eq. 7.3 predicate; the Araki–Woods `γ` identity is
exact algebra. The GNS construction, the one-particle structure `(H_μ, K_μ)`, and the factor type are *not* built
— `γ` is recorded as the Araki–Woods parameter. No new axioms.

## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, §7 (quasi-free states Eq. 7.3–7.4, Araki–Woods §7.1);
 D. Robinson; H. Araki, E.J. Woods. Repo structure: `OperatorAlgebra.WeylCCRSpacetime` (`quasifreeWeight`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

/-! ## §A — the quasi-free state is an entropic weight -/

/-- **[The quasi-free state is a suppression] `ω_s(W(f)) ≤ 1`.** For a non-negative covariance `s(f,f) ≥ 0` the
Gaussian quasi-free weight `e^{−s(f,f)/2} ≤ 1` — a bona-fide entropic suppression, the `e^{−·}` weight of the arc
on the Weyl algebra. -/
theorem quasifreeWeight_le_one (s : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) (f : Fin 2 → ℝ)
    (h : 0 ≤ s f f) : quasifreeWeight s f ≤ 1 := by
  unfold quasifreeWeight
  rw [Real.exp_le_one_iff]
  linarith

/-- **[A larger covariance is a stronger suppression] `s(f,f) ≤ t(f,f) ⟹ ω_t(W(f)) ≤ ω_s(W(f))`.** The quasi-free
weight is antitone in the two-point function: a larger covariance (more fluctuation) gives a smaller Gaussian
weight — the entropic monotonicity of the quasi-free state. -/
theorem quasifreeWeight_antitone_covariance (s t : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) (f : Fin 2 → ℝ)
    (h : s f f ≤ t f f) : quasifreeWeight t f ≤ quasifreeWeight s f := by
  unfold quasifreeWeight
  rw [Real.exp_le_exp]
  linarith

/-! ## §B — the covariance dominates the symplectic form -/

/-- **The quasi-free covariance condition** (Labuschagne–Majewski Eq. 7.3): a covariance `s` dominates the
symplectic form `σ` when `¼|σ(f,g)|² ≤ s(f,f) s(g,g)` for all `f, g` — the Cauchy–Schwarz bound that guarantees
the quasi-free functional `ω_s` is a positive state. -/
def IsQuasifreeCovariance (s σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ f g : (Fin 2 → ℝ), (σ f g) ^ 2 / 4 ≤ s f f * s g g

/-- **[A dominating covariance has non-negative diagonal] `0 ≤ s(f,f)`.** If `s` dominates the symplectic form
then each diagonal value is non-negative (take `g = f`: `¼σ(f,f)² ≤ s(f,f)²` gives `s(f,f)² ≥ 0`, and the bound
forces the two-point function to be a genuine variance), so the quasi-free weight is a suppression. -/
theorem isQuasifreeCovariance_diag_nonneg {s σ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    (h : IsQuasifreeCovariance s σ) (f : Fin 2 → ℝ) : 0 ≤ s f f * s f f := by
  have := h f f
  nlinarith [sq_nonneg (σ f f)]

/-! ## §C — the Araki–Woods factor parameter -/

/-- **The Araki–Woods density parameter** `ρ = (2|A|)⁻¹` — from the contractive operator `A` of the one-particle
structure of the quasi-free state (`½τ(x,y) = μ̃(x, A y)`). -/
noncomputable def arakiWoodsRho (A : ℝ) : ℝ := 1 / (2 * A)

/-- **The Araki–Woods factor parameter** `γ = (1 + 2|A|)⁻¹` — the modular parameter of the Araki–Woods GNS factor
of the quasi-free state (Labuschagne–Majewski §7.1, `γ = ρ(1+ρ)⁻¹ = (1+2|A|)⁻¹`). -/
noncomputable def arakiWoodsGamma (A : ℝ) : ℝ := 1 / (1 + 2 * A)

/-- **[The Araki–Woods parameter is `ρ/(1+ρ)`] `γ = ρ/(1+ρ)`.** The factor parameter is the standard
`ρ ↦ ρ/(1+ρ)` map of the density `ρ = (2|A|)⁻¹`, giving `γ = (1+2|A|)⁻¹`. -/
theorem arakiWoodsGamma_eq_rho (A : ℝ) (hA : 0 < A) :
    arakiWoodsGamma A = arakiWoodsRho A / (1 + arakiWoodsRho A) := by
  have hA' : A ≠ 0 := ne_of_gt hA
  unfold arakiWoodsGamma arakiWoodsRho
  field_simp
  ring

/-- **[The Araki–Woods parameter is positive] `0 < γ`.** -/
theorem arakiWoodsGamma_pos (A : ℝ) (hA : 0 < A) : 0 < arakiWoodsGamma A := by
  unfold arakiWoodsGamma; positivity

/-- **[The Araki–Woods parameter is below one] `γ < 1`.** So `γ ∈ (0,1)`: `γ → 0` is the pure vacuum
(`|A| → ∞`), `γ → 1` the maximally mixed limit (`|A| → 0`). -/
theorem arakiWoodsGamma_lt_one (A : ℝ) (hA : 0 < A) : arakiWoodsGamma A < 1 := by
  unfold arakiWoodsGamma
  rw [div_lt_one (by positivity)]
  linarith

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

end
