/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge

/-!
# The Lovelock–Palatini characterization: total antisymmetry and the projective gauge

Formalizes the algebraic backbone of N. Dadhich, J. M. Pons, *Characterization of the Lovelock–Palatini
Lagrangians with an arbitrary connection* (arXiv:1012.1692) — the Lovelock generalization of the
Einstein–Palatini result of `EinsteinPalatiniProjectiveGauge`. For a Palatini Lagrangian polynomial in the
Riemann curvature (no derivatives) with an *arbitrary* connection `Γ̄ = Γ + C`, their **theorem** is:

  *the Levi-Civita truncation (`C = 0`) is consistent* **iff** *the Lagrangian is Lovelock*,

equivalently (statements I–V) iff `∇_μ ∂ℒ/∂R_{μνρσ}` vanishes identically (Eq. eomextra, the cornerstone),
iff the truncated EOM is second order. The general homogeneous Lagrangian
`ℒ = R_{μ₁ν₁ρ₁σ₁}⋯R_{μₖνₖρₖσₖ} A^{μ₁ν₁ρ₁σ₁⋯}` (Eq. generalform) satisfies the cornerstone identically exactly
when the coefficient `A` is *totally antisymmetric* in its upper and in its lower index groups
(Eq. generalform2) — and the unique such geometric structure built from the metric is the **generalized
Kronecker delta** `δ^{μ₁…μᵣ}_{ν₁…νᵣ} = δ^{[μ₁}_{ν₁}⋯δ^{μᵣ]}_{νᵣ}` (Eq. multiK), yielding the Lovelock Lagrangian
`ℒ_p = √(-g)\, δ^{μ₁…σ_p}_{ρ₁…σ_p} R_{μ₁ν₁}{}^{ρ₁σ₁}⋯` (Eq. lovelocklag).

This file reuses `KroneckerDelta.Generalized.generalizedKroneckerDelta` (= `δ^{μ…}_{ν…} = det(δ[μᵢ,νⱼ])`,
Eq. multiK), the Lovelock survival data of `Curvature.LovelockDimensionalTermination`, and the projective
mode of `EinsteinPalatiniProjectiveGauge`, and adds:

* `generalizedKroneckerDelta_swap_lower` — lower-index antisymmetry (the paper's `A` antisymmetry, completing
  the existing upper-index `generalizedKroneckerDelta_swap`).
* `generalizedKroneckerDelta_eq_zero_of_repeat_upper` / `_lower` — a repeated index annihilates the
  generalized Kronecker delta. This is why a *symmetric* perturbation is invisible to the Lovelock
  Lagrangian: the mechanism behind the projective gauge invariance.
* `lovelockPalatini_projective_gauge` — the metric-affine gauge `Γ̄^ν_{μρ} → Γ̄^ν_{μρ} + V_μ δ^ν_ρ`
  (Eq. thegauges) is *exactly* the projective mode `EinsteinPalatiniProjectiveGauge.projectiveConnection` of
  the Einstein–Palatini case: the same abelian gauge symmetry governs the Lovelock–Palatini Lagrangian, and
  `projectiveConnection_add` gives its group law.

## References

* N. Dadhich, J. M. Pons, arXiv:1012.1692. Carriers: `KroneckerDelta.Generalized`
  (`generalizedKroneckerDelta`), `Curvature.LovelockDimensionalTermination`,
  `EinsteinPalatiniProjectiveGauge` (`projectiveConnection`).
-/

set_option autoImplicit false

open Matrix KroneckerDelta
open Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LovelockPalatiniCharacterization

variable {α ι : Type} [DecidableEq α] [DecidableEq ι] [Fintype ι]

/-! ### Total antisymmetry of the generalized Kronecker delta (the Lovelock coefficient structure) -/

set_option backward.isDefEq.respectTransparency false in
/-- **[Eq. generalform2 — lower antisymmetry] Swapping two lower indices negates** the generalized
Kronecker delta (one column transposition of `det(δ[μᵢ,νⱼ])`), completing the existing upper-index
antisymmetry `generalizedKroneckerDelta_swap`. Total antisymmetry in both groups is the defining property of
the Lovelock coefficient `A`. -/
theorem generalizedKroneckerDelta_swap_lower (μ ν : ι → α) {i j : ι} (hij : i ≠ j) :
    generalizedKroneckerDelta μ (ν ∘ Equiv.swap i j) = - generalizedKroneckerDelta μ ν := by
  rw [show generalizedKroneckerDelta μ (ν ∘ Equiv.swap i j)
        = (Matrix.submatrix (fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ))
            id (Equiv.swap i j)).det from rfl,
    Matrix.det_permute', Equiv.Perm.sign_swap hij]
  simp [generalizedKroneckerDelta]

/-- **[The antisymmetry mechanism] A repeated upper index annihilates the generalized Kronecker delta** —
`det` with two equal rows is zero. A symmetric perturbation contracts a Lovelock coefficient through a
repeated index and therefore vanishes: this is the algebraic reason the Lovelock Lagrangian is invariant
under the projective gauge (Eq. thegaugesR, where the trace term `η^{IJ}\,dV` drops out). -/
theorem generalizedKroneckerDelta_eq_zero_of_repeat_upper (μ ν : ι → α) {i j : ι} (hij : i ≠ j)
    (h : μ i = μ j) : generalizedKroneckerDelta μ ν = 0 := by
  have hfix : μ ∘ Equiv.swap i j = μ := by
    funext k
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, h]
    · rcases eq_or_ne k j with rfl | hkj
      · simp [Equiv.swap_apply_right, h]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hs := generalizedKroneckerDelta_swap μ ν hij
  rw [hfix] at hs
  omega

/-- **[The antisymmetry mechanism] A repeated lower index annihilates the generalized Kronecker delta.** -/
theorem generalizedKroneckerDelta_eq_zero_of_repeat_lower (μ ν : ι → α) {i j : ι} (hij : i ≠ j)
    (h : ν i = ν j) : generalizedKroneckerDelta μ ν = 0 := by
  have hfix : ν ∘ Equiv.swap i j = ν := by
    funext k
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, h]
    · rcases eq_or_ne k j with rfl | hkj
      · simp [Equiv.swap_apply_right, h]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hs := generalizedKroneckerDelta_swap_lower μ ν hij
  rw [hfix] at hs
  omega

/-! ### The projective gauge of the Lovelock–Palatini connection -/

/-- **[Eq. thegauges — the projective gauge is the Einstein–Palatini projective mode] `Γ̄^ν_{μρ} →
Γ̄^ν_{μρ} + V_μ δ^ν_ρ`.** The metric-affine gauge symmetry admitted by the Lovelock–Palatini Lagrangian is
*exactly* the projective connection `EinsteinPalatiniProjectiveGauge.projectiveConnection V`
(`(C^ν)_{μρ} = δ^ν_ρ V_μ`): the same `R^d` gauge freedom that leaves the Einstein–Palatini connection
undetermined governs every Lovelock order. -/
theorem lovelockPalatini_projective_gauge {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (V : ι' → ℝ)
    (ν μ ρ : ι') :
    projectiveConnection V ν μ ρ = if ρ = ν then V μ else 0 :=
  projectiveConnection_apply V ν μ ρ

/-- **[Eq. thegauges — the gauge group] The Lovelock–Palatini projective gauge is abelian.** Composing the
projective transformation adds the covectors (reusing `projectiveConnection_add`), so the gauge symmetry of
the Lovelock–Palatini Lagrangian is the abelian `R^d` group, identical to the Einstein–Palatini case. -/
theorem lovelockPalatini_gauge_add {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (V W : ι' → ℝ) :
    entropicConnection (projectiveConnection V) (projectiveConnection W)
      = projectiveConnection (fun μ => V μ + W μ) :=
  projectiveConnection_add V W

end Physlib.QuantumMechanics.ComplexAction.LovelockPalatiniCharacterization

end
