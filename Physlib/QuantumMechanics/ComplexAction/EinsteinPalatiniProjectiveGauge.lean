/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

/-!
# The projective gauge of the Einstein–Palatini connection

Formalizes the connection algebra of N. Dadhich and J. M. Pons, *On the equivalence of the Einstein–Hilbert
and the Einstein–Palatini formulations of general relativity for an arbitrary connection*, Gen. Rel. Grav.
44 (2012) 2337. In the Einstein–Palatini (affine-metric) formulation the connection `Γ̄` is an independent
field; writing `Γ̄ = Γ + C` (Eq. 2.3, the repo's `EntropicTime.ConnectionCovariantHessian.entropicConnection`
with `Γ` the Levi-Civita connection), the equation of motion for `C` is solved by the **projective mode**

  `C^σ_{μν} = δ^σ_ν U_μ`   (Eq. 2.8),

for an arbitrary covector `U`. This is a pure gauge direction: the infinitesimal `R^d` gauge transformation
`δC^σ_{μν} = δ^σ_ν ε_μ` (Sect. 5) shifts `C` by exactly such a mode, so it is undetermined by the field
equations. Einstein's condition that the connection reduce to Levi-Civita is the *gauge-fixing* `U = 0`
(Eq. 2.9), equivalent to the vanishing of the **trace of the torsion** — not of the torsion itself.

This file reuses the connection API of `ConnectionCovariantHessian` (`IsTorsionFree`, `entropicConnection`,
`entropicConnection_torsionFree`) and adds:

* `torsion` — the torsion tensor `T^σ_{μν} = Γ^σ_{μν} − Γ^σ_{νμ}`, with `torsion_eq_zero_iff_isTorsionFree`.
* `projectiveConnection` — the projective mode `C^σ_{μν} = δ^σ_ν U_μ` (Eq. 2.8).
* `torsion_projectiveConnection` (Eq. 2.8) — `T^σ_{μν} = δ^σ_ν U_μ − δ^σ_μ U_ν`.
* `torsion_projectiveConnection_trace` (Eq. 2.9) — `∑_ν T^ν_{μν} = (d−1)U_μ`, so `U_μ = T^ν_{μν}/(d−1)`.
* `projectiveConnection_isTorsionFree_iff` (Eq. 2.9) — the projective connection is torsion-free iff `U = 0`
  (`d ≥ 2`); hence `entropicConnection_projective_isTorsionFree_iff`: `Γ̄ = Γ + C(U)` is Levi-Civita iff
  `U = 0`.
* `projectiveConnection_add` — the projective modes are additive in `U`, the `R^d` gauge group of Sect. 5.

## References

* N. Dadhich, J. M. Pons, Gen. Rel. Grav. 44 (2012) 2337, §2, §5. Carrier: `ConnectionCovariantHessian`
  (`entropicConnection`, `IsTorsionFree`).
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The torsion tensor** `T^σ_{μν} = Γ^σ_{μν} − Γ^σ_{νμ}` — the antisymmetric part of the connection in its
lower pair. -/
def torsion (Γ : ι → Matrix ι ι ℝ) : ι → Matrix ι ι ℝ := fun l => Γ l - (Γ l)ᵀ

lemma torsion_apply (Γ : ι → Matrix ι ι ℝ) (l μ ν : ι) : torsion Γ l μ ν = Γ l μ ν - Γ l ν μ := by
  simp [torsion, Matrix.sub_apply, Matrix.transpose_apply]

/-- **[Torsion vanishes ⟺ torsion-free]** the torsion tensor is zero exactly when the connection is
symmetric in its lower indices (`ConnectionCovariantHessian.IsTorsionFree`). -/
theorem torsion_eq_zero_iff_isTorsionFree (Γ : ι → Matrix ι ι ℝ) :
    (∀ l, torsion Γ l = 0) ↔ IsTorsionFree Γ := by
  simp only [torsion, IsTorsionFree, sub_eq_zero]
  exact ⟨fun h l => (h l).symm, fun h l => (h l).symm⟩

/-- **[Dadhich–Pons Eq. 2.8] The projective connection** `C^σ_{μν} = δ^σ_ν U_μ` — the mode solving the
Einstein–Palatini equation of motion for `C`, for an arbitrary covector `U`. -/
def projectiveConnection (U : ι → ℝ) : ι → Matrix ι ι ℝ :=
  fun l => Matrix.of fun μ ν => if ν = l then U μ else 0

@[simp] lemma projectiveConnection_apply (U : ι → ℝ) (l μ ν : ι) :
    projectiveConnection U l μ ν = if ν = l then U μ else 0 := rfl

/-- **[Eq. 2.8] The torsion of the projective connection** `T^σ_{μν} = δ^σ_ν U_μ − δ^σ_μ U_ν`. -/
theorem torsion_projectiveConnection (U : ι → ℝ) (l μ ν : ι) :
    torsion (projectiveConnection U) l μ ν
      = (if ν = l then U μ else 0) - (if μ = l then U ν else 0) := by
  rw [torsion_apply, projectiveConnection_apply, projectiveConnection_apply]

/-- **[Eq. 2.9] The trace of the torsion is `(d−1)U`** — `∑_ν T^ν_{μν} = (d − 1) U_μ` with `d = dim`, so the
covector is recovered as `U_μ = (1/(d−1)) T^ν_{μν}`: it is the *trace* of the torsion, not the torsion
itself, that Einstein's condition sets to zero. -/
theorem torsion_projectiveConnection_trace (U : ι → ℝ) (μ : ι) :
    (∑ ν, torsion (projectiveConnection U) ν μ ν) = ((Fintype.card ι : ℝ) - 1) * U μ := by
  have h : ∀ ν, torsion (projectiveConnection U) ν μ ν = U μ - (if μ = ν then U ν else 0) := by
    intro ν; rw [torsion_projectiveConnection, if_pos rfl]
  simp_rw [h, Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ μ)]
  ring

/-- **[Eq. 2.9] The projective connection is torsion-free iff `U = 0`** (in dimension `d ≥ 2`). The
Levi-Civita "gauge fixing" of Einstein–Palatini removes precisely the projective covector. -/
theorem projectiveConnection_isTorsionFree_iff (U : ι → ℝ) (hd : 2 ≤ Fintype.card ι) :
    IsTorsionFree (projectiveConnection U) ↔ ∀ μ, U μ = 0 := by
  constructor
  · intro h μ
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) μ
    have := congrFun (congrFun (h l) μ) l
    rw [Matrix.transpose_apply, projectiveConnection_apply, projectiveConnection_apply,
      if_pos rfl, if_neg (Ne.symm hl)] at this
    exact this.symm
  · intro h
    intro l
    ext μ ν
    rw [Matrix.transpose_apply, projectiveConnection_apply, projectiveConnection_apply, h μ, h ν]
    simp

/-- **[Eqs. 2.3/2.9] `Γ̄ = Γ + C(U)` is Levi-Civita iff `U = 0`.** With `Γ` the (torsion-free) Levi-Civita
connection, the full Einstein–Palatini connection `Γ̄ = Γ + C(U)` (the reused `entropicConnection`) is itself
torsion-free exactly when the projective covector vanishes — the physical connection is Levi-Civita, up to the
undetermined gauge mode. -/
theorem entropicConnection_projective_isTorsionFree_iff (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (hd : 2 ≤ Fintype.card ι) :
    IsTorsionFree (entropicConnection Γ (projectiveConnection U)) ↔ ∀ μ, U μ = 0 := by
  constructor
  · intro h
    refine (projectiveConnection_isTorsionFree_iff U hd).mp ?_
    intro l
    have hΓl := hΓ l
    have hhl := h l
    simp only [entropicConnection, Matrix.transpose_add] at hhl
    rw [hΓl] at hhl
    exact add_left_cancel hhl
  · intro h
    exact entropicConnection_torsionFree Γ (projectiveConnection U) hΓ
      ((projectiveConnection_isTorsionFree_iff U hd).mpr h)

/-- **[Sect. 5 — the `R^d` gauge group] The projective modes are additive in `U`.** Composing the
projective transformation `C ↦ C + C(ε)` (the infinitesimal gauge move `δC^σ_{μν} = δ^σ_ν ε_μ`) is addition
of the covectors, so the projective transformations form the abelian `R^d` gauge group under which the
Einstein–Palatini connection is undetermined. -/
theorem projectiveConnection_add (U ε : ι → ℝ) :
    entropicConnection (projectiveConnection U) (projectiveConnection ε)
      = projectiveConnection (fun μ => U μ + ε μ) := by
  funext l
  ext μ ν
  simp only [entropicConnection, Matrix.add_apply, projectiveConnection_apply]
  split_ifs <;> ring

end Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge

end
