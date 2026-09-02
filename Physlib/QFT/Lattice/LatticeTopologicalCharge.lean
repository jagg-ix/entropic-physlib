/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The lattice topological charge and its Symanzik improvement

Ports `lean4/QCDVortex/TopologicalCharge.lean` of the qcd-vortex-entanglement tree (Lean layer
own authorship; LatticeQCD.jl observables, arXiv:1509.04259):

* `leviCivita4` — the explicit 24-entry 4D `ε_{μνρσ}` table, with vanishing on repeated
  indices (`leviCivita4_eq_zero_of_repeat`), antisymmetry in both index pairs
  (`leviCivita4_swap_12`/`_34`), and self-duality `ε_{μνρσ} = ε_{ρσμν}`
  (`leviCivita4_self_dual`) — all by exhaustive `fin_cases`;
* `topoChargeDensity`/`topoCharge` — `q(x) = (1/32π²)·ε_{μνρσ}F_{μν}F_{ρσ}` on an
  antisymmetric field-strength carrier, with `topoCharge_zero_of_negF` (T-even fields carry
  no charge);
* `improvedTopCharge` — the Symanzik-improved charge `(5/3)·Q_clover − (1/12)·Q_rect`, its
  tree-level consistency `c₀ + 8c₁ = 1`, and bilinear-improvement linearity.

**Honest layering.**  Exact combinatorial and algebraic content; `Q ∈ ℤ` in the continuum
(instanton number) and the `O(a²)`-artifact cancellation are the field-theory layer, cited
not re-proven.  The spacetime Levi-Civita *tensor* carrier is
`Relativity/Tensors/LeviCivita`; this is the lattice `Fin 4` symbol table those observables
sum against.  Three `:= rfl` definition restatements of the source are not reproduced.

## References

* Source: `lean4/QCDVortex/TopologicalCharge.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.Lattice.LatticeTopologicalCharge

open Real

/-! ## 1. Levi-Civita tensor in 4D -/

/--
4D Levi-Civita symbol ε_{μνρσ} ∈ {−1, 0, +1}.
Returns +1 for even permutations of (0,1,2,3),
        −1 for odd permutations,
         0 whenever any two indices coincide.

Matches the explicit table in LatticeQCD.jl `epsilon_tensor`.
-/
def leviCivita4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ
  | 0, 1, 2, 3 =>  1 | 0, 1, 3, 2 => -1
  | 0, 2, 1, 3 => -1 | 0, 2, 3, 1 =>  1
  | 0, 3, 1, 2 =>  1 | 0, 3, 2, 1 => -1
  | 1, 0, 2, 3 => -1 | 1, 0, 3, 2 =>  1
  | 1, 2, 0, 3 =>  1 | 1, 2, 3, 0 => -1
  | 1, 3, 0, 2 => -1 | 1, 3, 2, 0 =>  1
  | 2, 0, 1, 3 =>  1 | 2, 0, 3, 1 => -1
  | 2, 1, 0, 3 => -1 | 2, 1, 3, 0 =>  1
  | 2, 3, 0, 1 =>  1 | 2, 3, 1, 0 => -1
  | 3, 0, 1, 2 => -1 | 3, 0, 2, 1 =>  1
  | 3, 1, 0, 2 =>  1 | 3, 1, 2, 0 => -1
  | 3, 2, 0, 1 => -1 | 3, 2, 1, 0 =>  1
  | _, _, _, _ =>  0

set_option maxHeartbeats 1600000 in
/-- ε vanishes when any two indices coincide. -/
theorem leviCivita4_eq_zero_of_repeat (μ ν ρ σ : Fin 4)
    (h : μ = ν ∨ μ = ρ ∨ μ = σ ∨ ν = ρ ∨ ν = σ ∨ ρ = σ) :
    leviCivita4 μ ν ρ σ = 0 := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;>
    simp_all [leviCivita4]

/-- Antisymmetry in positions 1 and 2: ε_{νμρσ} = −ε_{μνρσ}. -/
theorem leviCivita4_swap_12 (μ ν ρ σ : Fin 4) :
    leviCivita4 ν μ ρ σ = -leviCivita4 μ ν ρ σ := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;> rfl

/-- Antisymmetry in positions 3 and 4: ε_{μνσρ} = −ε_{μνρσ}. -/
theorem leviCivita4_swap_34 (μ ν ρ σ : Fin 4) :
    leviCivita4 μ ν σ ρ = -leviCivita4 μ ν ρ σ := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;> rfl

/-- Self-duality: ε_{μνρσ} = ε_{ρσμν}. -/
theorem leviCivita4_self_dual (μ ν ρ σ : Fin 4) :
    leviCivita4 μ ν ρ σ = leviCivita4 ρ σ μ ν := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;> rfl

/-! ## 2. Topological charge density -/

/--
Field strength tensor F_{μν}(x) : ℝ.
In LatticeQCD.jl this is the real part of the traceless anti-Hermitian
projected plaquette: `Traceless_antihermitian(U_{μν}(x))`.
-/
structure GaugeFieldStrength (α : Type*) where
  /-- F_{μν}(x): the (μ,ν) component of the field strength at site x. -/
  F : α → Fin 4 → Fin 4 → ℝ
  /-- Antisymmetry F_{μν} = −F_{νμ}. -/
  antisymm : ∀ x μ ν, F x μ ν = -F x ν μ

/--
Local topological charge density:
  q(x) = (1/32π²) Σ_{μνρσ} ε_{μνρσ} · F_{μν}(x) · F_{ρσ}(x)

The sign convention follows LatticeQCD.jl `calc_Q` (which uses −1/(32π²),
absorbing sign into the ε tensor orientation).
-/
noncomputable def topoChargeDensity {α : Type*} (f : GaugeFieldStrength α) (x : α) : ℝ :=
  (1 / (32 * π^2)) * ∑ μ : Fin 4, ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    (leviCivita4 μ ν ρ σ : ℝ) * f.F x μ ν * f.F x ρ σ

/--
Total topological charge Q = Σ_x q(x) over all lattice sites.
In the continuum limit this converges to an integer: the instanton number.
-/
noncomputable def topoCharge {α : Type*} [Fintype α] (f : GaugeFieldStrength α) : ℝ :=
  ∑ x : α, topoChargeDensity f x

/-- Q vanishes for field strengths satisfying T-symmetry F → −F. -/
theorem topoCharge_zero_of_negF {α : Type*} [Fintype α] (f : GaugeFieldStrength α)
    (hT : ∀ x μ ν, f.F x μ ν = -f.F x μ ν) :
    topoCharge f = 0 := by
  have hF : ∀ x μ ν, f.F x μ ν = 0 := fun x μ ν => by linarith [hT x μ ν]
  simp [topoCharge, topoChargeDensity, hF]

/-! ## 3. Symanzik improvement -/

/-- Symanzik leading coefficient (1×1 clover). -/
noncomputable def c₀ : ℝ := 5 / 3

/-- Symanzik subleading coefficient (1×2 rectangle). -/
noncomputable def c₁ : ℝ := -1 / 12

/--
Symanzik-improved topological charge:
  Q_imp = c₀ · Q_clover + c₁ · Q_rect
        = (5/3) · Q_clover − (1/12) · Q_rect

Eliminates O(a²) lattice artifacts. From LatticeQCD.jl:
  Q_improved = (5/3) * Q_clover + (-1/12) * (2 * Q_rect_half)
-/
noncomputable def improvedTopCharge (Q_clover Q_rect : ℝ) : ℝ :=
  c₀ * Q_clover + c₁ * Q_rect

/-- Q_imp = (5/3) Q_clover when Q_rect = 0. -/
theorem improvedTopCharge_no_rect (Q_clover : ℝ) :
    improvedTopCharge Q_clover 0 = c₀ * Q_clover := by
  simp [improvedTopCharge]

/-- Symanzik tree-level consistency: c₀ + 8·c₁ = 1. -/
theorem symanzik_coefficients_tree_level : c₀ + 8 * c₁ = 1 := by
  norm_num [c₀, c₁]

/-- Improvement is linear in both charges. -/
theorem improvedTopCharge_linear (Q_c₁ Q_r₁ Q_c₂ Q_r₂ a : ℝ) :
    improvedTopCharge (a * Q_c₁ + Q_c₂) (a * Q_r₁ + Q_r₂) =
    a * improvedTopCharge Q_c₁ Q_r₁ + improvedTopCharge Q_c₂ Q_r₂ := by
  simp [improvedTopCharge]; ring

end Physlib.QFT.Lattice.LatticeTopologicalCharge

end
