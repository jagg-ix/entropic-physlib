/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.VonNeumann

@[expose] public section

noncomputable section

namespace QuantumInfo.Finite

open scoped HermitianMat InnerProductSpace RealInnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-!
# Entropic proper time (dimensionless core)

The **entropic proper time** of a state pair is the finite quantum relative
entropy `qRelativeEnt ρ σ`. This file contains only the pure
information-theoretic core — a dimensionless `ENNReal`-valued quantity and its
basic facts — with **no spacetime or units dependencies**, so it is safe to
re-export through `QuantumInfo.Finite.Entropy`.

The dimensional lift to a metric time and the spacetime coupling live in
`Physlib.SpaceAndTime.EntropicProperTime`.

## Source and equation map

* H. Umegaki, *Conditional expectation in an operator algebra. IV. Entropy and information*,
  Kodai Mathematical Seminar Reports 14 (1962), 59-85, doi:10.2996/kmj/1138844604.
  This is the finite-density-matrix relative entropy used here:
  `D(ρ‖σ) = Tr(ρ(log ρ - log σ))`.
* H. Araki, *Relative Entropy of States of von Neumann Algebras*, Publications of the
  Research Institute for Mathematical Sciences 11 (1976), 809-833,
  doi:10.2977/prims/1195191148. This is the von-Neumann-algebra extension whose
  faithful finite-dimensional specialization is the same logarithmic relative entropy.
* A. Connes and C. Rovelli, *Von Neumann algebra automorphisms and time-thermodynamics
  relation in generally covariant quantum theories*, Classical and Quantum Gravity 11
  (1994), 2899-2918, doi:10.1088/0264-9381/11/12/007. This branch does **not** identify
  `τ_ent` with the Connes-Rovelli modular flow; it uses only the relative-entropy scalar
  that later modules scale into a metric time.

The formal correspondence in this file is:

* `entropicProperTime ρ σ = qRelativeEnt ρ σ` (`entropicProperTime_eq_qRelativeEnt`);
* `τ_ent(ρ‖ρ) = 0` (`entropicProperTime_self`);
* `τ_ent = -S_vN(ρ) - ⟪ρ, log σ⟫` for nonsingular `σ`
  (`entropicProperTime_toReal_modular_form`);
* `0 ≤ τ_ent` as a real number (`entropicProperTime_toReal_nonneg`).
-/

/-- Dimensionless **entropic proper time**: the finite quantum relative
entropy of the state pair `(ρ, σ)`. -/
def entropicProperTime (ρ σ : MState d) : ENNReal :=
  qRelativeEnt ρ σ

/-- Definitional reduction: `entropicProperTime = qRelativeEnt`. -/
theorem entropicProperTime_eq_qRelativeEnt (ρ σ : MState d) :
    entropicProperTime ρ σ = qRelativeEnt ρ σ :=
  rfl

/-- `entropicProperTime` is a function of the state pair. -/
theorem entropicProperTime_congr
    {ρ σ ρ' σ' : MState d} (hρ : ρ = ρ') (hσ : σ = σ') :
    entropicProperTime ρ σ = entropicProperTime ρ' σ' := by
  rw [hρ, hσ]

/-- Vanishing on the diagonal: `τ_ent(ρ‖ρ) = 0`. -/
@[simp] theorem entropicProperTime_self (ρ : MState d) :
    entropicProperTime ρ ρ = 0 :=
  qRelEntropy_self ρ

/-- Finiteness under a non-singular reference state. -/
theorem entropicProperTime_ne_top
    {ρ σ : MState d} [σ.M.NonSingular] :
    entropicProperTime ρ σ ≠ ⊤ :=
  qRelativeEnt_ne_top

/-- Closed (modular) form `τ_ent = -Sᵥₙ(ρ) - ⟪ρ, log σ⟫` under a non-singular
reference state. -/
theorem entropicProperTime_toReal_modular_form
    {ρ σ : MState d} [σ.M.NonSingular] :
    (entropicProperTime ρ σ).toReal =
      -Sᵥₙ ρ - ⟪ρ.M, σ.M.log⟫ := by
  unfold entropicProperTime
  have h_ereal : (qRelativeEnt ρ σ : EReal) =
      ⟪ρ.M, ρ.M.log - σ.M.log⟫ := qRelativeEnt_rank
  have h_real : (qRelativeEnt ρ σ).toReal =
      ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
    rw [← EReal.toReal_coe_ennreal, h_ereal]
    exact EReal.toReal_coe _
  rw [h_real, inner_sub_right, Sᵥₙ_eq_neg_trace_log, real_inner_comm]
  ring

/-- Non-negativity of the real-valued entropic proper time. -/
theorem entropicProperTime_toReal_nonneg (ρ σ : MState d) :
    0 ≤ (entropicProperTime ρ σ).toReal :=
  ENNReal.toReal_nonneg

end QuantumInfo.Finite

end
