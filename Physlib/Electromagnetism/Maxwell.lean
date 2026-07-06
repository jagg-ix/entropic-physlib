/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Maxwell equations from the Faraday tensor

The covariant Maxwell equations for `F = dA`. The Faraday tensor `F_{μν} = k_μ A_ν − k_ν A_μ` (with `∂ → k`) is
**antisymmetric**, which yields both Maxwell equations:

* the **homogeneous** equation (Bianchi identity, `dF = 0`) `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`
  (`faraday_bianchi`) — from `d² = 0`;
* the **inhomogeneous** equation defines the four-current `J^ν = ∂_μ F^{μν}` (`fourCurrent`), whose four-divergence
  vanishes, `∂_ν J^ν = 0` (`fourCurrent_conserved`) — **charge conservation**, a consequence of the antisymmetry
  of `F` (the symmetric `k_μ k_ν` contracts to zero against the antisymmetric `F^{μν}`).

References: J.C. Maxwell; the covariant form `∂_μ F^{μν} = J^ν`, `∂_{[λ}F_{μν]} = 0`. No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.Electromagnetism.Maxwell

/-- **The Faraday tensor** `F_{μν} = k_μ A_ν − k_ν A_μ` (with `∂ → k`, `F = dA`). -/
def faraday (k A : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ := k μ * A ν - k ν * A μ

/-- **The Faraday tensor is antisymmetric** `F_{μν} = −F_{νμ}`. -/
theorem faraday_antisymm (k A : Fin 4 → ℝ) (μ ν : Fin 4) :
    faraday k A μ ν = -faraday k A ν μ := by
  unfold faraday; ring

/-- **The homogeneous Maxwell equation (Bianchi identity)** `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` — the
cyclic identity `dF = 0` for `F = dA`, from `d² = 0`. -/
theorem faraday_bianchi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0 := by
  unfold faraday; ring

/-- **The electromagnetic four-current** `J^ν = ∂_μ F^{μν} = Σ_μ k_μ F^{μν}` — the source of the inhomogeneous
Maxwell equation. -/
noncomputable def fourCurrent (k A : Fin 4 → ℝ) (ν : Fin 4) : ℝ := ∑ μ, k μ * faraday k A μ ν

/-- **Maxwell implies charge conservation** `∂_ν J^ν = Σ_ν k_ν J^ν = 0`. The four-divergence of the inhomogeneous
Maxwell law is `Σ_{μν} k_μ k_ν F^{μν}`; the symmetric `k_μ k_ν` contracted with the antisymmetric `F^{μν}`
vanishes — charge conservation follows from the antisymmetry of the field tensor. -/
theorem fourCurrent_conserved (k A : Fin 4 → ℝ) : ∑ ν, k ν * fourCurrent k A ν = 0 := by
  simp only [fourCurrent, faraday, Fin.sum_univ_four]
  ring

end Physlib.Electromagnetism.Maxwell

end
