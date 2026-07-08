/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint

/-!
# The curved-space quantum potential and the quantum matter super-Hamiltonian (Ipek–Caticha §8)

Completes the "matter" super-Hamiltonian of Ipek–Caticha (arXiv:2006.05036, Eqs. 52, 59, 60): the local **quantum
potential** in curved space. In flat space the quantum potential is `Q = ∫ρ λ(δ log ρ/δχ)²` (Eq. 60); the
transition to curved space is the substitution `d³x → √g d³x`, `δ/δχ → (1/√g) δ/δχ`, giving

`Q_σ = ∫ρ (λ/√g)(δ log ρ/δχ)²`,

so the curved quantum potential is the flat one (`edQuantumPotential`) with the coupling rescaled `λ → λ/√g` by the
metric density. Adding it to the classical curved Klein–Gordon energy gives the *quantum* matter super-Hamiltonian.

* the **curved quantum potential** `Q_σ = edQuantumPotential(λ/√g)` (`curvedQuantumPotential`) — the flat quantum
 potential with the metric-density-rescaled coupling, `= λ (δρ/δχ)²/(√g ρ)` (`curvedQuantumPotential_eq`);
* its **flat limit** `Q_σ|_{√g=1} = Q` (`curvedQuantumPotential_flat`) — recovering the flat quantum potential;
* its **positivity** `λ ≥ 0 ⟹ Q_σ ≥ 0` (`curvedQuantumPotential_nonneg`) — the quantum potential is non-negative
 precisely when `λ ≥ 0`; the paper excludes `λ < 0` as it leads to instabilities, so the coupling must be
 non-negative for the quantum potential to be a genuine (positive) energy;
* the **quantum matter super-Hamiltonian** `H̃_⊥ = ℋ_cl + Q_σ` (`quantumMatter_is_classical_plus_curvedQuantum`) —
 the classical curved Klein–Gordon density (`kgMatterDensity`, Eq. 100a) plus the curved quantum potential is the
 full quantum matter super-Hamiltonian (Eq. 59).

So the Ipek–Caticha matter super-Hamiltonian is the classical Klein–Gordon energy plus the curved quantum potential
`λ(δρ/δχ)²/(√g ρ)`, the metric-density generalization of the flat Fisher/Bohm term, non-negative exactly for the
physically allowed `λ ≥ 0` — the term that makes the coupled field theory quantum.

* **§A — the curved quantum potential** (`curvedQuantumPotential`, `curvedQuantumPotential_flat`,
 `curvedQuantumPotential_eq`, `curvedQuantumPotential_nonneg`).
* **§B — the quantum matter super-Hamiltonian** (`quantumMatter_is_classical_plus_curvedQuantum`).

The curved quantum potential, its flat limit, positivity, and the classical-plus-quantum
split are exact algebra, reusing `edQuantumPotential` and `kgMatterDensity`. The functional derivation of Eq. 59
(the `F_x` integration constant satisfying the Poisson bracket) is the referenced content. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 52, 59, 60). Repo dependencies:
 `EntropicTime.EntropicDynamicsCanonicalRepresentation` (`edQuantumPotential`),
 `EntropicTime.IpekCatichaMatterGravityConstraint` (`kgMatterDensity`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential

/-! ## §A — the curved quantum potential -/

/-- **The curved-space quantum potential** `Q_σ = edQuantumPotential(λ/√g)` (Ipek–Caticha Eq. 60) — the flat
quantum potential with the coupling rescaled `λ → λ/√g` by the metric density, from the curved-space substitution
`d³x → √g d³x`, `δ/δχ → (1/√g)δ/δχ`. -/
noncomputable def curvedQuantumPotential (sqrtg lam ρ dρ : ℝ) : ℝ :=
  edQuantumPotential (lam / sqrtg) ρ dρ

/-- **[The flat limit is the flat quantum potential] `Q_σ|_{√g=1} = Q`.** -/
theorem curvedQuantumPotential_flat (lam ρ dρ : ℝ) :
    curvedQuantumPotential 1 lam ρ dρ = edQuantumPotential lam ρ dρ := by
  unfold curvedQuantumPotential
  rw [div_one]

/-- **[The explicit curved quantum potential] `Q_σ = λ(δρ/δχ)²/(√g ρ)`.** The metric-density-weighted Fisher/Bohm
quantum potential. -/
theorem curvedQuantumPotential_eq (sqrtg lam ρ dρ : ℝ) :
    curvedQuantumPotential sqrtg lam ρ dρ = lam * dρ ^ 2 / (sqrtg * ρ) := by
  unfold curvedQuantumPotential edQuantumPotential
  ring

/-- **[The curved quantum potential is non-negative for `λ ≥ 0`] `Q_σ ≥ 0`.** For a positive metric density and
probability, the curved quantum potential is non-negative exactly when the coupling `λ ≥ 0` — the paper excludes
`λ < 0` (instabilities), so the physically allowed quantum potential is a positive energy. -/
theorem curvedQuantumPotential_nonneg (sqrtg lam ρ dρ : ℝ) (hlam : 0 ≤ lam) (hg : 0 < sqrtg)
    (hρ : 0 < ρ) : 0 ≤ curvedQuantumPotential sqrtg lam ρ dρ := by
  rw [curvedQuantumPotential_eq]
  exact div_nonneg (mul_nonneg hlam (sq_nonneg dρ)) (le_of_lt (mul_pos hg hρ))

/-! ## §B — the quantum matter super-Hamiltonian -/

/-- **[The quantum matter super-Hamiltonian is classical plus the curved quantum potential] `H̃_⊥ = ℋ_cl + Q_σ`.**
The Ipek–Caticha matter super-Hamiltonian (Eq. 59) is the classical curved Klein–Gordon energy density
(`kgMatterDensity`, Eq. 100a) plus the curved quantum potential — the quantum potential is what makes the coupled
Klein–Gordon field theory quantum. -/
theorem quantumMatter_is_classical_plus_curvedQuantum (sqrtg ginv π gradchi V lam ρ dρ : ℝ) :
    kgMatterDensity sqrtg ginv π gradchi V + curvedQuantumPotential sqrtg lam ρ dρ
      = kgMatterDensity sqrtg ginv π gradchi V + lam * dρ ^ 2 / (sqrtg * ρ) := by
  rw [curvedQuantumPotential_eq]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential

end
