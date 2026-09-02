/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification

/-!
# Greaves–Thomas `CPT`: Lorentz-covariant dynamics is `CPT`-invariant (the Dirac Lagrangian)

`PTSymmetricQFT.CPTComplexification` formalized the *group-theoretic* kernel of *H. Greaves, T. Thomas,
"The CPT Theorem"* (arXiv:1204.4674): the complexification path and `CPT` as spinorial total inversion.
But the paper's actual claim is about **field theories**: a *Lagrangian* (the dynamics `D`) built
Lorentz-covariantly is automatically `CPT`-invariant. This file supplies that missing link on the paper's
own motivating example — the **Dirac equation** `−iγ^μ∂_μ ψ + m ψ = 0` (their Eq. 1).

The Greaves–Thomas mechanism, made completely explicit, is a **cancellation of two total inversions**:

* the **spinor** action `ρ(−1) = −iγ⁵` sends each gamma `γ^μ ↦ −γ^μ`
  (`PTSymmetricQFT.CPTComplexification.cpt_total_inversion`);
* the **spacetime** action `ω(−1)` is total inversion `p ↦ −p` (equivalently `∂_μ ↦ −∂_μ`).

In the Dirac kinetic operator `p̸ = γ^μ p_μ` these multiply to `(−γ^μ)(−p_μ) = γ^μ p_μ`: the operator is
its own `CPT` image. This is the geometric action `u(g)Φ = ρ(g) ∘ Φ ∘ ω(g⁻¹)` of the paper's §2.3
instantiated at `g = −1` (total inversion), with the Dirac operator as a **fixed point** — the Lagrangian's
`CPT` invariance.

* **§A — the Dirac kinetic operator (Feynman slash)** (`diracSlash`, `diracSlash_neg`, `cpt_diracSlash`,
  `cpt_diracSlash_invariant`). `p̸ = ∑_μ γ^μ p_μ`; the spinor adjoint inverts it (`A p̸ A⁻¹ = −p̸`), the
  spacetime inversion inverts it (`p̸(−p) = −p̸(p)`), and the two cancel: `A p̸(−p) A⁻¹ = p̸(p)`.
* **§B — the full Dirac operator / Lagrangian dynamics** (`diracOp`, `cpt_diracOp_invariant`). The
  momentum-space Dirac operator `D(p) = p̸ − m` (the dynamics) is `CPT`-invariant: `A D(−p) A⁻¹ = D(p)` —
  the mass term `m·I` is `CPT`-even (commutes with `A`, momentum-independent).
* **§C — the dynamical `CPT` theorem** (`cpt_maps_dirac_solution`). The set of solutions is `CPT`-invariant:
  if `ψ` solves the Dirac equation at momentum `p` (`D(p)ψ = 0`), its `CPT` image `A⁻¹ψ = −Aψ` solves it at
  the reversed momentum `−p` (`D(−p)(A⁻¹ψ) = 0`). Lorentz-covariant dynamics ⟹ `CPT`-invariant dynamics.

Here `A = −iγ⁵` is the spinor `CPT` matrix (`A² = −1`, so `A⁻¹ = −A`).

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674 — §2.3 geometric actions; the `CPT`-invariance
  of Lorentz-covariant Lagrangians; the Dirac equation Eq. 1 as the motivating example.
* Repo carriers: `PTSymmetricQFT.CPTComplexification` (`cpt_total_inversion`, `tpc_matrix_sq`);
  `Relativity.CliffordAlgebra` (`γ`, the Dirac gammas).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics

open Matrix Complex
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification


/-- **The Dirac kinetic operator (Feynman slash)** `p̸ = ∑_μ γ^μ p_μ` — the principal symbol of
`−iγ^μ∂_μ` (Greaves–Thomas Eq. 1). -/
noncomputable def diracSlash (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ := ∑ μ, (p μ : ℂ) • γ μ

/-- **Spacetime total inversion negates the slash** `p̸(−p) = −p̸(p)` — the `ω(−1) : p ↦ −p` action. -/
lemma diracSlash_neg (p : Fin 4 → ℝ) : diracSlash (-p) = - diracSlash p := by
  simp only [diracSlash, Pi.neg_apply, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib]

/-- **The spinor `CPT` adjoint negates the slash** `A p̸ A⁻¹ = −p̸` — each `γ^μ ↦ −γ^μ` under `ρ(−1) = −iγ⁵`
(`cpt_total_inversion`), summed over `μ`. -/
lemma cpt_diracSlash (p : Fin 4 → ℝ) :
    ((-I) • γ5) * diracSlash p * (-((-I) • γ5)) = - diracSlash p := by
  unfold diracSlash
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  rw [mul_smul_comm, smul_mul_assoc, cpt_total_inversion, smul_neg]

/-- **[Greaves–Thomas] The Dirac kinetic operator is `CPT`-invariant.** The spinor total inversion
`γ^μ ↦ −γ^μ` and the spacetime total inversion `p ↦ −p` **cancel**: `A p̸(−p) A⁻¹ = p̸(p)`. This is the
geometric action `u(−1) p̸ = p̸` — the Lorentz-covariant kinetic term is its own `CPT` image. -/
lemma cpt_diracSlash_invariant (p : Fin 4 → ℝ) :
    ((-I) • γ5) * diracSlash (-p) * (-((-I) • γ5)) = diracSlash p := by
  rw [cpt_diracSlash (-p), diracSlash_neg, neg_neg]


/-- **The momentum-space Dirac operator** `D(p) = p̸ − m·I` — the dynamics of the Dirac Lagrangian
`ψ̄(iγ^μ∂_μ − m)ψ`; the field equation is `D(p)ψ = 0`. -/
noncomputable def diracOp (p : Fin 4 → ℝ) (m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diracSlash p - (m : ℂ) • 1

/-- **[Greaves–Thomas] The Dirac operator (the dynamics) is `CPT`-invariant** `A D(−p) A⁻¹ = D(p)`. The
kinetic term is invariant by the two-inversion cancellation (`cpt_diracSlash_invariant`); the mass term
`m·I` is `CPT`-even — it commutes with `A` and is momentum-independent. So the Lorentz-covariant Lagrangian
is `CPT`-invariant, the content of the Greaves–Thomas theorem on this example. -/
lemma cpt_diracOp_invariant (p : Fin 4 → ℝ) (m : ℝ) :
    ((-I) • γ5) * diracOp (-p) m * (-((-I) • γ5)) = diracOp p m := by
  unfold diracOp
  rw [mul_sub, sub_mul, cpt_diracSlash_invariant]
  congr 1
  rw [mul_smul_comm, mul_one, smul_mul_assoc, mul_neg, tpc_matrix_sq, neg_neg]


/-- **[Greaves–Thomas] `CPT` maps Dirac solutions to Dirac solutions.** If `ψ` solves the Dirac equation at
momentum `p` (`D(p)ψ = 0`), then its `CPT` image `A⁻¹ψ = −Aψ` solves the Dirac equation at the reversed
momentum `−p` (`D(−p)(−Aψ) = 0`). The solution set — the field theory `D` itself — is `CPT`-invariant:
Lorentz-covariant dynamics entails `CPT`-invariant dynamics. -/
lemma cpt_maps_dirac_solution (p : Fin 4 → ℝ) (m : ℝ) (ψ : Fin 4 → ℂ)
    (h : diracOp p m *ᵥ ψ = 0) :
    diracOp (-p) m *ᵥ ((-((-I) • γ5)) *ᵥ ψ) = 0 := by
  have hAA : (-((-I) • γ5)) * ((-I) • γ5) = 1 := by rw [neg_mul, tpc_matrix_sq, neg_neg]
  have key := cpt_diracOp_invariant p m
  have hconj : diracOp (-p) m * (-((-I) • γ5)) = (-((-I) • γ5)) * diracOp p m := by
    calc diracOp (-p) m * (-((-I) • γ5))
        = (-((-I) • γ5) * ((-I) • γ5)) * (diracOp (-p) m * (-((-I) • γ5))) := by rw [hAA, one_mul]
      _ = (-((-I) • γ5)) * (((-I) • γ5) * diracOp (-p) m * (-((-I) • γ5))) := by simp only [mul_assoc]
      _ = (-((-I) • γ5)) * diracOp p m := by rw [key]
  rw [Matrix.mulVec_mulVec, hconj, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics

end
