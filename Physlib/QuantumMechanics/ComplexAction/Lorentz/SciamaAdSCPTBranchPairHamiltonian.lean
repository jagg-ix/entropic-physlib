/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Matrix.Reflection

/-!
# The weakly-coupled branch-pair Hamiltonian: a consistent CPT/mirror interbranch link

The AdS/C-P-T `C` is a two-outcome Everett branch label (`SciamaAdSCPTEverettBranches`), and the electron/
positron carrier is the CPT/mirror-trefoil double `(ψ_b, K_b, Q_b) ↦ (Θ_CPT ψ_b, K̄_b, −Q_b)`
(`Particles.PositronModel`).  The clean way to couple a branch to its CPT partner is **not** to insert an
antiunitary charge-conjugation operator into a Hamiltonian, but to build the doubled carrier
`ℋ_b ⊕ ℋ_b̄` with a Hermitian `2×2` block Hamiltonian carrying a weak off-diagonal intertwiner:

`H_pair = [[H_b, εΔ], [εΔ†, H_b̄]]`.

This module formalizes that construction over an abstract operator ring `[Ring R] [StarRing R]` (`H_b, H_b̄, c`
are elements of `R`; the off-diagonal coupling is `c = εΔ`):

* `pairHamiltonian_isHermitian` — **Hermiticity**: `H_pair` is Hermitian whenever the diagonal branch
  Hamiltonians are self-adjoint (the `c / c†` off-diagonal makes the block automatically Hermitian), for **any**
  coupling `c` — no antiunitary operator in the Hamiltonian.
* `pairHamiltonian_zero_coupling` — **the `ε → 0` decoupling**: at zero coupling `H_pair` is block-diagonal, so
  local Standard-Model physics is unchanged in the decoupled limit (the interbranch link is a *new* term, off
  by default; `Particles.PositronModel.exists_arbitrarily_weak_nonzero_branch_mix` supplies the arbitrarily
  weak nonzero amplitudes).
* `pairHamiltonian_branchSwap_covariant` — **CPT / branch-exchange covariance**: conjugating by the branch swap
  `S = [[0,1],[1,0]]` exchanges the two branch Hamiltonians and conjugates the coupling,
  `S H_pair S = [[H_b̄, c†],[c, H_b]]` — the `b ↔ b̄` symmetry of the pair.
* `interbranchChargeTransfer` / `neutral_portal` / `charged_no_neutral_portal` — **charge bookkeeping**: since
  the partner carries `−Q_b`, a `b → b̄` link transfers charge `Q_b − (−Q_b) = 2Q_b`, so it conserves charge iff
  the sector is neutral (`2Q_b = 0`).  A charged sector (`Q_b ≠ 0` in `ℤ`) admits **no** charge-neutral portal:
  a charged electron cannot simply disappear into its branch partner; only neutral states (neutrinos, neutral
  mesons, photons) provide a clean portal, or the link must transfer a compensating pair.

CAR preservation of the doubled carrier is the existing
`Particles.PositronModel.weakBranchLink_preserves_inner` (the `u²+v²=1` Nambu–Bogoliubov rotation), reused here
rather than duplicated.

Honest scope: this proves the doubled branch-pair link is **internally consistent** — Hermitian, CPT/branch-
exchange covariant, decoupling at `ε → 0`, and charge-neutral exactly on neutral sectors.  It does **not** derive
that every fermion possesses such a link, nor its coupling strength `ε` or phase: "every fermion has a weak link
to another branch" remains a **new conditional dynamical law**, constrained — not implied — by the trefoil and
spinor topology.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchPairHamiltonian

open scoped Matrix

variable {R : Type*} [Ring R] [StarRing R]

/-- The doubled branch-pair Hamiltonian `[[H_b, c], [c†, H_b̄]]` on `ℋ_b ⊕ ℋ_b̄`, with interbranch coupling
`c = εΔ` (`c†` its adjoint). -/
def pairHamiltonian (Hb Hbbar c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![Hb, c; star c, Hbbar]

/-- **[Hermiticity] `H_pair` is Hermitian if both branch Hamiltonians are self-adjoint.**  The `c / c†`
off-diagonal makes the block automatically Hermitian for any coupling `c` — no antiunitary operator enters. -/
theorem pairHamiltonian_isHermitian {Hb Hbbar c : R}
    (hb : IsSelfAdjoint Hb) (hbbar : IsSelfAdjoint Hbbar) :
    (pairHamiltonian Hb Hbbar c).IsHermitian := by
  show (pairHamiltonian Hb Hbbar c)ᴴ = pairHamiltonian Hb Hbbar c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairHamiltonian, Matrix.conjTranspose_apply, hb.star_eq, hbbar.star_eq, star_star]

/-- **[The `ε → 0` decoupling] zero coupling gives a block-diagonal Hamiltonian.**  With `c = 0` the branches do
not interact — local physics is unchanged in the decoupled limit; the link is an off-by-default new term. -/
theorem pairHamiltonian_zero_coupling (Hb Hbbar : R) :
    pairHamiltonian Hb Hbbar 0 = !![Hb, 0; 0, Hbbar] := by
  simp [pairHamiltonian, star_zero]

/-- The branch-exchange operator `S = [[0,1],[1,0]]` swapping `b ↔ b̄`. -/
def branchSwap : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- **[CPT / branch-exchange covariance] `S H_pair S = [[H_b̄, c†],[c, H_b]]`.**  Conjugating by the branch swap
exchanges the two branch Hamiltonians and conjugates the coupling — the `b ↔ b̄` symmetry of the pair. -/
theorem pairHamiltonian_branchSwap_covariant (Hb Hbbar c : R) :
    branchSwap * pairHamiltonian Hb Hbbar c * branchSwap = pairHamiltonian Hbbar Hb (star c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchSwap, pairHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, star_star]

/-! ## Charge bookkeeping: the neutral portal -/

section Charge

variable {Q : Type*} [AddGroup Q]

/-- The additive charge a `b → b̄` interbranch coupling must transfer: `Q_b − Q_{b̄} = Q_b − (−Q_b)`. -/
def interbranchChargeTransfer (Qb : Q) : Q := Qb - (-Qb)

/-- **[The transferred charge is `2Q_b`] `Q_b − (−Q_b) = Q_b + Q_b`.** -/
theorem interbranchChargeTransfer_eq (Qb : Q) : interbranchChargeTransfer Qb = Qb + Qb := by
  rw [interbranchChargeTransfer, sub_neg_eq_add]

/-- **[Neutral portal] the interbranch coupling conserves charge iff the sector is neutral (`2Q_b = 0`).** -/
theorem neutral_portal (Qb : Q) : interbranchChargeTransfer Qb = 0 ↔ Qb + Qb = 0 := by
  rw [interbranchChargeTransfer_eq]

end Charge

/-- **[A charged sector admits no neutral portal] `Q_b ≠ 0 ⟹ 2Q_b ≠ 0` (electric charge in `ℤ`).**  A charged
electron cannot simply disappear into its branch partner: the link must carry compensating charge or transfer a
charge-neutral particle–antiparticle pair. -/
theorem charged_no_neutral_portal (Qb : ℤ) (h : Qb ≠ 0) : interbranchChargeTransfer Qb ≠ 0 := by
  rw [interbranchChargeTransfer_eq]
  omega

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchPairHamiltonian

end
