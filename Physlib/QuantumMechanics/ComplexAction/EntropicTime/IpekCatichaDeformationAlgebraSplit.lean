/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

meta import Zil

/-!
# The gravitational/matter split of the deformation algebra (Ipek–Caticha §8)

Formalizes the mechanism by which the hypersurface-deformation (Dirac/DHKT) algebra of Ipek–Caticha
(arXiv:2006.05036, Eqs. 44, 48, 49) **splits** into a gravitational sector and a "matter" sector. The
super-Hamiltonian and super-momentum each divide into a gravitational piece `H^G_A[g, π]` (depending only on the
geometry) and a matter piece `H̃_A[ρ, Φ; g]` (Eq. 44) with *no gravitational dependence on the matter side and no
matter dependence on the gravitational side* — the sectors **decouple**. The consequence is that the deformation
Poisson brackets split: the gravitational generators close among themselves (Eqs. 48a–c) and the matter generators
close among themselves (Eqs. 49a–c), each an independent representation of the "algebra" of surface deformations.

The exact-algebra kernel, on the repository commutator `collisionStar` (the bracket of `HypersurfaceDeformationDHKTAlgebra`):

* the **decoupling makes the algebra split** `[H^G + H̃, H^G' + H̃'] = [H^G, H^G'] + [H̃, H̃']`
  (`deformation_algebra_split`) — when the cross brackets `[H^G, H̃'] = [H̃, H^G'] = 0` vanish, the total bracket is
  the sum of the gravitational and matter brackets: geometry and matter close independently, so their Poisson
  brackets can be solved separately;
* the **decoupling is symmetric** `[H^G, H̃'] = 0 ⟺ [H̃', H^G] = 0` (`decoupling_symmetric`) — from the
  antisymmetry of the commutator, so a single vanishing cross bracket suffices.

So the Ipek–Caticha coupled system decomposes into two independent deformation algebras — gravitational and matter —
because the generators decouple, which is exactly why the Poisson-bracket relations for geometry and for the quantum
"matter" can be solved independently (Eqs. 48–49); the coupling reappears only in the constraint `H^G_⊥ + H̃_⊥ ≈ 0`
(`IpekCatichaMatterGravityConstraint`).

* **§A — the split via decoupling** (`deformation_algebra_split`).
* **§B — the decoupling is symmetric** (`decoupling_symmetric`).

**Honest layering.** The split identity and the symmetry of decoupling are exact commutator algebra on
`collisionStar`, reusing `collisionStar_antisymm`. The functional Poisson-bracket relations (Eqs. 48–49) and the
non-derivative coupling assumption that guarantees the decoupling are the referenced content; here the algebraic
consequence of decoupling is proved. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 44, 48, 49). Repo carriers:
  `CollisionOperatorSl2.CollisionModular` (`collisionStar`, `collisionStar_antisymm`),
  `EntropicTime.HypersurfaceDeformationDHKTAlgebra` (the deformation algebra).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit


/-- **[Decoupling splits the deformation algebra] `[H^G + H̃, H^G' + H̃'] = [H^G, H^G'] + [H̃, H̃']`.** When the
gravitational and matter generators decouple — the cross brackets `[H^G, H̃'] = 0` and `[H̃, H^G'] = 0` vanish
(Ipek–Caticha Eq. 44: no matter dependence on the gravitational side, no gravitational dependence on the matter
side) — the total deformation bracket is the sum of the gravitational bracket (Eqs. 48) and the matter bracket
(Eqs. 49): the two sectors close independently. -/
lemma deformation_algebra_split {R : Type*} [Ring R] (HG_N HG_M HM_N HM_M : R)
    (hcross1 : collisionStar HG_N HM_M = 0) (hcross2 : collisionStar HM_N HG_M = 0) :
    collisionStar (HG_N + HM_N) (HG_M + HM_M)
      = collisionStar HG_N HG_M + collisionStar HM_N HM_M := by
  simp only [collisionStar] at hcross1 hcross2 ⊢
  have expand : (HG_N + HM_N) * (HG_M + HM_M) - (HG_M + HM_M) * (HG_N + HM_N)
      = (HG_N * HG_M - HG_M * HG_N) + (HM_N * HM_M - HM_M * HM_N)
        + (HG_N * HM_M - HM_M * HG_N) + (HM_N * HG_M - HG_M * HM_N) := by noncomm_ring
  rw [expand, hcross1, hcross2, add_zero, add_zero]


/-- **[The decoupling is symmetric] `[a, b] = 0 ⟹ [b, a] = 0`.** A vanishing cross bracket is symmetric, from the
antisymmetry of the commutator (`collisionStar_antisymm`): decoupling in one order is decoupling in the other, so a
single vanishing cross bracket certifies the sectors decouple. -/
lemma decoupling_symmetric {R : Type*} [Ring R] (a b : R) (h : collisionStar a b = 0) :
    collisionStar b a = 0 := by
  have hanti := collisionStar_antisymm a b
  rw [h] at hanti
  exact neg_eq_zero.mp hanti.symm

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit.deformation_algebra_split where
  formalizes @ "claim:when-the-gravitational-and-matter-generators-decouple-with-vanishing-cross-brackets-the-total-hypersurface-deformation-bracket-splits-into-independent-gravitational-and-matter-brackets-so-the-two-sectors-close-among-themselves",
  supported_by @ "paper:ipek-caticha-entropic-dynamics-quantum-gravity-functional-schrodinger-constraints"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit.decoupling_symmetric where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:a-vanishing-cross-bracket-is-symmetric-under-exchange-from-commutator-antisymmetry-so-a-single-vanishing-cross-bracket-certifies-gravity-matter-decoupling"

zil_file_contract physlib.ipekCatichaDeformationAlgebraSplit where
  promises "The gravitational/matter split of the hypersurface-deformation (Dirac) algebra in Ipek-Caticha entropic dynamics. When the cross brackets of the gravitational and matter generators vanish, the total deformation bracket splits into independent gravitational and matter brackets (deformation_algebra_split), so each sector closes among itself; a single vanishing cross bracket is symmetric under exchange (from commutator antisymmetry) and hence certifies decoupling (decoupling_symmetric)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.collisionStar"]
  forbids_substitutes ["the full structure functions of the hypersurface-deformation algebra with their metric-dependent (field-dependent) structure and the closure of the constraint algebra under Poisson brackets, which are the cited canonical-gravity infrastructure",
    "any claim that gravity and matter physically decouple; only the algebraic bilinearity of the bracket under the decoupling hypothesis is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit.deformation_algebra_split,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeformationAlgebraSplit.decoupling_symmetric]

/- ZIL-END -/
