/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Quantum chemistry from the particle archive: the second-quantized electronic Hamiltonian

The architecture `ParticleArchive → QEDSector → NonRelativisticLimit → BornOppenheimer → BasisExpansion →
SecondQuantizedHamiltonian → SolverTarget`. One does **not** simulate quarks and gluons: they are compressed
into effective **nuclear data** `(M_A, Z_A, μ_A, I_A)`, and chemistry is the low-energy QED sector of
electrons + nuclei + photons. This file isolates the *algebraically verifiable* backbone of that pipeline.

* **§A — the archive → effective nuclear data.** `NuclearData` `(M_A, Z_A, μ_A, 2I_A)` — the compression of
  the strong-sector archive into the parameters chemistry needs.
* **§B — the Born–Oppenheimer hierarchy.** `bornOppenheimerParameter me N = m_e/M_A`; for `m_e < M_A` it is
  `< 1` (`bornOppenheimer_small`) and decreases with nuclear mass (`bornOppenheimer_antitone`) — heavier
  nuclei are more nearly clamped, the basis of fixing the nuclei classically.
* **§C — the second-quantized electronic Hamiltonian** `Ĥ = Σ h_pq a†_p a_q + ½ Σ g_pqrs a†_p a†_q a_s a_r
  + E_NN` (the central object of quantum-chemistry algorithms), on an abstract `ℂ`-`*`-algebra with
  `a†_p = crea p`, `a_p = (crea p)*`. **Self-adjointness** `Ĥ† = Ĥ` follows from the Hermiticity of the
  one-electron integrals (`h_pq = h̄_qp`), the symmetry of the two-electron integrals (`g_pqrs = ḡ_rspq`), and
  real nuclear repulsion: `oneBody_self_adjoint`, `twoBody_self_adjoint`, and the main result
  `SecondQuantizedElectronicHamiltonian.hamiltonian_self_adjoint`.

**Honest layering.** Proven: the nuclear-data compression as a datatype, the Born–Oppenheimer mass inequality,
and the self-adjointness of the second-quantized Hamiltonian from the integral symmetries — the structural
invariant every solver relies on. The orbital integrals `h_pq, g_pqrs` themselves (`∫φ*∇²φ`, `∫∫φ*φ*/r₁₂ φφ`),
the QED→Schrödinger reduction, the CAR relations of `crea` (here `crea` is an abstract `*`-algebra family; the
electron Fock operators of `Fermion.FockFunctor` are a concrete instance), and the variational solution are
not derived here.

## References

* P. Jordan, E. Wigner (second quantization); A. Szabo, N. S. Ostlund, *Modern Quantum Chemistry* (1996) —
  the electronic Hamiltonian `Σ h_pq a†_p a_q + ½ Σ g_pqrs a†_p a†_q a_s a_r`; M. Born, R. Oppenheimer, Ann.
  Phys. **389** (1927) 457, doi:10.1002/andp.19273892002. `Physlib` (`Fermion.FockFunctor`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive


/-- **Effective nuclear data** — the compression of the quark/gluon archive into the four parameters
chemistry needs: nuclear mass `M_A`, charge number `Z_A` (in units of `e`), magnetic moment `μ_A`, and twice
the nuclear spin `2 I_A` (an integer). One does not simulate the strong sector; one *reads off* this tuple. -/
structure NuclearData where
  /-- Nuclear mass `M_A`. -/
  mass : ℝ
  /-- Nuclear charge number `Z_A`. -/
  charge : ℤ
  /-- Nuclear magnetic moment `μ_A`. -/
  magneticMoment : ℝ
  /-- Twice the nuclear spin, `2 I_A` (integer; even = boson, odd = fermion nucleus). -/
  spinDoubled : ℕ


/-- The **Born–Oppenheimer small parameter** `m_e / M_A` — the ratio controlling the nuclear/electronic
separation; `M_A ≫ m_e` makes it small, so the nuclei are treated as clamped classical parameters. -/
noncomputable def bornOppenheimerParameter (me : ℝ) (N : NuclearData) : ℝ := me / N.mass

/-- **[Born–Oppenheimer smallness]** `m_e / M_A < 1` when `0 < m_e < M_A` — the nuclear kinetic energy is
suppressed relative to the electronic, justifying clamped nuclei. -/
lemma bornOppenheimer_small (me : ℝ) (N : NuclearData) (hme : 0 < me) (h : me < N.mass) :
    bornOppenheimerParameter me N < 1 := by
  rw [bornOppenheimerParameter, div_lt_one (lt_trans hme h)]; exact h

/-- **[Heavier nuclei are more clamped]** `m_e/M_B ≤ m_e/M_A` when `0 < M_A ≤ M_B` — the Born–Oppenheimer
parameter decreases with nuclear mass. -/
lemma bornOppenheimer_antitone (me : ℝ) (N M : NuclearData) (hme : 0 ≤ me) (hN : 0 < N.mass)
    (h : N.mass ≤ M.mass) :
    bornOppenheimerParameter me M ≤ bornOppenheimerParameter me N := by
  unfold bornOppenheimerParameter; gcongr


variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι] (crea : ι → A)

/-- The **one-electron (core) term** `Σ_{pq} h_pq a†_p a_q`, with `a†_p = crea p`, `a_q = (crea q)*`. -/
noncomputable def oneBody (h : ι → ι → ℂ) : A := ∑ p, ∑ q, h p q • (crea p * star (crea q))

/-- The swap of the two electron labels `(p,q,r,s) ↦ (r,s,p,q)` (an involution). -/
def swap4 (x : ι × ι × ι × ι) : ι × ι × ι × ι := (x.2.2.1, x.2.2.2, x.1, x.2.1)

omit [Fintype ι] in
lemma swap4_involutive : Function.Involutive (swap4 (ι := ι)) := fun _ => rfl

/-- The two-electron monomial `g_pqrs a†_p a†_q a_s a_r` at `x = (p,q,r,s)`. -/
noncomputable def twoBodyTerm (g : ι → ι → ι → ι → ℂ) (x : ι × ι × ι × ι) : A :=
  g x.1 x.2.1 x.2.2.1 x.2.2.2 •
    (crea x.1 * crea x.2.1 * star (crea x.2.2.2) * star (crea x.2.2.1))

/-- The **two-electron (Coulomb) term** `½ Σ_{pqrs} g_pqrs a†_p a†_q a_s a_r`. -/
noncomputable def twoBody (g : ι → ι → ι → ι → ℂ) : A :=
  ((1 / 2 : ℝ) : ℂ) • ∑ x : ι × ι × ι × ι, twoBodyTerm crea g x

/-- **[The one-electron term is self-adjoint]** `(Σ h_pq a†_p a_q)† = Σ h_pq a†_p a_q` given the **Hermitian
one-electron integrals** `h_pq = h̄_qp` (`star (h p q) = h q p`). -/
lemma oneBody_self_adjoint (h : ι → ι → ℂ) (hh : ∀ p q, star (h p q) = h q p) :
    star (oneBody crea h) = oneBody crea h := by
  unfold oneBody
  simp only [star_sum, star_smul, star_mul, star_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hh]

omit [Fintype ι] in
/-- **[A two-electron monomial maps to its swapped partner under `†`]** `(g_pqrs a†_p a†_q a_s a_r)† =
g_rspq a†_r a†_s a_q a_p`, using the **symmetry of the two-electron integrals** `g_pqrs = ḡ_rspq`. -/
lemma star_twoBodyTerm (g : ι → ι → ι → ι → ℂ) (hg : ∀ p q r s, star (g p q r s) = g r s p q)
    (x : ι × ι × ι × ι) :
    star (twoBodyTerm crea g x) = twoBodyTerm crea g (swap4 x) := by
  simp only [twoBodyTerm, swap4, star_smul, star_mul, star_star, mul_assoc]
  rw [hg]

/-- **[The two-electron term is self-adjoint]** `(½ Σ g_pqrs a†_p a†_q a_s a_r)† = ½ Σ g_pqrs a†_p a†_q a_s a_r`
given the two-electron-integral symmetry `g_pqrs = ḡ_rspq` (which the real Coulomb kernel `1/r₁₂` enforces). -/
lemma twoBody_self_adjoint (g : ι → ι → ι → ι → ℂ) (hg : ∀ p q r s, star (g p q r s) = g r s p q) :
    star (twoBody crea g) = twoBody crea g := by
  unfold twoBody
  rw [star_smul, star_sum, show star (((1 / 2 : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) from by simp]
  rw [Finset.sum_congr rfl fun x _ => star_twoBodyTerm crea g hg x]
  rw [swap4_involutive.bijective.sum_comp (twoBodyTerm crea g)]


/-- A **second-quantized electronic-structure problem** (the `SolverTarget`): the orbital basis `crea`, the
one- and two-electron integrals `h_pq`, `g_pqrs` (Hermitian / Coulomb-symmetric), and the nuclear repulsion
`E_NN`. Generated from the particle archive via the QED → Born–Oppenheimer → basis-expansion pipeline. -/
structure SecondQuantizedElectronicHamiltonian (A : Type*) [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] (ι : Type*) [Fintype ι] where
  /-- Orbital creation operators `a†_p`. -/
  crea : ι → A
  /-- One-electron (core) integrals `h_pq`. -/
  oneBodyInt : ι → ι → ℂ
  /-- Two-electron (Coulomb) integrals `g_pqrs`. -/
  twoBodyInt : ι → ι → ι → ι → ℂ
  /-- Nuclear repulsion energy `E_NN`. -/
  nuclearRepulsion : ℝ
  /-- Hermiticity of the one-electron integrals `h_pq = h̄_qp`. -/
  h_herm : ∀ p q, star (oneBodyInt p q) = oneBodyInt q p
  /-- Coulomb symmetry of the two-electron integrals `g_pqrs = ḡ_rspq`. -/
  g_symm : ∀ p q r s, star (twoBodyInt p q r s) = twoBodyInt r s p q

namespace SecondQuantizedElectronicHamiltonian


/-- The **electronic Hamiltonian operator** `Ĥ = Σ h_pq a†_p a_q + ½ Σ g_pqrs a†_p a†_q a_s a_r + E_NN`. -/
noncomputable def hamiltonian (P : SecondQuantizedElectronicHamiltonian A ι) : A :=
  oneBody P.crea P.oneBodyInt + twoBody P.crea P.twoBodyInt
    + ((P.nuclearRepulsion : ℝ) : ℂ) • (1 : A)

/-- **[The electronic Hamiltonian is self-adjoint] `Ĥ† = Ĥ`** — the central invariant of every quantum-
chemistry solver, from the Hermitian one-electron integrals, the Coulomb-symmetric two-electron integrals, and
the real nuclear repulsion. -/
lemma hamiltonian_self_adjoint (P : SecondQuantizedElectronicHamiltonian A ι) :
    star P.hamiltonian = P.hamiltonian := by
  unfold hamiltonian
  rw [star_add, star_add, oneBody_self_adjoint P.crea P.oneBodyInt P.h_herm,
    twoBody_self_adjoint P.crea P.twoBodyInt P.g_symm, star_smul, star_one,
    show star (((P.nuclearRepulsion : ℝ) : ℂ)) = ((P.nuclearRepulsion : ℝ) : ℂ) from by simp]

end SecondQuantizedElectronicHamiltonian

end Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive

end
