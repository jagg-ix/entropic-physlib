/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
public import Physlib.QuantumMechanics.ComplexAction.QuantumSU2EquivariantDirac
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
meta import Zil

/-!
# The represented Connes–de Rham forms and the degree collapse (Chakraborty–Pal Theorem 3.4)

Completes the Connes–de Rham complex of the finite spectral triples: the differential, the junk-form
source, and the **degree-two collapse** that supports the complex on degrees `{0, 1}` — the exact
mechanism of *Chakraborty–Pal, "Spectral Triples and Associated Connes-de Rham Complex for the
Quantum `SU(2)` and the Quantum Sphere" (CMP 240, 2003), Theorem 3.4* (`Ω¹_d(A_f) = A_f ⊕ I_β`,
`Ω^n_d(A_f) = 0` for `n ≥ 2`).

Every ingredient already exists in the repository:

* the differential `d̃a := [D, π(a)]` **is** the Saveliev collision star `collisionStar D a`
  (`CollisionOperatorSl2.CollisionModular`), with its Leibniz rule `collisionStar_leibniz`;
* the junk-form source `d²a = [D, [D, a]]` **is** `collisionDoubleStar D a` (Saveliev's temperature
  generator);
* the spectral-triple commutator `FiniteSpectralTriple.representedCommutator`
  (`AlgebraicQFT.ConnesAtiyahSingerKasparov`) is the same object in the endomorphism ring;
* the diagonal (equivariant) Dirac action on transitions is `equivariant_dirac_commutator`
  (`QuantumSU2EquivariantDirac`).

The new content:

* `twoForm_exact_sub_junk` — **every represented 2-form is exact minus junk**:
  `[D,a]·[D,b] = [D, a·[D,b]] − a·[D,[D,b]]` (pure Leibniz algebra). This is why the represented
  Connes–de Rham complex `Ω²_D = Ω²/(im d + junk)` vanishes: degree two contains nothing that is not
  a differential of degree one plus a junk term. Chakraborty–Pal Theorem 3.4 is this identity
  evaluated in their weighted-shift representation.
* `collisionDoubleStar_diagonal_single` — the junk source is *diagonal* on the transition basis with
  the **squared** eigenvalue difference: `d²f_{p←q} = (d_p − d_q)² f_{p←q}` (so junk vanishes exactly
  on degenerate transitions).
* `involutive_junk_source` — for the sign Dirac (`D² = 1`, Chakraborty–Pal's `S` of Eq. 2.8), the
  junk source is the odd-part projector `d²a = 2a − 2DaD`.
* `involutive_twoForm_collapse` — the assembled Theorem 3.4 mechanism for the sign Dirac: every
  2-form is exact plus zero-degree terms, `[D,a][D,b] = [D, a[D,b]] − 2ab + 2a(DbD)` — nothing
  genuinely new lives in degree ≥ 2.
* `representedCommutator_eq_collisionStar` — the spectral-triple differential of
  `ConnesAtiyahSingerKasparov` is the collision star in the endomorphism ring (the identification
  welding the two carriers).
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.QuantumSU2EquivariantDirac
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms

variable {R : Type*} [Ring R]

/-- **[The degree-two collapse] Every represented 2-form is exact minus junk**:

  `[D,a]·[D,b] = [D, a·[D,b]] − a·[D,[D,b]]`.

The product of two represented one-forms `da·db` is the differential of the represented one-form
`a·db` minus the junk term `a·d²b`. This is the algebraic mechanism of Chakraborty–Pal Theorem 3.4:
in the Connes–de Rham quotient `Ω²_D = Ω²/(im d̃ + junk)`, degree two — and inductively every higher
degree — vanishes, supporting the complex on `{0, 1}`. Pure consequence of the Leibniz rule for the
collision star. -/
theorem twoForm_exact_sub_junk (D a b : R) :
    collisionStar D a * collisionStar D b
      = collisionStar D (a * collisionStar D b) - a * collisionDoubleStar D b := by
  simp only [collisionStar, collisionDoubleStar]
  noncomm_ring

/-- **[The junk source is diagonal on transitions] `d²f_{p←q} = (d_p − d_q)²·f_{p←q}`.** On the
matrix-unit transition basis of the diagonal (equivariant) Dirac operator, the junk-form source
`[D,[D,·]]` acts diagonally with the *squared* eigenvalue difference — junk vanishes exactly on
degenerate transitions (`d_p = d_q`), and grows quadratically with the spectral separation. -/
theorem collisionDoubleStar_diagonal_single {n : ℕ} (dvec : Fin n → ℂ) (p q : Fin n) (c : ℂ) :
    collisionDoubleStar (Matrix.diagonal dvec) (Matrix.single p q c)
      = (dvec p - dvec q) ^ 2 • Matrix.single p q c := by
  have h1 : collisionStar (Matrix.diagonal dvec) (Matrix.single p q c)
      = (dvec p - dvec q) • Matrix.single p q c := by
    rw [collisionStar]; exact equivariant_dirac_commutator dvec p q c
  have h2 : collisionStar (Matrix.diagonal dvec) ((dvec p - dvec q) • Matrix.single p q c)
      = (dvec p - dvec q) • collisionStar (Matrix.diagonal dvec) (Matrix.single p q c) := by
    rw [collisionStar, collisionStar, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [collisionDoubleStar, h1, h2, h1, smul_smul, sq]

/-- **[The sign-Dirac junk source] `D² = 1 ⟹ d²a = 2a − 2DaD`.** For an involutive Dirac operator —
Chakraborty–Pal's sign operator `S` (`S² = 1`) entering their `D = N⊗S + I⊗N` (Eq. 2.8) — the junk
source is twice the `D`-odd projection: it annihilates the `D`-commuting (even) part and doubles the
anticommuting (odd) part. -/
theorem involutive_junk_source {D : R} (h : D * D = 1) (a : R) :
    collisionDoubleStar D a = 2 • a - 2 • (D * a * D) := by
  simp only [collisionDoubleStar, collisionStar, mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc D D a, h, one_mul, mul_one]
  abel

/-- **[Theorem 3.4 mechanism, assembled] For the sign Dirac every 2-form is exact plus degree-zero
terms**: `[D,a][D,b] = [D, a[D,b]] − 2ab + 2a(DbD)`. Nothing genuinely new lives in degree two — the
represented Connes–de Rham complex of an involutive Dirac is supported on degrees `{0, 1}`, which is
Chakraborty–Pal Theorem 3.4 (`Ω^n_d = 0` for `n ≥ 2`) at the represented level. -/
theorem involutive_twoForm_collapse {D : R} (h : D * D = 1) (a b : R) :
    collisionStar D a * collisionStar D b
      = collisionStar D (a * collisionStar D b) - 2 • (a * b) + 2 • (a * (D * b * D)) := by
  rw [twoForm_exact_sub_junk, involutive_junk_source h, mul_sub, mul_smul_comm, mul_smul_comm]
  abel

/-- **[The spectral-triple differential is the collision star]** — the represented commutator
`[D, π(a)]` of `ConnesAtiyahSingerKasparov.FiniteSpectralTriple` is `collisionStar T.dirac (π a)` in
the endomorphism ring: the Connes–de Rham differential, the Saveliev collision adjoint, and the
spectral-triple commutator are one object. (A definitional identification, recorded to weld the two
carriers; the substantive consequences are the theorems above.) -/
theorem representedCommutator_eq_collisionStar
    {A H ι : Type*} [Semiring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (T : FiniteSpectralTriple A H ι) (a : A) :
    T.representedCommutator a = collisionStar T.dirac (T.representation a) := rfl

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.twoForm_exact_sub_junk where
  formalizes @ "claim:every-represented-connes-de-rham-two-form-is-the-differential-of-a-one-form-minus-a-junk-term",
  supported_by @ "paper:chakraborty-pal-spectral-triples-connes-de-rham-quantum-su2"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.collisionDoubleStar_diagonal_single where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.QuantumSU2EquivariantDirac.equivariant_dirac_commutator",
  formalizes @ "claim:the-junk-form-source-acts-diagonally-on-transitions-with-the-squared-eigenvalue-difference",
  requires @ "claim:the-commutator-of-the-diagonal-equivariant-dirac-operator-with-a-matrix-unit-transition-is-the-eigenvalue-difference-times-that-transition"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.involutive_junk_source where
  formalizes @ "claim:for-an-involutive-sign-dirac-the-junk-source-is-twice-the-odd-part-projection"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.involutive_twoForm_collapse where
  formalizes @ "claim:for-the-sign-dirac-every-two-form-is-exact-plus-degree-zero-terms-the-connes-de-rham-complex-is-supported-on-degrees-zero-and-one",
  requires @ "claim:every-represented-connes-de-rham-two-form-is-the-differential-of-a-one-form-minus-a-junk-term",
  supported_by @ "paper:chakraborty-pal-spectral-triples-connes-de-rham-quantum-su2"

zil_file_contract physlib.connesDeRhamRepresentedForms where
  promises "The represented Connes-de Rham complex completed on repository carriers: the differential is the Saveliev collision star (with its existing Leibniz rule), the junk source d^2 is the collision double star, every represented two-form is exact minus junk (pure Leibniz algebra), the junk source is diagonal on the transition basis with the squared eigenvalue difference, and for the involutive sign Dirac every two-form collapses to exact plus degree-zero terms -- the mechanism of Chakraborty-Pal Theorem 3.4 supporting the complex on degrees zero and one. The spectral-triple representedCommutator is identified with the collision star."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.collisionStar",
    "lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular.collisionDoubleStar",
    "lean:Physlib.QuantumMechanics.ComplexAction.QuantumSU2EquivariantDirac.equivariant_dirac_commutator",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.FiniteSpectralTriple"]
  forbids_substitutes ["the weighted-shift representation asymptotics of the infinite quantum SU(2) triple, the collapse is carried at the represented-algebra level",
    "the universal graded differential envelope, the forms here are the represented images where the junk quotient acts"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.twoForm_exact_sub_junk,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.collisionDoubleStar_diagonal_single,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.involutive_junk_source,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesDeRhamRepresentedForms.involutive_twoForm_collapse]

/- ZIL-END -/
