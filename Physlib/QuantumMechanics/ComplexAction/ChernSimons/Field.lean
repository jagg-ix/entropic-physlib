/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.PartitionFunction

/-!
# Wiring the modular `S`-matrix into the Hayashi Bose/Fermi field bridge

Feeds the new `S`-matrix results into concrete instances of the Hayashi structures that the
Bose/Fermi field-operator bridge consumes, so the field operators **use** the `S`-matrix:

* `cswSMatrixOrthogonalityCarrier`: a `HayashiOrthogonalityCarrier` whose inner product is the genuine
  `S`-column overlap `Σ_a \overline{S_{aψ}} S_{aφ}` — orthogonality of distinct charge sectors is *derived*
  from `S`-unitarity (`cswSMatrix_colOrthogonal`), not posited.
* `cswSMatrix_orthogonality_kalnay_fields`: distinct `S`-charge sectors are orthogonal **and** include the
  Kálnay Bose-bilinear fermion-field statement — the field-bridge consumption of the orthogonality structure.
* `cswSMatrixDiagonalInvariant` / `cswSMatrix_invariant_kalnay_fields`: the `S`-matrix column as a torus
  character gives a `TopologicalInvariantFactorization`; fed through
  `hayashi_invariant_factorization_kalnay_bose_fermi_fields`, the genus-one `|S_{·q}|²` invariant includes the
  Kálnay fields.

## References

* Hayashi (CSW-gravity torus theorem, §F field-operator links); Kálnay (Bose-bilinear fermions). `Physlib`
  (`cswSMatrix_colOrthogonal`, `torusDiagonalInvariant`, `hayashi_*_kalnay_bose_fermi_fields`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — the `S`-matrix orthogonality structure -/

/-- **The `S`-matrix orthogonality structure.** States are charge labels `Fin k`; the inner product is the
genuine `S`-column overlap `Σ_a \overline{S_{aψ}} S_{aφ}`. Distinct charges are orthogonal *because* `S` is
unitary (`cswSMatrix_colOrthogonal`), realizing `HayashiOrthogonalityCarrier` concretely. -/
noncomputable def cswSMatrixOrthogonalityCarrier (k : ℕ) (hk : 0 < k) :
    HayashiOrthogonalityCarrier (Fin k) (Fin k) where
  inner ψ φ := ∑ a : Fin k, (starRingEnd ℂ) (cswSMatrix k a ψ) * cswSMatrix k a φ
  charge ψ := ψ
  orthogonal_of_charge_ne ψ φ h := by rw [cswSMatrix_colOrthogonal k hk ψ φ, if_neg h]

/-- **[The structure inner product is the Kronecker delta]** `⟨ψ, φ⟩ = δ_{ψφ}` — the `S`-columns are an
orthonormal character basis. -/
theorem cswSMatrixOrthogonalityCarrier_inner (k : ℕ) (hk : 0 < k) (ψ φ : Fin k) :
    (cswSMatrixOrthogonalityCarrier k hk).inner ψ φ = if ψ = φ then 1 else 0 :=
  cswSMatrix_colOrthogonal k hk ψ φ

/-- **[`S`-orthogonality includes the Kálnay Bose/Fermi fields]** distinct `S`-charge sectors are orthogonal
and, in the same statement, the Kálnay Bose-bilinear fermion-field operators satisfy their CAR statement. -/
theorem cswSMatrix_orthogonality_kalnay_fields (k : ℕ) (hk : 0 < k) (ψ φ : Fin k) (h : ψ ≠ φ)
    (p : Momentum 3) :
    (cswSMatrixOrthogonalityCarrier k hk).inner ψ φ = 0 ∧ KalnayBoseFermiFieldStatement p :=
  ⟨orthogonal_of_charge_ne (cswSMatrixOrthogonalityCarrier k hk) ψ φ h,
    kalnay_bose_fermi_field_statement p⟩

/-! ## §B — the `S`-column diagonal invariant -/

/-- **The `S`-column genus-one diagonal invariant.** Using the `q`-th `S`-matrix column `a ↦ S_{aq}` as a
torus character, the diagonal modular invariant `|S_{·q}|²` factorizes into the holomorphic and
anti-holomorphic characters — a `TopologicalInvariantFactorization` built from the `S`-matrix. -/
noncomputable def cswSMatrixDiagonalInvariant (k : ℕ) (q : Fin k) :
    TopologicalInvariantFactorization (Fin k) ℂ :=
  torusDiagonalInvariant k (fun a => cswSMatrix k a q)

/-- **[The `S`-column invariant includes the Kálnay Bose/Fermi fields]** the genus-one `|S_{·q}|²` invariant
factorizes and, in the same statement, includes the Kálnay Bose-bilinear fermion-field operators — the
field-bridge consumption of the `S`-matrix invariant. -/
theorem cswSMatrix_invariant_kalnay_fields (k : ℕ) (q O : Fin k) (p : Momentum 3) :
    (cswSMatrixDiagonalInvariant k q).complexInvariant O
        = (cswSMatrixDiagonalInvariant k q).rightInvariant O
          * (cswSMatrixDiagonalInvariant k q).leftInvariant O
      ∧ KalnayBoseFermiFieldStatement p :=
  hayashi_invariant_factorization_kalnay_bose_fermi_fields (cswSMatrixDiagonalInvariant k q) O p

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
