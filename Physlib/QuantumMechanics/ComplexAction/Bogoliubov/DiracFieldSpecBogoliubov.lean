/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.Basic
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FermionicBogoliubovCAR

/-!
# Tier 2: the Dirac `FieldSpecification` and the Bogoliubov element in the field-operator algebra

`Bogoliubov.FermionicBogoliubovCAR` proved the second-quantized Bogoliubov canonicity on a concrete `4×4` Fock
space. This file connects that to physlib's **PhysLean `FieldSpecification` framework**
(`Physlib/QFT/PerturbationTheory/`): it instantiates a **Dirac field specification**, forms the
Bogoliubov transformation as an actual element of the **field-operator free algebra**
`FieldOpFreeAlgebra` (`= FreeAlgebra ℂ CrAnFieldOp`), and represents it on the `4×4` Fock space via the
**universal property** of the free algebra.

## The construction

* `diracFieldSpec : FieldSpecification` — one **fermionic** field (`Field = Unit`,
 `statistic = fermionic`), with `AsymptoticLabel = Bool` distinguishing **particle** (`false`) from
 **antiparticle** (`true`).
* The asymptotic creation/annihilation operators are the `CrAnFieldOp`s `outAsymp` (annihilation) and
 `inAsymp` (creation): `particleAnnihil`, `particleCreate`, `antiparticleAnnihil`,
 `antiparticleCreate`.
* `fockRep : CrAnFieldOp → Matrix (Fin 4) (Fin 4) ℂ` sends these to the Tier-1 Jordan–Wigner operators
 `aOp, a†, b, b†`; the **universal property** (`FreeAlgebra.lift`) extends it to an algebra
 homomorphism `fockRepHom : FieldOpFreeAlgebra diracFieldSpec →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ`.
* `bogElement u v p = u·a + v·b†` is the **Bogoliubov transformation as an element of the field-operator
 algebra**; `fockRepHom_bogElement` shows it represents to the Tier-1 `bogA u v`.

## The result

The abstract field-algebra Bogoliubov element's anticommutator represents to the canonical CAR:

 `fockRepHom (ã·ã† + ã†·ã) = (u² + v²)·1` (`fock_bogoliubov_CAR`),

so it is **canonical** (`= 1`) exactly when `u² + v² = 1` (`fw_fock_bogoliubov_canonical`), the
Foldy–Wouthuysen normalization. The Bogoliubov transformation, written in physlib's
`FieldOpFreeAlgebra` for a Dirac `FieldSpecification`, is a CAR automorphism in the Fock
representation.

## Scope (what this adds, and the remaining frontier)

This instantiates the PhysLean `FieldSpecification` framework and writes the Bogoliubov transformation
as a genuine `FieldOpFreeAlgebra` element, represented on the finite Fock space — Tier 2. The
`FieldOpFreeAlgebra` is the **free** algebra, so its `superCommuteF` is the *formal* graded commutator;
the *c-number* CAR `{ã,ã†}=1` is the property of the Fock **representation** built here. What remains
(Tier 3): the continuum field `ψ(x) = ∫ d³k [a_k u_k + b†_k v_k]` and the Bogoliubov automorphism of
the full CAR `C*`-algebra over the momentum continuum — a measure-theoretic / operator-algebra layer
beyond the finite representation.

## References

* physlib `QFT/PerturbationTheory/FieldSpecification`, `FieldOpFreeAlgebra` (PhysLean). This
 development: `Bogoliubov.FermionicBogoliubovCAR`, `Bogoliubov.FoldyWouthuysenBogoliubovIdentity`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix FieldSpecification FieldSpecification.FieldOpFreeAlgebra

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracFieldSpecBogoliubov

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FermionicBogoliubovCAR

/-! ## §A — the Dirac field specification (one fermionic field, particle/antiparticle) -/

/-- **The Dirac field specification**: one **fermionic** field, with `AsymptoticLabel = Bool`
distinguishing particle (`false`) from antiparticle (`true`). -/
def diracFieldSpec : FieldSpecification where
  Field := Unit
  PositionLabel := fun _ => Unit
  AsymptoticLabel := fun _ => Bool
  statistic := fun _ => FieldStatistic.fermionic

/-! ## §B — the asymptotic creation/annihilation operators -/

/-- The **particle annihilation** operator `a` (`outAsymp`, label `false`). -/
def particleAnnihil (p : Momentum 3) : diracFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.outAsymp (⟨(), false⟩, p), ()⟩

/-- The **particle creation** operator `a†` (`inAsymp`, label `false`). -/
def particleCreate (p : Momentum 3) : diracFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.inAsymp (⟨(), false⟩, p), ()⟩

/-- The **antiparticle annihilation** operator `b` (`outAsymp`, label `true`). -/
def antiparticleAnnihil (p : Momentum 3) : diracFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.outAsymp (⟨(), true⟩, p), ()⟩

/-- The **antiparticle creation** operator `b†` (`inAsymp`, label `true`). -/
def antiparticleCreate (p : Momentum 3) : diracFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.inAsymp (⟨(), true⟩, p), ()⟩

/-! ## §C — the Fock representation (the universal property) -/

/-- **The Fock representation map** sending each creation/annihilation `CrAnFieldOp` to the
Jordan–Wigner operator of `Bogoliubov.FermionicBogoliubovCAR` (particle ↔ `a`, antiparticle ↔ `b`; `inAsymp` ↔
creation, `outAsymp` ↔ annihilation); position operators to `0`. -/
def fockRep : diracFieldSpec.CrAnFieldOp → Matrix (Fin 4) (Fin 4) ℂ
  | ⟨FieldOp.inAsymp (⟨_, true⟩, _), _⟩ => bDagOp
  | ⟨FieldOp.inAsymp (⟨_, false⟩, _), _⟩ => aDagOp
  | ⟨FieldOp.outAsymp (⟨_, true⟩, _), _⟩ => bOp
  | ⟨FieldOp.outAsymp (⟨_, false⟩, _), _⟩ => aOp
  | ⟨FieldOp.position _, _⟩ => 0

/-- **The Fock representation algebra homomorphism** `FieldOpFreeAlgebra diracFieldSpec →ₐ[ℂ]
Matrix (Fin 4) (Fin 4) ℂ`, the unique algebra map extending `fockRep` (the universal property of the
free field-operator algebra). -/
noncomputable def fockRepHom :
    FieldOpFreeAlgebra diracFieldSpec →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  FreeAlgebra.lift ℂ fockRep

@[simp] theorem fockRepHom_ofCrAnOpF (φ : diracFieldSpec.CrAnFieldOp) :
    fockRepHom (ofCrAnOpF φ) = fockRep φ := by
  rw [fockRepHom, ofCrAnOpF, FreeAlgebra.lift_ι_apply]

@[simp] theorem fockRep_particleAnnihil (p : Momentum 3) : fockRep (particleAnnihil p) = aOp := rfl
@[simp] theorem fockRep_particleCreate (p : Momentum 3) : fockRep (particleCreate p) = aDagOp := rfl
@[simp] theorem fockRep_antiparticleAnnihil (p : Momentum 3) :
    fockRep (antiparticleAnnihil p) = bOp := rfl
@[simp] theorem fockRep_antiparticleCreate (p : Momentum 3) :
    fockRep (antiparticleCreate p) = bDagOp := rfl

/-! ## §D — the Bogoliubov transformation as a field-operator-algebra element -/

/-- **The Bogoliubov transformation in the field-operator algebra** `ã = u·a + v·b†` — an actual
element of `FieldOpFreeAlgebra diracFieldSpec`. -/
def bogElement (u v : ℂ) (p : Momentum 3) : FieldOpFreeAlgebra diracFieldSpec :=
  u • ofCrAnOpF (particleAnnihil p) + v • ofCrAnOpF (antiparticleCreate p)

/-- **Its conjugate** `ã† = u·a† + v·b`. -/
def bogElementDag (u v : ℂ) (p : Momentum 3) : FieldOpFreeAlgebra diracFieldSpec :=
  u • ofCrAnOpF (particleCreate p) + v • ofCrAnOpF (antiparticleAnnihil p)

/-- **The Bogoliubov field-algebra element represents to the Tier-1 operator** `bogA u v`. -/
theorem fockRepHom_bogElement (u v : ℂ) (p : Momentum 3) :
    fockRepHom (bogElement u v p) = bogA u v := by
  rw [bogElement, map_add, map_smul, map_smul, fockRepHom_ofCrAnOpF, fockRepHom_ofCrAnOpF,
    fockRep_particleAnnihil, fockRep_antiparticleCreate, bogA]

/-- **Its conjugate represents to** `bogADag u v`. -/
theorem fockRepHom_bogElementDag (u v : ℂ) (p : Momentum 3) :
    fockRepHom (bogElementDag u v p) = bogADag u v := by
  rw [bogElementDag, map_add, map_smul, map_smul, fockRepHom_ofCrAnOpF, fockRepHom_ofCrAnOpF,
    fockRep_particleCreate, fockRep_antiparticleAnnihil, bogADag]

/-! ## §E — the canonical anticommutation relation in the Fock representation -/

/-- **The field-algebra Bogoliubov anticommutator represents to the canonical CAR**
`fockRepHom(ã·ã† + ã†·ã) = (u² + v²)·1`. The Bogoliubov transformation, written in physlib's
`FieldOpFreeAlgebra` for the Dirac field specification, has the canonical anticommutator in the Fock
representation. -/
theorem fock_bogoliubov_CAR (u v : ℂ) (p : Momentum 3) :
    fockRepHom (bogElement u v p * bogElementDag u v p + bogElementDag u v p * bogElement u v p)
      = ((u ^ 2 + v ^ 2 : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [map_add, map_mul, map_mul, fockRepHom_bogElement, fockRepHom_bogElementDag]
  exact bogoliubov_preserves_CAR u v

/-- **The Foldy–Wouthuysen Bogoliubov is a CAR automorphism in the field-operator algebra.** For the
Foldy–Wouthuysen amplitudes `u² + v² = 1`, the Bogoliubov element of `FieldOpFreeAlgebra
diracFieldSpec` has the canonical anticommutator `1` in the Fock representation — the second-quantized
statement, now for a Dirac `FieldSpecification`. -/
theorem fw_fock_bogoliubov_canonical (u v : ℂ) (p : Momentum 3) (h : u ^ 2 + v ^ 2 = 1) :
    fockRepHom (bogElement u v p * bogElementDag u v p + bogElementDag u v p * bogElement u v p)
      = 1 := by
  rw [fock_bogoliubov_CAR, h, one_smul]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracFieldSpecBogoliubov

end
