/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.Basic

/-!
# Kálnay field bridge: fermion fields as Bose-bilinear fields

`BoseFermiOperatorAlgebra.BoseBilinearRealization` proves the sector-compressed operator identity behind Kálnay's
construction: the Bose bilinear `a† b`, restricted to the one-boson two-mode sector, satisfies the CAR and
therefore is a genuine fermion mode. This file connects that concrete result to physlib's
`FieldSpecification` and `FieldOpFreeAlgebra` layer.

The bridge has two complementary parts.

* `kalnayBoseCarrierSpec` is a bosonic structure with two Bose field modes `a` and `b`.
* `kalnayFermionFieldSpec` is a one-field fermionic specification.
* `kalnayBosonizeCrAn` sends each fermion creation/annihilation field generator to the Bose-bilinear word
  `b† a` or `a† b` in the Bose free algebra.
* `kalnayFermionRep` and `kalnayFermionRepHom` realize the fermion field generators on the concrete
  single-boson sector as `star boseBilinear` and `boseBilinear`, inheriting the checked CAR from
  `boseBilinear_isFermionMode`.

This is deliberately not a claim that the raw Bose free algebra itself has CAR relations. The CAR is proved
after passing to the sector representation supplied by `BoseFermiOperatorAlgebra.BoseBilinearRealization`, exactly matching the
finite, interpretation-free core of Kálnay's construction.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open FieldSpecification FieldSpecification.FieldOpFreeAlgebra

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization

/-! ## §A — field specifications -/

/-- The two Bose modes used in the finite Kálnay bilinear `a† b`. -/
inductive KalnayBoseMode where
  | a : KalnayBoseMode
  | b : KalnayBoseMode
deriving DecidableEq

/-- The bosonic field specification with two modes, `a` and `b`. -/
def kalnayBoseCarrierSpec : FieldSpecification where
  Field := KalnayBoseMode
  PositionLabel := fun _ => Unit
  AsymptoticLabel := fun _ => Unit
  statistic := fun _ => FieldStatistic.bosonic

/-- The composite fermion field specification. It has one fermionic field. -/
def kalnayFermionFieldSpec : FieldSpecification where
  Field := Unit
  PositionLabel := fun _ => Unit
  AsymptoticLabel := fun _ => Unit
  statistic := fun _ => FieldStatistic.fermionic

@[simp] theorem kalnayBoseCarrier_statistic (m : kalnayBoseCarrierSpec.Field) :
    kalnayBoseCarrierSpec.statistic m = FieldStatistic.bosonic := rfl

@[simp] theorem kalnayFermionField_statistic (f : kalnayFermionFieldSpec.Field) :
    kalnayFermionFieldSpec.statistic f = FieldStatistic.fermionic := rfl

/-! ## §B — Bose structure creation/annihilation field operators -/

/-- Bose asymptotic creation operator for mode `m`. -/
def boseAsymptoticCreate (m : KalnayBoseMode) (p : Momentum 3) :
    kalnayBoseCarrierSpec.CrAnFieldOp :=
  ⟨FieldOp.inAsymp (⟨m, ()⟩, p), ()⟩

/-- Bose asymptotic annihilation operator for mode `m`. -/
def boseAsymptoticAnnihil (m : KalnayBoseMode) (p : Momentum 3) :
    kalnayBoseCarrierSpec.CrAnFieldOp :=
  ⟨FieldOp.outAsymp (⟨m, ()⟩, p), ()⟩

/-- Bose position-field creation component for mode `m`. -/
def bosePositionCreate (m : KalnayBoseMode) (x : SpaceTime) :
    kalnayBoseCarrierSpec.CrAnFieldOp :=
  ⟨FieldOp.position (⟨m, ()⟩, x), CreateAnnihilate.create⟩

/-- Bose position-field annihilation component for mode `m`. -/
def bosePositionAnnihil (m : KalnayBoseMode) (x : SpaceTime) :
    kalnayBoseCarrierSpec.CrAnFieldOp :=
  ⟨FieldOp.position (⟨m, ()⟩, x), CreateAnnihilate.annihilate⟩

/-- The asymptotic Bose-bilinear word representing the composite fermion annihilation field:
`f = a† b`. -/
def boseBilinearAnnihilAsymptotic (p : Momentum 3) :
    FieldOpFreeAlgebra kalnayBoseCarrierSpec :=
  ofCrAnOpF (boseAsymptoticCreate KalnayBoseMode.a p)
    * ofCrAnOpF (boseAsymptoticAnnihil KalnayBoseMode.b p)

/-- The asymptotic Bose-bilinear word representing the composite fermion creation field:
`f† = b† a`. -/
def boseBilinearCreateAsymptotic (p : Momentum 3) :
    FieldOpFreeAlgebra kalnayBoseCarrierSpec :=
  ofCrAnOpF (boseAsymptoticCreate KalnayBoseMode.b p)
    * ofCrAnOpF (boseAsymptoticAnnihil KalnayBoseMode.a p)

/-- The position-space Bose-bilinear word representing the composite fermion annihilation component. -/
def boseBilinearAnnihilPosition (x : SpaceTime) :
    FieldOpFreeAlgebra kalnayBoseCarrierSpec :=
  ofCrAnOpF (bosePositionCreate KalnayBoseMode.a x)
    * ofCrAnOpF (bosePositionAnnihil KalnayBoseMode.b x)

/-- The position-space Bose-bilinear word representing the composite fermion creation component. -/
def boseBilinearCreatePosition (x : SpaceTime) :
    FieldOpFreeAlgebra kalnayBoseCarrierSpec :=
  ofCrAnOpF (bosePositionCreate KalnayBoseMode.b x)
    * ofCrAnOpF (bosePositionAnnihil KalnayBoseMode.a x)

/-! ## §C — the fermion field and its bosonization dictionary -/

/-- The composite fermion asymptotic annihilation operator. -/
def kalnayFermionAnnihil (p : Momentum 3) : kalnayFermionFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.outAsymp (⟨(), ()⟩, p), ()⟩

/-- The composite fermion asymptotic creation operator. -/
def kalnayFermionCreate (p : Momentum 3) : kalnayFermionFieldSpec.CrAnFieldOp :=
  ⟨FieldOp.inAsymp (⟨(), ()⟩, p), ()⟩

/-- The composite fermion position field. -/
def kalnayFermionPosition (x : SpaceTime) : kalnayFermionFieldSpec.FieldOp :=
  FieldOp.position (⟨(), ()⟩, x)

/-- The creation component of the composite fermion position field. -/
def kalnayFermionPositionCreate (x : SpaceTime) : kalnayFermionFieldSpec.CrAnFieldOp :=
  ⟨kalnayFermionPosition x, CreateAnnihilate.create⟩

/-- The annihilation component of the composite fermion position field. -/
def kalnayFermionPositionAnnihil (x : SpaceTime) : kalnayFermionFieldSpec.CrAnFieldOp :=
  ⟨kalnayFermionPosition x, CreateAnnihilate.annihilate⟩

/-- The Kálnay bosonization dictionary on creation/annihilation field generators. It sends the fermion
field generator to a Bose-bilinear word in the Bose field algebra. -/
def kalnayBosonizeCrAn :
    kalnayFermionFieldSpec.CrAnFieldOp → FieldOpFreeAlgebra kalnayBoseCarrierSpec
  | ⟨FieldOp.inAsymp (_, p), _⟩ => boseBilinearCreateAsymptotic p
  | ⟨FieldOp.outAsymp (_, p), _⟩ => boseBilinearAnnihilAsymptotic p
  | ⟨FieldOp.position (_, x), CreateAnnihilate.create⟩ => boseBilinearCreatePosition x
  | ⟨FieldOp.position (_, x), CreateAnnihilate.annihilate⟩ => boseBilinearAnnihilPosition x

/-- The algebra homomorphism extending the generator-level Kálnay bosonization dictionary. -/
def kalnayBosonizationHom :
    FieldOpFreeAlgebra kalnayFermionFieldSpec →ₐ[ℂ]
      FieldOpFreeAlgebra kalnayBoseCarrierSpec :=
  FreeAlgebra.lift ℂ kalnayBosonizeCrAn

@[simp] theorem kalnayBosonizationHom_ofCrAnOpF
    (φ : kalnayFermionFieldSpec.CrAnFieldOp) :
    kalnayBosonizationHom (ofCrAnOpF φ) = kalnayBosonizeCrAn φ := by
  rw [kalnayBosonizationHom, ofCrAnOpF, FreeAlgebra.lift_ι_apply]

@[simp] theorem bosonize_kalnayFermionAnnihil (p : Momentum 3) :
    kalnayBosonizeCrAn (kalnayFermionAnnihil p) = boseBilinearAnnihilAsymptotic p := rfl

@[simp] theorem bosonize_kalnayFermionCreate (p : Momentum 3) :
    kalnayBosonizeCrAn (kalnayFermionCreate p) = boseBilinearCreateAsymptotic p := rfl

@[simp] theorem bosonize_kalnayFermionPositionAnnihil (x : SpaceTime) :
    kalnayBosonizeCrAn (kalnayFermionPositionAnnihil x) = boseBilinearAnnihilPosition x := rfl

@[simp] theorem bosonize_kalnayFermionPositionCreate (x : SpaceTime) :
    kalnayBosonizeCrAn (kalnayFermionPositionCreate x) = boseBilinearCreatePosition x := rfl

/-! ## §D — the concrete sector representation and CAR -/

/-- The concrete single-boson-sector interpretation of the composite fermion field generators. -/
def kalnayFermionRep : kalnayFermionFieldSpec.CrAnFieldOp → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨FieldOp.inAsymp _, _⟩ => star boseBilinear
  | ⟨FieldOp.outAsymp _, _⟩ => boseBilinear
  | ⟨FieldOp.position _, CreateAnnihilate.create⟩ => star boseBilinear
  | ⟨FieldOp.position _, CreateAnnihilate.annihilate⟩ => boseBilinear

/-- The algebra homomorphism induced by the concrete sector representation. -/
def kalnayFermionRepHom :
    FieldOpFreeAlgebra kalnayFermionFieldSpec →ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  FreeAlgebra.lift ℂ kalnayFermionRep

@[simp] theorem kalnayFermionRepHom_ofCrAnOpF
    (φ : kalnayFermionFieldSpec.CrAnFieldOp) :
    kalnayFermionRepHom (ofCrAnOpF φ) = kalnayFermionRep φ := by
  rw [kalnayFermionRepHom, ofCrAnOpF, FreeAlgebra.lift_ι_apply]

@[simp] theorem kalnayFermionRep_annihil (p : Momentum 3) :
    kalnayFermionRep (kalnayFermionAnnihil p) = boseBilinear := rfl

@[simp] theorem kalnayFermionRep_create (p : Momentum 3) :
    kalnayFermionRep (kalnayFermionCreate p) = star boseBilinear := rfl

@[simp] theorem kalnayFermionRep_position_annihil (x : SpaceTime) :
    kalnayFermionRep (kalnayFermionPositionAnnihil x) = boseBilinear := rfl

@[simp] theorem kalnayFermionRep_position_create (x : SpaceTime) :
    kalnayFermionRep (kalnayFermionPositionCreate x) = star boseBilinear := rfl

/-- The asymptotic composite fermion field is the Kálnay Bose bilinear on the sector representation. -/
theorem kalnayFermionRepHom_annihil_eq_boseBilinear (p : Momentum 3) :
    kalnayFermionRepHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinear := by
  simp

/-- The creation field is the adjoint Bose bilinear on the sector representation. -/
theorem kalnayFermionRepHom_create_eq_star_boseBilinear (p : Momentum 3) :
    kalnayFermionRepHom (ofCrAnOpF (kalnayFermionCreate p)) = star boseBilinear := by
  simp

/-- The composite fermion annihilation field squares to zero in the sector representation. -/
theorem kalnayFermionRepHom_annihil_sq_zero (p : Momentum 3) :
    kalnayFermionRepHom (ofCrAnOpF (kalnayFermionAnnihil p) * ofCrAnOpF (kalnayFermionAnnihil p))
      = 0 := by
  rw [map_mul, kalnayFermionRepHom_annihil_eq_boseBilinear]
  exact boseBilinear_isFermionMode.1

/-- The composite fermion creation/annihilation fields satisfy the CAR in the sector representation. -/
theorem kalnayFermionRepHom_CAR (p : Momentum 3) :
    kalnayFermionRepHom
      (ofCrAnOpF (kalnayFermionAnnihil p) * ofCrAnOpF (kalnayFermionCreate p)
        + ofCrAnOpF (kalnayFermionCreate p) * ofCrAnOpF (kalnayFermionAnnihil p))
      = 1 := by
  rw [map_add, map_mul, map_mul, kalnayFermionRepHom_annihil_eq_boseBilinear,
    kalnayFermionRepHom_create_eq_star_boseBilinear]
  exact boseBilinear_isFermionMode.2

/-- Position-field version: the creation and annihilation components are represented by `f†` and `f`,
where `f = a† b` is the Kálnay Bose bilinear. -/
theorem kalnayFermionPosition_components_are_bose_bilinears (x : SpaceTime) :
    kalnayFermionRepHom (ofCrAnOpF (kalnayFermionPositionAnnihil x)) = boseBilinear
      ∧ kalnayFermionRepHom (ofCrAnOpF (kalnayFermionPositionCreate x)) = star boseBilinear := by
  simp

/-- Assembled bridge: the fermion field generator is a Bose-bilinear word and its sector realization is a
genuine CAR fermion. -/
theorem kalnay_fermion_field_from_bose_fields (p : Momentum 3) :
    kalnayBosonizationHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinearAnnihilAsymptotic p
      ∧ kalnayBosonizationHom (ofCrAnOpF (kalnayFermionCreate p)) = boseBilinearCreateAsymptotic p
      ∧ kalnayFermionRepHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinear
      ∧ kalnayFermionRepHom
        (ofCrAnOpF (kalnayFermionAnnihil p) * ofCrAnOpF (kalnayFermionCreate p)
          + ofCrAnOpF (kalnayFermionCreate p) * ofCrAnOpF (kalnayFermionAnnihil p)) = 1 :=
  ⟨by simp, by simp, kalnayFermionRepHom_annihil_eq_boseBilinear p,
    kalnayFermionRepHom_CAR p⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField

end
