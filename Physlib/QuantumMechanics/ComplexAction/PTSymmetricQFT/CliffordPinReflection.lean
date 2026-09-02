/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.CliffordAlgebra
public import Physlib.Relativity.SL2C.Basic
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
meta import Zil

/-!
# Greaves–Thomas Appendix B: Clifford algebras and the Pin reflection cover

Formalizes Appendix B of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) — the Clifford-algebra
description of the covering groups — and links it to the repo's existing Dirac Clifford algebra
(`Relativity.CliffordAlgebra`) and to the `SL(2,ℂ)` cover of §7 (`PTSymmetricQFT.SL2CCover`).

Appendix B.1/B.3: the real Clifford algebra `Cℓ_ℝ` is built from `T M` by the relation `vw + wv = 2η(v,w)`
(`Cℓ` is its complexification, with `η_ℂ`). The Pin group consists of products of unit vectors, and the
covering map `π : P → L(C)` sends a unit vector `v` to the **reflection in the hyperplane orthogonal to
`v`**, `π(v) : x ↦ x − 2·η(x,v)/η(v,v)·v`.

* **§A — the Clifford form is the Minkowski norm** (`minkBilin`, `diracForm_eq_minkBilin_self`,
  `diracForm_eq_det_bracket`). The repo's `Relativity.CliffordAlgebra.diracForm` is `η(x,x) =
  x₀²−x₁²−x₂²−x₃²`; this is exactly the `SL(2,ℂ)` cover's Minkowski norm `det⟨x⟩` of
  `PTSymmetricQFT.SL2CCover.det_bracket` — the Clifford form of Appendix B and the determinant of the
  Hermitian encoding of §7 are the same quadratic form.
* **§B — the Clifford relation `vw + wv = 2η(v,w)`** (`polar_diracForm`, `clifford_relation`,
  `clifford_sq`). The defining Appendix-B.1 relation, from `CliffordAlgebra.ι_mul_ι_add_swap`: the
  anticommutator of two generators is `2η(v,w)` (the polar form of `diracForm`), and `v² = η(v,v)`.
* **§C — the Pin reflection covering map** (`reflect`, `reflect_isometry`, `reflect_involutive`,
  `reflect_preserves_diracForm`). `π(v)` is an involution and an isometry of `η` — a Lorentz
  transformation — realizing the covering map `P → L(C)`.
* **§D — Varlamov's fundamental Clifford symmetries.** Grade involution,
  reversion, and their Clifford-conjugate composite form an actual Klein-four
  action on the Clifford algebra.  This replaces a table of labels by the
  existing Mathlib maps and proves its composition law.
* **§E — the Pin sandwich formula.** The Clifford product
  `-Q(v)⁻¹ v x v` is proved to equal the geometric reflection `reflect v x`
  after embedding by `CliffordAlgebra.ι`.
* **§F — exact bundled spin-cover fibers.** The actual Physlib
  homomorphism `SL(2,ℂ) → SO⁺(1,3)` identifies `A` and `-A`, its kernel is
  exactly `{1,-1}`, and two spinors have the same Lorentz image exactly when
  they differ by this central sign.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, Appendix B (Clifford algebras, the Pin group,
  the reflection covering map `π(v)`).
* V. V. Varlamov, *Clifford Algebras and Lorentz Group*, especially
  Eq. (6.22), the Clifford--Lipschitz reflection cover, and the
  `SL(2,ℂ)` spinor covering discussion.
* Repo carriers: `Relativity.CliffordAlgebra` (`diracForm`, the Dirac `γ`-matrix Clifford algebra);
  `PTSymmetricQFT.SL2CCover.det_bracket` (the `SL(2,ℂ)` Minkowski norm); `CliffordAlgebra.ι_mul_ι_add_swap`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover
open spaceTime.γ
open MatrixGroups


/-- **The Minkowski bilinear form** `η(x,y) = x₀y₀ − x₁y₁ − x₂y₂ − x₃y₃` — half the polar form of the
Clifford `diracForm`. -/
def minkBilin (x y : Fin 4 → ℝ) : ℝ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- **The Clifford `diracForm` is the Minkowski norm** `diracForm x = η(x,x)`. -/
lemma diracForm_eq_minkBilin_self (x : Fin 4 → ℝ) : diracForm x = minkBilin x x := by
  simp only [diracForm_apply, minkBilin]

/-- **[Link to §7] The Clifford form equals the `SL(2,ℂ)` cover's Minkowski norm** `diracForm x = det⟨x⟩`.
The Appendix-B Clifford quadratic form and the determinant of the §7 Hermitian encoding
(`PTSymmetricQFT.SL2CCover.bracket`) are one and the same. -/
lemma diracForm_eq_det_bracket (x : Fin 4 → ℝ) :
    ((diracForm x : ℝ) : ℂ) = (bracket x).det := by
  rw [det_bracket]; push_cast [diracForm_apply]; ring


/-- **The polar form of `diracForm` is `2η`** `polar(v,w) = 2η(v,w)`. -/
lemma polar_diracForm (v w : Fin 4 → ℝ) :
    QuadraticMap.polar diracForm v w = 2 * minkBilin v w := by
  simp only [QuadraticMap.polar, diracForm_apply, minkBilin, Pi.add_apply]; ring

/-- **[Appendix B.1/B.3] The Clifford relation** `vw + wv = 2η(v,w)`. The anticommutator of two Clifford
generators is twice the Minkowski inner product — the defining relation of `Cℓ_ℝ` (and `Cℓ` over `η_ℂ`),
from `CliffordAlgebra.ι_mul_ι_add_swap`. -/
lemma clifford_relation (v w : Fin 4 → ℝ) :
    CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm w
      + CliffordAlgebra.ι diracForm w * CliffordAlgebra.ι diracForm v
      = algebraMap ℝ (CliffordAlgebra diracForm) (2 * minkBilin v w) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, polar_diracForm]

/-- **The diagonal Clifford relation** `v² = η(v,v)` — a unit vector squares to `±1`, the basis of the Pin
group. -/
lemma clifford_sq (v : Fin 4 → ℝ) :
    CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm v
      = algebraMap ℝ (CliffordAlgebra diracForm) (diracForm v) :=
  CliffordAlgebra.ι_sq_scalar diracForm v


/-- **[Appendix B covering map] The reflection in the hyperplane orthogonal to `v`**
`π(v) : x ↦ x − 2·η(x,v)/η(v,v)·v` — the image of a unit vector under the Pin covering map `P → L(C)`. -/
noncomputable def reflect (v x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x - (2 * minkBilin x v / minkBilin v v) • v

/-- **`π(v)` is an isometry of `η`** `η(π(v)x, π(v)y) = η(x,y)` — the reflection preserves the Minkowski
inner product, so `π(v)` is a Lorentz transformation. -/
lemma reflect_isometry (v x y : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    minkBilin (reflect v x) (reflect v y) = minkBilin x y := by
  have hv' : v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 ≠ 0 := by
    simpa only [minkBilin, pow_two] using hv
  simp only [minkBilin, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hv']
  ring

/-- **`π(v)` is an involution** `π(v) ∘ π(v) = id` — reflecting twice returns the original (`π(v)² = 1`). -/
lemma reflect_involutive (v x : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    reflect v (reflect v x) = x := by
  have hv' : v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 ≠ 0 := by
    simpa only [minkBilin, pow_two] using hv
  funext i
  simp only [reflect, minkBilin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> · field_simp [hv']; ring

/-- **`π(v)` preserves the Clifford form** `diracForm (π(v)x) = diracForm x` — the reflection is a Lorentz
isometry of the Minkowski norm `= det⟨x⟩`, the covering-map property `π : P → L(C)`. -/
lemma reflect_preserves_diracForm (v x : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    diracForm (reflect v x) = diracForm x := by
  rw [diracForm_eq_minkBilin_self, diracForm_eq_minkBilin_self, reflect_isometry v x x hv]

/-! ## Varlamov's fundamental Clifford symmetry group -/

/-- The two independent bits in Varlamov's fundamental Clifford symmetry
table: grade involution (`P`) and reversion (`T`).  Their simultaneous action
is Clifford conjugation (`PT`). -/
structure CliffordFundamentalSymmetry where
  /-- Apply the Clifford grade involution. -/
  parity : Bool
  /-- Apply Clifford reversion. -/
  time : Bool
deriving DecidableEq, Repr, Fintype

/-- The identity in the fundamental Clifford symmetry table. -/
def cliffordFundamentalIdentity : CliffordFundamentalSymmetry :=
  ⟨false, false⟩

/-- Componentwise XOR composition, the Klein-four group law. -/
def cliffordFundamentalCompose
    (s t : CliffordFundamentalSymmetry) : CliffordFundamentalSymmetry :=
  ⟨s.parity ^^ t.parity, s.time ^^ t.time⟩

/-- Coordinate equivalence exposing the two independent Boolean generators. -/
def cliffordFundamentalSymmetryEquiv :
    CliffordFundamentalSymmetry ≃ Bool × Bool where
  toFun s := (s.parity, s.time)
  invFun s := ⟨s.1, s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- The actual action of a fundamental symmetry on a Clifford algebra.  The
`time` generator is an antiautomorphism, so this is deliberately an action on
the underlying carrier rather than falsely bundling all four maps as
`AlgEquiv`s. -/
def cliffordFundamentalAction
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (s : CliffordFundamentalSymmetry)
    (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  match s.parity, s.time with
  | false, false => x
  | true, false => CliffordAlgebra.involute x
  | false, true => CliffordAlgebra.reverse x
  | true, true => CliffordAlgebra.reverse (CliffordAlgebra.involute x)

/-- Varlamov's fundamental table has exactly four symmetry labels. -/
@[zil_level structural]
lemma cliffordFundamentalSymmetry_card :
    Fintype.card CliffordFundamentalSymmetry = 4 := by
  rw [Fintype.card_congr cliffordFundamentalSymmetryEquiv]
  decide

/-- **Varlamov Eq. (6.22), realized rather than tabulated.** Composition of
the actual Clifford maps is componentwise XOR.  The proof uses the established
involutivity and commutation of grade involution and reversion. -/
@[zil_level bridge_theorem]
lemma cliffordFundamentalAction_comp
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (s t : CliffordFundamentalSymmetry)
    (x : CliffordAlgebra Q) :
    cliffordFundamentalAction (cliffordFundamentalCompose s t) x =
      cliffordFundamentalAction s (cliffordFundamentalAction t x) := by
  rcases s with ⟨s, u⟩
  rcases t with ⟨t, v⟩
  cases s <;> cases u <;> cases t <;> cases v <;>
    simp [cliffordFundamentalAction, cliffordFundamentalCompose,
      CliffordAlgebra.reverse_involute]

/-- Every fundamental Clifford symmetry is its own inverse. -/
@[zil_level bridge_theorem]
lemma cliffordFundamentalAction_involutive
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (s : CliffordFundamentalSymmetry)
    (x : CliffordAlgebra Q) :
    cliffordFundamentalAction s (cliffordFundamentalAction s x) = x := by
  rw [← cliffordFundamentalAction_comp]
  rcases s with ⟨s, t⟩
  cases s <;> cases t <;>
    simp [cliffordFundamentalCompose, cliffordFundamentalAction]

/-- The simultaneous `PT` bit is exactly Mathlib's Clifford star operation,
the composite of grade involution and reversion. -/
@[zil_level bridge_theorem]
lemma cliffordFundamentalAction_full_eq_star
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) :
    cliffordFundamentalAction ⟨true, true⟩ x = star x := by
  rfl

/-! ## The Clifford sandwich is the Pin reflection -/

/-- Algebraic reduction of the three-vector Clifford product used in the Pin
cover. -/
lemma clifford_triple_eq
    (v x : Fin 4 → ℝ) :
    CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm x *
        CliffordAlgebra.ι diracForm v =
      (2 * minkBilin v x) • CliffordAlgebra.ι diracForm v -
        diracForm v • CliffordAlgebra.ι diracForm x := by
  have hrel := clifford_relation v x
  have hsquare := clifford_sq v
  rw [eq_sub_of_add_eq hrel]
  rw [sub_mul, mul_assoc, hsquare]
  simp only [Algebra.smul_def]
  rw [map_mul]
  congr 1
  exact (Algebra.commutes (diracForm v)
    (CliffordAlgebra.ι diracForm x)).symm

/-- **The Pin covering formula.** For a non-isotropic vector `v`, twisted
Clifford conjugation by its generator is exactly the Lorentz reflection in
the hyperplane orthogonal to `v`:
`-Q(v)⁻¹ ι(v)ι(x)ι(v) = ι(x - 2η(x,v)/η(v,v) v)`. -/
@[zil_level physical_theorem]
lemma clifford_pin_sandwich_eq_reflect
    (v x : Fin 4 → ℝ) (hv : minkBilin v v ≠ 0) :
    -(diracForm v)⁻¹ •
        (CliffordAlgebra.ι diracForm v * CliffordAlgebra.ι diracForm x *
          CliffordAlgebra.ι diracForm v) =
      CliffordAlgebra.ι diracForm (reflect v x) := by
  rw [clifford_triple_eq]
  rw [show reflect v x = x - (2 * minkBilin v x / diracForm v) • v by
        simp only [reflect, diracForm_eq_minkBilin_self]
        congr 2
        unfold minkBilin
        ring]
  simp only [map_sub, map_smul]
  have hq : diracForm v ≠ 0 := by
    rw [diracForm_eq_minkBilin_self]
    exact hv
  have hcoeffV : -(diracForm v)⁻¹ * (2 * minkBilin v x) =
      -(2 * minkBilin v x / diracForm v) := by
    field_simp [hq]
  have hcoeffX : -(diracForm v)⁻¹ * diracForm v = -1 := by
    field_simp [hq]
  rw [smul_sub, smul_smul, smul_smul, hcoeffV, hcoeffX]
  module

/-! ## The central sign in the bundled `SL(2,ℂ)` cover -/

/-- The actual bundled Physlib Lorentz homomorphism identifies the two spinor
sheets `A` and `-A`. -/
@[zil_level bridge_theorem]
lemma sl2cBundledCover_neg (A : SL(2, ℂ)) :
    Lorentz.SL2C.toLorentzGroup (-A) = Lorentz.SL2C.toLorentzGroup A := by
  have hmap : Lorentz.SL2C.toSelfAdjointMap (-A) =
      Lorentz.SL2C.toSelfAdjointMap A := by
    ext X i j
    simp [Lorentz.SL2C.toSelfAdjointMap, Matrix.conjTranspose_neg]
  apply Subtype.ext
  change LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis'
      (Lorentz.SL2C.toSelfAdjointMap (-A)) =
    LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis'
      (Lorentz.SL2C.toSelfAdjointMap A)
  rw [hmap]

/-- The central sign is genuinely nontrivial on the spinor carrier. -/
lemma sl2c_negOne_ne_one : (-1 : SL(2, ℂ)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : SL(2, ℂ) => M.1 0 0) h
  norm_num at h00

/-- The nontrivial central sign belongs to the kernel of the bundled map to
the restricted Lorentz group.  Together with `sl2c_negOne_ne_one`, this is
the proved two-sheet witness; it does not by itself claim that the kernel has
no other elements or that the map is surjective. -/
@[zil_level physical_theorem]
lemma sl2c_negOne_mem_restrictedCover_kernel :
    (-1 : SL(2, ℂ)) ∈
      MonoidHom.ker Lorentz.SL2C.toRestrictedLorentzGroup := by
  change Lorentz.SL2C.toRestrictedLorentzGroup (-1 : SL(2, ℂ)) = 1
  apply Subtype.ext
  change Lorentz.SL2C.toLorentzGroup (-1 : SL(2, ℂ)) = 1
  simpa using sl2cBundledCover_neg (1 : SL(2, ℂ))

/-- **Exact kernel of the bundled spin cover.** A spinor acts trivially on
Minkowski space exactly when it is one of the two central signs.  The proof
uses the actual Pauli-basis representation: trivial action makes `A` unitary
and forces it to commute with the Pauli matrices; hence it is scalar, and
`det A = 1` leaves precisely `A = ±1`. -/
@[zil_level physical_theorem]
theorem sl2cBundledCover_eq_one_iff (A : SL(2, ℂ)) :
    Lorentz.SL2C.toLorentzGroup A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  intro hA
  have hmap : Lorentz.SL2C.toSelfAdjointMap A = 1 := by
    apply (LinearMap.toMatrix PauliMatrix.pauliBasis'
      PauliMatrix.pauliBasis').injective
    rw [LinearMap.toMatrix_one]
    change Lorentz.SL2C.toMatrix A = 1
    exact congrArg Subtype.val hA
  have hI := congrArg
    (fun f => f (PauliMatrix.pauliBasis' (Sum.inl 0))) hmap
  have hAAstar : A.1 * Matrix.conjTranspose A.1 = 1 := by
    apply congrArg Subtype.val at hI
    simpa [Lorentz.SL2C.toSelfAdjointMap, PauliMatrix.pauliBasis',
      PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix] using hI
  have hstarA : Matrix.conjTranspose A.1 * A.1 = 1 :=
    mul_eq_one_comm.mp hAAstar
  have hcommSelf
      (X : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
      A.1 * X.1 = X.1 * A.1 := by
    have hX := congrArg (fun f => f X) hmap
    apply congrArg Subtype.val at hX
    have hX' : A.1 * X.1 * Matrix.conjTranspose A.1 = X.1 := by
      simpa [Lorentz.SL2C.toSelfAdjointMap] using hX
    have hX'' := congrArg (fun M => M * A.1) hX'
    simpa [Matrix.mul_assoc, hstarA] using hX''
  have hcomm (i : Fin 3) :
      A.1 * PauliMatrix.pauliMatrix (Sum.inr i) =
        PauliMatrix.pauliMatrix (Sum.inr i) * A.1 := by
    simpa [PauliMatrix.pauliBasis, PauliMatrix.pauliSelfAdjoint] using
      hcommSelf (PauliMatrix.pauliBasis (Sum.inr i))
  have hoff01 : A.1 0 1 = 0 := by
    have h := congrFun₂ (hcomm 2) 0 1
    simp [PauliMatrix.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
    exact CharZero.neg_eq_self_iff.mp h
  have hoff10 : A.1 1 0 = 0 := by
    have h := congrFun₂ (hcomm 2) 1 0
    simp [PauliMatrix.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
    exact CharZero.neg_eq_self_iff.mp h.symm
  have hdiag : A.1 0 0 = A.1 1 1 := by
    have h := congrFun₂ (hcomm 0) 0 1
    simpa [PauliMatrix.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      using h
  have hsq : (A.1 0 0) ^ 2 = 1 := by
    have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.property
    rw [hoff01, hoff10, mul_zero, sub_zero] at hdet
    calc
      (A.1 0 0) ^ 2 = A.1 0 0 * A.1 1 1 := by rw [hdiag]; ring
      _ = 1 := hdet
  rcases sq_eq_one_iff.mp hsq with h | h
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h
    · simp [hoff01]
    · simp [hoff10]
    · simpa [← hdiag] using h
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h
    · simp [hoff01]
    · simp [hoff10]
    · simpa [← hdiag] using h
  · rintro (rfl | rfl)
    · simp
    · simpa using sl2cBundledCover_neg (1 : SL(2, ℂ))

/-- The kernel of the bundled homomorphism into the restricted Lorentz group
is exactly the two central spinor signs. -/
@[zil_level physical_theorem]
theorem sl2c_restrictedCover_mem_kernel_iff (A : SL(2, ℂ)) :
    A ∈ MonoidHom.ker Lorentz.SL2C.toRestrictedLorentzGroup ↔
      A = 1 ∨ A = -1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    rw [← sl2cBundledCover_eq_one_iff]
    exact congrArg (fun L : LorentzGroup.restricted 3 => L.1) hA
  · rintro (rfl | rfl)
    · simp
    · exact sl2c_negOne_mem_restrictedCover_kernel

/-- **Two-sheet fiber theorem.** Two elements of `SL(2,ℂ)` determine the
same bundled Lorentz transformation exactly when they are equal or differ by
the nontrivial central sign. -/
@[zil_level physical_theorem]
theorem sl2cBundledCover_eq_iff (A B : SL(2, ℂ)) :
    Lorentz.SL2C.toLorentzGroup A = Lorentz.SL2C.toLorentzGroup B ↔
      A = B ∨ A = -B := by
  constructor
  · intro hAB
    have hker : Lorentz.SL2C.toLorentzGroup (A * B⁻¹) = 1 := by
      simp [hAB]
    rcases (sl2cBundledCover_eq_one_iff (A * B⁻¹)).mp hker with h | h
    · left
      exact mul_inv_eq_one.mp h
    · right
      have h' := congrArg (fun C : SL(2, ℂ) => C * B) h
      simpa [mul_assoc] using h'
  · rintro (rfl | rfl)
    · rfl
    · exact sl2cBundledCover_neg B

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalAction_comp where
  formalizes @ "claim:varlamovs-four-fundamental-clifford-symmetries-identity-grade-involution-reversion-and-clifford-conjugation-obey-the-klein-four-composition-table-by-actual-map-composition",
  supported_by @ "paper:varlamov-clifford-algebras-and-lorentz-group-equation-6-22",
  caveat @ "claim:reversion-is-an-antiautomorphism-so-the-result-is-correctly-an-action-on-the-underlying-clifford-carrier-not-a-false-claim-that-all-four-maps-are-algebra-automorphisms"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalAction_full_eq_star where
  formalizes @ "claim:the-simultaneous-parity-time-fundamental-clifford-symmetry-is-exactly-clifford-conjugation-star-equal-to-reversion-after-grade-involution",
  supported_by @ "lean:CliffordAlgebra.star_def"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.clifford_pin_sandwich_eq_reflect where
  formalizes @ "claim:the-pin-clifford-sandwich-minus-q-v-inverse-times-v-x-v-is-exactly-the-minkowski-hyperplane-reflection-after-the-canonical-clifford-embedding",
  supported_by @ "paper:varlamov-clifford-algebras-and-lorentz-group-pin-cover",
  caveat @ "claim:the-reflecting-vector-is-explicitly-nonisotropic-this-is-the-pointwise-pin-reflection-formula-not-a-classification-of-all-eight-pin-p-q-covering-groups"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_neg where
  formalizes @ "claim:the-actual-bundled-sl-two-complex-to-lorentz-group-homomorphism-identifies-every-spinor-matrix-a-with-minus-a",
  supported_by @ "lean:Lorentz.SL2C.toLorentzGroup"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2c_negOne_mem_restrictedCover_kernel where
  formalizes @ "claim:the-nontrivial-central-minus-one-spinor-is-in-the-kernel-of-the-bundled-map-from-sl-two-complex-to-the-restricted-lorentz-group",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_neg"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2c_restrictedCover_mem_kernel_iff where
  formalizes @ "claim:the-kernel-of-the-actual-bundled-map-from-sl-two-complex-to-the-restricted-lorentz-group-is-exactly-the-two-central-elements-plus-one-and-minus-one",
  derives @ "claim:the-spin-cover-has-exactly-two-sheets-over-each-point-of-its-image",
  supported_by @ "lean:Lorentz.SL2C.toRestrictedLorentzGroup",
  caveat @ "claim:exact-kernel-and-fiber-cardinality-do-not-by-themselves-prove-surjectivity-onto-the-entire-restricted-lorentz-group"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_eq_iff where
  formalizes @ "claim:two-sl-two-complex-spinors-have-the-same-bundled-lorentz-image-if-and-only-if-they-are-equal-or-differ-by-the-central-minus-sign",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_eq_one_iff",
  caveat @ "claim:this-is-the-exact-two-sheet-fiber-theorem-over-the-image-and-does-not-assert-surjectivity-of-the-lorentz-homomorphism"

zil_file_contract physlib.varlamovCliffordLorentz where
  promises "Varlamov's Clifford-Lorentz algebraic core is realized on the repository's existing carriers rather than copied as a label table. Grade involution and reversion commute and square to the identity, giving an actual Klein-four action whose full element is Clifford conjugation. The Clifford sandwich by a non-isotropic vector is proved equal to the existing Minkowski hyperplane reflection. On the spinor side, the actual bundled Physlib homomorphism from SL(2,C) to the restricted Lorentz group has kernel exactly plus or minus one, and two spinors have the same Lorentz image exactly when they differ by that central sign."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:CliffordAlgebra.involute",
    "lean:CliffordAlgebra.reverse",
    "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.reflect",
    "lean:Lorentz.SL2C.toRestrictedLorentzGroup"]
  forbids_substitutes ["a Boolean symmetry label presented as though it were the corresponding Clifford map",
    "a raw matrix cover action presented as the bundled restricted-Lorentz homomorphism",
    "a claim of surjectivity onto the entire restricted Lorentz group from the exact kernel and fiber theorem alone"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalSymmetry_card,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalAction_comp,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalAction_involutive,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.cliffordFundamentalAction_full_eq_star,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.clifford_pin_sandwich_eq_reflect,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_neg,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2c_negOne_mem_restrictedCover_kernel,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_eq_one_iff,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2c_restrictedCover_mem_kernel_iff,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection.sl2cBundledCover_eq_iff]

/- ZIL-END -/
