/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SL2CDoubleCover
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracFieldSpecBogoliubov

/-!
# Hayashi's complex Chern-Simons-Witten gravity interface

This module records the Lean-checkable interface extracted from N. Hayashi,
*Quantum Hilbert Space of `G_c` Chern-Simons-Witten Theory and Gravity*,
Progress of Theoretical Physics Supplement **114** (1993), 125-147.

The file deliberately does **not** claim a full construction of the analytic CSW
functional integral, determinant line bundle, Verlinde basis, or WZNW model.
Instead it formalizes the conditional algebraic contracts that can be connected
to existing Physlib structures:

* the `G_c` CSW action splits into holomorphic and anti-holomorphic sectors;
* the integer CS level feeds the existing DJT topological-mass structure;
* the `SL(2,ℂ)` gravity reading is attached to the existing spinor double cover
  and Levi-Civita/Lusanna tetrad-invariant layer;
* Hayashi's CSW gravity replacement of Wheeler-DeWitt is represented as a
  parallel-transport interface over complex structures;
* torus physical states and genus-one topological invariants factor into
  left/right compact-sector data.
* the factorized CSW sector is linked to the repository's bosonic and fermionic
  field-operator structures: Kálnay Bose-bilinear fermions, CAR, Weyl CCR,
  Bogoliubov statistics, and the Dirac `FieldSpecification` Fock representation.

## References

* N. Hayashi, *Quantum Hilbert Space of `G_c` Chern-Simons-Witten Theory and Gravity*,
  Prog. Theor. Phys. Suppl. **114** (1993), 125-147.
* E. Witten, *Quantum Field Theory and the Jones Polynomial*, Commun. Math. Phys. **121** (1989), 351.
* Repo dependencies: `ChernSimons.TopologicalMassDJT`, `Hopf.SL2CDoubleCover`, `ComplexEinstein.WheelerDeWittComplexEinstein`,
  `LeviCivita.TetradInvariant`, `BoseFermiOperatorAlgebra.Basic`,
  `Bogoliubov.DiracFieldSpecBogoliubov`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.Hopf.SL2CDoubleCover
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracFieldSpecBogoliubov
open _root_.Lorentz

/-! ## §A — source-paper anchors -/

/-- Local bibliographic/source record for Hayashi's CSW-gravity paper. -/
structure HayashiPaperReference where
  title : String
  author : String
  journal : String
  pages : String
  localPdf : String
  deriving Repr, DecidableEq

/-- The local Hayashi source inspected for this formalization. -/
def hayashiPaperReference : HayashiPaperReference :=
  { title := "Quantum Hilbert Space of Gc Chern-Simons-Witten Theory and Gravity"
    author := "Nobuharu Hayashi"
    journal := "Progress of Theoretical Physics Supplement 114 (1993)"
    pages := "125-147"
    localPdf := "/Users/macbookpro/Downloads/chern-simons-witten-hayashi1993.pdf" }

/-- Stable anchors for the Hayashi claims used below. -/
inductive HayashiAnchor where
  | complexCSWAction
  | sl2cGravity
  | geometricQuantization
  | wheelerDeWittReplacement
  | torusHilbertFactorization
  | orthogonality
  | verlindeWilsonLoop
  | lensSpaceInvariantFactorization
  deriving Repr, DecidableEq

/-- Paper locator for each formalized Hayashi anchor. -/
def HayashiAnchor.paperLabel : HayashiAnchor → String
  | .complexCSWAction => "Section 2.1, equations (2.2)-(2.3)"
  | .sl2cGravity => "Section 2.1, equations (2.4)-(2.5)"
  | .geometricQuantization => "Section 2.2, equations (2.6)-(2.11)"
  | .wheelerDeWittReplacement => "Introduction and Section 2.2"
  | .torusHilbertFactorization => "Section 5.1, theorem around equation (5.7)"
  | .orthogonality => "Section 4"
  | .verlindeWilsonLoop => "Section 5.1, equations (5.8)-(5.11)"
  | .lensSpaceInvariantFactorization => "Section 5.2, equation (5.19)"

/-! ## §B — coupling constants and the CSW action split -/

/-- Hayashi's complex CSW coupling data `t = k + i s`, `tbar = k - i s`, with integer level `k`. -/
structure HayashiCouplings where
  /-- The integer Chern-Simons level. -/
  level : ℤ
  /-- The second coupling parameter; Hayashi allows this to vary. -/
  s : ℂ

/-- The holomorphic coupling `t = k + i s`. -/
def holomorphicCoupling (c : HayashiCouplings) : ℂ :=
  (c.level : ℂ) + Complex.I * c.s

/-- The anti-holomorphic coupling `tbar = k - i s`. -/
def antiholomorphicCoupling (c : HayashiCouplings) : ℂ :=
  (c.level : ℂ) - Complex.I * c.s

/-- The same integer level, viewed through the existing DJT topological-mass structure. -/
def toDJTData (c : HayashiCouplings) (e : ℝ) : DJTData :=
  { e := e, level := c.level }

/-- **[Hayashi → DJT level]** The integer `k` in Hayashi's `t = k + i s` is exactly the CS level used by
the existing DJT topological-mass structure. -/
theorem toDJTData_level (c : HayashiCouplings) (e : ℝ) :
    (toDJTData c e).level = c.level := rfl

/-- **[Hayashi level gives nonnegative DJT topological mass].** Reuses `ChernSimons.TopologicalMassDJT`: the same
integer CS level that appears in Hayashi's complex coupling gives a nonnegative DJT topological mass in
the `U(1)` specialization. -/
theorem hayashi_DJT_topologicalMass_nonneg (c : HayashiCouplings) (e : ℝ) :
    0 ≤ topologicalMass (toDJTData c e) :=
  topologicalMass_nonneg (toDJTData c e)

/-- Abstract representative for Hayashi's equation `I[A,Abar] = I[A] + I[Abar]`. -/
structure ComplexCSWAction (Field : Type*) where
  /-- Holomorphic CSW sector `I[A]`. -/
  holomorphicAction : Field → ℂ
  /-- Anti-holomorphic CSW sector `I[Abar]`. -/
  antiholomorphicAction : Field → ℂ
  /-- Full complex-group CSW action. -/
  totalAction : Field → ℂ
  /-- Hayashi's action split. -/
  total_eq_sector_sum : ∀ A, totalAction A = holomorphicAction A + antiholomorphicAction A

/-- **[CSW action split]** The total `G_c` action is the sum of holomorphic and anti-holomorphic CSW
actions, exactly as in Hayashi (2.2)-(2.3). -/
theorem complexCSWAction_split {Field : Type*} (I : ComplexCSWAction Field) (A : Field) :
    I.totalAction A = I.holomorphicAction A + I.antiholomorphicAction A :=
  I.total_eq_sector_sum A

/-! ## §C — `SL(2,ℂ)` gravity and tetrad invariance -/

/-- Conditional representative for Hayashi's `SL(2,ℂ)` gravity reading: after substituting `A = ω + i e` and
`Abar = ω - i e`, the complex CSW action splits into an exotic term and an Einstein-Hilbert term, while
`e` is interpreted as the dreibein/tetrad. -/
structure SL2CCSWGravityCarrier where
  complexAction : ℂ
  exoticTerm : ℂ
  einsteinHilbertTerm : ℂ
  action_decomposition : complexAction = exoticTerm + einsteinHilbertTerm
  spinConnectionDreibeinInterpretation : Prop
  spinConnectionDreibeinInterpretation_holds : spinConnectionDreibeinInterpretation
  euclideanNegativeCosmologicalConstant : Prop
  euclideanNegativeCosmologicalConstant_holds : euclideanNegativeCosmologicalConstant
  tetradInvariantGeometry : Prop
  tetradInvariantGeometry_holds : tetradInvariantGeometry

/-- **[Hayashi `SL(2,ℂ)` gravity package]** The formal content we use from the paper's gravity reading:
the action decomposes, the fields admit the spin-connection/dreibein interpretation, the Euclidean
sector has negative cosmological constant, and the resulting tetrad geometry is gauge invariant. -/
theorem sl2c_CSW_gravity_package (G : SL2CCSWGravityCarrier) :
    G.complexAction = G.exoticTerm + G.einsteinHilbertTerm
      ∧ G.spinConnectionDreibeinInterpretation
      ∧ G.euclideanNegativeCosmologicalConstant
      ∧ G.tetradInvariantGeometry :=
  ⟨G.action_decomposition, G.spinConnectionDreibeinInterpretation_holds,
    G.euclideanNegativeCosmologicalConstant_holds, G.tetradInvariantGeometry_holds⟩

/-- **[Hayashi uses the existing `SL(2,ℂ)` double cover].** The `SL(2,ℂ)` structure available in Physlib maps
the Bogoliubov spinor boost to the Lorentz boost with doubled rapidity, and the same component equals the
one-loop fermion determinant structure. This is the concrete repo hook for Hayashi's `SL(2,ℂ)` gravity
sector. -/
theorem hayashi_sl2c_doubleCover_bridge (η : ℝ) :
    (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
        = bogoliubovEnergy (Real.sinh (2 * η)) 1
      ∧ (SL2C.toLorentzGroup (bogoSL2C η)).1 (Sum.inl 0) (Sum.inl 0)
          = berezin (fermionGaussian (bogoliubovEnergy (Real.sinh (2 * η)) 1)) :=
  sl2c_doubleCover_bridge η

/-- **[Hayashi dreibein/tetrad sector uses the existing Lorentz-gauge invariant geometry].** Under local
Lorentz gauge `E ↦ ΛE`, the Lusanna tetrad proper separation is unchanged. This is the repo-level
geometric representative for the `e` field in Hayashi's `A = ω + i e`. -/
theorem hayashi_tetrad_properSeparation_lorentz_invariant {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hΛ : Λ ∈ LorentzGroup d)
    (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq (Λ * E) x = properSeparationSq E x :=
  properSeparationSq_lorentz_gauge hΛ x

/-! ## §D — Wheeler-DeWitt replaced by parallel transport -/

/-- Hayashi's CSW-gravity replacement interface: a Wheeler-DeWitt physical-state predicate is replaced by
parallel transport in the quantum bundle over complex structures. -/
structure HayashiParallelTransportReplacement (State : Type*) where
  wheelerDeWittPhysical : State → Prop
  parallelTransportPhysical : State → Prop
  replacement : ∀ ψ, wheelerDeWittPhysical ψ ↔ parallelTransportPhysical ψ

/-- **[WDW ↔ CSW parallel transport]** In a structure satisfying Hayashi's replacement interface, being a
Wheeler-DeWitt physical state is equivalent to being a CSW parallel-transport physical state. -/
theorem wheelerDeWitt_iff_parallelTransport {State : Type*}
    (R : HayashiParallelTransportReplacement State) (ψ : State) :
    R.wheelerDeWittPhysical ψ ↔ R.parallelTransportPhysical ψ :=
  R.replacement ψ

/-- **[existing WDW structure implies Hayashi parallel transport].** If the Hayashi replacement predicate is
instantiated by the existing `WheelerDeWitt` equation, then any Physlib Wheeler-DeWitt solution is a
Hayashi parallel-transport physical state. -/
theorem wheelerDeWitt_solution_is_hayashi_parallel
    (R : HayashiParallelTransportReplacement ℂ) (HR HI : ℝ) (Ψ : ℂ)
    (hWDW : R.wheelerDeWittPhysical Ψ ↔ WheelerDeWitt HR HI Ψ)
    (h : WheelerDeWitt HR HI Ψ) :
    R.parallelTransportPhysical Ψ :=
  (R.replacement Ψ).mp (hWDW.mpr h)

/-! ## §E — torus Hilbert-space, orthogonality, and invariant factorization -/

/-- Conditional form of Hayashi's torus theorem: a `G_c` physical state is assembled from left and right
compact-sector states. -/
structure TorusHilbertFactorization (GcState LeftState RightState : Type*) where
  leftState : GcState → LeftState
  rightState : GcState → RightState
  assemble : LeftState → RightState → GcState
  state_factorizes : ∀ ψ, assemble (leftState ψ) (rightState ψ) = ψ
  finiteDimensionalAtSpecialLevels : Prop
  finiteDimensionalAtSpecialLevels_holds : finiteDimensionalAtSpecialLevels

/-- **[Torus physical states factorize].** Every state in a Hayashi torus factorization structure is
recovered from its holomorphic and anti-holomorphic compact-sector components. -/
theorem torus_state_factorizes {GcState LeftState RightState : Type*}
    (F : TorusHilbertFactorization GcState LeftState RightState) (ψ : GcState) :
    F.assemble (F.leftState ψ) (F.rightState ψ) = ψ :=
  F.state_factorizes ψ

/-- **[Special levels give the finite-dimensional torus case].** This field records Hayashi's restriction
to special integral levels where the torus physical Hilbert space is finite-dimensional. -/
theorem torus_finiteDimensionalAtSpecialLevels {GcState LeftState RightState : Type*}
    (F : TorusHilbertFactorization GcState LeftState RightState) :
    F.finiteDimensionalAtSpecialLevels :=
  F.finiteDimensionalAtSpecialLevels_holds

/-- Orthogonality representative for Hayashi's torus basis: distinct conserved charges give zero inner product. -/
structure HayashiOrthogonalityCarrier (State Charge : Type*) where
  inner : State → State → ℂ
  charge : State → Charge
  orthogonal_of_charge_ne : ∀ ψ φ, charge ψ ≠ charge φ → inner ψ φ = 0

/-- **[Charge conservation gives orthogonality].** In Hayashi's torus basis structure, states with different
charges are orthogonal. -/
theorem orthogonal_of_charge_ne {State Charge : Type*} (O : HayashiOrthogonalityCarrier State Charge)
    (ψ φ : State) (h : O.charge ψ ≠ O.charge φ) :
    O.inner ψ φ = 0 :=
  O.orthogonal_of_charge_ne ψ φ h

/-- Conditional form of Hayashi's genus-one/lens-space invariant factorization: a complex-group invariant
is the product of the right and left compact-sector invariants. -/
structure TopologicalInvariantFactorization (Observable Value : Type*) [Mul Value] where
  leftInvariant : Observable → Value
  rightInvariant : Observable → Value
  complexInvariant : Observable → Value
  factorizes : ∀ O, complexInvariant O = rightInvariant O * leftInvariant O

/-- **[Hayashi invariant factorization]** Every genus-one `G_c` CSW invariant in the structure factors into
right and left compact-sector invariants, matching Hayashi's equation (5.19). -/
theorem topologicalInvariant_factorizes {Observable Value : Type*} [Mul Value]
    (F : TopologicalInvariantFactorization Observable Value) (O : Observable) :
    F.complexInvariant O = F.rightInvariant O * F.leftInvariant O :=
  F.factorizes O

/-! ## §F — links to Bose/Fermi field operators and CAR/Bogoliubov structures -/

/-- **[Hayashi torus sector ↔ Kálnay Bose/Fermi field operators].** A factorized Hayashi torus state can be stated together with the repo's concrete Bose-bilinear fermion-field statement: the fermion generator is a
Bose-bilinear word and its sector representation satisfies the CAR. -/
theorem hayashi_torus_factorization_kalnay_bose_fermi_fields
    {GcState LeftState RightState : Type*}
    (F : TorusHilbertFactorization GcState LeftState RightState) (ψ : GcState) (p : Momentum 3) :
    F.assemble (F.leftState ψ) (F.rightState ψ) = ψ
      ∧ KalnayBoseFermiFieldStatement p :=
  ⟨torus_state_factorizes F ψ, kalnay_bose_fermi_field_statement p⟩

/-- **[Hayashi invariant factorization ↔ Kálnay field operators].** Hayashi's genus-one/lens-space
factorization can be used in the same theorem as the Kálnay Bose-bilinear construction of fermion fields
from Bose field operators. -/
theorem hayashi_invariant_factorization_kalnay_bose_fermi_fields
    {Observable Value : Type*} [Mul Value]
    (F : TopologicalInvariantFactorization Observable Value) (O : Observable) (p : Momentum 3) :
    F.complexInvariant O = F.rightInvariant O * F.leftInvariant O
      ∧ KalnayBoseFermiFieldStatement p :=
  ⟨topologicalInvariant_factorizes F O, kalnay_bose_fermi_field_statement p⟩

/-- **[CSW parallel transport ↔ Kálnay field operators].** When a Physlib Wheeler-DeWitt solution is
identified with Hayashi's CSW parallel-transport physical state, the same theorem includes the Kálnay
Bose/Fermi field-operator statement. -/
theorem hayashi_parallel_transport_kalnay_bose_fermi_fields
    (R : HayashiParallelTransportReplacement ℂ) (HR HI : ℝ) (Ψ : ℂ) (p : Momentum 3)
    (hWDW : R.wheelerDeWittPhysical Ψ ↔ WheelerDeWitt HR HI Ψ)
    (h : WheelerDeWitt HR HI Ψ) :
    R.parallelTransportPhysical Ψ ∧ KalnayBoseFermiFieldStatement p :=
  ⟨wheelerDeWitt_solution_is_hayashi_parallel R HR HI Ψ hWDW h,
    kalnay_bose_fermi_field_statement p⟩

/-- **[Hayashi ↔ Dirac field-operator Bogoliubov CAR].** The Hayashi sector bridge can be paired with the
repo's Dirac `FieldSpecification` operator layer: the abstract Dirac Bogoliubov element has the canonical
anticommutator in the Fock representation, while the Kálnay finite sector simultaneously realizes a
fermion field from Bose bilinears. -/
theorem hayashi_dirac_bogoliubov_field_operator_link (u v : ℂ) (p : Momentum 3) :
    KalnayBoseFermiFieldStatement p
      ∧ fockRepHom (bogElement u v p * bogElementDag u v p + bogElementDag u v p * bogElement u v p)
          = ((u ^ 2 + v ^ 2 : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨kalnay_bose_fermi_field_statement p, fock_bogoliubov_CAR u v p⟩

/-- **[Canonical Dirac Bogoliubov + Kálnay Bose/Fermi field].** At Foldy-Wouthuysen normalization
`u² + v² = 1`, the Dirac field-operator Bogoliubov element is canonical in the Fock representation, and
the Kálnay Bose-bilinear field operator statement is available at the same momentum. -/
theorem hayashi_dirac_bogoliubov_canonical_with_kalnay_fields
    (u v : ℂ) (p : Momentum 3) (h : u ^ 2 + v ^ 2 = 1) :
    KalnayBoseFermiFieldStatement p
      ∧ fockRepHom (bogElement u v p * bogElementDag u v p + bogElementDag u v p * bogElement u v p)
          = 1 :=
  ⟨kalnay_bose_fermi_field_statement p, fw_fock_bogoliubov_canonical u v p h⟩

/-- The complete lightweight Hayashi bridge used by the repo: CSW action splitting, `SL(2,ℂ)` gravity,
WDW/parallel-transport replacement, torus state factorization, and topological-invariant factorization. -/
structure HayashiCSWGravityBridge
    (Field State GcState LeftState RightState Observable Value Charge : Type*) [Mul Value] where
  actionSplit : ComplexCSWAction Field
  gravity : SL2CCSWGravityCarrier
  parallelReplacement : HayashiParallelTransportReplacement State
  torusFactorization : TorusHilbertFactorization GcState LeftState RightState
  invariantFactorization : TopologicalInvariantFactorization Observable Value
  orthogonality : HayashiOrthogonalityCarrier GcState Charge

/-- **[Hayashi bridge synthesis].** The repo-level statement: assuming the five Hayashi structures, Lean
checks that the complex CSW action splits, the `SL(2,ℂ)` gravity package is available, WDW states are
equivalent to parallel-transport states, torus states factorize, topological invariants factorize, and
charge separation implies orthogonality. -/
theorem hayashi_CSW_gravity_bridge_synthesis
    {Field State GcState LeftState RightState Observable Value Charge : Type*} [Mul Value]
    (B : HayashiCSWGravityBridge Field State GcState LeftState RightState Observable Value Charge)
    (A : Field) (ψ : State) (Ψ : GcState) (O : Observable) (φ : GcState)
    (hcharge : B.orthogonality.charge Ψ ≠ B.orthogonality.charge φ) :
    B.actionSplit.totalAction A =
        B.actionSplit.holomorphicAction A + B.actionSplit.antiholomorphicAction A
      ∧ B.gravity.complexAction = B.gravity.exoticTerm + B.gravity.einsteinHilbertTerm
      ∧ (B.parallelReplacement.wheelerDeWittPhysical ψ
          ↔ B.parallelReplacement.parallelTransportPhysical ψ)
      ∧ B.torusFactorization.assemble
          (B.torusFactorization.leftState Ψ) (B.torusFactorization.rightState Ψ) = Ψ
      ∧ B.invariantFactorization.complexInvariant O =
          B.invariantFactorization.rightInvariant O * B.invariantFactorization.leftInvariant O
      ∧ B.orthogonality.inner Ψ φ = 0 :=
  ⟨complexCSWAction_split B.actionSplit A, B.gravity.action_decomposition,
    wheelerDeWitt_iff_parallelTransport B.parallelReplacement ψ,
    torus_state_factorizes B.torusFactorization Ψ,
    topologicalInvariant_factorizes B.invariantFactorization O,
    orthogonal_of_charge_ne B.orthogonality Ψ φ hcharge⟩

/-- **[Hayashi + Bose/Fermi operator synthesis].** The full bridge now also exposes the field-operator
content: alongside CSW action splitting, `SL(2,ℂ)` gravity, WDW/parallel-transport equivalence, torus
factorization, topological-invariant factorization, and orthogonality, the Kálnay Bose-bilinear fermion
field statement is available for the same formal sector. -/
theorem hayashi_CSW_gravity_bose_fermi_operator_synthesis
    {Field State GcState LeftState RightState Observable Value Charge : Type*} [Mul Value]
    (B : HayashiCSWGravityBridge Field State GcState LeftState RightState Observable Value Charge)
    (A : Field) (ψ : State) (Ψ : GcState) (O : Observable) (φ : GcState) (p : Momentum 3)
    (hcharge : B.orthogonality.charge Ψ ≠ B.orthogonality.charge φ) :
    B.actionSplit.totalAction A =
        B.actionSplit.holomorphicAction A + B.actionSplit.antiholomorphicAction A
      ∧ B.gravity.complexAction = B.gravity.exoticTerm + B.gravity.einsteinHilbertTerm
      ∧ (B.parallelReplacement.wheelerDeWittPhysical ψ
          ↔ B.parallelReplacement.parallelTransportPhysical ψ)
      ∧ B.torusFactorization.assemble
          (B.torusFactorization.leftState Ψ) (B.torusFactorization.rightState Ψ) = Ψ
      ∧ B.invariantFactorization.complexInvariant O =
          B.invariantFactorization.rightInvariant O * B.invariantFactorization.leftInvariant O
      ∧ B.orthogonality.inner Ψ φ = 0
      ∧ KalnayBoseFermiFieldStatement p :=
  ⟨complexCSWAction_split B.actionSplit A, B.gravity.action_decomposition,
    wheelerDeWitt_iff_parallelTransport B.parallelReplacement ψ,
    torus_state_factorizes B.torusFactorization Ψ,
    topologicalInvariant_factorizes B.invariantFactorization O,
    orthogonal_of_charge_ne B.orthogonality Ψ φ hcharge,
    kalnay_bose_fermi_field_statement p⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
