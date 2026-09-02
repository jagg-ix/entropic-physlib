/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2CoproductV2
public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

/-!
# Hopf algebra data as the algebraic carrier of Wilson loops

This file links the Hopf-algebra layer to the Chern-Simons/Wilson-loop layer without adding a new
Reshetikhin-Turaev construction.  The theorem-level links are the common carriers already formalized in the
repo:

* Hopf charge states multiply by charge addition, and Wilson point charges fuse by the same addition rule.
* The Hopf antipode is charge negation, while the modular `S²` matrix is charge conjugation on the same
  finite charge lattice.
* Sawin's braid matrices satisfy Yang-Baxter, and the Wilson braiding phase is the Verlinde `S` kernel.
* The Hopf ribbon twist is exactly the Wilson topological spin carrier, with the fermion sign at spin `1/2`.
* The coproduct relations and Wilson/Verlinde diagonalization are available together from one bridge import.


-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2CoproductV2
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop

/-- **[Hopf product = Wilson fusion of charges]** the Hopf charge basis has product
`|a⟩ |b⟩ = |a+b⟩`, and the Wilson/Verlinde point-charge convolution has the same fusion rule
`δ_a ⋆ δ_b = δ_{a+b}`. -/
lemma hopf_charge_addition_matches_wilson_fusion (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    chargeState (a.val : ℤ) * chargeState (b.val : ℤ)
        = chargeState ((a.val : ℤ) + (b.val : ℤ))
      ∧ cswConvolution (Pi.single a 1) (Pi.single b (1 : ℂ)) = Pi.single (a + b) 1 := by
  exact ⟨chargeState_mul (a.val : ℤ) (b.val : ℤ), cswConvolution_single hk a b⟩

/-- **[Hopf antipode = modular charge conjugation]** the Hopf antipode sends a charge state to the opposite
charge, is involutive, and the CSW modular matrix has `S² = C` on the same charge lattice. -/
lemma hopf_antipode_matches_modular_charge_conjugation (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    HopfAlgebra.antipode ℂ (chargeState (a.val : ℤ)) = chargeState (-(a.val : ℤ))
      ∧ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ (chargeState (a.val : ℤ)))
          = chargeState (a.val : ℤ)
      ∧ (∑ c : Fin k, cswSMatrix k a c * cswSMatrix k c b)
          = if (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ)) then 1 else 0 := by
  exact ⟨antipode_chargeState (a.val : ℤ), antipode_chargeState_involutive (a.val : ℤ),
    cswSMatrix_sq_eq_chargeConjugation k hk a b⟩

/-- **[Hopf/R-matrix braiding = Wilson braiding kernel]** Sawin's braid matrices obey the Yang-Baxter
relation, while the Wilson braiding phase is exactly the conjugate Verlinde `S` kernel up to the `√k`
normalization. -/
lemma hopf_rmatrix_yangBaxter_matches_wilson_braiding
    (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    braidC1 s * braidC2 s * braidC1 s = braidC2 s * braidC1 s * braidC2 s
      ∧ wilsonBraidingPhase k a b
          = (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b) := by
  exact ⟨braid_yangBaxter s hs, wilsonBraidingPhase_eq_S k hk a b⟩

/-- **[Hopf ribbon twist = Wilson topological spin]** the Wilson-loop topological spin is the same carrier
as the Hopf ribbon twist, evaluated at the Wilson conformal weight. -/
lemma hopf_ribbon_twist_is_wilson_topological_spin (k : ℕ) (a : Fin k) :
    wilsonTopologicalSpin k a = ribbonTwist (wilsonConformalWeight k a)
      ∧ wilsonTopologicalSpin k a = ribbonTwist ((a.val : ℝ) ^ 2 / (2 * k)) := by
  exact ⟨rfl, wilsonTopologicalSpin_eq_ribbonTwist k a⟩

/-- **[Fermion ribbon sign as Wilson topological spin]** when a Wilson charge has conformal weight `1/2`,
its Wilson topological spin is the Hopf fermion ribbon sign. -/
lemma hopf_ribbon_wilson_fermion_sign (k : ℕ) (hk : 0 < k) (a : Fin k)
    (h : (a.val : ℝ) ^ 2 = k) :
    ribbonTwist (1 / 2) = -1 ∧ wilsonTopologicalSpin k a = ribbonTwist (1 / 2) := by
  refine ⟨ribbonTwist_fermion, ?_⟩
  rw [wilsonTopologicalSpin_fermion k hk a h, ribbonTwist_fermion]

/-! ### Semion/anyon carrier -/

/-- The `U(1)₂` semion is available as a Hopf-ribbon/Wilson carrier: its
Wilson topological spin is the Hopf ribbon twist, its conformal weight is
`1/4`, and that weight is neither the boson value `0` nor the fermion value
`1/2`. -/
def HasHopfWilsonSemionBridge : Prop :=
  HasSemionAnyonCarrier
    ∧ wilsonTopologicalSpin 2 semionCharge = ribbonTwist (wilsonConformalWeight 2 semionCharge)
    ∧ wilsonConformalWeight 2 semionCharge = 1 / 4
    ∧ wilsonConformalWeight 2 semionCharge ≠ 0
    ∧ wilsonConformalWeight 2 semionCharge ≠ 1 / 2

/-- The semion bridge is checked from the Wilson-loop anyon carrier and the Hopf
ribbon-twist definition of topological spin. -/
lemma hopf_wilson_semion_bridge_checked : HasHopfWilsonSemionBridge := by
  rcases semionConformalWeight_not_boson_or_fermion with ⟨hnotBoson, hnotFermion⟩
  exact ⟨semionAnyonCarrier_checked, rfl, semionConformalWeight_quarter,
    hnotBoson, hnotFermion⟩

/-- The Yang-Baxter braid relation and the semion anyon carrier are available
together from the Hopf/Wilson bridge. -/
lemma hopf_yangBaxter_with_semion_sector (s : ℂ) (hs : s ≠ 0) :
    braidC1 s * braidC2 s * braidC1 s = braidC2 s * braidC1 s * braidC2 s
      ∧ HasHopfWilsonSemionBridge :=
  ⟨braid_yangBaxter s hs, hopf_wilson_semion_bridge_checked⟩

/-- The Hopf/Wilson semion bridge is the same level-2 semion used by the
half-filled FQHE topological-order bundle. The only analytic input required for
the complete bundle is the existing CSW geometric-quantization package. -/
lemma hopf_wilson_semion_with_halfFilling_topologicalOrder
    (G : CSWGeometricQuantizationPackage 2 (by norm_num)) :
    HasHopfWilsonSemionBridge ∧ HasHalfFillingCompleteTopologicalOrder :=
  ⟨hopf_wilson_semion_bridge_checked,
    halfFilling_completeTopologicalOrder_checked G⟩

/-- **[Coproduct relations and Wilson diagonalization in one bridge]** the quantum-group coproduct relations
and the Wilson/Verlinde diagonalization theorem are jointly available: the Hopf algebra supplies the tensor
charge action, and the Wilson operators are diagonalized by the modular `S` basis. -/
lemma hopf_coproduct_relations_with_wilson_diagonalization
    (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) (a q : Fin k) :
    coΔH * coΔX s - coΔX s * coΔH = 2 * coΔX s
      ∧ coΔH * coΔY s - coΔY s * coΔH = -(2 * coΔY s)
      ∧ (s ^ 2 - (s ^ 2)⁻¹) • (coΔX s * coΔY s - coΔY s * coΔX s)
          = coSPow2H s - coSPowm2H s
      ∧ cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
          = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) := by
  exact ⟨coproduct_relation_hx s hs, coproduct_relation_hy s, coproduct_relation_xy s hs,
    cswWilsonVerlinde_diagonalization k hk a q⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop

end
