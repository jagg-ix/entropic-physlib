/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-!
# Hatsugai bulk-edge correspondence for the integer quantum Hall effect

Formalizes the Lean-checkable core of Y. Hatsugai,
*Chern Number and Edge States in the Integer Quantum Hall Effect*,
Phys. Rev. Lett. 71, 3697 (1993).

The paper identifies two topological readings of the same integer Hall
conductance:

* the TKNN Chern number of the bulk Bloch bundle over the magnetic Brillouin
  torus, written as the normalized Berry-curvature integral;
* the winding number of edge-state zeros on the hyperelliptic energy surface
  of the transfer-matrix problem.

The heavy analytic inputs are explicit here.  A caller must provide:

* the Harper spectral data/trace factorization for the chosen rational flux;
* a normalized TKNN curvature witness;
* a finite set of bulk vortices/edge degeneracies after the gap is fixed;
* the local Hatsugai matching saying that the bulk vortex contribution at a
  touching point equals the edge-state winding contribution.

From these assumptions Lean proves the global statement:
`bulk Chern number = edge winding`, hence the Hall conductance in units of
`e^2/h` is the edge winding number.


-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge

open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling


/-- Hatsugai Eq. (1), localized at one lattice site.  The neighboring values
are supplied explicitly so this can also be used as a transfer-step equation. -/
def HarperEquationAt
    (t E ky flux : ℝ) (ψprev ψ ψnext : ℝ) (m : ℤ) : Prop :=
  -t * (ψnext + ψprev)
    - 2 * t * Real.cos (ky - 2 * Real.pi * flux * (m : ℝ)) * ψ = E * ψ

/-- Dimensionless Harper recurrence extracted from Eq. (8)-(9):
`ψ_{m+1} = (-ε - 2 cos θ) ψ_m - ψ_{m-1}`. -/
def HarperRecurrenceAt (ε θ : ℝ) (ψprev ψ ψnext : ℝ) : Prop :=
  ψnext = (-ε - 2 * Real.cos θ) * ψ - ψprev

/-- Dividing Hatsugai Eq. (1) by the hopping `t ≠ 0` gives the transfer-matrix
recurrence with dimensionless energy `ε = E/t`. -/
lemma harperEquationAt_iff_recurrence
    {t E ky flux ε θ ψprev ψ ψnext : ℝ} {m : ℤ}
    (ht : t ≠ 0)
    (hE : E = t * ε)
    (hθ : θ = ky - 2 * Real.pi * flux * (m : ℝ)) :
    HarperEquationAt t E ky flux ψprev ψ ψnext m ↔
      HarperRecurrenceAt ε θ ψprev ψ ψnext := by
  constructor
  · intro h
    subst E
    subst θ
    dsimp [HarperEquationAt, HarperRecurrenceAt] at h ⊢
    have hzero :
        t * (ψnext + ψprev
          + 2 * Real.cos (ky - 2 * Real.pi * flux * (m : ℝ)) * ψ
          + ε * ψ) = 0 := by
      nlinarith [h]
    have hsum :
        ψnext + ψprev
          + 2 * Real.cos (ky - 2 * Real.pi * flux * (m : ℝ)) * ψ
          + ε * ψ = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left ht
    nlinarith
  · intro h
    subst E
    subst θ
    dsimp [HarperEquationAt, HarperRecurrenceAt] at h ⊢
    rw [h]
    ring

/-- Strip geometry boundary condition, Hatsugai Eq. (6):
`ψ_0 = ψ_{L+1} = 0`. -/
def StripDirichletBoundary (L : ℕ) (ψ : ℤ → ℝ) : Prop :=
  ψ 0 = 0 ∧ ψ ((L : ℤ) + 1) = 0

/-- Infinite periodic geometry boundary condition, Hatsugai Eq. (7):
`ψ_{m+q} = ρ ψ_m`, with `ρ = exp(i q k_x)` in the paper. -/
def BlochBoundary (q : ℕ) (ρ : ℝ) (ψ : ℤ → ℝ) : Prop :=
  ∀ m : ℤ, ψ (m + (q : ℤ)) = ρ * ψ m

lemma StripDirichletBoundary.left {L : ℕ} {ψ : ℤ → ℝ}
    (h : StripDirichletBoundary L ψ) :
    ψ 0 = 0 :=
  h.1

lemma StripDirichletBoundary.right {L : ℕ} {ψ : ℤ → ℝ}
    (h : StripDirichletBoundary L ψ) :
    ψ ((L : ℤ) + 1) = 0 :=
  h.2

lemma BlochBoundary.shift {q : ℕ} {ρ : ℝ} {ψ : ℤ → ℝ}
    (h : BlochBoundary q ρ ψ) (m : ℤ) :
    ψ (m + (q : ℤ)) = ρ * ψ m :=
  h m


/-- Rational magnetic flux per plaquette `φ = p/q`. -/
def rationalMagneticFlux (p q : ℕ) : ℚ := (p : ℚ) / (q : ℚ)

/-- In the rational-flux Harper problem there are `q` magnetic subbands. -/
def magneticBandCount (q : ℕ) : ℕ := q

/-- For `q` bands there are `q-1` stable gaps when no gap closes. -/
def magneticGapCount (q : ℕ) : ℕ := q - 1

/-- Hatsugai's complex energy surface has genus equal to the number of gaps:
`g = q-1`. -/
def hatsugaiRiemannSurfaceGenus (q : ℕ) : ℕ := q - 1

/-- The number of edge-state loops is the same `q-1` count as the genus/gaps. -/
def hatsugaiEdgeLoopCount (q : ℕ) : ℕ := q - 1

lemma hatsugai_genus_eq_gapCount (q : ℕ) :
    hatsugaiRiemannSurfaceGenus q = magneticGapCount q := rfl

lemma hatsugai_edgeLoopCount_eq_gapCount (q : ℕ) :
    hatsugaiEdgeLoopCount q = magneticGapCount q := rfl

lemma hatsugai_genus_succ_eq_bandCount (q : ℕ) (hq : 0 < q) :
    hatsugaiRiemannSurfaceGenus q + 1 = magneticBandCount q := by
  unfold hatsugaiRiemannSurfaceGenus magneticBandCount
  omega

/-- The one-step Harper transfer matrix used in Hatsugai Eq. (9):
`[[-ε - 2 cos θ, -1], [1, 0]]`. -/
def hatsugaiTransferMatrix (ε θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-ε - 2 * Real.cos θ, -1; 1, 0]

/-- The Harper transfer matrix is unimodular.  This is the algebraic reason
the characteristic equation has the hyperelliptic form `w² = Δ² - 4`. -/
lemma hatsugaiTransferMatrix_det (ε θ : ℝ) :
    (hatsugaiTransferMatrix ε θ).det = 1 := by
  simp [hatsugaiTransferMatrix, Matrix.det_fin_two]

/-- Multiplication by Hatsugai's one-step transfer matrix is exactly the
dimensionless Harper recurrence. -/
lemma hatsugaiTransferMatrix_mulVec (ε θ ψ ψprev : ℝ) :
    (hatsugaiTransferMatrix ε θ).mulVec ![ψ, ψprev] =
      ![(-ε - 2 * Real.cos θ) * ψ - ψprev, ψ] := by
  ext i
  fin_cases i
  · simp [hatsugaiTransferMatrix, Matrix.mulVec]
    ring
  · simp [hatsugaiTransferMatrix, Matrix.mulVec]

/-- A solution of the scalar recurrence is equivalently advanced by the
transfer matrix. -/
lemma harperRecurrence_transferMatrix_step
    {ε θ ψprev ψ ψnext : ℝ}
    (h : HarperRecurrenceAt ε θ ψprev ψ ψnext) :
    (hatsugaiTransferMatrix ε θ).mulVec ![ψ, ψprev] = ![ψnext, ψ] := by
  rw [hatsugaiTransferMatrix_mulVec, h]

/-- The hyperelliptic discriminant appearing in Hatsugai's energy surface:
`w² = Δ(E)² - 4`. -/
def hatsugaiHyperellipticDiscriminant (trace : ℝ) : ℝ :=
  trace ^ 2 - 4

lemma hatsugaiHyperellipticDiscriminant_eq_zero_iff (trace : ℝ) :
    hatsugaiHyperellipticDiscriminant trace = 0 ↔ trace ^ 2 = 4 := by
  unfold hatsugaiHyperellipticDiscriminant
  constructor <;> intro h <;> linarith

/-- Product over the `2q` band edges in Hatsugai's factorization
`Δ(z)^2 - 4 = ∏ᵢ (z - Aᵢ)`. -/
def hatsugaiBandEdgeProduct {n : ℕ} (bandEdge : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∏ i, (z - bandEdge i)

/-- Paper-level branch-factorization data for the hyperelliptic energy
surface.  The factorization itself is analytic/spectral input; its branch-point
consequences are algebraic and proved below. -/
structure HatsugaiBranchFactorization (q : ℕ) where
  trace : ℝ → ℝ
  bandEdge : Fin (2 * q) → ℝ
  discriminant_factorizes :
    ∀ z, hatsugaiHyperellipticDiscriminant (trace z) =
      hatsugaiBandEdgeProduct bandEdge z

/-- A branch point of Hatsugai's energy surface is a zero of `Δ(z)^2 - 4`. -/
def IsHatsugaiBranchPoint {q : ℕ} (F : HatsugaiBranchFactorization q) (z : ℝ) : Prop :=
  hatsugaiHyperellipticDiscriminant (F.trace z) = 0

namespace HatsugaiBranchFactorization

variable {q : ℕ}

/-- Every listed band edge is a branch point of the hyperelliptic surface. -/
lemma bandEdge_is_branchPoint (F : HatsugaiBranchFactorization q)
    (i : Fin (2 * q)) :
    IsHatsugaiBranchPoint F (F.bandEdge i) := by
  unfold IsHatsugaiBranchPoint
  rw [F.discriminant_factorizes]
  unfold hatsugaiBandEdgeProduct
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end HatsugaiBranchFactorization


/-- TKNN witness for one isolated filled band or filled-band block.  It records
Hatsugai Eq. (2): the Chern integer is the normalized integral of the Berry
curvature over the magnetic Brillouin zone. -/
structure TKNNBerryCurvatureWitness (MBZ : Type*) [MeasurableSpace MBZ] where
  μ : Measure MBZ
  berryCurvature : MBZ → ℝ
  chernNumber : ℤ
  chern_eq_normalized_integral :
    (chernNumber : ℝ) =
      (1 / (2 * Real.pi)) * ∫ k, berryCurvature k ∂ μ

namespace TKNNBerryCurvatureWitness

variable {MBZ : Type*} [MeasurableSpace MBZ]
variable (T : TKNNBerryCurvatureWitness MBZ)

/-- Hall conductance in units of `e²/h` is the TKNN integer. -/
def hallConductanceUnits : ℝ := T.chernNumber

/-- The Hall conductance equals the normalized Berry-curvature integral. -/
lemma hallConductanceUnits_eq_normalized_integral :
    T.hallConductanceUnits =
      (1 / (2 * Real.pi)) * ∫ k, T.berryCurvature k ∂ T.μ := by
  simpa [hallConductanceUnits] using T.chern_eq_normalized_integral

/-- This TKNN conductance is the same natural-unit carrier used elsewhere in
the repository's Hall formalization. -/
lemma hallConductanceUnits_eq_repo_hallConductanceUnits :
    T.hallConductanceUnits =
      Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.hallConductanceUnits
        (T.chernNumber : ℝ) := rfl

end TKNNBerryCurvatureWitness


/-- A bulk/edge touching point: Hatsugai's local statement is that the vortex
of the bulk Bloch wavefunction at the band-edge degeneracy is the same integer
as the edge-state winding contribution. -/
structure HatsugaiTouching where
  /-- Local vorticity of the bulk Bloch-function zero. -/
  bulkVorticity : ℤ
  /-- Local edge-state winding contribution. -/
  edgeWindingContribution : ℤ
  /-- Hatsugai's local bulk-edge matching at this degeneracy. -/
  local_match : bulkVorticity = edgeWindingContribution

namespace HatsugaiTouching

/-- Each local touching has equal bulk and edge contribution. -/
lemma bulkVorticity_eq_edgeWindingContribution (x : HatsugaiTouching) :
    x.bulkVorticity = x.edgeWindingContribution :=
  x.local_match

end HatsugaiTouching

/-- Total vorticity of the bulk wavefunction zeros, Hatsugai Eq. (5). -/
def totalBulkVorticity {ι : Type*} [Fintype ι] (touching : ι → HatsugaiTouching) : ℤ :=
  ∑ i, (touching i).bulkVorticity

/-- Total winding number of the corresponding edge-state loop, Hatsugai
Eq. (14). -/
def totalEdgeWinding {ι : Type*} [Fintype ι] (touching : ι → HatsugaiTouching) : ℤ :=
  ∑ i, (touching i).edgeWindingContribution

/-- Local Hatsugai matching sums to the global equality between bulk vortex
number and edge winding. -/
lemma totalBulkVorticity_eq_totalEdgeWinding
    {ι : Type*} [Fintype ι] (touching : ι → HatsugaiTouching) :
    totalBulkVorticity touching = totalEdgeWinding touching := by
  unfold totalBulkVorticity totalEdgeWinding
  exact Finset.sum_congr rfl fun i _ => (touching i).local_match


/-- A finite-gap Hatsugai IQHE system.  The type `ι` indexes the finitely many
bulk zero/edge touching events for the chosen gap. -/
structure HatsugaiBulkEdgeSystem
    (MBZ : Type*) [MeasurableSpace MBZ] (ι : Type*) [Fintype ι] where
  tknn : TKNNBerryCurvatureWitness MBZ
  touching : ι → HatsugaiTouching
  edgeWinding : ℤ
  /-- Hatsugai Eq. (5): the TKNN integer is the total bulk vorticity. -/
  chern_eq_totalBulkVorticity :
    tknn.chernNumber = totalBulkVorticity touching
  /-- Hatsugai Eq. (14): the edge winding is the sum of edge contributions. -/
  edgeWinding_eq_totalEdgeWinding :
    edgeWinding = totalEdgeWinding touching

namespace HatsugaiBulkEdgeSystem

variable {MBZ ι : Type*} [MeasurableSpace MBZ] [Fintype ι]
variable (S : HatsugaiBulkEdgeSystem MBZ ι)

/-- Hatsugai's main bulk-edge equality: the TKNN Chern number equals the
edge-state winding number. -/
lemma chernNumber_eq_edgeWinding :
    S.tknn.chernNumber = S.edgeWinding := by
  rw [S.chern_eq_totalBulkVorticity, S.edgeWinding_eq_totalEdgeWinding]
  exact totalBulkVorticity_eq_totalEdgeWinding S.touching

/-- The integer Hall conductance in natural units is the edge winding. -/
lemma hallConductanceUnits_eq_edgeWinding :
    S.tknn.hallConductanceUnits = (S.edgeWinding : ℝ) := by
  have h : (S.tknn.chernNumber : ℝ) = (S.edgeWinding : ℝ) := by
    exact_mod_cast S.chernNumber_eq_edgeWinding
  simpa [TKNNBerryCurvatureWitness.hallConductanceUnits] using h

/-- The normalized TKNN Berry-curvature integral equals the edge-state winding. -/
lemma normalizedBerryIntegral_eq_edgeWinding :
    (1 / (2 * Real.pi)) * ∫ k, S.tknn.berryCurvature k ∂ S.tknn.μ =
      (S.edgeWinding : ℝ) := by
  calc
    (1 / (2 * Real.pi)) * ∫ k, S.tknn.berryCurvature k ∂ S.tknn.μ
        = (S.tknn.chernNumber : ℝ) := S.tknn.chern_eq_normalized_integral.symm
    _ = (S.edgeWinding : ℝ) := by
        exact_mod_cast S.chernNumber_eq_edgeWinding

/-- Repository-level form: the existing Hall-conductance carrier applied to
the TKNN integer is the edge winding. -/
lemma repoHallConductanceUnits_eq_edgeWinding :
    Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.hallConductanceUnits
        (S.tknn.chernNumber : ℝ) = (S.edgeWinding : ℝ) := by
  have h : (S.tknn.chernNumber : ℝ) = (S.edgeWinding : ℝ) := by
    exact_mod_cast S.chernNumber_eq_edgeWinding
  simpa [Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.hallConductanceUnits]
    using h

/-- Full critical Hatsugai package: TKNN integral, bulk vortex sum, edge
winding sum, and the bulk-edge equality all hold together. -/
def HasHatsugaiBulkEdgeCorrespondence : Prop :=
  S.tknn.hallConductanceUnits =
      (1 / (2 * Real.pi)) * ∫ k, S.tknn.berryCurvature k ∂ S.tknn.μ
    ∧ S.tknn.chernNumber = totalBulkVorticity S.touching
    ∧ S.edgeWinding = totalEdgeWinding S.touching
    ∧ totalBulkVorticity S.touching = totalEdgeWinding S.touching
    ∧ S.tknn.chernNumber = S.edgeWinding
    ∧ S.tknn.hallConductanceUnits = (S.edgeWinding : ℝ)

/-- The critical bulk-edge package is checked from the local matching and the
two paper equations supplied as explicit obligations. -/
lemma hatsugaiBulkEdgeCorrespondence_checked :
    S.HasHatsugaiBulkEdgeCorrespondence :=
  ⟨S.tknn.hallConductanceUnits_eq_normalized_integral,
    S.chern_eq_totalBulkVorticity,
    S.edgeWinding_eq_totalEdgeWinding,
    totalBulkVorticity_eq_totalEdgeWinding S.touching,
    S.chernNumber_eq_edgeWinding,
    S.hallConductanceUnits_eq_edgeWinding⟩

end HatsugaiBulkEdgeSystem


/-- Hatsugai Eq. (10): an edge-state energy is a zero of the transfer-matrix
entry `M₂₁(E)`. -/
def IsHatsugaiEdgeStateEnergy (M21 : ℝ → ℝ) (E : ℝ) : Prop :=
  M21 E = 0

/-- A named carrier for an edge-state zero of the transfer matrix. -/
structure HatsugaiEdgeStateZero where
  M21 : ℝ → ℝ
  energy : ℝ
  edge_zero : IsHatsugaiEdgeStateEnergy M21 energy

namespace HatsugaiEdgeStateZero

/-- The carrier exposes exactly Hatsugai's transfer-matrix edge equation. -/
lemma transferMatrix_M21_eq_zero (Z : HatsugaiEdgeStateZero) :
    Z.M21 Z.energy = 0 :=
  Z.edge_zero

end HatsugaiEdgeStateZero

/-- The specific situation used in the paper's proof: an edge-state zero of
`M₂₁` occurs at a band edge, hence at a branch point of the same
hyperelliptic surface. -/
structure HatsugaiBulkEdgeBandEdgeDegeneracy (q : ℕ) where
  branchData : HatsugaiBranchFactorization q
  edgeZero : HatsugaiEdgeStateZero
  bandEdgeIndex : Fin (2 * q)
  energy_eq_bandEdge : edgeZero.energy = branchData.bandEdge bandEdgeIndex

namespace HatsugaiBulkEdgeBandEdgeDegeneracy

variable {q : ℕ}

/-- The degenerate edge energy is a branch point of Hatsugai's Riemann
surface. -/
lemma edgeEnergy_is_branchPoint (D : HatsugaiBulkEdgeBandEdgeDegeneracy q) :
    IsHatsugaiBranchPoint D.branchData D.edgeZero.energy := by
  rw [D.energy_eq_bandEdge]
  exact D.branchData.bandEdge_is_branchPoint D.bandEdgeIndex

/-- The same degenerate energy still satisfies the transfer-matrix edge-state
zero equation. -/
lemma edgeEnergy_transferMatrix_M21_eq_zero
    (D : HatsugaiBulkEdgeBandEdgeDegeneracy q) :
    D.edgeZero.M21 D.edgeZero.energy = 0 :=
  D.edgeZero.transferMatrix_M21_eq_zero

end HatsugaiBulkEdgeBandEdgeDegeneracy

end Physlib.QuantumMechanics.ComplexAction.IntegerQuantumHallBulkEdge

end
