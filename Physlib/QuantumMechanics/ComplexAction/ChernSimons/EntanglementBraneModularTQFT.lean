/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ConcreteSynthesis
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
public import Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction
public import Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge
public import Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality
meta import Zil

/-!
# Entanglement branes, modular flow, and the extended TQFT entropy split

This module formalizes the reusable mathematical core of Donnelly--Wong,
*Entanglement branes, modular flow, and extended topological quantum field theory*
(JHEP 10 (2019) 016, arXiv:1811.10785), and connects it to the repository's
Verlinde and relative-entropy infrastructure.

* **E-brane retract.** `EntanglementBrane` packages the zipper `C → O`, cozipper
  `O → C`, and the paper's window-closing axiom.  It proves that cutting is
  injective, closing is surjective, and every closed evolution has an induced open
  evolution whose restriction to cut states is exactly the original evolution.
  Composition is preserved, so a closed modular flow induces an open modular flow.
* **Two-dimensional Yang--Mills sectors.** `YMSectorData` packages a normalized
  representation distribution and positive representation dimensions.  The
  extended entropy is the paper's
  `H(p) + n ⟨log dim R⟩`; the one- and two-interval cases give `n = 2` and
  `n = 4`.  Logarithmic negativity is the log edge moment
  `log ⟨(dim R)^n⟩`, and Jensen proves that it dominates the corresponding
  mean log edge dimension.
* **The actual Yang--Mills Gibbs weights.** `ymBoltzmannSectorData` constructs the
  normalized sphere distribution
  `p(R) = (dim R)^2 exp(-β C₂(R)) / Z`; its partition function is proved positive.
  The unnormalized modular Hamiltonian identity is
  `-log(exp(-β C₂(R))) = β C₂(R)`.
* **Verlinde specialization.** For the repository's `U(1)_k` charge sectors all
  irreducible representations are one-dimensional.  The existing proved-unitary
  Verlinde `S`-matrix therefore coexists with vanishing dimension-edge entropy and
  negativity; only the classical Shannon sector can remain.
* **Particle-physics boundary.** The checked Jain `e/5` and `e/7` excitations
  share the electron/proton unit-charge normalization, but are proved not to lie
  on the generated Standard-Model `e/3` Weyl-fermion charge lattice.  This makes
  their status as emergent Hall quasiparticles explicit in the theorem graph.

## Scope

The E-brane object is deliberately a narrow linear retract, not a second general
category-theoretic TQFT hierarchy.  The Yang--Mills formulas are finite semisimple
sector formulas from the paper.  They do **not** assert a tensor-product factorization
of continuum AQFT local algebras; the repository's Araki relative-entropy layer is the
appropriate nonfactorizing continuum interface.  The Gross--Taylor non-chiral/BV--BRST
extension is explicitly left open by the paper and is not claimed here.
Nor are Hall quasiparticles identified with elementary Standard-Model fields:
the charge-lattice separation theorem proves precisely the opposite.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT

open Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

/-! ## A. The entanglement-brane retract and induced modular flow -/

/-- A linear form of the entanglement-brane window-closing axiom.  `C` is the
closed state carrier, `O` the open/interval carrier, and `cozipper ∘ zipper = id`
is the paper's statement that the artificial entangling boundary can be closed. -/
structure EntanglementBrane (C O : Type*) [AddCommMonoid C] [Module ℂ C]
    [AddCommMonoid O] [Module ℂ O] where
  zipper : C →ₗ[ℂ] O
  cozipper : O →ₗ[ℂ] C
  close_window : cozipper.comp zipper = LinearMap.id

namespace EntanglementBrane

variable {C O : Type*} [AddCommMonoid C] [Module ℂ C]
    [AddCommMonoid O] [Module ℂ O] (E : EntanglementBrane C O)

/-- Closing immediately after cutting a closed state recovers that state. -/
@[simp] theorem cozipper_zipper (c : C) : E.cozipper (E.zipper c) = c := by
  have h := LinearMap.congr_fun E.close_window c
  simpa using h

/-- The E-brane cutting map is injective: no closed state is lost in the open
presentation. -/
theorem zipper_injective : Function.Injective E.zipper :=
  fun _ _ h => by simpa only [E.cozipper_zipper] using congrArg E.cozipper h

/-- The E-brane closing map is surjective onto the closed sector. -/
theorem cozipper_surjective : Function.Surjective E.cozipper :=
  fun c => ⟨E.zipper c, E.cozipper_zipper c⟩

/-- Induce an open-sector evolution by closing, evolving in the closed sector,
and cutting again. -/
def openEvolution (T : C →ₗ[ℂ] C) : O →ₗ[ℂ] O :=
  E.zipper.comp (T.comp E.cozipper)

/-- The induced open evolution intertwines the closed evolution on every cut
state. -/
@[simp] theorem openEvolution_on_cut (T : C →ₗ[ℂ] C) (c : C) :
    E.openEvolution T (E.zipper c) = E.zipper (T c) := by
  simp [openEvolution]

/-- Closing the induced open evolution recovers the original closed evolution.
This is the algebraic form of evaluating the modular cobordism in the closed
sector after closing its E-brane windows. -/
theorem close_openEvolution (T : C →ₗ[ℂ] C) :
    E.cozipper.comp ((E.openEvolution T).comp E.zipper) = T := by
  ext c
  simp

/-- E-brane induction preserves composition of closed evolutions. -/
theorem openEvolution_comp (T U : C →ₗ[ℂ] C) :
    (E.openEvolution T).comp (E.openEvolution U) = E.openEvolution (T.comp U) := by
  ext o
  simp [openEvolution]

/-- A one-parameter closed modular flow satisfying its additive group/semigroup
law induces an open modular flow satisfying the same composition law. -/
@[zil_level bridge_theorem]
theorem openModularFlow_add (T : ℝ → C →ₗ[ℂ] C)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t)) (s t : ℝ) :
    E.openEvolution (T (s + t)) =
      (E.openEvolution (T s)).comp (E.openEvolution (T t)) := by
  rw [hadd, E.openEvolution_comp]

end EntanglementBrane

/-! ## B. The Yang--Mills Shannon/edge split and logarithmic negativity -/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

variable {Rep : Type*} [Fintype Rep]

/-- A finite semisimple representation-sector distribution with the positive
integer dimensions that count interval edge modes in two-dimensional Yang--Mills. -/
structure YMSectorData (Rep : Type*) [Fintype Rep] where
  probability : Rep → ℝ
  representationDim : Rep → ℕ
  probability_nonneg : ∀ R, 0 ≤ probability R
  probability_sum_one : ∑ R, probability R = 1
  representationDim_pos : ∀ R, 0 < representationDim R

namespace YMSectorData

variable (D : YMSectorData Rep)

/-- The classical Shannon part of the representation-sector entropy. -/
noncomputable def shannonSectorEntropy : ℝ := entropy D.probability

/-- The expected logarithmic edge-mode degeneracy `⟨log dim R⟩`. -/
noncomputable def meanLogDim : ℝ :=
  ∑ R, D.probability R * Real.log (D.representationDim R)

/-- The Donnelly--Wong entropy for a region with `entanglingPoints` endpoints:
`H(p) + entanglingPoints * ⟨log dim R⟩`. -/
noncomputable def extendedEntropy (entanglingPoints : ℕ) : ℝ :=
  D.shannonSectorEntropy + entanglingPoints * D.meanLogDim

/-- The edge degeneracy moment `⟨(dim R)^n⟩` seen by the partial-transpose
replica construction. -/
noncomputable def edgeMoment (sharedEndpoints : ℕ) : ℝ :=
  ∑ R, D.probability R * (D.representationDim R : ℝ) ^ sharedEndpoints

/-- The paper's logarithmic-negativity sector formula
`log ⟨(dim R)^n⟩`. -/
noncomputable def logNegativity (sharedEndpoints : ℕ) : ℝ :=
  Real.log (D.edgeMoment sharedEndpoints)

/-- Equation (4.19): one interval has two entangling points. -/
@[zil_level bridge_theorem]
theorem extendedEntropy_singleInterval :
    D.extendedEntropy 2 = D.shannonSectorEntropy + 2 * D.meanLogDim := rfl

/-- Equation (4.24): two intervals have four entangling points. -/
@[zil_level bridge_theorem]
theorem extendedEntropy_twoIntervals :
    D.extendedEntropy 4 = D.shannonSectorEntropy + 4 * D.meanLogDim := rfl

/-- The logarithmic negativity dominates the corresponding mean log edge
dimension by concavity of `log`:
`⟨log ((dim R)^n)⟩ ≤ log ⟨(dim R)^n⟩`.
This proves the non-strict form of the distinction surrounding equations
(4.38) and (4.46), rather than merely recording the two formulas. -/
@[zil_level physical_theorem]
theorem meanLogEdgeDim_le_logNegativity (n : ℕ) :
    (∑ R, D.probability R * Real.log ((D.representationDim R : ℝ) ^ n))
      ≤ D.logNegativity n := by
  let x : Rep → ℝ := fun R => (D.representationDim R : ℝ) ^ n
  let m : ℝ := ∑ R, D.probability R * x R
  have hxpos : ∀ R, 0 < x R := fun R =>
    pow_pos (by exact_mod_cast D.representationDim_pos R) _
  have hxone : ∀ R, 1 ≤ x R := fun R => by
    apply one_le_pow₀
    exact_mod_cast D.representationDim_pos R
  have hmge : 1 ≤ m := by
    calc
      1 = ∑ R, D.probability R := D.probability_sum_one.symm
      _ ≤ ∑ R, D.probability R * x R := by
        apply Finset.sum_le_sum
        intro R _
        simpa using mul_le_mul_of_nonneg_left (hxone R) (D.probability_nonneg R)
      _ = m := rfl
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hmge
  have hterm : ∀ R,
      D.probability R * (Real.log (x R) - Real.log m) ≤
        D.probability R * (x R / m - 1) := by
    intro R
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hxpos R) hmpos)
    rw [Real.log_div (hxpos R).ne' hmpos.ne'] at hlog
    exact mul_le_mul_of_nonneg_left hlog (D.probability_nonneg R)
  have hsum :
      (∑ R, D.probability R * (Real.log (x R) - Real.log m)) ≤
        ∑ R, D.probability R * (x R / m - 1) :=
    Finset.sum_le_sum (fun R _ => hterm R)
  have hleft :
      (∑ R, D.probability R * (Real.log (x R) - Real.log m)) =
        (∑ R, D.probability R * Real.log (x R)) - Real.log m := by
    calc
      (∑ R, D.probability R * (Real.log (x R) - Real.log m)) =
          ∑ R, (D.probability R * Real.log (x R) -
            D.probability R * Real.log m) := by
              apply Finset.sum_congr rfl
              intro R _
              ring
      _ = (∑ R, D.probability R * Real.log (x R)) -
          ∑ R, D.probability R * Real.log m := by rw [Finset.sum_sub_distrib]
      _ = (∑ R, D.probability R * Real.log (x R)) - Real.log m := by
          rw [← Finset.sum_mul, D.probability_sum_one, one_mul]
  have hright : ∑ R, D.probability R * (x R / m - 1) = 0 := by
    calc
      (∑ R, D.probability R * (x R / m - 1)) =
          ∑ R, (D.probability R * x R / m - D.probability R) := by
            apply Finset.sum_congr rfl
            intro R _
            ring
      _ = (∑ R, D.probability R * x R) / m - ∑ R, D.probability R := by
          rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ = m / m - 1 := by rw [D.probability_sum_one]
      _ = 0 := by rw [div_self hmpos.ne', sub_self]
  rw [hleft, hright] at hsum
  have hfinal : (∑ R, D.probability R * Real.log (x R)) ≤ Real.log m := by
    linarith
  simpa [logNegativity, edgeMoment, x, m] using hfinal

/-- With no shared edge, the edge moment is normalized to one. -/
theorem edgeMoment_zero : D.edgeMoment 0 = 1 := by
  simp [edgeMoment, D.probability_sum_one]

/-- With no shared edge, logarithmic negativity vanishes. -/
theorem logNegativity_zero : D.logNegativity 0 = 0 := by
  rw [logNegativity, D.edgeMoment_zero, Real.log_one]

/-- One-dimensional representation sectors have no logarithmic edge term. -/
theorem meanLogDim_eq_zero_of_dim_one
    (hdim : ∀ R, D.representationDim R = 1) : D.meanLogDim = 0 := by
  simp [meanLogDim, hdim]

/-- When every representation is one-dimensional, the extended entropy reduces
exactly to the Shannon entropy. -/
theorem extendedEntropy_eq_shannon_of_dim_one
    (hdim : ∀ R, D.representationDim R = 1) (n : ℕ) :
    D.extendedEntropy n = D.shannonSectorEntropy := by
  rw [extendedEntropy, D.meanLogDim_eq_zero_of_dim_one hdim, mul_zero, add_zero]

/-- When every representation is one-dimensional, all edge-negativity moments
are one and logarithmic negativity vanishes. -/
theorem logNegativity_eq_zero_of_dim_one
    (hdim : ∀ R, D.representationDim R = 1) (n : ℕ) :
    D.logNegativity n = 0 := by
  rw [logNegativity]
  have hmoment : D.edgeMoment n = 1 := by
    simp [edgeMoment, hdim, D.probability_sum_one]
  rw [hmoment, Real.log_one]

end YMSectorData

/-! ## C. The normalized sphere distribution and modular Hamiltonian -/

/-- The unnormalized Yang--Mills Boltzmann eigenvalue `exp(-β C₂(R))`. -/
noncomputable def ymBoltzmannWeight (β casimir : ℝ) : ℝ :=
  Real.exp (-(β * casimir))

/-- Equation (4.17)'s modular Hamiltonian on an unnormalized sector:
`-log(exp(-β C₂(R))) = β C₂(R)`. -/
@[zil_level physical_theorem]
theorem neg_log_ymBoltzmannWeight (β casimir : ℝ) :
    -Real.log (ymBoltzmannWeight β casimir) = β * casimir := by
  simp [ymBoltzmannWeight]

/-- The sphere partition function
`Z = Σ_R (dim R)^2 exp(-β C₂(R))`. -/
noncomputable def ymSpherePartition (dim : Rep → ℕ) (casimir : Rep → ℝ) (β : ℝ) : ℝ :=
  ∑ R, (dim R : ℝ) ^ 2 * ymBoltzmannWeight β (casimir R)

/-- The normalized representation probability from equation (4.19). -/
noncomputable def ymSphereProbability (dim : Rep → ℕ) (casimir : Rep → ℝ) (β : ℝ) :
    Rep → ℝ :=
  fun R => (dim R : ℝ) ^ 2 * ymBoltzmannWeight β (casimir R) /
    ymSpherePartition dim casimir β

/-- Positive representation dimensions make the finite sphere partition
function strictly positive. -/
theorem ymSpherePartition_pos [Nonempty Rep] (dim : Rep → ℕ) (casimir : Rep → ℝ)
    (β : ℝ) (hdim : ∀ R, 0 < dim R) : 0 < ymSpherePartition dim casimir β := by
  classical
  let R₀ : Rep := Classical.choice (inferInstance : Nonempty Rep)
  apply Finset.sum_pos'
  · intro R _
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  · exact ⟨R₀, Finset.mem_univ _, mul_pos (sq_pos_of_pos (by exact_mod_cast hdim R₀))
      (Real.exp_pos _)⟩

/-- The normalized Yang--Mills sphere weights sum to one. -/
theorem ymSphereProbability_sum (dim : Rep → ℕ) (casimir : Rep → ℝ) (β : ℝ)
    (hZ : ymSpherePartition dim casimir β ≠ 0) :
    ∑ R, ymSphereProbability dim casimir β R = 1 := by
  rw [show (∑ R, ymSphereProbability dim casimir β R) =
      ymSpherePartition dim casimir β / ymSpherePartition dim casimir β by
    simp only [ymSphereProbability, ← Finset.sum_div, ymSpherePartition]]
  exact div_self hZ

/-- The normalized Yang--Mills sphere weights are nonnegative. -/
theorem ymSphereProbability_nonneg (dim : Rep → ℕ) (casimir : Rep → ℝ) (β : ℝ)
    (hZ : 0 < ymSpherePartition dim casimir β) (R : Rep) :
    0 ≤ ymSphereProbability dim casimir β R := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hZ.le

/-- Construct the paper's normalized finite semisimple Yang--Mills sector data
from positive representation dimensions and Casimir values. -/
noncomputable def ymBoltzmannSectorData [Nonempty Rep]
    (dim : Rep → ℕ) (casimir : Rep → ℝ) (β : ℝ) (hdim : ∀ R, 0 < dim R) :
    YMSectorData Rep where
  probability := ymSphereProbability dim casimir β
  representationDim := dim
  probability_nonneg := ymSphereProbability_nonneg dim casimir β
    (ymSpherePartition_pos dim casimir β hdim)
  probability_sum_one := ymSphereProbability_sum dim casimir β
    (ymSpherePartition_pos dim casimir β hdim).ne'
  representationDim_pos := hdim

/-! ## D. The `U(1)_k` Verlinde specialization -/

/-- A normalized distribution on the `U(1)_k` charge sectors, whose irreducible
representation dimensions are all one. -/
noncomputable def u1SectorData {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : YMSectorData (Fin k) where
  probability := p
  representationDim := fun _ => 1
  probability_nonneg := hp
  probability_sum_one := hsum
  representationDim_pos := fun _ => by simp

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge

/-- The `U(1)_k` specialization: the existing Verlinde matrix is unitary, while
one-dimensional Abelian charge sectors have no `log dim R` edge entropy and no
logarithmic negativity.  This does not say the Shannon sector entropy vanishes. -/
@[zil_level bridge_theorem]
theorem u1Verlinde_edge_contribution_vanishes (k : ℕ) (hk : 0 < k)
    (p : Fin k → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (n : ℕ) :
    (∀ a b : Fin k,
      (∑ c : Fin k, cswSMatrix k a c * (starRingEnd ℂ) (cswSMatrix k b c)) =
        if a = b then 1 else 0) ∧
    (u1SectorData p hp hsum).extendedEntropy n =
      (u1SectorData p hp hsum).shannonSectorEntropy ∧
    (u1SectorData p hp hsum).logNegativity n = 0 := by
  refine ⟨cswSMatrix_unitary k hk, ?_, ?_⟩
  · exact YMSectorData.extendedEntropy_eq_shannon_of_dim_one _ (fun _ => rfl) n
  · exact YMSectorData.logNegativity_eq_zero_of_dim_one _ (fun _ => rfl) n

/-- Any finite Abelian sector realization with one-dimensional irreducibles has
no representation-dimension edge entropy and no logarithmic negativity.  This
is the reusable part of the `U(1)_k` result and makes no claim that two Abelian
theories with the same number of sectors have the same modular data. -/
lemma finiteAbelian_edge_contribution_vanishes {k : ℕ}
    (D : YMSectorData (Fin k)) (hdim : ∀ a, D.representationDim a = 1)
    (n : ℕ) :
    D.extendedEntropy n = D.shannonSectorEntropy ∧ D.logNegativity n = 0 := by
  exact ⟨D.extendedEntropy_eq_shannon_of_dim_one hdim n,
    D.logNegativity_eq_zero_of_dim_one hdim n⟩

/-! ## E. Hierarchical FQHE endpoint -/

open Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction
open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

/-- The one-level FQHE hierarchy, the Laughlin `U(1)_k` Chern--Simons sector,
and the Donnelly--Wong E-brane entropy split are the same checked endpoint:
the filling is `1/k`, the torus state-space dimension is `k`, the Verlinde
matrix is unitary, and one-dimensional Abelian irreducible sectors contribute
neither `log dim R` edge entropy nor logarithmic negativity.  The classical
Shannon sector is retained explicitly. -/
@[zil_level bridge_theorem]
lemma hierarchyLaughlin_entanglementBrane_bridge (k n : ℕ) (hk : 0 < k)
    (p : Fin k → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    hierarchyFilling [(k : ℝ)] = laughlinFilling (k : ℝ) ∧
    Module.finrank ℂ (TorusHilbert k) = k ∧
    (∀ a b : Fin k,
      (∑ c : Fin k, cswSMatrix k a c * (starRingEnd ℂ) (cswSMatrix k b c)) =
        if a = b then 1 else 0) ∧
    (u1SectorData p hp hsum).extendedEntropy n =
      (u1SectorData p hp hsum).shannonSectorEntropy ∧
    (u1SectorData p hp hsum).logNegativity n = 0 := by
  refine ⟨hierarchyFilling_single_eq_laughlinFilling (k : ℝ),
    torusHilbert_finrank k, ?_⟩
  exact u1Verlinde_edge_contribution_vanishes k hk p hp hsum n

/-! ## F. Jain hierarchy matrices and finite Abelian edge sectors -/

/-- The determinant-five rank-two Jain realization supplies five Abelian
sectors.  For any one-dimensional realization on those five sectors, the
continued-fraction/K-matrix filling is `2/5`, the Donnelly edge-dimension term
vanishes, and the classical Shannon sector remains explicit. -/
@[zil_level bridge_theorem]
lemma jainTwoFifths_entanglementBrane_bridge
    (D : YMSectorData (Fin 5)) (hdim : ∀ a, D.representationDim a = 1)
    (n : ℕ) :
    (hierarchyKMatrix2 3 2).det = 5 ∧
      hierarchyFilling [3, 2] = hierarchyFillingFromK2 3 2 ∧
      hierarchyFillingFromK2 3 2 = 2 / 5 ∧
      D.extendedEntropy n = D.shannonSectorEntropy ∧
      D.logNegativity n = 0 := by
  refine ⟨jain_two_fifths_kmatrix_derivation.1,
    jain_two_fifths_kmatrix_derivation.2.2.2.1,
    jain_two_fifths_kmatrix_derivation.2.2.2.2, ?_⟩
  exact finiteAbelian_edge_contribution_vanishes D hdim n

/-- The determinant-seven rank-three Jain realization supplies seven Abelian
sectors.  For any one-dimensional realization on those seven sectors, the
continued-fraction/K-matrix filling is `3/7`, the Donnelly edge-dimension term
vanishes, and the classical Shannon sector remains explicit. -/
@[zil_level bridge_theorem]
lemma jainThreeSevenths_entanglementBrane_bridge
    (D : YMSectorData (Fin 7)) (hdim : ∀ a, D.representationDim a = 1)
    (n : ℕ) :
    (hierarchyKMatrix3 3 2 2).det = 7 ∧
      hierarchyFilling [3, 2, 2] = hierarchyFillingFromK3 3 2 2 ∧
      hierarchyFillingFromK3 3 2 2 = 3 / 7 ∧
      D.extendedEntropy n = D.shannonSectorEntropy ∧
      D.logNegativity n = 0 := by
  refine ⟨jain_three_sevenths_kmatrix_derivation.1,
    jain_three_sevenths_kmatrix_derivation.2.2.2.1,
    jain_three_sevenths_kmatrix_derivation.2.2.2.2, ?_⟩
  exact finiteAbelian_edge_contribution_vanishes D hdim n

/-! ## G. The complete Jain family on shared CSW/Yang--Mills sectors -/

/-- Numerator `p=n+1` of the `p=1` Jain hierarchy filling. -/
def jainHierarchyNumerator (n : ℕ) : ℕ := n + 1

/-- Denominator and finite Abelian sector count `q=2p+1=2n+3` for the `p=1`
Jain hierarchy. -/
def jainHierarchySectorCount (n : ℕ) : ℕ :=
  2 * jainHierarchyNumerator n + 1

/-- Every Jain hierarchy sector count is positive. -/
lemma jainHierarchySectorCount_pos (n : ℕ) :
    0 < jainHierarchySectorCount n := by
  simp [jainHierarchySectorCount, jainHierarchyNumerator]

/-- The actual normalized two-dimensional Yang--Mills Boltzmann sector data on
the Jain denominator carrier `Fin q`.  Representation dimensions are one, as
appropriate for a finite Abelian comparison sector, while the Casimir and
inverse area/temperature parameter remain explicit inputs. -/
noncomputable def jainHierarchyYMSectorData (n : ℕ)
    (casimir : Fin (jainHierarchySectorCount n) → ℝ) (β : ℝ) :
    YMSectorData (Fin (jainHierarchySectorCount n)) := by
  letI : Nonempty (Fin (jainHierarchySectorCount n)) :=
    Fin.pos_iff_nonempty.mp (jainHierarchySectorCount_pos n)
  exact ymBoltzmannSectorData (fun _ => 1) casimir β (fun _ => by simp)

/-- The complete Jain family has filling `p/q` with `p=n+1` and `q=2n+3`. -/
lemma hierarchyFilling_eq_jainNumerator_div_sectorCount (n : ℕ) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
      (jainHierarchyNumerator n : ℝ) / (jainHierarchySectorCount n : ℝ) := by
  rw [hierarchyFilling_three_cons_replicate_two]
  norm_num [jainHierarchyNumerator, jainHierarchySectorCount]

/-- The Cayley velocity of the full Jain family is the Pythagorean ratio
`(q²-p²)/(q²+p²)` on the same numerator/sector-count data. -/
lemma jainHierarchy_cayleyVelocity_sectorCount (n : ℕ) :
    fillingCayleyVelocity
        (hierarchyFilling ((3 : ℝ) :: List.replicate n 2)) =
      ((jainHierarchySectorCount n : ℝ) ^ 2 -
          (jainHierarchyNumerator n : ℝ) ^ 2) /
        ((jainHierarchySectorCount n : ℝ) ^ 2 +
          (jainHierarchyNumerator n : ℝ) ^ 2) := by
  simpa [jainHierarchyNumerator, jainHierarchySectorCount] using
    jainHierarchy_cayleyVelocity n

/-- **Local Chern--Simons/Yang--Mills curvature bridge on the Jain carrier.**
Choosing the Jain denominator `q=2n+3` as the size of the existing finite local
matrix carrier gives, without redefining either gauge theory,

* the hierarchy filling `p/q`;
* equality of the local Chern--Simons curvature with the repository's
  zero-coordinate-derivative Yang--Mills curvature;
* the cubic Chern--Simons density as `Tr(A₀ F₁₂)` using that same
  Yang--Mills curvature.

This is the finite/trivial-bundle curvature sector of `ConcreteSynthesis`; it
does not assert a continuum Yang--Mills solution or derive the physical gauge
rank from the filling denominator. -/
@[zil_level bridge_theorem]
lemma jainHierarchy_localChernSimons_yangMills_bridge (n : ℕ)
    (A : LocalCSConnection (jainHierarchySectorCount n)) (i j : Fin 3) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
        (jainHierarchyNumerator n : ℝ) / (jainHierarchySectorCount n : ℝ) ∧
      localCSCurvature A i j =
        yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A) () i j ∧
      localChernSimonsCubic A =
        Matrix.trace
          (A 0 * yangMillsCurvature localCSZeroPartial
            (localCSAsGaugePotential A) () 1 2) := by
  refine ⟨hierarchyFilling_eq_jainNumerator_div_sectorCount n,
    localCSCurvature_eq_yangMillsCurvature_zeroPartial A i j, ?_⟩
  rw [← localCSCurvature_eq_yangMillsCurvature_zeroPartial A 1 2]
  exact localChernSimonsCubic_eq_trace_A0_curvature12 A

/-- The continued-fraction Jain hierarchy is exactly the repository's existing
composite-fermion `jainFilling` family, now expressed through the shared
numerator/sector-count carrier. -/
lemma jainHierarchy_eq_compositeFermionFilling (n : ℕ) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
      jainFilling (jainHierarchyNumerator n : ℝ) 1 := by
  simpa [jainHierarchyNumerator] using hierarchyFilling_jain_sequence n

/-- On the Jain denominator comparison carrier, the existing Wilson/Verlinde
operator is diagonalized by every conjugate modular `S`-matrix column.  This is
an application of the repository's Wilson-loop theorem at `q=2n+3`; it does not
identify all Jain `K`-matrix Wilson data with those of `U(1)_q`. -/
lemma jainHierarchy_cswWilsonVerlinde_diagonalization (n : ℕ)
    (a r : Fin (jainHierarchySectorCount n)) :
    cswWilsonVerlindeOperator (jainHierarchySectorCount n) a
        (fun b => (starRingEnd ℂ)
          (cswSMatrix (jainHierarchySectorCount n) b r)) =
      fun c =>
        cswVerlindeEigenvalue (jainHierarchySectorCount n)
            (jainHierarchySectorCount_pos n) a r *
          (starRingEnd ℂ) (cswSMatrix (jainHierarchySectorCount n) c r) := by
  exact cswWilsonVerlinde_diagonalization
    (jainHierarchySectorCount n) (jainHierarchySectorCount_pos n) a r

/-- The topological-entropy functional of the level-`q` CSW comparison carrier
is one half of `log q`, with `q` the Jain hierarchy sector count.  The theorem
specializes the existing CSW torus-dimension result and does not replace the
full `K`-matrix quantum-dimension calculation. -/
lemma jainHierarchy_cswComparison_topologicalEntropy (n : ℕ) :
    topologicalEntanglementEntropy
        (Module.finrank ℂ (TorusHilbert (jainHierarchySectorCount n)) : ℝ) =
      Real.log (jainHierarchySectorCount n : ℝ) / 2 := by
  exact tee_from_csw_torus_dimension (jainHierarchySectorCount n)

/-- The Jain-sized finite local gauge carrier also reaches the repository's
Deser--Jackiw--Templeton Yang--Mills--Chern--Simons equation: at zero
topological mass it is exactly the ordinary Yang--Mills equation.  The filling
identity is retained in the same theorem so this is a checked cross-sector
bridge rather than an unconnected specialization. -/
@[zil_level bridge_theorem]
lemma jainHierarchy_topologicallyMassiveYangMills_zeroMass (n : ℕ)
    (A : LocalCSConnection (jainHierarchySectorCount n))
    (dualF : GaugeDualCurvature Unit (Fin 3)
      (Matrix (Fin (jainHierarchySectorCount n))
        (Fin (jainHierarchySectorCount n)) ℂ))
    (J : GaugeCurrent Unit (Fin 3)
      (Matrix (Fin (jainHierarchySectorCount n))
        (Fin (jainHierarchySectorCount n)) ℂ)) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
        jainFilling (jainHierarchyNumerator n : ℝ) 1 ∧
      (TopologicallyMassiveYangMillsEquation localCSZeroPartial
          (localCSAsGaugePotential A)
          (yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A))
          dualF J 0 ↔
        YangMillsEquation localCSZeroPartial (localCSAsGaugePotential A)
          (yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A)) J) := by
  exact ⟨jainHierarchy_eq_compositeFermionFilling n,
    topologicallyMassiveYangMills_zeroMass_iff_yangMills
      localCSZeroPartial (localCSAsGaugePotential A)
      (yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A)) dualF J⟩

/-- **Jain--CSW--Yang--Mills family bridge.**  The denominator `q=2n+3`
simultaneously indexes:

* the hierarchy filling `p/q` and its Pythagorean Cayley coordinate;
* the repository's `q`-dimensional CSW torus comparison carrier and unitary
  Verlinde Fourier matrix;
* a concrete normalized two-dimensional Yang--Mills Boltzmann distribution on
  `Fin q`, whose one-dimensional Abelian sectors have no representation-edge
  entropy or logarithmic negativity.

The theorem deliberately asserts a shared finite carrier and checked formulas,
not equivalence of the Jain `K`-matrix modular category with `U(1)_q`. -/
@[zil_level bridge_theorem]
lemma jainHierarchy_cswYangMills_cayley_bridge (n : ℕ)
    (casimir : Fin (jainHierarchySectorCount n) → ℝ) (β : ℝ)
    (entanglingPoints : ℕ) :
    hierarchyFilling ((3 : ℝ) :: List.replicate n 2) =
        (jainHierarchyNumerator n : ℝ) / (jainHierarchySectorCount n : ℝ) ∧
      Module.finrank ℂ (TorusHilbert (jainHierarchySectorCount n)) =
        jainHierarchySectorCount n ∧
      (∀ a b : Fin (jainHierarchySectorCount n),
        (∑ c : Fin (jainHierarchySectorCount n),
          cswSMatrix (jainHierarchySectorCount n) a c *
            (starRingEnd ℂ) (cswSMatrix (jainHierarchySectorCount n) b c)) =
          if a = b then 1 else 0) ∧
      0 < ymSpherePartition
        (fun _ : Fin (jainHierarchySectorCount n) => 1) casimir β ∧
      (∑ R, (jainHierarchyYMSectorData n casimir β).probability R) = 1 ∧
      (jainHierarchyYMSectorData n casimir β).extendedEntropy entanglingPoints =
        (jainHierarchyYMSectorData n casimir β).shannonSectorEntropy ∧
      (jainHierarchyYMSectorData n casimir β).logNegativity entanglingPoints = 0 ∧
      fillingCayleyVelocity
          (hierarchyFilling ((3 : ℝ) :: List.replicate n 2)) =
        ((jainHierarchySectorCount n : ℝ) ^ 2 -
            (jainHierarchyNumerator n : ℝ) ^ 2) /
          ((jainHierarchySectorCount n : ℝ) ^ 2 +
            (jainHierarchyNumerator n : ℝ) ^ 2) := by
  letI : Nonempty (Fin (jainHierarchySectorCount n)) :=
    Fin.pos_iff_nonempty.mp (jainHierarchySectorCount_pos n)
  have hedge := finiteAbelian_edge_contribution_vanishes
    (jainHierarchyYMSectorData n casimir β) (fun _ => rfl) entanglingPoints
  exact ⟨hierarchyFilling_eq_jainNumerator_div_sectorCount n,
    torusHilbert_finrank (jainHierarchySectorCount n),
    cswSMatrix_unitary (jainHierarchySectorCount n)
      (jainHierarchySectorCount_pos n),
    ymSpherePartition_pos
      (fun _ : Fin (jainHierarchySectorCount n) => 1) casimir β
      (fun _ => by simp),
    (jainHierarchyYMSectorData n casimir β).probability_sum_one,
    hedge.1, hedge.2,
    jainHierarchy_cayleyVelocity_sectorCount n⟩

/-- **Observed Jain plateau data contact.**  The two experimentally established
Jain anchors have the standard quantized Hall responses, while their checked
`K`-matrix determinants agree with the dimensions of the corresponding finite
CSW comparison carriers.  This theorem joins measured response to the exact
finite topological bookkeeping; it does not claim that measurement selects the
comparison `U(1)_q` modular category or the Yang--Mills Casimir data. -/
@[zil_level bridge_theorem]
lemma observedJain_hallPlateaus_csw_dataContact :
    hallConductanceUnits (hierarchyFilling [3, 2]) = 2 / 5 ∧
      hallResistivityUnits (hierarchyFilling [3, 2]) = 5 / 2 ∧
      hierarchyTerminalQuasiparticleCharge2 3 2 = 1 / 5 ∧
      (hierarchyKMatrix2 3 2).det = 5 ∧
      Module.finrank ℂ (TorusHilbert 5) = 5 ∧
      hallConductanceUnits (hierarchyFilling [3, 2, 2]) = 3 / 7 ∧
      hallResistivityUnits (hierarchyFilling [3, 2, 2]) = 7 / 3 ∧
      hierarchyTerminalQuasiparticleCharge3 3 2 2 = 1 / 7 ∧
      (hierarchyKMatrix3 3 2 2).det = 7 ∧
      Module.finrank ℂ (TorusHilbert 7) = 7 := by
  exact ⟨jain_two_fifths_hallConductance, jain_two_fifths_hallResistivity,
    jain_two_fifths_terminalQuasiparticleCharge,
    jain_two_fifths_kmatrix_derivation.1, torusHilbert_finrank 5,
    jain_three_sevenths_hallConductance, jain_three_sevenths_hallResistivity,
    jain_three_sevenths_terminalQuasiparticleCharge,
    jain_three_sevenths_kmatrix_derivation.1, torusHilbert_finrank 7⟩

/-! ## Particle-physics charge boundary -/

/-- `e/5` is not on the Standard-Model `e/3` electric-charge lattice. -/
lemma one_fifth_not_standardModelThirdCharge :
    ¬ IsThirdQuantizedCharge (1 / 5) := by
  rintro ⟨n, hn⟩
  have h3 : (3 : ℚ) = 5 * (n : ℚ) := by field_simp at hn; linarith
  have hz : (3 : ℤ) = 5 * n := by exact_mod_cast h3
  omega

/-- `e/7` is not on the Standard-Model `e/3` electric-charge lattice. -/
lemma one_seventh_not_standardModelThirdCharge :
    ¬ IsThirdQuantizedCharge (1 / 7) := by
  rintro ⟨n, hn⟩
  have h3 : (3 : ℚ) = 7 * (n : ℚ) := by field_simp at hn; linarith
  have hz : (3 : ℤ) = 7 * n := by exact_mod_cast h3
  omega

/-- The Jain `e/5` excitation cannot be the electric charge of any generated
active Standard-Model Weyl fermion or sterile-neutrino extension. -/
@[zil_level bridge_theorem]
lemma jainTwoFifths_quasiparticle_ne_extendedStandardModelCharge
    (f : ExtendedStandardModelWeylFermion) :
    hierarchyTerminalQuasiparticleCharge2 3 2 ≠
      ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ) := by
  rw [jain_two_fifths_terminalQuasiparticleCharge]
  intro h
  have hq : (1 / 5 : ℚ) = (extendedStandardModelQuantumNumbers f).electricCharge := by
    have hc : ((1 / 5 : ℚ) : ℝ) = ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ) := by
      push_cast; linarith [h]
    exact_mod_cast hc
  apply one_fifth_not_standardModelThirdCharge
  rcases extendedStandardModelElectricCharge_thirdQuantized f with ⟨n, hn⟩
  exact ⟨n, hq.trans hn⟩

/-- The Jain `e/7` excitation likewise cannot be any generated elementary
Standard-Model Weyl-fermion charge. -/
@[zil_level bridge_theorem]
lemma jainThreeSevenths_quasiparticle_ne_extendedStandardModelCharge
    (f : ExtendedStandardModelWeylFermion) :
    hierarchyTerminalQuasiparticleCharge3 3 2 2 ≠
      ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ) := by
  rw [jain_three_sevenths_terminalQuasiparticleCharge]
  intro h
  have hq : (1 / 7 : ℚ) = (extendedStandardModelQuantumNumbers f).electricCharge := by
    have hc : ((1 / 7 : ℚ) : ℝ) = ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ) := by
      push_cast; linarith [h]
    exact_mod_cast hc
  apply one_seventh_not_standardModelThirdCharge
  rcases extendedStandardModelElectricCharge_thirdQuantized f with ⟨n, hn⟩
  exact ⟨n, hq.trans hn⟩

/-- **Particle-physics boundary for the Jain excitations.**  Five `e/5` charge
units or seven `e/7` charge units add to the repository's proton unit charge,
but neither individual excitation belongs to the generated Standard-Model
elementary charge spectrum.  This is charge bookkeeping only: it does not
identify a collection of Hall anyons with a proton or construct a fusion
channel. -/
@[zil_level bridge_theorem]
lemma jainQuasiparticle_particlePhysicsChargeBoundary :
    5 * hierarchyTerminalQuasiparticleCharge2 3 2 =
        ((baryonCharge upWinding upWinding downWinding : ℚ) : ℝ) ∧
      7 * hierarchyTerminalQuasiparticleCharge3 3 2 2 =
        ((baryonCharge upWinding upWinding downWinding : ℚ) : ℝ) ∧
      (∀ f : ExtendedStandardModelWeylFermion,
        hierarchyTerminalQuasiparticleCharge2 3 2 ≠
          ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ)) ∧
      ∀ f : ExtendedStandardModelWeylFermion,
        hierarchyTerminalQuasiparticleCharge3 3 2 2 ≠
          ((extendedStandardModelQuantumNumbers f).electricCharge : ℝ) := by
  refine ⟨?_, ?_, jainTwoFifths_quasiparticle_ne_extendedStandardModelCharge,
    jainThreeSevenths_quasiparticle_ne_extendedStandardModelCharge⟩
  · rw [jain_two_fifths_terminalQuasiparticleCharge, proton_charge]
    norm_num
  · rw [jain_three_sevenths_terminalQuasiparticleCharge, proton_charge]
    norm_num

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.extendedStandardModelElectricCharge_thirdQuantized where
  formalizes @ "claim:every-generated-active-or-sterile-standard-model-weyl-state-has-electric-charge-on-the-one-third-electron-charge-lattice",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.fermionElectricCharge_thirdQuantized",
  supported_by @ "paper:georgi-glashow-1974-unity-of-all-elementary-particle-forces-doi-10.1103-physrevlett.32.438",
  caveat @ "scope:this-is-the-charge-spectrum-of-the-repositorys-su-five-standard-model-carrier-not-a-derivation-that-nature-realizes-su-five-unification"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.EntanglementBrane.close_openEvolution where
  formalizes @ "claim:the-entanglement-brane-window-closing-axiom-makes-the-open-presentation-of-a-closed-evolution-recover-the-original-closed-evolution",
  supported_by @ "paper:donnelly-wong-2019-equations-3.6-3.12"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.EntanglementBrane.openModularFlow_add where
  formalizes @ "claim:a-closed-modular-flow-induces-an-open-sector-modular-flow-through-the-entanglement-brane-retract",
  supported_by @ "paper:donnelly-wong-2019-equation-3.12",
  caveat @ "claim:this-is-the-algebraic-open-closed-intertwiner-not-an-operator-algebraic-tomita-takesaki-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.extendedEntropy_singleInterval where
  formalizes @ "claim:two-dimensional-yang-mills-one-interval-entropy-is-shannon-entropy-plus-two-times-the-mean-log-representation-dimension",
  supported_by @ "paper:donnelly-wong-2019-equation-4.19",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.extendedEntropy_twoIntervals where
  formalizes @ "claim:two-dimensional-yang-mills-two-interval-entropy-is-shannon-entropy-plus-four-times-the-mean-log-representation-dimension",
  supported_by @ "paper:donnelly-wong-2019-equation-4.24",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.meanLogEdgeDim_le_logNegativity where
  formalizes @ "claim:the-mean-log-edge-degeneracy-is-bounded-by-the-logarithmic-negativity-edge-moment",
  supported_by @ "paper:donnelly-wong-2019-equations-4.38-4.46",
  supported_by @ "lean:strictConcaveOn_log_Ioi"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.neg_log_ymBoltzmannWeight where
  formalizes @ "claim:the-two-dimensional-yang-mills-reduced-sector-boltzmann-weight-has-modular-hamiltonian-beta-times-the-quadratic-casimir",
  supported_by @ "paper:donnelly-wong-2019-equations-4.17-4.18",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.ymSphereProbability_sum where
  formalizes @ "claim:the-two-dimensional-yang-mills-sphere-sector-weights-form-a-normalized-probability-distribution",
  supported_by @ "paper:donnelly-wong-2019-equation-4.19"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.u1Verlinde_edge_contribution_vanishes where
  formalizes @ "claim:for-u-one-level-k-the-unitary-verlinde-sector-has-no-representation-dimension-edge-entropy-or-negativity-because-all-irreducible-sectors-are-one-dimensional",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary",
  caveat @ "claim:the-shannon-entropy-of-the-charge-sector-distribution-can-remain-nonzero"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.hierarchyLaughlin_entanglementBrane_bridge where
  formalizes @ "claim:the-one-level-fqhe-hierarchy-is-the-laughlin-u-one-level-k-verlinde-sector-with-the-donnelly-wong-abelian-edge-split",
  supported_by @ "paper:fujita-li-ryu-takayanagi-2009-equation-1.2",
  supported_by @ "paper:donnelly-wong-2019-equations-4.19-4.38",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.laughlin_filling_eq_csw_torus_dim",
  caveat @ "claim:this-one-level-abelian-endpoint-does-not-construct-the-general-hierarchical-k-matrix-or-identify-the-nonzero-shannon-sector-with-edge-negativity"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainTwoFifths_entanglementBrane_bridge where
  formalizes @ "claim:the-determinant-five-jain-two-fifths-k-matrix-has-a-finite-abelian-entanglement-brane-realization-with-zero-dimension-edge-term",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_kmatrix_derivation",
  supported_by @ "paper:donnelly-wong-2019-equations-4.19-4.38",
  caveat @ "claim:five-one-dimensional-sectors-do-not-by-themselves-identify-the-full-modular-data-with-u-one-level-five"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainThreeSevenths_entanglementBrane_bridge where
  formalizes @ "claim:the-determinant-seven-jain-three-sevenths-k-matrix-has-a-finite-abelian-entanglement-brane-realization-with-zero-dimension-edge-term",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_kmatrix_derivation",
  supported_by @ "paper:donnelly-wong-2019-equations-4.19-4.38",
  caveat @ "claim:seven-one-dimensional-sectors-do-not-by-themselves-identify-the-full-modular-data-with-u-one-level-seven"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswYangMills_cayley_bridge where
  formalizes @ "claim:the-complete-p-one-jain-family-shares-its-denominator-sector-carrier-with-a-csw-torus-comparison-basis-and-normalized-abelian-yang-mills-boltzmann-data",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.ymBoltzmannSectorData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jainHierarchy_cayleyVelocity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.observedJain_hallPlateaus_csw_dataContact",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-u-one-q-verlinde-matrix-is-a-same-cardinality-comparison-carrier-not-a-proof-of-equivalence-with-the-full-jain-k-matrix-modular-category",
  caveat @ "claim:the-casimir-spectrum-and-beta-parameter-remain-explicit-yang-mills-inputs-rather-than-predictions-from-the-filling-fraction",
  caveat @ "claim:the-cayley-coordinate-is-not-a-measured-spacetime-velocity-of-the-hall-fluid"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_localChernSimons_yangMills_bridge where
  formalizes @ "claim:on-the-shared-jain-denominator-matrix-carrier-the-local-chern-simons-curvature-is-the-zero-partial-yang-mills-curvature-and-the-cubic-density-is-trace-a-zero-f-one-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.localCSCurvature_eq_yangMillsCurvature_zeroPartial",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.localChernSimonsCubic_eq_trace_A0_curvature12",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence",
  caveat @ "claim:this-is-the-finite-trivial-bundle-zero-coordinate-derivative-sector-not-a-continuum-yang-mills-field-equation",
  caveat @ "claim:using-the-filling-denominator-as-matrix-size-is-an-explicit-carrier-choice-not-a-derivation-of-the-physical-gauge-rank"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswWilsonVerlinde_diagonalization where
  formalizes @ "claim:the-jain-denominator-csw-comparison-carrier-inherits-the-proved-wilson-verlinde-s-matrix-diagonalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswWilsonVerlinde_diagonalization",
  caveat @ "claim:this-is-the-u-one-q-comparison-carrier-and-does-not-identify-the-full-jain-k-matrix-wilson-category"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswComparison_topologicalEntropy where
  formalizes @ "claim:the-csw-torus-comparison-carrier-at-the-jain-sector-count-has-topological-entropy-one-half-log-q",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling.tee_from_csw_torus_dimension",
  caveat @ "claim:this-specializes-the-u-one-q-comparison-functional-and-does-not-substitute-for-a-full-hierarchical-k-matrix-quantum-dimension-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_topologicallyMassiveYangMills_zeroMass where
  formalizes @ "claim:on-the-jain-sized-finite-local-carrier-zero-chern-simons-topological-mass-reduces-the-djt-equation-exactly-to-yang-mills",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge.topologicallyMassiveYangMills_zeroMass_iff_yangMills",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling_jain_sequence",
  caveat @ "claim:the-zero-mass-reduction-is-an-exact-equation-equivalence-not-a-claim-that-the-physical-fqhe-topological-mass-vanishes",
  caveat @ "claim:the-finite-local-matrix-carrier-does-not-prove-a-continuum-yang-mills-chern-simons-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.observedJain_hallPlateaus_csw_dataContact where
  formalizes @ "claim:the-observed-two-fifths-and-three-sevenths-hall-responses-and-elementary-quasiparticle-charges-match-the-checked-k-matrix-determinants-and-csw-comparison-sector-counts",
  epistemic_status @ "conditional-model",
  prediction_class @ "standard-physics-data-contact",
  standard_physics_postulates @ "law:fractional-hall-conductance-sigma-xy-equals-filling-times-e-squared-over-h",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_hallConductance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_hallConductance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_terminalQuasiparticleCharge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_terminalQuasiparticleCharge",
  supported_by @ "measurement:feldman-krauss-smet-yacoby-2012-standard-composite-fermion-sequence-doi-10.1126-science.1224784",
  supported_by @ "measurement:chung-heiblum-umansky-2003-fractional-shot-noise-doi-10.1103-physrevlett.91.216804",
  experimental_bound @ "value:incompressible-states-and-dimensionless-hall-responses-at-two-fifths-and-three-sevenths-with-unbunched-elementary-charges-e-over-five-and-e-over-seven;test:the-response-denominators-and-elementary-charge-denominators-must-agree-with-the-checked-k-matrices",
  caveat @ "epistemic:the-measurements-verify-the-fractions-and-incompressibility-not-equivalence-of-the-full-jain-k-matrix-category-with-u-one-q",
  caveat @ "experiment:shot-noise-effective-charge-is-regime-dependent-because-low-temperature-backscattering-can-bunch-elementary-quasiparticles",
  caveat @ "claim:the-yang-mills-casimir-spectrum-beta-and-the-cayley-coordinate-are-not-fixed-by-these-hall-measurements"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainTwoFifths_quasiparticle_ne_extendedStandardModelCharge where
  formalizes @ "claim:the-jain-two-fifths-elementary-quasiparticle-charge-e-over-five-is-not-the-charge-of-any-generated-standard-model-weyl-fermion-or-sterile-neutrino",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.extendedStandardModelElectricCharge_thirdQuantized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_two_fifths_terminalQuasiparticleCharge",
  caveat @ "scope:this-separates-an-emergent-condensed-matter-quasiparticle-charge-from-the-elementary-standard-model-charge-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainThreeSevenths_quasiparticle_ne_extendedStandardModelCharge where
  formalizes @ "claim:the-jain-three-sevenths-elementary-quasiparticle-charge-e-over-seven-is-not-the-charge-of-any-generated-standard-model-weyl-fermion-or-sterile-neutrino",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.extendedStandardModelElectricCharge_thirdQuantized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jain_three_sevenths_terminalQuasiparticleCharge",
  caveat @ "scope:this-separates-an-emergent-condensed-matter-quasiparticle-charge-from-the-elementary-standard-model-charge-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainQuasiparticle_particlePhysicsChargeBoundary where
  formalizes @ "claim:jain-e-over-five-and-e-over-seven-quasiparticles-share-the-unit-electric-charge-normalization-with-particle-physics-while-remaining-outside-the-standard-model-elementary-charge-spectrum",
  epistemic_status @ "conditional-model",
  standard_physics_postulates @ "postulate:abelian-chern-simons-quasiparticle-charge-is-t-transpose-k-inverse-l",
  standard_physics_postulates @ "postulate:su-five-standard-model-electric-charges-lie-on-the-one-third-charge-lattice",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.proton_charge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.extendedStandardModelElectricCharge_thirdQuantized",
  supported_by @ "measurement:chung-heiblum-umansky-2003-fractional-shot-noise-doi-10.1103-physrevlett.91.216804",
  caveat @ "scope:five-or-seven-hall-charge-units-adding-to-one-electron-charge-is-additive-charge-bookkeeping-not-a-proton-composition-or-anyon-fusion-theorem",
  caveat @ "scope:hall-quasiparticles-are-emergent-two-dimensional-excitations-not-new-free-elementary-particles"

zil_file_contract physlib.entanglementBraneModularTQFT where
  promises "A finite semisimple implementation of Donnelly and Wong's entanglement-brane core: window closing is a linear retract, induced open modular evolution composes and recovers the closed evolution, the two-dimensional Yang-Mills sphere weights are normalized from positive Casimir Boltzmann factors, one- and two-interval entropies split into Shannon and edge-mode terms, logarithmic negativity is the edge moment and obeys the Jensen comparison, and finite one-dimensional Abelian sectors have vanishing representation edge contribution.  The observed 2/5 and 3/7 Hall responses, reciprocal resistivities, and terminal e/5 and e/7 charges are connected to the checked determinant-five/determinant-seven Jain matrices and CSW sector counts.  Their particle-physics boundary is explicit: five or seven corresponding quasiparticle charge units recover the proton/electron unit normalization, while neither individual emergent charge belongs to the complete generated Standard-Model e/3 charge lattice.  The complete Jain p=1 family is connected separately to the existing composite-fermion filling, CSW torus and Wilson comparison carriers, normalized Yang-Mills sectors, the finite local Chern-Simons/Yang-Mills curvature identity, the DJT zero-mass Yang-Mills reduction, the CSW entropy functional, and the rational Cayley law while retaining the Shannon sector."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.hierarchyFilling",
    "lean:Physlib.QuantumMechanics.ComplexAction.FQHEHierarchyContinuedFraction.jainHierarchy_cayleyVelocity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree.extendedStandardModelElectricCharge_thirdQuantized",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.proton_charge",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.localCSCurvature",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswWilsonVerlindeOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.TopologicallyMassiveGauge.TopologicallyMassiveYangMillsEquation"]
  forbids_substitutes ["claiming-that-continuum-aqft-local-algebras-factor-as-a-hilbert-space-tensor-product",
    "claiming-a-classification-of-all-open-closed-tqfts-admitting-entanglement-branes",
    "claiming-the-full-nonchiral-gross-taylor-bv-brst-extension-left-open-by-the-paper",
    "identifying-the-shannon-sector-entropy-with-quantum-edge-mode-negativity",
    "identifying-an-abelian-k-matrix-theory-with-u-one-level-det-k-from-sector-count-alone",
    "identifying-an-emergent-hall-quasiparticle-with-an-elementary-standard-model-fermion-or-a-proton",
    "reading-additive-unit-charge-closure-as-a-dynamical-anyon-fusion-or-particle-composition-theorem",
    "deriving-the-yang-mills-casimir-spectrum-or-beta-parameter-from-the-jain-filling-alone"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.EntanglementBrane.close_openEvolution,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.EntanglementBrane.openModularFlow_add,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.extendedEntropy_singleInterval,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.extendedEntropy_twoIntervals,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.YMSectorData.meanLogEdgeDim_le_logNegativity,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.neg_log_ymBoltzmannWeight,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.ymSphereProbability_sum,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.u1Verlinde_edge_contribution_vanishes,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.hierarchyLaughlin_entanglementBrane_bridge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainTwoFifths_entanglementBrane_bridge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainThreeSevenths_entanglementBrane_bridge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswYangMills_cayley_bridge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_localChernSimons_yangMills_bridge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswWilsonVerlinde_diagonalization,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_cswComparison_topologicalEntropy,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainHierarchy_topologicallyMassiveYangMills_zeroMass,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.observedJain_hallPlateaus_csw_dataContact,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainTwoFifths_quasiparticle_ne_extendedStandardModelCharge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainThreeSevenths_quasiparticle_ne_extendedStandardModelCharge,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.EntanglementBraneModularTQFT.jainQuasiparticle_particlePhysicsChargeBoundary]

/- ZIL-END -/
