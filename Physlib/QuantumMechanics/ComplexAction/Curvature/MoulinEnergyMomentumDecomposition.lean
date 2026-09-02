/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureOperator

meta import Zil

/-!
# Moulin's 4-index Einstein tensor and the two-part energy-momentum decomposition

Completes §4.2–4.6 of F. Moulin, *Generalization of Einstein's gravitational field equations*
(arXiv:2405.03698): the 4-index generalized Einstein tensor `G_{ijkl}`, its split into a Weyl
(conformal/field) part and a `B` (matter) part, and the resulting **two-part decomposition of the total
4-index energy-momentum tensor** `T_{ijkl} = T^(F)_{ijkl} + T^(M)_{ijkl}`.

* **§A — the tensors.** The `B`-tensor (Eq. 36) and the 4-index Einstein tensor `G_{ijkl}` (Eq. 32) for a
  parameter `a`.
* **§B — the split `G = aC + B`** (`fourIndexEinstein_eq_weyl_add_b`, Eq. 34): the generalized Einstein tensor
  is `a` times the (trace-free) Weyl tensor plus the `B`-tensor — a purely algebraic identity.
* **§C — contractions back to the 2-index Einstein tensor.** `gᵃᶜ B_{abcd} = R_{bd} − ½R g_{bd}`
  (`bTensor_contraction`, Eq. 38) from the Moulin contraction lemmas; together with the Weyl trace-freeness
  (`weyl_traceFree_matrix`, Eq. 37) this gives `gᵃᶜ G_{abcd} = G_{bd}` (`fourIndexEinstein_contraction`,
  Eq. 33) — the generalized equation reduces to ordinary general relativity.
* **§D — the 4-index energy-momentum tensor.** From `G_{ijkl} = χ T_{ijkl}`, the total energy-momentum tensor
  `T = G/χ` splits (Eq. 39) into the **field** part `T^(F) = aC/χ` (Eq. 47, trace-free — the gravitational
  field in vacuum) and the **matter** part `T^(M) = B/χ` (Eq. 45, contracting to the 2-index source):
  `energyMomentum_two_part`, `field_traceFree`, `matter_contraction`.

## References

* F. Moulin (2024), arXiv:2405.03698, §4.2–4.6, Eqs. 32, 34, 36, 38, 39, 45, 47. Carrier: `Physlib`
  (`Curvature.WeylTensorTraceFree`, `Curvature.RiemannCurvatureOperator`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- **Moulin's `B`-tensor** (Eq. 36) `B_{ijkl} = 1/(n−2)(g_{ik}R_{jl} − g_{il}R_{jk} − g_{jk}R_{il} +
g_{jl}R_{ik}) − n/(2(n−1)(n−2)) (g_{ik}g_{jl} − g_{il}g_{jk}) R` — the matter part of the curvature. -/
noncomputable def bTensor (n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) : RiemannTensor ι :=
  fun i j k l => (1 / (n - 2)) * (g i k * Ric j l - g i l * Ric j k - g j k * Ric i l + g j l * Ric i k)
    - (n * scalarR / (2 * (n - 1) * (n - 2))) * (g i k * g j l - g i l * g j k)

/-- **Moulin's 4-index Einstein tensor** (Eq. 32) `G_{ijkl} = a R_{ijkl} + (1−a)/(n−2)(g_{ik}R_{jl} − … ) −
(n−2a)/(2(n−1)(n−2)) (g_{ik}g_{jl} − g_{il}g_{jk}) R`, the linear-in-Riemann generalization of the Einstein
tensor. -/
noncomputable def fourIndexEinsteinTensor (a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) : RiemannTensor ι :=
  fun i j k l => a * Rm i j k l
    + ((1 - a) / (n - 2)) * (g i k * Ric j l - g i l * Ric j k - g j k * Ric i l + g j l * Ric i k)
    - ((n - 2 * a) * scalarR / (2 * (n - 1) * (n - 2))) * (g i k * g j l - g i l * g j k)


omit [Fintype ι] [DecidableEq ι] in
/-- **[Moulin Eq. 34] `G_{ijkl} = a C_{ijkl} + B_{ijkl}`.** The 4-index Einstein tensor splits into `a` times
the Weyl conformal tensor plus the `B`-tensor — a purely algebraic identity. -/
lemma fourIndexEinstein_eq_weyl_add_b (a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    fourIndexEinsteinTensor a n g Ric scalarR Rm
      = a • weylTensor n g Ric scalarR Rm + bTensor n g Ric scalarR := by
  funext i j k l
  simp only [fourIndexEinsteinTensor, weylTensor, bTensor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring


variable {g gInv : Matrix ι ι ℝ}

/-- **[Moulin Eq. 38] `gᵃᶜ B_{abcd} = R_{bd} − ½R g_{bd}`** — the `B`-tensor contracts to the 2-index Einstein
tensor. -/
lemma bTensor_contraction (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    ricci gInv (bTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm))
      = einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g := by
  ext b d
  show (∑ a, ∑ c, gInv a c *
    bTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) a b c d) = _
  have expand : ∀ a c, gInv a c *
      bTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) a b c d
      = (1 / ((Fintype.card ι : ℝ) - 2)) * (gInv a c * (g a c * ricci gInv Rm b d
          - g a d * ricci gInv Rm b c - g b c * ricci gInv Rm a d + g b d * ricci gInv Rm a c))
        - ((Fintype.card ι : ℝ) * scalarCurvature gInv Rm
            / (2 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2)))
            * (gInv a c * (g a c * g b d - g a d * g b c)) := by
    intro a c; simp only [bTensor]; ring
  simp only [expand, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [contraction_metricRicci hg hgi hinv h, contraction_metricStructure hg hgi hinv,
    einsteinTensor, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **[Moulin Eq. 37, matrix form] `gᵃᶜ C_{abcd} = 0`** — the Weyl tensor contraction vanishes. -/
lemma weyl_traceFree_matrix (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    ricci gInv (weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) = 0 := by
  ext b d; simpa using weyl_traceFree hg hgi hinv h hn1 hn2 b d

/-- **[Moulin Eq. 33] `gᵃᶜ G_{abcd} = G_{bd}`** — the generalized 4-index Einstein tensor contracts to the
ordinary 2-index Einstein tensor, so the generalized equation reduces to general relativity. -/
lemma fourIndexEinstein_contraction (a : ℝ) (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    ricci gInv (fourIndexEinsteinTensor a (Fintype.card ι) g
        (ricci gInv Rm) (scalarCurvature gInv Rm) Rm)
      = einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g := by
  rw [fourIndexEinstein_eq_weyl_add_b (hn1 := hn1) (hn2 := hn2), ricci_add, ricci_smul,
    weyl_traceFree_matrix hg hgi hinv h hn1 hn2, smul_zero, zero_add,
    bTensor_contraction hg hgi hinv h hn1 hn2]


/-- **The total 4-index energy-momentum tensor** `T_{ijkl} = G_{ijkl}/χ` (from `G = χ T`, Moulin Eq. 31). -/
noncomputable def fourIndexEnergyMomentum (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) : RiemannTensor ι :=
  χ⁻¹ • fourIndexEinsteinTensor a n g Ric scalarR Rm

/-- **The matter part** of the energy-momentum tensor `T^(M)_{ijkl} = B_{ijkl}/χ` (Moulin Eq. 45). -/
noncomputable def matterEnergyMomentum (χ n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) : RiemannTensor ι :=
  χ⁻¹ • bTensor n g Ric scalarR

/-- **The gravitational-field part** of the energy-momentum tensor `T^(F)_{ijkl} = a C_{ijkl}/χ`
(Moulin Eq. 47). -/
noncomputable def fieldEnergyMomentum (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) : RiemannTensor ι :=
  χ⁻¹ • (a • weylTensor n g Ric scalarR Rm)

omit [Fintype ι] [DecidableEq ι] in
/-- **[Moulin Eq. 39] the two-part decomposition of the total energy-momentum tensor**
`T_{ijkl} = T^(F)_{ijkl} + T^(M)_{ijkl}` — the total 4-index energy-momentum splits into a gravitational-field
part and a matter part. -/
lemma energyMomentum_two_part (χ a n : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι)
    (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    fourIndexEnergyMomentum χ a n g Ric scalarR Rm
      = fieldEnergyMomentum χ a n g Ric scalarR Rm + matterEnergyMomentum χ n g Ric scalarR := by
  rw [fourIndexEnergyMomentum, fieldEnergyMomentum, matterEnergyMomentum,
    fourIndexEinstein_eq_weyl_add_b (hn1 := hn1) (hn2 := hn2), smul_add]

/-- **[The field part is trace-free, Moulin Eq. 48] `gᵃᶜ T^(F)_{abcd} = 0`.** The gravitational-field
energy-momentum has vanishing contraction — it is invisible to the 2-index equation. -/
lemma field_traceFree (χ a : ℝ) (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    ricci gInv (fieldEnergyMomentum χ a (Fintype.card ι) g
      (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) = 0 := by
  rw [fieldEnergyMomentum, ricci_smul, ricci_smul, weyl_traceFree_matrix hg hgi hinv h hn1 hn2,
    smul_zero, smul_zero]

/-- **[The matter part contracts to the Einstein source] `gᵃᶜ T^(M)_{abcd} = G_{bd}/χ`.** The matter
energy-momentum carries the ordinary 2-index source of general relativity. -/
lemma matter_contraction (χ : ℝ) (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    ricci gInv (matterEnergyMomentum χ (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm))
      = χ⁻¹ • einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g := by
  rw [matterEnergyMomentum, ricci_smul, bTensor_contraction hg hgi hinv h hn1 hn2]

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_eq_weyl_add_b where
  formalizes @ "claim:moulins-4-index-einstein-tensor-splits-algebraically-into-a-times-the-trace-free-weyl-conformal-part-plus-the-b-matter-tensor",
  supported_by @ "paper:moulin-arxiv-2405-03698-generalization-of-einsteins-gravitational-field-equations"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_contraction where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_eq_weyl_add_b",
  formalizes @ "claim:the-generalized-4-index-einstein-tensor-contracts-traces-back-to-the-ordinary-two-index-einstein-tensor-so-the-generalized-field-equation-reduces-to-standard-general-relativity",
  requires @ "claim:moulins-4-index-einstein-tensor-splits-algebraically-into-a-times-the-trace-free-weyl-conformal-part-plus-the-b-matter-tensor"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.energyMomentum_two_part where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_eq_weyl_add_b",
  formalizes @ "claim:the-total-4-index-energy-momentum-tensor-decomposes-into-a-gravitational-field-part-and-a-matter-part-t-equals-t-field-plus-t-matter"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.matter_contraction where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor_contraction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.ricci_smul",
  formalizes @ "claim:the-matter-part-of-the-4-index-energy-momentum-tensor-alone-carries-the-ordinary-two-index-einstein-source-while-the-trace-free-field-part-is-invisible-to-the-two-index-equation"

zil_file_contract physlib.moulinEnergyMomentumDecomposition where
  promises "Moulin's 4-index Einstein tensor and the two-part energy-momentum decomposition (arXiv:2405.03698, sections 4.2-4.6). The 4-index Einstein tensor splits into a*(trace-free Weyl/conformal part) plus the B (matter) tensor (fourIndexEinstein_eq_weyl_add_b), and contracts back to the ordinary 2-index Einstein tensor (fourIndexEinstein_contraction), so the generalized equation reduces to standard GR. The total energy-momentum splits into field and matter parts (energyMomentum_two_part), with the matter part alone carrying the 2-index Einstein source (matter_contraction)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinsteinTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.bTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.matterEnergyMomentum",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fieldEnergyMomentum",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.weylTensor"]
  forbids_substitutes ["the physical interpretation of the trace-free field part as gravitational-wave / Weyl radiation and the covariant conservation laws on a genuine spacetime, which are the cited GR infrastructure",
    "any claim that a matter model is specified; only the algebraic Weyl-plus-B decomposition and its 2-index contraction are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_eq_weyl_add_b,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.fourIndexEinstein_contraction,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.energyMomentum_two_part,
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.matter_contraction]

/- ZIL-END -/
