/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
public import Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo

/-!
# The Standard-Model generation is anomaly-free

A chiral gauge theory is consistent only if its gauge anomalies cancel. For one Standard-Model
generation, the relevant state space is generated internally as the `SU(5)` representation
`5̄ ⊕ Λ²(5)`: five antifundamental indices plus ten ordered wedge pairs. The quantum numbers below
are computed from the `SU(3) ⊕ SU(2)` block decomposition and the additive generator action on
`Λ²(5)`, then checked against the repository's existing charge and conservation-law structures.

* **§A — multiplet shorthand.** `genY`, `genMult`; these are used only for the compressed anomaly
  formulas, while the state-level traces are computed from `SMWeylFermion`.
* **§B — computable Weyl-fermion generation.** `SMWeylFermion` and `fermionQuantumNumbers` compute
  `(Q,T₃,Y,B,L,spin,color,weak,chiral)` for the 15 left-handed Weyl states directly from the
  `5̄ ⊕ Λ²(5)` indices, with `fermionElectricCharge_eq_gmn` and links back to the existing `SU(5)`
  `5̄`/`10` charge vectors.
* **§C — named generated fermions.** Electron, neutrino, colour-labelled quarks and antiquarks,
  and `e^c` are concrete `SMWeylFermion` terms with checked quantum-number theorems.
* **§D — three-generation labels.** Three copies of the generated generation give the named
  electron/muon/tau, neutrino, quark, and antiquark states.
* **§E — sterile right-handed neutrino singlets.** The optional `ν_R` states are added as
  gauge-singlet, right-chiral states outside the minimal `SU(5)` representation, giving
  `45 + 3 = 48` states without changing the minimal `15`/generation theorem.
* **§F — the `U(1)` anomalies.** `gravitationalAnomaly` `= ∑ mult·Y = 0` (the mixed
  gravitational–`U(1)_Y`), `cubicAnomaly` `= ∑ mult·Y³ = 0` (the `U(1)_Y³`).
* **§G — the non-abelian mixed anomalies.** `su2Anomaly` `[SU(2)]²U(1)_Y = 0` (weak doublets only),
  `su3Anomaly` `[SU(3)]²U(1)_Y = 0` (colour triplets only).

**Honest layering.** Proven: all four anomaly coefficients vanish for the generation as arithmetic
over the hypercharges. Interpretive: that these coefficients *are* the gauge anomalies (the triangle
diagrams) is the physics; the identification is standard, not re-derived here.

## References

* Standard-Model anomaly cancellation (`∑Y = ∑Y³ = 0` per generation); `SU(5)` `5̄ ⊕ 10` is
  anomaly-free (Georgi–Glashow). Reuses the internal `SU(5)` charge generators and
  `Particles.GellMannNishijima`; no particle-row source is imported for the computation.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree

open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor


/-- **The weak hypercharges** of the five left-handed multiplets `{Q, u^c, d^c, L, e^c}`
(`Q = T₃ + Y/2` convention): `(+1/3, −4/3, +2/3, −1, +2)`. -/
def genY : Fin 5 → ℚ := ![1/3, -4/3, 2/3, -1, 2]

/-- **The state multiplicities** (colour × weak) of the multiplets: `(6, 3, 3, 2, 1)`, summing to the
`15` chiral states of a generation. -/
def genMult : Fin 5 → ℚ := ![6, 3, 3, 2, 1]

/-- **The positron `e⁺` charge `+1`** from Gell-Mann–Nishijima: `Q = T₃ + Y/2 = 0 + 2/2`. -/
lemma positron_charge_from_gmn : gellMannNishijima 0 2 = 1 := by
  unfold gellMannNishijima; norm_num

/-- **The up antiquark `u^c` charge `−2/3`** from Gell-Mann–Nishijima: `0 + (−4/3)/2`. -/
lemma upAntiquark_charge_from_gmn : gellMannNishijima 0 (-4 / 3) = -2 / 3 := by
  unfold gellMannNishijima; norm_num

/-- **The down antiquark `d^c` charge `+1/3`** from Gell-Mann–Nishijima: `0 + (2/3)/2`. -/
lemma downAntiquark_charge_from_gmn : gellMannNishijima 0 (2 / 3) = 1 / 3 := by
  unfold gellMannNishijima; norm_num


/-- The colour representation carried by a Standard-Model Weyl field. -/
inductive ColourRepresentation where
  | singlet
  | triplet
  | antiTriplet
  deriving DecidableEq, Repr

/-- The weak `SU(2)_L` representation carried by a Standard-Model Weyl field. -/
inductive WeakRepresentation where
  | singlet
  | doublet
  deriving DecidableEq, Repr

/-- The chirality label used for the one-generation Weyl state space. -/
inductive WeylChirality where
  | left
  | right
  deriving DecidableEq, Repr

/-- The `SU(5)` `10 = Λ²(5)` basis indices, represented without a lookup list as ordered
pairs `i < j` of fundamental indices. -/
abbrev SU5TenIndex := {p : Fin 5 × Fin 5 // p.1 < p.2}

set_option backward.isDefEq.respectTransparency false in
/-- The 15 left-handed Weyl fermion states in one Standard-Model generation, represented by their
`SU(5)` origin rather than by imported particle rows: five states in the `5̄` and ten states in
`Λ²(5)`. -/
inductive SMWeylFermion where
  | fiveBar (i : Fin 5)
  | ten (ij : SU5TenIndex)
  deriving DecidableEq, Fintype

/-- A computable bundle of the usual fermion quantum numbers.  The hypercharge uses the canonical
`Q = T₃ + Y/2` convention, and `spin` is measured in units of `ℏ`. -/
structure FermionQuantumNumbers where
  electricCharge : ℚ
  weakIsospin3 : ℚ
  hypercharge : ℚ
  baryonNumber : ℚ
  leptonNumber : ℚ
  spin : ℚ
  colour : ColourRepresentation
  weak : WeakRepresentation
  chirality : WeylChirality
  deriving Repr

/-- The `SU(3)` colour block inside the `SU(5)` fundamental indices. -/
def su5IndexIsColour (i : Fin 5) : Prop := i.val < 3

instance decidableSu5IndexIsColour (i : Fin 5) : Decidable (su5IndexIsColour i) := by
  unfold su5IndexIsColour
  infer_instance

/-- The `5̄` weak-isospin component computed from the `SU(3) ⊕ SU(2)` block decomposition:
colour indices are weak singlets, while the two weak indices form the lepton doublet. -/
def su5AntifundWeakIsospin3FromBlock (i : Fin 5) : ℚ :=
  if i = 3 then -1 / 2 else if i = 4 then 1 / 2 else 0

/-- The `5̄` conventional weak hypercharge computed from the `SU(3) ⊕ SU(2)` block decomposition:
the colour block has `Y = 2/3`, the weak block has `Y = -1`. -/
def su5AntifundHyperchargeFromBlock (i : Fin 5) : ℚ :=
  if su5IndexIsColour i then 2 / 3 else -1

/-- The fundamental `5` has the conjugate weak-isospin generator. -/
def su5FundWeakIsospin3FromBlock (i : Fin 5) : ℚ :=
  -su5AntifundWeakIsospin3FromBlock i

/-- The fundamental `5` has the conjugate hypercharge generator. -/
def su5FundHyperchargeFromBlock (i : Fin 5) : ℚ :=
  -su5AntifundHyperchargeFromBlock i

/-- The electric charge of a `5̄` index is computed, not tabulated, by Gell-Mann--Nishijima. -/
lemma su5Antifund_charge_from_block (i : Fin 5) :
    gellMannNishijima (su5AntifundWeakIsospin3FromBlock i)
      (su5AntifundHyperchargeFromBlock i) = su5AntifundCharge i := by
  fin_cases i <;>
    simp [su5AntifundWeakIsospin3FromBlock, su5AntifundHyperchargeFromBlock,
      su5IndexIsColour, gellMannNishijima, su5AntifundCharge] <;> norm_num

/-- The third weak-isospin component `T₃`, computed from the `SU(5)` representation index.  On
`Λ²(5)` the generator acts additively on wedge factors. -/
def fermionWeakIsospin3 : SMWeylFermion → ℚ
  | .fiveBar i => su5AntifundWeakIsospin3FromBlock i
  | .ten ij => su5FundWeakIsospin3FromBlock ij.1.1 + su5FundWeakIsospin3FromBlock ij.1.2

/-- The conventional weak hypercharge `Y`, computed from the `SU(5)` representation index.  On
`Λ²(5)` the generator acts additively on wedge factors. -/
def fermionHypercharge : SMWeylFermion → ℚ
  | .fiveBar i => su5AntifundHyperchargeFromBlock i
  | .ten ij => su5FundHyperchargeFromBlock ij.1.1 + su5FundHyperchargeFromBlock ij.1.2

/-- The electric charge computed from `T₃ + Y/2`.  The theorem
`fermionElectricCharge_eq_gmn` below identifies this local computation with the repository's
canonical Gell-Mann--Nishijima definition. -/
def fermionElectricCharge (f : SMWeylFermion) : ℚ :=
  fermionWeakIsospin3 f + fermionHypercharge f / 2

/-- A rational electric charge lies on the Standard-Model third-charge
lattice when it is an integer multiple of `e/3`. -/
def IsThirdQuantizedCharge (q : ℚ) : Prop :=
  ∃ n : ℤ, q = n / 3

/-- The baryon number, computed from whether the `SU(5)` indices lie in the colour block.  The
`Λ²(5)` cases are: colour-colour (`u^c`-type), colour-weak (`Q`-type), and weak-weak (`e^c`-type). -/
def fermionBaryonNumber : SMWeylFermion → ℚ
  | .fiveBar i => if su5IndexIsColour i then -1 / 3 else 0
  | .ten ij =>
      if su5IndexIsColour ij.1.1 ∧ su5IndexIsColour ij.1.2 then -1 / 3
      else if su5IndexIsColour ij.1.1 ∨ su5IndexIsColour ij.1.2 then 1 / 3
      else 0

/-- The lepton number, computed from whether the `SU(5)` indices lie in the weak block. -/
def fermionLeptonNumber : SMWeylFermion → ℚ
  | .fiveBar i => if su5IndexIsColour i then 0 else 1
  | .ten ij =>
      if ¬ su5IndexIsColour ij.1.1 ∧ ¬ su5IndexIsColour ij.1.2 then -1 else 0

/-- The colour representation, computed from the index block membership. -/
def fermionColour : SMWeylFermion → ColourRepresentation
  | .fiveBar i => if su5IndexIsColour i then .antiTriplet else .singlet
  | .ten ij =>
      if su5IndexIsColour ij.1.1 ∧ su5IndexIsColour ij.1.2 then .antiTriplet
      else if su5IndexIsColour ij.1.1 ∨ su5IndexIsColour ij.1.2 then .triplet
      else .singlet

/-- The weak representation, computed from the index block membership. -/
def fermionWeakRepresentation : SMWeylFermion → WeakRepresentation
  | .fiveBar i => if su5IndexIsColour i then .singlet else .doublet
  | .ten ij =>
      if su5IndexIsColour ij.1.1 ∨ su5IndexIsColour ij.1.2 then
        if su5IndexIsColour ij.1.1 ∧ su5IndexIsColour ij.1.2 then .singlet else .doublet
      else .singlet

/-- The full computable quantum-number map for one Standard-Model Weyl fermion. -/
def fermionQuantumNumbers (f : SMWeylFermion) : FermionQuantumNumbers where
  electricCharge := fermionElectricCharge f
  weakIsospin3 := fermionWeakIsospin3 f
  hypercharge := fermionHypercharge f
  baryonNumber := fermionBaryonNumber f
  leptonNumber := fermionLeptonNumber f
  spin := 1 / 2
  colour := fermionColour f
  weak := fermionWeakRepresentation f
  chirality := .left

/-- The additive `(Q,B,L)` projection reuses the repository's conservation-law structure. -/
def fermionAdditiveQuantumNumbers (f : SMWeylFermion) :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers :=
  ⟨fermionElectricCharge f, fermionBaryonNumber f, fermionLeptonNumber f⟩

/-- The computed electric charge is not independent data: it is exactly Gell-Mann--Nishijima. -/
lemma fermionElectricCharge_eq_gmn (f : SMWeylFermion) :
    (fermionQuantumNumbers f).electricCharge =
      gellMannNishijima (fermionQuantumNumbers f).weakIsospin3
        (fermionQuantumNumbers f).hypercharge := by
  simp [fermionQuantumNumbers, fermionElectricCharge, gellMannNishijima]

/-- Every field in the one-generation state space has spin `1/2`. -/
lemma fermion_spin_half (f : SMWeylFermion) : (fermionQuantumNumbers f).spin = 1 / 2 := rfl

/-- The generated fermions are tied to the existing spin-statistics theorem: spin `1/2` has
fermionic exchange. -/
lemma fermion_spin_statistics (_f : SMWeylFermion) :
    Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist.ribbonTwist
      ((0 : ℝ) + 1 / 2) = -1 :=
  by
    simpa using
      (Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo.halfInteger_spin_fermion 0)

/-- The `5̄` branch agrees with the existing `SU(5)` electric-charge generator. -/
lemma su5AntifundAsFermion_charge (i : Fin 5) :
    (fermionQuantumNumbers (SMWeylFermion.fiveBar i)).electricCharge = su5AntifundCharge i := by
  rw [← su5Antifund_charge_from_block i]
  simp [fermionQuantumNumbers, fermionElectricCharge, fermionWeakIsospin3, fermionHypercharge,
    gellMannNishijima]

/-- The `10 = Λ²(5)` electric charge is computed by additivity of the fundamental generator on
wedge factors. -/
def su5TenComputedCharge (ij : SU5TenIndex) : ℚ :=
  su5FundCharge ij.1.1 + su5FundCharge ij.1.2

/-- The `10` branch agrees with the additive `Λ²(5)` charge computation; no particle-row lookup is
used. -/
lemma su5TenAsFermion_charge (ij : SU5TenIndex) :
    (fermionQuantumNumbers (SMWeylFermion.ten ij)).electricCharge = su5TenComputedCharge ij := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  all_goals
    simp [fermionQuantumNumbers, fermionElectricCharge, fermionWeakIsospin3, fermionHypercharge,
      su5FundWeakIsospin3FromBlock, su5FundHyperchargeFromBlock,
      su5AntifundWeakIsospin3FromBlock, su5AntifundHyperchargeFromBlock, su5IndexIsColour,
      su5TenComputedCharge, su5FundCharge,
      Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4.weightConjugation,
      su5AntifundCharge] at hij ⊢
  all_goals norm_num

/-- Every Weyl fermion generated by the `SU(5)` `5̄ ⊕ 10` carrier has
electric charge on the `e/3` lattice.  This packages the complete finite
charge spectrum as one reusable theorem rather than a list of named cases. -/
lemma fermionElectricCharge_thirdQuantized (f : SMWeylFermion) :
    IsThirdQuantizedCharge (fermionElectricCharge f) := by
  cases f with
  | fiveBar i =>
      fin_cases i <;>
        simp [IsThirdQuantizedCharge, fermionElectricCharge, fermionWeakIsospin3,
          fermionHypercharge, su5AntifundWeakIsospin3FromBlock,
          su5AntifundHyperchargeFromBlock, su5IndexIsColour] <;>
        first
          | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
          | (refine ⟨-1, ?_⟩; norm_num; done) | (refine ⟨2, ?_⟩; norm_num; done)
          | (refine ⟨-2, ?_⟩; norm_num; done) | (refine ⟨3, ?_⟩; norm_num; done)
          | (refine ⟨-3, ?_⟩; norm_num; done) | norm_num
  | ten ij =>
      rcases ij with ⟨⟨i, j⟩, hij⟩
      fin_cases i <;> fin_cases j
      all_goals
        simp [IsThirdQuantizedCharge, fermionElectricCharge, fermionWeakIsospin3,
          fermionHypercharge, su5FundWeakIsospin3FromBlock,
          su5FundHyperchargeFromBlock, su5AntifundWeakIsospin3FromBlock,
          su5AntifundHyperchargeFromBlock, su5IndexIsColour] at hij ⊢
      all_goals
        first
          | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
          | (refine ⟨-1, ?_⟩; norm_num; done) | (refine ⟨2, ?_⟩; norm_num; done)
          | (refine ⟨-2, ?_⟩; norm_num; done) | (refine ⟨3, ?_⟩; norm_num; done)
          | (refine ⟨-3, ?_⟩; norm_num; done) | norm_num

/-- One Standard-Model generation contains `15` left-handed Weyl fermion states. -/
lemma smWeylFermion_state_count : Fintype.card SMWeylFermion = 15 := by
  native_decide

/-- The electric-charge trace computed over the generated `5̄ ⊕ Λ²(5)` Weyl states. -/
def smGenerationElectricChargeTrace : ℚ :=
  ∑ f : SMWeylFermion, fermionElectricCharge f

/-- The generated `5̄ ⊕ Λ²(5)` one-generation state space is electrically neutral. -/
lemma smGenerationCharge_zero : smGenerationElectricChargeTrace = 0 := by
  native_decide

/-- The computed electron state agrees with the existing additive `(Q,B,L)` electron quantum
numbers. -/
lemma electron_additiveQuantumNumbers_eq_particleElectron :
    fermionAdditiveQuantumNumbers (SMWeylFermion.fiveBar 3) =
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.electron := by
  ext <;> simp [fermionAdditiveQuantumNumbers, fermionElectricCharge, fermionWeakIsospin3,
    fermionHypercharge, fermionBaryonNumber, fermionLeptonNumber,
    su5AntifundWeakIsospin3FromBlock, su5AntifundHyperchargeFromBlock, su5IndexIsColour,
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.electron]


/-- A compact proposition stating the computed quantum numbers of a generated Weyl state. -/
def HasComputedQuantumNumbers (f : SMWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) : Prop :=
  (fermionQuantumNumbers f).electricCharge = electric
    ∧ (fermionQuantumNumbers f).weakIsospin3 = weakIsospin3
    ∧ (fermionQuantumNumbers f).hypercharge = hypercharge
    ∧ (fermionQuantumNumbers f).baryonNumber = baryon
    ∧ (fermionQuantumNumbers f).leptonNumber = lepton
    ∧ (fermionQuantumNumbers f).spin = spin
    ∧ (fermionQuantumNumbers f).colour = colour
    ∧ (fermionQuantumNumbers f).weak = weak
    ∧ (fermionQuantumNumbers f).chirality = chirality

instance decidableHasComputedQuantumNumbers (f : SMWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) :
    Decidable
      (HasComputedQuantumNumbers f electric weakIsospin3 hypercharge baryon lepton spin colour weak
        chirality) := by
  unfold HasComputedQuantumNumbers
  infer_instance

/-- The left-handed electron `e_L`, generated as the weak charged component of `5̄`. -/
def leftElectronState : SMWeylFermion := .fiveBar 3

/-- The left-handed electron neutrino `ν_{eL}`, generated as the weak neutral component of `5̄`. -/
def leftElectronNeutrinoState : SMWeylFermion := .fiveBar 4

/-- The red down antiquark component in `5̄`. -/
def downAntiquarkRedState : SMWeylFermion := .fiveBar 0

/-- The green down antiquark component in `5̄`. -/
def downAntiquarkGreenState : SMWeylFermion := .fiveBar 1

/-- The blue down antiquark component in `5̄`. -/
def downAntiquarkBlueState : SMWeylFermion := .fiveBar 2

/-- The left-handed red up-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftUpQuarkRedState : SMWeylFermion := .ten ⟨(0, 3), by decide⟩

/-- The left-handed green up-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftUpQuarkGreenState : SMWeylFermion := .ten ⟨(1, 3), by decide⟩

/-- The left-handed blue up-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftUpQuarkBlueState : SMWeylFermion := .ten ⟨(2, 3), by decide⟩

/-- The left-handed red down-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftDownQuarkRedState : SMWeylFermion := .ten ⟨(0, 4), by decide⟩

/-- The left-handed green down-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftDownQuarkGreenState : SMWeylFermion := .ten ⟨(1, 4), by decide⟩

/-- The left-handed blue down-quark component, generated by a colour/weak wedge in `Λ²(5)`. -/
def leftDownQuarkBlueState : SMWeylFermion := .ten ⟨(2, 4), by decide⟩

/-- The red up-antiquark component `u^c_r`; the complementary colour-colour wedge is the
anti-triplet basis. -/
def upAntiquarkRedState : SMWeylFermion := .ten ⟨(1, 2), by decide⟩

/-- The green up-antiquark component `u^c_g`; the complementary colour-colour wedge is the
anti-triplet basis. -/
def upAntiquarkGreenState : SMWeylFermion := .ten ⟨(0, 2), by decide⟩

/-- The blue up-antiquark component `u^c_b`; the complementary colour-colour wedge is the
anti-triplet basis. -/
def upAntiquarkBlueState : SMWeylFermion := .ten ⟨(0, 1), by decide⟩

/-- The left-handed charged antilepton `e^c` / positron state in `Λ²(5)`. -/
def leftPositronState : SMWeylFermion := .ten ⟨(3, 4), by decide⟩

/-- The generated electron has `(Q,T₃,Y,B,L,s) = (-1,-1/2,-1,0,1,1/2)`. -/
lemma leftElectron_hasQuantumNumbers :
    HasComputedQuantumNumbers leftElectronState (-1) (-1 / 2) (-1) 0 1 (1 / 2)
      .singlet .doublet .left := by
  native_decide

/-- The generated electron neutrino has `(Q,T₃,Y,B,L,s) = (0,1/2,-1,0,1,1/2)`. -/
lemma leftElectronNeutrino_hasQuantumNumbers :
    HasComputedQuantumNumbers leftElectronNeutrinoState 0 (1 / 2) (-1) 0 1 (1 / 2)
      .singlet .doublet .left := by
  native_decide

/-- The red down antiquark has `(Q,T₃,Y,B,L,s) = (1/3,0,2/3,-1/3,0,1/2)`. -/
lemma downAntiquarkRed_hasQuantumNumbers :
    HasComputedQuantumNumbers downAntiquarkRedState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The green down antiquark has `(Q,T₃,Y,B,L,s) = (1/3,0,2/3,-1/3,0,1/2)`. -/
lemma downAntiquarkGreen_hasQuantumNumbers :
    HasComputedQuantumNumbers downAntiquarkGreenState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The blue down antiquark has `(Q,T₃,Y,B,L,s) = (1/3,0,2/3,-1/3,0,1/2)`. -/
lemma downAntiquarkBlue_hasQuantumNumbers :
    HasComputedQuantumNumbers downAntiquarkBlueState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The red up quark has `(Q,T₃,Y,B,L,s) = (2/3,1/2,1/3,1/3,0,1/2)`. -/
lemma leftUpQuarkRed_hasQuantumNumbers :
    HasComputedQuantumNumbers leftUpQuarkRedState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The green up quark has `(Q,T₃,Y,B,L,s) = (2/3,1/2,1/3,1/3,0,1/2)`. -/
lemma leftUpQuarkGreen_hasQuantumNumbers :
    HasComputedQuantumNumbers leftUpQuarkGreenState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The blue up quark has `(Q,T₃,Y,B,L,s) = (2/3,1/2,1/3,1/3,0,1/2)`. -/
lemma leftUpQuarkBlue_hasQuantumNumbers :
    HasComputedQuantumNumbers leftUpQuarkBlueState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The red down quark has `(Q,T₃,Y,B,L,s) = (-1/3,-1/2,1/3,1/3,0,1/2)`. -/
lemma leftDownQuarkRed_hasQuantumNumbers :
    HasComputedQuantumNumbers leftDownQuarkRedState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The green down quark has `(Q,T₃,Y,B,L,s) = (-1/3,-1/2,1/3,1/3,0,1/2)`. -/
lemma leftDownQuarkGreen_hasQuantumNumbers :
    HasComputedQuantumNumbers leftDownQuarkGreenState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The blue down quark has `(Q,T₃,Y,B,L,s) = (-1/3,-1/2,1/3,1/3,0,1/2)`. -/
lemma leftDownQuarkBlue_hasQuantumNumbers :
    HasComputedQuantumNumbers leftDownQuarkBlueState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left := by
  native_decide

/-- The red up antiquark has `(Q,T₃,Y,B,L,s) = (-2/3,0,-4/3,-1/3,0,1/2)`. -/
lemma upAntiquarkRed_hasQuantumNumbers :
    HasComputedQuantumNumbers upAntiquarkRedState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The green up antiquark has `(Q,T₃,Y,B,L,s) = (-2/3,0,-4/3,-1/3,0,1/2)`. -/
lemma upAntiquarkGreen_hasQuantumNumbers :
    HasComputedQuantumNumbers upAntiquarkGreenState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The blue up antiquark has `(Q,T₃,Y,B,L,s) = (-2/3,0,-4/3,-1/3,0,1/2)`. -/
lemma upAntiquarkBlue_hasQuantumNumbers :
    HasComputedQuantumNumbers upAntiquarkBlueState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left := by
  native_decide

/-- The generated `e^c` / positron has `(Q,T₃,Y,B,L,s) = (1,0,2,0,-1,1/2)`. -/
lemma leftPositron_hasQuantumNumbers :
    HasComputedQuantumNumbers leftPositronState 1 0 2 0 (-1) (1 / 2)
      .singlet .singlet .left := by
  native_decide

/-- All named first-generation fermion components are checked from the generated `SU(5)` state
space. -/
def HasNamedFirstGenerationFermionComputations : Prop :=
  HasComputedQuantumNumbers leftElectronState (-1) (-1 / 2) (-1) 0 1 (1 / 2)
      .singlet .doublet .left
    ∧ HasComputedQuantumNumbers leftElectronNeutrinoState 0 (1 / 2) (-1) 0 1 (1 / 2)
      .singlet .doublet .left
    ∧ HasComputedQuantumNumbers downAntiquarkRedState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers downAntiquarkGreenState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers downAntiquarkBlueState (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers leftUpQuarkRedState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers leftUpQuarkGreenState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers leftUpQuarkBlueState (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers leftDownQuarkRedState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers leftDownQuarkGreenState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers leftDownQuarkBlueState (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2)
      .triplet .doublet .left
    ∧ HasComputedQuantumNumbers upAntiquarkRedState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers upAntiquarkGreenState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers upAntiquarkBlueState (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2)
      .antiTriplet .singlet .left
    ∧ HasComputedQuantumNumbers leftPositronState 1 0 2 0 (-1) (1 / 2)
      .singlet .singlet .left

instance decidableHasNamedFirstGenerationFermionComputations :
    Decidable HasNamedFirstGenerationFermionComputations := by
  unfold HasNamedFirstGenerationFermionComputations
  infer_instance

/-- The named first-generation fermion computations all follow by reducing the generated `SU(5)`
state definitions. -/
lemma namedFirstGenerationFermionComputations_checked :
    HasNamedFirstGenerationFermionComputations := by
  native_decide


set_option backward.isDefEq.respectTransparency false in
/-- The three Standard-Model fermion generations.  This is a flavor label; the gauge quantum
numbers are still computed from the `SMWeylFermion` component. -/
inductive FermionGeneration where
  | first
  | second
  | third
  deriving DecidableEq, Fintype, Repr

set_option backward.isDefEq.respectTransparency false in
/-- Colour labels for the three components of a colour triplet or anti-triplet. -/
inductive QCDColour where
  | red
  | green
  | blue
  deriving DecidableEq, Fintype, Repr

set_option backward.isDefEq.respectTransparency false in
/-- Charged lepton flavor labels. -/
inductive ChargedLeptonFlavor where
  | electron
  | muon
  | tau
  deriving DecidableEq, Fintype, Repr

set_option backward.isDefEq.respectTransparency false in
/-- Neutrino flavor labels for the left-handed weak doublets. -/
inductive NeutrinoFlavor where
  | electron
  | muon
  | tau
  deriving DecidableEq, Fintype, Repr

set_option backward.isDefEq.respectTransparency false in
/-- Up-type quark flavor labels. -/
inductive UpTypeQuarkFlavor where
  | up
  | charm
  | top
  deriving DecidableEq, Fintype, Repr

set_option backward.isDefEq.respectTransparency false in
/-- Down-type quark flavor labels. -/
inductive DownTypeQuarkFlavor where
  | down
  | strange
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- The generation associated to a charged lepton flavor. -/
def chargedLeptonGeneration : ChargedLeptonFlavor → FermionGeneration
  | .electron => .first
  | .muon => .second
  | .tau => .third

/-- The generation associated to a neutrino flavor. -/
def neutrinoGeneration : NeutrinoFlavor → FermionGeneration
  | .electron => .first
  | .muon => .second
  | .tau => .third

/-- The generation associated to an up-type quark flavor. -/
def upTypeQuarkGeneration : UpTypeQuarkFlavor → FermionGeneration
  | .up => .first
  | .charm => .second
  | .top => .third

/-- The generation associated to a down-type quark flavor. -/
def downTypeQuarkGeneration : DownTypeQuarkFlavor → FermionGeneration
  | .down => .first
  | .strange => .second
  | .bottom => .third

/-- A three-generation Weyl fermion is a generation label paired with the generated one-generation
`SU(5)` state. -/
abbrev ThreeGenerationWeylFermion := FermionGeneration × SMWeylFermion

/-- The quantum numbers of a three-generation Weyl fermion ignore the generation label and are
computed from the generated `SU(5)` state. -/
def threeGenerationQuantumNumbers (f : ThreeGenerationWeylFermion) : FermionQuantumNumbers :=
  fermionQuantumNumbers f.2

/-- Generation labels do not alter electric charge, so all 45 active
three-generation Weyl states remain on the `e/3` charge lattice. -/
lemma threeGenerationElectricCharge_thirdQuantized
    (f : ThreeGenerationWeylFermion) :
    IsThirdQuantizedCharge (threeGenerationQuantumNumbers f).electricCharge := by
  simpa [threeGenerationQuantumNumbers, fermionQuantumNumbers]
    using fermionElectricCharge_thirdQuantized f.2

/-- Compact proposition for the computed quantum numbers of a generation-labelled fermion. -/
def HasThreeGenerationComputedQuantumNumbers (f : ThreeGenerationWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) : Prop :=
  (threeGenerationQuantumNumbers f).electricCharge = electric
    ∧ (threeGenerationQuantumNumbers f).weakIsospin3 = weakIsospin3
    ∧ (threeGenerationQuantumNumbers f).hypercharge = hypercharge
    ∧ (threeGenerationQuantumNumbers f).baryonNumber = baryon
    ∧ (threeGenerationQuantumNumbers f).leptonNumber = lepton
    ∧ (threeGenerationQuantumNumbers f).spin = spin
    ∧ (threeGenerationQuantumNumbers f).colour = colour
    ∧ (threeGenerationQuantumNumbers f).weak = weak
    ∧ (threeGenerationQuantumNumbers f).chirality = chirality

instance decidableHasThreeGenerationComputedQuantumNumbers (f : ThreeGenerationWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) :
    Decidable
      (HasThreeGenerationComputedQuantumNumbers f electric weakIsospin3 hypercharge baryon lepton
        spin colour weak chirality) := by
  unfold HasThreeGenerationComputedQuantumNumbers threeGenerationQuantumNumbers
  infer_instance

/-- The generated three-generation state count: three copies of `5̄ ⊕ Λ²(5)`. -/
lemma threeGenerationWeylFermion_state_count :
    Fintype.card ThreeGenerationWeylFermion = 45 := by
  native_decide

/-- Map a colour label to the `SU(5)` colour-block index. -/
def qcdColourIndex : QCDColour → Fin 5
  | .red => 0
  | .green => 1
  | .blue => 2

/-- The generated left-handed charged lepton of a given flavor. -/
def chargedLeptonParticle (flavor : ChargedLeptonFlavor) : ThreeGenerationWeylFermion :=
  (chargedLeptonGeneration flavor, leftElectronState)

/-- The generated left-handed neutrino of a given flavor. -/
def neutrinoParticle (flavor : NeutrinoFlavor) : ThreeGenerationWeylFermion :=
  (neutrinoGeneration flavor, leftElectronNeutrinoState)

/-- The generated left-handed charged antilepton `ℓ^c` of a given flavor. -/
def chargedAntileptonParticle (flavor : ChargedLeptonFlavor) : ThreeGenerationWeylFermion :=
  (chargedLeptonGeneration flavor, leftPositronState)

/-- The generated down-type antiquark of a given flavor and anti-colour component. -/
def downTypeAntiquarkParticle (flavor : DownTypeQuarkFlavor) (colour : QCDColour) :
    ThreeGenerationWeylFermion :=
  (downTypeQuarkGeneration flavor, .fiveBar (qcdColourIndex colour))

/-- The generated left-handed up-type quark of a given flavor and colour component. -/
def upTypeQuarkParticle (flavor : UpTypeQuarkFlavor) (colour : QCDColour) :
    ThreeGenerationWeylFermion :=
  (upTypeQuarkGeneration flavor, .ten ⟨(qcdColourIndex colour, 3), by
    cases colour <;> decide⟩)

/-- The generated left-handed down-type quark of a given flavor and colour component. -/
def downTypeQuarkParticle (flavor : DownTypeQuarkFlavor) (colour : QCDColour) :
    ThreeGenerationWeylFermion :=
  (downTypeQuarkGeneration flavor, .ten ⟨(qcdColourIndex colour, 4), by
    cases colour <;> decide⟩)

/-- The generated up-type antiquark of a given flavor and anti-colour component. -/
def upTypeAntiquarkParticle (flavor : UpTypeQuarkFlavor) (colour : QCDColour) :
    ThreeGenerationWeylFermion :=
  (upTypeQuarkGeneration flavor,
    match colour with
    | .red => .ten ⟨(1, 2), by decide⟩
    | .green => .ten ⟨(0, 2), by decide⟩
    | .blue => .ten ⟨(0, 1), by decide⟩)

/-- Named electron state. -/
def electronParticle : ThreeGenerationWeylFermion := chargedLeptonParticle .electron

/-- Named muon state. -/
def muonParticle : ThreeGenerationWeylFermion := chargedLeptonParticle .muon

/-- Named tau state. -/
def tauParticle : ThreeGenerationWeylFermion := chargedLeptonParticle .tau

/-- Named electron-neutrino state. -/
def electronNeutrinoParticle : ThreeGenerationWeylFermion := neutrinoParticle .electron

/-- Named muon-neutrino state. -/
def muonNeutrinoParticle : ThreeGenerationWeylFermion := neutrinoParticle .muon

/-- Named tau-neutrino state. -/
def tauNeutrinoParticle : ThreeGenerationWeylFermion := neutrinoParticle .tau

/-- Named positron state, i.e. the `e^c` Weyl field. -/
def positronParticle : ThreeGenerationWeylFermion := chargedAntileptonParticle .electron

/-- Named antimuon state, i.e. the `μ^c` Weyl field. -/
def antiMuonParticle : ThreeGenerationWeylFermion := chargedAntileptonParticle .muon

/-- Named antitau state, i.e. the `τ^c` Weyl field. -/
def antiTauParticle : ThreeGenerationWeylFermion := chargedAntileptonParticle .tau

/-- Named up-quark state for a given colour. -/
def upQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeQuarkParticle .up colour

/-- Named charm-quark state for a given colour. -/
def charmQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeQuarkParticle .charm colour

/-- Named top-quark state for a given colour. -/
def topQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeQuarkParticle .top colour

/-- Named down-quark state for a given colour. -/
def downQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeQuarkParticle .down colour

/-- Named strange-quark state for a given colour. -/
def strangeQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeQuarkParticle .strange colour

/-- Named bottom-quark state for a given colour. -/
def bottomQuarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeQuarkParticle .bottom colour

/-- Named up-antiquark state for a given anti-colour. -/
def upAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeAntiquarkParticle .up colour

/-- Named charm-antiquark state for a given anti-colour. -/
def charmAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeAntiquarkParticle .charm colour

/-- Named top-antiquark state for a given anti-colour. -/
def topAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  upTypeAntiquarkParticle .top colour

/-- Named down-antiquark state for a given anti-colour. -/
def downAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeAntiquarkParticle .down colour

/-- Named strange-antiquark state for a given anti-colour. -/
def strangeAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeAntiquarkParticle .strange colour

/-- Named bottom-antiquark state for a given anti-colour. -/
def bottomAntiquarkParticle (colour : QCDColour) : ThreeGenerationWeylFermion :=
  downTypeAntiquarkParticle .bottom colour

/-- Every charged lepton flavor has the generated charged-lepton quantum numbers. -/
lemma chargedLeptonParticle_hasQuantumNumbers (flavor : ChargedLeptonFlavor) :
    HasThreeGenerationComputedQuantumNumbers (chargedLeptonParticle flavor)
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left := by
  cases flavor <;> native_decide

/-- Every neutrino flavor in the left-handed weak doublet has the generated neutrino quantum
numbers. -/
lemma neutrinoParticle_hasQuantumNumbers (flavor : NeutrinoFlavor) :
    HasThreeGenerationComputedQuantumNumbers (neutrinoParticle flavor)
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left := by
  cases flavor <;> native_decide

/-- Every charged antilepton flavor has the generated `ℓ^c` quantum numbers. -/
lemma chargedAntileptonParticle_hasQuantumNumbers (flavor : ChargedLeptonFlavor) :
    HasThreeGenerationComputedQuantumNumbers (chargedAntileptonParticle flavor)
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left := by
  cases flavor <;> native_decide

/-- Every up-type quark flavor and colour has the generated up-type quark quantum numbers. -/
lemma upTypeQuarkParticle_hasQuantumNumbers (flavor : UpTypeQuarkFlavor) (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (upTypeQuarkParticle flavor colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left := by
  cases flavor <;> cases colour <;> native_decide

/-- Every down-type quark flavor and colour has the generated down-type quark quantum numbers. -/
lemma downTypeQuarkParticle_hasQuantumNumbers
    (flavor : DownTypeQuarkFlavor) (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (downTypeQuarkParticle flavor colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left := by
  cases flavor <;> cases colour <;> native_decide

/-- Every up-type antiquark flavor and anti-colour has the generated up-antiquark quantum
numbers. -/
lemma upTypeAntiquarkParticle_hasQuantumNumbers
    (flavor : UpTypeQuarkFlavor) (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (upTypeAntiquarkParticle flavor colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left := by
  cases flavor <;> cases colour <;> native_decide

/-- Every down-type antiquark flavor and anti-colour has the generated down-antiquark quantum
numbers. -/
lemma downTypeAntiquarkParticle_hasQuantumNumbers
    (flavor : DownTypeQuarkFlavor) (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (downTypeAntiquarkParticle flavor colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left := by
  cases flavor <;> cases colour <;> native_decide

/-! ### Specific named fermion particles -/

/-- The named electron state has the computed charged-lepton quantum numbers. -/
lemma electronParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers electronParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  chargedLeptonParticle_hasQuantumNumbers .electron

/-- The named muon state has the computed charged-lepton quantum numbers. -/
lemma muonParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers muonParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  chargedLeptonParticle_hasQuantumNumbers .muon

/-- The named tau state has the computed charged-lepton quantum numbers. -/
lemma tauParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers tauParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  chargedLeptonParticle_hasQuantumNumbers .tau

/-- The named electron-neutrino state has the computed active-neutrino quantum numbers. -/
lemma electronNeutrinoParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers electronNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  neutrinoParticle_hasQuantumNumbers .electron

/-- The named muon-neutrino state has the computed active-neutrino quantum numbers. -/
lemma muonNeutrinoParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers muonNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  neutrinoParticle_hasQuantumNumbers .muon

/-- The named tau-neutrino state has the computed active-neutrino quantum numbers. -/
lemma tauNeutrinoParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers tauNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left :=
  neutrinoParticle_hasQuantumNumbers .tau

/-- The named positron Weyl state has the computed charged-antilepton quantum numbers. -/
lemma positronParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers positronParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left :=
  chargedAntileptonParticle_hasQuantumNumbers .electron

/-- The named antimuon Weyl state has the computed charged-antilepton quantum numbers. -/
lemma antiMuonParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers antiMuonParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left :=
  chargedAntileptonParticle_hasQuantumNumbers .muon

/-- The named antitau Weyl state has the computed charged-antilepton quantum numbers. -/
lemma antiTauParticle_hasQuantumNumbers :
    HasThreeGenerationComputedQuantumNumbers antiTauParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left :=
  chargedAntileptonParticle_hasQuantumNumbers .tau

/-- The named up quark has the computed up-type quark quantum numbers in every colour. -/
lemma upQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (upQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  upTypeQuarkParticle_hasQuantumNumbers .up colour

/-- The named charm quark has the computed up-type quark quantum numbers in every colour. -/
lemma charmQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (charmQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  upTypeQuarkParticle_hasQuantumNumbers .charm colour

/-- The named top quark has the computed up-type quark quantum numbers in every colour. -/
lemma topQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (topQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  upTypeQuarkParticle_hasQuantumNumbers .top colour

/-- The named down quark has the computed down-type quark quantum numbers in every colour. -/
lemma downQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (downQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  downTypeQuarkParticle_hasQuantumNumbers .down colour

/-- The named strange quark has the computed down-type quark quantum numbers in every colour. -/
lemma strangeQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (strangeQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  downTypeQuarkParticle_hasQuantumNumbers .strange colour

/-- The named bottom quark has the computed down-type quark quantum numbers in every colour. -/
lemma bottomQuarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (bottomQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left :=
  downTypeQuarkParticle_hasQuantumNumbers .bottom colour

/-- The named up antiquark has the computed up-antiquark quantum numbers in every anti-colour. -/
lemma upAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (upAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  upTypeAntiquarkParticle_hasQuantumNumbers .up colour

/-- The named charm antiquark has the computed up-antiquark quantum numbers in every anti-colour. -/
lemma charmAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (charmAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  upTypeAntiquarkParticle_hasQuantumNumbers .charm colour

/-- The named top antiquark has the computed up-antiquark quantum numbers in every anti-colour. -/
lemma topAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (topAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  upTypeAntiquarkParticle_hasQuantumNumbers .top colour

/-- The named down antiquark has the computed down-antiquark quantum numbers in every anti-colour. -/
lemma downAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (downAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  downTypeAntiquarkParticle_hasQuantumNumbers .down colour

/-- The named strange antiquark has the computed down-antiquark quantum numbers in every anti-colour. -/
lemma strangeAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (strangeAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  downTypeAntiquarkParticle_hasQuantumNumbers .strange colour

/-- The named bottom antiquark has the computed down-antiquark quantum numbers in every anti-colour. -/
lemma bottomAntiquarkParticle_hasQuantumNumbers (colour : QCDColour) :
    HasThreeGenerationComputedQuantumNumbers (bottomAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left :=
  downTypeAntiquarkParticle_hasQuantumNumbers .bottom colour

/-- Direct named-particle accessors for the full three-generation Standard-Model fermion list. -/
def HasNamedPhysicalFermionParticleComputations : Prop :=
  HasThreeGenerationComputedQuantumNumbers electronParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers muonParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers tauParticle
      (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers electronNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers muonNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers tauNeutrinoParticle
      0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left
    ∧ HasThreeGenerationComputedQuantumNumbers positronParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left
    ∧ HasThreeGenerationComputedQuantumNumbers antiMuonParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left
    ∧ HasThreeGenerationComputedQuantumNumbers antiTauParticle
      1 0 2 0 (-1) (1 / 2) .singlet .singlet .left
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (upQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (charmQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (topQuarkParticle colour)
      (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (downQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (strangeQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (bottomQuarkParticle colour)
      (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (upAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (charmAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (topAntiquarkParticle colour)
      (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (downAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (strangeAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ colour : QCDColour, HasThreeGenerationComputedQuantumNumbers (bottomAntiquarkParticle colour)
      (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)

instance decidableHasNamedPhysicalFermionParticleComputations :
    Decidable HasNamedPhysicalFermionParticleComputations := by
  unfold HasNamedPhysicalFermionParticleComputations
  infer_instance

lemma namedPhysicalFermionParticleComputations_checked :
    HasNamedPhysicalFermionParticleComputations :=
  ⟨electronParticle_hasQuantumNumbers,
    muonParticle_hasQuantumNumbers,
    tauParticle_hasQuantumNumbers,
    electronNeutrinoParticle_hasQuantumNumbers,
    muonNeutrinoParticle_hasQuantumNumbers,
    tauNeutrinoParticle_hasQuantumNumbers,
    positronParticle_hasQuantumNumbers,
    antiMuonParticle_hasQuantumNumbers,
    antiTauParticle_hasQuantumNumbers,
    upQuarkParticle_hasQuantumNumbers,
    charmQuarkParticle_hasQuantumNumbers,
    topQuarkParticle_hasQuantumNumbers,
    downQuarkParticle_hasQuantumNumbers,
    strangeQuarkParticle_hasQuantumNumbers,
    bottomQuarkParticle_hasQuantumNumbers,
    upAntiquarkParticle_hasQuantumNumbers,
    charmAntiquarkParticle_hasQuantumNumbers,
    topAntiquarkParticle_hasQuantumNumbers,
    downAntiquarkParticle_hasQuantumNumbers,
    strangeAntiquarkParticle_hasQuantumNumbers,
    bottomAntiquarkParticle_hasQuantumNumbers⟩

/-- The three-generation electric-charge trace: three copies of the generated generation. -/
def threeGenerationElectricChargeTrace : ℚ :=
  ∑ f : ThreeGenerationWeylFermion, (threeGenerationQuantumNumbers f).electricCharge

/-- The three-generation hypercharge trace. -/
def threeGenerationHyperchargeTrace : ℚ :=
  ∑ f : ThreeGenerationWeylFermion, (threeGenerationQuantumNumbers f).hypercharge

/-- The three-generation cubic hypercharge trace. -/
def threeGenerationCubicHyperchargeTrace : ℚ :=
  ∑ f : ThreeGenerationWeylFermion, (threeGenerationQuantumNumbers f).hypercharge ^ 3

/-- Three generated generations remain electrically neutral. -/
lemma threeGenerationElectricChargeTrace_zero :
    threeGenerationElectricChargeTrace = 0 := by
  native_decide

/-- Three generated generations have vanishing `Tr Y`. -/
lemma threeGenerationHyperchargeTrace_zero :
    threeGenerationHyperchargeTrace = 0 := by
  native_decide

/-- Three generated generations have vanishing `Tr Y^3`. -/
lemma threeGenerationCubicHyperchargeTrace_zero :
    threeGenerationCubicHyperchargeTrace = 0 := by
  native_decide

/-- The complete flavor-labelled Standard-Model fermion quantum-number computation currently
available from the generated `SU(5)` state space. -/
def HasNamedThreeGenerationFermionComputations : Prop :=
  Fintype.card ThreeGenerationWeylFermion = 45
    ∧ (∀ flavor : ChargedLeptonFlavor,
      HasThreeGenerationComputedQuantumNumbers (chargedLeptonParticle flavor)
        (-1) (-1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left)
    ∧ (∀ flavor : NeutrinoFlavor,
      HasThreeGenerationComputedQuantumNumbers (neutrinoParticle flavor)
        0 (1 / 2) (-1) 0 1 (1 / 2) .singlet .doublet .left)
    ∧ (∀ flavor : ChargedLeptonFlavor,
      HasThreeGenerationComputedQuantumNumbers (chargedAntileptonParticle flavor)
        1 0 2 0 (-1) (1 / 2) .singlet .singlet .left)
    ∧ (∀ (flavor : UpTypeQuarkFlavor) (colour : QCDColour),
      HasThreeGenerationComputedQuantumNumbers (upTypeQuarkParticle flavor colour)
        (2 / 3) (1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ (flavor : DownTypeQuarkFlavor) (colour : QCDColour),
      HasThreeGenerationComputedQuantumNumbers (downTypeQuarkParticle flavor colour)
        (-1 / 3) (-1 / 2) (1 / 3) (1 / 3) 0 (1 / 2) .triplet .doublet .left)
    ∧ (∀ (flavor : UpTypeQuarkFlavor) (colour : QCDColour),
      HasThreeGenerationComputedQuantumNumbers (upTypeAntiquarkParticle flavor colour)
        (-2 / 3) 0 (-4 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ (∀ (flavor : DownTypeQuarkFlavor) (colour : QCDColour),
      HasThreeGenerationComputedQuantumNumbers (downTypeAntiquarkParticle flavor colour)
        (1 / 3) 0 (2 / 3) (-1 / 3) 0 (1 / 2) .antiTriplet .singlet .left)
    ∧ HasNamedPhysicalFermionParticleComputations
    ∧ threeGenerationElectricChargeTrace = 0
    ∧ threeGenerationHyperchargeTrace = 0
    ∧ threeGenerationCubicHyperchargeTrace = 0

instance decidableHasNamedThreeGenerationFermionComputations :
    Decidable HasNamedThreeGenerationFermionComputations := by
  unfold HasNamedThreeGenerationFermionComputations
  infer_instance

/-- The named three-generation fermion quantum numbers are computed by generation-labelled copies
of the generated `5̄ ⊕ Λ²(5)` state space. -/
lemma namedThreeGenerationFermionComputations_checked :
    HasNamedThreeGenerationFermionComputations := by
  exact ⟨threeGenerationWeylFermion_state_count,
    chargedLeptonParticle_hasQuantumNumbers,
    neutrinoParticle_hasQuantumNumbers,
    chargedAntileptonParticle_hasQuantumNumbers,
    upTypeQuarkParticle_hasQuantumNumbers,
    downTypeQuarkParticle_hasQuantumNumbers,
    upTypeAntiquarkParticle_hasQuantumNumbers,
    downTypeAntiquarkParticle_hasQuantumNumbers,
    namedPhysicalFermionParticleComputations_checked,
    threeGenerationElectricChargeTrace_zero,
    threeGenerationHyperchargeTrace_zero,
    threeGenerationCubicHyperchargeTrace_zero⟩


/-- A right-handed neutrino `ν_R` is a generation-labelled Standard-Model gauge singlet.  It is not
part of the minimal `SU(5)` `5̄ ⊕ Λ²(5)` representation; it is the optional singlet extension
used, for example, in Dirac-neutrino or `SO(10)`-style completions. -/
abbrev RightHandedNeutrino := NeutrinoFlavor

/-- The generation label carried by a right-handed neutrino. -/
def rightHandedNeutrinoGeneration : RightHandedNeutrino → FermionGeneration :=
  neutrinoGeneration

/-- The family-number triple of a right-handed neutrino, reusing the existing lepton-flavor
bookkeeping. -/
def rightHandedNeutrinoLeptonFlavor :
    RightHandedNeutrino →
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.LeptonFlavor
  | .electron => Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.eNeutrino
  | .muon => Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muNeutrino
  | .tau => Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tauNeutrino

/-- Every right-handed neutrino has total lepton number `+1` in the existing family-number model. -/
lemma rightHandedNeutrinoLeptonFlavor_total (νR : RightHandedNeutrino) :
    Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total
      (rightHandedNeutrinoLeptonFlavor νR) = 1 := by
  cases νR <;>
    simp [rightHandedNeutrinoLeptonFlavor,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.eNeutrino,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muNeutrino,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.tauNeutrino]

/-- The total additive `(Q,B,L)` quantum numbers of a right-handed neutrino. -/
def rightHandedNeutrinoAdditiveQuantumNumbers (_νR : RightHandedNeutrino) :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers :=
  ⟨0, 0, 1⟩

/-- The additive quantum-number triple is neutral in charge and baryon number and has lepton number
`+1`, matching the existing total-lepton-number neutrino triple. -/
lemma rightHandedNeutrinoAdditiveQuantumNumbers_eq_totalNeutrino
    (νR : RightHandedNeutrino) :
    rightHandedNeutrinoAdditiveQuantumNumbers νR =
      Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.muonNeutrino := by
  rfl

/-- The computed quantum numbers of a right-handed sterile neutrino: all Standard-Model gauge
charges vanish, it is a colour and weak singlet, and it has right chirality. -/
def rightHandedNeutrinoQuantumNumbers (_νR : RightHandedNeutrino) : FermionQuantumNumbers where
  electricCharge := 0
  weakIsospin3 := 0
  hypercharge := 0
  baryonNumber := 0
  leptonNumber := 1
  spin := 1 / 2
  colour := .singlet
  weak := .singlet
  chirality := .right

/-- Compact proposition for the computed quantum numbers of a sterile right-handed neutrino. -/
def HasRightHandedNeutrinoQuantumNumbers (νR : RightHandedNeutrino)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) : Prop :=
  (rightHandedNeutrinoQuantumNumbers νR).electricCharge = electric
    ∧ (rightHandedNeutrinoQuantumNumbers νR).weakIsospin3 = weakIsospin3
    ∧ (rightHandedNeutrinoQuantumNumbers νR).hypercharge = hypercharge
    ∧ (rightHandedNeutrinoQuantumNumbers νR).baryonNumber = baryon
    ∧ (rightHandedNeutrinoQuantumNumbers νR).leptonNumber = lepton
    ∧ (rightHandedNeutrinoQuantumNumbers νR).spin = spin
    ∧ (rightHandedNeutrinoQuantumNumbers νR).colour = colour
    ∧ (rightHandedNeutrinoQuantumNumbers νR).weak = weak
    ∧ (rightHandedNeutrinoQuantumNumbers νR).chirality = chirality

instance decidableHasRightHandedNeutrinoQuantumNumbers (νR : RightHandedNeutrino)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) :
    Decidable
      (HasRightHandedNeutrinoQuantumNumbers νR electric weakIsospin3 hypercharge baryon lepton spin
        colour weak chirality) := by
  unfold HasRightHandedNeutrinoQuantumNumbers rightHandedNeutrinoQuantumNumbers
  infer_instance

/-- Every sterile right-handed neutrino flavor has the same gauge-singlet quantum numbers. -/
lemma rightHandedNeutrino_hasQuantumNumbers (νR : RightHandedNeutrino) :
    HasRightHandedNeutrinoQuantumNumbers νR 0 0 0 0 1 (1 / 2)
      .singlet .singlet .right := by
  cases νR <;> native_decide

/-- The sterile neutrino is electrically neutral by Gell-Mann--Nishijima with `T₃ = Y = 0`. -/
lemma rightHandedNeutrino_charge_eq_gmn (νR : RightHandedNeutrino) :
    (rightHandedNeutrinoQuantumNumbers νR).electricCharge =
      gellMannNishijima (rightHandedNeutrinoQuantumNumbers νR).weakIsospin3
        (rightHandedNeutrinoQuantumNumbers νR).hypercharge := by
  simp [rightHandedNeutrinoQuantumNumbers, gellMannNishijima]

/-- The electron-flavor right-handed sterile neutrino state. -/
def rightHandedElectronNeutrinoState : RightHandedNeutrino := .electron

/-- The muon-flavor right-handed sterile neutrino state. -/
def rightHandedMuonNeutrinoState : RightHandedNeutrino := .muon

/-- The tau-flavor right-handed sterile neutrino state. -/
def rightHandedTauNeutrinoState : RightHandedNeutrino := .tau

set_option backward.isDefEq.respectTransparency false in
/-- The generated `45` Weyl states plus three sterile right-handed neutrino singlets. -/
inductive ExtendedStandardModelWeylFermion where
  | active (f : ThreeGenerationWeylFermion)
  | sterileNeutrino (νR : RightHandedNeutrino)
  deriving DecidableEq, Fintype

/-- Quantum numbers for the active `45` states and the three sterile `ν_R` singlets. -/
def extendedStandardModelQuantumNumbers :
    ExtendedStandardModelWeylFermion → FermionQuantumNumbers
  | .active f => threeGenerationQuantumNumbers f
  | .sterileNeutrino νR => rightHandedNeutrinoQuantumNumbers νR

/-- Compact proposition for the extended state space. -/
def HasExtendedStandardModelComputedQuantumNumbers (f : ExtendedStandardModelWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) : Prop :=
  (extendedStandardModelQuantumNumbers f).electricCharge = electric
    ∧ (extendedStandardModelQuantumNumbers f).weakIsospin3 = weakIsospin3
    ∧ (extendedStandardModelQuantumNumbers f).hypercharge = hypercharge
    ∧ (extendedStandardModelQuantumNumbers f).baryonNumber = baryon
    ∧ (extendedStandardModelQuantumNumbers f).leptonNumber = lepton
    ∧ (extendedStandardModelQuantumNumbers f).spin = spin
    ∧ (extendedStandardModelQuantumNumbers f).colour = colour
    ∧ (extendedStandardModelQuantumNumbers f).weak = weak
    ∧ (extendedStandardModelQuantumNumbers f).chirality = chirality

instance decidableHasExtendedStandardModelComputedQuantumNumbers (f : ExtendedStandardModelWeylFermion)
    (electric weakIsospin3 hypercharge baryon lepton spin : ℚ)
    (colour : ColourRepresentation) (weak : WeakRepresentation)
    (chirality : WeylChirality) :
    Decidable
      (HasExtendedStandardModelComputedQuantumNumbers f electric weakIsospin3 hypercharge baryon
        lepton spin colour weak chirality) := by
  unfold HasExtendedStandardModelComputedQuantumNumbers extendedStandardModelQuantumNumbers
  infer_instance

/-- The extended state count: `45` active Standard-Model Weyl states plus three sterile singlets. -/
lemma extendedStandardModelWeylFermion_state_count :
    Fintype.card ExtendedStandardModelWeylFermion = 48 := by
  native_decide

/-- The right-handed electron-neutrino singlet inside the extended state space. -/
def rightHandedElectronNeutrinoExtendedState : ExtendedStandardModelWeylFermion :=
  .sterileNeutrino rightHandedElectronNeutrinoState

/-- The right-handed muon-neutrino singlet inside the extended state space. -/
def rightHandedMuonNeutrinoExtendedState : ExtendedStandardModelWeylFermion :=
  .sterileNeutrino rightHandedMuonNeutrinoState

/-- The right-handed tau-neutrino singlet inside the extended state space. -/
def rightHandedTauNeutrinoExtendedState : ExtendedStandardModelWeylFermion :=
  .sterileNeutrino rightHandedTauNeutrinoState

/-- Embed any active three-generation fermion into the extended `45 + 3` state space. -/
def activeExtendedParticle (f : ThreeGenerationWeylFermion) : ExtendedStandardModelWeylFermion :=
  .active f

/-- Computed quantum numbers are preserved by embedding an active fermion into the extended state
space. -/
lemma activeExtendedParticle_hasQuantumNumbers
    {f : ThreeGenerationWeylFermion}
    {electric weakIsospin3 hypercharge baryon lepton spin : ℚ}
    {colour : ColourRepresentation} {weak : WeakRepresentation}
    {chirality : WeylChirality}
    (h : HasThreeGenerationComputedQuantumNumbers f electric weakIsospin3 hypercharge baryon lepton
      spin colour weak chirality) :
    HasExtendedStandardModelComputedQuantumNumbers (activeExtendedParticle f)
      electric weakIsospin3 hypercharge baryon lepton spin colour weak chirality := by
  simpa [activeExtendedParticle, HasExtendedStandardModelComputedQuantumNumbers,
    extendedStandardModelQuantumNumbers, HasThreeGenerationComputedQuantumNumbers,
    threeGenerationQuantumNumbers] using h

/-- A sterile right-handed neutrino has the same gauge-singlet quantum numbers when viewed inside
the extended `45 + 3` state space. -/
lemma rightHandedNeutrinoExtended_hasQuantumNumbers (νR : RightHandedNeutrino) :
    HasExtendedStandardModelComputedQuantumNumbers (.sterileNeutrino νR)
      0 0 0 0 1 (1 / 2) .singlet .singlet .right := by
  simpa [HasExtendedStandardModelComputedQuantumNumbers, extendedStandardModelQuantumNumbers,
    HasRightHandedNeutrinoQuantumNumbers] using
      (rightHandedNeutrino_hasQuantumNumbers νR)

/-- The electron-flavor right-handed neutrino has the checked extended-state singlet numbers. -/
lemma rightHandedElectronNeutrinoExtended_hasQuantumNumbers :
    HasExtendedStandardModelComputedQuantumNumbers rightHandedElectronNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right :=
  rightHandedNeutrinoExtended_hasQuantumNumbers .electron

/-- The muon-flavor right-handed neutrino has the checked extended-state singlet numbers. -/
lemma rightHandedMuonNeutrinoExtended_hasQuantumNumbers :
    HasExtendedStandardModelComputedQuantumNumbers rightHandedMuonNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right :=
  rightHandedNeutrinoExtended_hasQuantumNumbers .muon

/-- The tau-flavor right-handed neutrino has the checked extended-state singlet numbers. -/
lemma rightHandedTauNeutrinoExtended_hasQuantumNumbers :
    HasExtendedStandardModelComputedQuantumNumbers rightHandedTauNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right :=
  rightHandedNeutrinoExtended_hasQuantumNumbers .tau

/-- The extended electric charge is still exactly Gell-Mann--Nishijima for every state. -/
lemma extendedStandardModelElectricCharge_eq_gmn
    (f : ExtendedStandardModelWeylFermion) :
    (extendedStandardModelQuantumNumbers f).electricCharge =
      gellMannNishijima (extendedStandardModelQuantumNumbers f).weakIsospin3
        (extendedStandardModelQuantumNumbers f).hypercharge := by
  cases f with
  | active f =>
      simpa [extendedStandardModelQuantumNumbers, threeGenerationQuantumNumbers] using
        (fermionElectricCharge_eq_gmn f.2)
  | sterileNeutrino νR =>
      simpa [extendedStandardModelQuantumNumbers] using
        (rightHandedNeutrino_charge_eq_gmn νR)

/-- The complete generated `45 + 3` active-plus-sterile carrier remains on
the `e/3` electric-charge lattice; the sterile extension contributes charge
zero. -/
lemma extendedStandardModelElectricCharge_thirdQuantized
    (f : ExtendedStandardModelWeylFermion) :
    IsThirdQuantizedCharge (extendedStandardModelQuantumNumbers f).electricCharge := by
  cases f with
  | active f =>
      simpa [extendedStandardModelQuantumNumbers] using
        threeGenerationElectricCharge_thirdQuantized f
  | sterileNeutrino νR =>
      exact ⟨0, by simp [IsThirdQuantizedCharge, extendedStandardModelQuantumNumbers,
        rightHandedNeutrinoQuantumNumbers]⟩

/-- The extended electric-charge trace remains zero because the sterile singlets have `Q=0`. -/
def extendedStandardModelElectricChargeTrace : ℚ :=
  ∑ f : ExtendedStandardModelWeylFermion, (extendedStandardModelQuantumNumbers f).electricCharge

/-- The extended hypercharge trace remains zero because the sterile singlets have `Y=0`. -/
def extendedStandardModelHyperchargeTrace : ℚ :=
  ∑ f : ExtendedStandardModelWeylFermion, (extendedStandardModelQuantumNumbers f).hypercharge

/-- The extended cubic hypercharge trace remains zero because the sterile singlets have `Y=0`. -/
def extendedStandardModelCubicHyperchargeTrace : ℚ :=
  ∑ f : ExtendedStandardModelWeylFermion, (extendedStandardModelQuantumNumbers f).hypercharge ^ 3

lemma extendedStandardModelElectricChargeTrace_zero :
    extendedStandardModelElectricChargeTrace = 0 := by
  native_decide

lemma extendedStandardModelHyperchargeTrace_zero :
    extendedStandardModelHyperchargeTrace = 0 := by
  native_decide

lemma extendedStandardModelCubicHyperchargeTrace_zero :
    extendedStandardModelCubicHyperchargeTrace = 0 := by
  native_decide

/-- The complete checked capability for adjoining sterile right-handed neutrino singlets to the
already generated three-generation Standard-Model Weyl state space. -/
def HasSterileRightHandedNeutrinoSingletComputations : Prop :=
  Fintype.card ExtendedStandardModelWeylFermion = 48
    ∧ (∀ νR : RightHandedNeutrino,
      HasRightHandedNeutrinoQuantumNumbers νR 0 0 0 0 1 (1 / 2)
        .singlet .singlet .right)
    ∧ (∀ f : ExtendedStandardModelWeylFermion,
      (extendedStandardModelQuantumNumbers f).electricCharge =
        gellMannNishijima (extendedStandardModelQuantumNumbers f).weakIsospin3
          (extendedStandardModelQuantumNumbers f).hypercharge)
    ∧ extendedStandardModelElectricChargeTrace = 0
    ∧ extendedStandardModelHyperchargeTrace = 0
    ∧ extendedStandardModelCubicHyperchargeTrace = 0
    ∧ (∀ νR : RightHandedNeutrino,
      Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.total
        (rightHandedNeutrinoLeptonFlavor νR) = 1)
    ∧ HasExtendedStandardModelComputedQuantumNumbers rightHandedElectronNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right
    ∧ HasExtendedStandardModelComputedQuantumNumbers rightHandedMuonNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right
    ∧ HasExtendedStandardModelComputedQuantumNumbers rightHandedTauNeutrinoExtendedState
      0 0 0 0 1 (1 / 2) .singlet .singlet .right

lemma sterileRightHandedNeutrinoSingletComputations_checked :
    HasSterileRightHandedNeutrinoSingletComputations :=
  ⟨extendedStandardModelWeylFermion_state_count,
    rightHandedNeutrino_hasQuantumNumbers,
    extendedStandardModelElectricCharge_eq_gmn,
    extendedStandardModelElectricChargeTrace_zero,
    extendedStandardModelHyperchargeTrace_zero,
    extendedStandardModelCubicHyperchargeTrace_zero,
    rightHandedNeutrinoLeptonFlavor_total,
    rightHandedElectronNeutrinoExtended_hasQuantumNumbers,
    rightHandedMuonNeutrinoExtended_hasQuantumNumbers,
    rightHandedTauNeutrinoExtended_hasQuantumNumbers⟩


/-- **The mixed gravitational–`U(1)_Y` anomaly** `∑ mult · Y` (`= Tr Y` over the generation). -/
def gravitationalAnomaly : ℚ := ∑ i, genMult i * genY i

/-- **The gravitational–`U(1)_Y` anomaly cancels**: `∑ mult · Y = 0` — the hypercharge is traceless
over the generation, exactly as the electric charge is (`su5_generation_charge_neutral`). -/
lemma gravitationalAnomaly_zero : gravitationalAnomaly = 0 := by
  unfold gravitationalAnomaly; simp [genMult, genY, Fin.sum_univ_five]; norm_num

/-- **The `U(1)_Y³` anomaly** `∑ mult · Y³`. -/
def cubicAnomaly : ℚ := ∑ i, genMult i * genY i ^ 3

/-- **The `U(1)_Y³` anomaly cancels**: `∑ mult · Y³ = 0`. -/
lemma cubicAnomaly_zero : cubicAnomaly = 0 := by
  unfold cubicAnomaly; simp [genMult, genY, Fin.sum_univ_five]; norm_num

/-- The hypercharge trace computed directly over the `15` Weyl fermion states. -/
def smGenerationHyperchargeTrace : ℚ :=
  ∑ f : SMWeylFermion, fermionHypercharge f

/-- The generated-state hypercharge trace is the same arithmetic object as `gravitationalAnomaly`
(`Tr Y`) written in multiplet notation. -/
lemma smGenerationHyperchargeTrace_eq_gravitationalAnomaly :
    smGenerationHyperchargeTrace = gravitationalAnomaly := by
  native_decide

/-- The computable Weyl-fermion state space has vanishing hypercharge trace `Tr Y = 0`. -/
lemma smGenerationHyperchargeTrace_zero : smGenerationHyperchargeTrace = 0 := by
  native_decide

/-- The cubic hypercharge trace computed directly over the `15` Weyl fermion states. -/
def smGenerationCubicHyperchargeTrace : ℚ :=
  ∑ f : SMWeylFermion, fermionHypercharge f ^ 3

/-- The generated-state cubic hypercharge trace is the same arithmetic object as the existing
`U(1)_Y^3` anomaly coefficient. -/
lemma smGenerationCubicHyperchargeTrace_eq_cubicAnomaly :
    smGenerationCubicHyperchargeTrace = cubicAnomaly := by
  native_decide

/-- The computable Weyl-fermion state space has vanishing cubic hypercharge trace `Tr Y^3 = 0`. -/
lemma smGenerationCubicHyperchargeTrace_zero : smGenerationCubicHyperchargeTrace = 0 := by
  native_decide


/-- Weak-doublet multiplicities (only `Q` and `L` are `SU(2)` doublets): `(3, 0, 0, 1, 0)`. -/
def su2Mult : Fin 5 → ℚ := ![3, 0, 0, 1, 0]

/-- **The `[SU(2)]²U(1)_Y` anomaly cancels**: summing `Y` over the weak doublets (colour-weighted)
gives `3·(1/3) + 1·(−1) = 0`. -/
lemma su2Anomaly_zero : ∑ i, su2Mult i * genY i = 0 := by
  simp [su2Mult, genY, Fin.sum_univ_five]

/-- Colour-triplet multiplicities (only `Q`, `u^c`, `d^c` are `SU(3)` triplets): `(2, 1, 1, 0, 0)`. -/
def su3Mult : Fin 5 → ℚ := ![2, 1, 1, 0, 0]

/-- **The `[SU(3)]²U(1)_Y` anomaly cancels**: summing `Y` over the colour triplets (weak-weighted)
gives `2·(1/3) + (−4/3) + (2/3) = 0`. -/
lemma su3Anomaly_zero : ∑ i, su3Mult i * genY i = 0 := by
  simp [su3Mult, genY, Fin.sum_univ_five]; norm_num

end Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
