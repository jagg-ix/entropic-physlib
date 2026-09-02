/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel
public import Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
meta import Zil

/-!
# The hadron sector: baryons and mesons assembled

Gathers the model's hadron classification — spin-statistics (`Particles.HadronSpinStatistics`) and charge integrality
from colour triality (`Particles.HadronChargeIntegrality`) — into per-species statements:

* a **baryon** `qqq` is a **fermion** (`(−1)³ = −1`), has **baryon number `1`**, and carries **integer
  electric charge** (a colour singlet, `3 ∣ Σn`);
* a **meson** `qq̄` is a **boson** (`(−1)² = +1`), has **baryon number `0`**, and carries **integer charge**;
* an **isolated quark** is **fractionally** charged, hence confined.

* **§A — the baryon** (`baryon_sector`: fermion ∧ `B=1` ∧ integer charge).
* **§B — the meson** (`meson_sector`: boson ∧ `B=0` ∧ integer charge).
* **§C — the main result** `hadron_sector` (baryon ∧ meson ∧ the confinement signature `isolated_quark_fractional`).
* **§D — named data-driven rows**: the same flavor table computes the charges,
  baryon numbers, strangeness/charm/bottomness, and componentwise meson charge
  coherence for nucleons, hyperons, pions, kaons, `D⁺`, `J/ψ`, and `Υ`.
* **§E — generated particle models**: each named row has a reusable
  `NamedHadronParticleModel` with additive `(Q,B,L)`, constituent count,
  statistics and exchange phase checked from the same valence table.
* **§F — loop occupations**: the same charge-triality layer supplies
  threefold `Z/3` quark loops, sixfold integer-charge lepton loops, and
  baryons as three threefold loops for finite occupation/configuration.
  The finite generator has all six lepton flavors, all six quark flavors,
  eighteen coloured quark states, twenty-four matter states, eight ordered
  baryon configurations, and four unordered charge classes.

**Honest layering.** Each conjunct is a theorem from `Particles.HadronSpinStatistics` (composite exchange phase, baryon
number) or `Particles.HadronChargeIntegrality` (integer charge from `3 ∣ Σn`, the charge face of confinement); this
file *assembles* them per hadron species. Hadron masses, magnetic moments, and the dynamical proof of
confinement are not modelled.

## References

* Baryon = fermion / meson = boson; integer charge of colour singlets; quark confinement (charge
  quantization). `Physlib` (`Particles.HadronSpinStatistics`, `Particles.HadronChargeIntegrality`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector


/-- A named hadron particle model: quark content, additive `(Q,B,L)` quantum
numbers, and the low-energy particle constants used by the hadron sector. -/
structure HadronParticleModel where
  quarkContent : List HadronFlavorModel.QuarkFlavor
  quantumNumbers :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers
  massMeV : ℝ
  magneticMomentNuclearMagnetons : ℝ
  meanLifeSeconds : ℝ

/-- The current mass of a quark from the Standard Model Yukawa equation
`m_q = y_q v / sqrt 2`. This is the shared hadron-sector name for the
repository's existing Yukawa mass carrier. -/
noncomputable def currentQuarkMass (y v : ℝ) : ℝ :=
  Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v

/-- The Yukawa recovery theorem from the existing Standard Model bridge applies
to the shared current-quark mass carrier. -/
lemma currentQuarkMass_yukawaCoupling (y v : ℝ) (hv : v ≠ 0) :
    Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaCoupling
        (currentQuarkMass y v) v = y :=
  Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling.yukawaCoupling_yukawaMass
    y v hv


/-- **[The baryon]** a three-quark composite (`nᵢ ≡ 2 mod 3`) is a **fermion** (exchange phase `(−1)³ = −1`),
has **baryon number `1`**, and is **integer-charged** (a colour singlet). -/
lemma baryon_sector (n₁ n₂ n₃ : ℤ) (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2) (h₃ : n₃ % 3 = 2) :
    compositeTwist 3 = -1
      ∧ 3 * quarkBaryonNumber = 1
      ∧ ∃ k : ℤ, baryonCharge n₁ n₂ n₃ = (k : ℚ) :=
  ⟨baryon_is_fermion, baryonNumber_baryon, baryon_integer_charge n₁ n₂ n₃ h₁ h₂ h₃⟩


/-- **[The meson]** a quark–antiquark composite is a **boson** (exchange phase `(−1)² = +1`), has **baryon
number `0`**, and is **integer-charged**. -/
lemma meson_sector (n n' : ℤ) (h₁ : n % 3 = 2) (h₂ : n' % 3 = 2) :
    compositeTwist 2 = 1
      ∧ quarkBaryonNumber + (-quarkBaryonNumber) = 0
      ∧ ∃ k : ℤ, mesonCharge n n' = (k : ℚ) :=
  ⟨meson_is_boson, baryonNumber_meson, meson_integer_charge n n' h₁ h₂⟩


/-- A tetraquark `qq qbar qbar` has bosonic exchange parity, baryon number
zero, and integer electric charge by the same color-triality closure as an
ordinary meson. -/
lemma tetraquark_sector (n₁ n₂ n₃ n₄ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2)
    (h₃ : n₃ % 3 = 2) (h₄ : n₄ % 3 = 2) :
    compositeTwist 4 = 1
      ∧ 2 * quarkBaryonNumber + 2 * (-quarkBaryonNumber) = 0
      ∧ ∃ k : ℤ, tetraquarkCharge n₁ n₂ n₃ n₄ = (k : ℚ) := by
  refine ⟨?_, ?_, tetraquark_integer_charge n₁ n₂ n₃ n₄ h₁ h₂ h₃ h₄⟩
  · rw [compositeTwist_eq]
    norm_num
  · unfold quarkBaryonNumber
    norm_num

/-- A pentaquark `qqqq qbar` has fermionic exchange parity, baryon number
one, and integer electric charge by color-triality closure. -/
lemma pentaquark_sector (n₁ n₂ n₃ n₄ n₅ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2)
    (h₃ : n₃ % 3 = 2) (h₄ : n₄ % 3 = 2) (h₅ : n₅ % 3 = 2) :
    compositeTwist 5 = -1
      ∧ 4 * quarkBaryonNumber + (-quarkBaryonNumber) = 1
      ∧ ∃ k : ℤ, pentaquarkCharge n₁ n₂ n₃ n₄ n₅ = (k : ℚ) := by
  refine ⟨?_, ?_, pentaquark_integer_charge n₁ n₂ n₃ n₄ n₅ h₁ h₂ h₃ h₄ h₅⟩
  · rw [compositeTwist_eq]
    norm_num
  · unfold quarkBaryonNumber
    norm_num

/-- The flavor quantum numbers of a gauge-only glueball valence carrier.  This
records only what follows from having no quark or lepton valence content:
`Q=B=L=0`.  It is not a mass, width, or confinement-spectrum theorem. -/
def glueballFlavorNeutralQuantumNumbers :
    Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation.QuantumNumbers :=
  ⟨0, 0, 0⟩

/-- Gauge-only glueball valence content is neutral in the additive
`(Q,B,L)` bookkeeping already used by the particle sector. -/
lemma glueballFlavorNeutralQuantumNumbers_checked :
    glueballFlavorNeutralQuantumNumbers.electric = 0
      ∧ glueballFlavorNeutralQuantumNumbers.baryon = 0
      ∧ glueballFlavorNeutralQuantumNumbers.lepton = 0 := by
  norm_num [glueballFlavorNeutralQuantumNumbers]

/-- The glueball valence layer is gauge-only: it uses the already-proved
non-Abelian gluon Lie/Jacobi structure while carrying no additive flavor
quantum numbers.  This is deliberately weaker than a glueball mass-spectrum
claim. -/
lemma glueballGaugeLieStructure_and_flavorNeutral {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ) :
    ⁅A, B⁆ = -⁅B, A⁆
      ∧ ⁅A, A⁆ = 0
      ∧ ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0
      ∧ glueballFlavorNeutralQuantumNumbers.electric = 0
      ∧ glueballFlavorNeutralQuantumNumbers.baryon = 0
      ∧ glueballFlavorNeutralQuantumNumbers.lepton = 0 :=
  ⟨Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra.gluon_lie_structure A B C |>.1,
    Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra.gluon_lie_structure A B C |>.2.1,
    Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra.gluon_lie_structure A B C |>.2.2,
    glueballFlavorNeutralQuantumNumbers_checked.1,
    glueballFlavorNeutralQuantumNumbers_checked.2.1,
    glueballFlavorNeutralQuantumNumbers_checked.2.2⟩


/-- **[The hadron sector]** baryons (`qqq`: fermion, `B=1`, integer charge) and mesons (`qq̄`: boson, `B=0`,
integer charge) are the colour-singlet composites; an isolated quark is fractionally charged and confined.
The colour-singlet bound states are integer-charged and observed; the fractional quarks are not. -/
lemma hadron_sector (n₁ n₂ n₃ : ℤ) (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2) (h₃ : n₃ % 3 = 2) :
    (compositeTwist 3 = -1 ∧ 3 * quarkBaryonNumber = 1
        ∧ ∃ k : ℤ, baryonCharge n₁ n₂ n₃ = (k : ℚ))
      ∧ (compositeTwist 2 = 1 ∧ quarkBaryonNumber + (-quarkBaryonNumber) = 0
        ∧ ∃ k : ℤ, mesonCharge n₁ n₂ = (k : ℚ))
      ∧ ¬ ∃ k : ℤ, windingCharge n₁ = (k : ℚ) :=
  ⟨baryon_sector n₁ n₂ n₃ h₁ h₂ h₃, meson_sector n₁ n₂ h₁ h₂, isolated_quark_fractional n₁ h₁⟩

/-- Capability predicate for the exotic valence sectors that are now covered:
tetraquarks and pentaquarks have derived triality charge closure and baryon
number; glueball valence is only the gauge-only neutral bookkeeping layer. -/
def HasExoticHadronValenceSectors : Prop :=
  (∀ n₁ n₂ n₃ n₄ : ℤ,
      n₁ % 3 = 2 → n₂ % 3 = 2 → n₃ % 3 = 2 → n₄ % 3 = 2 →
        compositeTwist 4 = 1
          ∧ 2 * quarkBaryonNumber + 2 * (-quarkBaryonNumber) = 0
          ∧ ∃ k : ℤ, tetraquarkCharge n₁ n₂ n₃ n₄ = (k : ℚ))
    ∧ (∀ n₁ n₂ n₃ n₄ n₅ : ℤ,
      n₁ % 3 = 2 → n₂ % 3 = 2 → n₃ % 3 = 2 → n₄ % 3 = 2 → n₅ % 3 = 2 →
        compositeTwist 5 = -1
          ∧ 4 * quarkBaryonNumber + (-quarkBaryonNumber) = 1
          ∧ ∃ k : ℤ, pentaquarkCharge n₁ n₂ n₃ n₄ n₅ = (k : ℚ))
    ∧ glueballFlavorNeutralQuantumNumbers.electric = 0
    ∧ glueballFlavorNeutralQuantumNumbers.baryon = 0
    ∧ glueballFlavorNeutralQuantumNumbers.lepton = 0

/-- The exotic valence sector is checked from the existing winding triality,
spin-statistics, and additive quantum-number infrastructure. -/
lemma exoticHadronValenceSectors_checked :
    HasExoticHadronValenceSectors :=
  ⟨fun n₁ n₂ n₃ n₄ h₁ h₂ h₃ h₄ =>
      tetraquark_sector n₁ n₂ n₃ n₄ h₁ h₂ h₃ h₄,
    fun n₁ n₂ n₃ n₄ n₅ h₁ h₂ h₃ h₄ h₅ =>
      pentaquark_sector n₁ n₂ n₃ n₄ n₅ h₁ h₂ h₃ h₄ h₅,
    glueballFlavorNeutralQuantumNumbers_checked.1,
    glueballFlavorNeutralQuantumNumbers_checked.2.1,
    glueballFlavorNeutralQuantumNumbers_checked.2.2⟩


/-- Every quark flavor is represented by the corresponding threefold
`Z/3` quark-base loop. Up-type flavors use the `+2/3` loop; down-type flavors
use the `-1/3` loop. -/
def quarkFlavorThreeFoldLoop :
    HadronFlavorModel.QuarkFlavor → ThreeFoldQuarkLoop
  | HadronFlavorModel.QuarkFlavor.up => upThreeFoldLoop
  | HadronFlavorModel.QuarkFlavor.down => downThreeFoldLoop
  | HadronFlavorModel.QuarkFlavor.strange => downThreeFoldLoop
  | HadronFlavorModel.QuarkFlavor.charm => upThreeFoldLoop
  | HadronFlavorModel.QuarkFlavor.bottom => downThreeFoldLoop
  | HadronFlavorModel.QuarkFlavor.top => upThreeFoldLoop

/-- The flavor-to-loop map preserves winding number. -/
lemma quarkFlavorThreeFoldLoop_winding
    (q : HadronFlavorModel.QuarkFlavor) :
    (quarkFlavorThreeFoldLoop q).winding =
      HadronFlavorModel.QuarkFlavor.windingNumber q := by
  cases q <;> rfl

/-- The flavor-to-loop map preserves electric charge. -/
lemma quarkFlavorThreeFoldLoop_charge
    (q : HadronFlavorModel.QuarkFlavor) :
    (quarkFlavorThreeFoldLoop q).charge =
      HadronFlavorModel.QuarkFlavor.electricCharge q := by
  cases q <;>
    simp [quarkFlavorThreeFoldLoop, ThreeFoldQuarkLoop.charge,
      HadronFlavorModel.QuarkFlavor.electricCharge,
      HadronFlavorModel.QuarkFlavor.windingNumber, upThreeFoldLoop,
      downThreeFoldLoop, upWinding, downWinding]

/-- Any ordered three-flavor baryon row becomes a three-loop baryon occupation. -/
def baryonFlavorThreeLoopOccupation
    (q1 q2 q3 : HadronFlavorModel.QuarkFlavor) :
    BaryonThreeLoopOccupation :=
  { q1 := quarkFlavorThreeFoldLoop q1
    q2 := quarkFlavorThreeFoldLoop q2
    q3 := quarkFlavorThreeFoldLoop q3 }

/-- The generated three-loop baryon occupation preserves the existing flavor
charge sum. -/
lemma baryonFlavorThreeLoopOccupation_totalCharge_eq_listCharge
    (q1 q2 q3 : HadronFlavorModel.QuarkFlavor) :
    (baryonFlavorThreeLoopOccupation q1 q2 q3).totalCharge =
      HadronFlavorModel.listCharge [q1, q2, q3] := by
  simp [baryonFlavorThreeLoopOccupation, BaryonThreeLoopOccupation.totalCharge,
    quarkFlavorThreeFoldLoop_charge, HadronFlavorModel.listCharge]
  ring

/-- Every ordered three-flavor baryon row has integer charge when read as
three threefold loops. -/
lemma baryonFlavorThreeLoopOccupation_integer_charge
    (q1 q2 q3 : HadronFlavorModel.QuarkFlavor) :
    ∃ k : ℤ,
      (baryonFlavorThreeLoopOccupation q1 q2 q3).totalCharge = (k : ℚ) :=
  BaryonThreeLoopOccupation.totalCharge_integer
    (baryonFlavorThreeLoopOccupation q1 q2 q3)

/-- The generated six-quark loop-flavor carrier maps to the repository's
existing hadron flavor model. -/
def quarkLoopFlavor_hadronFlavor :
    QuarkLoopFlavor → HadronFlavorModel.QuarkFlavor
  | QuarkLoopFlavor.up => HadronFlavorModel.QuarkFlavor.up
  | QuarkLoopFlavor.charm => HadronFlavorModel.QuarkFlavor.charm
  | QuarkLoopFlavor.top => HadronFlavorModel.QuarkFlavor.top
  | QuarkLoopFlavor.down => HadronFlavorModel.QuarkFlavor.down
  | QuarkLoopFlavor.strange => HadronFlavorModel.QuarkFlavor.strange
  | QuarkLoopFlavor.bottom => HadronFlavorModel.QuarkFlavor.bottom

/-- The all-quark loop-flavor carrier preserves the existing hadron-flavor
electric charge computation. -/
lemma quarkLoopFlavor_charge_eq_hadronFlavor
    (q : QuarkLoopFlavor) :
    q.charge =
      HadronFlavorModel.QuarkFlavor.electricCharge
        (quarkLoopFlavor_hadronFlavor q) := by
  cases q <;>
    simp [quarkLoopFlavor_hadronFlavor, QuarkLoopFlavor.charge,
      QuarkLoopFlavor.threeFoldLoop, QuarkLoopFlavor.chargeBase,
      QuarkLoopBase.threeFoldLoop, ThreeFoldQuarkLoop.charge,
      HadronFlavorModel.QuarkFlavor.electricCharge,
      HadronFlavorModel.QuarkFlavor.windingNumber, upThreeFoldLoop,
      downThreeFoldLoop, upWinding, downWinding]


/-- The six Standard-Model quark Yukawa couplings, indexed by named flavor.
These are input couplings; the mass relation below is the derived content. -/
structure QuarkYukawaCouplings where
  up : ℝ
  down : ℝ
  strange : ℝ
  charm : ℝ
  bottom : ℝ
  top : ℝ

namespace QuarkYukawaCouplings

/-- Retrieve the Yukawa coupling for a quark flavor. -/
def coupling (Y : QuarkYukawaCouplings) :
    HadronFlavorModel.QuarkFlavor → ℝ
  | HadronFlavorModel.QuarkFlavor.up => Y.up
  | HadronFlavorModel.QuarkFlavor.down => Y.down
  | HadronFlavorModel.QuarkFlavor.strange => Y.strange
  | HadronFlavorModel.QuarkFlavor.charm => Y.charm
  | HadronFlavorModel.QuarkFlavor.bottom => Y.bottom
  | HadronFlavorModel.QuarkFlavor.top => Y.top

end QuarkYukawaCouplings

/-- Current quark mass generated by the Higgs VEV from the shared Yukawa mass
equation `m_q = y_q v / sqrt 2`. -/
noncomputable def quarkCurrentMass
    (Y : QuarkYukawaCouplings) (v : ℝ)
    (q : HadronFlavorModel.QuarkFlavor) : ℝ :=
  currentQuarkMass (Y.coupling q) v

/-- The up-quark current mass `m_u = y_u v / sqrt 2`. -/
noncomputable def upQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.up

/-- The down-quark current mass `m_d = y_d v / sqrt 2`. -/
noncomputable def downQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.down

/-- The strange-quark current mass `m_s = y_s v / sqrt 2`. -/
noncomputable def strangeQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.strange

/-- The charm-quark current mass `m_c = y_c v / sqrt 2`. -/
noncomputable def charmQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.charm

/-- The bottom-quark current mass `m_b = y_b v / sqrt 2`. -/
noncomputable def bottomQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.bottom

/-- The top-quark current mass `m_t = y_t v / sqrt 2`. -/
noncomputable def topQuarkCurrentMass (Y : QuarkYukawaCouplings) (v : ℝ) : ℝ :=
  quarkCurrentMass Y v HadronFlavorModel.QuarkFlavor.top

/-- The generated quark current mass is exactly the repository's shared
Standard Model Yukawa mass carrier. -/
lemma quarkCurrentMass_eq_yukawaMass
    (Y : QuarkYukawaCouplings) (v : ℝ)
    (q : HadronFlavorModel.QuarkFlavor) :
    quarkCurrentMass Y v q =
      Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass
        (Y.coupling q) v := rfl

/-- Recovering the quark Yukawa coupling from the generated current mass gives
the original input coupling when the Higgs VEV is nonzero. -/
lemma quarkCurrentMass_yukawaCoupling
    (Y : QuarkYukawaCouplings) (v : ℝ) (hv : v ≠ 0)
    (q : HadronFlavorModel.QuarkFlavor) :
    Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaCoupling
        (quarkCurrentMass Y v q) v = Y.coupling q :=
  currentQuarkMass_yukawaCoupling (Y.coupling q) v hv

/-- For positive Higgs VEV, the current-quark mass map is strictly monotone in
the Yukawa coupling. This is the exact algebra behind generation ordering; no
measured quark masses are imported. -/
lemma currentQuarkMass_lt_of_yukawa_lt (y₁ y₂ v : ℝ)
    (hv : 0 < v) (hy : y₁ < y₂) :
    currentQuarkMass y₁ v < currentQuarkMass y₂ v := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hscale : 0 < v / Real.sqrt 2 := div_pos hv hsqrt2
  unfold currentQuarkMass
  unfold Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass
  calc
    y₁ * v / Real.sqrt 2 = y₁ * (v / Real.sqrt 2) := by ring
    _ < y₂ * (v / Real.sqrt 2) := mul_lt_mul_of_pos_right hy hscale
    _ = y₂ * v / Real.sqrt 2 := by ring

/-- If the up-type Yukawa couplings are ordered, the generated up-type current
masses are ordered: `m_u < m_c < m_t`. -/
lemma upTypeQuarkCurrentMass_hierarchy
    (Y : QuarkYukawaCouplings) (v : ℝ) (hv : 0 < v)
    (huc : Y.up < Y.charm) (hct : Y.charm < Y.top) :
    upQuarkCurrentMass Y v < charmQuarkCurrentMass Y v
      ∧ charmQuarkCurrentMass Y v < topQuarkCurrentMass Y v := by
  refine ⟨?_, ?_⟩
  · simpa [upQuarkCurrentMass, charmQuarkCurrentMass, quarkCurrentMass,
      QuarkYukawaCouplings.coupling] using
      currentQuarkMass_lt_of_yukawa_lt Y.up Y.charm v hv huc
  · simpa [charmQuarkCurrentMass, topQuarkCurrentMass, quarkCurrentMass,
      QuarkYukawaCouplings.coupling] using
      currentQuarkMass_lt_of_yukawa_lt Y.charm Y.top v hv hct

/-- If the down-type Yukawa couplings are ordered, the generated down-type
current masses are ordered: `m_d < m_s < m_b`. -/
lemma downTypeQuarkCurrentMass_hierarchy
    (Y : QuarkYukawaCouplings) (v : ℝ) (hv : 0 < v)
    (hds : Y.down < Y.strange) (hsb : Y.strange < Y.bottom) :
    downQuarkCurrentMass Y v < strangeQuarkCurrentMass Y v
      ∧ strangeQuarkCurrentMass Y v < bottomQuarkCurrentMass Y v := by
  refine ⟨?_, ?_⟩
  · simpa [downQuarkCurrentMass, strangeQuarkCurrentMass, quarkCurrentMass,
      QuarkYukawaCouplings.coupling] using
      currentQuarkMass_lt_of_yukawa_lt Y.down Y.strange v hv hds
  · simpa [strangeQuarkCurrentMass, bottomQuarkCurrentMass, quarkCurrentMass,
      QuarkYukawaCouplings.coupling] using
      currentQuarkMass_lt_of_yukawa_lt Y.strange Y.bottom v hv hsb

/-- Current mass for the generated six-quark loop-flavor carrier, routed
through the existing hadron flavor model. -/
noncomputable def quarkLoopFlavorCurrentMass
    (Y : QuarkYukawaCouplings) (v : ℝ) (q : QuarkLoopFlavor) : ℝ :=
  quarkCurrentMass Y v (quarkLoopFlavor_hadronFlavor q)

/-- The loop-flavor current mass uses the same flavor map that already
preserves electric charge. -/
lemma quarkLoopFlavorCurrentMass_eq_hadronFlavor
    (Y : QuarkYukawaCouplings) (v : ℝ) (q : QuarkLoopFlavor) :
    quarkLoopFlavorCurrentMass Y v q =
      quarkCurrentMass Y v (quarkLoopFlavor_hadronFlavor q) := rfl

/-- The generated quark mass spectrum covers all six quark flavors, recovers
their Yukawa couplings when `v ≠ 0`, and agrees with the loop-flavor carrier. -/
def HasQuarkYukawaMassSpectrum
    (Y : QuarkYukawaCouplings) (v : ℝ) : Prop :=
  (∀ q : HadronFlavorModel.QuarkFlavor,
      quarkCurrentMass Y v q =
        Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass
          (Y.coupling q) v)
    ∧ (∀ _hv : v ≠ 0, ∀ q : HadronFlavorModel.QuarkFlavor,
      Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaCoupling
          (quarkCurrentMass Y v q) v = Y.coupling q)
    ∧ (∀ q : QuarkLoopFlavor,
      quarkLoopFlavorCurrentMass Y v q =
        quarkCurrentMass Y v (quarkLoopFlavor_hadronFlavor q))
    ∧ (∀ q : QuarkLoopFlavor,
      q.charge =
        HadronFlavorModel.QuarkFlavor.electricCharge
          (quarkLoopFlavor_hadronFlavor q))

/-- The quark current-mass spectrum is checked from the shared Yukawa equation
and the already-proved loop-flavor-to-hadron-flavor bridge. -/
lemma quarkYukawaMassSpectrum_checked
    (Y : QuarkYukawaCouplings) (v : ℝ) :
    HasQuarkYukawaMassSpectrum Y v :=
  ⟨quarkCurrentMass_eq_yukawaMass Y v,
    fun hv q => quarkCurrentMass_yukawaCoupling Y v hv q,
    quarkLoopFlavorCurrentMass_eq_hadronFlavor Y v,
    quarkLoopFlavor_charge_eq_hadronFlavor⟩

/-- Checked hierarchy package for the six quark current masses. The order is
derived from ordered Yukawa couplings and positive Higgs VEV, rather than from
a mass table. -/
def HasQuarkYukawaGenerationMassHierarchy
    (Y : QuarkYukawaCouplings) (v : ℝ) : Prop :=
  (0 < v → Y.up < Y.charm → Y.charm < Y.top →
    upQuarkCurrentMass Y v < charmQuarkCurrentMass Y v
      ∧ charmQuarkCurrentMass Y v < topQuarkCurrentMass Y v)
    ∧ (0 < v → Y.down < Y.strange → Y.strange < Y.bottom →
      downQuarkCurrentMass Y v < strangeQuarkCurrentMass Y v
        ∧ strangeQuarkCurrentMass Y v < bottomQuarkCurrentMass Y v)

/-- The six-quark generation hierarchy is a theorem about the shared Yukawa
mass map: a positive common VEV preserves the coupling order. -/
lemma quarkYukawaGenerationMassHierarchy_checked
    (Y : QuarkYukawaCouplings) (v : ℝ) :
    HasQuarkYukawaGenerationMassHierarchy Y v :=
  ⟨fun hv huc hct => upTypeQuarkCurrentMass_hierarchy Y v hv huc hct,
    fun hv hds hsb => downTypeQuarkCurrentMass_hierarchy Y v hv hds hsb⟩


/-- Repository capability predicate for hadrons: named flavor charges,
Gell-Mann--Nishijima identities, and composite spin-statistics are all available
from the same sector. -/
def HasNamedHadronComputations : Prop :=
  HadronFlavorModel.listCharge HadronFlavorModel.proton = 1
    ∧ HadronFlavorModel.listCharge HadronFlavorModel.neutron = 0
    ∧ HadronFlavorModel.HasNuclearIsospinConvention
    ∧ (HadronFlavorModel.listCharge HadronFlavorModel.lambda = 0
      ∧ HadronFlavorModel.listStrangeness HadronFlavorModel.lambda = -1)
    ∧ HadronFlavorModel.HasLambdaBaryon
    ∧ (HadronFlavorModel.listCharge HadronFlavorModel.sigmaPlus = 1
      ∧ HadronFlavorModel.listStrangeness HadronFlavorModel.sigmaPlus = -1)
    ∧ HadronFlavorModel.HasSigmaBaryonTriplet
    ∧ HadronFlavorModel.HasSigmaLambdaIsospinWavefunctions
    ∧ HadronFlavorModel.HasXiBaryonDoublet
    ∧ HadronFlavorModel.HasOmegaBaryon
    ∧ (HadronFlavorModel.listCharge
        [HadronFlavorModel.QuarkFlavor.up,
          HadronFlavorModel.QuarkFlavor.down,
          HadronFlavorModel.QuarkFlavor.charm] = 1
      ∧ (([HadronFlavorModel.QuarkFlavor.up,
            HadronFlavorModel.QuarkFlavor.down,
            HadronFlavorModel.QuarkFlavor.charm].map
          HadronFlavorModel.QuarkFlavor.charmness).sum) = 1)
    ∧ HadronFlavorModel.HasPionFlavorTriplet
    ∧ HadronFlavorModel.HasKaonFlavorDoublet
    ∧ HadronFlavorModel.HasHeavyQuarkoniumFlavorModels
    ∧ HadronFlavorModel.HasDataDrivenNamedHadronTable
    ∧ HadronFlavorModel.HasDataDrivenNamedHadronParticleModels
    ∧ HadronFlavorModel.HasFlavorMultipletEnumeration
    ∧ (∀ Y v, HasQuarkYukawaMassSpectrum Y v)
    ∧ (∀ Y v, HasQuarkYukawaGenerationMassHierarchy Y v)
    ∧ HasThreeSixBaryonLoopOccupationModel
    ∧ HasFiniteThreeSixLoopEnumeration
    ∧ (∀ q : QuarkLoopFlavor,
      q.charge =
        HadronFlavorModel.QuarkFlavor.electricCharge
          (quarkLoopFlavor_hadronFlavor q))
    ∧ (∀ q : HadronFlavorModel.QuarkFlavor,
      (quarkFlavorThreeFoldLoop q).charge =
        HadronFlavorModel.QuarkFlavor.electricCharge q)
    ∧ (∀ q1 q2 q3 : HadronFlavorModel.QuarkFlavor,
      (baryonFlavorThreeLoopOccupation q1 q2 q3).totalCharge =
        HadronFlavorModel.listCharge [q1, q2, q3])
    ∧ (∀ q1 q2 q3 : HadronFlavorModel.QuarkFlavor,
      ∃ k : ℤ,
        (baryonFlavorThreeLoopOccupation q1 q2 q3).totalCharge = (k : ℚ))
    ∧ (∀ qs : List HadronFlavorModel.QuarkFlavor,
      HadronFlavorModel.listCharge qs =
        HadronFlavorModel.listIsospinT3 qs + HadronFlavorModel.listHypercharge qs / 2)
    ∧ (∀ qs : List HadronFlavorModel.QuarkFlavor,
      HadronFlavorModel.listHypercharge qs =
        2 * (HadronFlavorModel.listCharge qs - HadronFlavorModel.listIsospinT3 qs))
    ∧ (∀ q qbar : HadronFlavorModel.QuarkFlavor,
      HadronFlavorModel.mesonCharge q qbar =
        HadronFlavorModel.mesonIsospinT3 q qbar
          + HadronFlavorModel.mesonHypercharge q qbar / 2)
    ∧ compositeTwist 3 = -1
    ∧ compositeTwist 2 = 1
    ∧ 3 * quarkBaryonNumber = 1
    ∧ quarkBaryonNumber + (-quarkBaryonNumber) = 0

/-- Named hadron computations are obtained from the existing flavor bookkeeping
and the existing ribbon-twist statistics layer. -/
lemma namedHadronComputations_checked : HasNamedHadronComputations :=
  ⟨HadronFlavorModel.proton_charge,
    HadronFlavorModel.neutron_charge,
    HadronFlavorModel.nuclearIsospinConvention_checked,
    HadronFlavorModel.lambda_charge_strangeness,
    HadronFlavorModel.lambdaBaryon_checked,
    HadronFlavorModel.sigmaPlus_charge_strangeness,
    HadronFlavorModel.sigmaBaryonTriplet_checked,
    HadronFlavorModel.sigmaLambdaIsospinWavefunctions_checked,
    HadronFlavorModel.xiBaryonDoublet_checked,
    HadronFlavorModel.omegaBaryon_checked,
    HadronFlavorModel.lambdaC_charge_charm,
    HadronFlavorModel.pionFlavorTriplet_checked,
    HadronFlavorModel.kaonFlavorDoublet_checked,
    HadronFlavorModel.heavyQuarkoniumFlavorModels_checked,
    HadronFlavorModel.dataDrivenNamedHadronTable_checked,
    HadronFlavorModel.dataDrivenNamedHadronParticleModels_checked,
    HadronFlavorModel.flavorMultipletEnumeration_checked,
    quarkYukawaMassSpectrum_checked,
    quarkYukawaGenerationMassHierarchy_checked,
    threeSixBaryonLoopOccupationModel_checked,
    finiteThreeSixLoopEnumeration_checked,
    quarkLoopFlavor_charge_eq_hadronFlavor,
    quarkFlavorThreeFoldLoop_charge,
    baryonFlavorThreeLoopOccupation_totalCharge_eq_listCharge,
    baryonFlavorThreeLoopOccupation_integer_charge,
    HadronFlavorModel.gmn_strong_baryon,
    HadronFlavorModel.listHypercharge_eq_two_mul_charge_sub_isospin,
    HadronFlavorModel.gmn_strong_meson,
    baryon_is_fermion,
    meson_is_boson,
    baryonNumber_baryon,
    baryonNumber_meson⟩

/-- Full hadron sector bridge: generic integral-charge/spin-statistics facts and
named flavor computations are available together. -/
lemma hadron_sector_with_named_hadrons (n₁ n₂ n₃ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2) (h₃ : n₃ % 3 = 2) :
    ((compositeTwist 3 = -1 ∧ 3 * quarkBaryonNumber = 1
        ∧ ∃ k : ℤ, baryonCharge n₁ n₂ n₃ = (k : ℚ))
      ∧ (compositeTwist 2 = 1 ∧ quarkBaryonNumber + (-quarkBaryonNumber) = 0
        ∧ ∃ k : ℤ, mesonCharge n₁ n₂ = (k : ℚ))
      ∧ ¬ ∃ k : ℤ, windingCharge n₁ = (k : ℚ))
      ∧ HasNamedHadronComputations :=
  ⟨hadron_sector n₁ n₂ n₃ h₁ h₂ h₃,
    namedHadronComputations_checked⟩

/-- Full hadron sector bridge with the named hadrons and the newly covered
exotic valence sectors.  The covered exotic content is charge, baryon number,
exchange parity, and gauge-only neutrality; per-species masses, widths, and
form factors are intentionally not claimed here. -/
lemma hadron_sector_with_named_and_exotic_hadrons (n₁ n₂ n₃ : ℤ)
    (h₁ : n₁ % 3 = 2) (h₂ : n₂ % 3 = 2) (h₃ : n₃ % 3 = 2) :
    ((compositeTwist 3 = -1 ∧ 3 * quarkBaryonNumber = 1
        ∧ ∃ k : ℤ, baryonCharge n₁ n₂ n₃ = (k : ℚ))
      ∧ (compositeTwist 2 = 1 ∧ quarkBaryonNumber + (-quarkBaryonNumber) = 0
        ∧ ∃ k : ℤ, mesonCharge n₁ n₂ = (k : ℚ))
      ∧ ¬ ∃ k : ℤ, windingCharge n₁ = (k : ℚ))
      ∧ HasNamedHadronComputations
      ∧ HasExoticHadronValenceSectors :=
  ⟨hadron_sector n₁ n₂ n₃ h₁ h₂ h₃,
    namedHadronComputations_checked,
    exoticHadronValenceSectors_checked⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.currentQuarkMass_yukawaCoupling where
  formalizes @ "claim:the-current-quark-mass-is-the-yukawa-coupling-times-the-higgs-vev-over-root-two",
  supported_by @ "paper:pdg-2026-review-quark-masses"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.baryon_sector where
  formalizes @ "claim:a-baryon-from-three-color-triality-quark-windings-has-integer-electric-charge",
  supported_by @ "paper:gell-mann-1964-schematic-model-of-baryons-and-mesons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.hadron_sector where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.baryon_sector",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronChargeIntegrality.isolated_quark_fractional",
  formalizes @ "claim:the-color-singlet-hadron-sectors-baryon-meson-tetraquark-pentaquark-all-have-integer-charge-from-color-triality",
  requires @ "claim:a-baryon-from-three-color-triality-quark-windings-has-integer-electric-charge"

zil_file_contract physlib.hadronSector where
  promises "The color-singlet hadron sector built from color-triality quark windings (winding congruent to two mod three): baryons (three quarks), mesons (quark-antiquark), tetraquarks and pentaquarks all have integer electric charge; glueballs are flavor-neutral with the gauge Lie structure; and the current quark mass is the Yukawa coupling times the Higgs VEV over root two."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.currentQuarkMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.glueballFlavorNeutralQuantumNumbers"]
  forbids_substitutes ["a dynamical proof of color confinement, only the integer-charge signature and valence bookkeeping are carried",
    "a derivation of the quark charge windings or Yukawa couplings, taken as model inputs"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.currentQuarkMass_yukawaCoupling,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.baryon_sector,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.meson_sector,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.tetraquark_sector,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.pentaquark_sector,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector.hadron_sector]

/- ZIL-END -/
